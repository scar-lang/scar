//! Cranelift native backend for the Scar compiler.

use std::collections::HashMap;

use cranelift_codegen::{
    ir::{
        self, AbiParam, InstBuilder, MemFlags, StackSlotData, StackSlotKind, Type as ClifType,
        Value, types,
    },
    settings::{self, Configurable},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::{
    CompileError,
    ast::{BinaryOp, Expr, Function, Program, Stmt, Type, TypeDefKind, UnaryOp},
    codegen::{describe_type, infer_codegen_expr_type, is_codegen_signed_integer_type},
    sema::ProgramInfo,
};

pub struct NativeArtifact {
    pub object: Vec<u8>,
    pub object_extension: &'static str,
}

pub fn compile_object(
    program: &Program,
    info: &ProgramInfo,
    optimize: bool,
) -> Result<NativeArtifact, CompileError> {
    if !program.globals.is_empty() {
        return Err(CompileError::new(
            "native backend does not yet support globals",
        ));
    }
    let mut flag_builder = settings::builder();
    flag_builder
        .set("opt_level", if optimize { "speed" } else { "none" })
        .map_err(|e| CompileError::new(e.to_string()))?;
    flag_builder
        .set("is_pic", "true")
        .map_err(|e| CompileError::new(e.to_string()))?;
    flag_builder
        .set("unwind_info", "false")
        .map_err(|e| CompileError::new(e.to_string()))?;
    let flags = settings::Flags::new(flag_builder);
    let isa_builder = cranelift_native::builder()
        .map_err(|e| CompileError::new(format!("failed to create native target: {e}")))?;
    let isa = isa_builder
        .finish(flags)
        .map_err(|e| CompileError::new(format!("failed to initialize native target: {e}")))?;
    let object_extension = match isa.triple().binary_format {
        target_lexicon::BinaryFormat::Coff => "obj",
        _ => "o",
    };
    let builder = ObjectBuilder::new(isa, "scar", default_libcall_names())
        .map_err(|e| CompileError::new(format!("failed to create object module: {e}")))?;
    let module = ObjectModule::new(builder);
    let pointer_type = module.target_config().pointer_type();

    let reachable = collect_reachable_functions(program);
    let mut backend = Backend {
        module,
        pointer_type,
        info,
        reachable,
        function_ids: HashMap::new(),
        data_ids: HashMap::new(),
        strings: HashMap::new(),
        next_data: 0,
        next_block: 0,
    };

    backend.declare_functions(program)?;
    backend.define_strings(program)?;

    for function in &program.functions {
        if function.extern_name.is_some() || !backend.reachable.contains(&function.name) {
            continue;
        }
        backend.define_function(function)?;
    }
    backend.define_entrypoint(program)?;

    let product = backend.module.finish();
    let object = product
        .emit()
        .map_err(|e| CompileError::new(format!("failed to emit native object: {e}")))?;
    Ok(NativeArtifact {
        object,
        object_extension,
    })
}

struct Backend<'a> {
    module: ObjectModule,
    pointer_type: ClifType,
    info: &'a ProgramInfo,
    reachable: std::collections::HashSet<String>,
    function_ids: HashMap<String, FuncId>,
    data_ids: HashMap<String, DataId>,
    strings: HashMap<String, (DataId, usize)>,
    next_data: usize,
    next_block: usize,
}

#[derive(Clone, Copy)]
struct LoopContext {
    break_block: ir::Block,
    continue_block: ir::Block,
}

struct FunctionScope {
    vars: HashMap<String, (Variable, Type)>,
    return_var: Option<(Variable, Type)>,
    return_block: ir::Block,
    loops: Vec<LoopContext>,
    temp_slots: HashMap<String, ir::StackSlot>,
}

impl<'a> Backend<'a> {
    fn declare_functions(&mut self, program: &Program) -> Result<(), CompileError> {
        for function in &program.functions {
            if !self.reachable.contains(&function.name) {
                continue;
            }
            let signature = self.signature_for(function)?;
            let name = self.symbol_for(function);
            let linkage = if function.extern_name.is_some() {
                Linkage::Import
            } else {
                Linkage::Export
            };
            let func_id = self
                .module
                .declare_function(&name, linkage, &signature)
                .map_err(|e| CompileError::new(format!("failed to declare `{name}`: {e}")))?;
            self.function_ids.insert(function.name.clone(), func_id);
        }
        Ok(())
    }

    fn define_strings(&mut self, program: &Program) -> Result<(), CompileError> {
        let mut strings = Vec::new();
        collect_program_strings(program, &mut strings);
        for value in strings {
            if self.strings.contains_key(&value) {
                continue;
            }
            let mut bytes = value.as_bytes().to_vec();
            bytes.push(0);
            let len = bytes.len();
            let name = format!("__scar_str_{}", self.next_data);
            self.next_data += 1;
            let data_id = self
                .module
                .declare_data(&name, Linkage::Local, false, false)
                .map_err(|e| CompileError::new(e.to_string()))?;
            let mut desc = DataDescription::new();
            desc.define(bytes.into_boxed_slice());
            desc.set_align(1);
            self.module
                .define_data(data_id, &desc)
                .map_err(|e| CompileError::new(e.to_string()))?;
            self.strings.insert(value, (data_id, len));
            self.data_ids.insert(name, data_id);
        }
        Ok(())
    }

    fn define_entrypoint(&mut self, program: &Program) -> Result<(), CompileError> {
        let Some(main_function) = program
            .functions
            .iter()
            .find(|function| function.name == "main" && function.extern_name.is_none())
        else {
            return Ok(());
        };
        let mut signature = self.module.make_signature();
        signature.params.push(AbiParam::new(types::I32));
        signature.params.push(AbiParam::new(self.pointer_type));
        signature.returns.push(AbiParam::new(types::I32));
        let main_id = self
            .module
            .declare_function("main", Linkage::Export, &signature)
            .map_err(|e| CompileError::new(format!("failed to declare C entrypoint: {e}")))?;
        let mut ctx = self.module.make_context();
        ctx.func.signature = signature;
        ctx.func.name = ir::UserFuncName::user(0, main_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        builder.ins().nop();
        let function_id = *self
            .function_ids
            .get(&main_function.name)
            .ok_or_else(|| CompileError::new("missing main function id"))?;
        let func_ref = self.module.declare_func_in_func(function_id, builder.func);
        let call = builder.ins().call(func_ref, &[]);
        let result = builder.inst_results(call).first().copied();
        let value = match result {
            Some(value) if !matches!(main_function.return_type, Type::Void) => value,
            _ => builder.ins().iconst(types::I32, 0),
        };
        let value = if matches!(main_function.return_type, Type::Void) {
            builder.ins().iconst(types::I32, 0)
        } else {
            self.coerce_value(&mut builder, value, types::I32, &main_function.return_type)?
        };
        builder.ins().return_(&[value]);
        builder.finalize();
        self.module
            .define_function(main_id, &mut ctx)
            .map_err(|e| CompileError::new(format!("failed to define C entrypoint: {e:?}")))?;
        Ok(())
    }

    fn define_function(&mut self, function: &Function) -> Result<(), CompileError> {
        let func_id = *self.function_ids.get(&function.name).ok_or_else(|| {
            CompileError::new(format!("missing function id for {}", function.name))
        })?;
        let signature = self.signature_for(function)?;
        let mut ctx = self.module.make_context();
        ctx.func.signature = signature;
        ctx.func.name = ir::UserFuncName::user(0, func_id.as_u32());
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        builder.ins().nop();

        let return_block = builder.create_block();
        let return_var = if matches!(function.return_type, Type::Void) {
            None
        } else {
            let ty = self.type_of(&function.return_type)?;
            let var = builder.declare_var(ty);
            builder.append_block_param(return_block, ty);
            Some((var, function.return_type.clone()))
        };

        if let Some((var, return_ty)) = return_var.clone() {
            let ty = self.type_of(&return_ty)?;
            let zero = if ty.is_float() {
                if ty == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                }
            } else {
                builder.ins().iconst(ty, 0)
            };
            builder.def_var(var, zero);
        }

        let mut scope = FunctionScope {
            vars: HashMap::new(),
            return_var,
            return_block,
            loops: Vec::new(),
            temp_slots: HashMap::new(),
        };

        let params = builder.block_params(entry).to_vec();
        for (param, value) in function.params.iter().zip(params.into_iter()) {
            let ty = self.type_of(&param.ty)?;
            let var = builder.declare_var(ty);
            builder.def_var(var, value);
            scope
                .vars
                .insert(param.name.clone(), (var, param.ty.clone()));
        }

        self.emit_block(&mut builder, &function.body, function, &mut scope)?;
        if !current_block_terminated(&builder) {
            if let Some((return_var, _)) = scope.return_var.clone() {
                let value = builder.use_var(return_var);
                builder.ins().jump(return_block, &[value.into()]);
            } else {
                builder.ins().jump(return_block, &[]);
            }
        }
        builder.switch_to_block(return_block);
        builder.seal_block(return_block);
        let return_values = if scope.return_var.is_some() {
            vec![builder.block_params(return_block)[0]]
        } else {
            Vec::new()
        };
        builder.ins().return_(&return_values);
        builder.seal_all_blocks();
        builder.finalize();
        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| {
                CompileError::new(format!(
                    "failed to compile function `{}`: {e}",
                    function.name
                ))
            })?;
        Ok(())
    }

    fn signature_for(&self, function: &Function) -> Result<ir::Signature, CompileError> {
        let mut signature = self.module.make_signature();
        for param in &function.params {
            signature
                .params
                .push(AbiParam::new(self.type_of(&param.ty)?));
        }
        if !matches!(function.return_type, Type::Void) {
            signature
                .returns
                .push(AbiParam::new(self.type_of(&function.return_type)?));
        }
        Ok(signature)
    }

    fn symbol_for(&self, function: &Function) -> String {
        function
            .extern_name
            .clone()
            .or_else(|| self.info.function_symbols.get(&function.name).cloned())
            .unwrap_or_else(|| function.name.clone())
    }

    fn emit_block(
        &mut self,
        builder: &mut FunctionBuilder,
        body: &[Stmt],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        for stmt in body {
            if current_block_terminated(builder) {
                break;
            }
            self.emit_stmt(builder, stmt, function, scope)?;
        }
        Ok(())
    }

    fn emit_stmt(
        &mut self,
        builder: &mut FunctionBuilder,
        stmt: &Stmt,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        match stmt {
            Stmt::Defer { .. } => {
                return Err(CompileError::new(
                    "native backend does not yet support defer; use -c for the C backend",
                ));
            }
            Stmt::VarDecl {
                mutable: _,
                name,
                declared_type,
                init,
                ..
            } => {
                let ty = declared_type
                    .clone()
                    .or_else(|| {
                        self.info
                            .locals
                            .get(&function.name)
                            .and_then(|locals| locals.get(name))
                            .cloned()
                    })
                    .ok_or_else(|| CompileError::new(format!("missing type for local `{name}`")))?;
                let value = self.emit_expr(builder, init, Some(&ty), function, scope)?;
                let clif_ty = self.type_of(&ty)?;
                let value = self.coerce_value(builder, value, clif_ty, &ty)?;
                let var = builder.declare_var(clif_ty);
                builder.def_var(var, value);
                scope.vars.insert(name.clone(), (var, ty));
            }
            Stmt::Assign { target, value, .. } => {
                let target_ty = infer_codegen_expr_type(target, function, self.info)?;
                let value = self.emit_expr(builder, value, Some(&target_ty), function, scope)?;
                self.assign_place(builder, target, value, function, scope)?;
            }
            Stmt::AddAssign { target, value, .. } => {
                self.emit_compound_assign(builder, target, value, BinaryOp::Add, function, scope)?
            }
            Stmt::SubAssign { target, value, .. } => self.emit_compound_assign(
                builder,
                target,
                value,
                BinaryOp::Subtract,
                function,
                scope,
            )?,
            Stmt::MulAssign { target, value, .. } => self.emit_compound_assign(
                builder,
                target,
                value,
                BinaryOp::Multiply,
                function,
                scope,
            )?,
            Stmt::DivAssign { target, value, .. } => self.emit_compound_assign(
                builder,
                target,
                value,
                BinaryOp::Divide,
                function,
                scope,
            )?,
            Stmt::BitAndAssign { target, value, .. } => self.emit_compound_assign(
                builder,
                target,
                value,
                BinaryOp::BitAnd,
                function,
                scope,
            )?,
            Stmt::BitOrAssign { target, value, .. } => {
                self.emit_compound_assign(builder, target, value, BinaryOp::BitOr, function, scope)?
            }
            Stmt::BitXorAssign { target, value, .. } => self.emit_compound_assign(
                builder,
                target,
                value,
                BinaryOp::BitXor,
                function,
                scope,
            )?,
            Stmt::Increment { target, .. } => {
                let one = builder.ins().iconst(types::I64, 1);
                self.emit_compound_assign_value(
                    builder,
                    target,
                    one,
                    BinaryOp::Add,
                    function,
                    scope,
                )?
            }
            Stmt::Decrement { target, .. } => {
                let one = builder.ins().iconst(types::I64, 1);
                self.emit_compound_assign_value(
                    builder,
                    target,
                    one,
                    BinaryOp::Subtract,
                    function,
                    scope,
                )?
            }
            Stmt::Assert { .. } => {
                return Err(CompileError::new(
                    "native backend does not yet support assertions; use -c for the C backend",
                ));
            }
            Stmt::Return { value, .. } => {
                let Some((return_var, return_ty)) = scope.return_var.clone() else {
                    builder.ins().return_(&[]);
                    return Ok(());
                };
                let value = match value {
                    Some(value) => {
                        self.emit_expr(builder, value, Some(&return_ty), function, scope)?
                    }
                    None => builder.ins().iconst(types::I32, 0),
                };
                let clif_ty = self.type_of(&return_ty)?;
                let value = self.coerce_value(builder, value, clif_ty, &return_ty)?;
                builder.def_var(return_var, value);
                builder.ins().jump(scope.return_block, &[value.into()]);
            }
            Stmt::Block(body) => self.emit_block(builder, body, function, scope)?,
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                let cond = self.emit_expr(builder, condition, None, function, scope)?;
                let cond = self.to_bool(builder, cond)?;
                let then_block = self.new_block(builder);
                let else_block = self.new_block(builder);
                let merge_block = self.new_block(builder);
                builder.ins().brif(cond, then_block, &[], else_block, &[]);
                builder.switch_to_block(then_block);
                builder.seal_block(then_block);
                self.emit_block(builder, then_body, function, scope)?;
                if !current_block_terminated(builder) {
                    builder.ins().jump(merge_block, &[]);
                }
                builder.switch_to_block(else_block);
                builder.seal_block(else_block);
                self.emit_block(builder, else_body, function, scope)?;
                if !current_block_terminated(builder) {
                    builder.ins().jump(merge_block, &[]);
                }
                builder.switch_to_block(merge_block);
                builder.seal_block(merge_block);
            }
            Stmt::Match { .. } => {
                return Err(CompileError::new(
                    "native backend does not yet support match; use -c for the C backend",
                ));
            }
            Stmt::Expr { expr, .. } => {
                if matches!(expr, Expr::Pack(_)) {
                    return Err(CompileError::new("unexpected packed expression"));
                }
                let _ = self.emit_expr(builder, expr, None, function, scope)?;
            }
            Stmt::ForRange {
                var_name,
                start,
                end,
                body,
                ..
            } => self.emit_for_range(builder, var_name, start, end, body, function, scope)?,
            Stmt::ForEach { .. } => {
                return Err(CompileError::new(
                    "native backend does not yet support for-each; use -c for the C backend",
                ));
            }
            Stmt::ForClassic {
                var_name,
                init,
                condition,
                increment,
                body,
                ..
            } => self.emit_for_classic(
                builder, var_name, init, condition, increment, body, function, scope,
            )?,
            Stmt::While {
                condition, body, ..
            } => {
                let cond_block = self.new_block(builder);
                let body_block = self.new_block(builder);
                let after_block = self.new_block(builder);
                builder.ins().jump(cond_block, &[]);
                builder.switch_to_block(cond_block);
                let cond = self.emit_expr(builder, condition, None, function, scope)?;
                let cond = self.to_bool(builder, cond)?;
                builder.ins().brif(cond, body_block, &[], after_block, &[]);
                builder.switch_to_block(body_block);
                builder.seal_block(body_block);
                scope.loops.push(LoopContext {
                    break_block: after_block,
                    continue_block: cond_block,
                });
                self.emit_block(builder, body, function, scope)?;
                scope.loops.pop();
                if !current_block_terminated(builder) {
                    builder.ins().jump(cond_block, &[]);
                }
                builder.seal_block(cond_block);
                builder.switch_to_block(after_block);
                builder.seal_block(after_block);
            }
            Stmt::Loop { body, .. } => {
                let body_block = self.new_block(builder);
                let after_block = self.new_block(builder);
                builder.ins().jump(body_block, &[]);
                builder.switch_to_block(body_block);
                scope.loops.push(LoopContext {
                    break_block: after_block,
                    continue_block: body_block,
                });
                self.emit_block(builder, body, function, scope)?;
                scope.loops.pop();
                if !current_block_terminated(builder) {
                    builder.ins().jump(body_block, &[]);
                }
                builder.seal_block(body_block);
                builder.switch_to_block(after_block);
                builder.seal_block(after_block);
            }
            Stmt::Continue { .. } => {
                let ctx = scope
                    .loops
                    .last()
                    .copied()
                    .ok_or_else(|| CompileError::new("continue outside of a loop"))?;
                builder.ins().jump(ctx.continue_block, &[]);
            }
            Stmt::Break { .. } => {
                let ctx = scope
                    .loops
                    .last()
                    .copied()
                    .ok_or_else(|| CompileError::new("break outside of a loop"))?;
                builder.ins().jump(ctx.break_block, &[]);
            }
        }
        Ok(())
    }

    fn emit_for_range(
        &mut self,
        builder: &mut FunctionBuilder,
        var_name: &str,
        start: &Expr,
        end: &Expr,
        body: &[Stmt],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let var_ty = self
            .info
            .locals
            .get(&function.name)
            .and_then(|locals| locals.get(var_name))
            .cloned()
            .unwrap_or(Type::I32);
        let clif_ty = self.type_of(&var_ty)?;
        let start_value = self.emit_expr(builder, start, Some(&var_ty), function, scope)?;
        let start_value = self.coerce_value(builder, start_value, clif_ty, &var_ty)?;
        let end_value = self.emit_expr(builder, end, Some(&var_ty), function, scope)?;
        let end_value = self.coerce_value(builder, end_value, clif_ty, &var_ty)?;
        let var = builder.declare_var(clif_ty);
        builder.def_var(var, start_value);
        scope
            .vars
            .insert(var_name.to_string(), (var, var_ty.clone()));
        let cond_block = self.new_block(builder);
        let body_block = self.new_block(builder);
        let inc_block = self.new_block(builder);
        let after_block = self.new_block(builder);
        builder.ins().jump(cond_block, &[]);
        builder.switch_to_block(cond_block);
        let current = builder.use_var(var);
        let signed = is_codegen_signed_integer_type(&var_ty);
        let cond = builder.ins().icmp(
            if signed {
                ir::condcodes::IntCC::SignedLessThan
            } else {
                ir::condcodes::IntCC::UnsignedLessThan
            },
            current,
            end_value,
        );
        builder.ins().brif(cond, body_block, &[], after_block, &[]);
        builder.switch_to_block(body_block);
        builder.seal_block(body_block);
        scope.loops.push(LoopContext {
            break_block: after_block,
            continue_block: inc_block,
        });
        self.emit_block(builder, body, function, scope)?;
        scope.loops.pop();
        if !current_block_terminated(&builder) {
            builder.ins().jump(inc_block, &[]);
        }
        builder.switch_to_block(inc_block);
        builder.seal_block(inc_block);
        let current = builder.use_var(var);
        let one = builder.ins().iconst(clif_ty, 1);
        let next = builder.ins().iadd(current, one);
        builder.def_var(var, next);
        builder.ins().jump(cond_block, &[]);
        builder.seal_block(cond_block);
        builder.switch_to_block(after_block);
        builder.seal_block(after_block);
        Ok(())
    }

    fn emit_for_classic(
        &mut self,
        builder: &mut FunctionBuilder,
        var_name: &str,
        init: &Expr,
        condition: &Expr,
        increment: &Expr,
        body: &[Stmt],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let var_ty = self
            .info
            .locals
            .get(&function.name)
            .and_then(|locals| locals.get(var_name))
            .cloned()
            .unwrap_or(Type::I32);
        let clif_ty = self.type_of(&var_ty)?;
        let init_value = self.emit_expr(builder, init, Some(&var_ty), function, scope)?;
        let init_value = self.coerce_value(builder, init_value, clif_ty, &var_ty)?;
        let var = builder.declare_var(clif_ty);
        builder.def_var(var, init_value);
        scope.vars.insert(var_name.to_string(), (var, var_ty));
        let cond_block = self.new_block(builder);
        let body_block = self.new_block(builder);
        let inc_block = self.new_block(builder);
        let after_block = self.new_block(builder);
        builder.ins().jump(cond_block, &[]);
        builder.switch_to_block(cond_block);
        let cond = self.emit_expr(builder, condition, None, function, scope)?;
        let cond = self.to_bool(builder, cond)?;
        builder.ins().brif(cond, body_block, &[], after_block, &[]);
        builder.switch_to_block(body_block);
        builder.seal_block(body_block);
        scope.loops.push(LoopContext {
            break_block: after_block,
            continue_block: inc_block,
        });
        self.emit_block(builder, body, function, scope)?;
        scope.loops.pop();
        if !current_block_terminated(builder) {
            builder.ins().jump(inc_block, &[]);
        }
        builder.switch_to_block(inc_block);
        builder.seal_block(inc_block);
        let _ = self.emit_expr(builder, increment, None, function, scope)?;
        builder.ins().jump(cond_block, &[]);
        builder.seal_block(cond_block);
        builder.switch_to_block(after_block);
        builder.seal_block(after_block);
        Ok(())
    }

    fn emit_compound_assign(
        &mut self,
        builder: &mut FunctionBuilder,
        target: &Expr,
        value: &Expr,
        op: BinaryOp,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let target_ty = infer_codegen_expr_type(target, function, self.info)?;
        let rhs = self.emit_expr(builder, value, Some(&target_ty), function, scope)?;
        self.emit_compound_assign_value(builder, target, rhs, op, function, scope)
    }

    fn emit_compound_assign_value(
        &mut self,
        builder: &mut FunctionBuilder,
        target: &Expr,
        rhs: Value,
        op: BinaryOp,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let target_ty = infer_codegen_expr_type(target, function, self.info)?;
        let current = self.emit_expr(builder, target, Some(&target_ty), function, scope)?;
        let result = self.emit_binary_values(builder, current, rhs, op, &target_ty, &target_ty)?;
        self.assign_place(builder, target, result, function, scope)
    }

    fn emit_expr(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: &Expr,
        hint: Option<&Type>,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        match expr {
            Expr::Int(value) => {
                let ty = hint
                    .map(|ty| self.type_of(ty))
                    .transpose()?
                    .unwrap_or(types::I32);
                if ty.is_float() {
                    let value = *value as f64;
                    return Ok(if ty == types::F32 {
                        builder.ins().f32const(value as f32)
                    } else {
                        builder.ins().f64const(value)
                    });
                }
                Ok(builder.ins().iconst(ty, *value as i64))
            }
            Expr::Char(value) => Ok(builder.ins().iconst(types::I8, *value as i64)),
            Expr::Bool(value) => Ok(builder.ins().iconst(types::I8, i64::from(*value))),
            Expr::Float(value) => {
                let ty = hint
                    .map(|ty| self.type_of(ty))
                    .transpose()?
                    .unwrap_or(types::F64);
                Ok(if ty == types::F32 {
                    builder.ins().f32const(*value as f32)
                } else {
                    builder.ins().f64const(*value)
                })
            }
            Expr::String(value) => {
                let (data_id, _) = self
                    .strings
                    .get(value)
                    .copied()
                    .ok_or_else(|| CompileError::new("missing string constant"))?;
                let gv = self.module.declare_data_in_func(data_id, builder.func);
                Ok(builder.ins().global_value(self.pointer_type, gv))
            }
            Expr::None => Ok(builder.ins().iconst(self.pointer_type, 0)),
            Expr::Path(path) => self.emit_path(builder, path, function, scope),
            Expr::Unary { op, expr } => {
                let value = self.emit_expr(builder, expr, hint, function, scope)?;
                match op {
                    UnaryOp::Neg => {
                        let ty = builder.func.dfg.value_type(value);
                        Ok(if ty.is_float() {
                            builder.ins().fneg(value)
                        } else {
                            builder.ins().ineg(value)
                        })
                    }
                    UnaryOp::LogicalNot => {
                        let cond = self.to_bool(builder, value)?;
                        let one = builder.ins().iconst(types::I8, 1);
                        Ok(builder.ins().bxor(cond, one))
                    }
                    UnaryOp::BitNot => Ok(builder.ins().bnot(value)),
                    UnaryOp::PostfixInc | UnaryOp::PostfixDec => {
                        let ty = infer_codegen_expr_type(expr, function, self.info)?;
                        let clif_ty = self.type_of(&ty)?;
                        let one = if clif_ty.is_float() {
                            builder.ins().f64const(1.0)
                        } else {
                            builder.ins().iconst(clif_ty, 1)
                        };
                        let next = self.emit_binary_values(
                            builder,
                            value,
                            one,
                            if *op == UnaryOp::PostfixInc {
                                BinaryOp::Add
                            } else {
                                BinaryOp::Subtract
                            },
                            &ty,
                            &ty,
                        )?;
                        self.assign_place(builder, expr, next, function, scope)?;
                        Ok(value)
                    }
                }
            }
            Expr::Binary { lhs, op, rhs } => {
                if matches!(op, BinaryOp::LogicalAnd | BinaryOp::LogicalOr) {
                    return self.emit_logical(builder, lhs, *op, rhs, function, scope);
                }
                let lhs_ty = infer_codegen_expr_type(lhs, function, self.info)?;
                let rhs_ty = infer_codegen_expr_type(rhs, function, self.info)?;
                let mut result_ty = infer_codegen_expr_type(expr, function, self.info)?;
                if matches!(
                    op,
                    BinaryOp::LessThan
                        | BinaryOp::LessEqual
                        | BinaryOp::GreaterThan
                        | BinaryOp::GreaterEqual
                        | BinaryOp::Equal
                        | BinaryOp::NotEqual
                ) {
                    result_ty = Type::Bool;
                }
                let lhs_value = self.emit_expr(builder, lhs, Some(&lhs_ty), function, scope)?;
                let rhs_value = self.emit_expr(builder, rhs, Some(&rhs_ty), function, scope)?;
                self.emit_binary_values(builder, lhs_value, rhs_value, *op, &lhs_ty, &result_ty)
            }
            Expr::Cast { expr, ty } => {
                let source_ty = infer_codegen_expr_type(expr, function, self.info)?;
                let value = self.emit_expr(builder, expr, Some(&source_ty), function, scope)?;
                let target = self.type_of(ty)?;
                self.cast_value(builder, value, &source_ty, ty, target)
            }
            Expr::SizeOf(ty) => {
                let size = self.type_size_align(ty)?.0;
                Ok(builder.ins().iconst(self.pointer_type, size as i64))
            }
            Expr::BitCast { expr, ty } => {
                let source_ty = infer_codegen_expr_type(expr, function, self.info)?;
                let value = self.emit_expr(builder, expr, Some(&source_ty), function, scope)?;
                let target = self.type_of(ty)?;
                self.cast_value(builder, value, &source_ty, ty, target)
            }
            Expr::Call { callee, args } => self.emit_call(builder, callee, args, function, scope),
            Expr::BuiltinCall { name, args } => {
                self.emit_builtin(builder, name, args, function, scope)
            }
            Expr::StructInit { name, fields, .. } => {
                self.emit_struct_init(builder, name, fields, function, scope)
            }
            Expr::FieldAccess { .. } => {
                let (address, ty) = self.lvalue(builder, expr, function, scope)?;
                let clif_ty = self.type_of(&ty)?;
                Ok(builder.ins().load(clif_ty, MemFlags::new(), address, 0))
            }
            Expr::Index { .. } => {
                let (address, ty) = self.lvalue(builder, expr, function, scope)?;
                let clif_ty = self.type_of(&ty)?;
                Ok(builder.ins().load(clif_ty, MemFlags::new(), address, 0))
            }
            Expr::MethodCall { .. } => Err(CompileError::new(
                "native backend does not yet support methods; use -c for the C backend",
            )),
            Expr::Specialize { .. } => Err(CompileError::new(
                "generic specialization must be resolved before native code generation",
            )),
            Expr::Error { .. } | Expr::Try(_) => Err(CompileError::new(
                "native backend does not yet support result propagation; use -c for the C backend",
            )),
            Expr::Pack(_) => Err(CompileError::new("packed expression outside of @print")),
            Expr::ListLiteral(_) => Err(CompileError::new(
                "native backend does not yet support list literals; use -c for the C backend",
            )),
        }
    }

    fn emit_path(
        &mut self,
        builder: &mut FunctionBuilder,
        path: &[String],
        _function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        if path.len() == 1 {
            let name = &path[0];
            if let Some((var, _)) = scope.vars.get(name) {
                return Ok(builder.use_var(*var));
            }
            let function_name = &path[0];
            if let Some(func_id) = self.function_ids.get(function_name).copied() {
                let func_ref = self.module.declare_func_in_func(func_id, builder.func);
                return Ok(builder.ins().func_addr(self.pointer_type, func_ref));
            }
            if self.info.globals.contains_key(name) {
                return Err(CompileError::new(
                    "native backend does not yet support globals",
                ));
            }
        }
        Err(CompileError::new(format!(
            "unsupported path `{}` in native code generation",
            path.join(".")
        )))
    }

    fn emit_call(
        &mut self,
        builder: &mut FunctionBuilder,
        callee: &Expr,
        args: &[Expr],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        if let Expr::Path(path) = callee {
            if path.len() == 1 {
                let fn_ptr_ty = scope.vars.get(&path[0]).map(|(_, ty)| ty.clone());
                if let Some(Type::FnPtr(param_types, ret)) = fn_ptr_ty {
                    let fn_ptr = self.emit_path(builder, path, function, scope)?;
                    let mut values = Vec::new();
                    for (arg, ty) in args.iter().zip(param_types.iter()) {
                        let value = self.emit_expr(builder, arg, Some(ty), function, scope)?;
                        let clif_ty = self.type_of(ty)?;
                        values.push(self.coerce_value(builder, value, clif_ty, ty)?);
                    }
                    let signature = self.function_pointer_signature(&param_types, ret.as_ref())?;
                    let sig_ref = builder.import_signature(signature);
                    let call = builder.ins().call_indirect(sig_ref, fn_ptr, &values);
                    return Ok(self.call_result(builder, call, ret.as_ref()));
                }
            }
        }
        let Some(path) = callee.callee_path() else {
            return Err(CompileError::new(
                "native backend only supports direct function calls",
            ));
        };
        let function_name = path.join(".");
        let func_id = if let Some(func_id) = self.function_ids.get(&function_name).copied() {
            func_id
        } else if path.len() == 1 {
            let name = &path[0];
            let fn_ptr_ty = scope.vars.get(name).map(|(_, ty)| ty.clone());
            if let Some(Type::FnPtr(param_types, ret)) = fn_ptr_ty {
                let fn_ptr = self.emit_path(builder, &path, function, scope)?;
                let mut values = Vec::new();
                for (arg, ty) in args.iter().zip(param_types.iter()) {
                    let value = self.emit_expr(builder, arg, Some(ty), function, scope)?;
                    let clif_ty = self.type_of(ty)?;
                    values.push(self.coerce_value(builder, value, clif_ty, ty)?);
                }
                let signature = self.function_pointer_signature(&param_types, ret.as_ref())?;
                let sig_ref = builder.import_signature(signature);
                let call = builder.ins().call_indirect(sig_ref, fn_ptr, &values);
                return Ok(self.call_result(builder, call, ret.as_ref()));
            }
            return Err(CompileError::new(format!("unknown function `{name}`")));
        } else {
            return Err(CompileError::new(format!(
                "unknown function `{function_name}`"
            )));
        };
        let signature = self
            .info
            .functions
            .get(&function_name)
            .cloned()
            .ok_or_else(|| CompileError::new(format!("unknown function `{function_name}`")))?;
        let mut values = Vec::new();
        for (arg, ty) in args.iter().zip(signature.params.iter()) {
            let value = self.emit_expr(builder, arg, Some(ty), function, scope)?;
            let clif_ty = self.type_of(ty)?;
            values.push(self.coerce_value(builder, value, clif_ty, ty)?);
        }
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        let call = builder.ins().call(func_ref, &values);
        Ok(self.call_result(builder, call, &signature.return_type))
    }

    fn call_result(
        &self,
        builder: &mut FunctionBuilder,
        call: ir::Inst,
        return_type: &Type,
    ) -> Value {
        if matches!(return_type, Type::Void) {
            builder.ins().iconst(types::I32, 0)
        } else {
            builder.inst_results(call)[0]
        }
    }

    fn function_pointer_signature(
        &self,
        params: &[Type],
        ret: &Type,
    ) -> Result<ir::Signature, CompileError> {
        let mut signature = self.module.make_signature();
        for ty in params {
            signature.params.push(AbiParam::new(self.type_of(ty)?));
        }
        if !matches!(ret, Type::Void) {
            signature.returns.push(AbiParam::new(self.type_of(ret)?));
        }
        Ok(signature)
    }

    fn emit_builtin(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        args: &[Expr],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        match name {
            "puts" => {
                let value = self.emit_expr(builder, &args[0], None, function, scope)?;
                let callee = self.extern_function(
                    "scar_puts",
                    &[Type::Ref(Box::new(Type::U8))],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value]);
                Ok(builder.ins().iconst(types::I32, 0))
            }
            "print" => self.emit_print(builder, args, function, scope),
            "flush" => {
                let callee =
                    self.extern_function("fflush", &[Type::Ref(Box::new(Type::U8))], &Type::I32)?;
                let null = builder.ins().iconst(self.pointer_type, 0);
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let call = builder.ins().call(func_ref, &[null]);
                Ok(self.call_result(builder, call, &Type::I32))
            }
            "addr" => self.emit_addr(builder, &args[0], function, scope),
            "deref" => {
                let arg_ty = infer_codegen_expr_type(&args[0], function, self.info)?;
                let inner = match arg_ty {
                    Type::Ref(inner) | Type::Mut(inner) => *inner,
                    other => {
                        return Err(CompileError::new(format!(
                            "@deref requires a reference, got {}",
                            describe_type(&other)
                        )));
                    }
                };
                let pointer = self.emit_expr(builder, &args[0], None, function, scope)?;
                let clif_ty = self.type_of(&inner)?;
                Ok(builder.ins().load(clif_ty, MemFlags::new(), pointer, 0))
            }
            "zeroed" => {
                if args.is_empty() {
                    return Err(CompileError::new(
                        "native backend does not yet support bare @zeroed; use -c for the C backend",
                    ));
                }
                let ty = infer_codegen_expr_type(&args[0], function, self.info)?;
                let clif_ty = self.type_of(&ty)?;
                Ok(builder.ins().iconst(clif_ty, 0))
            }
            "alloc" => {
                let size =
                    self.emit_expr(builder, &args[0], Some(&Type::Usize), function, scope)?;
                let size = self.coerce_value(builder, size, self.pointer_type, &Type::Usize)?;
                let callee = self.extern_function(
                    "malloc",
                    &[Type::Usize],
                    &Type::Ref(Box::new(Type::Void)),
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let call = builder.ins().call(func_ref, &[size]);
                Ok(self.call_result(builder, call, &Type::Ref(Box::new(Type::Void))))
            }
            "realloc" => {
                let ptr = self.emit_expr(builder, &args[0], None, function, scope)?;
                let size =
                    self.emit_expr(builder, &args[1], Some(&Type::Usize), function, scope)?;
                let size = self.coerce_value(builder, size, self.pointer_type, &Type::Usize)?;
                let callee = self.extern_function(
                    "realloc",
                    &[Type::Ref(Box::new(Type::Void)), Type::Usize],
                    &Type::Ref(Box::new(Type::Void)),
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let call = builder.ins().call(func_ref, &[ptr, size]);
                Ok(self.call_result(builder, call, &Type::Ref(Box::new(Type::Void))))
            }
            "free" => {
                let ptr = self.emit_expr(builder, &args[0], None, function, scope)?;
                let callee =
                    self.extern_function("free", &[Type::Ref(Box::new(Type::Void))], &Type::Void)?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[ptr]);
                Ok(builder.ins().iconst(types::I32, 0))
            }
            "memcpy" | "memset" => {
                let dest = self.emit_expr(builder, &args[0], None, function, scope)?;
                let src = self.emit_expr(builder, &args[1], None, function, scope)?;
                let len = self.emit_expr(builder, &args[2], Some(&Type::Usize), function, scope)?;
                let len = self.coerce_value(builder, len, self.pointer_type, &Type::Usize)?;
                let (params, src) = if name == "memcpy" {
                    (
                        vec![
                            Type::Ref(Box::new(Type::Void)),
                            Type::Ref(Box::new(Type::Void)),
                            Type::Usize,
                        ],
                        src,
                    )
                } else {
                    (
                        vec![Type::Ref(Box::new(Type::Void)), Type::I32, Type::Usize],
                        self.coerce_value(builder, src, types::I32, &Type::I32)?,
                    )
                };
                let callee =
                    self.extern_function(name, &params, &Type::Ref(Box::new(Type::Void)))?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let call = builder.ins().call(func_ref, &[dest, src, len]);
                Ok(self.call_result(builder, call, &Type::Ref(Box::new(Type::Void))))
            }
            "neg" => {
                let value = self.emit_expr(builder, &args[0], None, function, scope)?;
                let ty = builder.func.dfg.value_type(value);
                Ok(if ty.is_float() {
                    builder.ins().fneg(value)
                } else {
                    builder.ins().ineg(value)
                })
            }
            "shl" | "shr" => {
                let lhs = self.emit_expr(builder, &args[0], None, function, scope)?;
                let rhs = self.emit_expr(builder, &args[1], None, function, scope)?;
                Ok(if name == "shl" {
                    builder.ins().ishl(lhs, rhs)
                } else {
                    builder.ins().ushr(lhs, rhs)
                })
            }
            "add" => {
                let arg_ty = infer_codegen_expr_type(&args[0], function, self.info)?;
                let pointer = self.emit_expr(builder, &args[0], None, function, scope)?;
                let offset = self.emit_expr(builder, &args[1], None, function, scope)?;
                let scale = match arg_ty {
                    Type::Ref(inner) | Type::Mut(inner) => self.type_size_align(&inner)?.0.max(1),
                    Type::Named(name) => self.type_size_align(&Type::Named(name))?.0.max(1),
                    _ => 1,
                };
                let scale = builder.ins().iconst(types::I64, scale as i64);
                let offset = self.coerce_value(builder, offset, types::I64, &Type::I64)?;
                let offset = builder.ins().imul(offset, scale);
                Ok(builder.ins().iadd(pointer, offset))
            }
            "as_mut" => self.emit_expr(builder, &args[0], None, function, scope),
            "call" => {
                let fn_ty = infer_codegen_expr_type(&args[0], function, self.info)?;
                let Type::FnPtr(param_types, ret) = fn_ty else {
                    return Err(CompileError::new("@call expects a function pointer"));
                };
                let fn_ptr = self.emit_expr(builder, &args[0], None, function, scope)?;
                let mut values = Vec::new();
                for (arg, ty) in args[1..].iter().zip(param_types.iter()) {
                    let value = self.emit_expr(builder, arg, Some(ty), function, scope)?;
                    let clif_ty = self.type_of(ty)?;
                    values.push(self.coerce_value(builder, value, clif_ty, ty)?);
                }
                let signature = self.function_pointer_signature(&param_types, &ret)?;
                let sig_ref = builder.import_signature(signature);
                let call = builder.ins().call_indirect(sig_ref, fn_ptr, &values);
                Ok(self.call_result(builder, call, &ret))
            }
            other => Err(CompileError::new(format!(
                "native backend does not yet support builtin @{other}; use -c for the C backend"
            ))),
        }
    }

    fn intern_string(&mut self, value: &str) -> Result<(DataId, usize), CompileError> {
        if let Some(existing) = self.strings.get(value) {
            return Ok(*existing);
        }
        let mut bytes = value.as_bytes().to_vec();
        bytes.push(0);
        let len = bytes.len();
        let name = format!("__scar_str_{}", self.next_data);
        self.next_data += 1;
        let data_id = self
            .module
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(|e| CompileError::new(e.to_string()))?;
        let mut desc = DataDescription::new();
        desc.define(bytes.into_boxed_slice());
        desc.set_align(1);
        self.module
            .define_data(data_id, &desc)
            .map_err(|e| CompileError::new(e.to_string()))?;
        self.strings.insert(value.to_string(), (data_id, len));
        self.data_ids.insert(name, data_id);
        Ok((data_id, len))
    }

    fn emit_print(
        &mut self,
        builder: &mut FunctionBuilder,
        args: &[Expr],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        let Expr::String(format) = &args[0] else {
            return Err(CompileError::new(
                "@print requires a string literal as its first argument",
            ));
        };
        let mut flattened = Vec::new();
        for arg in &args[1..] {
            if let Expr::Pack(values) = arg {
                flattened.extend(values.iter());
            } else {
                flattened.push(arg);
            }
        }
        let mut literal = String::new();
        let mut arg_index = 0;
        let chars: Vec<char> = format.chars().collect();
        let mut index = 0;
        while index < chars.len() {
            if chars[index] == '{' {
                let start = index + 1;
                let mut end = start;
                while end < chars.len() && chars[end] != '}' {
                    end += 1;
                }
                if end >= chars.len() {
                    return Err(CompileError::new("unterminated @print format marker"));
                }
                if !literal.is_empty() {
                    self.emit_print_string(builder, &literal)?;
                    literal.clear();
                }
                let marker: String = chars[start..end].iter().collect();
                let arg = flattened.get(arg_index).copied().ok_or_else(|| {
                    CompileError::new("@print format expects more values than were provided")
                })?;
                let ty = infer_codegen_expr_type(arg, function, self.info)?;
                self.emit_print_value(builder, &marker, arg, &ty, function, scope)?;
                arg_index += 1;
                index = end + 1;
                continue;
            }
            literal.push(chars[index]);
            index += 1;
        }
        if !literal.is_empty() {
            self.emit_print_string(builder, &literal)?;
        }
        if arg_index < flattened.len() {
            return Err(CompileError::new(
                "@print format expects more values than were provided",
            ));
        }
        Ok(builder.ins().iconst(types::I32, 0))
    }

    fn emit_print_string(
        &mut self,
        builder: &mut FunctionBuilder,
        value: &str,
    ) -> Result<(), CompileError> {
        let (data_id, _) = self.intern_string(value)?;
        let gv = self.module.declare_data_in_func(data_id, builder.func);
        let pointer = builder.ins().global_value(self.pointer_type, gv);
        let callee = self.extern_function(
            "scar_print_str",
            &[Type::Ref(Box::new(Type::U8))],
            &Type::Void,
        )?;
        let func_ref = self.module.declare_func_in_func(callee, builder.func);
        let _ = builder.ins().call(func_ref, &[pointer]);
        Ok(())
    }

    fn emit_print_value(
        &mut self,
        builder: &mut FunctionBuilder,
        marker: &str,
        arg: &Expr,
        ty: &Type,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let width_text: String = marker.chars().take_while(|c| c.is_ascii_digit()).collect();
        let width = width_text.parse::<i32>().unwrap_or(0);
        let base = marker.trim_start_matches(|c: char| c.is_ascii_digit());
        let value = self.emit_expr(builder, arg, Some(ty), function, scope)?;
        let unsigned = matches!(
            ty,
            Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize
        );
        match base {
            "d" | "ld" | "lld" => {
                let value = self.coerce_value(builder, value, types::I64, &Type::I64)?;
                let width = builder.ins().iconst(types::I32, width as i64);
                let signed = builder
                    .ins()
                    .iconst(types::I32, if unsigned { 1 } else { 0 });
                let callee = self.extern_function(
                    "scar_print_int",
                    &[Type::I64, Type::I32, Type::I32],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value, width, signed]);
            }
            "u" | "lu" | "llu" | "zu" => {
                let value = self.coerce_value(builder, value, types::I64, &Type::I64)?;
                let width = builder.ins().iconst(types::I32, width as i64);
                let unsigned = builder.ins().iconst(types::I32, 1);
                let callee = self.extern_function(
                    "scar_print_int",
                    &[Type::I64, Type::I32, Type::I32],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value, width, unsigned]);
            }
            "x" | "lx" | "llx" | "X" | "lX" | "llX" | "o" | "lo" | "llo" => {
                let value = self.coerce_value(builder, value, types::I64, &Type::I64)?;
                let width = builder.ins().iconst(types::I32, width as i64);
                let mode = if base.ends_with('x') {
                    0
                } else if base.ends_with('X') {
                    1
                } else {
                    2
                };
                let mode = builder.ins().iconst(types::I32, mode);
                let callee = self.extern_function(
                    "scar_print_radix",
                    &[Type::I64, Type::I32, Type::I32],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value, width, mode]);
            }
            "f" | "lf" | "e" | "E" | "g" | "G" => {
                let value = self.coerce_value(builder, value, types::F64, &Type::F64)?;
                let width = builder.ins().iconst(types::I32, width as i64);
                let mode = match base {
                    "e" => 1,
                    "E" => 2,
                    "g" => 3,
                    "G" => 4,
                    _ => 0,
                };
                let mode = builder.ins().iconst(types::I32, mode);
                let callee = self.extern_function(
                    "scar_print_float",
                    &[Type::F64, Type::I32, Type::I32],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value, width, mode]);
            }
            "b" => {
                let value = self.coerce_value(builder, value, types::I32, &Type::Bool)?;
                let callee = self.extern_function("scar_print_bool", &[Type::I32], &Type::Void)?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value]);
            }
            "p" => {
                let callee = self.extern_function(
                    "scar_print_ptr",
                    &[Type::Ref(Box::new(Type::Void))],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value]);
            }
            "s" => {
                let callee = self.extern_function(
                    "scar_print_str",
                    &[Type::Ref(Box::new(Type::U8))],
                    &Type::Void,
                )?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value]);
            }
            "c" => {
                let value = self.coerce_value(builder, value, types::I32, &Type::U8)?;
                let callee = self.extern_function("scar_print_char", &[Type::I32], &Type::Void)?;
                let func_ref = self.module.declare_func_in_func(callee, builder.func);
                let _ = builder.ins().call(func_ref, &[value]);
            }
            other => {
                return Err(CompileError::new(format!(
                    "unsupported @print marker `{{{other}}}` in native backend"
                )));
            }
        }
        Ok(())
    }

    fn emit_addr(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: &Expr,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        if let Expr::Path(path) = expr {
            if path.len() == 1 {
                if let Some((var, ty)) = scope.vars.get(&path[0]).cloned() {
                    let value = builder.use_var(var);
                    if matches!(
                        ty,
                        Type::Named(_)
                            | Type::Applied(_, _)
                            | Type::List(_)
                            | Type::FixedArray(_, _)
                    ) {
                        return Ok(value);
                    }
                    let size = self.type_size_align(&ty)?.0.max(1);
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size as u32,
                        3,
                    ));
                    builder.ins().stack_store(value, slot, 0);
                    return Ok(builder.ins().stack_addr(self.pointer_type, slot, 0));
                }
            }
        }
        let deref_expr = matches!(
            expr,
            Expr::BuiltinCall { name, .. } if name == "deref"
        );
        if matches!(expr, Expr::FieldAccess { .. } | Expr::Index { .. }) || deref_expr {
            let (address, _) = self.lvalue(builder, expr, function, scope)?;
            return Ok(address);
        }
        Err(CompileError::new(
            "@addr requires an addressable expression in native code generation",
        ))
    }

    fn emit_logical(
        &mut self,
        builder: &mut FunctionBuilder,
        lhs: &Expr,
        op: BinaryOp,
        rhs: &Expr,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        let lhs_value = self.emit_expr(builder, lhs, None, function, scope)?;
        let lhs_bool = self.to_bool(builder, lhs_value)?;
        let rhs_block = self.new_block(builder);
        let short_block = self.new_block(builder);
        let end_block = self.new_block(builder);
        let result_var = builder.declare_var(types::I8);
        if op == BinaryOp::LogicalAnd {
            builder
                .ins()
                .brif(lhs_bool, rhs_block, &[], short_block, &[]);
        } else {
            builder
                .ins()
                .brif(lhs_bool, short_block, &[], rhs_block, &[]);
        }
        builder.switch_to_block(short_block);
        builder.seal_block(short_block);
        let short_value = builder
            .ins()
            .iconst(types::I8, if op == BinaryOp::LogicalAnd { 0 } else { 1 });
        builder.def_var(result_var, short_value);
        builder.ins().jump(end_block, &[]);
        builder.switch_to_block(rhs_block);
        builder.seal_block(rhs_block);
        let rhs_value = self.emit_expr(builder, rhs, None, function, scope)?;
        let rhs_bool = self.to_bool(builder, rhs_value)?;
        builder.def_var(result_var, rhs_bool);
        builder.ins().jump(end_block, &[]);
        builder.switch_to_block(end_block);
        builder.seal_block(end_block);
        Ok(builder.use_var(result_var))
    }

    fn emit_binary_values(
        &mut self,
        builder: &mut FunctionBuilder,
        lhs: Value,
        rhs: Value,
        op: BinaryOp,
        lhs_ty: &Type,
        result_ty: &Type,
    ) -> Result<Value, CompileError> {
        let lhs_clif = builder.func.dfg.value_type(lhs);
        let rhs_clif = builder.func.dfg.value_type(rhs);
        let arithmetic_ty = common_numeric_clif(lhs_clif, rhs_clif).unwrap_or(lhs_clif);
        let lhs = self.coerce_raw(builder, lhs, arithmetic_ty);
        let rhs = self.coerce_raw(builder, rhs, arithmetic_ty);
        let bits = arithmetic_ty.bits();
        let is_signed = is_codegen_signed_integer_type(lhs_ty);
        let is_float = arithmetic_ty.is_float();
        match op {
            BinaryOp::Add => Ok(if is_float {
                builder.ins().fadd(lhs, rhs)
            } else {
                builder.ins().iadd(lhs, rhs)
            }),
            BinaryOp::Subtract => Ok(if is_float {
                builder.ins().fsub(lhs, rhs)
            } else {
                builder.ins().isub(lhs, rhs)
            }),
            BinaryOp::Multiply => Ok(if is_float {
                builder.ins().fmul(lhs, rhs)
            } else {
                builder.ins().imul(lhs, rhs)
            }),
            BinaryOp::Divide => Ok(if is_float {
                builder.ins().fdiv(lhs, rhs)
            } else if is_signed {
                builder.ins().sdiv(lhs, rhs)
            } else {
                builder.ins().udiv(lhs, rhs)
            }),
            BinaryOp::Modulo => {
                if is_float {
                    return Err(CompileError::new(
                        "native backend does not yet support floating-point modulo",
                    ));
                }
                Ok(if is_signed {
                    builder.ins().srem(lhs, rhs)
                } else {
                    builder.ins().urem(lhs, rhs)
                })
            }
            BinaryOp::BitAnd => Ok(builder.ins().band(lhs, rhs)),
            BinaryOp::BitOr => Ok(builder.ins().bor(lhs, rhs)),
            BinaryOp::BitXor => Ok(builder.ins().bxor(lhs, rhs)),
            BinaryOp::ShiftLeft => Ok(builder.ins().ishl(lhs, rhs)),
            BinaryOp::ShiftRight => Ok(builder.ins().ushr(lhs, rhs)),
            BinaryOp::LogicalAnd => {
                let l = self.to_bool(builder, lhs)?;
                let r = self.to_bool(builder, rhs)?;
                Ok(builder.ins().band(l, r))
            }
            BinaryOp::LogicalOr => {
                let l = self.to_bool(builder, lhs)?;
                let r = self.to_bool(builder, rhs)?;
                Ok(builder.ins().bor(l, r))
            }
            BinaryOp::LessThan
            | BinaryOp::LessEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterEqual
            | BinaryOp::Equal
            | BinaryOp::NotEqual => {
                let condition = if is_float {
                    let cc = match op {
                        BinaryOp::LessThan => ir::condcodes::FloatCC::LessThan,
                        BinaryOp::LessEqual => ir::condcodes::FloatCC::LessThanOrEqual,
                        BinaryOp::GreaterThan => ir::condcodes::FloatCC::GreaterThan,
                        BinaryOp::GreaterEqual => ir::condcodes::FloatCC::GreaterThanOrEqual,
                        BinaryOp::Equal => ir::condcodes::FloatCC::Equal,
                        BinaryOp::NotEqual => ir::condcodes::FloatCC::NotEqual,
                        _ => unreachable!(),
                    };
                    builder.ins().fcmp(cc, lhs, rhs)
                } else {
                    let cc = match op {
                        BinaryOp::LessThan if is_signed => ir::condcodes::IntCC::SignedLessThan,
                        BinaryOp::LessThan => ir::condcodes::IntCC::UnsignedLessThan,
                        BinaryOp::LessEqual if is_signed => {
                            ir::condcodes::IntCC::SignedLessThanOrEqual
                        }
                        BinaryOp::LessEqual => ir::condcodes::IntCC::UnsignedLessThanOrEqual,
                        BinaryOp::GreaterThan if is_signed => {
                            ir::condcodes::IntCC::SignedGreaterThan
                        }
                        BinaryOp::GreaterThan => ir::condcodes::IntCC::UnsignedGreaterThan,
                        BinaryOp::GreaterEqual if is_signed => {
                            ir::condcodes::IntCC::SignedGreaterThanOrEqual
                        }
                        BinaryOp::GreaterEqual => ir::condcodes::IntCC::UnsignedGreaterThanOrEqual,
                        BinaryOp::Equal => ir::condcodes::IntCC::Equal,
                        BinaryOp::NotEqual => ir::condcodes::IntCC::NotEqual,
                        _ => unreachable!(),
                    };
                    builder.ins().icmp(cc, lhs, rhs)
                };
                let _ = bits;
                let _ = result_ty;
                Ok(condition)
            }
        }
    }

    fn cast_value(
        &self,
        builder: &mut FunctionBuilder,
        value: Value,
        source_ty: &Type,
        target_ty: &Type,
        target: ClifType,
    ) -> Result<Value, CompileError> {
        let source = builder.func.dfg.value_type(value);
        if source == target {
            return Ok(value);
        }
        if source.is_float() && target.is_float() {
            return Ok(if target == types::F32 {
                builder.ins().fdemote(target, value)
            } else {
                builder.ins().fpromote(target, value)
            });
        }
        if source.is_float() && target.is_int() {
            let signed = is_codegen_signed_integer_type(target_ty);
            return Ok(if signed {
                builder.ins().fcvt_to_sint(target, value)
            } else {
                builder.ins().fcvt_to_uint(target, value)
            });
        }
        if source.is_int() && target.is_float() {
            let signed = is_codegen_signed_integer_type(source_ty);
            return Ok(if signed {
                builder.ins().fcvt_from_sint(target, value)
            } else {
                builder.ins().fcvt_from_uint(target, value)
            });
        }
        if source.is_int() && target.is_int() {
            return Ok(self.coerce_raw(builder, value, target));
        }
        Ok(builder.ins().bitcast(target, MemFlags::new(), value))
    }

    fn coerce_value(
        &self,
        builder: &mut FunctionBuilder,
        value: Value,
        target: ClifType,
        ty: &Type,
    ) -> Result<Value, CompileError> {
        let source = builder.func.dfg.value_type(value);
        if source == target {
            return Ok(value);
        }
        if source.is_int() && target.is_int() {
            return Ok(self.coerce_raw(builder, value, target));
        }
        if source.is_float() && target.is_float() {
            return Ok(if target == types::F32 {
                builder.ins().fdemote(target, value)
            } else {
                builder.ins().fpromote(target, value)
            });
        }
        if source.is_float() && target.is_int() {
            return Ok(if is_codegen_signed_integer_type(ty) {
                builder.ins().fcvt_to_sint(target, value)
            } else {
                builder.ins().fcvt_to_uint(target, value)
            });
        }
        if source.is_int() && target.is_float() {
            return Ok(if is_codegen_signed_integer_type(ty) {
                builder.ins().fcvt_from_sint(target, value)
            } else {
                builder.ins().fcvt_from_uint(target, value)
            });
        }
        Ok(value)
    }

    fn coerce_raw(&self, builder: &mut FunctionBuilder, value: Value, target: ClifType) -> Value {
        let source = builder.func.dfg.value_type(value);
        if source == target || source.is_float() || target.is_float() {
            return value;
        }
        let source_bits = source.bits();
        let target_bits = target.bits();
        if source_bits < target_bits {
            builder.ins().uextend(target, value)
        } else if source_bits > target_bits {
            builder.ins().ireduce(target, value)
        } else {
            value
        }
    }

    fn to_bool(&self, builder: &mut FunctionBuilder, value: Value) -> Result<Value, CompileError> {
        let ty = builder.func.dfg.value_type(value);
        if ty == types::I8 {
            return Ok(value);
        }
        if ty.is_float() {
            let zero = if ty == types::F32 {
                builder.ins().f32const(0.0)
            } else {
                builder.ins().f64const(0.0)
            };
            return Ok(builder
                .ins()
                .fcmp(ir::condcodes::FloatCC::NotEqual, value, zero));
        }
        Ok(builder
            .ins()
            .icmp_imm(ir::condcodes::IntCC::NotEqual, value, 0))
    }

    fn assign_place(
        &mut self,
        builder: &mut FunctionBuilder,
        target: &Expr,
        value: Value,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(), CompileError> {
        let target_ty = infer_codegen_expr_type(target, function, self.info)?;
        let clif_ty = self.type_of(&target_ty)?;
        let value = self.coerce_value(builder, value, clif_ty, &target_ty)?;
        if let Expr::Path(path) = target {
            if path.len() == 1 {
                if let Some((var, _)) = scope.vars.get(&path[0]).cloned() {
                    builder.def_var(var, value);
                    return Ok(());
                }
            }
        }
        let (addr, _) = self.lvalue(builder, target, function, scope)?;
        builder.ins().store(MemFlags::new(), value, addr, 0);
        Ok(())
    }

    fn lvalue(
        &mut self,
        builder: &mut FunctionBuilder,
        expr: &Expr,
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<(Value, Type), CompileError> {
        match expr {
            Expr::Path(path) if path.len() == 1 => {
                let name = &path[0];
                let (var, ty) = scope
                    .vars
                    .get(name)
                    .cloned()
                    .ok_or_else(|| CompileError::new(format!("unknown local `{name}`")))?;
                let value = builder.use_var(var);
                if is_pointer_value_type(&ty) {
                    return Ok((value, ty));
                }
                let slot_key = name.clone();
                let size = self.type_size_align(&ty)?.0.max(1);
                let slot = if let Some(slot) = scope.temp_slots.get(&slot_key) {
                    *slot
                } else {
                    let slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size as u32,
                        3,
                    ));
                    scope.temp_slots.insert(slot_key, slot);
                    slot
                };
                builder.ins().stack_store(value, slot, 0);
                Ok((builder.ins().stack_addr(self.pointer_type, slot, 0), ty))
            }
            Expr::FieldAccess { base, field } => {
                let base_ty = infer_codegen_expr_type(base, function, self.info)?;
                let (address, _) = self.lvalue(builder, base, function, scope)?;
                let ty = self.field_type(&base_ty, field)?;
                let offset = self.field_offset(&base_ty, field)?;
                Ok((builder.ins().iadd_imm(address, offset as i64), ty))
            }
            Expr::Index { base, index } => {
                let base_ty = infer_codegen_expr_type(base, function, self.info)?;
                let element_ty = match &base_ty {
                    Type::FixedArray(_, inner) => (**inner).clone(),
                    Type::List(inner) => (**inner).clone(),
                    Type::Ref(inner) | Type::Mut(inner) => match inner.as_ref() {
                        Type::FixedArray(_, element) => (**element).clone(),
                        other => {
                            return Err(CompileError::new(format!(
                                "cannot index {} in native backend",
                                describe_type(other)
                            )));
                        }
                    },
                    other => {
                        return Err(CompileError::new(format!(
                            "cannot index {} in native backend",
                            describe_type(other)
                        )));
                    }
                };
                let (address, _) = self.lvalue(builder, base, function, scope)?;
                let index_value = self.emit_expr(builder, index, None, function, scope)?;
                let index_value =
                    self.coerce_value(builder, index_value, types::I64, &Type::I64)?;
                let element_size = self.type_size_align(&element_ty)?.0.max(1);
                let element_size = builder.ins().iconst(types::I64, element_size as i64);
                let offset = builder.ins().imul(index_value, element_size);
                Ok((builder.ins().iadd(address, offset), element_ty))
            }
            Expr::BuiltinCall { name, args } if name == "deref" => {
                let ty = infer_codegen_expr_type(expr, function, self.info)?;
                let pointer = self.emit_expr(builder, &args[0], None, function, scope)?;
                Ok((pointer, ty))
            }
            _ => Err(CompileError::new(
                "expression is not assignable in native code generation",
            )),
        }
    }

    fn emit_struct_init(
        &mut self,
        builder: &mut FunctionBuilder,
        name: &str,
        fields: &[crate::ast::FieldInit],
        function: &Function,
        scope: &mut FunctionScope,
    ) -> Result<Value, CompileError> {
        let type_info = self
            .info
            .types
            .get(name)
            .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
        if type_info.kind != TypeDefKind::Struct {
            return Err(CompileError::new(format!(
                "native backend does not yet support initializing type `{name}`"
            )));
        }
        let (size, _) = self.type_size_align(&Type::Named(name.to_string()))?;
        let size = size.max(1);
        let size_value = builder.ins().iconst(self.pointer_type, size as i64);
        let malloc =
            self.extern_function("malloc", &[Type::Usize], &Type::Ref(Box::new(Type::Void)))?;
        let func_ref = self.module.declare_func_in_func(malloc, builder.func);
        let call = builder.ins().call(func_ref, &[size_value]);
        let pointer = builder.inst_results(call)[0];
        for field in fields {
            let field_ty = type_info
                .field_map
                .get(&field.name)
                .cloned()
                .ok_or_else(|| {
                    CompileError::new(format!("type `{name}` has no field `{}`", field.name))
                })?;
            let value = self.emit_expr(builder, &field.value, Some(&field_ty), function, scope)?;
            let clif_ty = self.type_of(&field_ty)?;
            let value = self.coerce_value(builder, value, clif_ty, &field_ty)?;
            let offset = type_info
                .fields
                .iter()
                .position(|candidate| candidate.name == field.name)
                .map(|index| self.field_offset_by_index(name, index))
                .transpose()?
                .unwrap_or(0);
            builder
                .ins()
                .store(MemFlags::new(), value, pointer, offset as i32);
        }
        Ok(pointer)
    }

    fn type_of(&self, ty: &Type) -> Result<ClifType, CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.info)?;
        Ok(match ty {
            Type::Void => types::I32,
            Type::Bool | Type::I8 | Type::U8 => types::I8,
            Type::I16 | Type::U16 => types::I16,
            Type::I32 | Type::U32 => types::I32,
            Type::I64 | Type::U64 => types::I64,
            Type::Isize | Type::Usize => self.pointer_type,
            Type::F32 => types::F32,
            Type::F64 => types::F64,
            Type::Named(name) => {
                let type_info = self
                    .info
                    .types
                    .get(&name)
                    .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
                if type_info.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "native backend does not yet support type `{name}`"
                    )));
                }
                self.pointer_type
            }
            Type::Ref(_) | Type::Mut(_) | Type::None | Type::FnPtr(_, _) => self.pointer_type,
            Type::Applied(_, _)
            | Type::List(_)
            | Type::FixedArray(_, _)
            | Type::Result(_)
            | Type::Error => {
                return Err(CompileError::new(format!(
                    "native backend does not yet support {} values",
                    describe_type(&ty)
                )));
            }
            Type::Infer => types::I32,
        })
    }

    fn type_size_align(&self, ty: &Type) -> Result<(u64, u64), CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.info)?;
        let pointer = self.pointer_type.bits() as u64 / 8;
        Ok(match ty {
            Type::Void => (0, 1),
            Type::Bool | Type::I8 | Type::U8 => (1, 1),
            Type::I16 | Type::U16 => (2, 2),
            Type::I32 | Type::U32 | Type::F32 => (4, 4),
            Type::I64 | Type::U64 | Type::F64 => (8, 8),
            Type::Isize | Type::Usize => (pointer, pointer),
            Type::Ref(_)
            | Type::Mut(_)
            | Type::List(_)
            | Type::Result(_)
            | Type::Error
            | Type::None
            | Type::FnPtr(_, _)
            | Type::Applied(_, _) => (pointer, pointer),
            Type::FixedArray(count, inner) => {
                let (size, align) = self.type_size_align(&inner)?;
                (size * count, align)
            }
            Type::Named(name) => {
                let type_info = self
                    .info
                    .types
                    .get(&name)
                    .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
                if type_info.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "native backend does not yet support type `{name}`"
                    )));
                }
                let mut size = 0u64;
                let mut align = 1u64;
                for field in &type_info.fields {
                    let (field_size, field_align) = self.type_size_align(&field.ty)?;
                    size = align_to(size, field_align) + field_size;
                    align = align.max(field_align);
                }
                (align_to(size, align), align)
            }
            Type::Infer => (4, 4),
        })
    }

    fn field_type(&self, base_ty: &Type, field: &str) -> Result<Type, CompileError> {
        let base_ty = crate::codegen::resolve_codegen_aliases(base_ty, self.info)?;
        let Type::Named(name) = crate::codegen::deref_refs(&base_ty) else {
            return Err(CompileError::new("field access requires a named type"));
        };
        self.info
            .types
            .get(name)
            .and_then(|type_info| type_info.field_map.get(field))
            .cloned()
            .ok_or_else(|| CompileError::new(format!("type `{name}` has no field `{field}`")))
    }

    fn field_offset(&self, base_ty: &Type, field: &str) -> Result<u64, CompileError> {
        let base_ty = crate::codegen::resolve_codegen_aliases(base_ty, self.info)?;
        let Type::Named(name) = crate::codegen::deref_refs(&base_ty) else {
            return Err(CompileError::new("field access requires a named type"));
        };
        let type_info = self
            .info
            .types
            .get(name)
            .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
        let index = type_info
            .fields
            .iter()
            .position(|candidate| candidate.name == field)
            .ok_or_else(|| CompileError::new(format!("type `{name}` has no field `{field}`")))?;
        self.field_offset_by_index(name, index)
    }

    fn field_offset_by_index(&self, name: &str, index: usize) -> Result<u64, CompileError> {
        let type_info = self
            .info
            .types
            .get(name)
            .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
        let mut offset = 0u64;
        for field in type_info.fields.iter().take(index) {
            let (size, align) = self.type_size_align(&field.ty)?;
            offset = align_to(offset, align) + size;
        }
        if let Some(field) = type_info.fields.get(index) {
            let (_, align) = self.type_size_align(&field.ty)?;
            offset = align_to(offset, align);
        }
        Ok(offset)
    }

    fn extern_function(
        &mut self,
        name: &str,
        params: &[Type],
        ret: &Type,
    ) -> Result<FuncId, CompileError> {
        let mut signature = self.module.make_signature();
        for ty in params {
            signature.params.push(AbiParam::new(self.type_of(ty)?));
        }
        if !matches!(ret, Type::Void) {
            signature.returns.push(AbiParam::new(self.type_of(ret)?));
        }
        self.extern_function_signature(name, signature)
    }

    fn extern_function_signature(
        &mut self,
        name: &str,
        signature: ir::Signature,
    ) -> Result<FuncId, CompileError> {
        let func_id = self
            .module
            .declare_function(name, Linkage::Import, &signature)
            .map_err(|e| CompileError::new(format!("failed to import `{name}`: {e}")))?;
        Ok(func_id)
    }

    fn new_block(&mut self, builder: &mut FunctionBuilder) -> ir::Block {
        let block = builder.create_block();
        self.next_block += 1;
        block
    }
}

fn is_pointer_value_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Named(_)
            | Type::Applied(_, _)
            | Type::Ref(_)
            | Type::Mut(_)
            | Type::List(_)
            | Type::FixedArray(_, _)
            | Type::Result(_)
            | Type::Error
            | Type::None
            | Type::FnPtr(_, _)
    )
}

fn current_block_terminated(builder: &FunctionBuilder) -> bool {
    let Some(block) = builder.current_block() else {
        return true;
    };
    let Some(last_inst) = builder.func.layout.last_inst(block) else {
        return false;
    };
    builder.func.dfg.insts[last_inst].opcode().is_terminator()
}

fn common_numeric_clif(lhs: ClifType, rhs: ClifType) -> Option<ClifType> {
    if lhs.is_float() || rhs.is_float() {
        if lhs == types::F64 || rhs == types::F64 {
            Some(types::F64)
        } else {
            Some(types::F32)
        }
    } else if lhs.is_int() && rhs.is_int() {
        Some(if lhs.bits() >= rhs.bits() { lhs } else { rhs })
    } else {
        None
    }
}

fn align_to(value: u64, align: u64) -> u64 {
    if align <= 1 {
        value
    } else {
        value.div_ceil(align) * align
    }
}

pub(crate) fn collect_reachable_functions(program: &Program) -> std::collections::HashSet<String> {
    use std::collections::{HashSet, VecDeque};

    let functions: HashMap<&str, &Function> = program
        .functions
        .iter()
        .map(|function| (function.name.as_str(), function))
        .collect();
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    if functions.contains_key("main") {
        reachable.insert("main".to_string());
        queue.push_back("main".to_string());
    }
    for test in &program.tests {
        for stmt in &test.body {
            collect_function_refs_stmt(stmt, &functions, &mut reachable, &mut queue);
        }
    }
    while let Some(name) = queue.pop_front() {
        if let Some(function) = functions.get(name.as_str()) {
            for stmt in &function.body {
                collect_function_refs_stmt(stmt, &functions, &mut reachable, &mut queue);
            }
        }
    }
    reachable
}

fn collect_function_refs_stmt(
    stmt: &Stmt,
    functions: &HashMap<&str, &Function>,
    reachable: &mut std::collections::HashSet<String>,
    queue: &mut std::collections::VecDeque<String>,
) {
    match stmt {
        Stmt::VarDecl { init, .. } => collect_function_refs_expr(init, functions, reachable, queue),
        Stmt::Assign { target, value, .. }
        | Stmt::AddAssign { target, value, .. }
        | Stmt::MulAssign { target, value, .. }
        | Stmt::SubAssign { target, value, .. }
        | Stmt::DivAssign { target, value, .. }
        | Stmt::BitAndAssign { target, value, .. }
        | Stmt::BitOrAssign { target, value, .. }
        | Stmt::BitXorAssign { target, value, .. } => {
            collect_function_refs_expr(target, functions, reachable, queue);
            collect_function_refs_expr(value, functions, reachable, queue);
        }
        Stmt::Increment { target, .. } | Stmt::Decrement { target, .. } => {
            collect_function_refs_expr(target, functions, reachable, queue)
        }
        Stmt::Assert { condition, .. } => {
            collect_function_refs_expr(condition, functions, reachable, queue)
        }
        Stmt::Return { value, .. } => {
            if let Some(value) = value {
                collect_function_refs_expr(value, functions, reachable, queue);
            }
        }
        Stmt::Defer { body, .. } | Stmt::Block(body) | Stmt::Loop { body, .. } => {
            for stmt in body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            collect_function_refs_expr(condition, functions, reachable, queue);
            for stmt in then_body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
            for stmt in else_body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::Match { expr, arms, .. } => {
            collect_function_refs_expr(expr, functions, reachable, queue);
            for arm in arms {
                for stmt in &arm.body {
                    collect_function_refs_stmt(stmt, functions, reachable, queue);
                }
            }
        }
        Stmt::Expr { expr, .. } => collect_function_refs_expr(expr, functions, reachable, queue),
        Stmt::ForRange {
            start, end, body, ..
        } => {
            collect_function_refs_expr(start, functions, reachable, queue);
            collect_function_refs_expr(end, functions, reachable, queue);
            for stmt in body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::ForEach { iterable, body, .. } => {
            collect_function_refs_expr(iterable, functions, reachable, queue);
            for stmt in body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::ForClassic {
            init,
            condition,
            increment,
            body,
            ..
        } => {
            collect_function_refs_expr(init, functions, reachable, queue);
            collect_function_refs_expr(condition, functions, reachable, queue);
            collect_function_refs_expr(increment, functions, reachable, queue);
            for stmt in body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::While {
            condition, body, ..
        } => {
            collect_function_refs_expr(condition, functions, reachable, queue);
            for stmt in body {
                collect_function_refs_stmt(stmt, functions, reachable, queue);
            }
        }
        Stmt::Continue { .. } | Stmt::Break { .. } => {}
    }
}

fn collect_function_refs_expr(
    expr: &Expr,
    functions: &HashMap<&str, &Function>,
    reachable: &mut std::collections::HashSet<String>,
    queue: &mut std::collections::VecDeque<String>,
) {
    let mut add_path = |path: &[String]| {
        let name = path.join(".");
        if functions.contains_key(name.as_str()) && reachable.insert(name.clone()) {
            queue.push_back(name);
        }
    };
    match expr {
        Expr::Path(path) => add_path(path),
        Expr::Call { callee, args } => {
            if let Some(path) = callee.callee_path() {
                add_path(&path);
            } else {
                collect_function_refs_expr(callee, functions, reachable, queue);
            }
            for arg in args {
                collect_function_refs_expr(arg, functions, reachable, queue);
            }
        }
        Expr::BuiltinCall { args, .. } => {
            for arg in args {
                collect_function_refs_expr(arg, functions, reachable, queue);
            }
        }
        Expr::ListLiteral(values) | Expr::Pack(values) => {
            for value in values {
                collect_function_refs_expr(value, functions, reachable, queue);
            }
        }
        Expr::Index { base, index } => {
            collect_function_refs_expr(base, functions, reachable, queue);
            collect_function_refs_expr(index, functions, reachable, queue);
        }
        Expr::FieldAccess { base, .. } => {
            collect_function_refs_expr(base, functions, reachable, queue)
        }
        Expr::StructInit { fields, .. } => {
            for field in fields {
                collect_function_refs_expr(&field.value, functions, reachable, queue);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_function_refs_expr(receiver, functions, reachable, queue);
            for arg in args {
                collect_function_refs_expr(arg, functions, reachable, queue);
            }
        }
        Expr::Specialize { callee, .. } => {
            collect_function_refs_expr(callee, functions, reachable, queue)
        }
        Expr::Cast { expr, .. }
        | Expr::BitCast { expr, .. }
        | Expr::Unary { expr, .. }
        | Expr::Try(expr) => collect_function_refs_expr(expr, functions, reachable, queue),
        Expr::Error { message } => collect_function_refs_expr(message, functions, reachable, queue),
        Expr::Binary { lhs, rhs, .. } => {
            collect_function_refs_expr(lhs, functions, reachable, queue);
            collect_function_refs_expr(rhs, functions, reachable, queue);
        }
        Expr::Int(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::None
        | Expr::SizeOf(_) => {}
    }
}

fn collect_program_strings(program: &Program, strings: &mut Vec<String>) {
    for function in &program.functions {
        for stmt in &function.body {
            collect_stmt_strings(stmt, strings);
        }
    }
    for test in &program.tests {
        for stmt in &test.body {
            collect_stmt_strings(stmt, strings);
        }
    }
    for global in &program.globals {
        collect_expr_strings(&global.init, strings);
    }
}

fn collect_stmt_strings(stmt: &Stmt, strings: &mut Vec<String>) {
    match stmt {
        Stmt::VarDecl { init, .. } => collect_expr_strings(init, strings),
        Stmt::Assign { target, value, .. }
        | Stmt::AddAssign { target, value, .. }
        | Stmt::MulAssign { target, value, .. }
        | Stmt::SubAssign { target, value, .. }
        | Stmt::DivAssign { target, value, .. }
        | Stmt::BitAndAssign { target, value, .. }
        | Stmt::BitOrAssign { target, value, .. }
        | Stmt::BitXorAssign { target, value, .. } => {
            collect_expr_strings(target, strings);
            collect_expr_strings(value, strings);
        }
        Stmt::Increment { target, .. } | Stmt::Decrement { target, .. } => {
            collect_expr_strings(target, strings)
        }
        Stmt::Assert { condition, .. } => collect_expr_strings(condition, strings),
        Stmt::Return { value, .. } => {
            if let Some(value) = value {
                collect_expr_strings(value, strings);
            }
        }
        Stmt::Defer { body, .. } | Stmt::Block(body) | Stmt::Loop { body, .. } => {
            for stmt in body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            collect_expr_strings(condition, strings);
            for stmt in then_body {
                collect_stmt_strings(stmt, strings);
            }
            for stmt in else_body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::Match { expr, arms, .. } => {
            collect_expr_strings(expr, strings);
            for arm in arms {
                for stmt in &arm.body {
                    collect_stmt_strings(stmt, strings);
                }
            }
        }
        Stmt::Expr { expr, .. } => collect_expr_strings(expr, strings),
        Stmt::ForRange {
            start, end, body, ..
        } => {
            collect_expr_strings(start, strings);
            collect_expr_strings(end, strings);
            for stmt in body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::ForEach { iterable, body, .. } => {
            collect_expr_strings(iterable, strings);
            for stmt in body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::ForClassic {
            init,
            condition,
            increment,
            body,
            ..
        } => {
            collect_expr_strings(init, strings);
            collect_expr_strings(condition, strings);
            collect_expr_strings(increment, strings);
            for stmt in body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::While {
            condition, body, ..
        } => {
            collect_expr_strings(condition, strings);
            for stmt in body {
                collect_stmt_strings(stmt, strings);
            }
        }
        Stmt::Continue { .. } | Stmt::Break { .. } => {}
    }
}

fn collect_expr_strings(expr: &Expr, strings: &mut Vec<String>) {
    match expr {
        Expr::String(value) => strings.push(value.clone()),
        Expr::Path(_)
        | Expr::Int(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Float(_)
        | Expr::None
        | Expr::SizeOf(_) => {}
        Expr::ListLiteral(values) | Expr::Pack(values) => {
            for value in values {
                collect_expr_strings(value, strings);
            }
        }
        Expr::Index { base, index } => {
            collect_expr_strings(base, strings);
            collect_expr_strings(index, strings);
        }
        Expr::FieldAccess { base, .. } => collect_expr_strings(base, strings),
        Expr::StructInit { fields, .. } => {
            for field in fields {
                collect_expr_strings(&field.value, strings);
            }
        }
        Expr::BuiltinCall { name, args } => {
            if name == "print" {
                if let Some(Expr::String(value)) = args.first() {
                    strings.push(value.clone());
                }
            }
            for arg in args {
                collect_expr_strings(arg, strings);
            }
        }
        Expr::Call { callee, args } => {
            collect_expr_strings(callee, strings);
            for arg in args {
                collect_expr_strings(arg, strings);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_expr_strings(receiver, strings);
            for arg in args {
                collect_expr_strings(arg, strings);
            }
        }
        Expr::Specialize { callee, .. } => collect_expr_strings(callee, strings),
        Expr::Cast { expr, .. }
        | Expr::BitCast { expr, .. }
        | Expr::Unary { expr, .. }
        | Expr::Try(expr) => collect_expr_strings(expr, strings),
        Expr::Error { message } => collect_expr_strings(message, strings),
        Expr::Binary { lhs, rhs, .. } => {
            collect_expr_strings(lhs, strings);
            collect_expr_strings(rhs, strings);
        }
    }
}

pub fn runtime_c() -> &'static str {
    r#"#include <stdint.h>
#include <stdio.h>
#include <stddef.h>

void scar_print_str(const char *s) {
    fputs(s ? s : "", stdout);
}

void scar_puts(const char *s) {
    fputs(s ? s : "", stdout);
    fputc('\n', stdout);
}

void scar_print_bool(int value) {
    fputs(value ? "true" : "false", stdout);
}

void scar_print_char(int value) {
    putchar(value);
}

void scar_print_ptr(const void *value) {
    printf("%p", value);
}

void scar_print_int(int64_t value, int width, int is_unsigned) {
    if (width > 0) {
        if (is_unsigned) printf("%*llu", width, (unsigned long long)value);
        else printf("%*lld", width, (long long)value);
    } else {
        if (is_unsigned) printf("%llu", (unsigned long long)value);
        else printf("%lld", (long long)value);
    }
}

void scar_print_radix(uint64_t value, int width, int mode) {
    if (mode == 1) {
        if (width > 0) printf("%*llX", width, (unsigned long long)value);
        else printf("%llX", (unsigned long long)value);
    } else if (mode == 2) {
        if (width > 0) printf("%*llo", width, (unsigned long long)value);
        else printf("%llo", (unsigned long long)value);
    } else {
        if (width > 0) printf("%*llx", width, (unsigned long long)value);
        else printf("%llx", (unsigned long long)value);
    }
}

void scar_print_float(double value, int width, int mode) {
    if (mode == 1) {
        if (width > 0) printf("%*e", width, value);
        else printf("%e", value);
    } else if (mode == 2) {
        if (width > 0) printf("%*E", width, value);
        else printf("%E", value);
    } else if (mode == 3) {
        if (width > 0) printf("%*g", width, value);
        else printf("%g", value);
    } else if (mode == 4) {
        if (width > 0) printf("%*G", width, value);
        else printf("%G", value);
    } else {
        if (width > 0) printf("%*f", width, value);
        else printf("%f", value);
    }
}
"#
}
