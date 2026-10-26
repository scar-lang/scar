//! WebAssembly backend for the Scar compiler.
//!
//! The generated module targets WASI and exports `_start` (plus `main`) so it
//! can be executed by any WASI-compatible runtime.

use std::collections::{HashMap, HashSet};

use crate::{
    CompileError,
    ast::{BinaryOp, Expr, Function, Program, Stmt, Type, TypeDefKind, UnaryOp},
    clif::collect_reachable_functions,
    codegen::{infer_codegen_expr_type, is_codegen_signed_integer_type},
    sema::ProgramInfo,
};

pub fn compile_wasm(
    program: &Program,
    info: &ProgramInfo,
    _optimize: bool,
) -> Result<Vec<u8>, CompileError> {
    let wat = generate_wat(program, info)?;
    wat::parse_str(&wat)
        .map_err(|error| CompileError::new(format!("failed to encode wasm: {error}")))
}

fn generate_wat(program: &Program, info: &ProgramInfo) -> Result<String, CompileError> {
    let Some(main_function) = program
        .functions
        .iter()
        .find(|function| function.name == "main" && function.extern_name.is_none())
    else {
        return Err(CompileError::new(
            "no `main` function found for wasm output",
        ));
    };
    let reachable = collect_reachable_functions(program);
    let mut backend = WasmBackend {
        info,
        program,
        reachable,
        strings: HashMap::new(),
        next_data: 1024,
        data_section: String::new(),
        functions: Vec::new(),
        defined_externs: HashSet::new(),
    };
    let newline = backend.intern("\n");
    let true_str = backend.intern("true");
    let false_str = backend.intern("false");
    let zero_str = backend.intern("0");

    for function in &program.functions {
        if function.extern_name.is_some() || !backend.reachable.contains(&function.name) {
            continue;
        }
        let generated = backend.generate_function(function)?;
        backend.functions.push(generated);
    }

    let main_symbol = info
        .function_symbols
        .get(&main_function.name)
        .cloned()
        .unwrap_or_else(|| "fn__main".to_string());
    let main_returns_value = !matches!(main_function.return_type, Type::Void);
    let main_return_ty = backend.wasm_type(&main_function.return_type)?;
    let mut start_body = String::new();
    start_body.push_str(&format!("    call ${main_symbol}\n"));
    if main_returns_value {
        start_body.push_str("    drop\n");
    }

    let main_export = if main_returns_value {
        format!(
            "  (func (export \"main\") (result i32)\n    call ${main_symbol}\n{}\n  )\n",
            if main_return_ty == "i32" {
                ""
            } else if main_return_ty == "i64" {
                "    i32.wrap_i64\n"
            } else {
                "    drop\n    i32.const 0\n"
            }
        )
    } else {
        format!(
            "  (func (export \"main\") (result i32)\n    call ${main_symbol}\n    i32.const 0\n  )\n"
        )
    };

    let runtime = runtime_wat(
        newline.0,
        true_str.0,
        true_str.1,
        false_str.0,
        false_str.1,
        zero_str.0,
    );

    let extern_funcs = backend.extern_runtime_functions();
    let mut wat = String::new();
    wat.push_str("(module\n");
    wat.push_str("  (import \"wasi_snapshot_preview1\" \"fd_write\" (func $fd_write (param i32 i32 i32 i32) (result i32)))\n");
    wat.push_str("  (memory (export \"memory\") 16)\n");
    wat.push_str("  (global $heap (mut i32) (i32.const 65536))\n\n");
    wat.push_str(&backend.data_section);
    wat.push('\n');
    wat.push_str(&runtime);
    wat.push_str(&extern_funcs);
    for function in &backend.functions {
        wat.push_str(function);
    }
    wat.push_str(&format!("  (func (export \"_start\")\n{}  )\n", start_body));
    wat.push_str(&main_export);
    wat.push_str(")\n");
    Ok(wat)
}

struct WasmBackend<'a> {
    info: &'a ProgramInfo,
    program: &'a Program,
    reachable: HashSet<String>,
    strings: HashMap<String, (u32, u32)>,
    next_data: u32,
    data_section: String,
    functions: Vec<String>,
    defined_externs: HashSet<String>,
}

impl<'a> WasmBackend<'a> {
    fn intern(&mut self, value: &str) -> (u32, u32) {
        if let Some(existing) = self.strings.get(value) {
            return *existing;
        }
        let offset = self.next_data;
        let bytes = value.as_bytes();
        let len = bytes.len() as u32;
        let mut escaped = String::new();
        for byte in bytes {
            match byte {
                b'\\' => escaped.push_str("\\\\"),
                b'"' => escaped.push_str("\\\""),
                b'\n' => escaped.push_str("\\n"),
                b'\r' => escaped.push_str("\\r"),
                b'\t' => escaped.push_str("\\t"),
                0x20..=0x7e => escaped.push(*byte as char),
                other => escaped.push_str(&format!("\\{other:02x}")),
            }
        }
        // Null-terminate strings so C-like pointer operations work.
        escaped.push_str("\\00");
        self.data_section
            .push_str(&format!("  (data (i32.const {offset}) \"{escaped}\")\n"));
        self.next_data = offset + len + 1;
        self.strings.insert(value.to_string(), (offset, len));
        (offset, len)
    }

    fn generate_function(&mut self, function: &Function) -> Result<String, CompileError> {
        let result_ty = self.wasm_type(&function.return_type)?;
        let symbol = self
            .info
            .function_symbols
            .get(&function.name)
            .cloned()
            .unwrap_or_else(|| function.name.clone());
        let param_types = function
            .params
            .iter()
            .map(|param| self.wasm_type(&param.ty))
            .collect::<Result<Vec<_>, _>>()?;
        let (body, local_decls, temp_decls) = {
            let mut codegen = FunctionCodegen::new(self, function)?;
            codegen.emit_block(&function.body)?;
            if !matches!(function.return_type, Type::Void) {
                codegen
                    .body
                    .push_str(&format!("    {} \n", default_value(&result_ty)));
                codegen.body.push_str("    return\n");
            }
            (codegen.body, codegen.local_decls, codegen.temp_decls)
        };
        let mut output = String::new();
        output.push_str(&format!("  (func ${symbol}"));
        for (param, ty) in function.params.iter().zip(param_types.iter()) {
            output.push_str(&format!(
                " (param ${} {ty})",
                self.local_id_for(&param.name)
            ));
        }
        if !matches!(function.return_type, Type::Void) {
            output.push_str(&format!(" (result {result_ty})"));
        }
        output.push('\n');
        for (name, ty) in &local_decls {
            output.push_str(&format!("    (local ${name} {ty})\n"));
        }
        for (name, ty) in &temp_decls {
            output.push_str(&format!("    (local ${name} {ty})\n"));
        }
        output.push_str(&body);
        output.push_str("  )\n");
        Ok(output)
    }

    fn local_id_for(&self, name: &str) -> String {
        let mut id = String::new();
        for ch in name.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                id.push(ch);
            } else {
                id.push('_');
            }
        }
        id
    }

    fn extern_runtime_functions(&mut self) -> String {
        let mut output = String::new();
        for function in &self.program.functions {
            if function.extern_name.is_none() {
                continue;
            }
            let Some(name) = &function.extern_name else {
                continue;
            };
            if self.defined_externs.contains(name) {
                continue;
            }
            if let Some(runtime) = wasm_extern_runtime(name) {
                output.push_str(&runtime);
                self.defined_externs.insert(name.clone());
            }
        }
        output
    }

    fn wasm_type(&self, ty: &Type) -> Result<String, CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.info)?;
        Ok(match ty {
            Type::Void => String::new(),
            Type::Bool => "i32".to_string(),
            Type::F32 | Type::F64 => "f64".to_string(),
            Type::Named(name) => {
                let Some(type_info) = self.info.types.get(&name) else {
                    return Ok("i32".to_string());
                };
                if type_info.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "wasm backend does not support type `{name}`"
                    )));
                }
                "i32".to_string()
            }
            Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::Isize
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
            | Type::U8 => "i64".to_string(),
            Type::Applied(_, _)
            | Type::Ref(_)
            | Type::Mut(_)
            | Type::List(_)
            | Type::FixedArray(_, _)
            | Type::Result(_)
            | Type::Error
            | Type::None
            | Type::FnPtr(_, _)
            | Type::Infer => "i32".to_string(),
        })
    }

    fn type_size_align(&self, ty: &Type) -> Result<(u32, u32), CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.info)?;
        Ok(match ty {
            Type::Void => (0, 1),
            Type::Bool => (4, 4),
            Type::I8 | Type::U8 => (1, 1),
            Type::I16 | Type::U16 => (2, 2),
            Type::I32 | Type::U32 | Type::F32 => (4, 4),
            _ => (8, 8),
        })
    }

    fn struct_layout(&self, name: &str) -> Result<(u32, HashMap<String, u32>), CompileError> {
        let type_info = self
            .info
            .types
            .get(name)
            .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
        if type_info.kind != TypeDefKind::Struct {
            return Err(CompileError::new(format!(
                "wasm backend does not support type `{name}`"
            )));
        }
        let mut fields = HashMap::new();
        let mut offset = 0u32;
        for field in &type_info.fields {
            let (size, align) = self.type_size_align(&field.ty)?;
            offset = align_to(offset, align);
            fields.insert(field.name.clone(), offset);
            offset += size;
        }
        Ok((align_to(offset.max(1), 8), fields))
    }
}

struct FunctionCodegen<'a, 'b> {
    backend: &'a mut WasmBackend<'b>,
    function: &'a Function,
    local_ids: HashMap<String, String>,
    local_decls: Vec<(String, String)>,
    temp_decls: Vec<(String, String)>,
    body: String,
    loops: Vec<(String, String)>,
    next_loop: usize,
    next_temp_name: usize,
}

impl<'a, 'b> FunctionCodegen<'a, 'b> {
    fn new(backend: &'a mut WasmBackend<'b>, function: &'a Function) -> Result<Self, CompileError> {
        let mut this = Self {
            backend,
            function,
            local_ids: HashMap::new(),
            local_decls: Vec::new(),
            temp_decls: Vec::new(),
            body: String::new(),
            loops: Vec::new(),
            next_loop: 0,
            next_temp_name: 0,
        };
        for param in &function.params {
            let ty = this.backend.wasm_type(&param.ty)?;
            let _ = ty;
            let id = this.make_local_id(&param.name);
            this.local_ids.insert(param.name.clone(), id);
        }
        let mut names = Vec::new();
        collect_local_names(&function.body, &mut names);
        for name in names {
            if this.local_ids.contains_key(&name) {
                continue;
            }
            let ty = this
                .backend
                .info
                .locals
                .get(&function.name)
                .and_then(|locals| locals.get(&name))
                .cloned()
                .unwrap_or(Type::I64);
            let wasm_ty = this.backend.wasm_type(&ty)?;
            let id = this.make_local_id(&name);
            this.local_ids.insert(name, id.clone());
            this.local_decls.push((id, wasm_ty));
        }
        Ok(this)
    }

    fn make_local_id(&mut self, name: &str) -> String {
        let mut id = String::new();
        for ch in name.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                id.push(ch);
            } else {
                id.push('_');
            }
        }
        id
    }

    fn local_id(&self, name: &str) -> String {
        self.local_ids
            .get(name)
            .cloned()
            .unwrap_or_else(|| name.to_string())
    }

    fn temp(&mut self, ty: &str) -> String {
        let id = format!("t{}", self.next_temp_name);
        self.next_temp_name += 1;
        self.temp_decls.push((id.clone(), ty.to_string()));
        id
    }

    fn push(&mut self, line: impl AsRef<str>) {
        self.body.push_str("    ");
        self.body.push_str(line.as_ref());
        self.body.push('\n');
    }

    fn emit_block(&mut self, body: &[Stmt]) -> Result<(), CompileError> {
        for stmt in body {
            self.emit_stmt(stmt)?;
        }
        Ok(())
    }

    fn emit_stmt(&mut self, stmt: &Stmt) -> Result<(), CompileError> {
        match stmt {
            Stmt::Defer { .. } => {
                return Err(CompileError::new("wasm backend does not yet support defer"));
            }
            Stmt::VarDecl { name, init, .. } => {
                self.emit_expr(init)?;
                self.push(format!("local.set ${}", self.local_id(name)));
            }
            Stmt::Assign { target, value, .. } => {
                self.emit_store(target, value)?;
            }
            Stmt::AddAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.add")?
            }
            Stmt::SubAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.sub")?
            }
            Stmt::MulAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.mul")?
            }
            Stmt::DivAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.div_s")?
            }
            Stmt::BitAndAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.and")?
            }
            Stmt::BitOrAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.or")?
            }
            Stmt::BitXorAssign { target, value, .. } => {
                self.emit_compound(target, value, "i64.xor")?
            }
            Stmt::Increment { target, .. } => {
                self.emit_expr(target)?;
                self.push("i64.const 1");
                self.push("i64.add");
                self.emit_set_path(target)?;
            }
            Stmt::Decrement { target, .. } => {
                self.emit_expr(target)?;
                self.push("i64.const 1");
                self.push("i64.sub");
                self.emit_set_path(target)?;
            }
            Stmt::Assert { condition, .. } => {
                self.emit_cond(condition)?;
                self.push("i32.eqz");
                self.push("if");
                self.push("  unreachable");
                self.push("end");
            }
            Stmt::Return { value, .. } => {
                if let Some(value) = value {
                    self.emit_expr(value)?;
                }
                self.push("return");
            }
            Stmt::Block(body) => self.emit_block(body)?,
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                self.emit_cond(condition)?;
                self.push("if");
                self.emit_block(then_body)?;
                if !else_body.is_empty() {
                    self.push("else");
                    self.emit_block(else_body)?;
                }
                self.push("end");
            }
            Stmt::Match { .. } => {
                return Err(CompileError::new("wasm backend does not yet support match"));
            }
            Stmt::Expr { expr, .. } => {
                let ty = infer_codegen_expr_type(expr, self.function, self.backend.info)?;
                if !matches!(ty, Type::Void) {
                    self.emit_expr(expr)?;
                    self.push("drop");
                } else {
                    self.emit_expr(expr)?;
                }
            }
            Stmt::ForRange {
                var_name,
                start,
                end,
                body,
                ..
            } => self.emit_for_range(var_name, start, end, body)?,
            Stmt::ForEach { .. } => {
                return Err(CompileError::new(
                    "wasm backend does not yet support for-each",
                ));
            }
            Stmt::ForClassic {
                var_name,
                init,
                condition,
                increment,
                body,
                ..
            } => self.emit_for_classic(var_name, init, condition, increment, body)?,
            Stmt::While {
                condition, body, ..
            } => {
                let break_label = self.next_loop_label("break");
                let continue_label = self.next_loop_label("continue");
                self.loops
                    .push((break_label.clone(), continue_label.clone()));
                self.push(format!("block ${break_label}"));
                self.push(format!("  loop ${continue_label}"));
                self.emit_cond(condition)?;
                self.push("  i32.eqz");
                self.push(format!("  br_if ${break_label}"));
                self.emit_block(body)?;
                self.push(format!("  br ${continue_label}"));
                self.push("  end");
                self.push("end");
                self.loops.pop();
            }
            Stmt::Loop { body, .. } => {
                let break_label = self.next_loop_label("break");
                let continue_label = self.next_loop_label("continue");
                self.loops
                    .push((break_label.clone(), continue_label.clone()));
                self.push(format!("block ${break_label}"));
                self.push(format!("  loop ${continue_label}"));
                self.emit_block(body)?;
                self.push(format!("  br ${continue_label}"));
                self.push("  end");
                self.push("end");
                self.loops.pop();
            }
            Stmt::Continue { .. } => {
                let (_, continue_label) = self
                    .loops
                    .last()
                    .cloned()
                    .ok_or_else(|| CompileError::new("continue outside of a loop"))?;
                self.push(format!("br ${continue_label}"));
            }
            Stmt::Break { .. } => {
                let (break_label, _) = self
                    .loops
                    .last()
                    .cloned()
                    .ok_or_else(|| CompileError::new("break outside of a loop"))?;
                self.push(format!("br ${break_label}"));
            }
        }
        Ok(())
    }

    fn emit_for_range(
        &mut self,
        var_name: &str,
        start: &Expr,
        end: &Expr,
        body: &[Stmt],
    ) -> Result<(), CompileError> {
        let var = self.local_id(var_name);
        self.emit_expr(start)?;
        self.push(format!("local.set ${var}"));
        let break_label = self.next_loop_label("break");
        let continue_label = self.next_loop_label("continue");
        let inc_label = self.next_loop_label("inc");
        self.loops.push((break_label.clone(), inc_label.clone()));
        self.push(format!("block ${break_label}"));
        self.push(format!("  loop ${continue_label}"));
        self.push(format!("    local.get ${var}"));
        self.emit_expr(end)?;
        self.push("    i64.lt_s");
        self.push("    i32.eqz");
        self.push(format!("    br_if ${break_label}"));
        self.push(format!("    block ${inc_label}"));
        self.emit_block(body)?;
        self.push("    end");
        self.push(format!("    local.get ${var}"));
        self.push("    i64.const 1");
        self.push("    i64.add");
        self.push(format!("    local.set ${var}"));
        self.push(format!("    br ${continue_label}"));
        self.push("  end");
        self.push("end");
        self.loops.pop();
        Ok(())
    }

    fn emit_for_classic(
        &mut self,
        var_name: &str,
        init: &Expr,
        condition: &Expr,
        increment: &Expr,
        body: &[Stmt],
    ) -> Result<(), CompileError> {
        let var = self.local_id(var_name);
        self.emit_expr(init)?;
        self.push(format!("local.set ${var}"));
        let break_label = self.next_loop_label("break");
        let continue_label = self.next_loop_label("continue");
        let inc_label = self.next_loop_label("inc");
        self.loops.push((break_label.clone(), inc_label.clone()));
        self.push(format!("block ${break_label}"));
        self.push(format!("  loop ${continue_label}"));
        self.emit_cond(condition)?;
        self.push("  i32.eqz");
        self.push(format!("  br_if ${break_label}"));
        self.push(format!("  block ${inc_label}"));
        self.emit_block(body)?;
        self.push("  end");
        self.emit_expr(increment)?;
        self.push("  drop");
        self.push(format!("  br ${continue_label}"));
        self.push("end");
        self.push("end");
        self.loops.pop();
        Ok(())
    }

    fn next_loop_label(&mut self, kind: &str) -> String {
        let label = format!("{kind}_{}", self.next_loop);
        self.next_loop += 1;
        label
    }

    fn emit_compound(&mut self, target: &Expr, value: &Expr, op: &str) -> Result<(), CompileError> {
        self.emit_expr(target)?;
        self.emit_expr(value)?;
        self.push(op);
        self.emit_set_path(target)
    }

    fn emit_set_path(&mut self, target: &Expr) -> Result<(), CompileError> {
        match target {
            Expr::Path(path) if path.len() == 1 => {
                self.push(format!("local.set ${}", self.local_id(&path[0])));
                Ok(())
            }
            _ => Err(CompileError::new(
                "wasm backend only supports assigning to local variables",
            )),
        }
    }

    fn emit_store(&mut self, target: &Expr, value: &Expr) -> Result<(), CompileError> {
        match target {
            Expr::Path(path) if path.len() == 1 => {
                self.emit_expr(value)?;
                self.push(format!("local.set ${}", self.local_id(&path[0])));
                Ok(())
            }
            Expr::FieldAccess { base, field } => {
                self.emit_expr(base)?;
                self.emit_expr(value)?;
                let field_ty = infer_codegen_expr_type(target, self.function, self.backend.info)?;
                let store = self.store_instruction(&field_ty)?;
                let (_, fields) = self.struct_layout_for_expr(base)?;
                let offset = *fields
                    .get(field)
                    .ok_or_else(|| CompileError::new(format!("unknown field `{field}`")))?;
                self.push(format!("{store} offset={offset}"));
                Ok(())
            }
            _ => Err(CompileError::new(
                "wasm backend only supports assigning to locals and fields",
            )),
        }
    }

    fn struct_layout_for_expr(
        &self,
        base: &Expr,
    ) -> Result<(u32, HashMap<String, u32>), CompileError> {
        let base_ty = infer_codegen_expr_type(base, self.function, self.backend.info)?;
        let base_ty = crate::codegen::resolve_codegen_aliases(&base_ty, self.backend.info)?;
        let Type::Named(name) = crate::codegen::deref_refs(&base_ty) else {
            return Err(CompileError::new("field access requires a named type"));
        };
        self.backend.struct_layout(name)
    }

    fn emit_cond(&mut self, expr: &Expr) -> Result<(), CompileError> {
        let ty = infer_codegen_expr_type(expr, self.function, self.backend.info)?;
        self.emit_expr(expr)?;
        match crate::codegen::resolve_codegen_aliases(&ty, self.backend.info)? {
            Type::Bool => {}
            Type::F32 | Type::F64 => {
                self.push("f64.const 0");
                self.push("f64.ne");
            }
            Type::Ref(_) | Type::Mut(_) | Type::Named(_) | Type::None | Type::Error => {
                self.push("i32.const 0");
                self.push("i32.ne");
            }
            _ => {
                self.push("i64.const 0");
                self.push("i64.ne");
            }
        }
        Ok(())
    }

    fn emit_expr(&mut self, expr: &Expr) -> Result<(), CompileError> {
        match expr {
            Expr::Int(value) => self.push(format!("i64.const {}", *value as i64)),
            Expr::Char(value) => self.push(format!("i64.const {}", *value)),
            Expr::Bool(value) => self.push(format!("i32.const {}", i32::from(*value))),
            Expr::Float(value) => self.push(format!("f64.const {}", float_literal(*value))),
            Expr::String(value) => {
                let (offset, _) = self.backend.intern(value);
                self.push(format!("i32.const {offset}"));
            }
            Expr::None => self.push("i32.const 0"),
            Expr::Path(path) => {
                if path.len() == 1 {
                    if let Some(_) = self.local_ids.get(&path[0]) {
                        self.push(format!("local.get ${}", self.local_id(&path[0])));
                        return Ok(());
                    }
                }
                return Err(CompileError::new(format!(
                    "wasm backend does not support path `{}`",
                    path.join(".")
                )));
            }
            Expr::Unary { op, expr } => match op {
                UnaryOp::Neg => {
                    let ty = infer_codegen_expr_type(expr, self.function, self.backend.info)?;
                    self.emit_expr(expr)?;
                    if matches!(ty, Type::F32 | Type::F64) {
                        self.push("f64.neg");
                    } else {
                        self.push("i64.const -1");
                        self.push("i64.mul");
                    }
                }
                UnaryOp::LogicalNot => {
                    self.emit_cond(expr)?;
                    self.push("i32.eqz");
                }
                UnaryOp::BitNot => {
                    self.emit_expr(expr)?;
                    self.push("i64.const -1");
                    self.push("i64.xor");
                }
                UnaryOp::PostfixInc | UnaryOp::PostfixDec => {
                    let temp = self.temp("i64");
                    self.emit_expr(expr)?;
                    self.push(format!("local.tee ${temp}"));
                    self.push("i64.const 1");
                    self.push(if *op == UnaryOp::PostfixInc {
                        "i64.add"
                    } else {
                        "i64.sub"
                    });
                    self.emit_set_path(expr)?;
                    self.push(format!("local.get ${temp}"));
                }
            },
            Expr::Binary { lhs, op, rhs } => self.emit_binary(lhs, *op, rhs)?,
            Expr::Cast { expr, ty } => {
                let source_ty = infer_codegen_expr_type(expr, self.function, self.backend.info)?;
                self.emit_expr(expr)?;
                let instruction = cast_instruction(&source_ty, ty, self.backend.info)?;
                if let Some(instruction) = instruction {
                    self.push(instruction);
                }
            }
            Expr::BitCast { expr, .. } => self.emit_expr(expr)?,
            Expr::SizeOf(ty) => {
                let (size, _) = self.backend.type_size_align(ty)?;
                self.push(format!("i64.const {size}"));
            }
            Expr::Call { callee, args } => self.emit_call(callee, args)?,
            Expr::BuiltinCall { name, args } => self.emit_builtin(name, args)?,
            Expr::StructInit { name, fields, .. } => {
                let (size, offsets) = self.backend.struct_layout(name)?;
                let temp = self.temp("i32");
                self.push(format!("i32.const {size}"));
                self.push("call $alloc");
                self.push(format!("local.set ${temp}"));
                let type_info = self
                    .backend
                    .info
                    .types
                    .get(name)
                    .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
                for field in fields {
                    let field_ty =
                        type_info
                            .field_map
                            .get(&field.name)
                            .cloned()
                            .ok_or_else(|| {
                                CompileError::new(format!(
                                    "type `{name}` has no field `{}`",
                                    field.name
                                ))
                            })?;
                    let offset = offsets
                        .get(&field.name)
                        .copied()
                        .ok_or_else(|| CompileError::new("unknown field"))?;
                    self.push(format!("local.get ${temp}"));
                    self.emit_expr(&field.value)?;
                    let store = self.store_instruction(&field_ty)?;
                    self.push(format!("{store} offset={offset}"));
                }
                self.push(format!("local.get ${temp}"));
            }
            Expr::FieldAccess { base, field } => {
                let ty = infer_codegen_expr_type(expr, self.function, self.backend.info)?;
                let (_, fields) = self.struct_layout_for_expr(base)?;
                let offset = *fields
                    .get(field)
                    .ok_or_else(|| CompileError::new(format!("unknown field `{field}`")))?;
                self.emit_expr(base)?;
                let load = self.load_instruction(&ty)?;
                self.push(format!("{load} offset={offset}"));
            }
            Expr::Index { .. } => {
                return Err(CompileError::new(
                    "wasm backend does not yet support indexing",
                ));
            }
            Expr::MethodCall { .. } => {
                return Err(CompileError::new(
                    "wasm backend does not yet support methods",
                ));
            }
            Expr::Specialize { .. } => {
                return Err(CompileError::new(
                    "wasm backend does not support unresolved generic specialization",
                ));
            }
            Expr::Error { .. } | Expr::Try(_) => {
                return Err(CompileError::new(
                    "wasm backend does not yet support result propagation",
                ));
            }
            Expr::Pack(_) => return Err(CompileError::new("packed expression outside of @print")),
            Expr::ListLiteral(_) => {
                return Err(CompileError::new(
                    "wasm backend does not yet support list literals",
                ));
            }
        }
        Ok(())
    }

    fn emit_binary(&mut self, lhs: &Expr, op: BinaryOp, rhs: &Expr) -> Result<(), CompileError> {
        if matches!(op, BinaryOp::LogicalAnd | BinaryOp::LogicalOr) {
            self.emit_cond(lhs)?;
            self.push("if (result i32)");
            if op == BinaryOp::LogicalOr {
                self.push("  i32.const 1");
                self.push("else");
                self.emit_cond(rhs)?;
            } else {
                self.emit_cond(rhs)?;
                self.push("else");
                self.push("  i32.const 0");
            }
            self.push("end");
            return Ok(());
        }
        let lhs_ty = infer_codegen_expr_type(lhs, self.function, self.backend.info)?;
        let rhs_ty = infer_codegen_expr_type(rhs, self.function, self.backend.info)?;
        let lhs_aliased = crate::codegen::resolve_codegen_aliases(&lhs_ty, self.backend.info)?;
        let is_float = matches!(lhs_aliased, Type::F32 | Type::F64);
        let is_signed = is_codegen_signed_integer_type(&lhs_aliased);
        let is_pointer = matches!(
            lhs_aliased,
            Type::Ref(_) | Type::Mut(_) | Type::Named(_) | Type::None | Type::FnPtr(_, _)
        );
        let both_bool = matches!(lhs_aliased, Type::Bool)
            && matches!(
                crate::codegen::resolve_codegen_aliases(&rhs_ty, self.backend.info)?,
                Type::Bool
            );
        self.emit_expr(lhs)?;
        self.emit_expr(rhs)?;
        let instruction = match op {
            BinaryOp::Add => {
                if is_float {
                    "f64.add"
                } else {
                    "i64.add"
                }
            }
            BinaryOp::Subtract => {
                if is_float {
                    "f64.sub"
                } else {
                    "i64.sub"
                }
            }
            BinaryOp::Multiply => {
                if is_float {
                    "f64.mul"
                } else {
                    "i64.mul"
                }
            }
            BinaryOp::Divide => {
                if is_float {
                    "f64.div"
                } else if is_signed {
                    "i64.div_s"
                } else {
                    "i64.div_u"
                }
            }
            BinaryOp::Modulo => {
                if is_float {
                    return Err(CompileError::new(
                        "wasm backend does not support floating-point modulo",
                    ));
                }
                if is_signed { "i64.rem_s" } else { "i64.rem_u" }
            }
            BinaryOp::BitAnd => "i64.and",
            BinaryOp::BitOr => "i64.or",
            BinaryOp::BitXor => "i64.xor",
            BinaryOp::ShiftLeft => "i64.shl",
            BinaryOp::ShiftRight => "i64.shr_u",
            BinaryOp::LessThan
            | BinaryOp::LessEqual
            | BinaryOp::GreaterThan
            | BinaryOp::GreaterEqual
            | BinaryOp::Equal
            | BinaryOp::NotEqual => {
                if is_float {
                    match op {
                        BinaryOp::LessThan => "f64.lt",
                        BinaryOp::LessEqual => "f64.le",
                        BinaryOp::GreaterThan => "f64.gt",
                        BinaryOp::GreaterEqual => "f64.ge",
                        BinaryOp::Equal => "f64.eq",
                        BinaryOp::NotEqual => "f64.ne",
                        _ => unreachable!(),
                    }
                } else if both_bool || is_pointer {
                    match op {
                        BinaryOp::Equal => "i32.eq",
                        BinaryOp::NotEqual => "i32.ne",
                        BinaryOp::LessThan => "i32.lt_u",
                        BinaryOp::LessEqual => "i32.le_u",
                        BinaryOp::GreaterThan => "i32.gt_u",
                        BinaryOp::GreaterEqual => "i32.ge_u",
                        _ => unreachable!(),
                    }
                } else if is_signed {
                    match op {
                        BinaryOp::LessThan => "i64.lt_s",
                        BinaryOp::LessEqual => "i64.le_s",
                        BinaryOp::GreaterThan => "i64.gt_s",
                        BinaryOp::GreaterEqual => "i64.ge_s",
                        BinaryOp::Equal => "i64.eq",
                        BinaryOp::NotEqual => "i64.ne",
                        _ => unreachable!(),
                    }
                } else {
                    match op {
                        BinaryOp::LessThan => "i64.lt_u",
                        BinaryOp::LessEqual => "i64.le_u",
                        BinaryOp::GreaterThan => "i64.gt_u",
                        BinaryOp::GreaterEqual => "i64.ge_u",
                        BinaryOp::Equal => "i64.eq",
                        BinaryOp::NotEqual => "i64.ne",
                        _ => unreachable!(),
                    }
                }
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => unreachable!(),
        };
        self.push(instruction);
        Ok(())
    }

    fn emit_call(&mut self, callee: &Expr, args: &[Expr]) -> Result<(), CompileError> {
        let Some(path) = callee.callee_path() else {
            return Err(CompileError::new("wasm backend only supports direct calls"));
        };
        let name = path.join(".");
        let signature = self
            .backend
            .info
            .functions
            .get(&name)
            .cloned()
            .ok_or_else(|| CompileError::new(format!("unknown function `{name}`")))?;
        for (arg, ty) in args.iter().zip(signature.params.iter()) {
            self.emit_expr(arg)?;
            let want = self.backend.wasm_type(ty)?;
            let got = self.backend.wasm_type(&infer_codegen_expr_type(
                arg,
                self.function,
                self.backend.info,
            )?)?;
            if want != got {
                if want == "i64" && got == "i32" {
                    self.push("i64.extend_i32_u");
                } else if want == "i32" && got == "i64" {
                    self.push("i32.wrap_i64");
                }
            }
        }
        let symbol = self
            .backend
            .info
            .function_symbols
            .get(&name)
            .cloned()
            .unwrap_or(name);
        self.push(format!("call ${symbol}"));
        Ok(())
    }

    fn emit_builtin(&mut self, name: &str, args: &[Expr]) -> Result<(), CompileError> {
        match name {
            "puts" => {
                self.emit_expr(&args[0])?;
                self.push("call $puts_str");
            }
            "print" => self.emit_print(args)?,
            "flush" => {}
            "alloc" => {
                self.emit_expr(&args[0])?;
                self.push("i32.wrap_i64");
                self.push("call $alloc");
            }
            "free" => {}
            "realloc" => {
                let old = self.temp("i32");
                let size = self.temp("i32");
                self.emit_expr(&args[0])?;
                self.push(format!("local.set ${old}"));
                self.emit_expr(&args[1])?;
                self.push("i32.wrap_i64");
                self.push(format!("local.tee ${size}"));
                self.push("call $alloc");
                let new = self.temp("i32");
                self.push(format!("local.set ${new}"));
                self.push(format!("local.get ${new}"));
                self.push(format!("local.get ${old}"));
                self.push(format!("local.get ${size}"));
                self.push("memory.copy");
                self.push(format!("local.get ${new}"));
            }
            "memcpy" => {
                self.emit_expr(&args[0])?;
                self.emit_expr(&args[1])?;
                self.emit_expr(&args[2])?;
                self.push("i32.wrap_i64");
                self.push("memory.copy");
            }
            "memset" => {
                self.emit_expr(&args[0])?;
                self.emit_expr(&args[1])?;
                self.push("i32.wrap_i64");
                self.emit_expr(&args[2])?;
                self.push("i32.wrap_i64");
                self.push("memory.fill");
            }
            "zeroed" => self.push("i64.const 0"),
            "addr" => {
                let arg_ty = infer_codegen_expr_type(&args[0], self.function, self.backend.info)?;
                if matches!(
                    arg_ty,
                    Type::Named(_) | Type::Ref(_) | Type::Mut(_) | Type::List(_)
                ) {
                    self.emit_expr(&args[0])?;
                } else {
                    let slot = self.temp("i32");
                    let size = self.backend.type_size_align(&arg_ty)?.0.max(1);
                    self.push(format!("i32.const {size}"));
                    self.push("call $alloc");
                    self.push(format!("local.set ${slot}"));
                    self.push(format!("local.get ${slot}"));
                    self.emit_expr(&args[0])?;
                    let store = self.store_instruction(&arg_ty)?;
                    self.push(store);
                    self.push(format!("local.get ${slot}"));
                }
            }
            "deref" => {
                let ty = infer_codegen_expr_type(&args[0], self.function, self.backend.info)?;
                let inner = match ty {
                    Type::Ref(inner) | Type::Mut(inner) => *inner,
                    other => {
                        return Err(CompileError::new(format!(
                            "@deref requires a reference, got {}",
                            crate::codegen::describe_type(&other)
                        )));
                    }
                };
                self.emit_expr(&args[0])?;
                let load = self.load_instruction(&inner)?;
                self.push(load);
            }
            "neg" => {
                self.emit_expr(&args[0])?;
                self.push("i64.const -1");
                self.push("i64.mul");
            }
            "shl" => {
                self.emit_expr(&args[0])?;
                self.emit_expr(&args[1])?;
                self.push("i64.shl");
            }
            "shr" => {
                self.emit_expr(&args[0])?;
                self.emit_expr(&args[1])?;
                self.push("i64.shr_u");
            }
            "as_mut" => self.emit_expr(&args[0])?,
            "add" => {
                let arg_ty = infer_codegen_expr_type(&args[0], self.function, self.backend.info)?;
                let scale = match arg_ty {
                    Type::Ref(inner) | Type::Mut(inner) => {
                        self.backend.type_size_align(&inner)?.0.max(1)
                    }
                    Type::Named(name) => self.backend.type_size_align(&Type::Named(name))?.0.max(1),
                    _ => 1,
                };
                self.emit_expr(&args[0])?;
                self.emit_expr(&args[1])?;
                self.push("i32.wrap_i64");
                self.push(format!("i32.const {scale}"));
                self.push("i32.mul");
                self.push("i32.add");
            }
            other => {
                return Err(CompileError::new(format!(
                    "wasm backend does not yet support builtin @{other}"
                )));
            }
        }
        Ok(())
    }

    fn emit_print(&mut self, args: &[Expr]) -> Result<(), CompileError> {
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
                    let (offset, len) = self.backend.intern(&literal);
                    self.push(format!("i32.const {offset}"));
                    self.push(format!("i32.const {len}"));
                    self.push("call $write");
                    literal.clear();
                }
                let marker: String = chars[start..end].iter().collect();
                let arg = flattened.get(arg_index).copied().ok_or_else(|| {
                    CompileError::new("@print format expects more values than were provided")
                })?;
                let ty = infer_codegen_expr_type(arg, self.function, self.backend.info)?;
                self.emit_expr(arg)?;
                self.emit_print_value(&marker, &ty)?;
                arg_index += 1;
                index = end + 1;
                continue;
            }
            literal.push(chars[index]);
            index += 1;
        }
        if !literal.is_empty() {
            let (offset, len) = self.backend.intern(&literal);
            self.push(format!("i32.const {offset}"));
            self.push(format!("i32.const {len}"));
            self.push("call $write");
        }
        Ok(())
    }

    fn emit_print_value(&mut self, marker: &str, ty: &Type) -> Result<(), CompileError> {
        let base = marker.trim_start_matches(|c: char| c.is_ascii_digit());
        match base {
            "d" | "ld" | "lld" => {
                if matches!(
                    ty,
                    Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize
                ) {
                    self.push("call $print_u64");
                } else {
                    self.push("call $print_i64");
                }
            }
            "u" | "lu" | "llu" | "zu" => self.push("call $print_u64"),
            "x" | "lx" | "llx" | "X" | "lX" | "llX" | "o" | "lo" | "llo" => {
                self.push("call $print_hex");
            }
            "b" => self.push("call $print_bool"),
            "p" => self.push("call $print_ptr"),
            "s" => self.push("call $print_str"),
            "f" | "lf" | "e" | "E" | "g" | "G" => self.push("call $print_float"),
            "c" => {
                self.push("i32.wrap_i64");
                self.push("call $print_char");
            }
            other => {
                return Err(CompileError::new(format!(
                    "unsupported @print marker `{{{other}}}` in wasm backend"
                )));
            }
        }
        Ok(())
    }

    fn load_instruction(&self, ty: &Type) -> Result<&'static str, CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.backend.info)?;
        Ok(match ty {
            Type::Bool => "i32.load8_u",
            Type::I8 | Type::U8 => "i64.load8_u",
            Type::I16 | Type::U16 => "i64.load16_u",
            Type::I32 | Type::U32 => "i64.load32_u",
            Type::F32 | Type::F64 => "f64.load",
            Type::Ref(_)
            | Type::Mut(_)
            | Type::Named(_)
            | Type::List(_)
            | Type::FixedArray(_, _)
            | Type::Result(_)
            | Type::Error
            | Type::None
            | Type::FnPtr(_, _) => "i32.load",
            _ => "i64.load",
        })
    }

    fn store_instruction(&self, ty: &Type) -> Result<&'static str, CompileError> {
        let ty = crate::codegen::resolve_codegen_aliases(ty, self.backend.info)?;
        Ok(match ty {
            Type::Bool => "i32.store8",
            Type::I8 | Type::U8 => "i64.store8",
            Type::I16 | Type::U16 => "i64.store16",
            Type::I32 | Type::U32 => "i64.store32",
            Type::F32 | Type::F64 => "f64.store",
            Type::Ref(_)
            | Type::Mut(_)
            | Type::Named(_)
            | Type::List(_)
            | Type::FixedArray(_, _)
            | Type::Result(_)
            | Type::Error
            | Type::None
            | Type::FnPtr(_, _) => "i32.store",
            _ => "i64.store",
        })
    }
}

fn cast_instruction(
    source: &Type,
    target: &Type,
    info: &ProgramInfo,
) -> Result<Option<&'static str>, CompileError> {
    let source = crate::codegen::resolve_codegen_aliases(source, info)?;
    let target = crate::codegen::resolve_codegen_aliases(target, info)?;
    let source_float = matches!(source, Type::F32 | Type::F64);
    let target_float = matches!(target, Type::F32 | Type::F64);
    let source_pointer = matches!(
        source,
        Type::Ref(_) | Type::Mut(_) | Type::Named(_) | Type::None
    );
    let target_pointer = matches!(
        target,
        Type::Ref(_) | Type::Mut(_) | Type::Named(_) | Type::None
    );
    Ok(if source_float && target_float {
        None
    } else if source_float && !target_float {
        if target_pointer {
            Some("i32.trunc_f64_s")
        } else if is_codegen_signed_integer_type(&target) {
            Some("i64.trunc_f64_s")
        } else {
            Some("i64.trunc_f64_u")
        }
    } else if !source_float && target_float {
        if source_pointer {
            Some("f64.convert_i32_s")
        } else if is_codegen_signed_integer_type(&source) {
            Some("f64.convert_i64_s")
        } else {
            Some("f64.convert_i64_u")
        }
    } else if target_pointer && !source_pointer {
        Some("i32.wrap_i64")
    } else if !target_pointer && source_pointer {
        if target_float {
            Some("f64.convert_i32_s")
        } else {
            Some("i64.extend_i32_u")
        }
    } else {
        None
    })
}

fn collect_local_names(body: &[Stmt], names: &mut Vec<String>) {
    for stmt in body {
        match stmt {
            Stmt::VarDecl { name, .. } => {
                if !names.contains(name) {
                    names.push(name.clone());
                }
            }
            Stmt::Defer { body, .. } | Stmt::Block(body) | Stmt::Loop { body, .. } => {
                collect_local_names(body, names)
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_local_names(then_body, names);
                collect_local_names(else_body, names);
            }
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    for binding in arm.bindings.iter().flatten() {
                        if !names.contains(binding) {
                            names.push(binding.clone());
                        }
                    }
                    collect_local_names(&arm.body, names);
                }
            }
            Stmt::ForRange { var_name, body, .. }
            | Stmt::ForEach { var_name, body, .. }
            | Stmt::ForClassic { var_name, body, .. } => {
                if !names.contains(var_name) {
                    names.push(var_name.clone());
                }
                collect_local_names(body, names);
            }
            Stmt::While { body, .. } => collect_local_names(body, names),
            _ => {}
        }
    }
}

fn default_value(ty: &str) -> &'static str {
    match ty {
        "i32" => "i32.const 0",
        "i64" => "i64.const 0",
        "f64" => "f64.const 0",
        _ => "i32.const 0",
    }
}

fn float_literal(value: f64) -> String {
    if value.is_nan() {
        "nan".to_string()
    } else if value.is_infinite() {
        if value.is_sign_negative() {
            "-inf".to_string()
        } else {
            "inf".to_string()
        }
    } else if value.fract() == 0.0 {
        format!("{value:.1}")
    } else {
        format!("{value}")
    }
}

fn align_to(value: u32, align: u32) -> u32 {
    if align <= 1 {
        value
    } else {
        value.div_ceil(align) * align
    }
}

fn runtime_wat(
    newline_offset: u32,
    true_offset: u32,
    _true_len: u32,
    false_offset: u32,
    _false_len: u32,
    zero_offset: u32,
) -> String {
    format!(
        r#"  (func $write (param $ptr i32) (param $len i32)
    i32.const 0
    local.get $ptr
    i32.store
    i32.const 4
    local.get $len
    i32.store
    i32.const 1
    i32.const 0
    i32.const 1
    i32.const 8
    call $fd_write
    drop
  )

  (func $strlen_i32 (param $ptr i32) (result i32)
    (local $n i32)
    block $done
      loop $loop
        local.get $ptr
        local.get $n
        i32.add
        i32.load8_u
        i32.eqz
        br_if $done
        local.get $n
        i32.const 1
        i32.add
        local.set $n
        br $loop
      end
    end
    local.get $n
  )

  (func $puts_str (param $ptr i32)
    local.get $ptr
    local.get $ptr
    call $strlen_i32
    call $write
    i32.const {newline_offset}
    i32.const 1
    call $write
  )

  (func $print_str (param $ptr i32)
    local.get $ptr
    local.get $ptr
    call $strlen_i32
    call $write
  )

  (func $print_char (param $value i32)
    i32.const 96
    local.get $value
    i32.store8
    i32.const 96
    i32.const 1
    call $write
  )

  (func $print_bool (param $value i32)
    local.get $value
    if
      i32.const {true_offset}
      i32.const 4
      call $write
    else
      i32.const {false_offset}
      i32.const 5
      call $write
    end
  )

  (func $print_i64 (param $value i64)
    local.get $value
    i64.const 0
    i64.lt_s
    if
      i32.const 100
      i32.const 45
      i32.store8
      i32.const 100
      i32.const 1
      call $write
      i64.const 0
      local.get $value
      i64.sub
      local.set $value
    end
    local.get $value
    call $print_u64_raw
  )

  (func $print_u64 (param $value i64)
    local.get $value
    call $print_u64_raw
  )

  (func $print_u64_raw (param $value i64)
    (local $pos i32) (local $u i64)
    i32.const 160
    local.set $pos
    local.get $value
    local.set $u
    block $done
      loop $loop
        local.get $pos
        i32.const 1
        i32.sub
        local.tee $pos
        local.get $u
        i64.const 10
        i64.rem_u
        i32.wrap_i64
        i32.const 48
        i32.add
        i32.store8
        local.get $u
        i64.const 10
        i64.div_u
        local.tee $u
        i64.eqz
        br_if $done
        br $loop
      end
    end
    local.get $pos
    i32.const 160
    local.get $pos
    i32.sub
    call $write
  )

  (func $print_hex (param $value i64)
    (local $pos i32) (local $u i64) (local $digit i32)
    i32.const 192
    local.set $pos
    local.get $value
    local.set $u
    block $done
      loop $loop
        local.get $pos
        i32.const 1
        i32.sub
        local.tee $pos
        local.get $u
        i32.wrap_i64
        i32.const 15
        i32.and
        local.tee $digit
        i32.const 10
        i32.lt_u
        if (result i32)
          local.get $digit
          i32.const 48
          i32.add
        else
          local.get $digit
          i32.const 87
          i32.add
        end
        i32.store8
        local.get $u
        i64.const 4
        i64.shr_u
        local.tee $u
        i64.eqz
        br_if $done
        br $loop
      end
    end
    local.get $pos
    i32.const 192
    local.get $pos
    i32.sub
    call $write
  )

  (func $print_ptr (param $value i32)
    i32.const 224
    i32.const 48
    i32.store8
    i32.const 225
    i32.const 120
    i32.store8
    i32.const 224
    i32.const 2
    call $write
    local.get $value
    i64.extend_i32_u
    call $print_hex
  )

  (func $print_float (param $value f64)
    local.get $value
    i64.trunc_f64_s
    call $print_i64
    i32.const 240
    i32.const 46
    i32.store8
    i32.const 240
    i32.const 1
    call $write
    local.get $value
    f64.abs
    f64.floor
    local.get $value
    f64.abs
    f64.sub
    f64.const 1000000
    f64.mul
    f64.nearest
    i64.trunc_f64_u
    call $print_zero_padded
  )

  (func $print_zero_padded (param $value i64)
    (local $digits i64)
    local.get $value
    local.set $digits
    local.get $value
    i64.const 100000
    i64.lt_u
    if
      i32.const {zero_offset}
      i32.const 1
      call $write
    end
    local.get $value
    i64.const 10000
    i64.lt_u
    if
      i32.const {zero_offset}
      i32.const 1
      call $write
    end
    local.get $value
    i64.const 1000
    i64.lt_u
    if
      i32.const {zero_offset}
      i32.const 1
      call $write
    end
    local.get $value
    i64.const 100
    i64.lt_u
    if
      i32.const {zero_offset}
      i32.const 1
      call $write
    end
    local.get $value
    i64.const 10
    i64.lt_u
    if
      i32.const {zero_offset}
      i32.const 1
      call $write
    end
    local.get $digits
    call $print_u64_raw
  )

  (func $alloc (param $size i32) (result i32)
    (local $ptr i32)
    global.get $heap
    local.set $ptr
    global.get $heap
    local.get $size
    i32.add
    i32.const 7
    i32.add
    i32.const -8
    i32.and
    global.set $heap
    local.get $ptr
  )

"#
    )
}

fn wasm_extern_runtime(name: &str) -> Option<String> {
    let source = match name {
        "strlen" => {
            r#"  (func $strlen (param $ptr i32) (result i64)
    local.get $ptr
    call $strlen_i32
    i64.extend_i32_u
  )
"#
        }
        "strcmp" => {
            r#"  (func $strcmp (param $a i32) (param $b i32) (result i64)
    (local $i i32) (local $ca i32) (local $cb i32)
    block $done
      loop $loop
        local.get $a
        local.get $i
        i32.add
        i32.load8_u
        local.set $ca
        local.get $b
        local.get $i
        i32.add
        i32.load8_u
        local.set $cb
        local.get $ca
        local.get $cb
        i32.ne
        br_if $done
        local.get $ca
        i32.eqz
        br_if $done
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $loop
      end
    end
    local.get $ca
    local.get $cb
    i32.sub
    i64.extend_i32_s
  )
"#
        }
        "strcpy" => {
            r#"  (func $strcpy (param $dest i32) (param $src i32) (result i32)
    (local $i i32) (local $c i32)
    block $done
      loop $loop
        local.get $src
        local.get $i
        i32.add
        i32.load8_u
        local.tee $c
        local.get $dest
        local.get $i
        i32.add
        i32.store8
        local.get $c
        i32.eqz
        br_if $done
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $loop
      end
    end
    local.get $dest
  )
"#
        }
        "strncpy" => {
            r#"  (func $strncpy (param $dest i32) (param $src i32) (param $n i64) (result i32)
    (local $i i32) (local $c i32)
    block $done
      loop $loop
        local.get $i
        i64.extend_i32_u
        local.get $n
        i64.ge_u
        br_if $done
        local.get $src
        local.get $i
        i32.add
        i32.load8_u
        local.tee $c
        local.get $dest
        local.get $i
        i32.add
        i32.store8
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        local.get $c
        i32.eqz
        br_if $done
        br $loop
      end
    end
    local.get $dest
  )
"#
        }
        "strcat" => {
            r#"  (func $strcat (param $dest i32) (param $src i32) (result i32)
    (local $d i32) (local $i i32) (local $c i32)
    local.get $dest
    call $strlen_i32
    local.set $d
    block $done
      loop $loop
        local.get $src
        local.get $i
        i32.add
        i32.load8_u
        local.tee $c
        local.get $dest
        local.get $d
        i32.add
        local.get $i
        i32.add
        i32.store8
        local.get $c
        i32.eqz
        br_if $done
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $loop
      end
    end
    local.get $dest
  )
"#
        }
        _ => return None,
    };
    Some(source.to_string())
}
