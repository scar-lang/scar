use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::{
    CompileError, CompileErrors,
    ast::{
        BinaryOp, Expr, FieldDef, Function, InterfaceMethod, MatchArmKind, Program, Stmt,
        TestBlock, Type, TypeDefKind, UnaryOp, UnionVariantDef,
    },
};

#[derive(Debug, Clone)]
pub struct FunctionSig {
    pub params: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct TypeDefInfo {
    pub kind: TypeDefKind,
    pub fields: Vec<FieldDef>,
    pub field_map: HashMap<String, Type>,
    pub alias: Option<Type>,
    pub derives: Vec<Type>,
    pub variants: Vec<UnionVariantDef>,
    pub variant_map: HashMap<String, Vec<Type>>,
}

#[derive(Debug, Clone)]
pub struct InterfaceDefInfo {
    pub methods: Vec<InterfaceMethod>,
}

#[derive(Debug)]
pub struct ProgramInfo {
    pub functions: HashMap<String, FunctionSig>,
    pub function_symbols: HashMap<String, String>,
    pub types: HashMap<String, TypeDefInfo>,
    pub locals: HashMap<String, HashMap<String, Type>>,
    pub globals: HashMap<String, (Type, bool)>, // name -> (type, mutable)
    pub scope_overrides: RefCell<HashMap<String, Type>>,
}

#[derive(Debug, Clone)]
struct LocalBinding {
    ty: Type,
    mutable: bool,
    used: bool,
    mutated: bool,
    is_global: bool,
}

pub fn analyze(program: &Program) -> Result<ProgramInfo, CompileErrors> {
    let interfaces = collect_interfaces(program).map_err(CompileErrors::single)?;
    let types = collect_types(program).map_err(CompileErrors::single)?;
    let mut functions = HashMap::new();
    let mut function_symbols = HashMap::new();

    for function in &program.functions {
        if functions.contains_key(&function.name) {
            return Err(CompileErrors::single(
                CompileError::new(format!("duplicate function definition `{}`", function.name))
                    .with_file_opt(function.file_path.clone()),
            ));
        }
        if function.name == "main" && !function.is_pub {
            return Err(CompileErrors::single(
                CompileError::new("function `main` must be declared as `pub def main`")
                    .with_file_opt(function.file_path.clone()),
            ));
        }
        validate_type(&function.return_type, &types).map_err(|e| {
            CompileErrors::single(
                CompileError::new(format!("in function `{}`: {}", function.name, e.message()))
                    .with_location(function.line, function.column)
                    .with_file_opt(function.file_path.clone()),
            )
        })?;
        functions.insert(
            function.name.clone(),
            FunctionSig {
                params: function
                    .params
                    .iter()
                    .map(|param| {
                        validate_type(&param.ty, &types).map_err(|e| {
                            CompileErrors::single(
                                CompileError::new(format!(
                                    "in function `{}`, parameter `{}`: {}",
                                    function.name,
                                    param.name,
                                    e.message()
                                ))
                                .with_location(param.line, param.column)
                                .with_file_opt(function.file_path.clone()),
                            )
                        })?;
                        Ok(param.ty.clone())
                    })
                    .collect::<Result<Vec<_>, CompileErrors>>()?,
                return_type: function.return_type.clone(),
            },
        );
        function_symbols.insert(
            function.name.clone(),
            function
                .extern_name
                .clone()
                .unwrap_or_else(|| mangle_function_symbol(&function.name)),
        );
    }

    let mut locals = HashMap::new();
    let mut globals = HashMap::new();

    for global in &program.globals {
        validate_type(&global.ty, &types).map_err(|e| {
            CompileErrors::single(
                CompileError::new(format!("in global `{}`: {}", global.name, e.message()))
                    .with_location(global.line, global.column)
                    .with_file_opt(global.file_path.clone()),
            )
        })?;
        let actual = infer_expr_type(
            &global.init,
            &functions,
            &types,
            &HashMap::new(),
            Some(&global.ty),
        )
        .map_err(|e| {
            CompileErrors::single(
                e.with_location(global.line, global.column)
                    .with_file_opt(global.file_path.clone()),
            )
        })?;
        if !matches!(global.init, Expr::BuiltinCall { ref name, .. } if name == "zeroed") {
            expect_same_type(&global.ty, &actual, &types, "global initializer").map_err(|e| {
                CompileErrors::single(
                    e.with_location(global.line, global.column)
                        .with_file_opt(global.file_path.clone()),
                )
            })?;
        }
        globals.insert(global.name.clone(), (global.ty.clone(), global.mutable));
    }

    let global_scope: HashMap<String, LocalBinding> = globals
        .iter()
        .map(|(name, (ty, mutable))| {
            (
                name.clone(),
                LocalBinding {
                    ty: ty.clone(),
                    mutable: *mutable,
                    used: true,
                    mutated: false,
                    is_global: true,
                },
            )
        })
        .collect();

    let mut all_errors = CompileErrors::new();
    for function in &program.functions {
        if let Err(errors) =
            analyze_function_with_globals(function, &functions, &types, &mut locals, &global_scope)
        {
            all_errors.extend(errors);
            if all_errors.is_full() {
                return Err(all_errors);
            }
        }
    }
    for test in &program.tests {
        if let Err(errors) = analyze_test_block(test, &functions, &types) {
            all_errors.extend(errors);
            if all_errors.is_full() {
                return Err(all_errors);
            }
        }
    }
    if !all_errors.is_empty() {
        return Err(all_errors);
    }
    validate_interface_satisfaction(&interfaces, &types, &functions)
        .map_err(CompileErrors::single)?;

    Ok(ProgramInfo {
        functions,
        function_symbols,
        types,
        locals,
        globals,
        scope_overrides: RefCell::new(HashMap::new()),
    })
}

fn mangle_function_symbol(name: &str) -> String {
    format!("fn__{}", sanitize_symbol_name(name))
}

fn sanitize_symbol_name(name: &str) -> String {
    name.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn collect_types(program: &Program) -> Result<HashMap<String, TypeDefInfo>, CompileError> {
    let known_type_names: HashSet<String> = program
        .type_defs
        .iter()
        .map(|def| def.name.clone())
        .chain(program.interface_defs.iter().map(|def| def.name.clone()))
        .collect();
    let mut types = HashMap::new();

    for type_def in &program.type_defs {
        if types.contains_key(&type_def.name) {
            return Err(CompileError::new(format!(
                "duplicate type definition `{}`",
                type_def.name
            ))
            .with_file_opt(type_def.file_path.clone()));
        }

        let mut field_map = HashMap::new();
        let mut variant_map = HashMap::new();

        let mut process_type_def = || -> Result<(), CompileError> {
            if let Some(alias) = &type_def.alias {
                if !type_def.fields.is_empty() || !type_def.variants.is_empty() {
                    return Err(CompileError::new(format!(
                        "type `{}` cannot declare both an alias and fields",
                        type_def.name
                    )));
                }
                if type_def.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "union `{}` cannot be declared as an alias",
                        type_def.name
                    )));
                }
                validate_type_with_known_names(alias, &known_type_names).map_err(|e| {
                    CompileError::new(format!("in type `{}`: {}", type_def.name, e.message()))
                        .with_location(type_def.line, type_def.column)
                })?;
            } else {
                for derive in &type_def.derives {
                    validate_type_with_known_names(derive, &known_type_names).map_err(|e| {
                        CompileError::new(format!("in type `{}`: {}", type_def.name, e.message()))
                            .with_location(type_def.line, type_def.column)
                    })?;
                }
                match type_def.kind {
                    TypeDefKind::Struct => {
                        for field in &type_def.fields {
                            if field_map.contains_key(&field.name) {
                                return Err(CompileError::new(format!(
                                    "duplicate field `{}` in type `{}`",
                                    field.name, type_def.name
                                )));
                            }
                            validate_type_with_known_names(&field.ty, &known_type_names).map_err(
                                |e| {
                                    CompileError::new(format!(
                                        "in type `{}`, field `{}`: {}",
                                        type_def.name,
                                        field.name,
                                        e.message()
                                    ))
                                    .with_location(field.line, field.column)
                                },
                            )?;
                            field_map.insert(field.name.clone(), field.ty.clone());
                        }
                    }
                    TypeDefKind::Union => {
                        if type_def.is_extern {
                            return Err(CompileError::new(format!(
                                "extern unions are not supported: `{}`",
                                type_def.name
                            )));
                        }
                        for variant in &type_def.variants {
                            if variant_map.contains_key(&variant.name) {
                                return Err(CompileError::new(format!(
                                    "duplicate variant `{}` in union `{}`",
                                    variant.name, type_def.name
                                )));
                            }
                            for payload_ty in &variant.payload_types {
                                validate_type_with_known_names(payload_ty, &known_type_names)
                                    .map_err(|e| {
                                        CompileError::new(format!(
                                            "in type `{}`, variant `{}`: {}",
                                            type_def.name,
                                            variant.name,
                                            e.message()
                                        ))
                                        .with_location(type_def.line, type_def.column)
                                    })?;
                            }
                            variant_map.insert(variant.name.clone(), variant.payload_types.clone());
                        }
                    }
                    TypeDefKind::Enum => {
                        for variant in &type_def.variants {
                            if variant_map.contains_key(&variant.name) {
                                return Err(CompileError::new(format!(
                                    "duplicate variant `{}` in enum `{}`",
                                    variant.name, type_def.name
                                )));
                            }
                            variant_map.insert(variant.name.clone(), vec![]);
                        }
                    }
                }
            }
            Ok(())
        };

        process_type_def().map_err(|e| e.with_file_opt(type_def.file_path.clone()))?;

        types.insert(
            type_def.name.clone(),
            TypeDefInfo {
                kind: type_def.kind,
                fields: type_def.fields.clone(),
                field_map,
                alias: type_def.alias.clone(),
                derives: type_def.derives.clone(),
                variants: type_def.variants.clone(),
                variant_map,
            },
        );
    }

    Ok(types)
}

fn collect_interfaces(
    program: &Program,
) -> Result<HashMap<String, InterfaceDefInfo>, CompileError> {
    let known_names: HashSet<String> = program
        .type_defs
        .iter()
        .map(|def| def.name.clone())
        .chain(program.interface_defs.iter().map(|def| def.name.clone()))
        .collect();
    let mut interfaces = HashMap::new();
    for interface_def in &program.interface_defs {
        if interfaces.contains_key(&interface_def.name) {
            return Err(CompileError::new(format!(
                "duplicate interface definition `{}`",
                interface_def.name
            ))
            .with_file_opt(interface_def.file_path.clone()));
        }
        let mut methods = Vec::new();
        let mut seen = HashSet::new();

        let mut process_interface_def = || -> Result<(), CompileError> {
            for method in &interface_def.methods {
                if !seen.insert(method.name.clone()) {
                    return Err(CompileError::new(format!(
                        "duplicate interface method `{}` in `{}`",
                        method.name, interface_def.name
                    )));
                }
                for param in &method.params {
                    validate_type_with_known_names(&param.ty, &known_names).map_err(|e| {
                        CompileError::new(format!(
                            "in interface `{}`, method `{}`, parameter `{}`: {}",
                            interface_def.name,
                            method.name,
                            param.name,
                            e.message()
                        ))
                    })?;
                }
                validate_type_with_known_names(&method.return_type, &known_names).map_err(|e| {
                    CompileError::new(format!(
                        "in interface `{}`, method `{}` return type: {}",
                        interface_def.name,
                        method.name,
                        e.message()
                    ))
                })?;
                methods.push(method.clone());
            }
            Ok(())
        };

        process_interface_def().map_err(|e| e.with_file_opt(interface_def.file_path.clone()))?;
        interfaces.insert(interface_def.name.clone(), InterfaceDefInfo { methods });
    }
    Ok(interfaces)
}

fn analyze_function_with_globals(
    function: &Function,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    locals: &mut HashMap<String, HashMap<String, Type>>,
    global_scope: &HashMap<String, LocalBinding>,
) -> Result<(), CompileErrors> {
    let mut scope = global_scope.clone();
    let mut function_locals = HashMap::new();

    for param in &function.params {
        validate_type(&param.ty, types).map_err(|e| {
            CompileErrors::single(
                CompileError::new(format!(
                    "in function `{}`, parameter `{}`: {}",
                    function.name,
                    param.name,
                    e.message()
                ))
                .with_location(param.line, param.column),
            )
        })?;
        if scope.contains_key(&param.name) {
            return Err(CompileErrors::single(CompileError::new(format!(
                "duplicate parameter `{}` in function `{}`",
                param.name, function.name
            ))));
        }
        scope.insert(
            param.name.clone(),
            LocalBinding {
                ty: param.ty.clone(),
                mutable: true,
                used: false,
                mutated: false,
                is_global: false,
            },
        );
    }

    let mut errors = CompileErrors::new();
    for stmt in &function.body {
        if let Err(e) = analyze_stmt(
            stmt,
            &function.name,
            &function.return_type,
            functions,
            types,
            &mut scope,
            &mut function_locals,
            false,
            function.name == "main" || function.name.starts_with("__scar_test_case_"),
        ) {
            errors.push(e.with_file_opt(function.file_path.clone()));
            if errors.is_full() {
                return Err(errors);
            }
        }
    }

    for stmt in &function.body {
        mark_usage_and_mutation_stmt(stmt, &mut scope);
    }

    if let Err(binding_errors) = check_unused_bindings(
        &scope,
        &function.name,
        &function
            .params
            .iter()
            .map(|p| p.name.clone())
            .collect::<Vec<_>>(),
    ) {
        for e in binding_errors.errors {
            errors.push(e);
            if errors.is_full() {
                return Err(errors);
            }
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    locals.insert(function.name.clone(), function_locals);
    Ok(())
}

fn analyze_test_block(
    test: &TestBlock,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<(), CompileErrors> {
    let mut scope = HashMap::new();
    let mut function_locals = HashMap::new();
    let mut errors = CompileErrors::new();
    for stmt in &test.body {
        if let Err(e) = analyze_stmt(
            stmt,
            &format!("test `{}`", test.name),
            &Type::Void,
            functions,
            types,
            &mut scope,
            &mut function_locals,
            false,
            true,
        ) {
            errors.push(e);
            if errors.is_full() {
                return Err(errors);
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn validate_interface_satisfaction(
    interfaces: &HashMap<String, InterfaceDefInfo>,
    types: &HashMap<String, TypeDefInfo>,
    functions: &HashMap<String, FunctionSig>,
) -> Result<(), CompileError> {
    for (type_name, type_info) in types {
        for derive in &type_info.derives {
            let Type::Named(interface_name) = derive else {
                return Err(CompileError::new(format!(
                    "type `{type_name}` may only derive named interfaces"
                )));
            };
            let interface = interfaces.get(interface_name).ok_or_else(|| {
                CompileError::new(format!(
                    "type `{type_name}` derives unknown interface `{interface_name}`"
                ))
            })?;
            for method in &interface.methods {
                let implementation_name = format!("{type_name}.{}", method.name);
                let implementation = functions.get(&implementation_name).ok_or_else(|| {
                    CompileError::new(format!(
                        "type `{type_name}` does not satisfy interface `{interface_name}`: missing `{implementation_name}`"
                    ))
                })?;
                if implementation.params.len() != method.params.len() {
                    return Err(CompileError::new(format!(
                        "type `{type_name}` does not satisfy interface `{interface_name}`: `{implementation_name}` has the wrong parameter count"
                    )));
                }
                for (expected, actual) in method.params.iter().zip(&implementation.params) {
                    let expected_ty =
                        substitute_interface_self(&expected.ty, interface_name, type_name);
                    if !types_compatible(&expected_ty, actual, types)? {
                        return Err(CompileError::new(format!(
                            "type `{type_name}` does not satisfy interface `{interface_name}`: `{implementation_name}` expects parameter type {} but found {}",
                            describe_type(&expected_ty),
                            describe_type(actual)
                        )));
                    }
                }
                let expected_return =
                    substitute_interface_self(&method.return_type, interface_name, type_name);
                if !types_compatible(&expected_return, &implementation.return_type, types)? {
                    return Err(CompileError::new(format!(
                        "type `{type_name}` does not satisfy interface `{interface_name}`: `{implementation_name}` returns {} but interface requires {}",
                        describe_type(&implementation.return_type),
                        describe_type(&expected_return)
                    )));
                }
            }
        }
    }
    Ok(())
}

fn substitute_interface_self(ty: &Type, interface_name: &str, type_name: &str) -> Type {
    match ty {
        Type::Named(name) if name == interface_name => Type::Named(type_name.to_string()),
        Type::Mut(inner) => Type::Mut(Box::new(substitute_interface_self(
            inner,
            interface_name,
            type_name,
        ))),
        Type::Ref(inner) => Type::Ref(Box::new(substitute_interface_self(
            inner,
            interface_name,
            type_name,
        ))),
        Type::List(inner) => Type::List(Box::new(substitute_interface_self(
            inner,
            interface_name,
            type_name,
        ))),
        Type::Result(inner) => Type::Result(Box::new(substitute_interface_self(
            inner,
            interface_name,
            type_name,
        ))),
        other => other.clone(),
    }
}

fn is_ref_type(ty: &Type) -> bool {
    matches!(ty, Type::Ref(_) | Type::Mut(_))
}

fn find_path_expr(expr: &Expr) -> Option<&[String]> {
    match expr {
        Expr::Path(path) => Some(path),
        Expr::Cast { expr, .. } => find_path_expr(expr),
        Expr::Try(inner) => find_path_expr(inner),
        Expr::Unary { expr, .. } => find_path_expr(expr),
        _ => None,
    }
}

fn find_base_path(expr: &Expr) -> Option<&[String]> {
    match expr {
        Expr::Path(path) => Some(path),
        Expr::FieldAccess { base, .. } => find_base_path(base),
        Expr::Index { base, .. } => find_base_path(base),
        Expr::BuiltinCall { name, args } if name == "addr" => {
            if let Some(arg) = args.first() {
                find_base_path(arg)
            } else {
                None
            }
        }
        Expr::Cast { expr, .. } => find_base_path(expr),
        Expr::Try(inner) => find_base_path(inner),
        Expr::Unary { expr, .. } => find_base_path(expr),
        _ => None,
    }
}

fn mark_ref_value_mutation(expr: &Expr, scope: &mut HashMap<String, LocalBinding>) {
    if let Some(path) = find_path_expr(expr) {
        if path.len() == 1 {
            if let Some(binding) = scope.get_mut(&path[0]) {
                if is_ref_type(&binding.ty) {
                    binding.mutated = true;
                }
            }
        }
    }
}

fn mark_usage_and_mutation_stmt(stmt: &Stmt, scope: &mut HashMap<String, LocalBinding>) {
    match stmt {
        Stmt::VarDecl { init, .. } => {
            mark_usage_and_mutation_expr(init, scope);
        }
        Stmt::Assign { target, value, .. } => {
            mark_mutation_target(target, scope);
            mark_usage_and_mutation_expr(value, scope);
        }
        Stmt::AddAssign { target, value, .. }
        | Stmt::MulAssign { target, value, .. }
        | Stmt::SubAssign { target, value, .. }
        | Stmt::DivAssign { target, value, .. }
        | Stmt::BitAndAssign { target, value, .. }
        | Stmt::BitOrAssign { target, value, .. }
        | Stmt::BitXorAssign { target, value, .. } => {
            mark_mutation_target(target, scope);
            mark_usage_and_mutation_expr(value, scope);
        }
        Stmt::Increment { target, .. } | Stmt::Decrement { target, .. } => {
            mark_mutation_target(target, scope);
        }
        Stmt::Assert { condition, .. } => {
            mark_usage_and_mutation_expr(condition, scope);
        }
        Stmt::Return { value, .. } => {
            if let Some(expr) = value {
                mark_ref_value_mutation(expr, scope);
                mark_usage_and_mutation_expr(expr, scope);
            }
        }
        Stmt::Defer { body, .. } => {
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::Block(body) => {
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            mark_usage_and_mutation_expr(condition, scope);
            for s in then_body {
                mark_usage_and_mutation_stmt(s, scope);
            }
            for s in else_body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::Match { expr, arms, .. } => {
            mark_usage_and_mutation_expr(expr, scope);
            for arm in arms {
                for s in &arm.body {
                    mark_usage_and_mutation_stmt(s, scope);
                }
            }
        }
        Stmt::Expr { expr, .. } => {
            mark_usage_and_mutation_expr(expr, scope);
        }
        Stmt::ForRange {
            start, end, body, ..
        } => {
            mark_usage_and_mutation_expr(start, scope);
            mark_usage_and_mutation_expr(end, scope);
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::ForEach { iterable, body, .. } => {
            mark_usage_and_mutation_expr(iterable, scope);
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::ForClassic {
            init,
            condition,
            increment,
            body,
            ..
        } => {
            mark_usage_and_mutation_expr(init, scope);
            mark_usage_and_mutation_expr(condition, scope);
            mark_usage_and_mutation_expr(increment, scope);
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::While {
            condition, body, ..
        } => {
            mark_usage_and_mutation_expr(condition, scope);
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::Loop { body, .. } => {
            for s in body {
                mark_usage_and_mutation_stmt(s, scope);
            }
        }
        Stmt::Continue { .. } | Stmt::Break { .. } => {}
    }
}

fn mark_mutation_target(expr: &Expr, scope: &mut HashMap<String, LocalBinding>) {
    match expr {
        Expr::Path(path) if path.len() == 1 => {
            if let Some(binding) = scope.get_mut(&path[0]) {
                binding.mutated = true;
            }
        }
        Expr::FieldAccess { base, .. } => {
            mark_mutation_target(base, scope);
        }
        Expr::Index { base, index, .. } => {
            mark_mutation_target(base, scope);
            mark_usage_and_mutation_expr(index, scope);
        }
        Expr::BuiltinCall { name, args } if name == "deref" => {
            if let Some(arg) = args.first() {
                if let Some(path) = find_base_path(arg) {
                    if path.len() == 1 {
                        if let Some(binding) = scope.get_mut(&path[0]) {
                            binding.mutated = true;
                        }
                    }
                }
                mark_usage_and_mutation_expr(arg, scope);
            }
        }
        _ => {}
    }
}

fn mark_usage_and_mutation_expr(expr: &Expr, scope: &mut HashMap<String, LocalBinding>) {
    match expr {
        Expr::Path(path) if path.len() == 1 => {
            if let Some(binding) = scope.get_mut(&path[0]) {
                binding.used = true;
                if is_ref_type(&binding.ty) {
                    binding.mutated = true;
                }
            }
        }
        Expr::Index { base, index } => {
            mark_usage_and_mutation_expr(base, scope);
            mark_usage_and_mutation_expr(index, scope);
        }
        Expr::FieldAccess { base, .. } => {
            mark_usage_and_mutation_expr(base, scope);
        }
        Expr::StructInit { fields, .. } => {
            for field in fields {
                mark_usage_and_mutation_expr(&field.value, scope);
            }
        }
        Expr::BuiltinCall { name, args } => {
            match name.as_str() {
                "addr" => {
                    if let Some(arg) = args.first() {
                        mark_usage_and_mutation_expr(arg, scope);
                        if let Some(path) = find_base_path(arg) {
                            if path.len() == 1 {
                                if let Some(binding) = scope.get_mut(&path[0]) {
                                    binding.used = true;
                                    if binding.mutable || is_ref_type(&binding.ty) {
                                        binding.mutated = true;
                                    }
                                }
                            }
                        }
                    }
                }
                "memcpy" | "memset" | "free" | "realloc" | "append" | "set" | "remove" => {
                    if let Some(Expr::Path(path)) = args.first() {
                        if path.len() == 1 {
                            if let Some(binding) = scope.get_mut(&path[0]) {
                                binding.used = true;
                                binding.mutated = true;
                            }
                        }
                    }
                    for arg in &args[1..] {
                        mark_usage_and_mutation_expr(arg, scope);
                    }
                    return;
                }
                _ => {}
            }
            for arg in args {
                mark_usage_and_mutation_expr(arg, scope);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            mark_usage_and_mutation_expr(receiver, scope);
            for arg in args {
                mark_ref_value_mutation(arg, scope);
                mark_usage_and_mutation_expr(arg, scope);
            }
        }
        Expr::Call { callee, args } => {
            mark_usage_and_mutation_expr(callee, scope);
            for arg in args {
                mark_ref_value_mutation(arg, scope);
                mark_usage_and_mutation_expr(arg, scope);
            }
        }
        Expr::Specialize { callee, .. } => {
            mark_usage_and_mutation_expr(callee, scope);
        }
        Expr::Cast { expr, .. } => {
            mark_usage_and_mutation_expr(expr, scope);
        }
        Expr::Error { message } => {
            mark_usage_and_mutation_expr(message, scope);
        }
        Expr::Try(inner) => {
            mark_usage_and_mutation_expr(inner, scope);
        }
        Expr::Unary { expr, .. } => {
            mark_usage_and_mutation_expr(expr, scope);
        }
        Expr::Pack(values) => {
            for v in values {
                mark_usage_and_mutation_expr(v, scope);
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            mark_usage_and_mutation_expr(lhs, scope);
            mark_usage_and_mutation_expr(rhs, scope);
        }
        Expr::ListLiteral(values) => {
            for v in values {
                mark_usage_and_mutation_expr(v, scope);
            }
        }
        Expr::SizeOf(_) => {}
        Expr::BitCast { expr, .. } => {
            mark_usage_and_mutation_expr(expr, scope);
        }
        Expr::Int(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::Path(_)
        | Expr::None => {}
    }
}

fn normalize_path(path: &str) -> String {
    let mut result = String::with_capacity(path.len());
    let mut prev_is_slash = false;
    for ch in path.chars() {
        if ch == '/' {
            if prev_is_slash {
                continue;
            }
            prev_is_slash = true;
        } else {
            prev_is_slash = false;
        }
        result.push(ch);
    }
    result
}

fn strip_generic_suffix(name: &str) -> String {
    if let Some(pos) = name.find(".generic") {
        name[..pos].to_string()
    } else {
        name.to_string()
    }
}

fn demangle_function_name(name: &str) -> String {
    let result = if let Some(pos) = name.rfind("__") {
        let prefix = &name[..pos];
        let suffix = &name[pos + 2..];
        if prefix.starts_with('_') && prefix.contains("__") {
            let path = prefix.replace("___", "/");
            let path = path.replace("__", "/");
            let path = normalize_path(&path);
            let path = path.trim_start_matches('/');
            if let Ok(cwd) = std::env::current_dir() {
                let cwd_str = cwd.to_string_lossy();
                if path.starts_with(&*cwd_str) {
                    let relative = &path[cwd_str.len()..];
                    let relative = normalize_path(relative);
                    let relative = relative.trim_start_matches('/');
                    format!("./{}.{suffix}", relative)
                } else {
                    format!("/{path}.{suffix}")
                }
            } else {
                format!("/{path}.{suffix}")
            }
        } else {
            let name = name.replace("____", "/");
            let name = name.replace("__", ".");
            name.to_string()
        }
    } else {
        let name = name.replace("____", "/");
        let name = name.replace("__", ".");
        name.to_string()
    };
    strip_generic_suffix(&result)
}

fn check_unused_bindings(
    scope: &HashMap<String, LocalBinding>,
    function_name: &str,
    param_names: &[String],
) -> Result<(), CompileErrors> {
    let display_name = demangle_function_name(function_name);
    let mut errors = CompileErrors::new();
    for (name, binding) in scope {
        if param_names.iter().any(|p| p == name) {
            continue;
        }
        if binding.is_global {
            continue;
        }
        if !binding.used && !binding.mutable {
            errors.push(CompileError::new(format!(
                "binding `{name}` in function `{display_name}` is never used"
            )));
            if errors.is_full() {
                return Err(errors);
            }
        }
        if binding.mutable && !binding.mutated {
            errors.push(CompileError::new(format!(
                "variable `{name}` in function `{display_name}` is declared as `var` but never mutated"
            )));
            if errors.is_full() {
                return Err(errors);
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn analyze_stmt(
    stmt: &Stmt,
    function_name: &str,
    expected_return: &Type,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &mut HashMap<String, LocalBinding>,
    function_locals: &mut HashMap<String, Type>,
    in_loop: bool,
    allow_try_panic: bool,
) -> Result<(), CompileError> {
    match stmt {
        Stmt::VarDecl {
            line,
            column,
            mutable,
            name,
            declared_type,
            init,
        } => {
            if scope.contains_key(name) {
                return Err(CompileError::new(format!(
                    "duplicate local binding `{name}` in function `{function_name}`"
                )));
            }
            let ty = match declared_type {
                Some(expected) => {
                    validate_type(expected, types)
                        .map_err(|error| error.with_location(*line, *column))?;
                    validate_try_usage(init, expected_return, allow_try_panic)
                        .map_err(|error| error.with_location(*line, *column))?;
                    if matches!(init, Expr::BuiltinCall { name, args } if name == "zeroed" && args.is_empty())
                    {
                        expected.clone()
                    } else if let Expr::ListLiteral(values) = init {
                        infer_list_literal_type(values, Some(expected), functions, types, scope)
                            .map_err(|error| error.with_location(*line, *column))?
                    } else {
                        let actual = infer_expr_type(init, functions, types, scope, None)
                            .map_err(|error| error.with_location(*line, *column))?;
                        expect_same_type(expected, &actual, types, "variable initializer")
                            .map_err(|error| error.with_location(*line, *column))?;
                        expected.clone()
                    }
                }
                None => {
                    validate_try_usage(init, expected_return, allow_try_panic)
                        .map_err(|error| error.with_location(*line, *column))?;
                    let inferred = infer_expr_type(init, functions, types, scope, None)
                        .map_err(|error| error.with_location(*line, *column))?;
                    if matches!(inferred, Type::Error | Type::None) {
                        return Err(CompileError::new(format!(
                            "cannot infer a variable type from {} alone",
                            describe_type(&inferred)
                        ))
                        .with_location(*line, *column));
                    }
                    if *mutable {
                        propagate_mut(inferred)
                    } else {
                        inferred
                    }
                }
            };
            scope.insert(
                name.clone(),
                LocalBinding {
                    ty: ty.clone(),
                    mutable: *mutable,
                    used: false,
                    mutated: false,
                    is_global: false,
                },
            );
            function_locals.insert(name.clone(), ty);
        }
        Stmt::Assign {
            line,
            column,
            target,
            value,
        } => {
            let target_ty = infer_mutable_target(target, functions, types, scope)
                .map_err(|error| error.with_location(*line, *column))?;
            validate_try_usage(value, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let value_ty = infer_expr_type(value, functions, types, scope, None)
                .map_err(|error| error.with_location(*line, *column))?;
            expect_same_type(&target_ty, &value_ty, types, "assignment")
                .map_err(|error| error.with_location(*line, *column))?;
        }
        Stmt::AddAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_arithmetic_assignment(
                target, value, "+=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::MulAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_arithmetic_assignment(
                target, value, "*=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::SubAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_arithmetic_assignment(
                target, value, "-=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::DivAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_arithmetic_assignment(
                target, value, "/=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::BitAndAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_bitwise_assignment(
                target, value, "&=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::BitOrAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_bitwise_assignment(
                target, value, "|=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::BitXorAssign {
            line,
            column,
            target,
            value,
        } => {
            analyze_bitwise_assignment(
                target, value, "^=", *line, *column, functions, types, scope,
            )?;
        }
        Stmt::Increment {
            line,
            column,
            target,
        }
        | Stmt::Decrement {
            line,
            column,
            target,
        } => {
            let target_ty = resolve_aliases(
                &infer_mutable_target(target, functions, types, scope)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            if !is_numeric_primitive_type(&target_ty) {
                return Err(CompileError::new(format!(
                    "postfix update requires a numeric target, got {}",
                    describe_type(&target_ty)
                ))
                .with_location(*line, *column));
            }
        }
        Stmt::Assert {
            line,
            column,
            condition,
        } => {
            validate_try_usage(condition, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let condition_ty = infer_expr_type(condition, functions, types, scope, None)
                .map_err(|error| error.with_location(*line, *column))?;
            if !is_condition_type(&condition_ty, types)? {
                return Err(CompileError::new(format!(
                    "`assert` conditions must be bool or integer-compatible, got {}",
                    describe_type(&condition_ty)
                ))
                .with_location(*line, *column));
            }
        }
        Stmt::Return {
            line,
            column,
            value,
        } => match (expected_return, value) {
            (Type::Void, None) => {}
            (Type::Result(inner), None) if inner.as_ref() == &Type::Void => {}
            (Type::Void, Some(_)) => {
                return Err(CompileError::new("void functions cannot return a value")
                    .with_location(*line, *column));
            }
            (expected, Some(expr)) => {
                validate_try_usage(expr, expected_return, allow_try_panic)
                    .map_err(|error| error.with_location(*line, *column))?;
                let actual = infer_expr_type(expr, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?;
                expect_return_type(expected, &actual, types)
                    .map_err(|error| error.with_location(*line, *column))?;
            }
            (_, None) => {
                return Err(CompileError::new("non-void functions must return a value")
                    .with_location(*line, *column));
            }
        },
        Stmt::Defer {
            line: _,
            column: _,
            body,
        } => {
            let mut defer_scope = scope.clone();
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut defer_scope,
                    function_locals,
                    in_loop,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::If {
            line,
            column,
            condition,
            then_body,
            else_body,
        } => {
            let condition_ty = infer_expr_type(condition, functions, types, scope, None)
                .map_err(|error| error.with_location(*line, *column))?;
            if !is_condition_type(&condition_ty, types)? {
                return Err(CompileError::new(format!(
                    "`if` conditions must be bool or integer-compatible, got {}",
                    describe_type(&condition_ty)
                ))
                .with_location(*line, *column));
            }
            let mut then_scope = scope.clone();
            for stmt in then_body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut then_scope,
                    function_locals,
                    in_loop,
                    allow_try_panic,
                )?;
            }
            let mut else_scope = scope.clone();
            for stmt in else_body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut else_scope,
                    function_locals,
                    in_loop,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::Match {
            line,
            column,
            expr,
            arms,
        } => {
            validate_try_usage(expr, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let matched_ty = resolve_aliases(
                &infer_expr_type(expr, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            match matched_ty {
                Type::Result(ok_ty) => {
                    let mut saw_ok = false;
                    let mut saw_error = false;
                    for arm in arms {
                        match &arm.kind {
                            MatchArmKind::Ok => saw_ok = true,
                            MatchArmKind::Error => saw_error = true,
                            MatchArmKind::Variant(name) => {
                                return Err(CompileError::new(format!(
                                    "result matches do not support variant arm `{name}`"
                                ))
                                .with_location(*line, *column));
                            }
                        }
                        if arm.bindings.len() != 1 {
                            return Err(CompileError::new(
                                "result match arms require exactly one binding or `_`",
                            )
                            .with_location(*line, *column));
                        }
                        let mut nested = scope.clone();
                        if let Some(binding) = &arm.bindings[0] {
                            let binding_ty = match arm.kind {
                                MatchArmKind::Ok => (*ok_ty).clone(),
                                MatchArmKind::Error => Type::Ref(Box::new(Type::U8)),
                                MatchArmKind::Variant(_) => unreachable!(),
                            };
                            nested.insert(
                                binding.clone(),
                                LocalBinding {
                                    ty: binding_ty.clone(),
                                    mutable: true,
                                    used: false,
                                    mutated: false,
                                    is_global: false,
                                },
                            );
                            function_locals.insert(binding.clone(), binding_ty);
                        }
                        for stmt in &arm.body {
                            analyze_stmt(
                                stmt,
                                function_name,
                                expected_return,
                                functions,
                                types,
                                &mut nested,
                                function_locals,
                                in_loop,
                                allow_try_panic,
                            )?;
                        }
                    }

                    if !saw_ok || !saw_error {
                        return Err(CompileError::new(
                            "`match` on a result value requires both `ok` and `error` arms",
                        )
                        .with_location(*line, *column));
                    }
                }
                Type::Named(name) => {
                    let type_info = types.get(&name).ok_or_else(|| {
                        CompileError::new(format!("unknown type `{name}`"))
                            .with_location(*line, *column)
                    })?;
                    if type_info.kind != TypeDefKind::Union && type_info.kind != TypeDefKind::Enum {
                        return Err(CompileError::new(format!(
                            "`match` currently requires a union, enum, or `T|error` expression, got {}",
                            describe_type(&Type::Named(name))
                        ))
                        .with_location(*line, *column));
                    }
                    let mut seen_variants = HashSet::new();
                    let mut has_wildcard = false;
                    for arm in arms {
                        let MatchArmKind::Variant(variant_name) = &arm.kind else {
                            return Err(
                                CompileError::new(
                                    "union/enum matches require variant arms of the form `Variant (...) => (...)`",
                                )
                                .with_location(*line, *column),
                            );
                        };

                        let bare_variant = variant_name.rsplit('.').next().unwrap_or(variant_name);

                        if bare_variant == "_" {
                            has_wildcard = true;
                            let mut nested = scope.clone();
                            for stmt in &arm.body {
                                analyze_stmt(
                                    stmt,
                                    function_name,
                                    expected_return,
                                    functions,
                                    types,
                                    &mut nested,
                                    function_locals,
                                    in_loop,
                                    allow_try_panic,
                                )?;
                            }
                            continue;
                        }

                        let payload_types = type_info
                            .variant_map
                            .get(bare_variant)
                            .cloned()
                            .unwrap_or_default();
                        if !seen_variants.insert(bare_variant.to_string()) {
                            return Err(CompileError::new(format!(
                                "duplicate match arm for variant `{variant_name}`"
                            ))
                            .with_location(*line, *column));
                        }
                        if arm.bindings.len() != payload_types.len() {
                            return Err(CompileError::new(format!(
                                "variant `{variant_name}` expects {} bindings but found {}",
                                payload_types.len(),
                                arm.bindings.len()
                            ))
                            .with_location(*line, *column));
                        }
                        let mut nested = scope.clone();
                        for (binding, binding_ty) in arm.bindings.iter().zip(payload_types.iter()) {
                            if let Some(binding) = binding {
                                nested.insert(
                                    binding.clone(),
                                    LocalBinding {
                                        ty: binding_ty.clone(),
                                        mutable: true,
                                        used: false,
                                        mutated: false,
                                        is_global: false,
                                    },
                                );
                                function_locals.insert(binding.clone(), binding_ty.clone());
                            }
                        }
                        for stmt in &arm.body {
                            analyze_stmt(
                                stmt,
                                function_name,
                                expected_return,
                                functions,
                                types,
                                &mut nested,
                                function_locals,
                                in_loop,
                                allow_try_panic,
                            )?;
                        }
                    }

                    if !has_wildcard && seen_variants.len() != type_info.variants.len() {
                        let missing = type_info
                            .variants
                            .iter()
                            .find(|variant| !seen_variants.contains(&variant.name))
                            .map(|variant| variant.name.clone())
                            .unwrap_or_else(|| "<unknown>".to_string());
                        let display_name = demangle_function_name(name.as_str());
                        return Err(CompileError::new(format!(
                            "`match` on union `{display_name}` is missing variant `{missing}`"
                        ))
                        .with_location(*line, *column));
                    }
                }
                _ if is_integer_type(&matched_ty, types)? => {
                    for arm in arms {
                        let MatchArmKind::Variant(_) = &arm.kind else {
                            return Err(CompileError::new(
                                "integer matches require variant arms of the form `value => (...)`",
                            )
                            .with_location(*line, *column));
                        };
                        let mut nested = scope.clone();
                        for stmt in &arm.body {
                            analyze_stmt(
                                stmt,
                                function_name,
                                expected_return,
                                functions,
                                types,
                                &mut nested,
                                function_locals,
                                in_loop,
                                allow_try_panic,
                            )?;
                        }
                    }
                }
                Type::F32 | Type::F64 => {
                    for arm in arms {
                        let MatchArmKind::Variant(_) = &arm.kind else {
                            return Err(CompileError::new(
                                "float matches require variant arms of the form `value => (...)`",
                            )
                            .with_location(*line, *column));
                        };
                        let mut nested = scope.clone();
                        for stmt in &arm.body {
                            analyze_stmt(
                                stmt,
                                function_name,
                                expected_return,
                                functions,
                                types,
                                &mut nested,
                                function_locals,
                                in_loop,
                                allow_try_panic,
                            )?;
                        }
                    }
                }
                other => {
                    return Err(CompileError::new(format!(
                        "`match` currently requires a union, integer, or `T|error` expression, got {}",
                        describe_type(&other)
                    ))
                    .with_location(*line, *column));
                }
            }
        }
        Stmt::Block(body) => {
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    scope,
                    function_locals,
                    in_loop,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::Expr { line, column, expr } => {
            validate_try_usage(expr, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            infer_expr_type(expr, functions, types, scope, None)
                .map_err(|error| error.with_location(*line, *column))?;
        }
        Stmt::ForRange {
            line,
            column,
            start,
            end,
            var_name,
            body,
            ..
        } => {
            validate_try_usage(start, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            validate_try_usage(end, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let start_ty = resolve_aliases(
                &infer_expr_type(start, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            let end_ty = resolve_aliases(
                &infer_expr_type(end, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            let is_signed_int = |ty: &Type| {
                matches!(
                    ty,
                    Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize
                )
            };
            let is_unsigned_int = |ty: &Type| {
                matches!(
                    ty,
                    Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize
                )
            };
            let is_int = |ty: &Type| is_signed_int(ty) || is_unsigned_int(ty);
            if !is_int(&start_ty) || !is_int(&end_ty) {
                return Err(CompileError::new("`for` bounds must be an integer type")
                    .with_location(*line, *column));
            }
            let var_ty = start_ty.clone();
            let mut nested = scope.clone();
            nested.insert(
                var_name.clone(),
                LocalBinding {
                    ty: var_ty.clone(),
                    mutable: true,
                    used: false,
                    mutated: false,
                    is_global: false,
                },
            );
            function_locals.insert(var_name.clone(), var_ty);
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut nested,
                    function_locals,
                    true,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::ForEach {
            line,
            column,
            var_name,
            iterable,
            body,
        } => {
            validate_try_usage(iterable, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let iterable_ty = resolve_aliases(
                &infer_expr_type(iterable, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            let Type::List(element_ty) = deref_refs(&iterable_ty) else {
                return Err(CompileError::new(format!(
                    "`for ... in ...` requires a list iterable, got {}",
                    describe_type(&iterable_ty)
                ))
                .with_location(*line, *column));
            };
            let mut nested = scope.clone();
            nested.insert(
                var_name.clone(),
                LocalBinding {
                    ty: (**element_ty).clone(),
                    mutable: true,
                    used: false,
                    mutated: false,
                    is_global: false,
                },
            );
            function_locals.insert(var_name.clone(), (**element_ty).clone());
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut nested,
                    function_locals,
                    true,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::ForClassic {
            line,
            column,
            var_name,
            init,
            condition,
            increment,
            body,
            ..
        } => {
            validate_try_usage(init, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let init_ty = resolve_aliases(
                &infer_expr_type(init, functions, types, scope, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            let mut nested = scope.clone();
            nested.insert(
                var_name.clone(),
                LocalBinding {
                    ty: init_ty.clone(),
                    mutable: true,
                    used: false,
                    mutated: false,
                    is_global: false,
                },
            );
            function_locals.insert(var_name.clone(), init_ty.clone());
            validate_try_usage(condition, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let condition_ty = resolve_aliases(
                &infer_expr_type(condition, functions, types, &nested, None)
                    .map_err(|error| error.with_location(*line, *column))?,
                types,
            )?;
            if !is_condition_primitive_type(&condition_ty) {
                return Err(CompileError::new("`for` condition must be a boolean type")
                    .with_location(*line, *column));
            }
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut nested,
                    function_locals,
                    true,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::While {
            line,
            column,
            condition,
            body,
        } => {
            validate_try_usage(condition, expected_return, allow_try_panic)
                .map_err(|error| error.with_location(*line, *column))?;
            let condition_ty = infer_expr_type(condition, functions, types, scope, None)
                .map_err(|error| error.with_location(*line, *column))?;
            if !is_condition_type(&condition_ty, types)? {
                return Err(CompileError::new(format!(
                    "`for (condition)` requires a bool or integer-compatible condition, got {}",
                    describe_type(&condition_ty)
                ))
                .with_location(*line, *column));
            }
            let mut nested = scope.clone();
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut nested,
                    function_locals,
                    true,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::Loop { body, .. } => {
            let mut nested = scope.clone();
            for stmt in body {
                analyze_stmt(
                    stmt,
                    function_name,
                    expected_return,
                    functions,
                    types,
                    &mut nested,
                    function_locals,
                    true,
                    allow_try_panic,
                )?;
            }
        }
        Stmt::Continue { line, column } => {
            if !in_loop {
                return Err(
                    CompileError::new("`continue` may only appear inside a loop")
                        .with_location(*line, *column),
                );
            }
        }
        Stmt::Break { line, column } => {
            if !in_loop {
                return Err(CompileError::new("`break` may only appear inside a loop")
                    .with_location(*line, *column));
            }
        }
    }
    Ok(())
}

fn infer_expr_type(
    expr: &Expr,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
    expected: Option<&Type>,
) -> Result<Type, CompileError> {
    match expr {
        Expr::Int(_) => Ok(Type::I32),
        Expr::Char(_) => Ok(Type::U8),
        Expr::Bool(_) => Ok(Type::Bool),
        Expr::Float(_) => Ok(Type::F32),
        Expr::String(_) => Ok(Type::Ref(Box::new(Type::U8))),
        Expr::None => Ok(Type::None),
        Expr::ListLiteral(values) => {
            infer_list_literal_type(values, expected, functions, types, scope)
        }
        Expr::Index { base, index } => {
            let base_ty = infer_expr_type(base, functions, types, scope, None)?;
            let index_ty = infer_expr_type(index, functions, types, scope, None)?;
            if !is_integer_type(&index_ty, types)? {
                return Err(CompileError::new(format!(
                    "index must be an integer type, got {}",
                    describe_type(&index_ty)
                )));
            }
            infer_index_type(&base_ty, types)
        }
        Expr::StructInit { name, fields, .. } => {
            let type_info = types
                .get(name)
                .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;
            if type_info.kind != TypeDefKind::Struct {
                return Err(CompileError::new(format!(
                    "union `{name}` cannot be initialized like a struct"
                )));
            }
            if type_info.alias.is_some() {
                return Err(CompileError::new(format!(
                    "type `{name}` is an alias and cannot be initialized like a struct"
                )));
            }
            let mut seen = HashSet::new();
            for field in fields {
                let expected = type_info.field_map.get(&field.name).ok_or_else(|| {
                    CompileError::new(format!("type `{name}` has no field `{}`", field.name))
                })?;
                if !seen.insert(field.name.clone()) {
                    return Err(CompileError::new(format!(
                        "duplicate field initializer `{}` for type `{name}`",
                        field.name
                    )));
                }
                let actual = infer_expr_type(&field.value, functions, types, scope, None)?;
                expect_same_type(expected, &actual, types, &format!("field `{}`", field.name))?;
            }
            if seen.len() != type_info.fields.len() {
                let missing = type_info
                    .fields
                    .iter()
                    .find(|field| !seen.contains(&field.name))
                    .map(|field| field.name.clone())
                    .unwrap_or_else(|| "<unknown>".to_string());
                return Err(CompileError::new(format!(
                    "missing field `{missing}` in initializer for type `{name}`"
                )));
            }
            Ok(Type::Named(name.clone()))
        }
        Expr::FieldAccess { base, field } => {
            let base_ty = infer_expr_type(base, functions, types, scope, None)?;
            infer_field_type(&base_ty, field, types)
        }
        Expr::BuiltinCall { name, args } => analyze_builtin(name, args, functions, types, scope),
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let receiver_ty = match method.as_str() {
                "capacity" => infer_expr_type(receiver, functions, types, scope, None)?,
                _ => infer_lvalue_type(receiver, functions, types, scope)?,
            };
            analyze_list_method_with_receiver(method, &receiver_ty, args, functions, types, scope)
        }
        Expr::Path(path) => match path.as_slice() {
            [name] => scope
                .get(name)
                .map(|binding| binding.ty.clone())
                .or_else(|| {
                    functions.get(name).map(|sig| {
                        Type::FnPtr(sig.params.clone(), Box::new(sig.return_type.clone()))
                    })
                })
                .or_else(|| types.get(name).map(|type_info| Type::Named(name.clone())))
                .ok_or_else(|| {
                    eprintln!("[DEBUG sema unknown name] name={:?}", name);
                    eprintln!(
                        "[DEBUG sema unknown name] scope keys: {:?}",
                        scope.keys().collect::<Vec<_>>()
                    );
                    eprintln!(
                        "[DEBUG sema unknown name] function keys: {:?}",
                        functions.keys().collect::<Vec<_>>()
                    );
                    eprintln!(
                        "[DEBUG sema unknown name] type keys: {:?}",
                        types.keys().collect::<Vec<_>>()
                    );
                    CompileError::new(format!("unknown name `{name}`"))
                }),
            [type_name, variant_name] => {
                if let Some(type_info) = types.get(type_name) {
                    if type_info.kind == TypeDefKind::Enum
                        && type_info.variant_map.contains_key(variant_name)
                    {
                        return Ok(Type::Named(type_name.clone()));
                    }
                }
                Err(CompileError::new(format!(
                    "qualified path `{}` is not a valid expression",
                    path.join(".")
                )))
            }
            _ => Err(CompileError::new(format!(
                "qualified path `{}` is not a valid expression",
                path.join(".")
            ))),
        },
        Expr::Call { callee, args } => analyze_call(callee, args, functions, types, scope),
        Expr::Specialize { .. } => Err(CompileError::new(
            "generic specialization must be resolved before semantic analysis",
        )),
        Expr::Cast { expr, ty } => {
            let source_ty = infer_expr_type(expr, functions, types, scope, Some(ty))?;
            validate_type(ty, types)?;
            let resolved_source = resolve_aliases(&source_ty, types)?;
            let resolved_target = resolve_aliases(ty, types)?;
            if resolved_source == resolved_target {
                Ok(ty.clone())
            } else if can_cast_between_primitive_refs(&resolved_source, &resolved_target) {
                Ok(ty.clone())
            } else if is_numeric_type(&source_ty, types)? && is_numeric_type(ty, types)? {
                if is_integer_type(&source_ty, types)? && is_integer_type(ty, types)? {
                    if let Some(value) = constant_integer_value(expr) {
                        validate_integer_literal_cast_range(value, ty)?;
                    }
                }
                Ok(ty.clone())
            } else {
                Err(CompileError::new(format!(
                    "cannot cast {} to {}",
                    describe_type(&source_ty),
                    describe_type(ty)
                )))
            }
        }
        Expr::SizeOf(_) => Ok(Type::Usize),
        Expr::BitCast { ty, .. } => Ok(ty.clone()),
        Expr::Error { message } => {
            let message_ty = resolve_aliases(
                &infer_expr_type(message, functions, types, scope, None)?,
                types,
            )?;
            if !is_string_compatible(&message_ty) {
                return Err(CompileError::new(format!(
                    "`error(...)` expects a string-compatible message, got {}",
                    describe_type(&message_ty)
                )));
            }
            Ok(Type::Error)
        }
        Expr::Try(inner) => {
            let inner_ty = resolve_aliases(
                &infer_expr_type(inner, functions, types, scope, None)?,
                types,
            )?;
            let Type::Result(ok_ty) = inner_ty else {
                return Err(CompileError::new(format!(
                    "`?` requires a `T|error` expression, got {}",
                    describe_type(&inner_ty)
                )));
            };
            Ok((*ok_ty).clone())
        }
        Expr::Unary { op, expr } => {
            let inner_ty = resolve_aliases(
                &infer_expr_type(expr, functions, types, scope, None)?,
                types,
            )?;
            match op {
                UnaryOp::Neg if is_signed_numeric_type(&inner_ty) => Ok(inner_ty),
                UnaryOp::Neg => Err(CompileError::new(
                    "unary `-` currently requires a signed numeric operand",
                )),
                UnaryOp::LogicalNot if is_condition_primitive_type(&inner_ty) => Ok(Type::Bool),
                UnaryOp::LogicalNot => Err(CompileError::new(
                    "unary `!` currently requires a bool or integer operand",
                )),
                UnaryOp::BitNot if is_integer_primitive_type(&inner_ty) => Ok(inner_ty),
                UnaryOp::BitNot => Err(CompileError::new(
                    "unary `~` currently requires an integer operand",
                )),
                UnaryOp::PostfixInc | UnaryOp::PostfixDec
                    if is_numeric_primitive_type(&inner_ty) =>
                {
                    Ok(inner_ty)
                }
                UnaryOp::PostfixInc | UnaryOp::PostfixDec => Err(CompileError::new(
                    "postfix increment/decrement requires a numeric operand",
                )),
                UnaryOp::PostfixInc | UnaryOp::PostfixDec => Err(CompileError::new(
                    "postfix increment/decrement requires a numeric operand",
                )),
            }
        }
        Expr::Pack(_) => Err(CompileError::new(
            "packed `{...}` expressions are only valid as @print arguments",
        )),
        Expr::Binary { lhs, op, rhs } => {
            let lhs_ty =
                resolve_aliases(&infer_expr_type(lhs, functions, types, scope, None)?, types)?;
            let rhs_ty =
                resolve_aliases(&infer_expr_type(rhs, functions, types, scope, None)?, types)?;
            match op {
                BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Divide | BinaryOp::Multiply
                    if common_numeric_type(&lhs_ty, &rhs_ty).is_some() =>
                {
                    Ok(common_numeric_type(&lhs_ty, &rhs_ty).unwrap())
                }
                BinaryOp::Modulo if common_integer_type(&lhs_ty, &rhs_ty).is_some() => {
                    Ok(common_integer_type(&lhs_ty, &rhs_ty).unwrap())
                }
                BinaryOp::Add => Err(CompileError::new(
                    "`+` currently requires compatible numeric operands",
                )),
                BinaryOp::Subtract => Err(CompileError::new(
                    "`-` currently requires compatible numeric operands",
                )),
                BinaryOp::Divide => Err(CompileError::new(
                    "`/` currently requires compatible numeric operands",
                )),
                BinaryOp::Multiply => Err(CompileError::new(
                    "`*` currently requires compatible numeric operands",
                )),
                BinaryOp::Modulo => Err(CompileError::new(
                    "`%` currently requires compatible integer operands",
                )),
                BinaryOp::LogicalAnd | BinaryOp::LogicalOr
                    if is_condition_primitive_type(&lhs_ty)
                        && is_condition_primitive_type(&rhs_ty) =>
                {
                    Ok(Type::Bool)
                }
                BinaryOp::LogicalAnd | BinaryOp::LogicalOr => Err(CompileError::new(
                    "logical operators currently require bool or integer operands",
                )),
                BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor
                    if common_integer_type(&lhs_ty, &rhs_ty).is_some() =>
                {
                    Ok(common_integer_type(&lhs_ty, &rhs_ty).unwrap())
                }
                BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => Err(CompileError::new(
                    "bitwise operators currently require compatible integer operands",
                )),
                BinaryOp::ShiftLeft | BinaryOp::ShiftRight
                    if is_integer_type(&lhs_ty, types)? && is_integer_type(&rhs_ty, types)? =>
                {
                    Ok(lhs_ty)
                }
                BinaryOp::ShiftLeft | BinaryOp::ShiftRight => Err(CompileError::new(
                    "shift operators currently require integer operands",
                )),
                BinaryOp::LessThan
                | BinaryOp::LessEqual
                | BinaryOp::GreaterThan
                | BinaryOp::GreaterEqual
                | BinaryOp::Equal
                | BinaryOp::NotEqual
                    if common_numeric_type(&lhs_ty, &rhs_ty).is_some() =>
                {
                    Ok(Type::Bool)
                }
                BinaryOp::Equal | BinaryOp::NotEqual
                    if lhs_ty == Type::Bool && rhs_ty == Type::Bool =>
                {
                    Ok(Type::Bool)
                }
                BinaryOp::Equal | BinaryOp::NotEqual if can_compare_with_none(&lhs_ty, &rhs_ty) => {
                    Ok(Type::Bool)
                }
                BinaryOp::Equal | BinaryOp::NotEqual
                    if is_string_compatible(&lhs_ty) && is_string_compatible(&rhs_ty) =>
                {
                    Err(CompileError::new(
                        "cannot compare strings with `==` or `!=`, compares pointers, not content; use `eql` from std/string instead",
                    ))
                }
                BinaryOp::Equal | BinaryOp::NotEqual
                    if is_nullable_pointer_type(&lhs_ty) && is_nullable_pointer_type(&rhs_ty) =>
                {
                    Ok(Type::Bool)
                }
                BinaryOp::Equal | BinaryOp::NotEqual if same_enum_type(&lhs_ty, &rhs_ty, types) => {
                    Ok(Type::Bool)
                }
                BinaryOp::LessThan
                | BinaryOp::LessEqual
                | BinaryOp::GreaterThan
                | BinaryOp::GreaterEqual
                | BinaryOp::Equal
                | BinaryOp::NotEqual => Err(CompileError::new(
                    "comparison operators currently require compatible numeric, bool, or pointer/null operands",
                )),
            }
        }
    }
}

fn analyze_call(
    callee: &Expr,
    args: &[Expr],
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    if let Expr::Path(path) = callee {
        if path.len() == 1 {
            let name = &path[0];
            if let Some(binding) = scope.get(name) {
                if let Type::FnPtr(param_types, ret_type) = &binding.ty {
                    if param_types.len() != args.len() {
                        return Err(CompileError::new(format!(
                            "function pointer `{name}` expects {} arguments but received {}",
                            param_types.len(),
                            args.len()
                        )));
                    }
                    for (arg, expected) in args.iter().zip(param_types.iter()) {
                        let actual = infer_expr_type(arg, functions, types, scope, None)?;
                        expect_same_type(expected, &actual, types, "function pointer argument")?;
                    }
                    return Ok(*ret_type.clone());
                }
            }
        }
    }

    if let Some(path) = callee.callee_path() {
        let function_name = path.join(".");
        if let Some(signature) = functions.get(&function_name) {
            if signature.params.len() != args.len() {
                return Err(CompileError::new(format!(
                    "function `{function_name}` expects {} arguments but received {}",
                    signature.params.len(),
                    args.len()
                )));
            }
            for (arg, expected) in args.iter().zip(&signature.params) {
                let actual = infer_expr_type(arg, functions, types, scope, None)?;
                expect_same_type(expected, &actual, types, "function argument")?;
            }
            return Ok(signature.return_type.clone());
        }

        if path.len() == 1 {
            if let Some(type_info) = types.get(&function_name) {
                if type_info.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "union `{function_name}` cannot be constructed positionally"
                    )));
                }
                if type_info.alias.is_some() {
                    return Err(CompileError::new(format!(
                        "type `{function_name}` is an alias and cannot be initialized like a struct"
                    )));
                }
                if type_info.fields.len() != args.len() {
                    return Err(CompileError::new(format!(
                        "type `{function_name}` expects {} constructor arguments but received {}",
                        type_info.fields.len(),
                        args.len()
                    )));
                }
                for (arg, field) in args.iter().zip(&type_info.fields) {
                    let actual = infer_expr_type(arg, functions, types, scope, None)?;
                    expect_same_type(
                        &field.ty,
                        &actual,
                        types,
                        &format!("field `{}`", field.name),
                    )?;
                }
                return Ok(Type::Named(function_name));
            }
        }

        if path.len() == 2 {
            let union_name = &path[0];
            let variant_name = &path[1];
            if let Some(type_info) = types.get(union_name) {
                if type_info.kind == TypeDefKind::Union {
                    let payload_types =
                        type_info.variant_map.get(variant_name).ok_or_else(|| {
                            CompileError::new(format!(
                                "union `{union_name}` has no variant `{variant_name}`"
                            ))
                        })?;
                    if payload_types.len() != args.len() {
                        return Err(CompileError::new(format!(
                            "variant `{variant_name}` expects {} arguments but received {}",
                            payload_types.len(),
                            args.len()
                        )));
                    }
                    for (arg, expected) in args.iter().zip(payload_types.iter()) {
                        let actual = infer_expr_type(arg, functions, types, scope, None)?;
                        expect_same_type(expected, &actual, types, "union constructor argument")?;
                    }
                    return Ok(Type::Named(union_name.clone()));
                }
            }
        }

        return Err(CompileError::new(format!(
            "unknown function `{function_name}`"
        )));
    }

    Err(CompileError::new(
        "only direct function calls and @builtin calls are currently supported",
    ))
}

fn analyze_builtin(
    name: &str,
    args: &[Expr],
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    match name {
        "append" | "capacity" | "reserve" | "set" | "insert" | "remove" | "clear" | "len" => {
            analyze_builtin_list_method(name, args, functions, types, scope)
        }
        "args" => {
            if !args.is_empty() {
                return Err(CompileError::new("@args expects no arguments"));
            }
            Ok(Type::List(Box::new(Type::Ref(Box::new(Type::U8)))))
        }
        "puts" => {
            if args.len() != 1 {
                return Err(CompileError::new("@puts expects exactly one argument"));
            }
            let arg_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_string_compatible(&arg_ty) {
                return Err(CompileError::new(format!(
                    "@puts expects a string-compatible value, got {}",
                    describe_type(&arg_ty)
                )));
            }
            Ok(Type::Void)
        }
        "flush" => {
            if !args.is_empty() {
                return Err(CompileError::new("@flush expects no arguments"));
            }
            Ok(Type::Void)
        }
        "print" => {
            if args.is_empty() {
                return Err(CompileError::new(
                    "@print expects at least a format string argument",
                ));
            }
            let Expr::String(format) = &args[0] else {
                return Err(CompileError::new(
                    "@print requires a string literal as its first argument",
                ));
            };
            let flattened = flatten_print_args(&args[1..]);
            let markers = parse_format_markers(format)?;
            if markers.len() != flattened.len() {
                return Err(CompileError::new(format!(
                    "@print format expects {} values but received {}",
                    markers.len(),
                    flattened.len()
                )));
            }
            for (marker, arg) in markers.iter().zip(flattened.iter()) {
                let arg_ty = infer_expr_type(arg, functions, types, scope, None)?;
                if !format_type_matches(*marker, &resolve_aliases(&arg_ty, types)?) {
                    return Err(CompileError::new(format!(
                        "format marker `{{{}}}` does not accept value of type {}",
                        print_marker_name(*marker),
                        describe_type(&arg_ty)
                    )));
                }
            }
            Ok(Type::Void)
        }
        "neg" => {
            if args.len() != 1 {
                return Err(CompileError::new("@neg expects exactly one argument"));
            }
            let arg_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_numeric_primitive_type(&arg_ty) {
                return Err(CompileError::new(format!(
                    "@neg expects a numeric operand, got {}",
                    describe_type(&arg_ty)
                )));
            }
            Ok(arg_ty)
        }
        "shl" | "shr" => {
            if args.len() != 2 {
                return Err(CompileError::new(format!(
                    "@{name} expects exactly two arguments"
                )));
            }
            let lhs_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            let rhs_ty = resolve_aliases(
                &infer_expr_type(&args[1], functions, types, scope, None)?,
                types,
            )?;
            if !is_integer_primitive_type(&lhs_ty) {
                return Err(CompileError::new(format!(
                    "@{name} expects an integer left operand, got {}",
                    describe_type(&lhs_ty)
                )));
            }
            if !is_integer_primitive_type(&rhs_ty) {
                return Err(CompileError::new(format!(
                    "@{name} expects an integer right operand, got {}",
                    describe_type(&rhs_ty)
                )));
            }
            Ok(lhs_ty)
        }
        "memcpy" => {
            if args.len() != 3 {
                return Err(CompileError::new("@memcpy expects exactly three arguments"));
            }
            let dest_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&dest_ty) {
                return Err(CompileError::new(format!(
                    "@memcpy expects a pointer-like destination, got {}",
                    describe_type(&dest_ty)
                )));
            }
            let src_ty = resolve_aliases(
                &infer_expr_type(&args[1], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&src_ty) {
                return Err(CompileError::new(format!(
                    "@memcpy expects a pointer-like source, got {}",
                    describe_type(&src_ty)
                )));
            }
            let len_ty = infer_expr_type(&args[2], functions, types, scope, None)?;
            if !is_integer_type(&len_ty, types)? {
                return Err(CompileError::new(format!(
                    "@memcpy expects an integer byte count, got {}",
                    describe_type(&len_ty)
                )));
            }
            Ok(Type::Void)
        }
        "zeroed" => {
            if !args.is_empty() {
                return Err(CompileError::new("@zeroed takes no arguments"));
            }
            Ok(Type::Void)
        }
        "memset" => {
            if args.len() != 3 {
                return Err(CompileError::new("@memset expects exactly three arguments"));
            }
            let dest_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&dest_ty) {
                return Err(CompileError::new(format!(
                    "@memset expects a pointer-like destination, got {}",
                    describe_type(&dest_ty)
                )));
            }
            let val_ty = infer_expr_type(&args[1], functions, types, scope, None)?;
            if !is_integer_type(&val_ty, types)? {
                return Err(CompileError::new(format!(
                    "@memset expects an integer fill value, got {}",
                    describe_type(&val_ty)
                )));
            }
            let len_ty = infer_expr_type(&args[2], functions, types, scope, None)?;
            if !is_integer_type(&len_ty, types)? {
                return Err(CompileError::new(format!(
                    "@memset expects an integer byte count, got {}",
                    describe_type(&len_ty)
                )));
            }
            Ok(Type::Void)
        }
        "addr" => {
            if args.len() != 1 {
                return Err(CompileError::new("@addr expects exactly one argument"));
            }
            let inner = infer_lvalue_type(&args[0], functions, types, scope)
                .or_else(|_| infer_expr_type(&args[0], functions, types, scope, None))?;
            let is_mut = matches!(&args[0], Expr::Path(path) if path.len() == 1 && scope.get(&path[0]).is_some_and(|b| b.mutable));
            if is_mut {
                Ok(Type::Mut(Box::new(Type::Ref(Box::new(inner)))))
            } else {
                Ok(Type::Ref(Box::new(inner)))
            }
        }
        "as_mut" => {
            if args.len() != 1 {
                return Err(CompileError::new("@as_mut expects exactly one argument"));
            }
            let inner = infer_expr_type(&args[0], functions, types, scope, None)?;
            Ok(as_mut_type(inner))
        }
        "call" => {
            if args.is_empty() {
                return Err(CompileError::new(
                    "@call expects a function pointer as its first argument",
                ));
            }
            let fn_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            let Type::FnPtr(param_types, ret_type) = fn_ty else {
                return Err(CompileError::new(format!(
                    "@call expects a function pointer as its first argument, got {}",
                    describe_type(&fn_ty)
                )));
            };
            let call_args = &args[1..];
            if param_types.len() != call_args.len() {
                return Err(CompileError::new(format!(
                    "@call: function pointer expects {} arguments but received {}",
                    param_types.len(),
                    call_args.len()
                )));
            }
            for (arg, expected) in call_args.iter().zip(param_types.iter()) {
                let actual = infer_expr_type(arg, functions, types, scope, None)?;
                expect_same_type(expected, &actual, types, "@call argument")?;
            }
            Ok(*ret_type)
        }
        "add" => {
            if args.len() != 2 {
                return Err(CompileError::new("@add expects exactly two arguments"));
            }
            let base_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&base_ty) {
                return Err(CompileError::new(format!(
                    "@add expects a pointer-like first argument, got {}",
                    describe_type(&base_ty)
                )));
            }
            let offset_ty = infer_expr_type(&args[1], functions, types, scope, None)?;
            if !is_integer_type(&offset_ty, types)? {
                return Err(CompileError::new(format!(
                    "@add expects an integer offset, got {}",
                    describe_type(&offset_ty)
                )));
            }
            Ok(pointer_arithmetic_type(&base_ty))
        }
        "alloc" => {
            if args.len() != 1 {
                return Err(CompileError::new("@alloc expects exactly one argument"));
            }
            let size_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            if !is_integer_type(&size_ty, types)? {
                return Err(CompileError::new(format!(
                    "@alloc expects an integer size, got {}",
                    describe_type(&size_ty)
                )));
            }
            Ok(Type::Mut(Box::new(Type::Ref(Box::new(Type::U8)))))
        }
        "realloc" => {
            if args.len() != 2 {
                return Err(CompileError::new("@realloc expects exactly two arguments"));
            }
            let ptr_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&ptr_ty) {
                return Err(CompileError::new(format!(
                    "@realloc expects a pointer-like first argument, got {}",
                    describe_type(&ptr_ty)
                )));
            }
            let size_ty = infer_expr_type(&args[1], functions, types, scope, None)?;
            if !is_integer_type(&size_ty, types)? {
                return Err(CompileError::new(format!(
                    "@realloc expects an integer size, got {}",
                    describe_type(&size_ty)
                )));
            }
            Ok(Type::Mut(Box::new(Type::Ref(Box::new(Type::U8)))))
        }
        "free" => {
            if args.len() != 1 {
                return Err(CompileError::new("@free expects exactly one argument"));
            }
            let ptr_ty = resolve_aliases(
                &infer_expr_type(&args[0], functions, types, scope, None)?,
                types,
            )?;
            if !is_memory_pointer_type(&ptr_ty) {
                return Err(CompileError::new(format!(
                    "@free expects a pointer-like argument, got {}",
                    describe_type(&ptr_ty)
                )));
            }
            Ok(Type::Void)
        }
        "deref" => {
            if args.len() != 1 {
                return Err(CompileError::new("@deref expects exactly one argument"));
            }
            let arg_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            match resolve_aliases(&arg_ty, types)? {
                Type::Ref(inner) => Ok(*inner),
                Type::Mut(inner) => match *inner {
                    Type::Ref(inner) => Ok(*inner),
                    other => Err(CompileError::new(format!(
                        "@deref requires a ref(...) argument, got {}",
                        describe_type(&other)
                    ))),
                },
                other => Err(CompileError::new(format!(
                    "@deref requires a ref(...) argument, got {}",
                    describe_type(&other)
                ))),
            }
        }
        _ => Err(CompileError::new(format!(
            "unsupported builtin intrinsic `@{name}` (known builtins: puts, print, flush, args, neg, shl, shr, memcpy, memset, zeroed, addr, deref, call, as_mut, add, alloc, realloc, free, len, append, capacity, reserve, set, insert, remove, clear)"
        ))),
    }
}

fn analyze_bitwise_assignment(
    target: &Expr,
    value: &Expr,
    operator: &str,
    line: usize,
    column: usize,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<(), CompileError> {
    let target_ty = resolve_aliases(
        &infer_mutable_target(target, functions, types, scope)
            .map_err(|error| error.with_location(line, column))?,
        types,
    )?;
    let value_ty = resolve_aliases(
        &infer_expr_type(value, functions, types, scope, None)
            .map_err(|error| error.with_location(line, column))?,
        types,
    )?;
    if common_integer_type(&target_ty, &value_ty) == Some(target_ty.clone()) {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "`{operator}` currently requires compatible integer operands"
        ))
        .with_location(line, column))
    }
}

fn analyze_arithmetic_assignment(
    target: &Expr,
    value: &Expr,
    operator: &str,
    line: usize,
    column: usize,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<(), CompileError> {
    let target_ty = resolve_aliases(
        &infer_mutable_target(target, functions, types, scope)
            .map_err(|error| error.with_location(line, column))?,
        types,
    )?;
    let value_ty = resolve_aliases(
        &infer_expr_type(value, functions, types, scope, None)
            .map_err(|error| error.with_location(line, column))?,
        types,
    )?;
    if common_numeric_type(&target_ty, &value_ty) == Some(target_ty.clone())
        || common_numeric_type(strip_mut(&target_ty), &value_ty)
            == Some(strip_mut(&target_ty).clone())
    {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "`{operator}` currently requires compatible numeric operands"
        ))
        .with_location(line, column))
    }
}

fn infer_lvalue_type(
    expr: &Expr,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    match expr {
        Expr::Path(path) if path.len() == 1 => scope
            .get(&path[0])
            .map(|binding| binding.ty.clone())
            .ok_or_else(|| CompileError::new(format!("unknown name `{}`", path[0]))),
        Expr::FieldAccess { base, field } => {
            let base_ty = infer_lvalue_type(base, functions, types, scope)?;
            infer_field_type(&base_ty, field, types)
        }
        Expr::Index { base, index } => {
            let base_ty = infer_lvalue_type(base, functions, types, scope)?;
            let index_ty = infer_expr_type(index, functions, types, scope, None)?;
            if !is_integer_type(&index_ty, types)? {
                return Err(CompileError::new(format!(
                    "index must be an integer type, got {}",
                    describe_type(&index_ty)
                )));
            }
            infer_index_type(&base_ty, types)
        }
        Expr::BuiltinCall { name, args } if name == "deref" => {
            analyze_builtin("deref", args, functions, types, scope)
        }
        _ => Err(CompileError::new(
            "only names, field references, index references, and @deref(...) may appear as lvalues",
        )),
    }
}

fn infer_mutable_target(
    expr: &Expr,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    match expr {
        Expr::Path(path) if path.len() == 1 => {
            let name = &path[0];
            let binding = scope
                .get(name)
                .ok_or_else(|| CompileError::new(format!("unknown name `{name}`")))?;
            if !binding.mutable {
                return Err(CompileError::new(format!(
                    "cannot assign to immutable binding `{name}`"
                )));
            }
            Ok(binding.ty.clone())
        }
        Expr::FieldAccess { base, field } => {
            let base_ty = infer_mutable_target(base, functions, types, scope)?;
            let resolved = resolve_aliases(&base_ty, types)?;
            if matches!(resolved, Type::Mut(_)) {
                infer_field_type(&resolved, field, types)
            } else {
                infer_field_type(&base_ty, field, types)
            }
        }
        Expr::Index { base, index } => {
            let base_ty = infer_mutable_target(base, functions, types, scope)?;
            let index_ty = infer_expr_type(index, functions, types, scope, None)?;
            if !is_integer_type(&index_ty, types)? {
                return Err(CompileError::new(format!(
                    "index must be an integer type, got {}",
                    describe_type(&index_ty)
                )));
            }
            infer_index_type(&base_ty, types)
        }
        Expr::BuiltinCall { name, args } if name == "deref" => {
            analyze_builtin("deref", args, functions, types, scope)
        }
        _ => Err(CompileError::new(
            "only names, field references, index references, and @deref(...) may appear on the left-hand side of an assignment",
        )),
    }
}

fn infer_field_type(
    base_ty: &Type,
    field: &str,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<Type, CompileError> {
    let resolved = resolve_aliases(base_ty, types)?;
    match deref_refs(&resolved) {
        Type::Named(name) => {
            let type_info = types
                .get(name.as_str())
                .ok_or_else(|| CompileError::new(format!("unknown type `{name}`")))?;

            if let Some(field_ty) = type_info.field_map.get(field) {
                return Ok(field_ty.clone());
            }

            if let Some(payloads) = type_info.variant_map.get(field) {
                if payloads.is_empty() {
                    return Ok(Type::Named(name.clone()));
                }
                return Ok(Type::Applied(name.clone(), payloads.clone()));
            }

            Err(CompileError::new(format!(
                "type `{name}` has no field `{field}`"
            )))
        }
        other => Err(CompileError::new(format!(
            "field access requires a named type, got {}",
            describe_type(other)
        ))),
    }
}

fn infer_index_type(
    base_ty: &Type,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<Type, CompileError> {
    let resolved = resolve_aliases(base_ty, types)?;
    match deref_refs(&resolved) {
        Type::List(inner) => Ok((**inner).clone()),
        Type::FixedArray(_, inner) => Ok((**inner).clone()),
        other => Err(CompileError::new(format!(
            "indexing requires a list or fixed array type, got {}",
            describe_type(other)
        ))),
    }
}

fn analyze_builtin_list_method(
    name: &str,
    args: &[Expr],
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    if args.is_empty() {
        return Err(CompileError::new(format!(
            "@{name} expects a list receiver as its first argument",
        )));
    }
    let receiver_ty = match name {
        "capacity" => infer_expr_type(&args[0], functions, types, scope, None)?,
        _ => infer_lvalue_type(&args[0], functions, types, scope)?,
    };
    analyze_list_method_with_receiver(name, &receiver_ty, &args[1..], functions, types, scope)
}

fn analyze_list_method_with_receiver(
    method: &str,
    receiver_ty: &Type,
    args: &[Expr],
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    let resolved_receiver = resolve_aliases(receiver_ty, types)?;
    let element_ty = match deref_refs(&resolved_receiver) {
        Type::List(inner) => inner,
        other => {
            return Err(CompileError::new(format!(
                "`@{method}` requires a list receiver, got {}",
                describe_type(other)
            )));
        }
    };

    match method {
        "append" => {
            if args.len() != 1 {
                return Err(CompileError::new("@append expects exactly one argument"));
            }
            let value_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            expect_same_type(element_ty, &value_ty, types, "@append")?;
            Ok(Type::Void)
        }
        "capacity" => {
            if !args.is_empty() {
                return Err(CompileError::new("@capacity expects no arguments"));
            }
            Ok(Type::I32)
        }
        "len" => {
            if !args.is_empty() {
                return Err(CompileError::new("@len expects no arguments"));
            }
            Ok(Type::Usize)
        }
        "reserve" => {
            if args.len() != 1 {
                return Err(CompileError::new("@reserve expects exactly one argument"));
            }
            let capacity_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            expect_same_type(&Type::I32, &capacity_ty, types, "@reserve")?;
            Ok(Type::Void)
        }
        "set" => {
            if args.len() != 2 {
                return Err(CompileError::new("@set expects exactly two arguments"));
            }
            let index_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            expect_same_type(&Type::I32, &index_ty, types, "@set index")?;
            let value_ty = infer_expr_type(&args[1], functions, types, scope, None)?;
            expect_same_type(element_ty, &value_ty, types, "@set value")?;
            Ok(Type::Void)
        }
        "insert" => {
            if args.len() != 2 {
                return Err(CompileError::new("@insert expects exactly two arguments"));
            }
            let index_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            expect_same_type(&Type::I32, &index_ty, types, "@insert index")?;
            let value_ty = infer_expr_type(&args[1], functions, types, scope, None)?;
            expect_same_type(element_ty, &value_ty, types, "@insert value")?;
            Ok(Type::Void)
        }
        "remove" => {
            if args.len() != 1 {
                return Err(CompileError::new("@remove expects exactly one argument"));
            }
            let index_ty = infer_expr_type(&args[0], functions, types, scope, None)?;
            expect_same_type(&Type::I32, &index_ty, types, "@remove index")?;
            Ok((**element_ty).clone())
        }
        "clear" => {
            if !args.is_empty() {
                return Err(CompileError::new("@clear expects no arguments"));
            }
            Ok(Type::Void)
        }
        _ => Err(CompileError::new(format!(
            "unsupported list accessor `@{method}`"
        ))),
    }
}

fn infer_list_literal_type(
    values: &[Expr],
    expected: Option<&Type>,
    functions: &HashMap<String, FunctionSig>,
    types: &HashMap<String, TypeDefInfo>,
    scope: &HashMap<String, LocalBinding>,
) -> Result<Type, CompileError> {
    if values.is_empty() {
        return match expected {
            Some(Type::List(element_ty)) => Ok(Type::List(element_ty.clone())),
            Some(Type::FixedArray(n, element_ty)) => Ok(Type::FixedArray(*n, element_ty.clone())),
            Some(other) => Err(CompileError::new(format!(
                "empty list literals require a list type, got {}",
                describe_type(other)
            ))),
            None => Err(CompileError::new(
                "cannot infer the element type of an empty list literal",
            )),
        };
    }

    let element_ty = match expected {
        Some(Type::List(element_ty)) => {
            for value in values {
                let actual = infer_expr_type(value, functions, types, scope, Some(element_ty))?;
                expect_same_type(element_ty, &actual, types, "list element")?;
            }
            return Ok(Type::List(element_ty.clone()));
        }
        Some(Type::FixedArray(n, element_ty)) => {
            if values.len() != *n as usize {
                return Err(CompileError::new(format!(
                    "fixed array `[{n}]{}` requires exactly {n} elements but got {}",
                    describe_type(element_ty),
                    values.len()
                )));
            }
            for value in values {
                let actual = infer_expr_type(value, functions, types, scope, Some(element_ty))?;
                expect_same_type(element_ty, &actual, types, "array element")?;
            }
            return Ok(Type::FixedArray(*n, element_ty.clone()));
        }
        Some(other) => {
            return Err(CompileError::new(format!(
                "list literal cannot initialize non-list type {}",
                describe_type(other)
            )));
        }
        None => {
            let first_ty = infer_expr_type(&values[0], functions, types, scope, None)?;
            for value in &values[1..] {
                let actual = infer_expr_type(value, functions, types, scope, None)?;
                expect_same_type(&first_ty, &actual, types, "list element")?;
            }
            Box::new(first_ty)
        }
    };

    Ok(Type::List(element_ty))
}

fn flatten_print_args<'a>(args: &'a [Expr]) -> Vec<&'a Expr> {
    let mut flattened = Vec::new();
    for arg in args {
        match arg {
            Expr::Pack(values) => flattened.extend(values.iter()),
            other => flattened.push(other),
        }
    }
    flattened
}

#[derive(Clone, Copy)]
enum PrintMarker {
    Int,
    Uint,
    Bool,
    String,
    Pointer,
    Float,
    Double,
    Char,
    Hex,
    HexUpper,
    Octal,
    Scientific,
    ScientificUpper,
    Shortest,
    ShortestUpper,
    Size,
}

fn parse_format_markers(format: &str) -> Result<Vec<PrintMarker>, CompileError> {
    let mut markers = Vec::new();
    let chars: Vec<char> = format.chars().collect();
    let mut index = 0;
    while index < chars.len() {
        if chars[index] == '{' {
            index += 1;
            let start = index;
            while index < chars.len() && chars[index] != '}' {
                index += 1;
            }
            if index >= chars.len() {
                return Err(CompileError::new("unterminated format marker in @print"));
            }
            let marker: String = chars[start..index].iter().collect();
            let parsed = match marker.as_str() {
                "d" | "ld" | "lld" => PrintMarker::Int,
                "u" | "lu" | "llu" => PrintMarker::Uint,
                "b" => PrintMarker::Bool,
                "s" => PrintMarker::String,
                "p" => PrintMarker::Pointer,
                "f" => PrintMarker::Float,
                "lf" => PrintMarker::Double,
                "c" => PrintMarker::Char,
                "x" | "lx" | "llx" => PrintMarker::Hex,
                "X" | "lX" | "llX" => PrintMarker::HexUpper,
                "o" | "lo" | "llo" => PrintMarker::Octal,
                "e" => PrintMarker::Scientific,
                "E" => PrintMarker::ScientificUpper,
                "g" => PrintMarker::Shortest,
                "G" => PrintMarker::ShortestUpper,
                "zu" => PrintMarker::Size,
                other => {
                    let split_pos = other.find(|c: char| c.is_ascii_alphabetic());
                    if let Some(pos) = split_pos {
                        let (width_part, spec_part) = other.split_at(pos);
                        if !width_part.is_empty() {
                            match spec_part {
                                "d" | "ld" | "lld" => PrintMarker::Int,
                                "u" | "lu" | "llu" => PrintMarker::Uint,
                                "s" => PrintMarker::String,
                                "f" => PrintMarker::Float,
                                "lf" => PrintMarker::Double,
                                "x" | "lx" | "llx" => PrintMarker::Hex,
                                "X" | "lX" | "llX" => PrintMarker::HexUpper,
                                "o" | "lo" | "llo" => PrintMarker::Octal,
                                "e" => PrintMarker::Scientific,
                                "E" => PrintMarker::ScientificUpper,
                                "g" => PrintMarker::Shortest,
                                "G" => PrintMarker::ShortestUpper,
                                "zu" => PrintMarker::Size,
                                _ => {
                                    return Err(CompileError::new(format!(
                                        "unsupported @print marker `{{{marker}}}`"
                                    )));
                                }
                            }
                        } else {
                            return Err(CompileError::new(format!(
                                "unsupported @print marker `{{{marker}}}`"
                            )));
                        }
                    } else {
                        return Err(CompileError::new(format!(
                            "unsupported @print marker `{{{marker}}}`"
                        )));
                    }
                }
            };
            markers.push(parsed);
        }
        index += 1;
    }
    Ok(markers)
}

fn format_type_matches(marker: PrintMarker, ty: &Type) -> bool {
    match marker {
        PrintMarker::Int => is_integer_primitive_type(ty),
        PrintMarker::Uint | PrintMarker::Size => is_integer_primitive_type(ty),
        PrintMarker::Bool => matches!(ty, Type::Bool),
        PrintMarker::String => is_string_compatible(ty),
        PrintMarker::Pointer => {
            matches!(ty, Type::Ref(_) | Type::Mut(_) | Type::Named(_)) || is_string_compatible(ty)
        }
        PrintMarker::Float => matches!(ty, Type::F32),
        PrintMarker::Double => matches!(ty, Type::F64),
        PrintMarker::Char => is_integer_primitive_type(ty),
        PrintMarker::Hex | PrintMarker::HexUpper | PrintMarker::Octal => {
            is_integer_primitive_type(ty)
        }
        PrintMarker::Scientific
        | PrintMarker::ScientificUpper
        | PrintMarker::Shortest
        | PrintMarker::ShortestUpper => {
            matches!(ty, Type::F32 | Type::F64)
        }
    }
}

fn print_marker_name(marker: PrintMarker) -> &'static str {
    match marker {
        PrintMarker::Int => "d",
        PrintMarker::Uint => "u",
        PrintMarker::Bool => "b",
        PrintMarker::String => "s",
        PrintMarker::Pointer => "p",
        PrintMarker::Float => "f",
        PrintMarker::Double => "lf",
        PrintMarker::Char => "c",
        PrintMarker::Hex => "x",
        PrintMarker::HexUpper => "X",
        PrintMarker::Octal => "o",
        PrintMarker::Scientific => "e",
        PrintMarker::ScientificUpper => "E",
        PrintMarker::Shortest => "g",
        PrintMarker::ShortestUpper => "G",
        PrintMarker::Size => "zu",
    }
}

fn validate_type(ty: &Type, types: &HashMap<String, TypeDefInfo>) -> Result<(), CompileError> {
    match ty {
        Type::Void
        | Type::Bool
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::Isize
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::Usize
        | Type::U8
        | Type::F32
        | Type::F64
        | Type::Error
        | Type::None => Ok(()),
        Type::Infer => Err(CompileError::new(
            "cannot infer type from type argument, specify it manually.",
        )),
        Type::Named(name) => {
            if types.contains_key(name) {
                Ok(())
            } else {
                Err(CompileError::new(format!("unknown type `{name}`")))
            }
        }
        Type::Applied(name, type_args) => {
            if !types.contains_key(name) {
                return Err(CompileError::new(format!("unknown type `{name}`")));
            }
            for type_arg in type_args {
                validate_type(type_arg, types)?;
            }
            Ok(())
        }
        Type::Result(inner) => validate_type(inner, types),
        Type::Mut(inner) => validate_type(inner, types),
        Type::Ref(inner) => validate_type(inner, types),
        Type::List(inner) => validate_type(inner, types),
        Type::FixedArray(_, inner) => validate_type(inner, types),
        Type::FnPtr(params, ret) => {
            for param in params {
                validate_type(param, types)?;
            }
            validate_type(ret, types)
        }
    }
}

fn validate_type_with_known_names(ty: &Type, known: &HashSet<String>) -> Result<(), CompileError> {
    match ty {
        Type::Void
        | Type::Bool
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::Isize
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::Usize
        | Type::U8
        | Type::F32
        | Type::F64
        | Type::Error
        | Type::None => Ok(()),
        Type::Infer => Err(CompileError::new(
            "cannot infer type from type argument, specify it manually.",
        )),
        Type::Named(name) => {
            if known.contains(name) {
                Ok(())
            } else {
                Err(CompileError::new(format!("unknown type `{name}`")))
            }
        }
        Type::Applied(name, type_args) => {
            if !known.contains(name) {
                return Err(CompileError::new(format!("unknown type `{name}`")));
            }
            for type_arg in type_args {
                validate_type_with_known_names(type_arg, known)?;
            }
            Ok(())
        }
        Type::Result(inner) => validate_type_with_known_names(inner, known),
        Type::Mut(inner) => validate_type_with_known_names(inner, known),
        Type::Ref(inner) => validate_type_with_known_names(inner, known),
        Type::List(inner) => validate_type_with_known_names(inner, known),
        Type::FixedArray(_, inner) => validate_type_with_known_names(inner, known),
        Type::FnPtr(params, ret) => {
            for param in params {
                validate_type_with_known_names(param, known)?;
            }
            validate_type_with_known_names(ret, known)
        }
    }
}

fn expect_same_type(
    expected: &Type,
    actual: &Type,
    types: &HashMap<String, TypeDefInfo>,
    context: &str,
) -> Result<(), CompileError> {
    if types_compatible(expected, actual, types)? {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "{context} expects type {} but found {}",
            describe_type(expected),
            describe_type(actual)
        )))
    }
}

fn expect_return_type(
    expected: &Type,
    actual: &Type,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<(), CompileError> {
    if types_compatible(expected, actual, types)? {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "return expects type {} but found {}",
            describe_type(expected),
            describe_type(actual)
        )))
    }
}

fn validate_try_usage(
    expr: &Expr,
    expected_return: &Type,
    allow_try_panic: bool,
) -> Result<(), CompileError> {
    if matches!(expr, Expr::Try(_))
        && !allow_try_panic
        && !matches!(expected_return, Type::Result(_))
    {
        return Err(CompileError::new(
            "`?` may only be used in functions returning `T|error`, in `main`, or in test blocks",
        ));
    }
    match expr {
        Expr::Index { base, index } => {
            validate_try_usage(base, expected_return, allow_try_panic)?;
            validate_try_usage(index, expected_return, allow_try_panic)?;
        }
        Expr::FieldAccess { base, .. } => {
            validate_try_usage(base, expected_return, allow_try_panic)?
        }
        Expr::StructInit { fields, .. } => {
            for field in fields {
                validate_try_usage(&field.value, expected_return, allow_try_panic)?;
            }
        }
        Expr::BuiltinCall { args, .. }
        | Expr::MethodCall { args, .. }
        | Expr::Call { args, .. }
        | Expr::Pack(args) => {
            for arg in args {
                validate_try_usage(arg, expected_return, allow_try_panic)?;
            }
            if let Expr::MethodCall { receiver, .. } = expr {
                validate_try_usage(receiver, expected_return, allow_try_panic)?;
            }
            if let Expr::Call { callee, .. } = expr {
                validate_try_usage(callee, expected_return, allow_try_panic)?;
            }
        }
        Expr::Cast { expr, .. }
        | Expr::Try(expr)
        | Expr::Error { message: expr }
        | Expr::Unary { expr, .. } => validate_try_usage(expr, expected_return, allow_try_panic)?,
        Expr::Specialize { callee, .. } => {
            validate_try_usage(callee, expected_return, allow_try_panic)?;
        }
        Expr::Binary { lhs, rhs, .. } => {
            validate_try_usage(lhs, expected_return, allow_try_panic)?;
            validate_try_usage(rhs, expected_return, allow_try_panic)?;
        }
        Expr::Int(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::Path(_)
        | Expr::ListLiteral(_)
        | Expr::None
        | Expr::SizeOf(_)
        | Expr::BitCast { .. } => {
            if let Expr::ListLiteral(values) = expr {
                for value in values {
                    validate_try_usage(value, expected_return, allow_try_panic)?;
                }
            }
        }
    }
    Ok(())
}

fn types_compatible(
    expected: &Type,
    actual: &Type,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<bool, CompileError> {
    let expected = normalize_value_mutability(&resolve_aliases(expected, types)?);
    let actual = normalize_value_mutability(&resolve_aliases(actual, types)?);
    Ok(types_compatible_resolved(&expected, &actual)
        || can_implicitly_convert_numeric(&actual, &expected))
}

fn types_compatible_resolved(expected: &Type, actual: &Type) -> bool {
    if expected == actual {
        return true;
    }
    match (expected, actual) {
        (Type::Result(expected_ok), Type::Result(actual_ok)) => {
            types_compatible_resolved(expected_ok, actual_ok)
        }
        (Type::Result(_expected_ok), Type::Error) => true,
        (Type::Result(expected_ok), other) => types_compatible_resolved(expected_ok, other),
        (expected, Type::None) | (Type::None, expected) => {
            expected == &Type::None || is_nullable_pointer_type(expected)
        }
        (Type::Ref(expected_inner), Type::Mut(actual_inner)) => {
            matches!(actual_inner.as_ref(), Type::Ref(inner) if inner == expected_inner)
        }
        (Type::Ref(inner), other) if inner.as_ref() == &Type::U8 => is_string_compatible(other),
        (Type::FnPtr(ep, er), Type::FnPtr(ap, ar)) => {
            ep.len() == ap.len()
                && ep
                    .iter()
                    .zip(ap.iter())
                    .all(|(e, a)| types_compatible_resolved(e, a))
                && types_compatible_resolved(er, ar)
        }
        _ => false,
    }
}

fn is_string_compatible(ty: &Type) -> bool {
    matches!(ty, Type::Ref(inner) if inner.as_ref() == &Type::U8)
        || matches!(ty, Type::Mut(inner) if matches!(inner.as_ref(), Type::Ref(inner) if inner.as_ref() == &Type::U8))
}

fn is_memory_pointer_type(ty: &Type) -> bool {
    matches!(ty, Type::Ref(_) | Type::Mut(_)) || is_string_compatible(ty)
}

fn pointer_arithmetic_type(ty: &Type) -> Type {
    match ty {
        Type::Ref(inner) if inner.as_ref() == &Type::Void => Type::Ref(Box::new(Type::U8)),
        Type::Ref(inner) => match inner.as_ref() {
            Type::List(elem) => Type::Ref(elem.clone()),
            _ => ty.clone(),
        },
        Type::Mut(inner) => match inner.as_ref() {
            Type::Ref(pointee) if pointee.as_ref() == &Type::Void => {
                Type::Mut(Box::new(Type::Ref(Box::new(Type::U8))))
            }
            Type::Ref(pointee) => match pointee.as_ref() {
                Type::List(elem) => Type::Mut(Box::new(Type::Ref(elem.clone()))),
                _ => ty.clone(),
            },
            _ => ty.clone(),
        },
        _ => ty.clone(),
    }
}

fn is_nullable_pointer_type(ty: &Type) -> bool {
    matches!(ty, Type::Ref(_) | Type::Mut(_)) || is_string_compatible(ty)
}

fn same_enum_type(lhs: &Type, rhs: &Type, types: &HashMap<String, TypeDefInfo>) -> bool {
    let lhs_name = match lhs {
        Type::Named(n) => n,
        _ => return false,
    };
    let rhs_name = match rhs {
        Type::Named(n) => n,
        _ => return false,
    };
    if lhs_name == rhs_name {
        return true;
    }
    if let (Some(lhs_info), Some(rhs_info)) = (types.get(lhs_name), types.get(rhs_name)) {
        if lhs_info.kind == TypeDefKind::Enum && rhs_info.kind == TypeDefKind::Enum {
            return lhs_name == rhs_name;
        }
    }
    false
}

fn as_mut_type(ty: Type) -> Type {
    match ty {
        Type::Mut(_) => ty,
        other => Type::Mut(Box::new(other)),
    }
}

fn propagate_mut(ty: Type) -> Type {
    match ty {
        Type::Ref(_) => Type::Mut(Box::new(ty)),
        other => other,
    }
}

fn normalize_value_mutability(ty: &Type) -> Type {
    match ty {
        Type::Mut(inner) => match inner.as_ref() {
            Type::Ref(inner) => Type::Mut(Box::new(Type::Ref(Box::new(
                normalize_value_mutability(inner),
            )))),
            other => normalize_value_mutability(other),
        },
        Type::Ref(inner) => Type::Ref(Box::new(normalize_value_mutability(inner))),
        Type::List(inner) => Type::List(Box::new(normalize_value_mutability(inner))),
        Type::FixedArray(n, inner) => {
            Type::FixedArray(*n, Box::new(normalize_value_mutability(inner)))
        }
        Type::Result(inner) => Type::Result(Box::new(normalize_value_mutability(inner))),
        other => other.clone(),
    }
}

fn can_compare_with_none(lhs: &Type, rhs: &Type) -> bool {
    matches!((lhs, rhs), (Type::None, Type::None))
        || (lhs == &Type::None && is_nullable_pointer_type(rhs))
        || (rhs == &Type::None && is_nullable_pointer_type(lhs))
}

fn can_cast_between_primitive_refs(source: &Type, target: &Type) -> bool {
    primitive_ref_element_type(source).is_some() && primitive_ref_element_type(target).is_some()
}

fn primitive_ref_element_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Ref(inner) => primitive_ref_base_type(inner),
        Type::Mut(inner) => primitive_ref_element_type(inner),
        _ => None,
    }
}

fn primitive_ref_base_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Void
        | Type::Bool
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::Isize
        | Type::U8
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::Usize
        | Type::F32
        | Type::F64 => Some(ty),
        _ => None,
    }
}

fn is_condition_type(
    ty: &Type,
    types: &HashMap<String, TypeDefInfo>,
) -> Result<bool, CompileError> {
    Ok(is_condition_primitive_type(&resolve_aliases(ty, types)?))
}

fn is_numeric_type(ty: &Type, types: &HashMap<String, TypeDefInfo>) -> Result<bool, CompileError> {
    Ok(is_numeric_primitive_type(&resolve_aliases(ty, types)?))
}

fn is_integer_type(ty: &Type, types: &HashMap<String, TypeDefInfo>) -> Result<bool, CompileError> {
    let ty = resolve_aliases(ty, types)?;
    Ok(is_integer_primitive_type(&ty))
}

fn is_numeric_primitive_type(ty: &Type) -> bool {
    is_integer_primitive_type(ty) || matches!(strip_mut(ty), Type::F32 | Type::F64)
}

fn is_condition_primitive_type(ty: &Type) -> bool {
    matches!(strip_mut(ty), Type::Bool) || is_integer_primitive_type(ty)
}

fn is_integer_primitive_type(ty: &Type) -> bool {
    integer_rank(ty).is_some()
}

fn is_signed_numeric_type(ty: &Type) -> bool {
    is_signed_integer_primitive_type(ty) || matches!(strip_mut(ty), Type::F32 | Type::F64)
}

fn is_signed_integer_primitive_type(ty: &Type) -> bool {
    matches!(
        strip_mut(ty),
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize
    )
}

fn is_unsigned_integer_primitive_type(ty: &Type) -> bool {
    matches!(
        strip_mut(ty),
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize
    )
}

fn integer_rank(ty: &Type) -> Option<u8> {
    match strip_mut(ty) {
        Type::U8 => Some(1),
        Type::I8 => Some(1),
        Type::I16 => Some(2),
        Type::I32 => Some(3),
        Type::I64 | Type::Isize => Some(4),
        Type::U16 => Some(2),
        Type::U32 => Some(3),
        Type::U64 | Type::Usize => Some(4),
        _ => None,
    }
}

fn constant_integer_value(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::Int(value) => Some(*value as i128),
        Expr::Char(value) => Some(*value as i128),
        Expr::Unary {
            op: UnaryOp::Neg,
            expr,
        } => constant_integer_value(expr).map(|value| -value),
        _ => None,
    }
}

fn validate_integer_literal_cast_range(value: i128, ty: &Type) -> Result<(), CompileError> {
    let Some((min, max)) = integer_cast_bounds(ty) else {
        return Ok(());
    };
    if value < min || value > max {
        return Err(CompileError::new(format!(
            "integer literal {value} does not fit in {}",
            describe_type(ty)
        )));
    }
    Ok(())
}

fn integer_cast_bounds(ty: &Type) -> Option<(i128, i128)> {
    match ty {
        Type::I8 => Some((i8::MIN as i128, i8::MAX as i128)),
        Type::I16 => Some((i16::MIN as i128, i16::MAX as i128)),
        Type::I32 => Some((i32::MIN as i128, i32::MAX as i128)),
        Type::I64 => Some((i64::MIN as i128, i64::MAX as i128)),
        Type::Isize => Some((isize::MIN as i128, isize::MAX as i128)),
        Type::U8 => Some((u8::MIN as i128, u8::MAX as i128)),
        Type::U16 => Some((u16::MIN as i128, u16::MAX as i128)),
        Type::U32 => Some((u32::MIN as i128, u32::MAX as i128)),
        Type::U64 => Some((u64::MIN as i128, u64::MAX as i128)),
        Type::Usize => Some((usize::MIN as i128, usize::MAX as i128)),
        _ => None,
    }
}

fn float_rank(ty: &Type) -> Option<u8> {
    match strip_mut(ty) {
        Type::F32 => Some(1),
        Type::F64 => Some(2),
        _ => None,
    }
}

fn common_integer_type(lhs: &Type, rhs: &Type) -> Option<Type> {
    let lhs = strip_mut(lhs);
    let rhs = strip_mut(rhs);
    if lhs == rhs && is_integer_primitive_type(lhs) {
        return Some(lhs.clone());
    }
    if *lhs == Type::I32 && is_integer_primitive_type(rhs) {
        return Some(rhs.clone());
    }
    if *rhs == Type::I32 && is_integer_primitive_type(lhs) {
        return Some(lhs.clone());
    }
    if is_signed_integer_primitive_type(lhs) && is_signed_integer_primitive_type(rhs) {
        return Some(if integer_rank(lhs)? >= integer_rank(rhs)? {
            lhs.clone()
        } else {
            rhs.clone()
        });
    }
    if is_unsigned_integer_primitive_type(lhs) && is_unsigned_integer_primitive_type(rhs) {
        return Some(if integer_rank(lhs)? >= integer_rank(rhs)? {
            lhs.clone()
        } else {
            rhs.clone()
        });
    }
    if is_unsigned_integer_primitive_type(lhs)
        && is_signed_integer_primitive_type(rhs)
        && integer_rank(lhs)? > integer_rank(rhs)?
    {
        return Some(lhs.clone());
    }
    if is_signed_integer_primitive_type(lhs)
        && is_unsigned_integer_primitive_type(rhs)
        && integer_rank(rhs)? > integer_rank(lhs)?
    {
        return Some(rhs.clone());
    }
    None
}

fn common_numeric_type(lhs: &Type, rhs: &Type) -> Option<Type> {
    if let Some(common) = common_integer_type(lhs, rhs) {
        return Some(common);
    }
    let lhs = strip_mut(lhs);
    let rhs = strip_mut(rhs);
    if lhs == rhs && matches!(lhs, Type::F32 | Type::F64) {
        return Some(lhs.clone());
    }
    if matches!(lhs, Type::F32 | Type::F64) && matches!(rhs, Type::F32 | Type::F64) {
        return Some(if float_rank(lhs)? >= float_rank(rhs)? {
            lhs.clone()
        } else {
            rhs.clone()
        });
    }
    None
}

fn can_implicitly_convert_numeric(actual: &Type, expected: &Type) -> bool {
    common_numeric_type(actual, expected)
        .map(|common| common == *expected)
        .unwrap_or(false)
}

fn deref_refs(mut ty: &Type) -> &Type {
    loop {
        match ty {
            Type::Ref(inner) | Type::Mut(inner) => ty = inner,
            _ => return ty,
        }
    }
}

fn strip_mut(mut ty: &Type) -> &Type {
    loop {
        match ty {
            Type::Mut(inner) => ty = inner,
            _ => return ty,
        }
    }
}

fn resolve_aliases(ty: &Type, types: &HashMap<String, TypeDefInfo>) -> Result<Type, CompileError> {
    match ty {
        Type::Named(name) => {
            let Some(type_info) = types.get(name) else {
                return Ok(Type::Named(name.clone()));
            };
            if let Some(alias) = &type_info.alias {
                resolve_aliases(alias, types)
            } else {
                Ok(Type::Named(name.clone()))
            }
        }
        Type::Applied(name, type_args) => Ok(Type::Applied(
            name.clone(),
            type_args
                .iter()
                .map(|type_arg| resolve_aliases(type_arg, types))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Type::Result(inner) => Ok(Type::Result(Box::new(resolve_aliases(inner, types)?))),
        Type::Mut(inner) => Ok(Type::Mut(Box::new(resolve_aliases(inner, types)?))),
        Type::Ref(inner) => Ok(Type::Ref(Box::new(resolve_aliases(inner, types)?))),
        Type::List(inner) => Ok(Type::List(Box::new(resolve_aliases(inner, types)?))),
        other => Ok(other.clone()),
    }
}

fn describe_type(ty: &Type) -> String {
    match ty {
        Type::Void => "void".to_string(),
        Type::Bool => "bool".to_string(),
        Type::I8 => "i8".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I64 => "i64".to_string(),
        Type::Isize => "isize".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U64 => "u64".to_string(),
        Type::Usize => "usize".to_string(),
        Type::U8 => "u8".to_string(),
        Type::F32 => "f32".to_string(),
        Type::F64 => "f64".to_string(),
        Type::Infer => "_".to_string(),
        Type::Named(name) => name.clone(),
        Type::Applied(name, type_args) => format!(
            "{}[{}]",
            name,
            type_args
                .iter()
                .map(describe_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Mut(inner) => format!("mut({})", describe_type(inner)),
        Type::Ref(inner) => format!("ref({})", describe_type(inner)),
        Type::List(inner) => format!("list[{}]", describe_type(inner)),
        Type::FixedArray(n, inner) => format!("[{n}]{}", describe_type(inner)),
        Type::Result(inner) => format!("{}|error", describe_type(inner)),
        Type::Error => "error".to_string(),
        Type::None => "none".to_string(),
        Type::FnPtr(params, ret) => format!(
            "(fn({}) {})",
            params
                .iter()
                .map(describe_type)
                .collect::<Vec<_>>()
                .join(", "),
            describe_type(ret)
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::analyze;
    use crate::{lexer::lex, parser::parse_program};

    #[test]
    fn rejects_non_pub_main() {
        let source = "def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(
            error.to_string(),
            "function `main` must be declared as `pub def main`"
        );
    }

    #[test]
    fn accepts_pub_main() {
        let source = "pub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_string_literals_as_ref_u8() {
        let source = "pub def main() void\n\tval message ref(u8) = \"hello\"\n\t@puts(message)\n\t@print(\"{s}\", {message})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_indexing_and_extern_calls() {
        let source = "type Grid\n\tcells list[list[i32]]\nend\nextern def sleep(t u32) void :: \"sleep\"\npub def main() void\n\tvar grid = Grid(cells: [[1]])\n\tgrid.cells[0][0] = 2\n\tsleep(100 as u32)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_regular_type_aliases() {
        let source = "type Count = i32\npub def main() void\n\tval count Count = 1\n\t@print(\"{d}\", {count})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_bitwise_and_shift_operators() {
        let source = "type Pair\n\tleft i32\n\tright i32\nend\npub def main() void\n\tvar mask i32 = (1 << 3) | (2 & 7) ^ (8 >> 1)\n\tmask &= 15\n\tmask |= 1\n\tmask ^= 2\n\tmask -= 1\n\tval product = (6 * 7) % 5\n\tval pair = Pair(mask, product)\n\tif !(1 == 0) && pair.left - pair.right == 10\n\t\t@print(\"{d} {d}\", {mask, product})\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_multiply_assignment() {
        let source = "pub def main() void\n\tvar value i32 = 3\n\tvalue *= 2\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_numeric_widening_and_float_print_markers() {
        let source = "pub def main() void\n\tval wide i64 = 1\n\tval sum i64 = wide + 2\n\tval small f32 = 3 as f32\n\tval big f64 = 4 as f64\n\t@print(\"{d} {f} {lf}\", {sum, small, big})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_bool_return_types_from_comparisons() {
        let source = "pub def same(x i32, y i32) bool\n\treturn x == y\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_bool_print_marker() {
        let source = "pub def main() void\n\tval ok bool = 1 == 1\n\t@print(\"{b}\", {ok})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_mutable_ref_u8_types() {
        let source = "extern def strcat(dest mut(ref(u8)), src ref(u8)) ref(u8) :: \"strcat\"\npub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_memcpy_and_pointer_add_intrinsics() {
        let source = "pub def main() void\n\tvar buffer mut(ref(u8)) = @alloc(16)\n\t@memcpy(buffer, \"hi\", 2 as usize)\n\tval next = @add(buffer, 1 as usize)\n\t@free(next)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn rejects_break_outside_loop() {
        let source = "pub def main() void\n\tbreak\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(error.to_string(), "`break` may only appear inside a loop");
    }

    #[test]
    fn accepts_as_mut_pointer_coercions() {
        let source = "type StringBuilder\n\tlen usize\nend\n\npub def StringBuilder.append(sb mut(ref(StringBuilder)), n usize) void\n\tsb.len = n\nend\n\npub def main() void\n\tvar sb StringBuilder = StringBuilder(len: 0 as usize)\n\tStringBuilder.append(@as_mut(@addr(sb)), 1 as usize)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_plain_value_return_for_mut_result_type() {
        let source = "type StringBuilder\n\tlen usize\nend\n\npub def build() mut(StringBuilder)|error\n\treturn StringBuilder(len: 0 as usize)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_unwrapped_mut_value_result_as_plain_initializer() {
        let source = "type StringBuilder\n\tlen usize\nend\n\npub def build() mut(StringBuilder)|error\n\treturn StringBuilder(len: 0 as usize)\nend\n\npub def main() void\n\tvar sb StringBuilder = build()?\n\tsb.len = 1 as usize\n\t@print(\"{d}\", {sb.len})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_in_range_integer_literal_cast_to_u8() {
        let source =
            "pub def main() void\n\tval byte u8 = 0 as u8\n\t@print(\"{d}\", {byte})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn rejects_out_of_range_integer_literal_cast_to_u8() {
        let source = "pub def main() void\n\tval byte u8 = 23490234 as u8\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(
            error.to_string(),
            "integer literal 23490234 does not fit in u8"
        );
    }

    #[test]
    fn rejects_negative_integer_literal_cast_to_u8() {
        let source = "pub def main() void\n\tval byte u8 = -123 as u8\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(error.to_string(), "integer literal -123 does not fit in u8");
    }

    #[test]
    fn rejects_string_addition() {
        let source = "pub def main() void\n\tvar line = \"hello\"\n\tline = line + \"sup\"\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(
            error.to_string(),
            "`+` currently requires compatible numeric operands"
        );
    }

    #[test]
    fn rejects_unused_binding() {
        let source = "pub def main() void\n\tval x = 42\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(
            error.to_string(),
            "binding `x` in function `main` is never used"
        );
    }

    #[test]
    fn rejects_var_never_mutated() {
        let source = "pub def main() void\n\tvar x = 42\n\t@print(\"{d}\", {x})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let error = analyze(&program).unwrap_err();
        assert_eq!(
            error.to_string(),
            "variable `x` in function `main` is declared as `var` but never mutated"
        );
    }

    #[test]
    fn accepts_var_that_is_mutated() {
        let source = "pub def main() void\n\tvar x = 42\n\tx = 10\n\t@print(\"{d}\", {x})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_addr_of_mut_value_as_mutation() {
        let source =
            "pub def main() void\n\tvar x = 42\n\tval p = @addr(x)\n\t@print(\"{p}\", {p})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }

    #[test]
    fn accepts_deref_mutation() {
        let source = "pub def main() void\n\tvar x = 42\n\tval p = @addr(x)\n\t@deref(p) = 10\n\t@print(\"{d}\", {x})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        analyze(&program).unwrap();
    }
}
