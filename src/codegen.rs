//! C99 backend for the Scar compiler.
//!
//! GPL-3.0-only
//! (C) Navid Momtahen

use std::{
    collections::HashSet,
    sync::atomic::{AtomicUsize, Ordering},
};

use crate::{
    CompileError,
    ast::{
        BinaryOp, Expr, Function, MatchArmKind, Program, Stmt, Type, TypeDef, TypeDefKind, UnaryOp,
    },
    sema::ProgramInfo,
};

pub fn generate_c(
    program: &Program,
    info: &ProgramInfo,
    install_debug_handlers: bool,
) -> Result<String, CompileError> {
    let mut seen_headers = HashSet::new();
    let mut output = String::new();
    output.push_str("#include <inttypes.h>\n");
    output.push_str("#include <signal.h>\n");
    output.push_str("#include <stdint.h>\n");
    output.push_str("#include <stdio.h>\n");
    output.push_str("#include <stdlib.h>\n");
    output.push_str("#include <string.h>\n");
    output.push_str("#include <errno.h>\n");
    output.push_str("#include <sys/stat.h>\n");
    output.push_str("#if !defined(_WIN32)\n");
    output.push_str("#include <unistd.h>\n");
    output.push_str("#endif\n\n");

    for header in &program.extern_headers {
        if seen_headers.insert(header.clone()) {
            output.push_str(&format!("#include \"{header}\"\n"));
        }
    }
    if !program.extern_headers.is_empty() {
        output.push('\n');
    }

    if install_debug_handlers {
        output.push_str("#if !defined(_WIN32)\n");
        output.push_str("#include <execinfo.h>\n");
        output.push_str("#include <unistd.h>\n");
        output.push_str("#endif\n\n");
    }

    output.push_str(&render_runtime_prelude(install_debug_handlers));

    for type_def in &program.type_defs {
        if let Some(fwd) = render_type_def_forward_decl(type_def) {
            output.push_str(&fwd);
        }
    }
    if program.type_defs.iter().any(|td| td.alias.is_none()) {
        output.push('\n');
    }

    let mut sorted_type_defs = program.type_defs.clone();
    sort_type_defs_by_deps(&mut sorted_type_defs);

    let list_types = collect_list_types(program, info);
    if !list_types.is_empty() {
        for list_ty in &list_types {
            output.push_str(&render_list_typedef(list_ty)?);
        }
        output.push('\n');
    }

    for type_def in &sorted_type_defs {
        output.push_str(&render_type_def(type_def));
        output.push('\n');
    }

    if !list_types.is_empty() {
        for list_ty in &list_types {
            output.push_str(&render_list_helpers(list_ty)?);
            output.push('\n');
        }
    }

    let result_types = collect_result_types(program, info);
    if !result_types.is_empty() {
        for result_ty in &result_types {
            output.push_str(&render_result_support(result_ty));
            output.push('\n');
        }
    }

    for global in &program.globals {
        if !global.mutable {
            output.push_str("const ");
        }
        output.push_str(&render_global_base_type(&global.ty));
        output.push_str(" scar__glob__");
        output.push_str(&global.name);
        output.push_str(&render_global_dims(&global.ty));
        output.push_str(" = ");
        let dummy_function = Function {
            is_pub: false,
            name: String::new(),
            extern_name: None,
            generic_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Void,
            body: Vec::new(),
            line: 0,
            column: 0,
            file_path: None,
        };
        output.push_str(&render_global_init(
            &global.init,
            &global.ty,
            &dummy_function,
            info,
        )?);
        output.push_str(";\n");
    }
    if !program.globals.is_empty() {
        output.push('\n');
    }

    for function in &program.functions {
        if function.extern_name.is_some() {
            continue;
        }
        output.push_str(&render_signature(function, info));
        output.push_str(";\n");
    }
    output.push('\n');

    for function in &program.functions {
        if function.extern_name.is_some() {
            continue;
        }
        render_function(&mut output, function, info, install_debug_handlers)?;
        output.push('\n');
    }

    if let Some(main_function) = program
        .functions
        .iter()
        .find(|function| function.name == "main" && function.extern_name.is_none())
    {
        output.push_str(&render_entrypoint(
            main_function,
            info,
            install_debug_handlers,
        )?);
    }

    Ok(output)
}

fn render_runtime_prelude(install_debug_handlers: bool) -> String {
    let mut output = String::new();
    output.push_str("static void scar_runtime_panic(const char *message) {\n");
    output.push_str("    fprintf(stderr, \"scar: panic: %s\\n\", message);\n");
    output.push_str("    exit(1);\n");
    output.push_str("}\n\n");
    output.push_str("static void *scar_runtime_alloc(size_t size) {\n");
    output.push_str("    void *ptr = malloc(size);\n");
    output.push_str("    if (ptr == NULL) {\n");
    output.push_str("        scar_runtime_panic(\"allocation failed\");\n");
    output.push_str("    }\n");
    output.push_str("    return ptr;\n");
    output.push_str("}\n\n");
    output.push_str("static void *scar_runtime_realloc(void *ptr, size_t size) {\n");
    output.push_str("    void *resized = realloc(ptr, size);\n");
    output.push_str("    if (resized == NULL) {\n");
    output.push_str("        scar_runtime_panic(\"reallocation failed\");\n");
    output.push_str("    }\n");
    output.push_str("    return resized;\n");
    output.push_str("}\n\n");
    output.push_str("static void scar_runtime_free(void *ptr) {\n");
    output.push_str("    free(ptr);\n");
    output.push_str("}\n\n");
    output.push_str("static int scar__argc;\n");
    output.push_str("static char **scar__argv;\n\n");
    if install_debug_handlers {
        output.push_str("static void scar_runtime_signal_handler(int signal_number) {\n");
        output.push_str("    fprintf(stderr, \"scar: fatal signal %d\\n\", signal_number);\n");
        output.push_str("#if !defined(_WIN32)\n");
        output.push_str("    void *frames[64];\n");
        output.push_str("    int frame_count = backtrace(frames, 64);\n");
        output.push_str("    backtrace_symbols_fd(frames, frame_count, STDERR_FILENO);\n");
        output.push_str("#endif\n");
        output.push_str("    _Exit(128 + signal_number);\n");
        output.push_str("}\n\n");
        output.push_str("static void scar_runtime_install_signal_handlers(void) {\n");
        output.push_str("    signal(SIGSEGV, scar_runtime_signal_handler);\n");
        output.push_str("#ifdef SIGBUS\n");
        output.push_str("    signal(SIGBUS, scar_runtime_signal_handler);\n");
        output.push_str("#endif\n");
        output.push_str("#ifdef SIGILL\n");
        output.push_str("    signal(SIGILL, scar_runtime_signal_handler);\n");
        output.push_str("#endif\n");
        output.push_str("#ifdef SIGABRT\n");
        output.push_str("    signal(SIGABRT, scar_runtime_signal_handler);\n");
        output.push_str("#endif\n");
        output.push_str("}\n\n");
    }
    output
}

fn is_deref_init(expr: &Expr) -> bool {
    matches!(expr, Expr::BuiltinCall { name, .. } if name == "deref")
}

fn collect_deref_locals(
    body: &[Stmt],
    locals: &std::collections::HashMap<String, Type>,
) -> std::collections::HashSet<String> {
    let mut set = std::collections::HashSet::new();
    collect_deref_locals_recursive(body, locals, &mut set);
    set
}

fn collect_deref_locals_recursive(
    body: &[Stmt],
    locals: &std::collections::HashMap<String, Type>,
    set: &mut std::collections::HashSet<String>,
) {
    for stmt in body {
        match stmt {
            Stmt::Defer { .. } => { /* handled in render_block */ }
            Stmt::VarDecl { name, init, .. } => {
                if is_deref_init(init) && matches!(locals.get(name), Some(Type::Named(_))) {
                    set.insert(name.clone());
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                collect_deref_locals_recursive(then_body, locals, set);
                collect_deref_locals_recursive(else_body, locals, set);
            }
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    collect_deref_locals_recursive(&arm.body, locals, set);
                }
            }
            Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::ForClassic { body, .. }
            | Stmt::While { body, .. }
            | Stmt::Loop { body, .. } => {
                collect_deref_locals_recursive(body, locals, set);
            }
            _ => {}
        }
    }
}

fn render_function(
    output: &mut String,
    function: &Function,
    info: &ProgramInfo,
    _: bool,
) -> Result<(), CompileError> {
    info.scope_overrides.borrow_mut().clear();
    let locals = info.locals.get(&function.name).cloned().unwrap_or_default();
    let deref_locals = collect_deref_locals(&function.body, &locals);
    let mut next_temp_id = 0usize;
    output.push_str(&render_signature(function, info));
    output.push_str(" {\n");
    if !matches!(function.return_type, Type::Void) {
        output.push_str("    ");
        output.push_str(&c_type(&function.return_type));
        output.push_str(" __scar_return_value;\n");
        if let Type::Result(ok_ty) = &function.return_type {
            if ok_ty.as_ref() == &Type::Void {
                output.push_str("    __scar_return_value = ");
                output.push_str(&render_result_ok_value(ok_ty, "0"));
                output.push_str(";\n");
            }
        }
    }
    let mut defer_stack = Vec::new();
    render_block(
        output,
        &function.body,
        function,
        info,
        1,
        &mut next_temp_id,
        &deref_locals,
        &mut defer_stack,
        0,
    )?;
    output.push_str("__scar_return:\n");
    if matches!(function.return_type, Type::Void) {
        output.push_str("    return;\n");
    } else {
        output.push_str("    return __scar_return_value;\n");
    }
    output.push_str("}\n");
    Ok(())
}

fn type_def_struct_tag(name: &str) -> String {
    format!("{name}_scar_tag")
}

fn enum_c_name(name: &str) -> String {
    format!("scar__enum__{name}")
}

fn render_type_def_forward_decl(type_def: &TypeDef) -> Option<String> {
    if type_def.alias.is_some() {
        return None;
    }
    if type_def.kind == TypeDefKind::Enum {
        return None;
    }
    Some(format!(
        "typedef struct {} {};\n",
        type_def_struct_tag(&type_def.name),
        type_def.name
    ))
}

fn render_type_def(type_def: &TypeDef) -> String {
    if let Some(alias) = &type_def.alias {
        return format!("typedef {} {};\n", c_type(alias), type_def.name);
    }

    let tag = type_def_struct_tag(&type_def.name);
    let mut output = String::new();
    match type_def.kind {
        TypeDefKind::Struct => {
            if type_def.is_extern {
                output.push_str("typedef struct ");
            } else {
                output.push_str("typedef struct ");
            }
            output.push_str(&tag);
            output.push_str(" {\n");
            for field in &type_def.fields {
                output.push_str("    ");
                output.push_str(&c_type_named(&field.ty, &field.name));
                output.push_str(";\n");
            }
            output.push_str("} ");
            output.push_str(&type_def.name);
            output.push_str(";\n");
        }
        TypeDefKind::Union => {
            output.push_str("enum {\n");
            for (index, variant) in type_def.variants.iter().enumerate() {
                output.push_str("    ");
                output.push_str(&union_tag_symbol(&type_def.name, &variant.name));
                output.push_str(" = ");
                output.push_str(&index.to_string());
                output.push_str(",\n");
            }
            output.push_str("};\n");
            output.push_str("typedef struct ");
            output.push_str(&tag);
            output.push_str(" {\n");
            output.push_str("    int32_t tag;\n");
            output.push_str("    union {\n");
            for variant in &type_def.variants {
                output.push_str("        struct {\n");
                for (index, payload_ty) in variant.payload_types.iter().enumerate() {
                    output.push_str("            ");
                    output.push_str(&c_type(payload_ty));
                    output.push(' ');
                    output.push_str(&union_payload_field(index));
                    output.push_str(";\n");
                }
                output.push_str("        } ");
                output.push_str(&variant.name);
                output.push_str(";\n");
            }
            output.push_str("    } data;\n");
            output.push_str("} ");
            output.push_str(&type_def.name);
            output.push_str(";\n");
        }
        TypeDefKind::Enum => {
            let c_name = enum_c_name(&type_def.name);
            output.push_str("typedef enum {\n");
            for (index, variant) in type_def.variants.iter().enumerate() {
                output.push_str("    ");
                output.push_str(&c_name);
                output.push('_');
                output.push_str(&variant.name);
                output.push_str(" = ");
                output.push_str(&index.to_string());
                output.push_str(",\n");
            }
            output.push_str("} ");
            output.push_str(&c_name);
            output.push_str(";\n");
            output.push_str("typedef ");
            output.push_str(&c_name);
            output.push(' ');
            output.push_str(&type_def.name);
            output.push_str(";\n");
        }
    }
    output
}

fn render_result_support(ok_ty: &Type) -> String {
    let mut output = String::new();
    let result_name = result_c_type(ok_ty);
    output.push_str("typedef struct {\n");
    output.push_str("    int32_t is_error;\n");
    output.push_str("    ");
    output.push_str(&result_ok_storage_c_type(ok_ty));
    output.push_str(" ok;\n");
    output.push_str("    const char *error;\n");
    output.push_str("} ");
    output.push_str(&result_name);
    output.push_str(";\n");
    output
}

fn union_tag_symbol(union_name: &str, variant_name: &str) -> String {
    format!("{union_name}__tag__{variant_name}")
}

fn union_payload_field(index: usize) -> String {
    format!("_{index}")
}

fn result_c_type(ok_ty: &Type) -> String {
    format!("scar_result__{}", type_suffix(ok_ty))
}

fn render_result_ok_value(ok_ty: &Type, value: &str) -> String {
    format!(
        "(({}){{ .is_error = 0, .ok = {}, .error = NULL }})",
        result_c_type(ok_ty),
        result_ok_storage_value(ok_ty, value)
    )
}

fn render_result_error_value(ok_ty: &Type, message: &str) -> String {
    format!(
        "(({}){{ .is_error = 1, .ok = ({}){{0}}, .error = {} }})",
        result_c_type(ok_ty),
        result_ok_storage_c_type(ok_ty),
        message
    )
}

fn result_ok_storage_c_type(ok_ty: &Type) -> String {
    if ok_ty == &Type::Void {
        "uint8_t".to_string()
    } else {
        c_type(ok_ty)
    }
}

fn result_ok_storage_value(ok_ty: &Type, value: &str) -> String {
    if ok_ty == &Type::Void {
        "0".to_string()
    } else {
        value.to_string()
    }
}

fn render_signature(function: &Function, info: &ProgramInfo) -> String {
    let return_type = c_type(&function.return_type);
    let symbol = info
        .function_symbols
        .get(&function.name)
        .cloned()
        .unwrap_or_else(|| function.name.clone());
    let params = if function.params.is_empty() {
        "void".to_string()
    } else {
        function
            .params
            .iter()
            .map(|param| c_type_named(&param.ty, &mangle_local_symbol(&param.name)))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let prefix = if function.extern_name.is_some() {
        "extern "
    } else {
        ""
    };
    format!("{prefix}{return_type} {symbol}({params})")
}

fn render_defers<'a>(
    output: &mut String,
    function: &Function,
    info: &ProgramInfo,
    level: usize,
    next_temp_id: &mut usize,
    deref_locals: &std::collections::HashSet<String>,
    defer_stack: &mut Vec<Vec<&'a Vec<Stmt>>>,
    loop_defer_level: usize,
    from_level: usize,
) -> Result<(), CompileError> {
    let mut defers_to_run = Vec::new();
    for scope_defers in defer_stack[from_level..].iter().rev() {
        for defer_body in scope_defers.iter().rev() {
            defers_to_run.push(*defer_body);
        }
    }
    for defer_body in defers_to_run {
        render_block(
            output,
            defer_body,
            function,
            info,
            level,
            next_temp_id,
            deref_locals,
            defer_stack,
            loop_defer_level,
        )?;
    }
    Ok(())
}

fn render_if_chain<'a>(
    defer_stack: &mut Vec<Vec<&'a Vec<Stmt>>>,
    loop_defer_level: usize,
    output: &mut String,
    condition: &Expr,
    then_body: &[Stmt],
    else_body: &[Stmt],
    function: &Function,
    info: &ProgramInfo,
    level: usize,
    next_temp_id: &mut usize,
    deref_locals: &std::collections::HashSet<String>,
    is_first: bool,
) -> Result<(), CompileError> {
    if is_first {
        indent(output, level);
        output.push_str("if (");
    } else {
        output.push_str(" else if (");
    }
    output.push_str(&render_expr(condition, function, info, deref_locals)?);
    output.push_str(") {\n");
    for stmt in then_body {
        render_stmt(
            defer_stack,
            loop_defer_level,
            output,
            stmt,
            function,
            info,
            level + 1,
            next_temp_id,
            deref_locals,
        )?;
    }
    indent(output, level);
    output.push('}');

    if else_body.is_empty() {
        output.push('\n');
        return Ok(());
    }

    if else_body.len() == 1 {
        if let Stmt::If {
            condition: next_cond,
            then_body: next_then,
            else_body: next_else,
            ..
        } = &else_body[0]
        {
            return render_if_chain(
                defer_stack,
                loop_defer_level,
                output,
                next_cond,
                next_then,
                next_else,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                false,
            );
        }
    }

    output.push_str(" else {\n");
    for stmt in else_body {
        render_stmt(
            defer_stack,
            loop_defer_level,
            output,
            stmt,
            function,
            info,
            level + 1,
            next_temp_id,
            deref_locals,
        )?;
    }
    indent(output, level);
    output.push_str("}\n");
    Ok(())
}

fn render_block<'a>(
    output: &mut String,
    body: &'a [Stmt],
    function: &Function,
    info: &ProgramInfo,
    level: usize,
    next_temp_id: &mut usize,
    deref_locals: &std::collections::HashSet<String>,
    defer_stack: &mut Vec<Vec<&'a Vec<Stmt>>>,
    loop_defer_level: usize,
) -> Result<(), CompileError> {
    defer_stack.push(Vec::new());
    for stmt in body {
        if let Stmt::Defer {
            body: defer_body, ..
        } = stmt
        {
            defer_stack.last_mut().unwrap().push(defer_body);
        } else {
            render_stmt(
                defer_stack,
                loop_defer_level,
                output,
                stmt,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
            )?;
        }
    }
    let current_level = defer_stack.len() - 1;
    render_defers(
        output,
        function,
        info,
        level,
        next_temp_id,
        deref_locals,
        defer_stack,
        loop_defer_level,
        current_level,
    )?;
    defer_stack.pop();
    Ok(())
}

fn render_stmt<'a>(
    defer_stack: &mut Vec<Vec<&'a Vec<Stmt>>>,
    loop_defer_level: usize,

    output: &mut String,
    stmt: &Stmt,
    function: &Function,
    info: &ProgramInfo,
    level: usize,
    next_temp_id: &mut usize,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<(), CompileError> {
    let result = render_stmt_inner(
        defer_stack,
        loop_defer_level,
        output,
        stmt,
        function,
        info,
        level,
        next_temp_id,
        deref_locals,
    );
    if let Some((line, column)) = stmt_location(stmt) {
        result.map_err(|error| error.with_location(line, column))
    } else {
        result
    }
}

fn render_stmt_inner<'a>(
    defer_stack: &mut Vec<Vec<&'a Vec<Stmt>>>,
    loop_defer_level: usize,

    output: &mut String,
    stmt: &Stmt,
    function: &Function,
    info: &ProgramInfo,
    level: usize,
    next_temp_id: &mut usize,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<(), CompileError> {
    match stmt {
        Stmt::Defer { .. } => { /* handled in render_block */ }
        Stmt::VarDecl {
            mutable,
            name,
            init,
            declared_type,
            ..
        } => {
            let ty = declared_type
                .clone()
                .or_else(|| info.scope_overrides.borrow().get(name).cloned())
                .or_else(|| {
                    info.locals
                        .get(&function.name)
                        .and_then(|locals| locals.get(name))
                        .cloned()
                })
                .ok_or_else(|| {
                    CompileError::new(format!(
                        "missing inferred type for local `{name}` in `{}`",
                        function.name
                    ))
                })?;
            info.scope_overrides
                .borrow_mut()
                .insert(name.clone(), ty.clone());
            let ty_ref = &ty;
            if let Expr::Try(inner) = init {
                let result_ty = infer_codegen_expr_type(inner, function, info)?;
                let Type::Result(_) = resolve_codegen_aliases(&result_ty, info)? else {
                    return Err(CompileError::new(
                        "`?` requires a result value during code generation",
                    ));
                };
                let temp_id = *next_temp_id;
                *next_temp_id += 1;
                let temp_name = format!("__scar_try_{temp_id}");
                indent(output, level);
                output.push_str(&c_type(&result_ty));
                output.push(' ');
                output.push_str(&temp_name);
                output.push_str(" = ");
                output.push_str(&render_expr(inner, function, info, deref_locals)?);
                output.push_str(";\n");
                indent(output, level);
                output.push_str("if (");
                output.push_str(&temp_name);
                output.push_str(".is_error) {\n");
                if function_allows_try_panic(function) {
                    indent(output, level + 1);
                    output.push_str("scar_runtime_panic(");
                    output.push_str(&temp_name);
                    output.push_str(".error);\n");
                } else if let Type::Result(function_ok_ty) = &function.return_type {
                    indent(output, level + 1);
                    output.push_str("__scar_return_value = ");
                    output.push_str(&render_result_error_value(
                        function_ok_ty,
                        &format!("{temp_name}.error"),
                    ));
                    output.push_str(";\n");
                    indent(output, level + 1);
                    render_defers(
                        output,
                        function,
                        info,
                        level,
                        next_temp_id,
                        deref_locals,
                        defer_stack,
                        loop_defer_level,
                        0,
                    )?;
                    output.push_str("goto __scar_return;\n");
                } else {
                    return Err(CompileError::new(
                        "`?` propagation requires a result-returning function during code generation",
                    ));
                }
                indent(output, level);
                output.push_str("}\n");
                indent(output, level);
                let c_ty_str = c_type_named(ty_ref, &mangle_local_symbol(name));
                let is_aggregate = matches!(ty_ref, Type::Named(_));
                if !mutable && !c_ty_str.starts_with("const ") && !is_aggregate {
                    output.push_str("const ");
                }
                output.push_str(&c_ty_str);
                output.push_str(" = ");
                output.push_str(&format!("{temp_name}.ok"));
                output.push_str(";\n");
                return Ok(());
            }
            if let Expr::BuiltinCall { name: bname, args } = init {
                if bname == "deref" && args.len() == 1 && matches!(ty_ref, Type::Named(_)) {
                    let inner_expr = &args[0];
                    indent(output, level);
                    if !*mutable {
                        output.push_str("const ");
                    }
                    output.push_str(&c_type(ty_ref));
                    output.push_str(" *");
                    output.push_str(&mangle_local_symbol(name));
                    output.push_str(" = ");
                    output.push_str(&render_expr(inner_expr, function, info, deref_locals)?);
                    output.push_str(";\n");
                    return Ok(());
                }
            }
            indent(output, level);
            let c_ty_str = c_type_named(ty_ref, &mangle_local_symbol(name));
            let is_aggregate = matches!(ty_ref, Type::Named(_));
            if !mutable && !c_ty_str.starts_with("const ") && !is_aggregate {
                output.push_str("const ");
            }
            output.push_str(&c_ty_str);
            output.push_str(" = ");
            output.push_str(&render_expr_with_hint(
                init,
                function,
                info,
                Some(ty_ref),
                deref_locals,
            )?);
            output.push_str(";\n");
        }
        Stmt::Assign { target, value, .. } => {
            let target_ty = infer_codegen_expr_type(target, function, info)?;
            if let Expr::Try(inner) = value {
                let result_ty = infer_codegen_expr_type(inner, function, info)?;
                let Type::Result(_ok_ty) = resolve_codegen_aliases(&result_ty, info)? else {
                    return Err(CompileError::new(
                        "`?` requires a result value during code generation",
                    ));
                };
                let temp_id = *next_temp_id;
                *next_temp_id += 1;
                let temp_name = format!("__scar_try_{temp_id}");
                indent(output, level);
                output.push_str(&c_type(&result_ty));
                output.push(' ');
                output.push_str(&temp_name);
                output.push_str(" = ");
                output.push_str(&render_expr(inner, function, info, deref_locals)?);
                output.push_str(";\n");
                indent(output, level);
                output.push_str("if (");
                output.push_str(&temp_name);
                output.push_str(".is_error) {\n");
                if function_allows_try_panic(function) {
                    indent(output, level + 1);
                    output.push_str("scar_runtime_panic(");
                    output.push_str(&temp_name);
                    output.push_str(".error);\n");
                } else if let Type::Result(function_ok_ty) = &function.return_type {
                    indent(output, level + 1);
                    output.push_str("__scar_return_value = ");
                    output.push_str(&render_result_error_value(
                        function_ok_ty,
                        &format!("{temp_name}.error"),
                    ));
                    output.push_str(";\n");
                    indent(output, level + 1);
                    render_defers(
                        output,
                        function,
                        info,
                        level,
                        next_temp_id,
                        deref_locals,
                        defer_stack,
                        loop_defer_level,
                        0,
                    )?;
                    output.push_str("goto __scar_return;\n");
                } else {
                    return Err(CompileError::new(
                        "`?` propagation requires a result-returning function during code generation",
                    ));
                }
                indent(output, level);
                output.push_str("}\n");
                indent(output, level);
                output.push_str(&render_expr(target, function, info, deref_locals)?);
                output.push_str(" = ");
                output.push_str(&format!("{temp_name}.ok"));
                output.push_str(";\n");
                return Ok(());
            }
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" = ");
            output.push_str(&render_expr_with_hint(
                value,
                function,
                info,
                Some(&target_ty),
                deref_locals,
            )?);
            output.push_str(";\n");
        }
        Stmt::AddAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" += ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::MulAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" *= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::SubAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" -= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::DivAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" /= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::BitAndAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" &= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::BitOrAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" |= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::BitXorAssign { target, value, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str(" ^= ");
            output.push_str(&render_expr(value, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::Increment { target, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str("++;\n");
        }
        Stmt::Decrement { target, .. } => {
            indent(output, level);
            output.push_str(&render_expr(target, function, info, deref_locals)?);
            output.push_str("--;\n");
        }
        Stmt::Assert {
            line,
            column,
            condition,
        } => {
            indent(output, level);
            output.push_str("if (!(");
            output.push_str(&render_expr(condition, function, info, deref_locals)?);
            output.push_str(")) {\n");
            indent(output, level + 1);
            output.push_str(&format!(
                "scar_runtime_panic(\"assertion failed in {} at {}:{}\");\n",
                escape_c_string(&function.name),
                line,
                column
            ));
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::Return { value: None, .. } => {
            indent(output, level);
            if let Type::Result(ok_ty) = &function.return_type {
                if ok_ty.as_ref() == &Type::Void {
                    output.push_str("__scar_return_value = ");
                    output.push_str(&render_result_ok_value(ok_ty, "0"));
                    output.push_str(";\n");
                    indent(output, level);
                }
            }
            render_defers(
                output,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                defer_stack,
                loop_defer_level,
                0,
            )?;
            output.push_str("goto __scar_return;\n");
        }
        Stmt::Return {
            value: Some(value), ..
        } => {
            if let Expr::Try(inner) = value {
                let result_ty = infer_codegen_expr_type(inner, function, info)?;
                let Type::Result(_) = resolve_codegen_aliases(&result_ty, info)? else {
                    return Err(CompileError::new(
                        "`?` requires a result value during code generation",
                    ));
                };
                let temp_id = *next_temp_id;
                *next_temp_id += 1;
                let temp_name = format!("__scar_try_{temp_id}");
                indent(output, level);
                output.push_str(&c_type(&result_ty));
                output.push(' ');
                output.push_str(&temp_name);
                output.push_str(" = ");
                output.push_str(&render_expr(inner, function, info, deref_locals)?);
                output.push_str(";\n");
                indent(output, level);
                output.push_str("if (");
                output.push_str(&temp_name);
                output.push_str(".is_error) {\n");
                if function_allows_try_panic(function) {
                    indent(output, level + 1);
                    output.push_str("scar_runtime_panic(");
                    output.push_str(&temp_name);
                    output.push_str(".error);\n");
                } else if let Type::Result(function_ok_ty) = &function.return_type {
                    indent(output, level + 1);
                    output.push_str("__scar_return_value = ");
                    output.push_str(&render_result_error_value(
                        function_ok_ty,
                        &format!("{temp_name}.error"),
                    ));
                    output.push_str(";\n");
                    indent(output, level + 1);
                    render_defers(
                        output,
                        function,
                        info,
                        level,
                        next_temp_id,
                        deref_locals,
                        defer_stack,
                        loop_defer_level,
                        0,
                    )?;
                    output.push_str("goto __scar_return;\n");
                } else {
                    return Err(CompileError::new(
                        "`?` propagation requires a result-returning function during code generation",
                    ));
                }
                indent(output, level);
                output.push_str("}\n");
                indent(output, level);
                output.push_str("__scar_return_value = ");
                if let Type::Result(function_ok_ty) = &function.return_type {
                    output.push_str(&render_result_ok_value(
                        function_ok_ty,
                        &format!("{temp_name}.ok"),
                    ));
                } else {
                    output.push_str(&format!("{temp_name}.ok"));
                }
                output.push_str(";\n");
                indent(output, level);
                render_defers(
                    output,
                    function,
                    info,
                    level,
                    next_temp_id,
                    deref_locals,
                    defer_stack,
                    loop_defer_level,
                    0,
                )?;
                output.push_str("goto __scar_return;\n");
                return Ok(());
            }
            indent(output, level);
            output.push_str("__scar_return_value = ");
            output.push_str(&render_expr_with_hint(
                value,
                function,
                info,
                Some(&function.return_type),
                deref_locals,
            )?);
            output.push_str(";\n");
            indent(output, level);
            render_defers(
                output,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                defer_stack,
                loop_defer_level,
                0,
            )?;
            output.push_str("goto __scar_return;\n");
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            ..
        } => {
            render_if_chain(
                defer_stack,
                loop_defer_level,
                output,
                condition,
                then_body,
                else_body,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                true,
            )?;
        }
        Stmt::Match { expr, arms, .. } => {
            let matched_ty = infer_codegen_expr_type(expr, function, info)?;
            let temp_id = *next_temp_id;
            *next_temp_id += 1;
            let temp_name = format!("__scar_match_{temp_id}");
            indent(output, level);
            output.push_str("{\n");
            indent(output, level + 1);
            output.push_str(&c_type(&matched_ty));
            output.push(' ');
            output.push_str(&temp_name);
            output.push_str(" = ");
            output.push_str(&render_expr(expr, function, info, deref_locals)?);
            output.push_str(";\n");
            match resolve_codegen_aliases(&matched_ty, info)? {
                Type::Result(ok_ty) => {
                    for (index, arm) in arms.iter().enumerate() {
                        let saved_overrides = info.scope_overrides.borrow().clone();
                        {
                            let mut overrides = info.scope_overrides.borrow_mut();
                            if let Some(binding) =
                                arm.bindings.first().and_then(|binding| binding.as_ref())
                            {
                                let binding_ty = match &arm.kind {
                                    MatchArmKind::Ok => (*ok_ty).clone(),
                                    MatchArmKind::Error => Type::Ref(Box::new(Type::U8)),
                                    MatchArmKind::Variant(_) => unreachable!(),
                                };
                                overrides.insert(binding.clone(), binding_ty);
                            }
                        }
                        indent(output, level + 1);
                        if index == 0 {
                            output.push_str("if (");
                        } else {
                            output.push_str("else if (");
                        }
                        match &arm.kind {
                            MatchArmKind::Ok => output.push_str("!"),
                            MatchArmKind::Error => {}
                            MatchArmKind::Variant(name) => {
                                return Err(CompileError::new(format!(
                                    "unexpected union match arm `{name}` for result code generation"
                                )));
                            }
                        }
                        output.push_str(&temp_name);
                        output.push_str(".is_error) {\n");
                        if let Some(binding) =
                            arm.bindings.first().and_then(|binding| binding.as_ref())
                        {
                            indent(output, level + 2);
                            match &arm.kind {
                                MatchArmKind::Ok => {
                                    output.push_str(&c_type_named(
                                        ok_ty.as_ref(),
                                        &mangle_local_symbol(binding),
                                    ));
                                    output.push_str(" = ");
                                    output.push_str(&temp_name);
                                    output.push_str(".ok;\n");
                                }
                                MatchArmKind::Error => {
                                    output.push_str("const char * ");
                                    output.push_str(&mangle_local_symbol(binding));
                                    output.push_str(" = ");
                                    output.push_str(&temp_name);
                                    output.push_str(".error;\n");
                                }
                                MatchArmKind::Variant(_) => unreachable!(),
                            }
                        }
                        for stmt in &arm.body {
                            render_stmt(
                                defer_stack,
                                loop_defer_level,
                                output,
                                stmt,
                                function,
                                info,
                                level + 2,
                                next_temp_id,
                                deref_locals,
                            )?;
                        }
                        *info.scope_overrides.borrow_mut() = saved_overrides;
                        indent(output, level + 1);
                        output.push_str("}\n");
                    }
                }
                Type::Named(union_name) => {
                    let type_info = info.types.get(&union_name).ok_or_else(|| {
                        CompileError::new(format!(
                            "unknown type `{union_name}` in match code generation"
                        ))
                    })?;
                    if type_info.kind == TypeDefKind::Enum {
                        for (index, arm) in arms.iter().enumerate() {
                            let MatchArmKind::Variant(variant_name) = &arm.kind else {
                                return Err(CompileError::new(
                                    "result-style match arms are not supported for enum code generation",
                                ));
                            };
                            let bare_variant =
                                variant_name.rsplit('.').next().unwrap_or(variant_name);
                            if bare_variant == "_" {
                                indent(output, level + 1);
                                output.push_str("else {\n");
                                for stmt in &arm.body {
                                    render_stmt(
                                        defer_stack,
                                        loop_defer_level,
                                        output,
                                        stmt,
                                        function,
                                        info,
                                        level + 2,
                                        next_temp_id,
                                        deref_locals,
                                    )?;
                                }
                                indent(output, level + 1);
                                output.push_str("}\n");
                                continue;
                            }
                            indent(output, level + 1);
                            if index == 0 {
                                output.push_str("if (");
                            } else {
                                output.push_str("else if (");
                            }
                            output.push_str(&temp_name);
                            output.push_str(" == ");
                            output.push_str(&format!(
                                "{}_{}",
                                enum_c_name(&union_name),
                                bare_variant
                            ));
                            output.push_str(") {\n");
                            for stmt in &arm.body {
                                render_stmt(
                                    defer_stack,
                                    loop_defer_level,
                                    output,
                                    stmt,
                                    function,
                                    info,
                                    level + 2,
                                    next_temp_id,
                                    deref_locals,
                                )?;
                            }
                            indent(output, level + 1);
                            output.push_str("}\n");
                        }
                    } else {
                        for (index, arm) in arms.iter().enumerate() {
                            let MatchArmKind::Variant(variant_name) = &arm.kind else {
                                return Err(CompileError::new(
                                    "result-style match arms are not supported for union code generation",
                                ));
                            };
                            let bare_variant =
                                variant_name.rsplit('.').next().unwrap_or(variant_name);
                            if bare_variant == "_" {
                                indent(output, level + 1);
                                output.push_str("else {\n");
                                for stmt in &arm.body {
                                    render_stmt(
                                        defer_stack,
                                        loop_defer_level,
                                        output,
                                        stmt,
                                        function,
                                        info,
                                        level + 2,
                                        next_temp_id,
                                        deref_locals,
                                    )?;
                                }
                                indent(output, level + 1);
                                output.push_str("}\n");
                                continue;
                            }
                            let payload_types =
                                type_info.variant_map.get(bare_variant).ok_or_else(|| {
                                    CompileError::new(format!(
                                        "union `{union_name}` has no variant `{variant_name}`"
                                    ))
                                })?;
                            indent(output, level + 1);
                            if index == 0 {
                                output.push_str("if (");
                            } else {
                                output.push_str("else if (");
                            }
                            output.push_str(&temp_name);
                            output.push_str(".tag == ");
                            output.push_str(&union_tag_symbol(&union_name, bare_variant));
                            output.push_str(") {\n");
                            for (binding, payload_ty, payload_index) in arm
                                .bindings
                                .iter()
                                .zip(payload_types.iter())
                                .zip(0usize..)
                                .map(|((binding, payload_ty), payload_index)| {
                                    (binding, payload_ty, payload_index)
                                })
                            {
                                if let Some(binding) = binding {
                                    indent(output, level + 2);
                                    output.push_str(&c_type_named(
                                        payload_ty,
                                        &mangle_local_symbol(binding),
                                    ));
                                    output.push_str(" = ");
                                    output.push_str(&temp_name);
                                    output.push_str(".data.");
                                    output.push_str(bare_variant);
                                    output.push('.');
                                    output.push_str(&union_payload_field(payload_index));
                                    output.push_str(";\n");
                                }
                            }
                            let saved_overrides = info.scope_overrides.borrow().clone();
                            {
                                let mut overrides = info.scope_overrides.borrow_mut();
                                for (binding, payload_ty) in
                                    arm.bindings.iter().zip(payload_types.iter())
                                {
                                    if let Some(binding) = binding {
                                        overrides.insert(binding.clone(), payload_ty.clone());
                                    }
                                }
                            }
                            for stmt in &arm.body {
                                render_stmt(
                                    defer_stack,
                                    loop_defer_level,
                                    output,
                                    stmt,
                                    function,
                                    info,
                                    level + 2,
                                    next_temp_id,
                                    deref_locals,
                                )?;
                            }
                            *info.scope_overrides.borrow_mut() = saved_overrides;
                            indent(output, level + 1);
                            output.push_str("}\n");
                        }
                    }
                }
                other => {
                    if !is_integer_codegen_type(&other) {
                        return Err(CompileError::new(format!(
                            "`match` expects a union or result value during code generation, got {}",
                            describe_type(&other)
                        )));
                    }
                    let mut has_wildcard = false;
                    for (index, arm) in arms.iter().enumerate() {
                        let MatchArmKind::Variant(variant_name) = &arm.kind else {
                            return Err(CompileError::new(
                                "integer matches require variant arms during code generation",
                            ));
                        };
                        indent(output, level + 1);
                        if variant_name == "_" {
                            has_wildcard = true;
                            if index > 0 {
                                output.push_str("else {\n");
                            } else {
                                output.push_str("{\n");
                            }
                        } else {
                            if index == 0 {
                                output.push_str("if (");
                            } else {
                                output.push_str("else if (");
                            }
                            output.push_str(&temp_name);
                            output.push_str(" == ");
                            if variant_name
                                .chars()
                                .next()
                                .is_some_and(|c| c.is_alphabetic() || c == '_')
                            {
                                output.push_str(&render_symbol_name(variant_name, function, info));
                            } else {
                                output.push_str(variant_name);
                            }
                            output.push_str(") {\n");
                        }
                        for stmt in &arm.body {
                            render_stmt(
                                defer_stack,
                                loop_defer_level,
                                output,
                                stmt,
                                function,
                                info,
                                level + 2,
                                next_temp_id,
                                deref_locals,
                            )?;
                        }
                        indent(output, level + 1);
                        output.push_str("}\n");
                        if has_wildcard {
                            break;
                        }
                    }
                }
            }
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::Block(body) => {
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level,
                    next_temp_id,
                    deref_locals,
                )?;
            }
        }
        Stmt::Expr { expr, .. } => {
            if let Expr::Try(inner) = expr {
                let result_ty = infer_codegen_expr_type(inner, function, info)?;
                let Type::Result(_ok_ty) = resolve_codegen_aliases(&result_ty, info)? else {
                    return Err(CompileError::new(
                        "`?` requires a result value during code generation",
                    ));
                };
                let temp_id = *next_temp_id;
                *next_temp_id += 1;
                let temp_name = format!("__scar_try_{temp_id}");
                indent(output, level);
                output.push_str(&c_type(&result_ty));
                output.push(' ');
                output.push_str(&temp_name);
                output.push_str(" = ");
                output.push_str(&render_expr(inner, function, info, deref_locals)?);
                output.push_str(";\n");
                indent(output, level);
                output.push_str("if (");
                output.push_str(&temp_name);
                output.push_str(".is_error) {\n");
                if function_allows_try_panic(function) {
                    indent(output, level + 1);
                    output.push_str("scar_runtime_panic(");
                    output.push_str(&temp_name);
                    output.push_str(".error);\n");
                } else if let Type::Result(function_ok_ty) = &function.return_type {
                    indent(output, level + 1);
                    output.push_str("__scar_return_value = ");
                    output.push_str(&render_result_error_value(
                        function_ok_ty,
                        &format!("{temp_name}.error"),
                    ));
                    output.push_str(";\n");
                    indent(output, level + 1);
                    render_defers(
                        output,
                        function,
                        info,
                        level,
                        next_temp_id,
                        deref_locals,
                        defer_stack,
                        loop_defer_level,
                        0,
                    )?;
                    output.push_str("goto __scar_return;\n");
                } else {
                    return Err(CompileError::new(
                        "`?` propagation requires a result-returning function during code generation",
                    ));
                }
                indent(output, level);
                output.push_str("}\n");
                return Ok(());
            }
            indent(output, level);
            output.push_str(&render_expr(expr, function, info, deref_locals)?);
            output.push_str(";\n");
        }
        Stmt::ForRange {
            pragma,
            var_name,
            start,
            end,
            body,
            ..
        } => {
            let var_ty = info
                .locals
                .get(&function.name)
                .and_then(|locals| locals.get(var_name))
                .ok_or_else(|| {
                    CompileError::new(format!(
                        "missing type for for-loop variable `{var_name}` in `{}`",
                        function.name
                    ))
                })?;
            indent(output, level);
            if let Some(pragma) = pragma {
                output.push_str("#pragma ");
                output.push_str(pragma);
                output.push('\n');
                indent(output, level);
            }
            output.push_str(&format!("for ({} ", c_type(var_ty)));
            output.push_str(&mangle_local_symbol(var_name));
            output.push_str(" = ");
            output.push_str(&render_expr(start, function, info, deref_locals)?);
            output.push_str("; ");
            output.push_str(&mangle_local_symbol(var_name));
            output.push_str(" < ");
            output.push_str(&render_expr(end, function, info, deref_locals)?);
            output.push_str("; ++");
            output.push_str(&mangle_local_symbol(var_name));
            output.push_str(") {\n");
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level + 1,
                    next_temp_id,
                    deref_locals,
                )?;
            }
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::ForEach {
            var_name,
            iterable,
            body,
            ..
        } => {
            let iterable_ty = infer_codegen_expr_type(iterable, function, info)?;
            let Type::List(element_ty) = deref_refs(&iterable_ty) else {
                return Err(CompileError::new(format!(
                    "expected list iterable during code generation, got {}",
                    describe_type(&iterable_ty)
                )));
            };
            let temp_id = *next_temp_id;
            *next_temp_id += 1;
            let iter_name = format!("__scar_iter_{temp_id}");
            let index_name = format!("__scar_index_{temp_id}");

            indent(output, level);
            output.push_str("{\n");
            indent(output, level + 1);
            output.push_str(&c_type(&iterable_ty));
            output.push(' ');
            output.push_str(&iter_name);
            output.push_str(" = ");
            output.push_str(&render_expr(iterable, function, info, deref_locals)?);
            output.push_str(";\n");
            indent(output, level + 1);
            output.push_str("for (int32_t ");
            output.push_str(&index_name);
            output.push_str(" = 0; ");
            output.push_str(&index_name);
            output.push_str(" < ");
            output.push_str(&iter_name);
            output.push_str(".len; ++");
            output.push_str(&index_name);
            output.push_str(") {\n");
            indent(output, level + 2);
            output.push_str(&c_type_named(element_ty, &mangle_local_symbol(var_name)));
            output.push_str(" = ");
            output.push_str(&iter_name);
            output.push_str(".data[");
            output.push_str(&index_name);
            output.push_str("];\n");
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level + 2,
                    next_temp_id,
                    deref_locals,
                )?;
            }
            indent(output, level + 1);
            output.push_str("}\n");
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::ForClassic {
            pragma,
            var_name,
            init,
            condition,
            increment,
            body,
            ..
        } => {
            let var_ty = info
                .locals
                .get(&function.name)
                .and_then(|locals| locals.get(var_name))
                .ok_or_else(|| {
                    CompileError::new(format!(
                        "missing type for for-loop variable `{var_name}` in `{}`",
                        function.name
                    ))
                })?;
            indent(output, level);
            if let Some(pragma) = pragma {
                output.push_str("#pragma ");
                output.push_str(pragma);
                output.push('\n');
                indent(output, level);
            }
            output.push_str(&format!("for ({} ", c_type(var_ty)));
            output.push_str(&mangle_local_symbol(var_name));
            output.push_str(" = ");
            output.push_str(&render_expr(init, function, info, deref_locals)?);
            output.push_str("; ");
            output.push_str(&render_expr(condition, function, info, deref_locals)?);
            output.push_str("; ");
            output.push_str(&render_expr(increment, function, info, deref_locals)?);
            output.push_str(") {\n");
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level + 1,
                    next_temp_id,
                    deref_locals,
                )?;
            }
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::While {
            condition, body, ..
        } => {
            indent(output, level);
            output.push_str("while (");
            output.push_str(&render_expr(condition, function, info, deref_locals)?);
            output.push_str(") {\n");
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level + 1,
                    next_temp_id,
                    deref_locals,
                )?;
            }
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::Loop { body, .. } => {
            indent(output, level);
            output.push_str("for (;;) {\n");
            for stmt in body {
                render_stmt(
                    defer_stack,
                    loop_defer_level,
                    output,
                    stmt,
                    function,
                    info,
                    level + 1,
                    next_temp_id,
                    deref_locals,
                )?;
            }
            indent(output, level);
            output.push_str("}\n");
        }
        Stmt::Continue { .. } => {
            indent(output, level);
            render_defers(
                output,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                defer_stack,
                loop_defer_level,
                loop_defer_level,
            )?;
            output.push_str("continue;\n");
        }
        Stmt::Break { .. } => {
            indent(output, level);
            render_defers(
                output,
                function,
                info,
                level,
                next_temp_id,
                deref_locals,
                defer_stack,
                loop_defer_level,
                loop_defer_level,
            )?;
            output.push_str("break;\n");
        }
    }
    Ok(())
}

fn stmt_location(stmt: &Stmt) -> Option<(usize, usize)> {
    match stmt {
        Stmt::Block(body) => body.first().and_then(stmt_location),
        Stmt::Defer { line, column, .. }
        | Stmt::VarDecl { line, column, .. }
        | Stmt::Assign { line, column, .. }
        | Stmt::AddAssign { line, column, .. }
        | Stmt::MulAssign { line, column, .. }
        | Stmt::SubAssign { line, column, .. }
        | Stmt::DivAssign { line, column, .. }
        | Stmt::BitAndAssign { line, column, .. }
        | Stmt::BitOrAssign { line, column, .. }
        | Stmt::BitXorAssign { line, column, .. }
        | Stmt::Increment { line, column, .. }
        | Stmt::Decrement { line, column, .. }
        | Stmt::Assert { line, column, .. }
        | Stmt::Return { line, column, .. }
        | Stmt::If { line, column, .. }
        | Stmt::Match { line, column, .. }
        | Stmt::Expr { line, column, .. }
        | Stmt::ForRange { line, column, .. }
        | Stmt::ForEach { line, column, .. }
        | Stmt::ForClassic { line, column, .. }
        | Stmt::While { line, column, .. }
        | Stmt::Loop { line, column, .. }
        | Stmt::Continue { line, column }
        | Stmt::Break { line, column } => Some((*line, *column)),
    }
}

fn render_expr(
    expr: &Expr,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    render_expr_with_hint(expr, function, info, None, deref_locals)
}

fn render_expr_with_hint(
    expr: &Expr,
    function: &Function,
    info: &ProgramInfo,
    hint: Option<&Type>,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    if let Some(Type::Result(ok_ty)) = hint {
        let actual_ty =
            resolve_codegen_aliases(&infer_codegen_expr_type(expr, function, info)?, info)?;
        return match actual_ty {
            Type::Result(_) => render_expr_with_hint(expr, function, info, None, deref_locals),
            Type::Error => match expr {
                Expr::Error { message } => Ok(render_result_error_value(
                    ok_ty,
                    &render_expr(message, function, info, deref_locals)?,
                )),
                _ => Err(CompileError::new(
                    "missing error constructor payload during code generation",
                )),
            },
            _ => Ok(render_result_ok_value(
                ok_ty,
                &render_expr_with_hint(expr, function, info, Some(ok_ty), deref_locals)?,
            )),
        };
    }
    match expr {
        Expr::Int(value) => Ok(value.to_string()),
        Expr::Char(value) => Ok(value.to_string()),
        Expr::Bool(value) => Ok(if *value {
            "1".to_string()
        } else {
            "0".to_string()
        }),
        Expr::Float(value) => {
            if let Some(Type::F32) = hint {
                let s = value.to_string();
                if s.contains('.') {
                    Ok(format!("{s}f"))
                } else {
                    Ok(format!("{s}.0f"))
                }
            } else {
                Ok(value.to_string())
            }
        }
        Expr::String(value) => Ok(format!("\"{}\"", escape_c_string(value))),
        Expr::None => Ok("NULL".to_string()),
        Expr::ListLiteral(values) => {
            if let Some(Type::FixedArray(_, element_ty)) = hint {
                let rendered = values
                    .iter()
                    .map(|v| {
                        render_expr_with_hint(v, function, info, Some(element_ty), deref_locals)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(format!("{{{}}}", rendered.join(", ")));
            }
            let list_ty = match hint {
                Some(Type::List(_)) => hint.cloned().ok_or_else(|| {
                    CompileError::new("missing list type hint during code generation")
                })?,
                _ => infer_codegen_expr_type(expr, function, info)?,
            };
            render_list_literal(values, &list_ty, function, info, deref_locals)
        }
        Expr::Index { base, index } => render_index_expr(base, index, function, info, deref_locals),
        Expr::FieldAccess { base, field } => {
            render_field_access(base, field, function, info, deref_locals)
        }
        Expr::StructInit { name, fields, .. } => {
            let type_info = info.types.get(name).ok_or_else(|| {
                CompileError::new(format!("unknown type `{name}` in code generation"))
            })?;
            if type_info.kind != TypeDefKind::Struct {
                return Err(CompileError::new(format!(
                    "union `{name}` cannot be initialized like a struct"
                )));
            }
            let rendered_fields = fields
                .iter()
                .map(|field| {
                    let field_ty = type_info.field_map.get(&field.name).ok_or_else(|| {
                        CompileError::new(format!("type `{name}` has no field `{}`", field.name))
                    })?;
                    Ok(format!(
                        ".{} = {}",
                        field.name,
                        render_expr_with_hint(
                            &field.value,
                            function,
                            info,
                            Some(field_ty),
                            deref_locals
                        )?
                    ))
                })
                .collect::<Result<Vec<_>, CompileError>>()?;
            Ok(format!("({name}){{ {} }}", rendered_fields.join(", ")))
        }
        Expr::BuiltinCall { name, args } => {
            render_builtin_call(name, args, function, info, deref_locals)
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => render_list_method_call(method, receiver, args, function, info, deref_locals),
        Expr::Path(path) => match path.as_slice() {
            [name] => {
                let symbol = render_symbol_name(name, function, info);
                Ok(symbol)
            }
            [type_name, variant_name] => {
                if let Some(type_info) = info.types.get(type_name) {
                    if type_info.kind == TypeDefKind::Enum {
                        return Ok(format!("{}_{}", enum_c_name(type_name), variant_name));
                    }
                }
                Err(CompileError::new(format!(
                    "unsupported qualified expression `{}` in code generation",
                    path.join(".")
                )))
            }
            _ => Err(CompileError::new(format!(
                "unsupported qualified expression `{}` in code generation",
                path.join(".")
            ))),
        },
        Expr::Call { callee, args } => render_call(callee, args, function, info, deref_locals),
        Expr::Specialize { .. } => Err(CompileError::new(
            "generic specialization must be resolved before code generation",
        )),
        Expr::Cast { expr, ty } => {
            if matches!(expr.as_ref(), Expr::ListLiteral(_)) {
                return render_expr_with_hint(expr, function, info, Some(ty), deref_locals);
            }
            Ok(format!(
                "(({})({}))",
                c_type(ty),
                render_expr(expr, function, info, deref_locals)?
            ))
        }
        Expr::SizeOf(ty) => Ok(format!("((size_t)sizeof({}))", c_type(ty))),
        Expr::BitCast { expr, ty } => {
            let src = render_expr(expr, function, info, deref_locals)?;
            let dst_ty = c_type(ty);
            match &*ty {
                Type::Ref(_) | Type::Mut(_) => Ok(format!("(({dst_ty})({src}))")),
                _ => Ok(format!(
                    "({{ {dst_ty} __scar_bc; memcpy(&__scar_bc, &({src}), sizeof(__scar_bc)); __scar_bc; }})"
                )),
            }
        }
        Expr::Error { .. } => Err(CompileError::new(
            "`error(...)` requires a `T|error` context during code generation",
        )),
        Expr::Try(inner) => render_try_expr(inner, function, info, deref_locals),
        Expr::Unary { op, expr } => match op {
            UnaryOp::Neg => Ok(format!(
                "(-({}))",
                render_expr(expr, function, info, deref_locals)?
            )),
            UnaryOp::LogicalNot => Ok(format!(
                "(!({}))",
                render_expr(expr, function, info, deref_locals)?
            )),
            UnaryOp::BitNot => Ok(format!(
                "(~({}))",
                render_expr(expr, function, info, deref_locals)?
            )),
            UnaryOp::PostfixInc => Ok(format!(
                "({}++)",
                render_expr(expr, function, info, deref_locals)?
            )),
            UnaryOp::PostfixDec => Ok(format!(
                "({}--)",
                render_expr(expr, function, info, deref_locals)?
            )),
        },
        Expr::Pack(_) => Err(CompileError::new(
            "packed `{...}` expressions are only valid inside @print",
        )),
        Expr::Binary { lhs, op, rhs } => {
            if *op == BinaryOp::ShiftRight {
                return render_logical_shift_right(lhs, rhs, function, info, deref_locals);
            }
            let operator = match op {
                BinaryOp::Add => "+",
                BinaryOp::Subtract => "-",
                BinaryOp::Divide => "/",
                BinaryOp::Multiply => "*",
                BinaryOp::Modulo => "%",
                BinaryOp::LogicalAnd => "&&",
                BinaryOp::LogicalOr => "||",
                BinaryOp::BitAnd => "&",
                BinaryOp::BitOr => "|",
                BinaryOp::BitXor => "^",
                BinaryOp::ShiftLeft => "<<",
                BinaryOp::LessThan => "<",
                BinaryOp::LessEqual => "<=",
                BinaryOp::GreaterThan => ">",
                BinaryOp::GreaterEqual => ">=",
                BinaryOp::Equal => "==",
                BinaryOp::NotEqual => "!=",
                BinaryOp::ShiftRight => unreachable!("handled above"),
            };
            let lhs_type = infer_codegen_expr_type(lhs, function, info).ok();
            let rhs_type = infer_codegen_expr_type(rhs, function, info).ok();
            Ok(format!(
                "(({}) {} ({}))",
                render_expr_with_hint(lhs, function, info, rhs_type.as_ref(), deref_locals)?,
                operator,
                render_expr_with_hint(rhs, function, info, lhs_type.as_ref(), deref_locals)?
            ))
        }
    }
}

fn render_entrypoint(
    main_function: &Function,
    info: &ProgramInfo,
    install_debug_handlers: bool,
) -> Result<String, CompileError> {
    let main_symbol = info
        .function_symbols
        .get(&main_function.name)
        .cloned()
        .ok_or_else(|| CompileError::new("missing mangled symbol for main"))?;
    let mut output = String::new();
    output.push_str("int main(int argc, char *argv[]) {\n");
    output.push_str("    scar__argc = argc;\n");
    output.push_str("    scar__argv = argv;\n");
    if install_debug_handlers {
        output.push_str("    scar_runtime_install_signal_handlers();\n");
    }
    match main_function.return_type {
        Type::Void => {
            output.push_str(&format!("    {main_symbol}();\n"));
            output.push_str("    return 0;\n");
        }
        Type::Result(ref _ok_ty) => {
            output.push_str(&format!(
                "    {} __scar_main_result = {main_symbol}();\n",
                c_type(&main_function.return_type)
            ));
            output.push_str("    if (__scar_main_result.is_error) {\n");
            output.push_str("        scar_runtime_panic(__scar_main_result.error);\n");
            output.push_str("    }\n");
            output.push_str(&format!("    return (int)(__scar_main_result.ok);\n"));
        }
        _ => {
            output.push_str(&format!("    return (int)({main_symbol}());\n"));
        }
    }
    output.push_str("}\n");
    Ok(output)
}

fn render_symbol_name(name: &str, function: &Function, info: &ProgramInfo) -> String {
    if info.scope_overrides.borrow().contains_key(name)
        || info
            .locals
            .get(&function.name)
            .is_some_and(|locals| locals.contains_key(name))
        || function.params.iter().any(|param| param.name == name)
    {
        return mangle_local_symbol(name);
    }
    if let Some(symbol) = info.function_symbols.get(name) {
        return symbol.clone();
    }
    if info.globals.contains_key(name) {
        return format!("scar__glob__{}", name);
    }
    name.to_string()
}

fn mangle_local_symbol(name: &str) -> String {
    format!("loc__{name}")
}

fn function_allows_try_panic(function: &Function) -> bool {
    function.name == "main" || function.name.starts_with("__scar_test_case_")
}

fn next_codegen_temp_id() -> usize {
    static NEXT_TEMP_ID: AtomicUsize = AtomicUsize::new(0);
    NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed)
}

fn render_try_expr(
    inner: &Expr,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let result_ty = infer_codegen_expr_type(inner, function, info)?;
    let resolved_result_ty = resolve_codegen_aliases(&result_ty, info)?;
    let Type::Result(ok_ty) = resolved_result_ty else {
        return Err(CompileError::new(
            "`?` requires a result value during code generation",
        ));
    };
    let temp_id = next_codegen_temp_id();
    let temp_name = format!("__scar_try_expr_{temp_id}");
    let mut rendered = String::new();
    rendered.push_str("({ ");
    rendered.push_str(&c_type(&result_ty));
    rendered.push(' ');
    rendered.push_str(&temp_name);
    rendered.push_str(" = ");
    rendered.push_str(&render_expr(inner, function, info, deref_locals)?);
    rendered.push_str("; if (");
    rendered.push_str(&temp_name);
    rendered.push_str(".is_error) { ");
    if function_allows_try_panic(function) {
        rendered.push_str("scar_runtime_panic(");
        rendered.push_str(&temp_name);
        rendered.push_str(".error);");
    } else if let Type::Result(function_ok_ty) = &function.return_type {
        rendered.push_str("__scar_return_value = ");
        rendered.push_str(&render_result_error_value(
            function_ok_ty,
            &format!("{temp_name}.error"),
        ));
        rendered.push_str("; goto __scar_return;");
    } else {
        return Err(CompileError::new(
            "`?` propagation requires a result-returning function during code generation",
        ));
    }
    rendered.push_str(" } ");
    rendered.push_str(&temp_name);
    rendered.push_str(".ok; })");
    let _ = ok_ty;
    Ok(rendered)
}

fn render_field_access(
    base: &Expr,
    field: &str,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let base_ty = infer_codegen_expr_type(base, function, info)?;
    let rendered_base = render_expr(base, function, info, deref_locals)?;
    let base_is_deref_local =
        matches!(base, Expr::Path(path) if path.len() == 1 && deref_locals.contains(&path[0]));
    if is_reference_like(&base_ty) || base_is_deref_local {
        Ok(format!("({rendered_base})->{field}"))
    } else {
        Ok(format!("({rendered_base}).{field}"))
    }
}

fn render_index_expr(
    base: &Expr,
    index: &Expr,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let base_ty = infer_codegen_expr_type(base, function, info)?;
    match deref_refs(&base_ty) {
        Type::FixedArray(_, _) => Ok(format!(
            "({}[{}])",
            render_expr(base, function, info, deref_locals)?,
            render_expr(index, function, info, deref_locals)?
        )),
        _ => {
            let element_ty = list_element_type(&base_ty)?;
            let helper_prefix = list_helper_prefix(element_ty);
            Ok(format!(
                "(*{helper_prefix}_at({}, {}))",
                render_list_pointer(base, &base_ty, function, info)?,
                render_expr(index, function, info, deref_locals)?
            ))
        }
    }
}

fn render_call(
    callee: &Expr,
    args: &[Expr],
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    if let Expr::Path(path) = callee {
        if path.len() == 1 {
            let name = &path[0];
            let local_ty = info
                .scope_overrides
                .borrow()
                .get(name)
                .cloned()
                .or_else(|| {
                    info.locals
                        .get(&function.name)
                        .and_then(|locals| locals.get(name))
                        .cloned()
                })
                .or_else(|| {
                    function
                        .params
                        .iter()
                        .find(|p| p.name == *name)
                        .map(|p| p.ty.clone())
                });
            if let Some(Type::FnPtr(param_types, _)) = local_ty {
                let rendered_args = args
                    .iter()
                    .zip(param_types.iter())
                    .map(|(arg, param_ty)| {
                        render_expr_with_hint(arg, function, info, Some(param_ty), deref_locals)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mangled = mangle_local_symbol(name);
                return Ok(format!("{mangled}({})", rendered_args.join(", ")));
            }
        }
    }

    if let Some(path) = callee.callee_path() {
        let function_name = path.join(".");
        if let Some(signature) = info.functions.get(&function_name) {
            let rendered_args = args
                .iter()
                .zip(signature.params.iter())
                .map(|(arg, param_ty)| {
                    render_expr_with_hint(arg, function, info, Some(param_ty), deref_locals)
                })
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(symbol) = info.function_symbols.get(&function_name).cloned() {
                return Ok(format!("{symbol}({})", rendered_args.join(", ")));
            }
        }
        if path.len() == 1 {
            if let Some(type_info) = info.types.get(&function_name) {
                if type_info.kind != TypeDefKind::Struct {
                    return Err(CompileError::new(format!(
                        "union `{function_name}` cannot be constructed positionally"
                    )));
                }
                if type_info.alias.is_some() {
                    return Err(CompileError::new(format!(
                        "type `{}` is an alias and cannot be initialized like a struct",
                        function_name
                    )));
                }
                if type_info.fields.len() != args.len() {
                    return Err(CompileError::new(format!(
                        "type `{}` expects {} constructor arguments but received {}",
                        function_name,
                        type_info.fields.len(),
                        args.len()
                    )));
                }
                let rendered_args = args
                    .iter()
                    .zip(type_info.fields.iter())
                    .map(|(arg, field)| {
                        render_expr_with_hint(arg, function, info, Some(&field.ty), deref_locals)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(format!(
                    "({}){{ {} }}",
                    function_name,
                    rendered_args.join(", ")
                ));
            }
        }
        if path.len() == 2 {
            let union_name = &path[0];
            let variant_name = &path[1];
            if let Some(type_info) = info.types.get(union_name) {
                if type_info.kind == TypeDefKind::Union {
                    let payload_types =
                        type_info.variant_map.get(variant_name).ok_or_else(|| {
                            CompileError::new(format!(
                                "union `{union_name}` has no variant `{variant_name}`"
                            ))
                        })?;
                    let rendered_args = args
                        .iter()
                        .zip(payload_types.iter())
                        .map(|(arg, payload_ty)| {
                            render_expr_with_hint(
                                arg,
                                function,
                                info,
                                Some(payload_ty),
                                deref_locals,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let rendered_fields = rendered_args
                        .iter()
                        .enumerate()
                        .map(|(index, value)| {
                            format!(".{} = {}", union_payload_field(index), value)
                        })
                        .collect::<Vec<_>>();
                    return Ok(format!(
                        "(({}){{ .tag = {}, .data.{} = {{ {} }} }})",
                        union_name,
                        union_tag_symbol(union_name, variant_name),
                        variant_name,
                        rendered_fields.join(", ")
                    ));
                }
            }
        }
        return Err(CompileError::new(format!(
            "unknown function `{function_name}`"
        )));
    }

    Err(CompileError::new(
        "only direct function calls and @builtin calls are currently supported in codegen",
    ))
}

fn render_builtin_call(
    name: &str,
    args: &[Expr],
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    match name {
        "append" | "capacity" | "reserve" | "set" | "insert" | "remove" | "clear" | "len" => {
            if args.is_empty() {
                return Err(CompileError::new(format!(
                    "@{name} expects a list receiver as its first argument",
                )));
            }
            render_list_method_call(name, &args[0], &args[1..], function, info, deref_locals)
        }
        "puts" => Ok(format!(
            "puts({})",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "flush" => {
            if !args.is_empty() {
                return Err(CompileError::new("@flush expects no arguments"));
            }
            Ok("fflush(stdout)".to_string())
        }
        "print" => {
            let Expr::String(format) = &args[0] else {
                return Err(CompileError::new(
                    "@print requires a string literal as its first argument",
                ));
            };
            let flattened = flatten_print_args(&args[1..]);
            let arg_types = flattened
                .iter()
                .map(|arg| {
                    resolve_codegen_aliases(&infer_codegen_expr_type(arg, function, info)?, info)
                })
                .collect::<Result<Vec<_>, CompileError>>()?;
            let (converted, markers) = convert_format_string(format, &arg_types)?;
            let mut rendered_args = vec![format!("\"{}\"", escape_c_string(&converted))];
            for ((marker, expr), arg_ty) in markers
                .into_iter()
                .zip(flattened.into_iter())
                .zip(arg_types.into_iter())
            {
                let rendered = render_expr(expr, function, info, deref_locals)?;
                rendered_args.push(render_print_value(marker, &arg_ty, &rendered)?);
            }
            Ok(format!("printf({})", rendered_args.join(", ")))
        }
        "args" => {
            let list_name = c_type(&Type::List(Box::new(Type::Ref(Box::new(Type::U8)))));
            let helper_prefix = list_helper_prefix(&Type::Ref(Box::new(Type::U8)));
            Ok(format!(
                "({{ {list_name} __scar_args = {helper_prefix}_new(); {helper_prefix}_ensure_capacity(&__scar_args, scar__argc); memcpy(__scar_args.data, scar__argv, sizeof(const char *) * (size_t)scar__argc); __scar_args.len = scar__argc; __scar_args; }})"
            ))
        }
        "neg" => Ok(format!(
            "(-({}))",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "shl" => Ok(format!(
            "({} << {})",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "shr" => Ok(format!(
            "({} >> {})",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "memcpy" => Ok(format!(
            "memcpy((void *)({}), (void const *)({}), (size_t)({}))",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?,
            render_expr(&args[2], function, info, deref_locals)?
        )),
        "zeroed" => Ok("{0}".to_string()),
        "memset" => Ok(format!(
            "memset((void *)({}), (int)({}), (size_t)({}))",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?,
            render_expr(&args[2], function, info, deref_locals)?
        )),
        "addr" => {
            if let Expr::Path(path) = &args[0] {
                if path.len() == 1 && deref_locals.contains(&path[0]) {
                    return Ok(mangle_local_symbol(&path[0]));
                }
            }
            let rendered = render_expr(&args[0], function, info, deref_locals)?;
            if is_addressable_expr(&args[0]) {
                Ok(format!("(&{})", rendered))
            } else {
                let ty = infer_codegen_expr_type(&args[0], function, info)?;
                let c_ty = c_type(&ty);
                let temp_id = next_codegen_temp_id();
                Ok(format!(
                    "({{ {c_ty} *__scar_addr_{temp_id} = ({c_ty} *)scar_runtime_alloc(sizeof({c_ty})); *__scar_addr_{temp_id} = {rendered}; __scar_addr_{temp_id}; }})"
                ))
            }
        }
        "call" => {
            let fn_ptr = render_expr(&args[0], function, info, deref_locals)?;
            let rendered_args = args[1..]
                .iter()
                .map(|arg| render_expr(arg, function, info, deref_locals))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("({})({})", fn_ptr, rendered_args.join(", ")))
        }
        "as_mut" => {
            if args.len() != 1 {
                return Err(CompileError::new("@as_mut expects exactly one argument"));
            }
            let arg_ty = infer_codegen_expr_type(&args[0], function, info)?;
            Ok(format!(
                "(({})({}))",
                c_type(&as_mut_type(arg_ty)),
                render_expr(&args[0], function, info, deref_locals)?
            ))
        }
        "add" => Ok(format!(
            "(({}) + ({}))",
            render_pointer_arithmetic_base(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "alloc" => Ok(format!(
            "scar_runtime_alloc((size_t)({}))",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "realloc" => Ok(format!(
            "scar_runtime_realloc((void *)({}), (size_t)({}))",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "free" => Ok(format!(
            "scar_runtime_free((void *)({}))",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "deref" => Ok(format!(
            "(*({}))",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        _ => Err(CompileError::new(format!(
            "unsupported builtin intrinsic `@{name}` during code generation (known builtins: puts, print, flush, args, neg, shl, shr, memcpy, memset, zeroed, addr, deref, call, as_mut, add, alloc, realloc, free, len, append, capacity, reserve, set, insert, remove, clear)"
        ))),
    }
}

fn render_list_method_call(
    method: &str,
    receiver: &Expr,
    args: &[Expr],
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let receiver_ty = infer_codegen_expr_type(receiver, function, info)?;
    let element_ty = list_element_type(&receiver_ty)?;
    let helper_prefix = list_helper_prefix(element_ty);
    let receiver_ptr = render_list_pointer(receiver, &receiver_ty, function, info)?;

    match method {
        "append" => Ok(format!(
            "{helper_prefix}_append({receiver_ptr}, {})",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "capacity" => Ok(format!("{helper_prefix}_capacity({receiver_ptr})")),
        "len" => Ok(format!("{helper_prefix}_len({receiver_ptr})")),
        "reserve" => Ok(format!(
            "{helper_prefix}_reserve({receiver_ptr}, {})",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "set" => Ok(format!(
            "{helper_prefix}_set({receiver_ptr}, {}, {})",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "insert" => Ok(format!(
            "{helper_prefix}_insert({receiver_ptr}, {}, {})",
            render_expr(&args[0], function, info, deref_locals)?,
            render_expr(&args[1], function, info, deref_locals)?
        )),
        "remove" => Ok(format!(
            "{helper_prefix}_remove({receiver_ptr}, {})",
            render_expr(&args[0], function, info, deref_locals)?
        )),
        "clear" => Ok(format!("{helper_prefix}_clear({receiver_ptr})")),
        _ => Err(CompileError::new(format!(
            "unsupported list accessor `@{method}` during code generation"
        ))),
    }
}

fn render_list_pointer(
    receiver: &Expr,
    receiver_ty: &Type,
    function: &Function,
    info: &ProgramInfo,
) -> Result<String, CompileError> {
    let rendered = render_expr(receiver, function, info, &HashSet::new())?;
    match deref_refs(receiver_ty) {
        Type::List(_) => {
            if matches!(receiver_ty, Type::Ref(inner) if matches!(inner.as_ref(), Type::List(_))) {
                Ok(format!("({rendered})"))
            } else {
                Ok(format!("&({rendered})"))
            }
        }
        other => Err(CompileError::new(format!(
            "expected list receiver during code generation, got {}",
            describe_type(other)
        ))),
    }
}

fn render_global_base_type(ty: &Type) -> String {
    match ty {
        Type::FixedArray(_, inner) => render_global_base_type(inner),
        _ => c_type(ty),
    }
}

fn render_global_dims(ty: &Type) -> String {
    match ty {
        Type::FixedArray(n, inner) => format!("[{}]", n) + &render_global_dims(inner),
        _ => String::new(),
    }
}

fn render_global_init(
    expr: &Expr,
    expected_ty: &Type,
    function: &Function,
    info: &ProgramInfo,
) -> Result<String, CompileError> {
    match (expr, expected_ty) {
        (Expr::ListLiteral(values), Type::FixedArray(_, element_ty)) => {
            let rendered_values = values
                .iter()
                .map(|value| render_global_init(value, element_ty, function, info))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("{{ {} }}", rendered_values.join(", ")))
        }
        _ => render_expr(expr, function, info, &HashSet::new()),
    }
}

fn render_list_literal(
    values: &[Expr],
    ty: &Type,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let element_ty = list_element_type(ty)?;
    let helper_prefix = list_helper_prefix(element_ty);
    if values.is_empty() {
        return Ok(format!("{helper_prefix}_new()"));
    }
    let rendered_values = values
        .iter()
        .map(|value| render_expr(value, function, info, deref_locals))
        .collect::<Result<Vec<_>, _>>()?;
    let mut code = format!("({helper_prefix}_new()");
    for rv in &rendered_values {
        code.push_str(&format!(", ({helper_prefix}_append(&__l, {}), __l)", rv));
    }
    code.push(')');
    Ok(format!(
        "({{\n    {0} __l = {1}_new();\n    __l = {2};\n    __l;\n}})",
        c_type(ty),
        helper_prefix,
        code
    ))
}

pub(crate) fn infer_codegen_expr_type(
    expr: &Expr,
    function: &Function,
    info: &ProgramInfo,
) -> Result<Type, CompileError> {
    match expr {
        Expr::Int(_) => Ok(Type::I32),
        Expr::Bool(_) => Ok(Type::Bool),
        Expr::Float(_) => Ok(Type::F32),
        Expr::String(_) => Ok(Type::Ref(Box::new(Type::U8))),
        Expr::None => Ok(Type::None),
        Expr::ListLiteral(values) => {
            if values.is_empty() {
                return Err(CompileError::new(
                    "cannot infer the element type of an empty list literal during code generation",
                ));
            }
            let first_ty = infer_codegen_expr_type(&values[0], function, info)?;
            for value in &values[1..] {
                let ty = infer_codegen_expr_type(value, function, info)?;
                if ty != first_ty {
                    return Err(CompileError::new(format!(
                        "list literal contains mixed element types {} and {} during code generation",
                        describe_type(&first_ty),
                        describe_type(&ty)
                    )));
                }
            }
            Ok(Type::List(Box::new(first_ty)))
        }
        Expr::Index { base, .. } => {
            infer_index_type(&infer_codegen_expr_type(base, function, info)?)
        }
        Expr::Path(path) => match path.as_slice() {
            [name] => info
                .scope_overrides
                .borrow()
                .get(name)
                .cloned()
                .or_else(|| {
                    info.locals
                        .get(&function.name)
                        .and_then(|locals| locals.get(name))
                        .cloned()
                })
                .or_else(|| {
                    function
                        .params
                        .iter()
                        .find(|param| param.name == *name)
                        .map(|param| param.ty.clone())
                })
                .or_else(|| {
                    info.functions.get(name).map(|sig| {
                        Type::FnPtr(sig.params.clone(), Box::new(sig.return_type.clone()))
                    })
                })
                .or_else(|| info.globals.get(name).map(|(ty, _)| ty.clone()))
                .ok_or_else(|| {
                    CompileError::new(format!("unknown expression `{name}` in code generation"))
                }),
            [type_name, variant_name] => {
                if let Some(type_info) = info.types.get(type_name) {
                    if type_info.kind == TypeDefKind::Enum
                        && type_info.variant_map.contains_key(variant_name)
                    {
                        return Ok(Type::Named(type_name.clone()));
                    }
                }
                Err(CompileError::new(format!(
                    "unsupported qualified expression `{}` in code generation",
                    path.join(".")
                )))
            }
            _ => Err(CompileError::new(format!(
                "unsupported qualified expression `{}` in code generation",
                path.join(".")
            ))),
        },
        Expr::FieldAccess { base, field } => {
            let base_ty = infer_codegen_expr_type(base, function, info)?;
            match deref_refs(&base_ty) {
                Type::Named(name) => info
                    .types
                    .get(name)
                    .and_then(|type_info| type_info.field_map.get(field))
                    .cloned()
                    .ok_or_else(|| {
                        CompileError::new(format!("type `{name}` has no field `{field}`"))
                    }),
                other => Err(CompileError::new(format!(
                    "field access requires a named type during code generation, got {}",
                    describe_type(other)
                ))),
            }
        }
        Expr::StructInit { name, .. } => Ok(Type::Named(name.clone())),
        Expr::Char(_) => Ok(Type::U8),
        Expr::BuiltinCall { name, args } => infer_builtin_type(name, args, function, info),
        Expr::MethodCall {
            receiver,
            method,
            args: _,
        } => {
            let receiver_ty = infer_codegen_expr_type(receiver, function, info)?;
            let element_ty = list_element_type(&receiver_ty)?;
            match method.as_str() {
                "capacity" => Ok(Type::I32),
                "len" => Ok(Type::Usize),
                "remove" => Ok(element_ty.clone()),
                "append" | "reserve" | "set" | "insert" | "clear" => Ok(Type::Void),
                _ => Err(CompileError::new(format!(
                    "unsupported list accessor `@{method}` during code generation"
                ))),
            }
        }
        Expr::Call { callee, .. } => {
            if let Expr::Path(path) = callee.as_ref() {
                if path.len() == 1 {
                    let name = &path[0];
                    let local_ty = info
                        .locals
                        .get(&function.name)
                        .and_then(|locals| locals.get(name))
                        .cloned()
                        .or_else(|| {
                            function
                                .params
                                .iter()
                                .find(|p| p.name == *name)
                                .map(|p| p.ty.clone())
                        });
                    if let Some(Type::FnPtr(_, ret_type)) = local_ty {
                        return Ok(*ret_type);
                    }
                }
            }

            let Some(path) = callee.callee_path() else {
                return Err(CompileError::new(
                    "only direct calls are supported during code generation",
                ));
            };
            let function_name = path.join(".");
            if let Some(signature) = info.functions.get(&function_name) {
                return Ok(signature.return_type.clone());
            }
            match path.as_slice() {
                [name] => {
                    if info.types.contains_key(name) {
                        Ok(Type::Named(name.clone()))
                    } else {
                        Err(CompileError::new(format!("unknown function `{name}`")))
                    }
                }
                [union_name, variant_name] => {
                    if let Some(type_info) = info.types.get(union_name)
                        && type_info.kind == TypeDefKind::Union
                        && type_info.variant_map.contains_key(variant_name)
                    {
                        Ok(Type::Named(union_name.clone()))
                    } else {
                        Err(CompileError::new(format!(
                            "unsupported call target `{}` in code generation; expected a resolved function or union variant constructor",
                            function_name
                        )))
                    }
                }
                _ => Err(CompileError::new(format!(
                    "unsupported call target `{}` in code generation; expected a resolved function or union variant constructor",
                    function_name
                ))),
            }
        }
        Expr::Specialize { .. } => Err(CompileError::new(
            "generic specialization must be resolved before code generation",
        )),
        Expr::Cast { ty, .. } => Ok(ty.clone()),
        Expr::SizeOf(_) => Ok(Type::Usize),
        Expr::BitCast { ty, .. } => Ok(ty.clone()),
        Expr::Error { .. } => Ok(Type::Error),
        Expr::Try(inner) => {
            let inner_ty =
                resolve_codegen_aliases(&infer_codegen_expr_type(inner, function, info)?, info)?;
            let Type::Result(ok_ty) = inner_ty else {
                return Err(CompileError::new(format!(
                    "`?` requires a `T|error` expression, got {}",
                    describe_type(&inner_ty)
                )));
            };
            Ok((*ok_ty).clone())
        }
        Expr::Unary { op, expr } => match op {
            UnaryOp::Neg | UnaryOp::LogicalNot | UnaryOp::BitNot => {
                infer_codegen_integer_unary_type(*op, expr, function, info)
            }
            UnaryOp::PostfixInc | UnaryOp::PostfixDec => {
                infer_codegen_expr_type(expr, function, info)
            }
        },
        Expr::Pack(_) => Err(CompileError::new(
            "packed `{...}` expressions are only valid inside @print",
        )),
        Expr::Binary { lhs, op, rhs } => {
            let lhs_ty =
                resolve_codegen_aliases(&infer_codegen_expr_type(lhs, function, info)?, info)?;
            let rhs_ty =
                resolve_codegen_aliases(&infer_codegen_expr_type(rhs, function, info)?, info)?;
            match op {
                BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Divide | BinaryOp::Multiply
                    if common_codegen_numeric_type(&lhs_ty, &rhs_ty).is_some() =>
                {
                    Ok(common_codegen_numeric_type(&lhs_ty, &rhs_ty).unwrap())
                }
                BinaryOp::Modulo if common_codegen_integer_type(&lhs_ty, &rhs_ty).is_some() => {
                    Ok(common_codegen_integer_type(&lhs_ty, &rhs_ty).unwrap())
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
                    if is_codegen_condition_type(&lhs_ty) && is_codegen_condition_type(&rhs_ty) =>
                {
                    Ok(Type::Bool)
                }
                BinaryOp::LogicalAnd | BinaryOp::LogicalOr => Err(CompileError::new(
                    "logical operators currently require bool or integer operands",
                )),
                BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor
                    if common_codegen_integer_type(&lhs_ty, &rhs_ty).is_some() =>
                {
                    Ok(common_codegen_integer_type(&lhs_ty, &rhs_ty).unwrap())
                }
                BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => Err(CompileError::new(
                    "bitwise operators currently require compatible integer operands",
                )),
                BinaryOp::ShiftLeft | BinaryOp::ShiftRight
                    if is_codegen_integer_type(&lhs_ty) && is_codegen_integer_type(&rhs_ty) =>
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
                    if common_codegen_numeric_type(&lhs_ty, &rhs_ty).is_some()
                        || (lhs_ty == Type::Bool && rhs_ty == Type::Bool)
                        || can_codegen_compare_with_none(&lhs_ty, &rhs_ty)
                        || same_codegen_enum_type(&lhs_ty, &rhs_ty, info) =>
                {
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

fn render_logical_shift_right(
    lhs: &Expr,
    rhs: &Expr,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let lhs_ty = resolve_codegen_aliases(&infer_codegen_expr_type(lhs, function, info)?, info)?;
    let rendered_lhs = render_expr(lhs, function, info, deref_locals)?;
    let rendered_rhs = render_expr(rhs, function, info, deref_locals)?;
    match lhs_ty {
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize => {
            let signed = c_type(&lhs_ty);
            let unsigned = unsigned_c_type(&lhs_ty).ok_or_else(|| {
                CompileError::new(format!(
                    "logical shift-right requires an integer operand during code generation, got {}",
                    describe_type(&lhs_ty)
                ))
            })?;
            Ok(format!(
                "(({})(({})({rendered_lhs}) >> ({rendered_rhs})))",
                signed, unsigned
            ))
        }
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize => Ok(format!(
            "(({})({rendered_lhs}) >> ({rendered_rhs}))",
            c_type(&lhs_ty)
        )),
        other => Err(CompileError::new(format!(
            "logical shift-right requires an integer operand during code generation, got {}",
            describe_type(&other)
        ))),
    }
}

fn infer_codegen_integer_unary_type(
    op: UnaryOp,
    expr: &Expr,
    function: &Function,
    info: &ProgramInfo,
) -> Result<Type, CompileError> {
    let inner_ty = resolve_codegen_aliases(&infer_codegen_expr_type(expr, function, info)?, info)?;
    match op {
        UnaryOp::Neg if is_codegen_signed_numeric_type(&inner_ty) => Ok(inner_ty),
        UnaryOp::Neg => Err(CompileError::new(
            "unary `-` currently requires a signed numeric operand",
        )),
        UnaryOp::LogicalNot if is_codegen_condition_type(&inner_ty) => Ok(Type::Bool),
        UnaryOp::LogicalNot => Err(CompileError::new(
            "unary `!` currently requires a bool or integer operand",
        )),
        UnaryOp::BitNot if is_codegen_integer_type(&inner_ty) => Ok(inner_ty),
        UnaryOp::BitNot => Err(CompileError::new(
            "unary `~` currently requires an integer operand",
        )),
        UnaryOp::PostfixInc | UnaryOp::PostfixDec if is_codegen_signed_numeric_type(&inner_ty) => {
            Ok(inner_ty)
        }
        UnaryOp::PostfixInc | UnaryOp::PostfixDec => Err(CompileError::new(
            "postfix increment/decrement requires a numeric operand",
        )),
    }
}

fn is_addressable_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) => true,
        Expr::FieldAccess { base, .. } => is_addressable_expr(base),
        Expr::Index { base, .. } => is_addressable_expr(base),
        Expr::BuiltinCall { name, .. } if name == "deref" => true,
        _ => false,
    }
}

fn as_mut_type(ty: Type) -> Type {
    match ty {
        Type::Mut(_) => ty,
        other => Type::Mut(Box::new(other)),
    }
}

fn infer_builtin_type(
    name: &str,
    args: &[Expr],
    function: &Function,
    info: &ProgramInfo,
) -> Result<Type, CompileError> {
    match name {
        "append" | "capacity" | "reserve" | "set" | "insert" | "remove" | "clear" | "len" => {
            if args.is_empty() {
                return Err(CompileError::new(format!(
                    "@{name} expects a list receiver as its first argument",
                )));
            }
            let receiver_ty = infer_codegen_expr_type(&args[0], function, info)?;
            let element_ty = list_element_type(&receiver_ty)?;
            match name {
                "len" => Ok(Type::Usize),
                "capacity" => Ok(Type::I32),
                "remove" => Ok(element_ty.clone()),
                _ => Ok(Type::Void),
            }
        }
        "puts" | "print" | "flush" | "free" | "memcpy" | "memset" | "zeroed" => Ok(Type::Void),
        "args" => Ok(Type::List(Box::new(Type::Ref(Box::new(Type::U8))))),
        "neg" => infer_codegen_expr_type(&args[0], function, info),
        "shl" | "shr" => infer_codegen_expr_type(&args[0], function, info),
        "add" => Ok(pointer_arithmetic_type(&infer_codegen_expr_type(
            &args[0], function, info,
        )?)),
        "alloc" | "realloc" => Ok(Type::Mut(Box::new(Type::Ref(Box::new(Type::U8))))),
        "addr" => Ok(Type::Ref(Box::new(infer_codegen_expr_type(
            &args[0], function, info,
        )?))),
        "call" => {
            let fn_ty =
                resolve_codegen_aliases(&infer_codegen_expr_type(&args[0], function, info)?, info)?;
            match fn_ty {
                Type::FnPtr(_, ret) => Ok(*ret),
                other => Err(CompileError::new(format!(
                    "@call expects a function pointer, got {}",
                    describe_type(&other)
                ))),
            }
        }
        "as_mut" => {
            if args.len() != 1 {
                return Err(CompileError::new("@as_mut expects exactly one argument"));
            }
            Ok(as_mut_type(infer_codegen_expr_type(
                &args[0], function, info,
            )?))
        }
        "deref" => match infer_codegen_expr_type(&args[0], function, info)? {
            Type::Ref(inner) => Ok(*inner),
            Type::Mut(inner) => match *inner {
                Type::Ref(inner) => Ok(*inner),
                other => Err(CompileError::new(format!(
                    "@deref requires a ref(...) argument during code generation, got {}",
                    describe_type(&other)
                ))),
            },
            other => Err(CompileError::new(format!(
                "@deref requires a ref(...) argument during code generation, got {}",
                describe_type(&other)
            ))),
        },
        _ => Err(CompileError::new(format!(
            "unsupported builtin intrinsic `@{name}` during type inference in code generation (known builtins: puts, print, flush, free, memcpy, memset, zeroed, args, neg, shl, shr, add, alloc, realloc, addr, call, as_mut, deref, len, append, capacity, reserve, set, insert, remove, clear)"
        ))),
    }
}

fn flatten_print_args(args: &[Expr]) -> Vec<&Expr> {
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
    Pointer,
    String,
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

fn convert_format_string(
    input: &str,
    arg_types: &[Type],
) -> Result<(String, Vec<PrintMarker>), CompileError> {
    let mut output = String::new();
    let mut markers = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let mut index = 0;
    let mut arg_index = 0;
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
            let marker: String = chars[start..end].iter().collect();
            let parsed = match marker.as_str() {
                "d" | "ld" | "lld" => PrintMarker::Int,
                "u" | "lu" | "llu" => PrintMarker::Uint,
                "b" => PrintMarker::Bool,
                "p" => PrintMarker::Pointer,
                "s" => PrintMarker::String,
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
            let arg_ty = arg_types.get(arg_index).ok_or_else(|| {
                CompileError::new("@print format expects more values than were provided")
            })?;
            let width_prefix: String = marker.chars().take_while(|c| c.is_ascii_digit()).collect();
            let base_specifier = print_format_specifier(parsed, arg_ty)?;
            let specifier = if width_prefix.is_empty() {
                base_specifier.to_string()
            } else {
                format!("%{}{}", width_prefix, &base_specifier[1..])
            };
            output.push_str(&specifier);
            markers.push(parsed);
            arg_index += 1;
            index = end + 1;
            continue;
        }
        output.push(chars[index]);
        index += 1;
    }
    Ok((output, markers))
}

fn collect_inline_type_deps(ty: &Type, names: &mut HashSet<String>) {
    match ty {
        Type::Ref(_) | Type::Mut(_) | Type::List(_) => {}
        Type::Result(inner) => collect_inline_type_deps(inner, names),
        Type::Named(name) => {
            names.insert(name.clone());
        }
        Type::Applied(name, args) => {
            names.insert(name.clone());
            for arg in args {
                collect_inline_type_deps(arg, names);
            }
        }
        _ => {}
    }
}

fn sort_type_defs_by_deps(type_defs: &mut Vec<TypeDef>) {
    let all_names: HashSet<String> = type_defs.iter().map(|td| td.name.clone()).collect();

    let mut deps: Vec<(usize, Vec<String>)> = Vec::new();
    for (i, td) in type_defs.iter().enumerate() {
        let mut dep_names = HashSet::new();
        for field in &td.fields {
            collect_inline_type_deps(&field.ty, &mut dep_names);
        }
        for variant in &td.variants {
            for payload in &variant.payload_types {
                collect_inline_type_deps(payload, &mut dep_names);
            }
        }
        let filtered: Vec<String> = dep_names
            .into_iter()
            .filter(|name| all_names.contains(name) && name != &td.name)
            .collect();
        deps.push((i, filtered));
    }

    let mut sorted_indices = Vec::new();
    let mut visited = HashSet::new();
    let mut in_stack = HashSet::new();

    fn visit(
        i: usize,
        deps: &[(usize, Vec<String>)],
        type_defs: &[TypeDef],
        all_names: &HashSet<String>,
        visited: &mut HashSet<usize>,
        in_stack: &mut HashSet<usize>,
        sorted: &mut Vec<usize>,
    ) {
        if !visited.insert(i) {
            return;
        }
        in_stack.insert(i);
        if let Some((_, dep_list)) = deps.get(i) {
            for dep_name in dep_list {
                if let Some(dep_idx) = type_defs.iter().position(|td| td.name == *dep_name) {
                    if in_stack.contains(&dep_idx) {
                        continue;
                    }
                    visit(
                        dep_idx, deps, type_defs, all_names, visited, in_stack, sorted,
                    );
                }
            }
        }
        in_stack.remove(&i);
        sorted.push(i);
    }

    for (i, _) in deps.iter().enumerate() {
        if !visited.contains(&i) {
            visit(
                i,
                &deps,
                type_defs,
                &all_names,
                &mut visited,
                &mut in_stack,
                &mut sorted_indices,
            );
        }
    }

    let mut sorted: Vec<TypeDef> = sorted_indices
        .iter()
        .map(|&i| type_defs[i].clone())
        .collect();
    sorted.extend(
        type_defs
            .iter()
            .enumerate()
            .filter(|(i, _)| !sorted_indices.contains(i))
            .map(|(_, td)| td.clone()),
    );
    *type_defs = sorted;
}

fn collect_list_types(program: &Program, info: &ProgramInfo) -> Vec<Type> {
    let mut set = HashSet::new();
    for type_def in &program.type_defs {
        if let Some(alias) = &type_def.alias {
            collect_list_types_from_type(alias, &mut set);
        }
        for field in &type_def.fields {
            collect_list_types_from_type(&field.ty, &mut set);
        }
        for variant in &type_def.variants {
            for payload_ty in &variant.payload_types {
                collect_list_types_from_type(payload_ty, &mut set);
            }
        }
    }
    for function in &program.functions {
        collect_list_types_from_type(&function.return_type, &mut set);
        for param in &function.params {
            collect_list_types_from_type(&param.ty, &mut set);
        }
    }
    for locals in info.locals.values() {
        for ty in locals.values() {
            collect_list_types_from_type(ty, &mut set);
        }
    }

    let mut list_types: Vec<_> = set.into_iter().collect();
    list_types.sort_by_key(describe_type);
    list_types
}

fn collect_result_types(program: &Program, info: &ProgramInfo) -> Vec<Type> {
    let mut set = HashSet::new();
    for type_def in &program.type_defs {
        if let Some(alias) = &type_def.alias {
            collect_result_types_from_type(alias, &mut set);
        }
        for field in &type_def.fields {
            collect_result_types_from_type(&field.ty, &mut set);
        }
        for variant in &type_def.variants {
            for payload_ty in &variant.payload_types {
                collect_result_types_from_type(payload_ty, &mut set);
            }
        }
    }
    for function in &program.functions {
        collect_result_types_from_type(&function.return_type, &mut set);
        for param in &function.params {
            collect_result_types_from_type(&param.ty, &mut set);
        }
    }
    for locals in info.locals.values() {
        for ty in locals.values() {
            collect_result_types_from_type(ty, &mut set);
        }
    }
    let mut result_types: Vec<_> = set.into_iter().collect();
    result_types.sort_by_key(describe_type);
    result_types
}

fn collect_result_types_from_type(ty: &Type, set: &mut HashSet<Type>) {
    match ty {
        Type::Result(inner) => {
            collect_result_types_from_type(inner, set);
            set.insert((**inner).clone());
        }
        Type::List(inner) => collect_result_types_from_type(inner, set),
        Type::Mut(inner) => collect_result_types_from_type(inner, set),
        Type::Ref(inner) => collect_result_types_from_type(inner, set),
        Type::FnPtr(params, ret) => {
            for p in params {
                collect_result_types_from_type(p, set);
            }
            collect_result_types_from_type(ret, set);
        }
        _ => {}
    }
}

fn collect_list_types_from_type(ty: &Type, set: &mut HashSet<Type>) {
    match ty {
        Type::List(inner) => {
            collect_list_types_from_type(inner, set);
            set.insert(ty.clone());
        }
        Type::Result(inner) => collect_list_types_from_type(inner, set),
        Type::Mut(inner) => collect_list_types_from_type(inner, set),
        Type::Ref(inner) => collect_list_types_from_type(inner, set),
        Type::FnPtr(params, ret) => {
            for p in params {
                collect_list_types_from_type(p, set);
            }
            collect_list_types_from_type(ret, set);
        }
        _ => {}
    }
}

fn render_list_typedef(list_ty: &Type) -> Result<String, CompileError> {
    let element_ty = list_element_type(list_ty)?;
    let list_name = c_type(list_ty);
    let element_c_ty = c_type(element_ty);
    let mut output = String::new();
    output.push_str("typedef struct {\n");
    output.push_str("    ");
    output.push_str(&element_c_ty);
    output.push_str(" *data;\n");
    output.push_str("    int32_t len;\n");
    output.push_str("    int32_t cap;\n");
    output.push_str("} ");
    output.push_str(&list_name);
    output.push_str(";\n");
    Ok(output)
}

fn render_list_helpers(list_ty: &Type) -> Result<String, CompileError> {
    let element_ty = list_element_type(list_ty)?;
    let list_name = c_type(list_ty);
    let element_c_ty = c_type(element_ty);
    let helper_prefix = list_helper_prefix(element_ty);
    let mut output = String::new();

    output.push_str("static ");
    output.push_str(&list_name);
    output.push(' ');
    output.push_str(&helper_prefix);
    output.push_str("_new(void) {\n");
    output.push_str("    return (");
    output.push_str(&list_name);
    output.push_str("){ .data = NULL, .len = 0, .cap = 0 };\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_ensure_capacity(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t requested) {\n");
    output.push_str("    if (requested < 0) {\n");
    output.push_str("        scar_runtime_panic(\"list capacity cannot be negative\");\n");
    output.push_str("    }\n");
    output.push_str("    if (requested <= list->cap) {\n");
    output.push_str("        return;\n");
    output.push_str("    }\n");
    output.push_str("    int32_t new_cap = list->cap > 0 ? list->cap : 4;\n");
    output.push_str("    while (new_cap < requested) {\n");
    output.push_str("        if (new_cap > INT32_MAX / 2) {\n");
    output.push_str("            new_cap = requested;\n");
    output.push_str("            break;\n");
    output.push_str("        }\n");
    output.push_str("        new_cap *= 2;\n");
    output.push_str("    }\n");
    output.push_str("    void *resized = realloc(list->data, sizeof(");
    output.push_str(&element_c_ty);
    output.push_str(") * (size_t)new_cap);\n");
    output.push_str("    if (resized == NULL) {\n");
    output.push_str("        scar_runtime_panic(\"failed to allocate list storage\");\n");
    output.push_str("    }\n");
    output.push_str("    list->data = (");
    output.push_str(&element_c_ty);
    output.push_str(" *)resized;\n");
    output.push_str("    list->cap = new_cap;\n");
    output.push_str("}\n\n");

    output.push_str("static ");
    output.push_str(&list_name);
    output.push(' ');
    output.push_str(&helper_prefix);
    output.push_str("_from_array(");
    output.push_str(&element_c_ty);
    output.push_str(" const *items, int32_t len) {\n");
    output.push_str("    ");
    output.push_str(&list_name);
    output.push_str(" list = ");
    output.push_str(&helper_prefix);
    output.push_str("_new();\n");
    output.push_str("    if (len == 0) {\n");
    output.push_str("        return list;\n");
    output.push_str("    }\n");
    output.push_str("    ");
    output.push_str(&helper_prefix);
    output.push_str("_ensure_capacity(&list, len);\n");
    output.push_str("    memcpy(list.data, items, sizeof(");
    output.push_str(&element_c_ty);
    output.push_str(") * (size_t)len);\n");
    output.push_str("    list.len = len;\n");
    output.push_str("    return list;\n");
    output.push_str("}\n\n");

    output.push_str("static ");
    output.push_str(&element_c_ty);
    output.push_str(" *");
    output.push_str(&helper_prefix);
    output.push_str("_at(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t index) {\n");
    output.push_str("    if (index < 0 || index >= list->len) {\n");
    output.push_str("        fprintf(stderr, \"scar: panic: list index out of bounds (index %d, len %d)\\n\", index, list->len);\n");
    output.push_str("        exit(1);\n");
    output.push_str("    }\n");
    output.push_str("    return &list->data[index];\n");
    output.push_str("}\n\n");

    output.push_str("static int32_t ");
    output.push_str(&helper_prefix);
    output.push_str("_capacity(");
    output.push_str(&list_name);
    output.push_str(" *list) {\n");
    output.push_str("    return list->cap;\n");
    output.push_str("}\n\n");

    output.push_str("static uintptr_t ");
    output.push_str(&helper_prefix);
    output.push_str("_len(");
    output.push_str(&list_name);
    output.push_str(" *list) {\n");
    output.push_str("    return (uintptr_t)list->len;\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_reserve(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t capacity) {\n");
    output.push_str("    ");
    output.push_str(&helper_prefix);
    output.push_str("_ensure_capacity(list, capacity);\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_append(");
    output.push_str(&list_name);
    output.push_str(" *list, ");
    output.push_str(&element_c_ty);
    output.push_str(" value) {\n");
    output.push_str("    ");
    output.push_str(&helper_prefix);
    output.push_str("_ensure_capacity(list, list->len + 1);\n");
    output.push_str("    list->data[list->len++] = value;\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_set(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t index, ");
    output.push_str(&element_c_ty);
    output.push_str(" value) {\n");
    output.push_str("    *");
    output.push_str(&helper_prefix);
    output.push_str("_at(list, index) = value;\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_insert(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t index, ");
    output.push_str(&element_c_ty);
    output.push_str(" value) {\n");
    output.push_str("    if (index < 0 || index > list->len) {\n");
    output.push_str("        fprintf(stderr, \"scar: panic: list insert index out of bounds (index %d, len %d)\\n\", index, list->len);\n");
    output.push_str("        exit(1);\n");
    output.push_str("    }\n");
    output.push_str("    ");
    output.push_str(&helper_prefix);
    output.push_str("_ensure_capacity(list, list->len + 1);\n");
    output.push_str("    if (index < list->len) {\n");
    output.push_str("        memmove(&list->data[index + 1], &list->data[index], sizeof(");
    output.push_str(&element_c_ty);
    output.push_str(") * (size_t)(list->len - index));\n");
    output.push_str("    }\n");
    output.push_str("    list->data[index] = value;\n");
    output.push_str("    list->len += 1;\n");
    output.push_str("}\n\n");

    output.push_str("static ");
    output.push_str(&element_c_ty);
    output.push(' ');
    output.push_str(&helper_prefix);
    output.push_str("_remove(");
    output.push_str(&list_name);
    output.push_str(" *list, int32_t index) {\n");
    output.push_str("    ");
    output.push_str(&element_c_ty);
    output.push_str(" removed = *");
    output.push_str(&helper_prefix);
    output.push_str("_at(list, index);\n");
    output.push_str("    if (index + 1 < list->len) {\n");
    output.push_str("        memmove(&list->data[index], &list->data[index + 1], sizeof(");
    output.push_str(&element_c_ty);
    output.push_str(") * (size_t)(list->len - index - 1));\n");
    output.push_str("    }\n");
    output.push_str("    list->len -= 1;\n");
    output.push_str("    return removed;\n");
    output.push_str("}\n\n");

    output.push_str("static void ");
    output.push_str(&helper_prefix);
    output.push_str("_clear(");
    output.push_str(&list_name);
    output.push_str(" *list) {\n");
    output.push_str("    list->len = 0;\n");
    output.push_str("}\n");

    Ok(output)
}

fn list_helper_prefix(element_ty: &Type) -> String {
    format!("scar_list__{}", type_suffix(element_ty))
}

fn type_suffix(ty: &Type) -> String {
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
        Type::Infer => "infer".to_string(),
        Type::Named(name) => sanitize_identifier(name),
        Type::Applied(name, type_args) => format!(
            "{}__{}",
            sanitize_identifier(name),
            type_args
                .iter()
                .map(type_suffix)
                .collect::<Vec<_>>()
                .join("__")
        ),
        Type::Mut(inner) => format!("mut__{}", type_suffix(inner)),
        Type::Ref(inner) => format!("ref__{}", type_suffix(inner)),
        Type::List(inner) => format!("list__{}", type_suffix(inner)),
        Type::FixedArray(n, inner) => format!("arr{n}__{}", type_suffix(inner)),
        Type::Result(inner) => format!("result__{}", type_suffix(inner)),
        Type::Error => "error".to_string(),
        Type::None => "none".to_string(),
        Type::FnPtr(params, ret) => format!(
            "fn__{}__{}",
            params
                .iter()
                .map(type_suffix)
                .collect::<Vec<_>>()
                .join("__"),
            type_suffix(ret)
        ),
    }
}

fn sanitize_identifier(name: &str) -> String {
    name.chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect()
}

fn c_type(ty: &Type) -> String {
    match ty {
        Type::Void => "void".to_string(),
        Type::Bool => "int32_t".to_string(),
        Type::I8 => "int8_t".to_string(),
        Type::I16 => "int16_t".to_string(),
        Type::I32 => "int32_t".to_string(),
        Type::I64 => "int64_t".to_string(),
        Type::Isize => "intptr_t".to_string(),
        Type::U16 => "uint16_t".to_string(),
        Type::U32 => "uint32_t".to_string(),
        Type::U64 => "uint64_t".to_string(),
        Type::Usize => "uintptr_t".to_string(),
        Type::U8 => "uint8_t".to_string(),
        Type::F32 => "float".to_string(),
        Type::F64 => "double".to_string(),
        Type::Infer => "void".to_string(),
        Type::Named(name) => name.clone(),
        Type::Applied(name, _) => name.clone(),
        Type::Mut(inner) => c_type_mut(inner),
        Type::Ref(inner) => {
            let inner = c_type(inner);
            if inner.ends_with('*') {
                format!("{inner}*")
            } else {
                format!("{inner} *")
            }
        }
        Type::List(inner) => format!("scar_list__{}", type_suffix(inner)),
        Type::FixedArray(_, inner) => {
            // In expression context (casts, etc.) treat as pointer to element
            let inner_c = c_type(inner);
            if inner_c.ends_with('*') {
                format!("{inner_c}*")
            } else {
                format!("{inner_c} *")
            }
        }
        Type::Result(inner) => result_c_type(inner),
        Type::Error => "const char *".to_string(),
        Type::None => "void *".to_string(),
        Type::FnPtr(params, ret) => {
            let ret_c = c_type(ret);
            let params_c = if params.is_empty() {
                "void".to_string()
            } else {
                params.iter().map(c_type).collect::<Vec<_>>().join(", ")
            };
            format!("{ret_c} (*)({params_c})")
        }
    }
}

pub(crate) fn list_element_type(ty: &Type) -> Result<&Type, CompileError> {
    match deref_refs(ty) {
        Type::List(inner) => Ok(inner),
        other => Err(CompileError::new(format!(
            "expected list type, got {}",
            describe_type(other)
        ))),
    }
}

fn infer_index_type(ty: &Type) -> Result<Type, CompileError> {
    match deref_refs(ty) {
        Type::List(inner) => Ok((**inner).clone()),
        Type::FixedArray(_, inner) => Ok((**inner).clone()),
        other => Err(CompileError::new(format!(
            "expected list or fixed array type, got {}",
            describe_type(other)
        ))),
    }
}

fn is_codegen_condition_type(ty: &Type) -> bool {
    matches!(ty, Type::Bool) || is_codegen_integer_type(ty)
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

fn render_pointer_arithmetic_base(
    expr: &Expr,
    function: &Function,
    info: &ProgramInfo,
    deref_locals: &std::collections::HashSet<String>,
) -> Result<String, CompileError> {
    let rendered = render_expr(expr, function, info, deref_locals)?;
    let ty = infer_codegen_expr_type(expr, function, info)?;
    Ok(match ty {
        Type::Ref(inner) if inner.as_ref() == &Type::Void => format!("((char *)({rendered}))"),
        Type::Ref(inner) => match inner.as_ref() {
            Type::List(_) => format!("(({rendered})->data)"),
            _ => rendered,
        },
        Type::Mut(inner) => match inner.as_ref() {
            Type::Ref(pointee) if pointee.as_ref() == &Type::Void => {
                format!("((char *)({rendered}))")
            }
            Type::Ref(pointee) => match pointee.as_ref() {
                Type::List(_) => format!("(({rendered})->data)"),
                _ => rendered,
            },
            _ => rendered,
        },
        _ => rendered,
    })
}

fn is_codegen_string_compatible(ty: &Type) -> bool {
    matches!(ty, Type::Ref(inner) if inner.as_ref() == &Type::U8)
        || matches!(ty, Type::Mut(inner) if matches!(inner.as_ref(), Type::Ref(inner) if inner.as_ref() == &Type::U8))
}

fn is_codegen_nullable_pointer_type(ty: &Type) -> bool {
    matches!(ty, Type::Ref(_) | Type::Mut(_)) || is_codegen_string_compatible(ty)
}

fn can_codegen_compare_with_none(lhs: &Type, rhs: &Type) -> bool {
    matches!((lhs, rhs), (Type::None, Type::None))
        || (lhs == &Type::None && is_codegen_nullable_pointer_type(rhs))
        || (rhs == &Type::None && is_codegen_nullable_pointer_type(lhs))
}

fn is_codegen_signed_numeric_type(ty: &Type) -> bool {
    is_codegen_signed_integer_type(ty) || matches!(ty, Type::F32 | Type::F64)
}

pub(crate) fn is_codegen_signed_integer_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Isize
    )
}

pub(crate) fn is_codegen_unsigned_integer_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::U8 | Type::U16 | Type::U32 | Type::U64 | Type::Usize
    )
}

fn codegen_integer_rank(ty: &Type) -> Option<u8> {
    match ty {
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

fn codegen_float_rank(ty: &Type) -> Option<u8> {
    match ty {
        Type::F32 => Some(1),
        Type::F64 => Some(2),
        _ => None,
    }
}

fn common_codegen_integer_type(lhs: &Type, rhs: &Type) -> Option<Type> {
    if !is_codegen_integer_type(lhs) || !is_codegen_integer_type(rhs) {
        return None;
    }
    if lhs == rhs {
        return Some(lhs.clone());
    }
    let lhs_rank = codegen_integer_rank(lhs)?;
    let rhs_rank = codegen_integer_rank(rhs)?;
    if lhs_rank > rhs_rank {
        return Some(lhs.clone());
    }
    if rhs_rank > lhs_rank {
        return Some(rhs.clone());
    }
    if is_codegen_unsigned_integer_type(lhs) {
        Some(lhs.clone())
    } else {
        Some(rhs.clone())
    }
}

fn same_codegen_enum_type(lhs: &Type, rhs: &Type, info: &ProgramInfo) -> bool {
    if lhs != rhs {
        return false;
    }
    let name = match lhs {
        Type::Named(name) => name,
        Type::Applied(name, _) => name,
        _ => return false,
    };
    info.types
        .get(name)
        .is_some_and(|type_info| type_info.kind == TypeDefKind::Enum)
}

pub(crate) fn common_codegen_numeric_type(lhs: &Type, rhs: &Type) -> Option<Type> {
    if let Some(common) = common_codegen_integer_type(lhs, rhs) {
        return Some(common);
    }
    if lhs == rhs && matches!(lhs, Type::F32 | Type::F64) {
        return Some(lhs.clone());
    }
    if matches!(lhs, Type::F32 | Type::F64) && matches!(rhs, Type::F32 | Type::F64) {
        return Some(if codegen_float_rank(lhs)? >= codegen_float_rank(rhs)? {
            lhs.clone()
        } else {
            rhs.clone()
        });
    }
    None
}

pub(crate) fn unsigned_c_type(ty: &Type) -> Option<&'static str> {
    match ty {
        Type::I8 => Some("uint8_t"),
        Type::I16 => Some("uint16_t"),
        Type::I32 => Some("uint32_t"),
        Type::I64 => Some("uint64_t"),
        Type::Isize => Some("uintptr_t"),
        _ => None,
    }
}

fn print_format_specifier(marker: PrintMarker, ty: &Type) -> Result<&'static str, CompileError> {
    match marker {
        PrintMarker::Int if is_codegen_signed_integer_type(ty) => Ok("%jd"),
        PrintMarker::Int if is_codegen_unsigned_integer_type(ty) => Ok("%ju"),
        PrintMarker::Uint if is_codegen_unsigned_integer_type(ty) => Ok("%ju"),
        PrintMarker::Uint if is_codegen_signed_integer_type(ty) => Ok("%ju"),
        PrintMarker::Bool if matches!(ty, Type::Bool) => Ok("%s"),
        PrintMarker::Pointer
            if matches!(ty, Type::Ref(_) | Type::Mut(_) | Type::Named(_))
                || is_codegen_string_compatible(ty) =>
        {
            Ok("%p")
        }
        PrintMarker::String if is_codegen_string_compatible(ty) => Ok("%s"),
        PrintMarker::Float if matches!(ty, Type::F32 | Type::F64) => Ok("%f"),
        PrintMarker::Double if matches!(ty, Type::F32 | Type::F64) => Ok("%lf"),
        PrintMarker::Char if matches!(ty, Type::U8 | Type::I8) => Ok("%c"),
        PrintMarker::Hex if is_codegen_integer_type(ty) => Ok("%jx"),
        PrintMarker::HexUpper if is_codegen_integer_type(ty) => Ok("%jX"),
        PrintMarker::Octal if is_codegen_integer_type(ty) => Ok("%jo"),
        PrintMarker::Scientific if matches!(ty, Type::F32 | Type::F64) => Ok("%e"),
        PrintMarker::ScientificUpper if matches!(ty, Type::F32 | Type::F64) => Ok("%E"),
        PrintMarker::Shortest if matches!(ty, Type::F32 | Type::F64) => Ok("%g"),
        PrintMarker::ShortestUpper if matches!(ty, Type::F32 | Type::F64) => Ok("%G"),
        PrintMarker::Size if matches!(ty, Type::Usize | Type::Isize) => Ok("%zu"),
        other => {
            let name = match other {
                PrintMarker::Int => "d",
                PrintMarker::Uint => "u",
                PrintMarker::Bool => "b",
                PrintMarker::Pointer => "p",
                PrintMarker::String => "s",
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
            };
            Err(CompileError::new(format!(
                "format marker `{{{name}}}` does not accept value of type {}",
                describe_type(ty)
            )))
        }
    }
}

fn is_codegen_integer_type(ty: &Type) -> bool {
    is_codegen_signed_integer_type(ty) || is_codegen_unsigned_integer_type(ty)
}

fn render_print_value(
    marker: PrintMarker,
    ty: &Type,
    rendered: &str,
) -> Result<String, CompileError> {
    match marker {
        PrintMarker::Int if is_codegen_signed_integer_type(ty) => {
            Ok(format!("((intmax_t)({rendered}))"))
        }
        PrintMarker::Int if is_codegen_unsigned_integer_type(ty) => {
            Ok(format!("((uintmax_t)({rendered}))"))
        }
        PrintMarker::Uint if is_codegen_integer_type(ty) => {
            Ok(format!("((uintmax_t)({rendered}))"))
        }
        PrintMarker::Hex | PrintMarker::HexUpper | PrintMarker::Octal
            if is_codegen_signed_integer_type(ty) =>
        {
            Ok(format!("((uintmax_t)((intmax_t)({rendered})))"))
        }
        PrintMarker::Hex | PrintMarker::HexUpper | PrintMarker::Octal
            if is_codegen_unsigned_integer_type(ty) =>
        {
            Ok(format!("((uintmax_t)({rendered}))"))
        }
        PrintMarker::Size if matches!(ty, Type::Usize | Type::Isize) => {
            Ok(format!("((size_t)({rendered}))"))
        }
        PrintMarker::Bool if matches!(ty, Type::Bool) => {
            Ok(format!("(({rendered}) ? \"true\" : \"false\")"))
        }
        PrintMarker::Char if matches!(ty, Type::U8 | Type::I8) => {
            Ok(format!("((int)({rendered}))"))
        }
        PrintMarker::Pointer => Ok(format!("(void *)({rendered})")),
        PrintMarker::String
        | PrintMarker::Float
        | PrintMarker::Double
        | PrintMarker::Scientific
        | PrintMarker::ScientificUpper
        | PrintMarker::Shortest
        | PrintMarker::ShortestUpper => Ok(rendered.to_string()),
        _ => Err(CompileError::new(format!(
            "unsupported @print argument type {}",
            describe_type(ty)
        ))),
    }
}

pub(crate) fn resolve_codegen_aliases(ty: &Type, info: &ProgramInfo) -> Result<Type, CompileError> {
    match ty {
        Type::Named(name) => {
            let Some(type_info) = info.types.get(name) else {
                return Ok(Type::Named(name.clone()));
            };
            if let Some(alias) = &type_info.alias {
                resolve_codegen_aliases(alias, info)
            } else {
                Ok(Type::Named(name.clone()))
            }
        }
        Type::Result(inner) => Ok(Type::Result(Box::new(resolve_codegen_aliases(
            inner, info,
        )?))),
        Type::Mut(inner) => Ok(Type::Mut(Box::new(resolve_codegen_aliases(inner, info)?))),
        Type::Ref(inner) => Ok(Type::Ref(Box::new(resolve_codegen_aliases(inner, info)?))),
        Type::List(inner) => Ok(Type::List(Box::new(resolve_codegen_aliases(inner, info)?))),
        Type::FnPtr(params, ret) => Ok(Type::FnPtr(
            params
                .into_iter()
                .map(|p| resolve_codegen_aliases(p, info))
                .collect::<Result<Vec<_>, _>>()?,
            Box::new(resolve_codegen_aliases(ret, info)?),
        )),
        other => Ok(other.clone()),
    }
}

pub(crate) fn deref_refs(mut ty: &Type) -> &Type {
    loop {
        match ty {
            Type::Ref(inner) | Type::Mut(inner) => ty = inner,
            _ => return ty,
        }
    }
}

fn escape_c_string(value: &str) -> String {
    let mut escaped = String::new();
    for ch in value.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            other => escaped.push(other),
        }
    }
    escaped
}

pub(crate) fn is_integer_codegen_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
    )
}

pub(crate) fn describe_type(ty: &Type) -> String {
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
        Type::Applied(name, type_args) => format!(
            "{}[{}]",
            name,
            type_args
                .iter()
                .map(describe_type)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// Render a C declaration of the form `type name` or, for function pointers, `ret (*name)(params)`.
fn c_type_named(ty: &Type, name: &str) -> String {
    match ty {
        Type::FnPtr(params, ret) => {
            let ret_c = c_type(ret);
            let params_c = if params.is_empty() {
                "void".to_string()
            } else {
                params.iter().map(c_type).collect::<Vec<_>>().join(", ")
            };
            format!("{ret_c} (*{name})({params_c})")
        }
        Type::FixedArray(n, inner) => {
            // C declaration: `element_type name[N]`
            format!("{} {name}[{n}]", c_type(inner))
        }
        other => format!("{} {}", c_type(other), name),
    }
}

fn c_type_mut(ty: &Type) -> String {
    match ty {
        Type::Ref(inner) => {
            let inner = c_type_mut(inner);
            if inner.ends_with('*') {
                format!("{inner}*")
            } else {
                format!("{inner} *")
            }
        }
        Type::Mut(inner) => c_type_mut(inner),
        other => c_type(other),
    }
}

pub(crate) fn is_reference_like(ty: &Type) -> bool {
    matches!(ty, Type::Ref(_))
        || matches!(ty, Type::Mut(inner) if matches!(inner.as_ref(), Type::Ref(_)))
}

fn indent(output: &mut String, level: usize) {
    for _ in 0..level {
        output.push_str("    ");
    }
}

#[cfg(test)]
mod tests {
    use super::generate_c;
    use crate::{lexer::lex, parser::parse_program, sema::analyze};

    #[test]
    fn generates_qualified_function_calls_in_expression_context() {
        let source = "type Arena\n\tcap usize\nend\n\npub def Arena.alloc_aligned(a ref(Arena), size usize, align usize) ref(void)|error\n\treturn none\nend\n\npub def Arena.alloc(a ref(Arena), size usize) ref(void)|error\n\treturn Arena.alloc_aligned(a, size, 8)\nend\n\npub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();
        let info = analyze(&program).unwrap();

        let output = generate_c(&program, &info, false).unwrap();

        assert!(output.contains("fn__Arena_alloc_aligned"));
        assert!(output.contains("fn__Arena_alloc_aligned(loc__a, loc__size, 8)"));
    }

    #[test]
    fn emits_extern_header_includes() {
        let source = "extern \"windows.h\"\nextern def GetTickCount() u32 :: \"GetTickCount\"\npub def main() void\n\tGetTickCount()\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();
        let info = analyze(&program).unwrap();

        let output = generate_c(&program, &info, false).unwrap();

        assert!(output.contains("#include \"windows.h\""));
    }
}
