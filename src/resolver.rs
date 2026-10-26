use std::{
    collections::{HashMap, HashSet},
    env, fs,
    path::{Path, PathBuf},
};

use crate::{
    CompileError,
    ast::{
        BinaryOp, EnumDef, Expr, FieldDef, FieldInit, Function, GenericParam, GlobalVar,
        InterfaceDef, InterfaceMethod, MatchArmKind, ModuleUse, Param, Program, Stmt, TestBlock,
        Type, TypeDef, TypeDefKind, TypeSetDef, UnaryOp, UnionVariantDef,
    },
    lexer::lex,
    parser::parse_program,
};

pub fn resolve_entry_program(entry: &Path) -> Result<Program, CompileError> {
    let entry = canonicalize_path(entry)?;
    let root_dir = entry
        .parent()
        .ok_or_else(|| CompileError::new("input file must have a parent directory"))?
        .to_path_buf();
    let mut resolver = Resolver {
        root_dir,
        local_std_root: discover_local_std_root()?,
        home_std_root: discover_home_std_root()?,
        cache: HashMap::new(),
        emitted_modules: HashSet::new(),
        resolved_interfaces: Vec::new(),
        resolved_types: Vec::new(),
        resolved_typesets: Vec::new(),
        resolved_enums: Vec::new(),
        resolved_functions: Vec::new(),
        resolved_globals: Vec::new(),
        resolved_extern_headers: Vec::new(),
        resolved_link_flags: Vec::new(),
        visiting: Vec::new(),
        used_module_aliases: HashSet::new(),
    };

    USED_MODULE_ALIASES.with(|u| u.borrow_mut().clear());

    let program = parse_program_file(&entry)?;
    let module_aliases = resolver.resolve_module_uses(&program.module_uses, &entry)?;
    let local_symbols = build_named_symbol_map(
        &program.type_defs,
        &program.interface_defs,
        &program.typesets,
        &program.enum_defs,
        None,
    );
    let local_functions = build_function_map(&program.functions, None);
    let local_globals = build_global_map(&program.globals, None);
    LOCAL_GLOBALS.with(|lg| *lg.borrow_mut() = local_globals);
    let mut interface_defs = resolver.resolved_interfaces;
    for interface_def in program.interface_defs {
        interface_defs.push(rewrite_interface_def(
            interface_def,
            &local_symbols,
            &module_aliases,
        )?);
    }
    let mut type_defs = resolver.resolved_types;
    for type_def in program.type_defs {
        type_defs.push(rewrite_type_def(type_def, &local_symbols, &module_aliases)?);
    }
    let mut typesets = resolver.resolved_typesets;
    for typeset in program.typesets {
        typesets.push(rewrite_typeset_def(
            typeset,
            &local_symbols,
            &module_aliases,
        ));
    }
    let mut functions = resolver.resolved_functions;
    for function in program.functions {
        functions.push(rewrite_function(
            function,
            &local_functions,
            &local_symbols,
            &module_aliases,
        )?);
    }
    let mut globals = resolver.resolved_globals;
    for global in program.globals {
        globals.push(rewrite_global_var(
            global,
            &local_functions,
            &local_symbols,
            &module_aliases,
        )?);
    }
    let tests = program
        .tests
        .into_iter()
        .map(|test| rewrite_test_block(test, &local_functions, &local_symbols, &module_aliases))
        .collect::<Result<Vec<_>, _>>()?;

    USED_MODULE_ALIASES.with(|u| {
        let used = u.borrow();
        for module_use in &program.module_uses {
            if !used.contains(&module_use.name) {
                return Err(CompileError::new(format!(
                    "module `{}` imported but never used",
                    module_use.path
                )));
            }
        }
        Ok(())
    })?;

    instantiate_generic_functions(Program {
        module_uses: Vec::new(),
        extern_headers: {
            let mut headers = resolver.resolved_extern_headers;
            headers.extend(program.extern_headers);
            headers
        },
        link_flags: {
            let mut flags = resolver.resolved_link_flags;
            flags.extend(program.link_flags);
            let mut unique = Vec::new();
            let mut seen = HashSet::new();
            for flag in flags {
                if seen.insert(flag.clone()) {
                    unique.push(flag);
                }
            }
            unique
        },
        interface_defs,
        type_defs,
        typesets,
        enum_defs: Vec::new(),
        functions,
        tests,
        globals,
    })
}

#[derive(Clone)]
struct ModuleExports {
    functions: HashMap<String, String>,
    named_types: HashMap<String, String>,
    interfaces: HashMap<String, String>,
    typesets: HashMap<String, String>,
    globals: HashMap<String, String>,
}

type ModuleAliases = HashMap<String, ModuleExports>;

struct Resolver {
    root_dir: PathBuf,
    local_std_root: Option<PathBuf>,
    home_std_root: Option<PathBuf>,
    cache: HashMap<PathBuf, ModuleExports>,
    emitted_modules: HashSet<PathBuf>,
    resolved_interfaces: Vec<InterfaceDef>,
    resolved_types: Vec<TypeDef>,
    resolved_typesets: Vec<TypeSetDef>,
    resolved_enums: Vec<EnumDef>,
    resolved_functions: Vec<Function>,
    resolved_globals: Vec<GlobalVar>,
    resolved_extern_headers: Vec<String>,
    resolved_link_flags: Vec<String>,
    visiting: Vec<PathBuf>,
    used_module_aliases: HashSet<String>,
}

impl Resolver {
    fn resolve_module_uses(
        &mut self,
        module_uses: &[ModuleUse],
        current_file: &Path,
    ) -> Result<ModuleAliases, CompileError> {
        let current_dir = current_file.parent().ok_or_else(|| {
            CompileError::new(format!(
                "source file {} must have a parent directory",
                current_file.display()
            ))
        })?;

        let mut aliases = HashMap::new();
        for module_use in module_uses {
            let module_path = resolve_module_use_path(
                current_dir,
                &module_use.path,
                self.local_std_root.as_deref(),
                self.home_std_root.as_deref(),
            )?;
            let exports = self.resolve_module(&module_path)?;
            aliases.insert(module_use.name.clone(), exports);
        }
        Ok(aliases)
    }

    fn resolve_module(&mut self, module_path: &Path) -> Result<ModuleExports, CompileError> {
        let module_path = canonicalize_path(module_path)?;
        if let Some(exports) = self.cache.get(&module_path) {
            return Ok(exports.clone());
        }
        if let Some(index) = self.visiting.iter().position(|path| path == &module_path) {
            let cycle = self.visiting[index..]
                .iter()
                .chain(std::iter::once(&module_path))
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(" -> ");
            return Err(CompileError::new(format!(
                "module import cycle detected: {cycle}"
            )));
        }

        self.visiting.push(module_path.clone());
        let parsed = parse_program_file(&module_path)?;
        let module_aliases = self.resolve_module_uses(&parsed.module_uses, &module_path)?;
        let prefix = module_prefix(&module_path, &self.root_dir);
        let local_symbols = build_named_symbol_map(
            &parsed.type_defs,
            &parsed.interface_defs,
            &parsed.typesets,
            &parsed.enum_defs,
            Some(&prefix),
        );
        let local_functions = build_function_map(&parsed.functions, Some(&prefix));
        let local_globals = build_global_map(&parsed.globals, Some(&prefix));
        LOCAL_GLOBALS.with(|lg| *lg.borrow_mut() = local_globals);
        let public_functions = build_public_function_map(&parsed.functions, Some(&prefix));
        let public_types = build_public_named_type_map(&parsed.type_defs, Some(&prefix));
        let public_interfaces = build_public_interface_map(&parsed.interface_defs, Some(&prefix));
        let public_typesets = build_public_typeset_map(&parsed.typesets, Some(&prefix));

        let mut rewritten_interfaces = Vec::new();
        for interface_def in parsed.interface_defs {
            rewritten_interfaces.push(rewrite_interface_def(
                interface_def,
                &local_symbols,
                &module_aliases,
            )?);
        }
        let mut rewritten_types = Vec::new();
        for type_def in parsed.type_defs {
            rewritten_types.push(rewrite_type_def(type_def, &local_symbols, &module_aliases)?);
        }
        let mut rewritten_typesets = Vec::new();
        for typeset in parsed.typesets {
            rewritten_typesets.push(rewrite_typeset_def(
                typeset,
                &local_symbols,
                &module_aliases,
            ));
        }

        let mut rewritten_functions = Vec::new();
        for function in parsed.functions {
            rewritten_functions.push(rewrite_function(
                function,
                &local_functions,
                &local_symbols,
                &module_aliases,
            )?);
        }

        let mut rewritten_globals = Vec::new();
        for global in &parsed.globals {
            rewritten_globals.push(rewrite_global_var(
                global.clone(),
                &local_functions,
                &local_symbols,
                &module_aliases,
            )?);
        }
        let public_globals = build_public_global_map(&parsed.globals);

        if self.emitted_modules.insert(module_path.clone()) {
            self.resolved_interfaces.extend(rewritten_interfaces);
            self.resolved_types.extend(rewritten_types);
            self.resolved_typesets.extend(rewritten_typesets);
            self.resolved_functions.extend(rewritten_functions);
            self.resolved_globals.extend(rewritten_globals);
            self.resolved_extern_headers.extend(parsed.extern_headers);
            self.resolved_link_flags.extend(parsed.link_flags);
        }

        self.visiting.pop();
        let mut all_public_types = public_types;
        for enum_def in &parsed.enum_defs {
            if enum_def.is_pub {
                let mapped = format!("{prefix}__{}", enum_def.name);
                all_public_types.insert(enum_def.name.clone(), mapped);
            }
        }
        let exports = ModuleExports {
            functions: public_functions,
            named_types: all_public_types,
            interfaces: public_interfaces,
            typesets: public_typesets,
            globals: public_globals,
        };
        self.cache.insert(module_path, exports.clone());
        Ok(exports)
    }
}

fn parse_program_file(path: &Path) -> Result<Program, CompileError> {
    let source = fs::read_to_string(path).map_err(|error| {
        CompileError::new(format!("failed to read {}: {error}", path.display())).with_file(path)
    })?;
    let tokens = lex(&source).map_err(|error| {
        CompileError::new(format!("in {}: {error}", path.display())).with_file(path)
    })?;
    let mut program = parse_program(tokens).map_err(|error| error.with_file(path))?;
    for f in &mut program.functions {
        f.file_path = Some(path.to_path_buf());
    }
    for t in &mut program.type_defs {
        t.file_path = Some(path.to_path_buf());
    }
    for e in &mut program.enum_defs {
        e.file_path = Some(path.to_path_buf());
    }
    for g in &mut program.globals {
        g.file_path = Some(path.to_path_buf());
    }
    for i in &mut program.interface_defs {
        i.file_path = Some(path.to_path_buf());
    }
    Ok(program)
}

fn discover_local_std_root() -> Result<Option<PathBuf>, CompileError> {
    let candidate = env::current_dir()
        .map_err(|error| CompileError::new(format!("failed to get current directory: {error}")))?
        .join("lib")
        .join("std");
    if candidate.is_dir() {
        Ok(Some(canonicalize_path(&candidate)?))
    } else {
        Ok(None)
    }
}

fn discover_home_std_root() -> Result<Option<PathBuf>, CompileError> {
    let Some(home) = env::var_os("HOME") else {
        return Ok(None);
    };
    let candidate = PathBuf::from(home).join(".scar").join("lib").join("std");
    if candidate.is_dir() {
        Ok(Some(canonicalize_path(&candidate)?))
    } else {
        Ok(None)
    }
}

fn resolve_module_use_path(
    current_dir: &Path,
    module_path: &str,
    local_std_root: Option<&Path>,
    home_std_root: Option<&Path>,
) -> Result<PathBuf, CompileError> {
    fn check_path(base: &Path) -> Result<Option<PathBuf>, CompileError> {
        let mod_path = base.join("mod.scar");
        let file_path = base.with_extension("scar");

        let mod_exists = mod_path.exists();
        let file_exists = file_path.exists();

        if mod_exists && file_exists {
            return Err(CompileError::new(format!(
                "ambiguous module resolution: both {} and {} exist",
                mod_path.display(),
                file_path.display()
            )));
        }

        if mod_exists {
            Ok(Some(mod_path))
        } else if file_exists {
            Ok(Some(file_path))
        } else {
            Ok(None)
        }
    }

    if let Some(rest) = module_path.strip_prefix("std/") {
        if let Some(local_std_root) = local_std_root {
            let base = local_std_root.join(rest);
            if let Some(path) = check_path(&base)? {
                return Ok(path);
            }
        }
        if let Some(home_std_root) = home_std_root {
            let base = home_std_root.join(rest);
            if let Some(path) = check_path(&base)? {
                return Ok(path);
            }
        }

        if let Some(local_std_root) = local_std_root {
            return Ok(local_std_root.join(rest).with_extension("scar"));
        } else if let Some(home_std_root) = home_std_root {
            return Ok(home_std_root.join(rest).with_extension("scar"));
        }
    }

    let base = current_dir.join(module_path);
    if let Some(path) = check_path(&base)? {
        Ok(path)
    } else {
        Ok(base.with_extension("scar"))
    }
}

fn canonicalize_path(path: &Path) -> Result<PathBuf, CompileError> {
    fs::canonicalize(path).map_err(|error| {
        CompileError::new(format!("failed to resolve {}: {error}", path.display()))
    })
}

fn build_function_map(functions: &[Function], prefix: Option<&str>) -> HashMap<String, String> {
    functions
        .iter()
        .map(|function| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", function.name),
                None => function.name.clone(),
            };
            (function.name.clone(), mapped)
        })
        .collect()
}

fn build_global_map(globals: &[GlobalVar], prefix: Option<&str>) -> HashMap<String, String> {
    globals
        .iter()
        .map(|global| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", global.name),
                None => global.name.clone(),
            };
            (global.name.clone(), mapped)
        })
        .collect()
}

fn build_public_function_map(
    functions: &[Function],
    prefix: Option<&str>,
) -> HashMap<String, String> {
    functions
        .iter()
        .filter(|function| function.is_pub)
        .map(|function| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", function.name),
                None => function.name.clone(),
            };
            (function.name.clone(), mapped)
        })
        .collect()
}

fn build_named_symbol_map(
    type_defs: &[TypeDef],
    interface_defs: &[InterfaceDef],
    typesets: &[TypeSetDef],
    enum_defs: &[EnumDef],
    prefix: Option<&str>,
) -> HashMap<String, String> {
    let mut named = type_defs
        .iter()
        .map(|type_def| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", type_def.name),
                None => type_def.name.clone(),
            };
            (type_def.name.clone(), mapped)
        })
        .collect::<HashMap<_, _>>();
    named.extend(interface_defs.iter().map(|interface_def| {
        let mapped = match prefix {
            Some(prefix) => format!("{prefix}__{}", interface_def.name),
            None => interface_def.name.clone(),
        };
        (interface_def.name.clone(), mapped)
    }));
    named.extend(typesets.iter().map(|typeset| {
        let mapped = match prefix {
            Some(prefix) => format!("{prefix}__{}", typeset.name),
            None => typeset.name.clone(),
        };
        (typeset.name.clone(), mapped)
    }));
    for enum_def in enum_defs {
        let mapped = match prefix {
            Some(prefix) => format!("{prefix}__{}", enum_def.name),
            None => enum_def.name.clone(),
        };
        named.insert(enum_def.name.clone(), mapped.clone());
        for variant in &enum_def.variants {
            named.insert(
                format!("{}.{}", enum_def.name, variant.name),
                format!("{}__{}", mapped, variant.name),
            );
        }
    }
    named
}

fn build_public_named_type_map(
    type_defs: &[TypeDef],
    prefix: Option<&str>,
) -> HashMap<String, String> {
    type_defs
        .iter()
        .filter(|type_def| type_def.is_pub)
        .map(|type_def| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", type_def.name),
                None => type_def.name.clone(),
            };
            (type_def.name.clone(), mapped)
        })
        .collect()
}

fn build_public_interface_map(
    interface_defs: &[InterfaceDef],
    prefix: Option<&str>,
) -> HashMap<String, String> {
    interface_defs
        .iter()
        .filter(|interface_def| interface_def.is_pub)
        .map(|interface_def| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", interface_def.name),
                None => interface_def.name.clone(),
            };
            (interface_def.name.clone(), mapped)
        })
        .collect()
}

fn build_public_typeset_map(
    typesets: &[TypeSetDef],
    prefix: Option<&str>,
) -> HashMap<String, String> {
    typesets
        .iter()
        .filter(|typeset| typeset.is_pub)
        .map(|typeset| {
            let mapped = match prefix {
                Some(prefix) => format!("{prefix}__{}", typeset.name),
                None => typeset.name.clone(),
            };
            (typeset.name.clone(), mapped)
        })
        .collect()
}

fn build_public_global_map(globals: &[GlobalVar]) -> HashMap<String, String> {
    let local_globals = LOCAL_GLOBALS.with(|lg| lg.borrow().clone());
    globals
        .iter()
        .filter(|g| g.is_pub)
        .map(|g| {
            let mapped = local_globals
                .get(&g.name)
                .cloned()
                .unwrap_or_else(|| g.name.clone());
            (g.name.clone(), mapped)
        })
        .collect()
}

fn rewrite_global_var(
    mut global: GlobalVar,
    local_functions: &HashMap<String, String>,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<GlobalVar, CompileError> {
    if let Some(mapped) = LOCAL_GLOBALS.with(|lg| lg.borrow().get(&global.name).cloned()) {
        global.name = mapped;
    }
    global.ty = rewrite_type(global.ty, local_types, module_aliases);
    global.init = rewrite_expr(global.init, local_functions, local_types, module_aliases)?;
    Ok(global)
}

fn module_prefix(module_path: &Path, root_dir: &Path) -> String {
    let relative = module_path
        .strip_prefix(root_dir)
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|_| {
            env::current_dir()
                .ok()
                .and_then(|cwd| module_path.strip_prefix(&cwd).ok())
                .map(|p| p.to_path_buf())
                .unwrap_or_else(|| module_path.to_path_buf())
        })
        .with_extension("");
    let mut segments = Vec::new();
    for component in relative.components() {
        let piece = component.as_os_str().to_string_lossy();
        let sanitized: String = piece
            .chars()
            .map(|ch| {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    ch
                } else {
                    '_'
                }
            })
            .collect();
        if !sanitized.is_empty() {
            segments.push(sanitized);
        }
    }
    if segments.is_empty() {
        "module".to_string()
    } else {
        segments.join("__")
    }
}

thread_local! {
    static LOCAL_VARS: std::cell::RefCell<HashSet<String>> = std::cell::RefCell::new(HashSet::new());
    static USED_MODULE_ALIASES: std::cell::RefCell<HashSet<String>> = std::cell::RefCell::new(HashSet::new());
    static LOCAL_GLOBALS: std::cell::RefCell<HashMap<String, String>> = std::cell::RefCell::new(HashMap::new());
}

fn collect_local_vars(params: &[Param], body: &[Stmt]) -> HashSet<String> {
    let mut vars = HashSet::new();
    for param in params {
        vars.insert(param.name.clone());
    }
    fn collect(stmts: &[Stmt], vars: &mut HashSet<String>) {
        for stmt in stmts {
            match stmt {
                Stmt::VarDecl { name, .. } => {
                    vars.insert(name.clone());
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    collect(then_body, vars);
                    collect(else_body, vars);
                }
                Stmt::Match { arms, .. } => {
                    for arm in arms {
                        collect(&arm.body, vars);
                    }
                }
                Stmt::ForRange { var_name, body, .. } => {
                    vars.insert(var_name.clone());
                    collect(body, vars);
                }
                Stmt::ForEach { var_name, body, .. } => {
                    vars.insert(var_name.clone());
                    collect(body, vars);
                }
                Stmt::ForClassic { var_name, body, .. } => {
                    vars.insert(var_name.clone());
                    collect(body, vars);
                }
                Stmt::While { body, .. } | Stmt::Loop { body, .. } => {
                    collect(body, vars);
                }
                _ => {}
            }
        }
    }
    collect(body, &mut vars);
    vars
}

fn rewrite_function(
    mut function: Function,
    local_functions: &HashMap<String, String>,
    local_symbols: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<Function, CompileError> {
    let vars = collect_local_vars(&function.params, &function.body);
    LOCAL_VARS.with(|lv| {
        *lv.borrow_mut() = vars;
    });

    if let Some(mapped) = local_functions.get(&function.name) {
        function.name = mapped.clone();
    }
    function.generic_params = function
        .generic_params
        .into_iter()
        .map(|GenericParam { name, constraints }| GenericParam {
            name,
            constraints: constraints
                .into_iter()
                .map(|constraint| rewrite_type(constraint, local_symbols, module_aliases))
                .collect(),
        })
        .collect();
    function.params = function
        .params
        .into_iter()
        .map(|mut param| {
            param.ty = rewrite_type(param.ty, local_symbols, module_aliases);
            param
        })
        .collect();
    function.return_type = rewrite_type(function.return_type, local_symbols, module_aliases);
    function.body = function
        .body
        .into_iter()
        .map(|stmt| rewrite_stmt(stmt, local_functions, local_symbols, module_aliases))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(function)
}

fn rewrite_interface_def(
    interface_def: InterfaceDef,
    local_symbols: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<InterfaceDef, CompileError> {
    let name = local_symbols
        .get(&interface_def.name)
        .cloned()
        .unwrap_or(interface_def.name);
    let methods = interface_def
        .methods
        .into_iter()
        .map(|method| {
            Ok(InterfaceMethod {
                is_pub: method.is_pub,
                name: method.name,
                params: method
                    .params
                    .into_iter()
                    .map(|param| Param {
                        name: param.name,
                        ty: rewrite_type(param.ty, local_symbols, module_aliases),
                        line: param.line,
                        column: param.column,
                    })
                    .collect(),
                return_type: rewrite_type(method.return_type, local_symbols, module_aliases),
            })
        })
        .collect::<Result<Vec<_>, CompileError>>()?;
    Ok(InterfaceDef {
        is_pub: interface_def.is_pub,
        name,
        methods,
        file_path: interface_def.file_path,
    })
}

fn rewrite_type_def(
    type_def: TypeDef,
    local_symbols: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<TypeDef, CompileError> {
    let name = local_symbols
        .get(&type_def.name)
        .cloned()
        .unwrap_or(type_def.name);
    let is_extern = type_def.is_extern;
    let is_pub = type_def.is_pub;
    let generic_params = type_def
        .generic_params
        .into_iter()
        .map(|GenericParam { name, constraints }| GenericParam {
            name,
            constraints: constraints
                .into_iter()
                .map(|constraint| rewrite_type(constraint, local_symbols, module_aliases))
                .collect(),
        })
        .collect();
    let alias = type_def
        .alias
        .map(|ty| rewrite_type(ty, local_symbols, module_aliases));
    let derives = type_def
        .derives
        .into_iter()
        .map(|ty| rewrite_type(ty, local_symbols, module_aliases))
        .collect();
    let fields = type_def
        .fields
        .into_iter()
        .map(|field| FieldDef {
            name: field.name,
            ty: rewrite_type(field.ty, local_symbols, module_aliases),
            line: field.line,
            column: field.column,
        })
        .collect();
    Ok(TypeDef {
        is_pub,
        name,
        generic_params,
        kind: type_def.kind,
        is_extern,
        alias,
        derives,
        fields,
        variants: type_def
            .variants
            .into_iter()
            .map(|variant| UnionVariantDef {
                name: variant.name,
                payload_types: variant
                    .payload_types
                    .into_iter()
                    .map(|ty| rewrite_type(ty, local_symbols, module_aliases))
                    .collect(),
            })
            .collect(),
        line: type_def.line,
        column: type_def.column,
        file_path: type_def.file_path,
    })
}

fn rewrite_typeset_def(
    typeset: TypeSetDef,
    local_symbols: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> TypeSetDef {
    TypeSetDef {
        is_pub: typeset.is_pub,
        name: local_symbols
            .get(&typeset.name)
            .cloned()
            .unwrap_or(typeset.name),
        members: typeset
            .members
            .into_iter()
            .map(|member| rewrite_type(member, local_symbols, module_aliases))
            .collect(),
    }
}

fn rewrite_test_block(
    test: TestBlock,
    local_functions: &HashMap<String, String>,
    local_symbols: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<TestBlock, CompileError> {
    Ok(TestBlock {
        name: test.name,
        body: test
            .body
            .into_iter()
            .map(|stmt| rewrite_stmt(stmt, local_functions, local_symbols, module_aliases))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn rewrite_stmt(
    stmt: Stmt,
    local_functions: &HashMap<String, String>,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<Stmt, CompileError> {
    match stmt {
        Stmt::VarDecl {
            line,
            column,
            mutable,
            name,
            declared_type,
            init,
        } => Ok(Stmt::VarDecl {
            line,
            column,
            mutable,
            name,
            declared_type: declared_type.map(|ty| rewrite_type(ty, local_types, module_aliases)),
            init: rewrite_expr(init, local_functions, local_types, module_aliases)?,
        }),
        Stmt::Assign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::Assign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::AddAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::AddAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::MulAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::MulAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::SubAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::SubAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::DivAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::DivAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::BitAndAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::BitAndAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::BitOrAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::BitOrAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::BitXorAssign {
            line,
            column,
            target,
            value,
        } => Ok(Stmt::BitXorAssign {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
            value: rewrite_expr(value, local_functions, local_types, module_aliases)?,
        }),
        Stmt::Increment {
            line,
            column,
            target,
        } => Ok(Stmt::Increment {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
        }),
        Stmt::Decrement {
            line,
            column,
            target,
        } => Ok(Stmt::Decrement {
            line,
            column,
            target: rewrite_expr(target, local_functions, local_types, module_aliases)?,
        }),
        Stmt::Assert {
            line,
            column,
            condition,
        } => Ok(Stmt::Assert {
            line,
            column,
            condition: rewrite_expr(condition, local_functions, local_types, module_aliases)?,
        }),
        Stmt::Return {
            line,
            column,
            value,
        } => Ok(Stmt::Return {
            line,
            column,
            value: value
                .map(|expr| rewrite_expr(expr, local_functions, local_types, module_aliases))
                .transpose()?,
        }),
        Stmt::Block(body) => Ok(Stmt::Block(
            body.into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Stmt::Expr { line, column, expr } => Ok(Stmt::Expr {
            line,
            column,
            expr: rewrite_expr(expr, local_functions, local_types, module_aliases)?,
        }),
        Stmt::If {
            line,
            column,
            condition,
            then_body,
            else_body,
        } => Ok(Stmt::If {
            line,
            column,
            condition: rewrite_expr(condition, local_functions, local_types, module_aliases)?,
            then_body: then_body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
            else_body: else_body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::Match {
            line,
            column,
            expr,
            arms,
        } => Ok(Stmt::Match {
            line,
            column,
            expr: rewrite_expr(expr, local_functions, local_types, module_aliases)?,
            arms: arms
                .into_iter()
                .map(|arm| {
                    Ok(crate::ast::MatchArm {
                        kind: arm.kind,
                        bindings: arm.bindings,
                        body: arm
                            .body
                            .into_iter()
                            .map(|stmt| {
                                rewrite_stmt(stmt, local_functions, local_types, module_aliases)
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    })
                })
                .collect::<Result<Vec<_>, CompileError>>()?,
        }),
        Stmt::ForRange {
            line,
            column,
            pragma,
            var_name,
            start,
            end,
            body,
        } => Ok(Stmt::ForRange {
            line,
            column,
            pragma,
            var_name,
            start: rewrite_expr(start, local_functions, local_types, module_aliases)?,
            end: rewrite_expr(end, local_functions, local_types, module_aliases)?,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::ForEach {
            line,
            column,
            var_name,
            iterable,
            body,
        } => Ok(Stmt::ForEach {
            line,
            column,
            var_name,
            iterable: rewrite_expr(iterable, local_functions, local_types, module_aliases)?,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::ForClassic {
            line,
            column,
            pragma,
            var_name,
            init,
            condition,
            increment,
            body,
        } => Ok(Stmt::ForClassic {
            line,
            column,
            pragma,
            var_name,
            init: rewrite_expr(init, local_functions, local_types, module_aliases)?,
            condition: rewrite_expr(condition, local_functions, local_types, module_aliases)?,
            increment: rewrite_expr(increment, local_functions, local_types, module_aliases)?,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::While {
            line,
            column,
            condition,
            body,
        } => Ok(Stmt::While {
            line,
            column,
            condition: rewrite_expr(condition, local_functions, local_types, module_aliases)?,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::Loop { line, column, body } => Ok(Stmt::Loop {
            line,
            column,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Stmt::Continue { line, column } => Ok(Stmt::Continue { line, column }),
        Stmt::Break { line, column } => Ok(Stmt::Break { line, column }),
        Stmt::Defer { line, column, body } => Ok(Stmt::Defer {
            line,
            column,
            body: body
                .into_iter()
                .map(|stmt| rewrite_stmt(stmt, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

fn rewrite_expr(
    expr: Expr,
    local_functions: &HashMap<String, String>,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<Expr, CompileError> {
    match expr {
        Expr::Int(_)
        | Expr::Char(_)
        | Expr::Bool(_)
        | Expr::Float(_)
        | Expr::String(_)
        | Expr::None => Ok(expr),
        Expr::Path(ref path) => {
            if path.len() == 1 {
                if let Some(mapped) = local_types.get(&path[0]) {
                    return Ok(Expr::Path(vec![mapped.clone()]));
                }
                let is_local = LOCAL_VARS.with(|lv| lv.borrow().contains(&path[0]));
                if !is_local {
                    if let Some(mapped) = local_functions.get(&path[0]) {
                        return Ok(Expr::Path(vec![mapped.clone()]));
                    }
                    if let Some(mapped) =
                        LOCAL_GLOBALS.with(|lg| lg.borrow().get(&path[0]).cloned())
                    {
                        return Ok(Expr::Path(vec![mapped.clone()]));
                    }
                }
            }
            let full_path = path.join(".");
            if let Some(mapped) = local_types.get(&full_path) {
                if path.len() == 2 {
                    let type_mapped = local_types
                        .get(&path[0])
                        .cloned()
                        .unwrap_or_else(|| path[0].clone());
                    return Ok(Expr::Path(vec![type_mapped, path[1].clone()]));
                }
                return Ok(Expr::Path(vec![mapped.clone()]));
            }
            if let Some(mapped) = local_functions.get(&full_path) {
                return Ok(Expr::Path(vec![mapped.clone()]));
            }
            if path.len() == 3 {
                let is_local = LOCAL_VARS.with(|lv| lv.borrow().contains(&path[0]));
                if !is_local {
                    if let Some(module) = module_aliases.get(&path[0]) {
                        USED_MODULE_ALIASES.with(|u| u.borrow_mut().insert(path[0].clone()));
                        if let Some(type_name) = module.named_types.get(&path[1]) {
                            return Ok(Expr::Path(vec![type_name.clone(), path[2].clone()]));
                        }
                    }
                }
            }
            if path.len() == 2 {
                let is_local = LOCAL_VARS.with(|lv| lv.borrow().contains(&path[0]));
                if !is_local {
                    if let Some(module) = module_aliases.get(&path[0]) {
                        USED_MODULE_ALIASES.with(|u| u.borrow_mut().insert(path[0].clone()));
                        if let Some(func_name) = module.functions.get(&path[1]) {
                            return Ok(Expr::Path(vec![func_name.clone()]));
                        }
                    }
                }
            }
            Ok(expr)
        }
        Expr::ListLiteral(values) => Ok(Expr::ListLiteral(
            values
                .into_iter()
                .map(|value| rewrite_expr(value, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Expr::Index { base, index } => Ok(Expr::Index {
            base: Box::new(rewrite_expr(
                *base,
                local_functions,
                local_types,
                module_aliases,
            )?),
            index: Box::new(rewrite_expr(
                *index,
                local_functions,
                local_types,
                module_aliases,
            )?),
        }),
        Expr::FieldAccess { base, field } => {
            if let Expr::Path(ref path) = *base {
                if path.len() == 1 {
                    let qualified = format!("{}.{}", path[0], field);
                    if local_types.contains_key(&qualified) {
                        let type_mapped = local_types
                            .get(&path[0])
                            .cloned()
                            .unwrap_or_else(|| path[0].clone());
                        return Ok(Expr::Path(vec![type_mapped, field.clone()]));
                    }
                    let is_local = LOCAL_VARS.with(|lv| lv.borrow().contains(&path[0]));
                    if !is_local {
                        if let Some(module) = module_aliases.get(&path[0]) {
                            USED_MODULE_ALIASES.with(|u| u.borrow_mut().insert(path[0].clone()));
                            if let Some(global_name) = module.globals.get(&field) {
                                return Ok(Expr::Path(vec![global_name.clone()]));
                            }
                            if let Some(func_name) = module.functions.get(&field) {
                                return Ok(Expr::Path(vec![func_name.clone()]));
                            }
                            if let Some(type_name) = module.named_types.get(&field) {
                                return Ok(Expr::Path(vec![type_name.clone()]));
                            }
                        }
                    }
                }
            }
            let rewritten_base = rewrite_expr(*base, local_functions, local_types, module_aliases)?;
            if let Expr::Path(ref path) = rewritten_base {
                if path.len() == 1 {
                    let qualified = format!("{}.{}", path[0], field);
                    if local_types.contains_key(&qualified) {
                        let type_mapped = local_types
                            .get(&path[0])
                            .cloned()
                            .unwrap_or_else(|| path[0].clone());
                        return Ok(Expr::Path(vec![type_mapped, field.clone()]));
                    }
                    if local_types.contains_key(&path[0]) {
                        return Ok(Expr::Path(vec![path[0].clone(), field.clone()]));
                    }
                    for (key, value) in local_types {
                        if *value == path[0] {
                            let unmapped_qualified = format!("{}.{}", key, field);
                            if local_types.contains_key(&unmapped_qualified) {
                                return Ok(Expr::Path(vec![key.clone(), field.clone()]));
                            }
                            return Ok(Expr::Path(vec![key.clone(), field.clone()]));
                        }
                    }
                    if path[0].contains("__") {
                        return Ok(Expr::Path(vec![path[0].clone(), field.clone()]));
                    }
                }
            }
            Ok(Expr::FieldAccess {
                base: Box::new(rewritten_base),
                field,
            })
        }
        Expr::StructInit {
            name,
            type_args,
            fields,
        } => Ok(Expr::StructInit {
            name: rewrite_named_type(name, local_types, module_aliases),
            type_args: type_args
                .into_iter()
                .map(|ty| rewrite_type(ty, local_types, module_aliases))
                .collect(),
            fields: fields
                .into_iter()
                .map(|field| {
                    Ok(FieldInit {
                        name: field.name,
                        value: rewrite_expr(
                            field.value,
                            local_functions,
                            local_types,
                            module_aliases,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, CompileError>>()?,
        }),
        Expr::BuiltinCall { name, args } => Ok(Expr::BuiltinCall {
            name,
            args: args
                .into_iter()
                .map(|arg| rewrite_expr(arg, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Ok(Expr::MethodCall {
            receiver: Box::new(rewrite_expr(
                *receiver,
                local_functions,
                local_types,
                module_aliases,
            )?),
            method,
            args: args
                .into_iter()
                .map(|arg| rewrite_expr(arg, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Expr::Call { callee, args } => Ok(Expr::Call {
            callee: Box::new(rewrite_callee(
                *callee,
                local_functions,
                local_types,
                module_aliases,
            )?),
            args: args
                .into_iter()
                .map(|arg| rewrite_expr(arg, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        Expr::Specialize { callee, type_args } => Ok(Expr::Specialize {
            callee: Box::new(rewrite_callee(
                *callee,
                local_functions,
                local_types,
                module_aliases,
            )?),
            type_args: type_args
                .into_iter()
                .map(|ty| rewrite_type(ty, local_types, module_aliases))
                .collect(),
        }),
        Expr::Cast { expr, ty } => Ok(Expr::Cast {
            expr: Box::new(rewrite_expr(
                *expr,
                local_functions,
                local_types,
                module_aliases,
            )?),
            ty: rewrite_type(ty, local_types, module_aliases),
        }),
        Expr::Error { message } => Ok(Expr::Error {
            message: Box::new(rewrite_expr(
                *message,
                local_functions,
                local_types,
                module_aliases,
            )?),
        }),
        Expr::Try(expr) => Ok(Expr::Try(Box::new(rewrite_expr(
            *expr,
            local_functions,
            local_types,
            module_aliases,
        )?))),
        Expr::Unary { op, expr } => Ok(Expr::Unary {
            op,
            expr: Box::new(rewrite_expr(
                *expr,
                local_functions,
                local_types,
                module_aliases,
            )?),
        }),
        Expr::Pack(values) => Ok(Expr::Pack(
            values
                .into_iter()
                .map(|value| rewrite_expr(value, local_functions, local_types, module_aliases))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Expr::Binary { lhs, op, rhs } => Ok(Expr::Binary {
            lhs: Box::new(rewrite_expr(
                *lhs,
                local_functions,
                local_types,
                module_aliases,
            )?),
            op,
            rhs: Box::new(rewrite_expr(
                *rhs,
                local_functions,
                local_types,
                module_aliases,
            )?),
        }),
        Expr::SizeOf(ty) => Ok(Expr::SizeOf(rewrite_type(ty, local_types, module_aliases))),
        Expr::BitCast { expr, ty } => Ok(Expr::BitCast {
            expr: Box::new(rewrite_expr(
                *expr,
                local_functions,
                local_types,
                module_aliases,
            )?),
            ty: rewrite_type(ty, local_types, module_aliases),
        }),
    }
}

fn rewrite_callee(
    callee: Expr,
    local_functions: &HashMap<String, String>,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Result<Expr, CompileError> {
    if let Some(path) = extract_callee_path(&callee) {
        if path.len() == 1 {
            let name = &path[0];
            return Ok(Expr::Path(vec![
                local_functions
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone()),
            ]));
        }
        if let Some(rewritten) = rewrite_constructor_path(&path, local_types, module_aliases) {
            return Ok(Expr::Path(rewritten));
        }
        if let Some(module) = module_aliases.get(&path[0]) {
            USED_MODULE_ALIASES.with(|u| u.borrow_mut().insert(path[0].clone()));
            let member = path[1..].join(".");
            if let Some(ty_name) = module.named_types.get(&member) {
                return Ok(Expr::Path(vec![ty_name.clone()]));
            }
            if let Some(global_name) = module.globals.get(&member) {
                return Ok(Expr::Path(vec![global_name.clone()]));
            }
            let function = module.functions.get(&member).ok_or_else(|| {
                CompileError::new(format!(
                    "module `{}` has no public function or type `{}`",
                    path[0], member
                ))
            })?;
            return Ok(Expr::Path(vec![function.clone()]));
        }
        let qualified = path.join(".");
        if let Some(function) = local_functions.get(&qualified) {
            return Ok(Expr::Path(vec![function.clone()]));
        }
    }
    match callee {
        Expr::FieldAccess { base, field } => rewrite_expr(
            Expr::FieldAccess { base, field },
            local_functions,
            local_types,
            module_aliases,
        ),
        other => rewrite_expr(other, local_functions, local_types, module_aliases),
    }
}

fn rewrite_constructor_path(
    path: &[String],
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Option<Vec<String>> {
    match path {
        [base, variant] => local_types
            .get(base)
            .cloned()
            .map(|mapped| vec![mapped, variant.clone()]),
        [module_alias, type_name, variant] => module_aliases
            .get(module_alias)
            .and_then(|module| module.named_types.get(type_name))
            .cloned()
            .map(|mapped| vec![mapped, variant.clone()]),
        _ => None,
    }
}

fn extract_callee_path(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Path(path) => Some(path.clone()),
        Expr::FieldAccess { base, field } => {
            let mut path = extract_callee_path(base)?;
            path.push(field.clone());
            Some(path)
        }
        _ => None,
    }
}

fn rewrite_type(
    ty: Type,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> Type {
    match ty {
        Type::Named(name) => Type::Named(rewrite_named_type(name, local_types, module_aliases)),
        Type::Applied(name, type_args) => Type::Applied(
            rewrite_named_type(name, local_types, module_aliases),
            type_args
                .into_iter()
                .map(|arg| rewrite_type(arg, local_types, module_aliases))
                .collect(),
        ),
        Type::Result(inner) => {
            Type::Result(Box::new(rewrite_type(*inner, local_types, module_aliases)))
        }
        Type::Mut(inner) => Type::Mut(Box::new(rewrite_type(*inner, local_types, module_aliases))),
        Type::Ref(inner) => Type::Ref(Box::new(rewrite_type(*inner, local_types, module_aliases))),
        Type::List(inner) => {
            Type::List(Box::new(rewrite_type(*inner, local_types, module_aliases)))
        }
        Type::FixedArray(n, inner) => Type::FixedArray(
            n,
            Box::new(rewrite_type(*inner, local_types, module_aliases)),
        ),
        Type::FnPtr(params, ret) => Type::FnPtr(
            params
                .into_iter()
                .map(|p| rewrite_type(p, local_types, module_aliases))
                .collect(),
            Box::new(rewrite_type(*ret, local_types, module_aliases)),
        ),
        Type::U32 => Type::U32,
        other => other,
    }
}

fn rewrite_named_type(
    name: String,
    local_types: &HashMap<String, String>,
    module_aliases: &ModuleAliases,
) -> String {
    if let Some(mapped) = local_types.get(&name) {
        return mapped.clone();
    }
    if let Some((alias, member)) = name.split_once('.') {
        if let Some(module) = module_aliases.get(alias) {
            USED_MODULE_ALIASES.with(|u| u.borrow_mut().insert(alias.to_string()));
            if let Some(mapped) = module.named_types.get(member) {
                return mapped.clone();
            }
            if let Some(mapped) = module.interfaces.get(member) {
                return mapped.clone();
            }
            if let Some(mapped) = module.typesets.get(member) {
                return mapped.clone();
            }
        }
    }
    name
}

fn instantiate_generic_functions(program: Program) -> Result<Program, CompileError> {
    let interface_names = program
        .interface_defs
        .iter()
        .map(|interface_def| interface_def.name.clone())
        .collect::<HashSet<_>>();
    let type_interfaces = program
        .type_defs
        .iter()
        .map(|type_def| {
            (
                type_def.name.clone(),
                type_def
                    .derives
                    .iter()
                    .filter_map(|derive| match derive {
                        Type::Named(name) => Some(name.clone()),
                        _ => None,
                    })
                    .collect::<HashSet<_>>(),
            )
        })
        .collect::<HashMap<_, _>>();
    let mut templates = HashMap::new();
    let mut type_templates = HashMap::new();
    let mut function_returns = HashMap::new();
    let mut concrete_functions = Vec::new();
    let mut concrete_type_defs = Vec::new();
    for function in program.functions {
        if function.generic_params.is_empty() {
            function_returns.insert(function.name.clone(), function.return_type.clone());
            concrete_functions.push(function);
        } else {
            if function.extern_name.is_some() {
                return Err(CompileError::new(format!(
                    "generic extern functions are not supported: `{}`",
                    function.name
                )));
            }
            templates.insert(function.name.clone(), function);
        }
    }
    for type_def in program.type_defs {
        if type_def.generic_params.is_empty() {
            concrete_type_defs.push(type_def);
        } else {
            if type_def.is_extern {
                return Err(CompileError::new(format!(
                    "generic extern types are not supported: `{}`",
                    type_def.name
                )));
            }
            type_templates.insert(type_def.name.clone(), type_def);
        }
    }

    let mut instantiator = GenericInstantiator {
        templates,
        type_templates,
        function_returns,
        types: HashMap::new(),
        function_instantiated_names: HashMap::new(),
        type_instantiated_names: HashMap::new(),
        specialized_types: HashMap::new(),
        generated_functions: Vec::new(),
        generated_types: Vec::new(),
        interface_names,
        type_interfaces,
        type_sets: HashMap::new(),
    };

    let typesets = program
        .typesets
        .into_iter()
        .map(|typeset| instantiator.rewrite_typeset_def(typeset))
        .collect::<Result<Vec<_>, _>>()?;
    let interface_defs = program
        .interface_defs
        .into_iter()
        .map(|interface_def| instantiator.rewrite_interface_def(interface_def))
        .collect::<Result<Vec<_>, _>>()?;
    let type_defs = concrete_type_defs
        .into_iter()
        .map(|type_def| instantiator.rewrite_concrete_type_def(type_def))
        .collect::<Result<Vec<_>, _>>()?;

    let functions = concrete_functions
        .into_iter()
        .map(|function| instantiator.rewrite_function_body(function))
        .collect::<Result<Vec<_>, _>>()?;
    let tests = program
        .tests
        .into_iter()
        .map(|test| instantiator.rewrite_test_body(test))
        .collect::<Result<Vec<_>, _>>()?;

    let mut all_functions = functions;
    all_functions.extend(instantiator.generated_functions);
    let mut all_type_defs = type_defs;
    all_type_defs.extend(instantiator.generated_types);

    Ok(Program {
        module_uses: program.module_uses,
        extern_headers: program.extern_headers,
        link_flags: program.link_flags,
        interface_defs,
        type_defs: all_type_defs,
        typesets,
        enum_defs: program.enum_defs,
        functions: all_functions,
        tests,
        globals: program.globals,
    })
}

struct GenericInstantiator {
    templates: HashMap<String, Function>,
    type_templates: HashMap<String, TypeDef>,
    function_returns: HashMap<String, Type>,
    types: HashMap<String, TypeDef>,
    function_instantiated_names: HashMap<String, String>,
    type_instantiated_names: HashMap<String, String>,
    specialized_types: HashMap<String, (String, Vec<Type>)>,
    generated_functions: Vec<Function>,
    generated_types: Vec<TypeDef>,
    interface_names: HashSet<String>,
    type_interfaces: HashMap<String, HashSet<String>>,
    type_sets: HashMap<String, Vec<Type>>,
}

impl GenericInstantiator {
    fn rewrite_typeset_def(&mut self, mut typeset: TypeSetDef) -> Result<TypeSetDef, CompileError> {
        typeset.members = typeset
            .members
            .into_iter()
            .map(|member| self.rewrite_concrete_type(member))
            .collect::<Result<Vec<_>, _>>()?;
        self.type_sets
            .insert(typeset.name.clone(), typeset.members.clone());
        Ok(typeset)
    }

    fn rewrite_interface_def(
        &mut self,
        mut interface_def: InterfaceDef,
    ) -> Result<InterfaceDef, CompileError> {
        interface_def.methods = interface_def
            .methods
            .into_iter()
            .map(|mut method| {
                method.params = method
                    .params
                    .into_iter()
                    .map(|mut param| {
                        param.ty = self.rewrite_concrete_type(param.ty)?;
                        Ok(param)
                    })
                    .collect::<Result<Vec<_>, CompileError>>()?;
                method.return_type = self.rewrite_concrete_type(method.return_type)?;
                Ok(method)
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        Ok(interface_def)
    }

    fn rewrite_concrete_type_def(
        &mut self,
        mut type_def: TypeDef,
    ) -> Result<TypeDef, CompileError> {
        type_def.alias = type_def
            .alias
            .map(|alias| self.rewrite_concrete_type(alias))
            .transpose()?;
        type_def.derives = type_def
            .derives
            .into_iter()
            .map(|derive| self.rewrite_concrete_type(derive))
            .collect::<Result<Vec<_>, _>>()?;
        type_def.fields = type_def
            .fields
            .into_iter()
            .map(|mut field| {
                field.ty = self.rewrite_concrete_type(field.ty)?;
                Ok(field)
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        type_def.variants = type_def
            .variants
            .into_iter()
            .map(|mut variant| {
                variant.payload_types = variant
                    .payload_types
                    .into_iter()
                    .map(|payload| self.rewrite_concrete_type(payload))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(variant)
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        self.register_concrete_type(&type_def);
        Ok(type_def)
    }

    fn register_concrete_type(&mut self, type_def: &TypeDef) {
        self.types.insert(type_def.name.clone(), type_def.clone());
        self.type_interfaces.insert(
            type_def.name.clone(),
            type_def
                .derives
                .iter()
                .filter_map(|derive| match derive {
                    Type::Named(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
        );
    }

    fn rewrite_concrete_type(&mut self, ty: Type) -> Result<Type, CompileError> {
        match ty {
            Type::Applied(name, type_args) => {
                let resolved_type_args = type_args
                    .into_iter()
                    .map(|type_arg| self.rewrite_concrete_type(type_arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type::Named(self.instantiate_type_specialization(
                    &name,
                    &resolved_type_args,
                )?))
            }
            Type::Named(name) => {
                if self.type_templates.contains_key(&name) {
                    Err(CompileError::new(format!(
                        "generic type `{name}` requires explicit type arguments"
                    )))
                } else {
                    Ok(Type::Named(name))
                }
            }
            Type::Result(inner) => Ok(Type::Result(Box::new(self.rewrite_concrete_type(*inner)?))),
            Type::Mut(inner) => Ok(Type::Mut(Box::new(self.rewrite_concrete_type(*inner)?))),
            Type::Ref(inner) => Ok(Type::Ref(Box::new(self.rewrite_concrete_type(*inner)?))),
            Type::List(inner) => Ok(Type::List(Box::new(self.rewrite_concrete_type(*inner)?))),
            Type::FixedArray(n, inner) => Ok(Type::FixedArray(
                n,
                Box::new(self.rewrite_concrete_type(*inner)?),
            )),
            Type::FnPtr(params, ret) => Ok(Type::FnPtr(
                params
                    .into_iter()
                    .map(|p| self.rewrite_concrete_type(p))
                    .collect::<Result<Vec<_>, _>>()?,
                Box::new(self.rewrite_concrete_type(*ret)?),
            )),
            other => Ok(other),
        }
    }

    fn instantiate_type_specialization(
        &mut self,
        name: &str,
        type_args: &[Type],
    ) -> Result<String, CompileError> {
        let template = self
            .type_templates
            .get(name)
            .cloned()
            .ok_or_else(|| CompileError::new(format!("unknown generic type `{name}`")))?;
        if template.generic_params.len() != type_args.len() {
            return Err(CompileError::new(format!(
                "generic type `{}` expects {} type arguments but received {}",
                template.name,
                template.generic_params.len(),
                type_args.len()
            )));
        }

        for (param, type_arg) in template.generic_params.iter().zip(type_args.iter()) {
            if !param.constraints.is_empty()
                && !param
                    .constraints
                    .iter()
                    .any(|allowed| self.constraint_matches(allowed, type_arg))
            {
                return Err(CompileError::new(format!(
                    "generic parameter `{}` on `{}` does not allow type {}",
                    param.name,
                    template.name,
                    describe_type(type_arg)
                )));
            }
        }

        let key = specialization_key(name, type_args);
        if let Some(existing) = self.type_instantiated_names.get(&key) {
            return Ok(existing.clone());
        }

        let specialized_name = format!(
            "{}__generic__{}",
            template.name,
            specialization_suffix(type_args)
        );
        self.type_instantiated_names
            .insert(key, specialized_name.clone());
        self.specialized_types.insert(
            specialized_name.clone(),
            (template.name.clone(), type_args.to_vec()),
        );

        let substitutions = template
            .generic_params
            .iter()
            .zip(type_args.iter())
            .map(|(param, type_arg)| (param.name.clone(), type_arg.clone()))
            .collect::<HashMap<_, _>>();

        let mut specialized = template.clone();
        specialized.name = specialized_name.clone();
        specialized.generic_params.clear();
        specialized.alias = specialized
            .alias
            .map(|alias| self.rewrite_concrete_type(substitute_type(alias, &substitutions)))
            .transpose()?;
        specialized.derives = specialized
            .derives
            .into_iter()
            .map(|derive| self.rewrite_concrete_type(substitute_type(derive, &substitutions)))
            .collect::<Result<Vec<_>, _>>()?;
        specialized.fields = specialized
            .fields
            .into_iter()
            .map(|field| {
                Ok(FieldDef {
                    name: field.name,
                    ty: self.rewrite_concrete_type(substitute_type(field.ty, &substitutions))?,
                    line: field.line,
                    column: field.column,
                })
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        specialized.variants = specialized
            .variants
            .into_iter()
            .map(|variant| {
                Ok(UnionVariantDef {
                    name: variant.name,
                    payload_types: variant
                        .payload_types
                        .into_iter()
                        .map(|payload| {
                            self.rewrite_concrete_type(substitute_type(payload, &substitutions))
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                })
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        self.register_concrete_type(&specialized);
        self.generated_types.push(specialized);

        Ok(specialized_name)
    }

    fn rewrite_function_body(&mut self, mut function: Function) -> Result<Function, CompileError> {
        function.params = function
            .params
            .into_iter()
            .map(|mut param| {
                param.ty = self.rewrite_concrete_type(param.ty)?;
                Ok(param)
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        function.return_type = self.rewrite_concrete_type(function.return_type)?;
        let mut scope = function
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect::<HashMap<_, _>>();
        function.body = function
            .body
            .into_iter()
            .map(|stmt| self.rewrite_stmt_generics(stmt, &mut scope))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(function)
    }

    fn rewrite_test_body(&mut self, mut test: TestBlock) -> Result<TestBlock, CompileError> {
        let mut scope = HashMap::new();
        test.body = test
            .body
            .into_iter()
            .map(|stmt| self.rewrite_stmt_generics(stmt, &mut scope))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(test)
    }

    fn rewrite_stmt_generics(
        &mut self,
        stmt: Stmt,
        scope: &mut HashMap<String, Type>,
    ) -> Result<Stmt, CompileError> {
        Ok(match stmt {
            Stmt::VarDecl {
                line,
                column,
                mutable,
                name,
                declared_type,
                init,
            } => {
                let init = self.rewrite_expr_generics(init, scope)?;
                let declared_type = declared_type
                    .map(|ty| self.rewrite_concrete_type(ty))
                    .transpose()?;
                let binding_ty = match &declared_type {
                    Some(ty) => ty.clone(),
                    None => self.infer_expr_type(&init, scope).ok_or_else(|| {
                        CompileError::new(format!(
                            "cannot infer local type for `{name}` during generic rewriting"
                        ))
                    })?,
                };
                scope.insert(name.clone(), binding_ty);
                Stmt::VarDecl {
                    line,
                    column,
                    mutable,
                    name,
                    declared_type,
                    init,
                }
            }
            Stmt::Assign {
                line,
                column,
                target,
                value,
            } => Stmt::Assign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::AddAssign {
                line,
                column,
                target,
                value,
            } => Stmt::AddAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::MulAssign {
                line,
                column,
                target,
                value,
            } => Stmt::MulAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::SubAssign {
                line,
                column,
                target,
                value,
            } => Stmt::SubAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::DivAssign {
                line,
                column,
                target,
                value,
            } => Stmt::DivAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::BitAndAssign {
                line,
                column,
                target,
                value,
            } => Stmt::BitAndAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::BitOrAssign {
                line,
                column,
                target,
                value,
            } => Stmt::BitOrAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::BitXorAssign {
                line,
                column,
                target,
                value,
            } => Stmt::BitXorAssign {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
                value: self.rewrite_expr_generics(value, scope)?,
            },
            Stmt::Increment {
                line,
                column,
                target,
            } => Stmt::Increment {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
            },
            Stmt::Decrement {
                line,
                column,
                target,
            } => Stmt::Decrement {
                line,
                column,
                target: self.rewrite_expr_generics(target, scope)?,
            },
            Stmt::Assert {
                line,
                column,
                condition,
            } => Stmt::Assert {
                line,
                column,
                condition: self.rewrite_expr_generics(condition, scope)?,
            },
            Stmt::Return {
                line,
                column,
                value,
            } => Stmt::Return {
                line,
                column,
                value: value
                    .map(|expr| self.rewrite_expr_generics(expr, scope))
                    .transpose()?,
            },
            Stmt::If {
                line,
                column,
                condition,
                then_body,
                else_body,
            } => Stmt::If {
                line,
                column,
                condition: self.rewrite_expr_generics(condition, scope)?,
                then_body: {
                    let mut nested = scope.clone();
                    then_body
                        .into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
                else_body: {
                    let mut nested = scope.clone();
                    else_body
                        .into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
            Stmt::Match {
                line,
                column,
                expr,
                arms,
            } => {
                let expr = self.rewrite_expr_generics(expr, scope)?;
                let matched_ty = self.infer_expr_type(&expr, scope);
                Stmt::Match {
                    line,
                    column,
                    expr,
                    arms: arms
                        .into_iter()
                        .map(|arm| {
                            let mut nested = scope.clone();
                            for (name, ty) in self.infer_match_arm_bindings(
                                matched_ty.as_ref(),
                                &arm.kind,
                                &arm.bindings,
                            ) {
                                nested.insert(name, ty);
                            }
                            Ok(crate::ast::MatchArm {
                                kind: arm.kind,
                                bindings: arm.bindings,
                                body: arm
                                    .body
                                    .into_iter()
                                    .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                                    .collect::<Result<Vec<_>, _>>()?,
                            })
                        })
                        .collect::<Result<Vec<_>, CompileError>>()?,
                }
            }
            Stmt::Block(body) => Stmt::Block(
                body.into_iter()
                    .map(|stmt| self.rewrite_stmt_generics(stmt, scope))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Stmt::Expr { line, column, expr } => Stmt::Expr {
                line,
                column,
                expr: self.rewrite_expr_generics(expr, scope)?,
            },
            Stmt::ForRange {
                line,
                column,
                pragma,
                var_name,
                start,
                end,
                body,
            } => Stmt::ForRange {
                line,
                column,
                pragma,
                var_name: var_name.clone(),
                start: self.rewrite_expr_generics(start, scope)?,
                end: self.rewrite_expr_generics(end, scope)?,
                body: {
                    let mut nested = scope.clone();
                    nested.insert(var_name.clone(), Type::I32);
                    body.into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
            Stmt::ForEach {
                line,
                column,
                var_name,
                iterable,
                body,
            } => {
                let iterable = self.rewrite_expr_generics(iterable, scope)?;
                Stmt::ForEach {
                    line,
                    column,
                    var_name: var_name.clone(),
                    iterable: iterable.clone(),
                    body: {
                        let mut nested = scope.clone();
                        if let Some(iterable_ty) = self.infer_expr_type(&iterable, scope) {
                            if let Type::List(inner) = iterable_ty {
                                nested.insert(var_name.clone(), *inner);
                            }
                        }
                        body.into_iter()
                            .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                            .collect::<Result<Vec<_>, _>>()?
                    },
                }
            }
            Stmt::ForClassic {
                line,
                column,
                pragma,
                var_name,
                init,
                condition,
                increment,
                body,
            } => Stmt::ForClassic {
                line,
                column,
                pragma,
                var_name: var_name.clone(),
                init: self.rewrite_expr_generics(init.clone(), scope)?,
                condition: self.rewrite_expr_generics(condition, scope)?,
                increment: self.rewrite_expr_generics(increment, scope)?,
                body: {
                    let mut nested = scope.clone();
                    if let Some(init_ty) = self.infer_expr_type(&init, scope) {
                        nested.insert(var_name.clone(), init_ty);
                    }
                    body.into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
            Stmt::While {
                line,
                column,
                condition,
                body,
            } => Stmt::While {
                line,
                column,
                condition: self.rewrite_expr_generics(condition, scope)?,
                body: {
                    let mut nested = scope.clone();
                    body.into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
            Stmt::Loop { line, column, body } => Stmt::Loop {
                line,
                column,
                body: {
                    let mut nested = scope.clone();
                    body.into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
            Stmt::Continue { line, column } => Stmt::Continue { line, column },
            Stmt::Break { line, column } => Stmt::Break { line, column },
            Stmt::Defer { line, column, body } => Stmt::Defer {
                line,
                column,
                body: {
                    let mut nested = scope.clone();
                    body.into_iter()
                        .map(|stmt| self.rewrite_stmt_generics(stmt, &mut nested))
                        .collect::<Result<Vec<_>, _>>()?
                },
            },
        })
    }

    fn rewrite_expr_generics(
        &mut self,
        expr: Expr,
        scope: &HashMap<String, Type>,
    ) -> Result<Expr, CompileError> {
        Ok(match expr {
            Expr::ListLiteral(values) => Expr::ListLiteral(
                values
                    .into_iter()
                    .map(|value| self.rewrite_expr_generics(value, scope))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(self.rewrite_expr_generics(*base, scope)?),
                index: Box::new(self.rewrite_expr_generics(*index, scope)?),
            },
            Expr::FieldAccess { base, field } => Expr::FieldAccess {
                base: Box::new(self.rewrite_expr_generics(*base, scope)?),
                field,
            },
            Expr::StructInit {
                name,
                type_args,
                fields,
            } => {
                let resolved_type_args = type_args
                    .into_iter()
                    .map(|ty| self.rewrite_concrete_type(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                Expr::StructInit {
                    name: if resolved_type_args.is_empty() {
                        if self.type_templates.contains_key(&name) {
                            return Err(CompileError::new(format!(
                                "generic type `{name}` requires explicit type arguments"
                            )));
                        }
                        name
                    } else {
                        self.instantiate_type_specialization(&name, &resolved_type_args)?
                    },
                    type_args: Vec::new(),
                    fields: fields
                        .into_iter()
                        .map(|field| {
                            Ok(FieldInit {
                                name: field.name,
                                value: self.rewrite_expr_generics(field.value, scope)?,
                            })
                        })
                        .collect::<Result<Vec<_>, CompileError>>()?,
                }
            }
            Expr::BuiltinCall { name, args } => Expr::BuiltinCall {
                name,
                args: args
                    .into_iter()
                    .map(|arg| self.rewrite_expr_generics(arg, scope))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expr::MethodCall {
                receiver,
                method,
                args,
            } => Expr::MethodCall {
                receiver: Box::new(self.rewrite_expr_generics(*receiver, scope)?),
                method,
                args: args
                    .into_iter()
                    .map(|arg| self.rewrite_expr_generics(arg, scope))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expr::Call { callee, args } => {
                let callee = self.rewrite_expr_generics(*callee, scope)?;
                let args = args
                    .into_iter()
                    .map(|arg| self.rewrite_expr_generics(arg, scope))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Expr::Specialize { callee, type_args } = callee {
                    let Some(path) = extract_callee_path(&callee) else {
                        return Err(CompileError::new(
                            "generic specialization currently requires a direct function name",
                        ));
                    };
                    let specialized =
                        self.instantiate_specialization(&path.join("."), &type_args, &args, scope)?;
                    Expr::Call {
                        callee: Box::new(Expr::Path(vec![specialized])),
                        args,
                    }
                } else {
                    Expr::Call {
                        callee: Box::new(callee),
                        args,
                    }
                }
            }
            Expr::Specialize { callee, type_args } => Expr::Specialize {
                callee: Box::new(self.rewrite_expr_generics(*callee, scope)?),
                type_args: type_args
                    .into_iter()
                    .map(|ty| self.rewrite_concrete_type(ty))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Expr::Cast { expr, ty } => Expr::Cast {
                expr: Box::new(self.rewrite_expr_generics(*expr, scope)?),
                ty: self.rewrite_concrete_type(ty)?,
            },
            Expr::Error { message } => Expr::Error {
                message: Box::new(self.rewrite_expr_generics(*message, scope)?),
            },
            Expr::Try(expr) => Expr::Try(Box::new(self.rewrite_expr_generics(*expr, scope)?)),
            Expr::Unary { op, expr } => Expr::Unary {
                op,
                expr: Box::new(self.rewrite_expr_generics(*expr, scope)?),
            },
            Expr::Pack(values) => Expr::Pack(
                values
                    .into_iter()
                    .map(|value| self.rewrite_expr_generics(value, scope))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Expr::Binary { lhs, op, rhs } => Expr::Binary {
                lhs: Box::new(self.rewrite_expr_generics(*lhs, scope)?),
                op,
                rhs: Box::new(self.rewrite_expr_generics(*rhs, scope)?),
            },
            Expr::SizeOf(ty) => Expr::SizeOf(self.rewrite_concrete_type(ty)?),
            Expr::BitCast { expr, ty } => Expr::BitCast {
                expr: Box::new(self.rewrite_expr_generics(*expr, scope)?),
                ty: self.rewrite_concrete_type(ty)?,
            },
            other => other,
        })
    }

    fn instantiate_specialization(
        &mut self,
        name: &str,
        type_args: &[Type],
        args: &[Expr],
        scope: &HashMap<String, Type>,
    ) -> Result<String, CompileError> {
        let template = self
            .templates
            .get(name)
            .cloned()
            .ok_or_else(|| CompileError::new(format!("unknown generic function `{name}`")))?;
        if template.generic_params.len() != type_args.len() {
            return Err(CompileError::new(format!(
                "generic function `{}` expects {} type arguments but received {}",
                template.name,
                template.generic_params.len(),
                type_args.len()
            )));
        }

        let mut substitutions = HashMap::new();
        for (param, type_arg) in template.generic_params.iter().zip(type_args.iter()) {
            if *type_arg != Type::Infer {
                substitutions.insert(param.name.clone(), type_arg.clone());
            }
        }

        if template.params.len() == args.len() {
            for (param, arg) in template.params.iter().zip(args.iter()) {
                let Some(actual_ty) = self.infer_expr_type(arg, scope) else {
                    continue;
                };
                self.infer_substitutions_from_types(
                    &param.ty,
                    &actual_ty,
                    &template.generic_params,
                    &mut substitutions,
                );
            }
        }

        for param in &template.generic_params {
            if !substitutions.contains_key(&param.name) {
                return Err(CompileError::new(
                    "cannot infer type from type argument, specify it manually.",
                ));
            }
            let type_arg = substitutions.get(&param.name).expect("checked above");
            if !param.constraints.is_empty()
                && !param
                    .constraints
                    .iter()
                    .any(|allowed| self.constraint_matches(allowed, type_arg))
            {
                return Err(CompileError::new(format!(
                    "generic parameter `{}` on `{}` does not allow type {}",
                    param.name,
                    template.name,
                    describe_type(type_arg)
                )));
            }
        }

        let resolved_type_args = template
            .generic_params
            .iter()
            .map(|param| {
                substitutions
                    .get(&param.name)
                    .cloned()
                    .expect("checked above")
            })
            .collect::<Vec<_>>();

        let key = specialization_key(name, &resolved_type_args);
        if let Some(existing) = self.function_instantiated_names.get(&key) {
            return Ok(existing.clone());
        }

        let specialized_name = format!(
            "{}__generic__{}",
            template.name,
            specialization_suffix(&resolved_type_args)
        );
        self.function_instantiated_names
            .insert(key, specialized_name.clone());

        let mut specialized = template.clone();
        specialized.name = specialized_name.clone();
        specialized.generic_params.clear();
        specialized.params = specialized
            .params
            .into_iter()
            .map(|param| {
                Ok(crate::ast::Param {
                    name: param.name,
                    ty: self.rewrite_concrete_type(substitute_type(param.ty, &substitutions))?,
                    line: param.line,
                    column: param.column,
                })
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        specialized.return_type =
            self.rewrite_concrete_type(substitute_type(specialized.return_type, &substitutions))?;
        if specialized.return_type == Type::Void {
            if let Some(inferred) = infer_implicit_return_type(&specialized, &substitutions) {
                specialized.return_type = self.rewrite_concrete_type(inferred)?;
            }
        }
        specialized.body = specialized
            .body
            .into_iter()
            .map(|stmt| substitute_stmt(stmt, &substitutions))
            .collect();
        specialized = self.rewrite_function_body(specialized)?;
        self.function_returns
            .insert(specialized.name.clone(), specialized.return_type.clone());
        self.generated_functions.push(specialized);

        Ok(specialized_name)
    }

    fn infer_substitutions_from_types(
        &self,
        template_ty: &Type,
        actual_ty: &Type,
        generic_params: &[GenericParam],
        substitutions: &mut HashMap<String, Type>,
    ) {
        match template_ty {
            Type::Named(name) => {
                if generic_params.iter().any(|param| param.name == *name) {
                    substitutions
                        .entry(name.clone())
                        .or_insert_with(|| actual_ty.clone());
                }
            }
            Type::Applied(name, type_args) => match actual_ty {
                Type::Named(actual_name) => {
                    if let Some((actual_template, actual_type_args)) =
                        self.specialized_types.get(actual_name)
                    {
                        if actual_template == name && actual_type_args.len() == type_args.len() {
                            for (template_arg, actual_arg) in
                                type_args.iter().zip(actual_type_args.iter())
                            {
                                self.infer_substitutions_from_types(
                                    template_arg,
                                    actual_arg,
                                    generic_params,
                                    substitutions,
                                );
                            }
                        }
                    }
                }
                Type::Applied(actual_name, actual_type_args)
                    if actual_name == name && actual_type_args.len() == type_args.len() =>
                {
                    for (template_arg, actual_arg) in type_args.iter().zip(actual_type_args.iter())
                    {
                        self.infer_substitutions_from_types(
                            template_arg,
                            actual_arg,
                            generic_params,
                            substitutions,
                        );
                    }
                }
                _ => {}
            },
            Type::Mut(inner) => {
                if let Type::Mut(actual_inner) = actual_ty {
                    self.infer_substitutions_from_types(
                        inner,
                        actual_inner,
                        generic_params,
                        substitutions,
                    );
                }
            }
            Type::Ref(inner) => {
                if let Type::Ref(actual_inner) = actual_ty {
                    self.infer_substitutions_from_types(
                        inner,
                        actual_inner,
                        generic_params,
                        substitutions,
                    );
                }
            }
            Type::List(inner) => {
                if let Type::List(actual_inner) = actual_ty {
                    self.infer_substitutions_from_types(
                        inner,
                        actual_inner,
                        generic_params,
                        substitutions,
                    );
                }
            }
            Type::Result(inner) => {
                if let Type::Result(actual_inner) = actual_ty {
                    self.infer_substitutions_from_types(
                        inner,
                        actual_inner,
                        generic_params,
                        substitutions,
                    );
                }
            }
            _ => {}
        }
    }

    fn infer_expr_type(&self, expr: &Expr, scope: &HashMap<String, Type>) -> Option<Type> {
        match expr {
            Expr::Int(_) => Some(Type::I32),
            Expr::Char(_) => Some(Type::U8),
            Expr::Bool(_) => Some(Type::Bool),
            Expr::Float(_) => Some(Type::F32),
            Expr::String(_) => Some(Type::Ref(Box::new(Type::U8))),
            Expr::None => Some(Type::None),
            Expr::Path(path) => {
                if path.len() == 1 {
                    scope.get(&path[0]).cloned()
                } else {
                    self.function_returns.get(&path.join(".")).cloned()
                }
            }
            Expr::ListLiteral(values) => {
                let first = self.infer_expr_type(values.first()?, scope)?;
                if values
                    .iter()
                    .skip(1)
                    .all(|value| self.infer_expr_type(value, scope) == Some(first.clone()))
                {
                    Some(Type::List(Box::new(first)))
                } else {
                    None
                }
            }
            Expr::Index { base, .. } => match self.infer_expr_type(base, scope)? {
                Type::List(inner) => Some(*inner),
                _ => None,
            },
            Expr::FieldAccess { base, field } => {
                let base_ty = self.infer_expr_type(base, scope)?;
                self.infer_field_type(&base_ty, field)
            }
            Expr::StructInit { name, .. } => Some(Type::Named(name.clone())),
            Expr::BuiltinCall { name, args } => self.infer_builtin_type(name, args, scope),
            Expr::MethodCall { .. } => None,
            Expr::Call { callee, .. } => {
                let path = self.extract_expr_path(callee)?;
                if let Some(return_ty) = self.function_returns.get(&path.join(".")) {
                    Some(return_ty.clone())
                } else {
                    match path.as_slice() {
                        [name] => self.types.get(name).map(|_| Type::Named(name.clone())),
                        [union_name, variant_name] => {
                            self.types.get(union_name).and_then(|type_def| {
                                (type_def.kind == TypeDefKind::Union
                                    && type_def
                                        .variants
                                        .iter()
                                        .any(|variant| variant.name == *variant_name))
                                .then(|| Type::Named(union_name.clone()))
                            })
                        }
                        _ => None,
                    }
                }
            }
            Expr::Specialize { .. } => None,
            Expr::Cast { ty, .. } => Some(ty.clone()),
            Expr::SizeOf(_) => Some(Type::Usize),
            Expr::BitCast { ty, .. } => Some(ty.clone()),
            Expr::Error { .. } => Some(Type::Error),
            Expr::Try(inner) => match self.infer_expr_type(inner, scope)? {
                Type::Result(inner) => Some(*inner),
                _ => None,
            },
            Expr::Unary { op, expr } => {
                let inner = self.infer_expr_type(expr, scope)?;
                match op {
                    UnaryOp::LogicalNot => Some(Type::Bool),
                    _ => Some(inner),
                }
            }
            Expr::Pack(_) => None,
            Expr::Binary { lhs, op, rhs } => {
                let lhs_ty = self.infer_expr_type(lhs, scope)?;
                let rhs_ty = self.infer_expr_type(rhs, scope)?;
                match op {
                    BinaryOp::Add
                    | BinaryOp::Subtract
                    | BinaryOp::Divide
                    | BinaryOp::Multiply
                    | BinaryOp::Modulo
                    | BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                        if lhs_ty == rhs_ty =>
                    {
                        Some(lhs_ty)
                    }
                    BinaryOp::Add
                    | BinaryOp::Subtract
                    | BinaryOp::Divide
                    | BinaryOp::Multiply
                    | BinaryOp::Modulo
                    | BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                        if rhs_ty == Type::I32 =>
                    {
                        Some(lhs_ty)
                    }
                    BinaryOp::Add
                    | BinaryOp::Subtract
                    | BinaryOp::Divide
                    | BinaryOp::Multiply
                    | BinaryOp::Modulo
                    | BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                        if lhs_ty == Type::I32 =>
                    {
                        Some(rhs_ty)
                    }
                    BinaryOp::ShiftLeft | BinaryOp::ShiftRight => Some(lhs_ty),
                    BinaryOp::LessThan
                    | BinaryOp::LessEqual
                    | BinaryOp::GreaterThan
                    | BinaryOp::GreaterEqual
                    | BinaryOp::Equal
                    | BinaryOp::NotEqual
                    | BinaryOp::LogicalAnd
                    | BinaryOp::LogicalOr => Some(Type::Bool),
                    _ => None,
                }
            }
        }
    }

    fn infer_match_arm_bindings(
        &self,
        matched_ty: Option<&Type>,
        kind: &MatchArmKind,
        bindings: &[Option<String>],
    ) -> Vec<(String, Type)> {
        match (matched_ty, kind) {
            (Some(Type::Result(ok_ty)), MatchArmKind::Ok) if bindings.len() == 1 => bindings[0]
                .clone()
                .map(|name| vec![(name, (**ok_ty).clone())])
                .unwrap_or_default(),
            (Some(Type::Result(_)), MatchArmKind::Error) if bindings.len() == 1 => bindings[0]
                .clone()
                .map(|name| vec![(name, Type::Ref(Box::new(Type::U8)))])
                .unwrap_or_default(),
            (Some(Type::Named(union_name)), MatchArmKind::Variant(variant_name)) => {
                let bare_variant = variant_name.rsplit('.').next().unwrap_or(variant_name);
                self.types
                    .get(union_name)
                    .filter(|type_def| type_def.kind == TypeDefKind::Union)
                    .and_then(|type_def| {
                        type_def
                            .variants
                            .iter()
                            .find(|variant| variant.name == bare_variant)
                    })
                    .map(|variant| {
                        bindings
                            .iter()
                            .zip(variant.payload_types.iter())
                            .filter_map(|(binding, ty)| {
                                binding.clone().map(|name| (name, ty.clone()))
                            })
                            .collect()
                    })
                    .unwrap_or_default()
            }
            _ => Vec::new(),
        }
    }

    fn infer_builtin_type(
        &self,
        name: &str,
        args: &[Expr],
        scope: &HashMap<String, Type>,
    ) -> Option<Type> {
        match name {
            "puts" | "print" | "free" | "memcpy" => Some(Type::Void),
            "args" => Some(Type::List(Box::new(Type::Ref(Box::new(Type::U8))))),
            "alloc" | "realloc" => Some(Type::Mut(Box::new(Type::Ref(Box::new(Type::U8))))),
            "addr" => Some(Type::Ref(Box::new(
                self.infer_expr_type(args.first()?, scope)?,
            ))),
            "as_mut" => Some(Type::Mut(Box::new(
                self.infer_expr_type(args.first()?, scope)?,
            ))),
            "add" => Some(pointer_arithmetic_type(
                &self.infer_expr_type(args.first()?, scope)?,
            )),
            "deref" => match self.infer_expr_type(args.first()?, scope)? {
                Type::Ref(inner) | Type::Mut(inner) => Some(*inner),
                _ => None,
            },
            _ => None,
        }
    }

    fn infer_field_type(&self, base_ty: &Type, field: &str) -> Option<Type> {
        match self.resolve_aliases(base_ty) {
            Type::Named(name) => self
                .types
                .get(&name)
                .and_then(|type_def| {
                    type_def
                        .fields
                        .iter()
                        .find(|field_def| field_def.name == field)
                        .map(|field_def| field_def.ty.clone())
                })
                .or_else(|| {
                    self.types.get(&name).and_then(|type_def| {
                        type_def
                            .alias
                            .as_ref()
                            .and_then(|alias| self.infer_field_type(alias, field))
                    })
                }),
            other => match deref_type_refs(&other) {
                Type::Named(name) => self.types.get(name).and_then(|type_def| {
                    type_def
                        .fields
                        .iter()
                        .find(|field_def| field_def.name == field)
                        .map(|field_def| field_def.ty.clone())
                }),
                _ => None,
            },
        }
    }

    fn resolve_aliases(&self, ty: &Type) -> Type {
        match ty {
            Type::Named(name) => self
                .types
                .get(name)
                .and_then(|type_def| type_def.alias.as_ref())
                .map(|alias| self.resolve_aliases(alias))
                .unwrap_or_else(|| Type::Named(name.clone())),
            Type::Applied(name, type_args) => Type::Applied(
                name.clone(),
                type_args
                    .iter()
                    .map(|type_arg| self.resolve_aliases(type_arg))
                    .collect(),
            ),
            Type::Result(inner) => Type::Result(Box::new(self.resolve_aliases(inner))),
            Type::Mut(inner) => Type::Mut(Box::new(self.resolve_aliases(inner))),
            Type::Ref(inner) => Type::Ref(Box::new(self.resolve_aliases(inner))),
            Type::List(inner) => Type::List(Box::new(self.resolve_aliases(inner))),
            other => other.clone(),
        }
    }

    fn extract_expr_path(&self, expr: &Expr) -> Option<Vec<String>> {
        match expr {
            Expr::Path(path) => Some(path.clone()),
            Expr::FieldAccess { base, field } => {
                let mut path = self.extract_expr_path(base)?;
                path.push(field.clone());
                Some(path)
            }
            _ => None,
        }
    }

    fn constraint_matches(&self, constraint: &Type, type_arg: &Type) -> bool {
        let unwrapped = unwrap_ref_mut(type_arg);
        if constraint == type_arg || *constraint == unwrapped {
            return true;
        }
        if let Type::Named(typeset_name) = constraint {
            if let Some(members) = self.type_sets.get(typeset_name) {
                return members
                    .iter()
                    .any(|member| member == type_arg || *member == unwrapped);
            }
        }
        match (constraint, &unwrapped) {
            (Type::Named(interface_name), Type::Named(type_name))
                if self.interface_names.contains(interface_name) =>
            {
                self.type_interfaces
                    .get(type_name)
                    .is_some_and(|interfaces| interfaces.contains(interface_name))
            }
            _ => false,
        }
    }
}

fn unwrap_ref_mut(ty: &Type) -> Type {
    match ty {
        Type::Ref(inner) | Type::Mut(inner) => (**inner).clone(),
        _ => ty.clone(),
    }
}

fn substitute_stmt(stmt: Stmt, substitutions: &HashMap<String, Type>) -> Stmt {
    match stmt {
        Stmt::VarDecl {
            line,
            column,
            mutable,
            name,
            declared_type,
            init,
        } => Stmt::VarDecl {
            line,
            column,
            mutable,
            name,
            declared_type: declared_type.map(|ty| substitute_type(ty, substitutions)),
            init: substitute_expr(init, substitutions),
        },
        Stmt::Assign {
            line,
            column,
            target,
            value,
        } => Stmt::Assign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::AddAssign {
            line,
            column,
            target,
            value,
        } => Stmt::AddAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::MulAssign {
            line,
            column,
            target,
            value,
        } => Stmt::MulAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::SubAssign {
            line,
            column,
            target,
            value,
        } => Stmt::SubAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::DivAssign {
            line,
            column,
            target,
            value,
        } => Stmt::DivAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::BitAndAssign {
            line,
            column,
            target,
            value,
        } => Stmt::BitAndAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::BitOrAssign {
            line,
            column,
            target,
            value,
        } => Stmt::BitOrAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::BitXorAssign {
            line,
            column,
            target,
            value,
        } => Stmt::BitXorAssign {
            line,
            column,
            target: substitute_expr(target, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::Increment {
            line,
            column,
            target,
        } => Stmt::Increment {
            line,
            column,
            target: substitute_expr(target, substitutions),
        },
        Stmt::Decrement {
            line,
            column,
            target,
        } => Stmt::Decrement {
            line,
            column,
            target: substitute_expr(target, substitutions),
        },
        Stmt::Assert {
            line,
            column,
            condition,
        } => Stmt::Assert {
            line,
            column,
            condition: substitute_expr(condition, substitutions),
        },
        Stmt::Return {
            line,
            column,
            value,
        } => Stmt::Return {
            line,
            column,
            value: value.map(|expr| substitute_expr(expr, substitutions)),
        },
        Stmt::If {
            line,
            column,
            condition,
            then_body,
            else_body,
        } => Stmt::If {
            line,
            column,
            condition: substitute_expr(condition, substitutions),
            then_body: then_body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
            else_body: else_body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::Match {
            line,
            column,
            expr,
            arms,
        } => Stmt::Match {
            line,
            column,
            expr: substitute_expr(expr, substitutions),
            arms: arms
                .into_iter()
                .map(|arm| crate::ast::MatchArm {
                    kind: arm.kind,
                    bindings: arm.bindings,
                    body: arm
                        .body
                        .into_iter()
                        .map(|stmt| substitute_stmt(stmt, substitutions))
                        .collect(),
                })
                .collect(),
        },
        Stmt::Block(body) => Stmt::Block(
            body.into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        ),
        Stmt::Expr { line, column, expr } => Stmt::Expr {
            line,
            column,
            expr: substitute_expr(expr, substitutions),
        },
        Stmt::ForRange {
            line,
            column,
            pragma,
            var_name,
            start,
            end,
            body,
        } => Stmt::ForRange {
            line,
            column,
            pragma,
            var_name,
            start: substitute_expr(start, substitutions),
            end: substitute_expr(end, substitutions),
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::ForEach {
            line,
            column,
            var_name,
            iterable,
            body,
        } => Stmt::ForEach {
            line,
            column,
            var_name,
            iterable: substitute_expr(iterable, substitutions),
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::While {
            line,
            column,
            condition,
            body,
        } => Stmt::While {
            line,
            column,
            condition: substitute_expr(condition, substitutions),
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::Loop { line, column, body } => Stmt::Loop {
            line,
            column,
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::ForClassic {
            line,
            column,
            pragma,
            var_name,
            init,
            condition,
            increment,
            body,
        } => Stmt::ForClassic {
            line,
            column,
            pragma,
            var_name,
            init: substitute_expr(init, substitutions),
            condition: substitute_expr(condition, substitutions),
            increment: substitute_expr(increment, substitutions),
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
        Stmt::Continue { line, column } => Stmt::Continue { line, column },
        Stmt::Break { line, column } => Stmt::Break { line, column },
        Stmt::Defer { line, column, body } => Stmt::Defer {
            line,
            column,
            body: body
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
        },
    }
}

fn substitute_expr(expr: Expr, substitutions: &HashMap<String, Type>) -> Expr {
    match expr {
        Expr::Bool(value) => Expr::Bool(value),
        Expr::Char(value) => Expr::Char(value),
        Expr::Path(path) => {
            if path.len() == 1 {
                if let Some(Type::Named(name)) = substitutions.get(&path[0]) {
                    return Expr::Path(vec![name.clone()]);
                }
            }
            Expr::Path(path)
        }
        Expr::ListLiteral(values) => Expr::ListLiteral(
            values
                .into_iter()
                .map(|value| substitute_expr(value, substitutions))
                .collect(),
        ),
        Expr::Index { base, index } => Expr::Index {
            base: Box::new(substitute_expr(*base, substitutions)),
            index: Box::new(substitute_expr(*index, substitutions)),
        },
        Expr::FieldAccess { base, field } => {
            if let Expr::Path(path) = base.as_ref() {
                if path.len() == 1 {
                    if let Some(Type::Named(type_name)) = substitutions.get(&path[0]) {
                        return Expr::Path(vec![format!("{type_name}.{field}")]);
                    }
                }
            }
            Expr::FieldAccess {
                base: Box::new(substitute_expr(*base, substitutions)),
                field,
            }
        }
        Expr::StructInit {
            name,
            type_args,
            fields,
        } => Expr::StructInit {
            name,
            type_args: type_args
                .into_iter()
                .map(|ty| substitute_type(ty, substitutions))
                .collect(),
            fields: fields
                .into_iter()
                .map(|field| FieldInit {
                    name: field.name,
                    value: substitute_expr(field.value, substitutions),
                })
                .collect(),
        },
        Expr::BuiltinCall { name, args } => Expr::BuiltinCall {
            name,
            args: args
                .into_iter()
                .map(|arg| substitute_expr(arg, substitutions))
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: Box::new(substitute_expr(*receiver, substitutions)),
            method,
            args: args
                .into_iter()
                .map(|arg| substitute_expr(arg, substitutions))
                .collect(),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(substitute_expr(*callee, substitutions)),
            args: args
                .into_iter()
                .map(|arg| substitute_expr(arg, substitutions))
                .collect(),
        },
        Expr::Specialize { callee, type_args } => Expr::Specialize {
            callee: Box::new(substitute_expr(*callee, substitutions)),
            type_args: type_args
                .into_iter()
                .map(|ty| substitute_type(ty, substitutions))
                .collect(),
        },
        Expr::Cast { expr, ty } => Expr::Cast {
            expr: Box::new(substitute_expr(*expr, substitutions)),
            ty: substitute_type(ty, substitutions),
        },
        Expr::Error { message } => Expr::Error {
            message: Box::new(substitute_expr(*message, substitutions)),
        },
        Expr::Try(expr) => Expr::Try(Box::new(substitute_expr(*expr, substitutions))),
        Expr::Unary { op, expr } => Expr::Unary {
            op,
            expr: Box::new(substitute_expr(*expr, substitutions)),
        },
        Expr::Pack(values) => Expr::Pack(
            values
                .into_iter()
                .map(|value| substitute_expr(value, substitutions))
                .collect(),
        ),
        Expr::Binary { lhs, op, rhs } => Expr::Binary {
            lhs: Box::new(substitute_expr(*lhs, substitutions)),
            op,
            rhs: Box::new(substitute_expr(*rhs, substitutions)),
        },
        Expr::SizeOf(ty) => Expr::SizeOf(substitute_type(ty, substitutions)),
        Expr::BitCast { expr, ty } => Expr::BitCast {
            expr: Box::new(substitute_expr(*expr, substitutions)),
            ty: substitute_type(ty, substitutions),
        },
        other => other,
    }
}

fn substitute_type(ty: Type, substitutions: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Infer => Type::Infer,
        Type::Named(name) => substitutions
            .get(&name)
            .cloned()
            .unwrap_or(Type::Named(name)),
        Type::Applied(name, type_args) => Type::Applied(
            name,
            type_args
                .into_iter()
                .map(|type_arg| substitute_type(type_arg, substitutions))
                .collect(),
        ),
        Type::Result(inner) => Type::Result(Box::new(substitute_type(*inner, substitutions))),
        Type::Mut(inner) => Type::Mut(Box::new(substitute_type(*inner, substitutions))),
        Type::Ref(inner) => Type::Ref(Box::new(substitute_type(*inner, substitutions))),
        Type::List(inner) => Type::List(Box::new(substitute_type(*inner, substitutions))),
        Type::FixedArray(n, inner) => {
            Type::FixedArray(n, Box::new(substitute_type(*inner, substitutions)))
        }
        Type::FnPtr(params, ret) => Type::FnPtr(
            params
                .into_iter()
                .map(|p| substitute_type(p, substitutions))
                .collect(),
            Box::new(substitute_type(*ret, substitutions)),
        ),
        other => other,
    }
}

fn deref_type_refs(mut ty: &Type) -> &Type {
    loop {
        match ty {
            Type::Ref(inner) | Type::Mut(inner) => ty = inner,
            _ => return ty,
        }
    }
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

fn infer_implicit_return_type(
    function: &Function,
    substitutions: &HashMap<String, Type>,
) -> Option<Type> {
    let param_types = function
        .params
        .iter()
        .map(|param| {
            (
                param.name.clone(),
                substitute_type(param.ty.clone(), substitutions),
            )
        })
        .collect::<HashMap<_, _>>();
    infer_return_type_from_stmts(&function.body, &param_types)
}

fn infer_return_type_from_stmts(
    body: &[Stmt],
    param_types: &HashMap<String, Type>,
) -> Option<Type> {
    for stmt in body {
        match stmt {
            Stmt::Return {
                value: Some(expr), ..
            } => {
                if let Some(ty) = infer_expr_type_from_template(expr, param_types) {
                    return Some(ty);
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                if let Some(ty) = infer_return_type_from_stmts(then_body, param_types) {
                    return Some(ty);
                }
                if let Some(ty) = infer_return_type_from_stmts(else_body, param_types) {
                    return Some(ty);
                }
            }
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    if let Some(ty) = infer_return_type_from_stmts(&arm.body, param_types) {
                        return Some(ty);
                    }
                }
            }
            Stmt::ForRange { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::While { body, .. }
            | Stmt::Loop { body, .. } => {
                if let Some(ty) = infer_return_type_from_stmts(body, param_types) {
                    return Some(ty);
                }
            }
            _ => {}
        }
    }
    None
}

fn infer_expr_type_from_template(expr: &Expr, param_types: &HashMap<String, Type>) -> Option<Type> {
    match expr {
        Expr::Int(_) => Some(Type::I32),
        Expr::Char(_) => Some(Type::U8),
        Expr::Bool(_) => Some(Type::Bool),
        Expr::Float(_) => Some(Type::F32),
        Expr::String(_) => Some(Type::Ref(Box::new(Type::U8))),
        Expr::Path(path) if path.len() == 1 => param_types.get(&path[0]).cloned(),
        Expr::StructInit {
            name, type_args, ..
        } => {
            if type_args.is_empty() {
                Some(Type::Named(name.clone()))
            } else {
                Some(Type::Applied(name.clone(), type_args.clone()))
            }
        }
        Expr::Cast { ty, .. } => Some(ty.clone()),
        Expr::SizeOf(_) => Some(Type::Usize),
        Expr::BitCast { ty, .. } => Some(ty.clone()),
        Expr::Unary { op, expr } => {
            let inner = infer_expr_type_from_template(expr, param_types)?;
            match op {
                crate::ast::UnaryOp::LogicalNot => Some(Type::Bool),
                _ => Some(inner),
            }
        }
        Expr::Binary { lhs, op, rhs } => {
            let lhs_ty = infer_expr_type_from_template(lhs, param_types)?;
            let rhs_ty = infer_expr_type_from_template(rhs, param_types)?;
            match op {
                crate::ast::BinaryOp::Add
                | crate::ast::BinaryOp::Subtract
                | crate::ast::BinaryOp::Divide
                | crate::ast::BinaryOp::Multiply
                | crate::ast::BinaryOp::Modulo
                | crate::ast::BinaryOp::BitAnd
                | crate::ast::BinaryOp::BitOr
                | crate::ast::BinaryOp::BitXor
                | crate::ast::BinaryOp::ShiftLeft
                | crate::ast::BinaryOp::ShiftRight
                    if lhs_ty == rhs_ty =>
                {
                    Some(lhs_ty)
                }
                crate::ast::BinaryOp::LessThan
                | crate::ast::BinaryOp::LessEqual
                | crate::ast::BinaryOp::GreaterThan
                | crate::ast::BinaryOp::GreaterEqual
                | crate::ast::BinaryOp::Equal
                | crate::ast::BinaryOp::NotEqual
                | crate::ast::BinaryOp::LogicalAnd
                | crate::ast::BinaryOp::LogicalOr => Some(Type::Bool),
                _ => None,
            }
        }
        _ => None,
    }
}

fn specialization_key(name: &str, type_args: &[Type]) -> String {
    format!("{name}[{}]", specialization_suffix(type_args))
}

fn specialization_suffix(type_args: &[Type]) -> String {
    type_args
        .iter()
        .map(type_suffix_for_specialization)
        .collect::<Vec<_>>()
        .join("__")
}

fn type_suffix_for_specialization(ty: &Type) -> String {
    match ty {
        Type::Infer => "infer".to_string(),
        Type::Void => "void".to_string(),
        Type::Bool => "bool".to_string(),
        Type::I8 => "i8".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I64 => "i64".to_string(),
        Type::Isize => "isize".to_string(),
        Type::U8 => "u8".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U64 => "u64".to_string(),
        Type::Usize => "usize".to_string(),
        Type::F32 => "f32".to_string(),
        Type::F64 => "f64".to_string(),
        Type::Named(name) => sanitize_generic_name(name),
        Type::Applied(name, type_args) => format!(
            "{}__{}",
            sanitize_generic_name(name),
            type_args
                .iter()
                .map(type_suffix_for_specialization)
                .collect::<Vec<_>>()
                .join("__")
        ),
        Type::Mut(inner) => format!("mut__{}", type_suffix_for_specialization(inner)),
        Type::Ref(inner) => format!("ref__{}", type_suffix_for_specialization(inner)),
        Type::List(inner) => format!("list__{}", type_suffix_for_specialization(inner)),
        Type::FixedArray(n, inner) => format!("arr{n}__{}", type_suffix_for_specialization(inner)),
        Type::Result(inner) => format!("result__{}", type_suffix_for_specialization(inner)),
        Type::FnPtr(_, bt) => format!("fnptr__{}", type_suffix_for_specialization(bt)),
        Type::Error => "error".to_string(),
        Type::None => "none".to_string(),
    }
}

fn sanitize_generic_name(name: &str) -> String {
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

fn describe_type(ty: &Type) -> String {
    match ty {
        Type::Void => "void".to_string(),
        Type::Bool => "bool".to_string(),
        Type::I8 => "i8".to_string(),
        Type::I16 => "i16".to_string(),
        Type::I32 => "i32".to_string(),
        Type::I64 => "i64".to_string(),
        Type::Isize => "isize".to_string(),
        Type::U8 => "u8".to_string(),
        Type::U16 => "u16".to_string(),
        Type::U32 => "u32".to_string(),
        Type::U64 => "u64".to_string(),
        Type::Usize => "usize".to_string(),
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
        Type::Result(inner) => format!("{}|error", describe_type(inner)),
        Type::FnPtr(_, inner) => format!("fn({})", describe_type(inner)),
        Type::FixedArray(size, inner) => format!("[{}]{}", size, describe_type(inner)),
        Type::Error => "error".to_string(),
        Type::None => "none".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::{resolve_entry_program, resolve_module_use_path};

    #[test]
    fn resolves_module_calls_to_namespaced_functions() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("some_file.scar");

        fs::write(
            &entry,
            "val some_module = use(\"some_file\")\npub def main() void\n\tsome_module.some_function()\nend\n",
        )
        .unwrap();
        fs::write(
            &module,
            "pub def some_function() void\n\t@puts(\"hello\")\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert!(program.type_defs.is_empty());
        assert_eq!(program.functions.len(), 2);
        assert_eq!(program.functions[0].name, "some_file__some_function");
        assert_eq!(program.functions[1].name, "main");

        fs::remove_dir_all(temp_dir).unwrap();
    }

    fn create_temp_dir() -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!("scar-module-test-{unique}"));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[allow(dead_code)]
    fn _assert_exists(path: &Path) {
        assert!(path.exists());
    }

    #[test]
    fn resolves_module_type_defs() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("some_file.scar");

        fs::write(
            &entry,
            "val some_module = use(\"some_file\")\npub def main() void\n\tsome_module.some_other_function()\nend\n",
        )
        .unwrap();
        fs::write(
            &module,
            "type SomeType\n\tx i32\nend\n\npub def some_other_function() void\n\tval st = SomeType(x: 10)\n\t@print(\"{d}\", {st.x})\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name, "some_file__SomeType");

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn resolves_namespaced_type_functions() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "pub type Arena\n\tcap usize\nend\n\npub def Arena.new(cap usize) Arena\n\treturn Arena(cap: cap)\nend\n\npub def main() void\n\tval arena = Arena.new(4 as usize)\n\t@print(\"{d}\", {arena.cap})\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert_eq!(program.type_defs[0].name, "Arena");
        assert_eq!(program.functions[0].name, "Arena.new");

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn resolves_specialized_same_module_type_functions() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "pub type Arena\n\tcap usize\nend\n\npub def StringBuilder.new[A](ac A, cap usize) usize\n\treturn cap\nend\n\npub def main() void\n\tStringBuilder.new[Arena](Arena(cap: 1 as usize), 4 as usize)\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert_eq!(program.functions.len(), 2);
        assert_eq!(program.functions[0].name, "main");
        assert!(
            program.functions[1]
                .name
                .starts_with("StringBuilder.new__generic__Arena")
        );

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn specializes_generic_types_in_resolved_programs() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "type Pair[T, U]\n\tfirst T\n\tsecond U\nend\n\ndef make_pair[T, U](first T, second U) Pair[T, U]\n\treturn Pair[T, U](first: first, second: second)\nend\n\npub def main() void\n\tval pair = make_pair[i32, ref(u8)](1, \"ok\")\n\t@print(\"{d}\", {pair.first})\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert!(
            program
                .type_defs
                .iter()
                .any(|type_def| type_def.name == "Pair__generic__i32__ref__u8")
        );
        assert!(program.functions.iter().any(|function| {
            function.name == "make_pair__generic__i32__ref__u8"
                && matches!(
                    function.return_type,
                    crate::Type::Named(ref name) if name == "Pair__generic__i32__ref__u8"
                )
        }));

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn enforces_typeset_constraints_for_generic_functions() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "pub typeset Integer\n\ti32, u32\nend\n\ndef id[T: Integer](value T) T\n\treturn value\nend\n\npub def main() void\n\tid[ref(u8)](\"nope\")\nend\n",
        )
        .unwrap();

        let error = resolve_entry_program(&entry).unwrap_err();

        assert!(
            error
                .to_string()
                .contains("generic parameter `T` on `id` does not allow type ref(u8)")
        );

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn resolves_cross_module_typeset_constraints() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("other_file.scar");

        fs::write(
            &entry,
            "val other_file = use(\"other_file\")\n\ntype Pair[T, U]\n\tfirst T\n\tsecond U\nend\n\ndef print_pair[T: other_file.Integer](p Pair[T, ref(u8)]) T\n\treturn p.first\nend\n\npub def main() void\n\tval p = Pair[i32, ref(u8)](first: 1, second: \"ok\")\n\tprint_pair[i32](p)\nend\n",
        )
        .unwrap();
        fs::write(&module, "pub typeset Integer\n\ti32, u32\nend\n").unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert!(program.functions.iter().any(|function| {
            function.name == "print_pair__generic__i32"
                && matches!(function.return_type, crate::Type::I32)
        }));

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn infers_underscore_generic_type_arguments_from_call_args() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "pub type Arena\n\tcap usize\nend\n\npub def Arena.new(cap usize) Arena\n\treturn Arena(cap: cap)\nend\n\npub def StringBuilder.new[A](ac A, cap usize) usize\n\treturn cap\nend\n\npub def main() void\n\tvar ac = Arena.new(1 as usize)\n\tStringBuilder.new[_](ac, 4 as usize)\nend\n",
        )
        .unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert_eq!(program.functions.len(), 3);
        assert!(program.functions.iter().any(|function| {
            function
                .name
                .starts_with("StringBuilder.new__generic__Arena")
        }));

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn rejects_uninferrable_underscore_generic_type_arguments() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");

        fs::write(
            &entry,
            "pub def helper[T](value i32) i32\n\treturn value\nend\n\npub def main() void\n\thelper[_](1)\nend\n",
        )
        .unwrap();

        let error = resolve_entry_program(&entry).unwrap_err();

        assert_eq!(
            error.to_string(),
            "cannot infer type from type argument, specify it manually."
        );

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn rejects_private_module_function_calls() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("some_file.scar");

        fs::write(
            &entry,
            "val some_module = use(\"some_file\")\npub def main() void\n\tsome_module.hidden()\nend\n",
        )
        .unwrap();
        fs::write(&module, "def hidden() void\nend\n").unwrap();

        let error = resolve_entry_program(&entry).unwrap_err();

        assert!(
            error
                .to_string()
                .contains("module `some_module` has no public function or type `hidden`")
        );

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn resolves_public_extern_functions_from_modules() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("some_file.scar");

        fs::write(
            &entry,
            "val some_module = use(\"some_file\")\npub def main() void\n\tsome_module.sleep(1 as u32)\nend\n",
        )
        .unwrap();
        fs::write(&module, "pub extern def sleep(t u32) void :: \"sleep\"\n").unwrap();

        let program = resolve_entry_program(&entry).unwrap();

        assert_eq!(program.functions.len(), 2);
        assert_eq!(program.functions[0].name, "some_file__sleep");
        assert!(program.functions[0].is_pub);
        assert_eq!(program.functions[0].extern_name.as_deref(), Some("sleep"));

        fs::remove_dir_all(temp_dir).unwrap();
    }

    #[test]
    fn std_imports_prefer_local_std_root() {
        let resolved = resolve_module_use_path(
            Path::new("/project/src"),
            "std/string",
            Some(Path::new("/project/lib/std")),
            Some(Path::new("/home/test/.scar/lib/std")),
        )
        .unwrap();

        assert_eq!(resolved, Path::new("/project/lib/std/string.scar"));
    }

    #[test]
    fn std_imports_fall_back_to_home_std_root() {
        let resolved = resolve_module_use_path(
            Path::new("/project/src"),
            "std/string",
            None,
            Some(Path::new("/home/test/.scar/lib/std")),
        )
        .unwrap();

        assert_eq!(resolved, Path::new("/home/test/.scar/lib/std/string.scar"));
    }

    #[test]
    fn non_std_imports_stay_relative_to_current_file() {
        let resolved = resolve_module_use_path(
            Path::new("/project/src"),
            "some_file",
            Some(Path::new("/project/lib/std")),
            Some(Path::new("/home/test/.scar/lib/std")),
        )
        .unwrap();

        assert_eq!(resolved, Path::new("/project/src/some_file.scar"));
    }

    #[test]
    fn rejects_unused_module_import() {
        let temp_dir = create_temp_dir();
        let entry = temp_dir.join("main.scar");
        let module = temp_dir.join("unused_mod.scar");

        fs::write(
            &entry,
            "val unused_mod = use(\"unused_mod\")\npub def main() void\n\t@puts(\"hello\")\nend\n",
        )
        .unwrap();
        fs::write(
            &module,
            "pub def some_function() void\n\t@puts(\"from module\")\nend\n",
        )
        .unwrap();

        let error = resolve_entry_program(&entry).unwrap_err();
        assert_eq!(
            error.to_string(),
            "module `unused_mod` imported but never used"
        );

        fs::remove_dir_all(temp_dir).unwrap();
    }
}
