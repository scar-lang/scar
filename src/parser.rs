use crate::{
    CompileError,
    ast::{
        BinaryOp, EnumDef, EnumVariant, Expr, FieldDef, FieldInit, Function, GenericParam,
        GlobalVar, InterfaceDef, InterfaceMethod, MatchArm, MatchArmKind, ModuleUse, Param,
        Program, Stmt, TestBlock, Type, TypeDef, TypeDefKind, TypeSetDef, UnaryOp, UnionVariantDef,
    },
    lexer::{Token, TokenKind},
};

pub fn parse_program(tokens: Vec<Token>) -> Result<Program, CompileError> {
    Parser::new(tokens).parse_program()
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    line: usize,
}

#[derive(Default)]
struct TopLevelItems {
    module_uses: Vec<ModuleUse>,
    extern_headers: Vec<String>,
    link_flags: Vec<String>,
    interface_defs: Vec<InterfaceDef>,
    type_defs: Vec<TypeDef>,
    typesets: Vec<TypeSetDef>,
    enum_defs: Vec<EnumDef>,
    functions: Vec<Function>,
    tests: Vec<TestBlock>,
    globals: Vec<GlobalVar>,
}

impl TopLevelItems {
    fn append(&mut self, mut other: Self) {
        self.module_uses.append(&mut other.module_uses);
        self.extern_headers.append(&mut other.extern_headers);
        self.link_flags.append(&mut other.link_flags);
        self.interface_defs.append(&mut other.interface_defs);
        self.type_defs.append(&mut other.type_defs);
        self.typesets.append(&mut other.typesets);
        self.enum_defs.append(&mut other.enum_defs);
        self.functions.append(&mut other.functions);
        self.tests.append(&mut other.tests);
        self.globals.append(&mut other.globals);
    }
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            pos: 0,
            line: 1,
        }
    }

    fn parse_program(&mut self) -> Result<Program, CompileError> {
        let items = self.parse_top_level_items_until(&[])?;
        Ok(Program {
            module_uses: items.module_uses,
            extern_headers: items.extern_headers,
            link_flags: items.link_flags,
            interface_defs: items.interface_defs,
            type_defs: items.type_defs,
            typesets: items.typesets,
            enum_defs: items.enum_defs,
            functions: items.functions,
            tests: items.tests,
            globals: items.globals,
        })
    }

    fn parse_top_level_items_until(
        &mut self,
        terminators: &[TokenKind],
    ) -> Result<TopLevelItems, CompileError> {
        let mut items = TopLevelItems::default();
        self.consume_newlines();
        while !self.check_any_simple(terminators) && !self.is_eof() {
            if self.check_simple(&TokenKind::When) {
                items.append(self.parse_when_top_level_items()?);
            } else if self.check_simple(&TokenKind::Link) {
                self.advance();
                let TokenKind::Str(flag) = self.current().kind.clone() else {
                    return Err(self.error_at_current("expected a string literal after `link`"));
                };
                items.link_flags.push(flag);
                self.advance();
                self.expect_newline("expected a newline after link flag")?;
            } else if self.check_simple(&TokenKind::Val) {
                if self.is_module_use() {
                    items.module_uses.push(self.parse_module_use()?);
                } else {
                    items.globals.push(self.parse_global_var(false)?);
                }
            } else if self.check_simple(&TokenKind::Var) {
                items.globals.push(self.parse_global_var(false)?);
            } else if self.check_simple(&TokenKind::Pub) && self.check_next_simple(&TokenKind::Val)
            {
                items.globals.push(self.parse_global_var(true)?);
            } else if self.check_simple(&TokenKind::Pub) && self.check_next_simple(&TokenKind::Var)
            {
                items.globals.push(self.parse_global_var(true)?);
            } else if self.check_simple(&TokenKind::Test) {
                items.tests.push(self.parse_test_block()?);
            } else if self.check_simple(&TokenKind::Pub)
                && self.check_next_simple(&TokenKind::Interface)
            {
                items.interface_defs.push(self.parse_interface_def(true)?);
            } else if self.check_simple(&TokenKind::Interface) {
                items.interface_defs.push(self.parse_interface_def(false)?);
            } else if self.check_simple(&TokenKind::Pub)
                && self.check_next_simple(&TokenKind::Typeset)
            {
                items.typesets.push(self.parse_typeset_def(true)?);
            } else if self.check_simple(&TokenKind::Typeset) {
                items.typesets.push(self.parse_typeset_def(false)?);
            } else if self.check_simple(&TokenKind::Pub) && self.check_next_simple(&TokenKind::Enum)
            {
                let enum_def = self.parse_enum_def(true)?;
                items.enum_defs.push(enum_def.clone());
                items.type_defs.push(TypeDef {
                    is_pub: enum_def.is_pub,
                    name: enum_def.name.clone(),
                    generic_params: vec![],
                    kind: TypeDefKind::Enum,
                    is_extern: false,
                    alias: None,
                    derives: vec![],
                    fields: vec![],
                    variants: enum_def
                        .variants
                        .iter()
                        .map(|v| UnionVariantDef {
                            name: v.name.clone(),
                            payload_types: vec![],
                        })
                        .collect(),
                    line: enum_def.line,
                    column: enum_def.column,
                    file_path: None,
                });
            } else if self.check_simple(&TokenKind::Enum) {
                let enum_def = self.parse_enum_def(false)?;
                items.enum_defs.push(enum_def.clone());
                items.type_defs.push(TypeDef {
                    is_pub: enum_def.is_pub,
                    name: enum_def.name.clone(),
                    generic_params: vec![],
                    kind: TypeDefKind::Enum,
                    is_extern: false,
                    alias: None,
                    derives: vec![],
                    fields: vec![],
                    variants: enum_def
                        .variants
                        .iter()
                        .map(|v| UnionVariantDef {
                            name: v.name.clone(),
                            payload_types: vec![],
                        })
                        .collect(),
                    line: enum_def.line,
                    column: enum_def.column,
                    file_path: None,
                });
            } else if self.check_simple(&TokenKind::Pub) && self.check_next_simple(&TokenKind::Type)
            {
                items.type_defs.push(self.parse_type_def(true, false)?);
            } else if self.check_simple(&TokenKind::Pub)
                && self.check_next_simple(&TokenKind::Union)
            {
                items.type_defs.push(self.parse_union_def(true)?);
            } else if self.check_simple(&TokenKind::Pub)
                && self.check_next_simple(&TokenKind::Extern)
            {
                items.functions.push(self.parse_extern_function(true)?);
            } else if self.check_simple(&TokenKind::Type) {
                items.type_defs.push(self.parse_type_def(false, false)?);
            } else if self.check_simple(&TokenKind::Union) {
                items.type_defs.push(self.parse_union_def(false)?);
            } else if self.check_simple(&TokenKind::Extern)
                && self.check_next_simple(&TokenKind::Type)
            {
                items.type_defs.push(self.parse_type_def(false, true)?);
            } else if self.check_simple(&TokenKind::Extern)
                && matches!(
                    self.next_non_newline_kind(self.pos + 1),
                    Some(TokenKind::Str(_))
                )
            {
                items.extern_headers.push(self.parse_extern_header()?);
            } else if self.check_simple(&TokenKind::Extern) {
                items.functions.push(self.parse_extern_function(false)?);
            } else {
                items.functions.push(self.parse_function()?);
            }
            self.consume_newlines();
        }
        Ok(items)
    }

    fn parse_when_top_level_items(&mut self) -> Result<TopLevelItems, CompileError> {
        self.expect_simple(TokenKind::When)?;
        let matches = self.evaluate_when_condition()?;
        self.expect_newline("expected a newline after platform selector")?;
        let items = self.parse_top_level_items_until(&[TokenKind::End])?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        if matches {
            Ok(items)
        } else {
            Ok(TopLevelItems::default())
        }
    }

    fn is_module_use(&self) -> bool {
        if !matches!(
            self.tokens.get(self.pos).map(|t| &t.kind),
            Some(TokenKind::Val)
        ) {
            return false;
        }
        let mut i = self.pos + 1;
        if !matches!(
            self.tokens.get(i).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        ) {
            return false;
        }
        i += 1;
        if !matches!(self.tokens.get(i).map(|t| &t.kind), Some(TokenKind::Assign)) {
            return false;
        }
        i += 1;
        matches!(self.tokens.get(i).map(|t| &t.kind), Some(TokenKind::Ident(s)) if s == "use")
    }

    fn parse_global_var(&mut self, is_pub: bool) -> Result<GlobalVar, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        let line = self.current().line;
        let column = self.current().column;
        let mutable = self.check_simple(&TokenKind::Var);
        self.advance(); // consume val or var
        let name = self.expect_ident()?;
        let ty = self.parse_type()?;
        self.expect_simple(TokenKind::Assign)?;
        let init = self.parse_expr()?;
        self.expect_stmt_terminator()?;
        Ok(GlobalVar {
            is_pub,
            mutable,
            name,
            ty,
            init,
            line,
            column,
            file_path: None,
        })
    }

    fn parse_module_use(&mut self) -> Result<ModuleUse, CompileError> {
        self.expect_simple(TokenKind::Val)?;
        let name = self.expect_ident()?;
        self.expect_simple(TokenKind::Assign)?;
        match self.current().kind.clone() {
            TokenKind::Ident(keyword) if keyword == "use" => self.advance(),
            _ => {
                return Err(
                    self.error_at_current("expected `use(\"path\")` in top-level module binding")
                );
            }
        }
        self.expect_simple(TokenKind::LParen)?;
        let TokenKind::Str(path) = self.current().kind.clone() else {
            return Err(self.error_at_current("expected a string literal module path"));
        };
        self.advance();
        self.expect_simple(TokenKind::RParen)?;
        self.expect_stmt_terminator()?;
        Ok(ModuleUse { name, path })
    }

    fn parse_type_def(&mut self, is_pub: bool, is_extern: bool) -> Result<TypeDef, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        if is_extern {
            self.expect_simple(TokenKind::Extern)?;
        }
        let def_line = self.current().line;
        let def_column = self.current().column;
        self.expect_simple(TokenKind::Type)?;
        let name = self.expect_ident()?;
        let generic_params = if self.check_simple(&TokenKind::LBracket) {
            self.parse_generic_params()?
        } else {
            Vec::new()
        };
        let derives = if self.check_simple(&TokenKind::Colon) {
            self.advance();
            self.parse_derive_list()?
        } else {
            Vec::new()
        };
        if self.check_simple(&TokenKind::Assign) {
            if is_extern {
                return Err(
                    self.error_at_current("extern types must be explicitly defined with fields")
                );
            }
            self.advance();
            let alias = Some(self.parse_type()?);
            self.expect_stmt_terminator()?;
            return Ok(TypeDef {
                is_pub,
                name,
                generic_params,
                kind: TypeDefKind::Struct,
                is_extern,
                alias,
                derives,
                fields: Vec::new(),
                variants: Vec::new(),
                line: def_line,
                column: def_column,
                file_path: None,
            });
        }
        self.expect_newline("expected a newline after type name")?;

        let mut fields = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            let field_line = self.current().line;
            let field_column = self.current().column;
            let field_name = self.expect_ident()?;
            let ty = self.parse_type()?;
            self.expect_stmt_terminator()?;
            fields.push(FieldDef {
                name: field_name,
                ty,
                line: field_line,
                column: field_column,
            });
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(TypeDef {
            is_pub,
            name,
            generic_params,
            kind: TypeDefKind::Struct,
            is_extern,
            alias: None,
            derives,
            fields,
            variants: Vec::new(),
            line: def_line,
            column: def_column,
            file_path: None,
        })
    }

    fn parse_union_def(&mut self, is_pub: bool) -> Result<TypeDef, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        let def_line = self.current().line;
        let def_column = self.current().column;
        self.expect_simple(TokenKind::Union)?;
        let name = self.expect_ident()?;
        self.expect_newline("expected a newline after union name")?;

        let mut variants = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            let variant_name = self.expect_ident()?;
            let payload_types = if self.check_simple(&TokenKind::LParen) {
                self.advance();
                self.consume_newlines();
                let mut payload_types = Vec::new();
                if !self.check_simple(&TokenKind::RParen) {
                    loop {
                        payload_types.push(self.parse_type()?);
                        if self.check_simple(&TokenKind::Comma) {
                            self.advance();
                            self.consume_newlines();
                        } else {
                            self.consume_newlines();
                            break;
                        }
                    }
                }
                self.expect_simple(TokenKind::RParen)?;
                payload_types
            } else {
                Vec::new()
            };
            self.expect_stmt_terminator()?;
            variants.push(UnionVariantDef {
                name: variant_name,
                payload_types,
            });
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(TypeDef {
            is_pub,
            name,
            generic_params: Vec::new(),
            kind: TypeDefKind::Union,
            is_extern: false,
            alias: None,
            derives: Vec::new(),
            fields: Vec::new(),
            variants,
            line: def_line,
            column: def_column,
            file_path: None,
        })
    }

    fn parse_typeset_def(&mut self, is_pub: bool) -> Result<TypeSetDef, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        self.expect_simple(TokenKind::Typeset)?;
        let name = self.expect_ident()?;
        self.expect_newline("expected a newline after typeset name")?;

        let mut members = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            members.push(self.parse_non_result_type()?);
            if self.check_simple(&TokenKind::Comma) {
                self.advance();
            }
            self.consume_newlines();
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(TypeSetDef {
            is_pub,
            name,
            members,
        })
    }

    fn parse_enum_def(&mut self, is_pub: bool) -> Result<EnumDef, CompileError> {
        let line = self.line;
        let column = self.current().column;
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        self.expect_simple(TokenKind::Enum)?;
        let name = self.expect_ident()?;
        self.expect_newline("expected a newline after enum name")?;

        let mut variants = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            let variant_name = self.expect_ident()?;
            variants.push(EnumVariant { name: variant_name });
            if self.check_simple(&TokenKind::Comma) {
                self.advance();
            }
            self.consume_newlines();
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(EnumDef {
            is_pub,
            name,
            variants,
            line,
            column,
            file_path: None,
        })
    }

    fn parse_interface_def(&mut self, is_pub: bool) -> Result<InterfaceDef, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        self.expect_simple(TokenKind::Interface)?;
        let name = self.expect_ident()?;
        self.expect_newline("expected a newline after interface name")?;

        let mut methods = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            let method_is_pub = if self.check_simple(&TokenKind::Pub) {
                self.advance();
                true
            } else {
                false
            };
            let (method_name, generic_params, params, return_type) =
                self.parse_function_signature()?;
            if !generic_params.is_empty() {
                return Err(self.error_at_current("interface methods cannot declare generics"));
            }
            self.expect_stmt_terminator()?;
            methods.push(InterfaceMethod {
                is_pub: method_is_pub,
                name: method_name,
                params,
                return_type,
            });
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(InterfaceDef {
            is_pub,
            name,
            methods,
            file_path: None,
        })
    }

    fn parse_function(&mut self) -> Result<Function, CompileError> {
        let is_pub = if self.check_simple(&TokenKind::Pub) {
            self.advance();
            true
        } else {
            false
        };
        let fn_line = self.current().line;
        let fn_column = self.current().column;
        let (name, generic_params, params, return_type) = self.parse_function_signature()?;
        let body = self.parse_block()?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();

        Ok(Function {
            is_pub,
            name,
            extern_name: None,
            generic_params,
            params,
            return_type,
            body,
            line: fn_line,
            column: fn_column,
            file_path: None,
        })
    }

    fn parse_extern_function(&mut self, is_pub: bool) -> Result<Function, CompileError> {
        if is_pub {
            self.expect_simple(TokenKind::Pub)?;
        }
        self.expect_simple(TokenKind::Extern)?;
        let fn_line = self.current().line;
        let fn_column = self.current().column;
        let (name, generic_params, params, return_type) = self.parse_function_signature()?;
        self.expect_simple(TokenKind::ColonColon)?;
        let TokenKind::Str(extern_name) = self.current().kind.clone() else {
            return Err(self.error_at_current("expected a string literal extern symbol name"));
        };
        self.advance();
        self.expect_stmt_terminator()?;

        Ok(Function {
            is_pub,
            name,
            extern_name: Some(extern_name),
            generic_params,
            params,
            return_type,
            body: Vec::new(),
            line: fn_line,
            column: fn_column,
            file_path: None,
        })
    }

    fn parse_extern_header(&mut self) -> Result<String, CompileError> {
        self.expect_simple(TokenKind::Extern)?;
        let TokenKind::Str(header) = self.current().kind.clone() else {
            return Err(self.error_at_current("expected a string literal header name"));
        };
        self.advance();
        self.expect_stmt_terminator()?;
        Ok(header)
    }

    fn parse_test_block(&mut self) -> Result<TestBlock, CompileError> {
        self.expect_simple(TokenKind::Test)?;
        let TokenKind::Str(name) = self.current().kind.clone() else {
            return Err(self.error_at_current("expected a string literal test name"));
        };
        self.advance();
        self.expect_newline("expected a newline after test name")?;
        let body = self.parse_block()?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(TestBlock { name, body })
    }

    fn parse_function_signature(
        &mut self,
    ) -> Result<(String, Vec<GenericParam>, Vec<Param>, Type), CompileError> {
        self.expect_simple(TokenKind::Def)?;
        let name = self.parse_qualified_name()?;
        let generic_params = if self.check_simple(&TokenKind::LBracket) {
            self.parse_generic_params()?
        } else {
            Vec::new()
        };
        self.expect_simple(TokenKind::LParen)?;
        self.consume_newlines();

        let mut params = Vec::new();
        if !self.check_simple(&TokenKind::RParen) {
            loop {
                let param_line = self.current().line;
                let param_column = self.current().column;
                let param_name = self.expect_ident()?;
                if self.check_simple(&TokenKind::Colon) {
                    return Err(self.error_at_current(
                        "unexpected `:` in parameter — use `name Type` not `name: Type`",
                    ));
                }
                let ty = self.parse_type()?;
                params.push(Param {
                    name: param_name,
                    ty,
                    line: param_line,
                    column: param_column,
                });
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    self.consume_newlines();
                } else {
                    break;
                }
            }
        }
        self.consume_newlines();
        self.expect_simple(TokenKind::RParen)?;

        let return_type = if self.check_simple(&TokenKind::Colon) {
            return Err(self.error_at_current(
                "unexpected `:` before return type — write the type directly after `)`",
            ));
        } else if self.starts_type() {
            self.parse_type()?
        } else {
            Type::Void
        };
        Ok((name, generic_params, params, return_type))
    }

    fn parse_qualified_name(&mut self) -> Result<String, CompileError> {
        let mut segments = vec![self.expect_ident()?];
        while self.check_simple(&TokenKind::Dot) {
            self.advance();
            segments.push(self.expect_ident()?);
        }
        Ok(segments.join("."))
    }

    fn parse_generic_params(&mut self) -> Result<Vec<GenericParam>, CompileError> {
        self.expect_simple(TokenKind::LBracket)?;
        self.consume_newlines();
        let mut params = Vec::new();
        while !self.check_simple(&TokenKind::RBracket) {
            let name = self.expect_ident()?;
            let constraints = if self.check_simple(&TokenKind::Colon) {
                self.advance();
                self.parse_type_constraint_list()?
            } else if self.starts_type() {
                return Err(self.error_at_current(
                    "expected `:` before type constraint — use `T: Interface` not `T Interface`",
                ));
            } else {
                Vec::new()
            };
            params.push(GenericParam { name, constraints });
            if self.check_simple(&TokenKind::Comma) {
                self.advance();
                self.consume_newlines();
            } else {
                self.consume_newlines();
                break;
            }
        }
        self.expect_simple(TokenKind::RBracket)?;
        Ok(params)
    }

    fn parse_type_constraint_list(&mut self) -> Result<Vec<Type>, CompileError> {
        let mut constraints = vec![self.parse_non_result_type()?];
        while self.check_simple(&TokenKind::Pipe) {
            self.advance();
            constraints.push(self.parse_non_result_type()?);
        }
        Ok(constraints)
    }

    fn parse_derive_list(&mut self) -> Result<Vec<Type>, CompileError> {
        let mut derives = vec![self.parse_non_result_type()?];
        while self.check_simple(&TokenKind::Comma) {
            self.advance();
            self.consume_newlines();
            derives.push(self.parse_non_result_type()?);
        }
        Ok(derives)
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, CompileError> {
        self.parse_block_until(&[TokenKind::End])
    }

    fn parse_block_until(&mut self, terminators: &[TokenKind]) -> Result<Vec<Stmt>, CompileError> {
        let mut body = Vec::new();
        self.consume_newlines();
        while !self.check_any_simple(terminators) && !self.is_eof() {
            if self.check_simple(&TokenKind::When) {
                body.extend(self.parse_when_stmt_block()?);
            } else {
                body.push(self.parse_stmt()?);
            }
            self.consume_newlines();
        }
        Ok(body)
    }

    fn parse_when_stmt_block(&mut self) -> Result<Vec<Stmt>, CompileError> {
        self.expect_simple(TokenKind::When)?;
        let matches = self.evaluate_when_condition()?;
        self.expect_newline("expected a newline after platform selector")?;
        let body = self.parse_block()?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        if matches { Ok(body) } else { Ok(Vec::new()) }
    }

    fn evaluate_when_condition(&mut self) -> Result<bool, CompileError> {
        let mut matches = false;
        loop {
            let TokenKind::Ident(platform) = self.current().kind.clone() else {
                return Err(self.error_at_current("expected a platform name after `when`"));
            };
            if !is_supported_platform_name(&platform) {
                return Err(
                    self.error_at_current(format!("unsupported platform selector `{platform}`"))
                );
            }
            if platform_matches(&platform) {
                matches = true;
            }
            self.advance();

            if self.check_simple(&TokenKind::Pipe) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(matches)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;

        if matches!(&self.current().kind, TokenKind::Ident(name) if name == "assert") {
            self.advance();
            let condition = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Assert {
                line,
                column,
                condition,
            });
        }

        if self.check_simple(&TokenKind::Var) || self.check_simple(&TokenKind::Val) {
            let mutable = self.check_simple(&TokenKind::Var);
            self.advance();

            if self.check_simple(&TokenKind::LParen) {
                self.advance();
                self.consume_newlines();
                let mut decls = Vec::new();
                while !self.check_simple(&TokenKind::RParen) {
                    let decl_line = self.current().line;
                    let decl_column = self.current().column;
                    let name = self.expect_ident()?;
                    let declared_type = if self.check_simple(&TokenKind::Assign) {
                        None
                    } else {
                        Some(self.parse_type()?)
                    };
                    self.expect_simple(TokenKind::Assign)?;
                    let init = self.parse_expr()?;
                    self.expect_stmt_terminator()?;
                    self.consume_newlines();
                    decls.push(Stmt::VarDecl {
                        line: decl_line,
                        column: decl_column,
                        mutable,
                        name,
                        declared_type,
                        init,
                    });
                }
                self.advance();
                self.expect_stmt_terminator()?;
                return Ok(Stmt::Block(decls));
            }

            let name = self.expect_ident()?;
            let declared_type = if self.check_simple(&TokenKind::Assign) {
                None
            } else {
                Some(self.parse_type()?)
            };
            self.expect_simple(TokenKind::Assign)?;
            let init = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::VarDecl {
                line,
                column,
                mutable,
                name,
                declared_type,
                init,
            });
        }

        if self.check_simple(&TokenKind::Return) {
            self.advance();
            let value = if self.at_stmt_end() {
                None
            } else {
                Some(self.parse_expr()?)
            };
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Return {
                line,
                column,
                value,
            });
        }

        if self.check_simple(&TokenKind::Defer) {
            self.advance();
            self.expect_newline("expected a newline after defer")?;
            let body = self.parse_block()?;
            self.expect_simple(TokenKind::End)?;
            self.consume_newlines();
            return Ok(Stmt::Defer { line, column, body });
        }

        if self.check_simple(&TokenKind::If) {
            return self.parse_if_stmt();
        }

        if self.check_simple(&TokenKind::Guard) {
            return self.parse_guard_stmt();
        }

        if self.check_simple(&TokenKind::Match) {
            return self.parse_match_stmt();
        }

        if self.check_simple(&TokenKind::At) && self.check_next_simple(&TokenKind::LParen) {
            return self.parse_pragma_stmt();
        }

        if self.check_simple(&TokenKind::For) {
            return self.parse_for_stmt(None);
        }

        if self.check_simple(&TokenKind::Parallel) {
            self.advance();
            return self.parse_for_stmt(Some("omp parallel for".to_string()));
        }

        if self.check_simple(&TokenKind::Continue) {
            self.advance();
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Continue { line, column });
        }
        if self.check_simple(&TokenKind::Break) {
            self.advance();
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Break { line, column });
        }

        let expr = self.parse_expr()?;
        if self.check_simple(&TokenKind::Assign) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Assign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::PlusEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::AddAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::StarEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::MulAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::MinusEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::SubAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::SlashEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::DivAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::AmpEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::BitAndAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::PipeEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::BitOrAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::CaretEqual) {
            self.advance();
            self.consume_newlines();
            let value = self.parse_expr()?;
            self.expect_stmt_terminator()?;
            return Ok(Stmt::BitXorAssign {
                line,
                column,
                target: expr,
                value,
            });
        }
        if self.check_simple(&TokenKind::PlusPlus) {
            self.advance();
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Increment {
                line,
                column,
                target: expr,
            });
        }
        if self.check_simple(&TokenKind::MinusMinus) {
            self.advance();
            self.expect_stmt_terminator()?;
            return Ok(Stmt::Decrement {
                line,
                column,
                target: expr,
            });
        }

        let expr = if self.at_stmt_end() {
            self.maybe_promote_bracketless_call(expr)
        } else {
            expr
        };
        self.expect_stmt_terminator()?;
        Ok(Stmt::Expr { line, column, expr })
    }

    fn parse_if_stmt(&mut self) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;
        self.expect_simple(TokenKind::If)?;
        let condition = self.parse_expr()?;
        self.expect_newline("expected a newline after if condition")?;
        let then_body =
            self.parse_block_until(&[TokenKind::Else, TokenKind::Elif, TokenKind::End])?;

        let else_body = if self.check_simple(&TokenKind::Elif) {
            vec![self.parse_elif_chain()?]
        } else if self.check_simple(&TokenKind::Else) {
            self.advance();
            self.expect_newline("expected a newline after else")?;
            self.parse_block()?
        } else {
            Vec::new()
        };

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(Stmt::If {
            line,
            column,
            condition,
            then_body,
            else_body,
        })
    }

    fn parse_elif_chain(&mut self) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;
        self.expect_simple(TokenKind::Elif)?;
        let condition = self.parse_expr()?;
        self.expect_newline("expected a newline after elif condition")?;
        let then_body =
            self.parse_block_until(&[TokenKind::Else, TokenKind::Elif, TokenKind::End])?;

        let else_body = if self.check_simple(&TokenKind::Elif) {
            vec![self.parse_elif_chain()?]
        } else if self.check_simple(&TokenKind::Else) {
            self.advance();
            self.expect_newline("expected a newline after else")?;
            self.parse_block()?
        } else {
            Vec::new()
        };

        Ok(Stmt::If {
            line,
            column,
            condition,
            then_body,
            else_body,
        })
    }

    fn parse_guard_stmt(&mut self) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;
        self.expect_simple(TokenKind::Guard)?;
        let condition = self.parse_expr()?;
        self.expect_simple(TokenKind::Else)?;
        self.expect_newline("expected a newline after guard else")?;
        let else_body = self.parse_block()?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(Stmt::If {
            line,
            column,
            condition: Expr::Unary {
                op: UnaryOp::LogicalNot,
                expr: Box::new(condition),
            },
            then_body: else_body,
            else_body: Vec::new(),
        })
    }

    fn parse_match_stmt(&mut self) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;
        self.expect_simple(TokenKind::Match)?;
        let expr = self.parse_expr()?;
        self.expect_newline("expected a newline after match expression")?;

        let mut arms = Vec::new();
        self.consume_newlines();
        while !self.check_simple(&TokenKind::End) && !self.is_eof() {
            let mut patterns = vec![self.parse_match_pattern()?];
            while self.check_simple(&TokenKind::Pipe) {
                self.advance();
                patterns.push(self.parse_match_pattern()?);
            }
            self.expect_simple(TokenKind::FatArrow)?;
            let body = self.parse_match_arm_body()?;
            for (kind, bindings) in patterns {
                arms.push(MatchArm {
                    kind,
                    bindings,
                    body: body.clone(),
                });
            }
            self.consume_newlines();
        }

        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(Stmt::Match {
            line,
            column,
            expr,
            arms,
        })
    }

    fn parse_match_pattern(&mut self) -> Result<(MatchArmKind, Vec<Option<String>>), CompileError> {
        if self.check_simple(&TokenKind::Int(0)) {
            let value = match &self.current().kind {
                TokenKind::Int(v) => v.to_string(),
                _ => unreachable!(),
            };
            self.advance();
            let bindings = if self.check_simple(&TokenKind::LParen) {
                self.parse_match_bindings()?
            } else {
                Vec::new()
            };
            Ok((MatchArmKind::Variant(value), bindings))
        } else if self.check_simple(&TokenKind::Char(0)) {
            let value = match &self.current().kind {
                TokenKind::Char(v) => v.to_string(),
                _ => unreachable!(),
            };
            self.advance();
            let bindings = if self.check_simple(&TokenKind::LParen) {
                self.parse_match_bindings()?
            } else {
                Vec::new()
            };
            Ok((MatchArmKind::Variant(value), bindings))
        } else if self.check_simple(&TokenKind::Str(String::new())) {
            let value = match &self.current().kind {
                TokenKind::Str(s) => {
                    let bytes = s.as_bytes();
                    if bytes.is_empty() {
                        "0".to_string()
                    } else {
                        format!("{}", bytes[0])
                    }
                }
                _ => unreachable!(),
            };
            self.advance();
            let bindings = if self.check_simple(&TokenKind::LParen) {
                self.parse_match_bindings()?
            } else {
                Vec::new()
            };
            Ok((MatchArmKind::Variant(value), bindings))
        } else if matches!(&self.current().kind, TokenKind::Float(_)) {
            let mut value = match &self.current().kind {
                TokenKind::Float(v) => v.to_string(),
                _ => unreachable!(),
            };
            self.advance();
            if self.check_simple(&TokenKind::Ident("f32".to_string())) {
                value.push_str("f32");
                self.advance();
            } else if self.check_simple(&TokenKind::Ident("f64".to_string())) {
                value.push_str("f64");
                self.advance();
            }
            let bindings = if self.check_simple(&TokenKind::LParen) {
                self.parse_match_bindings()?
            } else {
                Vec::new()
            };
            Ok((MatchArmKind::Variant(value), bindings))
        } else {
            let mut arm_parts = vec![self.expect_ident()?];
            while self.check_simple(&TokenKind::Dot) {
                self.advance();
                arm_parts.push(self.expect_ident()?);
            }
            if arm_parts.len() == 1
                && arm_parts[0] == "ok"
                && !self.check_simple(&TokenKind::LParen)
            {
                Ok((MatchArmKind::Ok, vec![self.parse_match_binding()?]))
            } else if arm_parts.len() == 1
                && arm_parts[0] == "error"
                && !self.check_simple(&TokenKind::LParen)
            {
                Ok((MatchArmKind::Error, vec![self.parse_match_binding()?]))
            } else {
                let bindings = if self.check_simple(&TokenKind::LParen) {
                    self.parse_match_bindings()?
                } else {
                    Vec::new()
                };
                let variant_name = arm_parts.join(".");
                Ok((MatchArmKind::Variant(variant_name), bindings))
            }
        }
    }

    fn parse_match_arm_body(&mut self) -> Result<Vec<Stmt>, CompileError> {
        self.consume_newlines();
        if self.check_simple(&TokenKind::LParen) {
            self.advance();
            self.consume_newlines();
            let body = self.parse_block_until(&[TokenKind::RParen])?;
            self.expect_simple(TokenKind::RParen)?;
            Ok(body)
        } else {
            let stmt = self.parse_stmt()?;
            Ok(vec![stmt])
        }
    }

    fn parse_match_binding(&mut self) -> Result<Option<String>, CompileError> {
        match self.current().kind.clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(if name == "_" { None } else { Some(name) })
            }
            _ => Err(self.error_at_current("expected a match binding name or `_`")),
        }
    }

    fn parse_match_bindings(&mut self) -> Result<Vec<Option<String>>, CompileError> {
        self.expect_simple(TokenKind::LParen)?;
        self.consume_newlines();
        let mut bindings = Vec::new();
        if !self.check_simple(&TokenKind::RParen) {
            loop {
                bindings.push(self.parse_match_binding()?);
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    self.consume_newlines();
                } else {
                    self.consume_newlines();
                    break;
                }
            }
        }
        self.expect_simple(TokenKind::RParen)?;
        Ok(bindings)
    }

    fn parse_pragma_stmt(&mut self) -> Result<Stmt, CompileError> {
        self.expect_simple(TokenKind::At)?;
        self.expect_simple(TokenKind::LParen)?;
        let TokenKind::Str(pragma) = self.current().kind.clone() else {
            return Err(self.error_at_current("expected a string literal pragma directive"));
        };
        self.advance();
        self.expect_simple(TokenKind::RParen)?;
        self.expect_newline("expected a newline after pragma directive")?;

        match self.parse_stmt()? {
            Stmt::ForRange {
                line,
                column,
                pragma: None,
                var_name,
                start,
                end,
                body,
            } => Ok(Stmt::ForRange {
                line,
                column,
                pragma: Some(pragma),
                var_name,
                start,
                end,
                body,
            }),
            _ => Err(CompileError::new(
                "pragma directives currently apply only to `for` loops",
            )),
        }
    }

    fn parse_for_stmt(&mut self, pragma: Option<String>) -> Result<Stmt, CompileError> {
        let line = self.current().line;
        let column = self.current().column;
        self.expect_simple(TokenKind::For)?;

        if self.check_simple(&TokenKind::LParen) {
            if pragma.is_some() {
                return Err(self.error_at_current(
                    "pragma directives currently apply only to range-based `for` loops",
                ));
            }
            self.advance();
            self.consume_newlines();
            let condition = self.parse_expr()?;
            self.consume_newlines();
            self.expect_simple(TokenKind::RParen)?;
            self.expect_newline("expected a newline after for condition")?;
            let body = self.parse_block()?;
            self.expect_simple(TokenKind::End)?;
            self.consume_newlines();
            return Ok(Stmt::While {
                line,
                column,
                condition,
                body,
            });
        }

        if self.check_simple(&TokenKind::Newline) {
            if pragma.is_some() {
                return Err(self.error_at_current(
                    "pragma directives currently apply only to range-based `for` loops",
                ));
            }
            self.consume_newlines();
            let body = self.parse_block()?;
            self.expect_simple(TokenKind::End)?;
            self.consume_newlines();
            return Ok(Stmt::Loop { line, column, body });
        }

        if self.check_simple(&TokenKind::Var) {
            self.advance();
            let var_name = self.expect_ident()?;
            if self.check_simple(&TokenKind::Assign) {
                self.advance();
                let start = self.parse_expr()?;
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    let condition = self.parse_expr()?;
                    self.expect_simple(TokenKind::Comma)?;
                    let mut increment = self.parse_expr()?;
                    if self.check_simple(&TokenKind::MinusMinus) {
                        self.advance();
                        increment = Expr::Unary {
                            op: UnaryOp::PostfixDec,
                            expr: Box::new(increment),
                        };
                    } else if self.check_simple(&TokenKind::PlusPlus) {
                        self.advance();
                        increment = Expr::Unary {
                            op: UnaryOp::PostfixInc,
                            expr: Box::new(increment),
                        };
                    }
                    self.expect_newline("expected a newline after for header")?;
                    let body = self.parse_block()?;
                    self.expect_simple(TokenKind::End)?;
                    self.consume_newlines();
                    return Ok(Stmt::ForClassic {
                        line,
                        column,
                        pragma,
                        var_name,
                        init: start,
                        condition,
                        increment,
                        body,
                    });
                }
                self.expect_simple(TokenKind::DotDot)?;
                let end = self.parse_expr()?;
                self.expect_newline("expected a newline after for header")?;
                let body = self.parse_block()?;
                self.expect_simple(TokenKind::End)?;
                self.consume_newlines();
                return Ok(Stmt::ForRange {
                    line,
                    column,
                    pragma,
                    var_name,
                    start,
                    end,
                    body,
                });
            }

            if pragma.is_some() {
                return Err(self.error_at_current(
                    "pragma directives currently apply only to range-based `for` loops",
                ));
            }

            self.expect_simple(TokenKind::In)?;
            let iterable = self.parse_expr()?;
            self.expect_newline("expected a newline after for header")?;
            let body = self.parse_block()?;
            self.expect_simple(TokenKind::End)?;
            self.consume_newlines();
            return Ok(Stmt::ForEach {
                line,
                column,
                var_name,
                iterable,
                body,
            });
        }

        if pragma.is_some() {
            return Err(self.error_at_current(
                "pragma directives currently apply only to range-based `for` loops",
            ));
        }

        let condition = self.parse_expr()?;
        self.expect_newline("expected a newline after for header")?;
        let body = self.parse_block()?;
        self.expect_simple(TokenKind::End)?;
        self.consume_newlines();
        Ok(Stmt::While {
            line,
            column,
            condition,
            body,
        })
    }

    fn parse_expr(&mut self) -> Result<Expr, CompileError> {
        self.parse_logical_or()
    }

    fn parse_cast(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_unary()?;
        while self.check_simple(&TokenKind::As) {
            self.advance();
            let ty = self.parse_type()?;
            expr = Expr::Cast {
                expr: Box::new(expr),
                ty,
            };
        }
        Ok(expr)
    }

    fn parse_logical_or(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_logical_and()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::PipePipe))
        {
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_logical_and()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op: BinaryOp::LogicalOr,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_logical_and(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_bitwise_or()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::AmpAmp))
        {
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_bitwise_or()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op: BinaryOp::LogicalAnd,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_bitwise_or(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_bitwise_xor()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::Pipe))
        {
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_bitwise_xor()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op: BinaryOp::BitOr,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_bitwise_xor(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_bitwise_and()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::Caret))
        {
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_bitwise_and()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op: BinaryOp::BitXor,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_bitwise_and(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_equality()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::Amp))
        {
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_equality()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op: BinaryOp::BitAnd,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_equality(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_comparison()?;
        while self
            .next_non_newline_kind(self.pos)
            .is_some_and(|k| matches!(k, TokenKind::EqualEqual | TokenKind::BangEqual))
        {
            self.consume_newlines();
            let op = if self.check_simple(&TokenKind::EqualEqual) {
                BinaryOp::Equal
            } else {
                BinaryOp::NotEqual
            };
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_comparison()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_comparison(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_shift()?;
        loop {
            let op = match self.next_non_newline_kind(self.pos) {
                Some(TokenKind::Less) => Some(BinaryOp::LessThan),
                Some(TokenKind::LessEqual) => Some(BinaryOp::LessEqual),
                Some(TokenKind::Greater) => Some(BinaryOp::GreaterThan),
                Some(TokenKind::GreaterEqual) => Some(BinaryOp::GreaterEqual),
                _ => None,
            };
            let Some(op) = op else {
                break;
            };
            self.consume_newlines();
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_shift()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_shift(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_additive()?;
        loop {
            let op = if self.check_simple(&TokenKind::ShiftLeft) {
                Some(BinaryOp::ShiftLeft)
            } else if self.check_simple(&TokenKind::ShiftRight) {
                Some(BinaryOp::ShiftRight)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_additive()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_additive(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_multiplicative()?;
        while self.check_simple(&TokenKind::Plus) || self.check_simple(&TokenKind::Minus) {
            let op = if self.check_simple(&TokenKind::Plus) {
                BinaryOp::Add
            } else {
                BinaryOp::Subtract
            };
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_multiplicative()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_cast()?;
        while self.check_simple(&TokenKind::Star)
            || self.check_simple(&TokenKind::Slash)
            || self.check_simple(&TokenKind::Percent)
        {
            let op = if self.check_simple(&TokenKind::Star) {
                BinaryOp::Multiply
            } else if self.check_simple(&TokenKind::Slash) {
                BinaryOp::Divide
            } else {
                BinaryOp::Modulo
            };
            self.advance();
            self.consume_newlines();
            let rhs = self.parse_cast()?;
            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, CompileError> {
        if self.check_simple(&TokenKind::Minus) {
            self.advance();
            let expr = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(expr),
            });
        }
        if self.check_simple(&TokenKind::Bang) {
            self.advance();
            let expr = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::LogicalNot,
                expr: Box::new(expr),
            });
        }
        if self.check_simple(&TokenKind::Tilde) {
            self.advance();
            let expr = self.parse_unary()?;
            return Ok(Expr::Unary {
                op: UnaryOp::BitNot,
                expr: Box::new(expr),
            });
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<Expr, CompileError> {
        let mut expr = self.parse_primary()?;
        loop {
            if self.looks_like_specialization(&expr) {
                let type_args = self.parse_type_arg_list()?;
                expr = Expr::Specialize {
                    callee: Box::new(expr),
                    type_args,
                };
                continue;
            }

            if self.check_simple(&TokenKind::LBracket) {
                self.advance();
                let index = self.parse_expr()?;
                self.expect_simple(TokenKind::RBracket)?;
                expr = Expr::Index {
                    base: Box::new(expr),
                    index: Box::new(index),
                };
                continue;
            }

            if self.check_simple(&TokenKind::Dot) {
                self.advance();
                let field = self.expect_ident()?;
                expr = Expr::FieldAccess {
                    base: Box::new(expr),
                    field,
                };
                continue;
            }

            if self.check_simple(&TokenKind::At) {
                self.advance();
                let method = self.expect_ident()?;
                let args = self.parse_call_args()?;
                expr = Expr::MethodCall {
                    receiver: Box::new(expr),
                    method,
                    args,
                };
                continue;
            }

            if self.check_simple(&TokenKind::LParen) {
                if let Some(path) = expr.callee_path() {
                    if self.looks_like_struct_init() {
                        expr = self.parse_struct_init(path.join("."), Vec::new())?;
                        continue;
                    }
                }
                if let Expr::Specialize { callee, type_args } = &expr {
                    if let Some(path) = callee.callee_path() {
                        if self.looks_like_struct_init() {
                            expr = self.parse_struct_init(path.join("."), type_args.clone())?;
                            continue;
                        }
                    }
                }

                let args = self.parse_call_args()?;
                let is_error_constructor =
                    matches!(expr.as_path(), Some(path) if path.len() == 1 && path[0] == "error");
                expr = if is_error_constructor && args.len() == 1 {
                    Expr::Error {
                        message: Box::new(args.into_iter().next().expect("checked length")),
                    }
                } else {
                    Expr::Call {
                        callee: Box::new(expr),
                        args,
                    }
                };
                continue;
            }

            if self.check_simple(&TokenKind::Question) {
                self.advance();
                expr = Expr::Try(Box::new(expr));
                continue;
            }

            break;
        }
        Ok(expr)
    }

    fn parse_type_arg_list(&mut self) -> Result<Vec<Type>, CompileError> {
        self.expect_simple(TokenKind::LBracket)?;
        self.consume_newlines();
        let mut type_args = Vec::new();
        while !self.check_simple(&TokenKind::RBracket) {
            type_args.push(self.parse_type()?);
            if self.check_simple(&TokenKind::Comma) {
                self.advance();
                self.consume_newlines();
            } else {
                self.consume_newlines();
                break;
            }
        }
        self.expect_simple(TokenKind::RBracket)?;
        Ok(type_args)
    }

    fn parse_primary(&mut self) -> Result<Expr, CompileError> {
        match self.current().kind.clone() {
            TokenKind::Int(value) => {
                self.advance();
                Ok(Expr::Int(value))
            }
            TokenKind::Char(value) => {
                self.advance();
                Ok(Expr::Char(value))
            }
            TokenKind::Ident(name) if name == "true" || name == "false" => {
                self.advance();
                Ok(Expr::Bool(name == "true"))
            }
            TokenKind::Float(value) => {
                self.advance();
                Ok(Expr::Float(value))
            }
            TokenKind::Str(value) => {
                self.advance();
                Ok(Expr::String(value))
            }
            TokenKind::LBracket => self.parse_list_literal(),
            TokenKind::At => self.parse_builtin_call(),
            TokenKind::Ident(_) => self.parse_name(),
            TokenKind::LParen => {
                self.advance();
                self.consume_newlines();
                let expr = self.parse_expr()?;
                self.consume_newlines();
                self.expect_simple(TokenKind::RParen)?;
                Ok(expr)
            }
            TokenKind::LBrace => self.parse_pack(),
            _ => Err(self.error_at_current("expected an expression")),
        }
    }

    fn parse_builtin_call(&mut self) -> Result<Expr, CompileError> {
        self.expect_simple(TokenKind::At)?;
        let name = self.expect_ident()?;
        if name == "sizeof" {
            self.expect_simple(TokenKind::LParen)?;
            let ty = self.parse_type()?;
            self.expect_simple(TokenKind::RParen)?;
            return Ok(Expr::SizeOf(ty));
        }
        if name == "bitcast" {
            self.expect_simple(TokenKind::LParen)?;
            let expr = self.parse_expr()?;
            self.expect_simple(TokenKind::Comma)?;
            let ty = self.parse_type()?;
            self.expect_simple(TokenKind::RParen)?;
            return Ok(Expr::BitCast {
                expr: Box::new(expr),
                ty,
            });
        }
        let args = self.parse_call_args()?;
        Ok(Expr::BuiltinCall { name, args })
    }

    fn parse_name(&mut self) -> Result<Expr, CompileError> {
        let name = self.expect_ident()?;
        if name == "none" {
            Ok(Expr::None)
        } else {
            Ok(Expr::Path(vec![name]))
        }
    }

    fn parse_struct_init(
        &mut self,
        name: String,
        type_args: Vec<Type>,
    ) -> Result<Expr, CompileError> {
        self.expect_simple(TokenKind::LParen)?;
        self.consume_newlines();
        let mut fields = Vec::new();
        while !self.check_simple(&TokenKind::RParen) {
            let field_name = self.expect_ident()?;
            self.expect_simple(TokenKind::Colon)?;
            let value = self.parse_expr()?;
            fields.push(FieldInit {
                name: field_name,
                value,
            });
            if self.check_simple(&TokenKind::Comma) {
                self.advance();
                self.consume_newlines();
            } else {
                self.consume_newlines();
                break;
            }
        }
        self.expect_simple(TokenKind::RParen)?;
        Ok(Expr::StructInit {
            name,
            type_args,
            fields,
        })
    }

    fn parse_pack(&mut self) -> Result<Expr, CompileError> {
        self.expect_simple(TokenKind::LBrace)?;
        self.consume_newlines();
        let mut values = Vec::new();
        if !self.check_simple(&TokenKind::RBrace) {
            loop {
                values.push(self.parse_expr()?);
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    self.consume_newlines();
                } else {
                    self.consume_newlines();
                    break;
                }
            }
        }
        self.expect_simple(TokenKind::RBrace)?;
        Ok(Expr::Pack(values))
    }

    fn parse_list_literal(&mut self) -> Result<Expr, CompileError> {
        self.expect_simple(TokenKind::LBracket)?;
        self.consume_newlines();
        let mut values = Vec::new();
        if !self.check_simple(&TokenKind::RBracket) {
            loop {
                values.push(self.parse_expr()?);
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    self.consume_newlines();
                } else {
                    self.consume_newlines();
                    break;
                }
            }
        }
        self.expect_simple(TokenKind::RBracket)?;
        Ok(Expr::ListLiteral(values))
    }

    fn parse_type(&mut self) -> Result<Type, CompileError> {
        let ty = self.parse_non_result_type()?;
        if self.check_simple(&TokenKind::Pipe) {
            self.advance();
            match self.current().kind.clone() {
                TokenKind::Ident(name) if name == "error" => {
                    self.advance();
                    Ok(Type::Result(Box::new(ty)))
                }
                _ => Err(self.error_at_current("expected `error` after `|` in a result type")),
            }
        } else {
            Ok(ty)
        }
    }

    fn parse_non_result_type(&mut self) -> Result<Type, CompileError> {
        match self.current().kind.clone() {
            TokenKind::Void => {
                self.advance();
                Ok(Type::Void)
            }
            TokenKind::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            TokenKind::I8 => {
                self.advance();
                Ok(Type::I8)
            }
            TokenKind::I16 => {
                self.advance();
                Ok(Type::I16)
            }
            TokenKind::I32 => {
                self.advance();
                Ok(Type::I32)
            }
            TokenKind::I64 => {
                self.advance();
                Ok(Type::I64)
            }
            TokenKind::Isize => {
                self.advance();
                Ok(Type::Isize)
            }
            TokenKind::U16 => {
                self.advance();
                Ok(Type::U16)
            }
            TokenKind::U32 => {
                self.advance();
                Ok(Type::U32)
            }
            TokenKind::U64 => {
                self.advance();
                Ok(Type::U64)
            }
            TokenKind::Usize => {
                self.advance();
                Ok(Type::Usize)
            }
            TokenKind::U8 => {
                self.advance();
                Ok(Type::U8)
            }
            TokenKind::F32 => {
                self.advance();
                Ok(Type::F32)
            }
            TokenKind::F64 => {
                self.advance();
                Ok(Type::F64)
            }
            TokenKind::Mut => {
                self.advance();
                self.expect_simple(TokenKind::LParen)?;
                let inner = self.parse_type()?;
                self.expect_simple(TokenKind::RParen)?;
                Ok(Type::Mut(Box::new(inner)))
            }
            TokenKind::Ident(name) => {
                if name == "_" {
                    self.advance();
                    return Ok(Type::Infer);
                }
                let mut segments = vec![name];
                self.advance();
                while self.check_simple(&TokenKind::Dot) {
                    self.advance();
                    segments.push(self.expect_ident()?);
                }
                let name = segments.join(".");
                if self.check_simple(&TokenKind::LBracket) {
                    Ok(Type::Applied(name, self.parse_type_arg_list()?))
                } else {
                    Ok(Type::Named(name))
                }
            }
            TokenKind::Ref => {
                self.advance();
                self.expect_simple(TokenKind::LParen)?;
                let inner = self.parse_type()?;
                self.expect_simple(TokenKind::RParen)?;
                Ok(Type::Ref(Box::new(inner)))
            }
            TokenKind::List => {
                self.advance();
                self.expect_simple(TokenKind::LBracket)?;
                let inner = self.parse_type()?;
                self.expect_simple(TokenKind::RBracket)?;
                Ok(Type::List(Box::new(inner)))
            }
            TokenKind::LBracket => {
                self.advance();
                let TokenKind::Int(n) = self.current().kind.clone() else {
                    return Err(self.error_at_current(
                        "expected an integer length in fixed array type `[N]T`",
                    ));
                };
                self.advance();
                self.expect_simple(TokenKind::RBracket)?;
                let inner = self.parse_non_result_type()?;
                Ok(Type::FixedArray(n, Box::new(inner)))
            }
            TokenKind::LParen => {
                self.advance();
                self.expect_simple(TokenKind::Fn)?;
                self.expect_simple(TokenKind::LParen)?;
                let mut params = Vec::new();
                if !self.check_simple(&TokenKind::RParen) {
                    loop {
                        params.push(self.parse_type()?);
                        if self.check_simple(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                }
                self.expect_simple(TokenKind::RParen)?;
                let ret = if self.starts_type() {
                    self.parse_type()?
                } else {
                    Type::Void
                };
                self.expect_simple(TokenKind::RParen)?;
                Ok(Type::FnPtr(params, Box::new(ret)))
            }
            _ => Err(self.error_at_current("expected a type")),
        }
    }

    fn starts_type(&self) -> bool {
        matches!(
            self.current().kind,
            TokenKind::Void
                | TokenKind::Bool
                | TokenKind::I8
                | TokenKind::I16
                | TokenKind::I32
                | TokenKind::I64
                | TokenKind::Isize
                | TokenKind::U16
                | TokenKind::U32
                | TokenKind::U64
                | TokenKind::Usize
                | TokenKind::U8
                | TokenKind::F32
                | TokenKind::F64
                | TokenKind::Mut
                | TokenKind::Ref
                | TokenKind::List
                | TokenKind::LBracket
                | TokenKind::LParen
                | TokenKind::Ident(_)
        )
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, CompileError> {
        self.expect_simple(TokenKind::LParen)?;
        self.parse_call_args_after_lparen()
    }

    fn parse_call_args_after_lparen(&mut self) -> Result<Vec<Expr>, CompileError> {
        self.consume_newlines();
        let mut args = Vec::new();
        if !self.check_simple(&TokenKind::RParen) {
            loop {
                args.push(self.parse_expr()?);
                if self.check_simple(&TokenKind::Comma) {
                    self.advance();
                    self.consume_newlines();
                } else {
                    self.consume_newlines();
                    break;
                }
            }
        }
        self.expect_simple(TokenKind::RParen)?;
        Ok(args)
    }

    fn maybe_promote_bracketless_call(&self, expr: Expr) -> Expr {
        match expr {
            Expr::Path(_) => Expr::Call {
                callee: Box::new(expr),
                args: Vec::new(),
            },
            other => other,
        }
    }

    fn expect_ident(&mut self) -> Result<String, CompileError> {
        match self.current().kind.clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(self.error_at_current("expected an identifier")),
        }
    }

    fn expect_simple(&mut self, expected: TokenKind) -> Result<(), CompileError> {
        if self.check_simple(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(self.error_at_current(format!("expected {}", Self::describe(&expected))))
        }
    }

    fn expect_newline(&mut self, message: &str) -> Result<(), CompileError> {
        if self.check_simple(&TokenKind::Newline) {
            self.consume_newlines();
            Ok(())
        } else {
            Err(self.error_at_current(message))
        }
    }

    fn expect_stmt_terminator(&mut self) -> Result<(), CompileError> {
        if self.at_stmt_end() {
            self.consume_newlines();
            Ok(())
        } else {
            Err(self.error_at_current("expected a newline after the statement"))
        }
    }

    fn at_stmt_end(&self) -> bool {
        self.check_simple(&TokenKind::Newline)
            || self.check_simple(&TokenKind::End)
            || self.check_simple(&TokenKind::Else)
            || self.check_simple(&TokenKind::Eof)
            || self.check_simple(&TokenKind::RParen)
    }

    fn consume_newlines(&mut self) {
        while self.check_simple(&TokenKind::Newline) {
            self.advance();
        }
    }

    fn check_simple(&self, expected: &TokenKind) -> bool {
        std::mem::discriminant(&self.current().kind) == std::mem::discriminant(expected)
    }

    fn check_next_simple(&self, expected: &TokenKind) -> bool {
        self.tokens.get(self.pos + 1).is_some_and(|token| {
            std::mem::discriminant(&token.kind) == std::mem::discriminant(expected)
        })
    }

    fn check_any_simple(&self, expected: &[TokenKind]) -> bool {
        expected.iter().any(|kind| self.check_simple(kind))
    }

    fn looks_like_struct_init(&self) -> bool {
        self.check_simple(&TokenKind::LParen)
            && self
                .next_non_newline_kind(self.pos + 1)
                .is_some_and(|kind| matches!(kind, TokenKind::Ident(_)))
            && self
                .next_non_newline_kind_after_ident(self.pos + 1)
                .is_some_and(|kind| matches!(kind, TokenKind::Colon))
    }

    fn next_non_newline_kind(&self, start: usize) -> Option<&TokenKind> {
        self.tokens
            .iter()
            .skip(start)
            .find(|token| !matches!(token.kind, TokenKind::Newline))
            .map(|token| &token.kind)
    }

    fn next_non_newline_kind_after_ident(&self, start: usize) -> Option<&TokenKind> {
        let mut saw_ident = false;
        for token in self.tokens.iter().skip(start) {
            if matches!(token.kind, TokenKind::Newline) {
                continue;
            }
            if !saw_ident {
                if matches!(token.kind, TokenKind::Ident(_)) {
                    saw_ident = true;
                    continue;
                }
                return None;
            }
            return Some(&token.kind);
        }
        None
    }

    fn looks_like_specialization(&self, expr: &Expr) -> bool {
        self.supports_specialization(expr)
            && self.check_simple(&TokenKind::LBracket)
            && self
                .next_non_newline_kind(self.pos + 1)
                .is_some_and(|kind| self.kind_starts_type(kind))
            && self
                .token_after_matching_bracket(self.pos)
                .is_some_and(|kind| matches!(kind, TokenKind::LParen))
    }

    fn supports_specialization(&self, expr: &Expr) -> bool {
        let _ = self;
        match expr {
            Expr::Path(_) => true,
            Expr::FieldAccess { base, .. } => self.supports_specialization(base),
            _ => false,
        }
    }

    fn token_after_matching_bracket(&self, start: usize) -> Option<&TokenKind> {
        let mut depth = 0usize;
        for index in start..self.tokens.len() {
            match self.tokens[index].kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        return self.next_non_newline_kind(index + 1);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn kind_starts_type(&self, kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::Void
                | TokenKind::Bool
                | TokenKind::I8
                | TokenKind::I16
                | TokenKind::I32
                | TokenKind::I64
                | TokenKind::Isize
                | TokenKind::U16
                | TokenKind::U32
                | TokenKind::U64
                | TokenKind::Usize
                | TokenKind::U8
                | TokenKind::F32
                | TokenKind::F64
                | TokenKind::Mut
                | TokenKind::Ref
                | TokenKind::List
                | TokenKind::Ident(_)
        )
    }

    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn advance(&mut self) {
        if !self.is_eof() {
            self.pos += 1;
        }
    }

    fn is_eof(&self) -> bool {
        matches!(self.current().kind, TokenKind::Eof)
    }

    fn error_at_current(&self, message: impl Into<String>) -> CompileError {
        let token = self.current();
        CompileError::new(format!(
            "{} at {}:{}",
            message.into(),
            token.line,
            token.column
        ))
    }

    fn describe(kind: &TokenKind) -> &'static str {
        match kind {
            TokenKind::Pub => "`pub`",
            TokenKind::Def => "`def`",
            TokenKind::Extern => "`extern`",
            TokenKind::Test => "`test`",
            TokenKind::Match => "`match`",
            TokenKind::Interface => "`interface`",
            TokenKind::Type => "`type`",
            TokenKind::Typeset => "`typeset`",
            TokenKind::Union => "`union`",
            TokenKind::Enum => "`enum`",
            TokenKind::End => "`end`",
            TokenKind::Var => "`var`",
            TokenKind::Val => "`val`",
            TokenKind::Return => "`return`",
            TokenKind::If => "`if`",
            TokenKind::Guard => "`guard`",
            TokenKind::Else => "`else`",
            TokenKind::Elif => "`elif`",
            TokenKind::Break => "`break`",
            TokenKind::Continue => "`continue`",
            TokenKind::Parallel => "`parallel`",
            TokenKind::For => "`for`",
            TokenKind::When => "`when`",
            TokenKind::In => "`in`",
            TokenKind::As => "`as`",
            TokenKind::Mut => "`mut`",
            TokenKind::Ref => "`ref`",
            TokenKind::List => "`list`",
            TokenKind::Void => "`void`",
            TokenKind::Bool => "`bool`",
            TokenKind::I8 => "`i8`",
            TokenKind::I16 => "`i16`",
            TokenKind::I32 => "`i32`",
            TokenKind::I64 => "`i64`",
            TokenKind::Isize => "`isize`",
            TokenKind::U16 => "`u16`",
            TokenKind::U32 => "`u32`",
            TokenKind::U64 => "`u64`",
            TokenKind::Usize => "`usize`",
            TokenKind::U8 => "`u8`",
            TokenKind::F32 => "`f32`",
            TokenKind::F64 => "`f64`",
            TokenKind::Float(_) => "a float",
            TokenKind::Newline => "a newline",
            TokenKind::At => "`@`",
            TokenKind::LParen => "`(`",
            TokenKind::RParen => "`)`",
            TokenKind::LBracket => "`[`",
            TokenKind::RBracket => "`]`",
            TokenKind::LBrace => "`{`",
            TokenKind::RBrace => "`}`",
            TokenKind::Comma => "`,`",
            TokenKind::Colon => "`:`",
            TokenKind::ColonColon => "`::`",
            TokenKind::Dot => "`.`",
            TokenKind::DotDot => "`..`",
            TokenKind::Assign => "`=`",
            TokenKind::EqualEqual => "`==`",
            TokenKind::BangEqual => "`!=`",
            TokenKind::Amp => "`&`",
            TokenKind::AmpAmp => "`&&`",
            TokenKind::AmpEqual => "`&=`",
            TokenKind::Pipe => "`|`",
            TokenKind::PipePipe => "`||`",
            TokenKind::PipeEqual => "`|=`",
            TokenKind::Caret => "`^`",
            TokenKind::CaretEqual => "`^=`",
            TokenKind::Bang => "`!`",
            TokenKind::Tilde => "`~`",
            TokenKind::Less => "`<`",
            TokenKind::LessEqual => "`<=`",
            TokenKind::ShiftLeft => "`<<`",
            TokenKind::Greater => "`>`",
            TokenKind::GreaterEqual => "`>=`",
            TokenKind::ShiftRight => "`>>`",
            TokenKind::Star => "`*`",
            TokenKind::StarEqual => "`*=`",
            TokenKind::Slash => "`/`",
            TokenKind::SlashEqual => "`/=`",
            TokenKind::Percent => "`%`",
            TokenKind::Minus => "`-`",
            TokenKind::MinusMinus => "`--`",
            TokenKind::MinusEqual => "`-=`",
            TokenKind::Plus => "`+`",
            TokenKind::PlusPlus => "`++`",
            TokenKind::PlusEqual => "`+=`",
            TokenKind::FatArrow => "`=>`",
            TokenKind::Question => "`?`",
            TokenKind::Eof => "end of file",
            TokenKind::Ident(_) => "an identifier",
            TokenKind::Int(_) => "an integer",
            TokenKind::Char(_) => "a character",
            TokenKind::Str(_) => "a string",
            TokenKind::Fn => "`fn`",
            TokenKind::Link => "`link`",
            TokenKind::Defer => "`defer`",
        }
    }
}

fn is_supported_platform_name(name: &str) -> bool {
    matches!(
        name,
        "linux"
            | "windows"
            | "darwin"
            | "macos"
            | "dragonflybsd"
            | "freebsd"
            | "openbsd"
            | "netbsd"
            | "redox"
            | "android"
            | "ios"
            | "posix"
    )
}

fn platform_matches(name: &str) -> bool {
    match name {
        "linux" => cfg!(target_os = "linux"),
        "windows" => cfg!(target_os = "windows"),
        "darwin" | "macos" => cfg!(target_os = "macos"),
        "dragonflybsd" => cfg!(target_os = "dragonfly"),
        "freebsd" => cfg!(target_os = "freebsd"),
        "openbsd" => cfg!(target_os = "openbsd"),
        "netbsd" => cfg!(target_os = "netbsd"),
        "redox" => cfg!(target_os = "redox"),
        "android" => cfg!(target_os = "android"),
        "ios" => cfg!(target_os = "ios"),
        "posix" => cfg!(unix),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::parse_program;
    use crate::{
        ast::{BinaryOp, Expr, Stmt, Type, UnaryOp},
        lexer::lex,
    };

    #[test]
    fn parses_pub_function() {
        let source = "pub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(program.functions[0].is_pub);
        assert_eq!(program.functions[0].name, "main");
    }

    #[test]
    fn parses_extern_function() {
        let source = "extern def sleep(t u32) void :: \"sleep\"\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].extern_name.as_deref(), Some("sleep"));
        assert_eq!(program.functions[0].params[0].ty, Type::U32);
        assert!(program.functions[0].body.is_empty());
    }

    #[test]
    fn parses_public_extern_function() {
        let source = "pub extern def sleep(t u32) void :: \"sleep\"\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(program.functions[0].is_pub);
        assert_eq!(program.functions[0].extern_name.as_deref(), Some("sleep"));
    }

    #[test]
    fn parses_extern_header_include() {
        let source = "extern \"windows.h\"\nextern def sleep(t u32) void :: \"sleep\"\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.extern_headers, vec!["windows.h"]);
        assert_eq!(program.functions.len(), 1);
    }

    #[test]
    fn parses_public_type_definition() {
        let source = "pub type Arena\n\tcap usize\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(program.type_defs[0].is_pub);
        assert_eq!(program.type_defs[0].name, "Arena");
    }

    #[test]
    fn parses_namespaced_function_definition() {
        let source = "pub def Arena.new(cap usize) Arena\n\treturn Arena(cap: cap)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions[0].name, "Arena.new");
    }

    #[test]
    fn ignores_top_level_test_blocks() {
        let source = "extern def strcmp(x ref(u8), y ref(u8)) :: \"strcmp\"\n\ntest \"equals works\"\n\tassert strcmp(\"a\", \"a\")\nend\n\npub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions.len(), 2);
        assert_eq!(program.tests.len(), 1);
        assert_eq!(program.functions[0].name, "strcmp");
        assert_eq!(program.functions[1].name, "main");
    }

    #[test]
    fn parses_extern_type_alias_and_packed_type() {
        let source = "extern type Point\n\tx i32\n\ty i32\nend\ntype Count = i32\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.type_defs.len(), 2);
        assert_eq!(program.type_defs[0].name, "Point");
        assert!(program.type_defs[0].is_extern);
        assert!(program.type_defs[0].alias.is_none());
        assert_eq!(program.type_defs[0].fields.len(), 2);

        assert_eq!(program.type_defs[1].name, "Count");
        assert!(!program.type_defs[1].is_extern);
        assert_eq!(program.type_defs[1].alias, Some(Type::I32));
        assert!(program.type_defs[1].fields.is_empty());
    }

    #[test]
    fn rejects_extern_type_aliases() {
        let source = "extern type Useconds = i32\n";
        let error = parse_program(lex(source).unwrap()).unwrap_err();

        assert!(
            error
                .message
                .contains("extern types must be explicitly defined with fields")
        );
    }

    #[test]
    fn parses_top_level_module_use() {
        let source = "val some_module = use(\"some_file\")\npub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.module_uses.len(), 1);
        assert_eq!(program.module_uses[0].name, "some_module");
        assert_eq!(program.module_uses[0].path, "some_file");
        assert!(program.type_defs.is_empty());
        assert_eq!(program.functions.len(), 1);
    }

    #[test]
    fn parses_top_level_single_hash_comments() {
        let source = "# comment\npub def main() void\n\t# inside function\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions.len(), 1);
        assert_eq!(program.functions[0].name, "main");
    }

    #[test]
    fn parses_type_defs_and_field_access() {
        let source = "type SomeType\n\tx i32\n\ty i32\nend\npub def main() void\n\tval st = SomeType(x: 10, y: 12)\n\t@print(\"{d}\", {st.x})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name, "SomeType");
        assert!(!program.type_defs[0].is_extern);
        assert!(program.type_defs[0].alias.is_none());
        assert_eq!(program.type_defs[0].fields.len(), 2);

        match &program.functions[0].body[0] {
            Stmt::VarDecl {
                init: Expr::StructInit { name, fields, .. },
                ..
            } => {
                assert_eq!(name, "SomeType");
                assert_eq!(fields.len(), 2);
            }
            other => panic!("expected struct init, got {other:?}"),
        }
    }

    #[test]
    fn parses_pragma_for_loop() {
        let source =
            "pub def main() void\n@(\"omp parallel for\")\nfor var i = 0 .. 10\nend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::ForRange {
                pragma,
                var_name,
                body,
                ..
            } => {
                assert_eq!(pragma.as_deref(), Some("omp parallel for"));
                assert_eq!(var_name, "i");
                assert!(body.is_empty());
            }
            other => panic!("expected for loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_conditional_for_loop() {
        let source = "pub def main() void\n\tfor (value < 10)\n\t\tvalue++\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::While {
                condition, body, ..
            } => {
                assert!(matches!(
                    condition,
                    Expr::Binary {
                        op: BinaryOp::LessThan,
                        ..
                    }
                ));
                assert!(matches!(body[0], Stmt::Increment { .. }));
            }
            other => panic!("expected conditional for loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_conditional_for_loop_without_parentheses() {
        let source = "pub def main() void\n\tfor value < 10\n\t\tvalue++\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::While {
                condition, body, ..
            } => {
                assert!(matches!(
                    condition,
                    Expr::Binary {
                        op: BinaryOp::LessThan,
                        ..
                    }
                ));
                assert!(matches!(body[0], Stmt::Increment { .. }));
            }
            other => panic!("expected conditional for loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_complex_conditional_for_loop_without_parentheses() {
        let source =
            "pub def main() void\n\tfor out > 1 as usize && ready()\n\t\tout--\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::While {
                condition:
                    Expr::Binary {
                        op: BinaryOp::LogicalAnd,
                        lhs,
                        rhs,
                    },
                body,
                ..
            } => {
                assert!(matches!(
                    lhs.as_ref(),
                    Expr::Binary {
                        op: BinaryOp::GreaterThan,
                        rhs,
                        ..
                    } if matches!(
                        rhs.as_ref(),
                        Expr::Cast { ty: Type::Usize, .. }
                    )
                ));
                assert!(matches!(rhs.as_ref(), Expr::Call { .. }));
                assert!(matches!(body[0], Stmt::Decrement { .. }));
            }
            other => panic!("expected conditional for loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_complex_parenthesized_conditional_for_loop() {
        let source =
            "pub def main() void\n\tfor (out > 1 as usize && !done)\n\t\tout--\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::While {
                condition:
                    Expr::Binary {
                        op: BinaryOp::LogicalAnd,
                        lhs,
                        rhs,
                    },
                ..
            } => {
                assert!(matches!(
                    lhs.as_ref(),
                    Expr::Binary {
                        op: BinaryOp::GreaterThan,
                        rhs,
                        ..
                    } if matches!(
                        rhs.as_ref(),
                        Expr::Cast { ty: Type::Usize, .. }
                    )
                ));
                assert!(matches!(
                    rhs.as_ref(),
                    Expr::Unary {
                        op: UnaryOp::LogicalNot,
                        ..
                    }
                ));
            }
            other => panic!("expected conditional for loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_top_level_when_blocks_for_current_platform() {
        let source =
            "when posix\n\tpub def posix_only() void\n\tend\nend\n\npub def main() void\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions.len(), if cfg!(unix) { 2 } else { 1 });
        assert_eq!(program.functions.last().unwrap().name, "main");
    }

    #[test]
    fn parses_statement_when_blocks_for_current_platform() {
        let source = "pub def main() void\n\twhen posix\n\t\t@puts(\"posix\")\n\tend\n\twhen windows\n\t\t@puts(\"windows\")\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        let body = &program.functions[0].body;
        if cfg!(unix) {
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Expr { .. }));
        } else {
            assert_eq!(body.len(), 1);
            assert!(matches!(body[0], Stmt::Expr { .. }));
        }
    }

    #[test]
    fn rejects_unknown_platform_selector() {
        let source = "pub def main() void\n\twhen solarpunk\n\t\t@puts(\"nope\")\n\tend\nend\n";
        let error = parse_program(lex(source).unwrap()).unwrap_err();

        assert!(
            error
                .message
                .contains("unsupported platform selector `solarpunk`")
        );
    }

    #[test]
    fn parses_multiline_function_signature() {
        let source = "def add(\n\ta i32,\n\tb i32\n) i32\n\treturn a + b\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions[0].name, "add");
        assert_eq!(program.functions[0].params.len(), 2);
        assert_eq!(program.functions[0].return_type, Type::I32);
    }

    #[test]
    fn parses_extended_numeric_primitive_types() {
        let source = "def numerics(a i64, b f64, c usize) bool\n\treturn 0 == 0\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.functions[0].params[0].ty, Type::I64);
        assert_eq!(program.functions[0].params[1].ty, Type::F64);
        assert_eq!(program.functions[0].params[2].ty, Type::Usize);
        assert_eq!(program.functions[0].return_type, Type::Bool);
    }

    #[test]
    fn parses_mutable_ref_type() {
        let source = "def concat(dest mut(ref(u8)), src ref(u8)) ref(u8)\n\treturn dest\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(
            &program.functions[0].params[0].ty,
            Type::Mut(inner) if matches!(inner.as_ref(), Type::Ref(inner) if inner.as_ref() == &Type::U8)
        ));
    }

    #[test]
    fn parses_list_declaration_foreach_and_bracketless_call() {
        let source = "pub def helper() void\nend\npub def main() void\n\tval values list[i32] = [1, 2, 3]\n\tfor var value in values\n\t\t@print(\"{d}\", {value})\n\tend\n\thelper\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[1].body[0] {
            Stmt::VarDecl {
                declared_type: Some(Type::List(inner)),
                init: Expr::ListLiteral(values),
                ..
            } => {
                assert_eq!(**inner, Type::I32);
                assert_eq!(values.len(), 3);
            }
            other => panic!("expected typed list declaration, got {other:?}"),
        }

        match &program.functions[1].body[1] {
            Stmt::ForEach {
                var_name,
                iterable,
                body,
                ..
            } => {
                assert_eq!(var_name, "value");
                assert!(
                    matches!(iterable, Expr::Path(path) if path == &vec!["values".to_string()])
                );
                assert_eq!(body.len(), 1);
            }
            other => panic!("expected foreach loop, got {other:?}"),
        }

        match &program.functions[1].body[2] {
            Stmt::Expr {
                expr: Expr::Call { callee, args },
                ..
            } => {
                assert!(
                    matches!(callee.as_ref(), Expr::Path(path) if path == &vec!["helper".to_string()])
                );
                assert!(args.is_empty());
            }
            other => panic!("expected bracketless call, got {other:?}"),
        }
    }

    #[test]
    fn parses_if_loop_index_and_cast() {
        let source = "pub def main() void\n\tvar rows list[list[i32]] = []\n\tfor\n\t\tif rows[0][1] == -1\n\t\t\tcontinue\n\t\telse\n\t\t\t@append(rows, [1, 2] as list[i32])\n\t\tend\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(program.functions[0].body[1], Stmt::Loop { .. }));
    }

    #[test]
    fn parses_multiline_grouped_return_expression() {
        let source = "pub def main() i32\n\treturn (\n\t\t1 +\n\t\t2\n\t)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(
            &program.functions[0].body[0],
            Stmt::Return {
                value: Some(Expr::Binary {
                    op: BinaryOp::Add,
                    ..
                }),
                ..
            }
        ));
    }

    #[test]
    fn parses_multiline_assignment_to_indexed_field() {
        let source = "type Matrix\n\trows list[list[i32]]\nend\npub def main() void\n\tvar m = Matrix(rows: [[0]])\n\tm.rows[0][0] =\n\t\t1 + 2\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(
            &program.functions[0].body[1],
            Stmt::Assign {
                target: Expr::Index { .. },
                value: Expr::Binary {
                    op: BinaryOp::Add,
                    ..
                },
                ..
            }
        ));
    }

    #[test]
    fn parses_multiply_assignment() {
        let source = "pub def main() void\n\tvar value = 3\n\tvalue *= 2\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(
            program.functions[0].body[1],
            Stmt::MulAssign { .. }
        ));
    }

    #[test]
    fn parses_full_comparison_set() {
        let source = "pub def main() void\n\tif 1 < 2 && 2 <= 2 && 3 > 2 && 4 >= 4\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert!(matches!(program.functions[0].body[0], Stmt::If { .. }));
    }

    #[test]
    fn parses_bitwise_and_boolean_style_operators() {
        let source = "pub def main() void\n\tvar mask = (1 << 2) & 7 | 8 ^ 3\n\tmask &= 6\n\tmask |= 1\n\tmask ^= 2\n\tval product = 2 + 3 * 4\n\tif !(1 == 0) && 2 == 2\n\t\t@print(\"{d} {d}\", {mask, product})\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::VarDecl { init, .. } => match init {
                Expr::Binary {
                    op: BinaryOp::BitOr,
                    lhs,
                    rhs,
                } => {
                    assert!(matches!(
                        rhs.as_ref(),
                        Expr::Binary {
                            op: BinaryOp::BitXor,
                            ..
                        }
                    ));
                    assert!(matches!(
                        lhs.as_ref(),
                        Expr::Binary {
                            op: BinaryOp::BitAnd,
                            lhs,
                            ..
                        } if matches!(
                            lhs.as_ref(),
                            Expr::Binary {
                                op: BinaryOp::ShiftLeft,
                                ..
                            }
                        )
                    ));
                }
                other => panic!("expected operator tree, got {other:?}"),
            },
            other => panic!("expected variable declaration, got {other:?}"),
        }

        match &program.functions[0].body[1] {
            Stmt::BitAndAssign { .. } => {}
            other => panic!("expected bitwise and assign, got {other:?}"),
        }

        match &program.functions[0].body[2] {
            Stmt::BitOrAssign { .. } => {}
            other => panic!("expected bitwise or assign, got {other:?}"),
        }

        match &program.functions[0].body[3] {
            Stmt::BitXorAssign { .. } => {}
            other => panic!("expected bitwise xor assign, got {other:?}"),
        }

        match &program.functions[0].body[4] {
            Stmt::VarDecl { init, .. } => assert!(matches!(
                init,
                Expr::Binary {
                    op: BinaryOp::Add,
                    rhs,
                    ..
                } if matches!(
                    rhs.as_ref(),
                    Expr::Binary {
                        op: BinaryOp::Multiply,
                        ..
                    }
                )
            )),
            other => panic!("expected variable declaration, got {other:?}"),
        }

        match &program.functions[0].body[5] {
            Stmt::If { condition, .. } => assert!(matches!(
                condition,
                Expr::Binary {
                    op: BinaryOp::LogicalAnd,
                    lhs,
                    rhs,
                } if matches!(
                    lhs.as_ref(),
                    Expr::Unary {
                        op: UnaryOp::LogicalNot,
                        expr,
                    } if matches!(
                        expr.as_ref(),
                        Expr::Binary {
                            op: BinaryOp::Equal,
                            ..
                        }
                    )
                ) && matches!(
                    rhs.as_ref(),
                    Expr::Binary {
                        op: BinaryOp::Equal,
                        ..
                    }
                )
            )),
            other => panic!("expected if statement, got {other:?}"),
        }
    }

    #[test]
    fn parses_at_builtin_calls() {
        let source = "pub def main() void\n@print(\"{d}\", {1})\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Expr {
                expr: Expr::BuiltinCall { name, args },
                ..
            } => {
                assert_eq!(name, "print");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected @builtin expression, got {other:?}"),
        }
    }

    #[test]
    fn parses_specialized_qualified_function_calls() {
        let source = "pub def main() void\n\tStringBuilder.new[Arena](ac, 128)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Expr {
                expr: Expr::Call { callee, args },
                ..
            } => {
                assert_eq!(args.len(), 2);
                match callee.as_ref() {
                    Expr::Specialize { callee, type_args } => {
                        assert_eq!(type_args.len(), 1);
                        assert!(matches!(&type_args[0], Type::Named(name) if name == "Arena"));
                        assert!(matches!(
                            callee.as_ref(),
                            Expr::FieldAccess { base, field }
                                if matches!(base.as_ref(), Expr::Path(path) if path == &vec!["StringBuilder".to_string()])
                                    && field == "new"
                        ));
                    }
                    other => panic!("expected specialized callee, got {other:?}"),
                }
            }
            other => panic!("expected call expression, got {other:?}"),
        }
    }

    #[test]
    fn parses_generic_type_defs_typesets_and_specialized_struct_inits() {
        let source = "type Pair[T, U]\n\tfirst T\n\tsecond U\nend\n\npub typeset Integer\n\ti32, u32\nend\n\ndef print_pair[T: Integer](p Pair[T, ref(u8)]) Pair[T, ref(u8)]\n\treturn Pair[T, ref(u8)](first: p.first, second: p.second)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        assert_eq!(program.type_defs.len(), 1);
        assert_eq!(program.type_defs[0].name, "Pair");
        assert_eq!(program.type_defs[0].generic_params.len(), 2);
        assert_eq!(program.typesets.len(), 1);
        assert_eq!(program.typesets[0].name, "Integer");
        assert!(matches!(
            program.typesets[0].members.as_slice(),
            [Type::I32, Type::U32]
        ));

        let function = &program.functions[0];
        assert_eq!(function.generic_params.len(), 1);
        assert_eq!(function.generic_params[0].name, "T");
        assert!(matches!(
            function.generic_params[0].constraints.as_slice(),
            [Type::Named(name)] if name == "Integer"
        ));
        assert!(matches!(
            &function.params[0].ty,
            Type::Applied(name, type_args)
                if name == "Pair"
                    && matches!(type_args.as_slice(), [Type::Named(first), Type::Ref(inner)]
                        if first == "T" && matches!(inner.as_ref(), Type::U8))
        ));
        assert!(matches!(
            &function.return_type,
            Type::Applied(name, type_args)
                if name == "Pair"
                    && matches!(type_args.as_slice(), [Type::Named(first), Type::Ref(inner)]
                        if first == "T" && matches!(inner.as_ref(), Type::U8))
        ));

        match &function.body[0] {
            Stmt::Return {
                value:
                    Some(Expr::StructInit {
                        name,
                        type_args,
                        fields,
                    }),
                ..
            } => {
                assert_eq!(name, "Pair");
                assert!(matches!(
                    type_args.as_slice(),
                    [Type::Named(first), Type::Ref(inner)]
                        if first == "T" && matches!(inner.as_ref(), Type::U8)
                ));
                assert_eq!(fields.len(), 2);
            }
            other => panic!("expected specialized struct init, got {other:?}"),
        }
    }

    #[test]
    fn parses_guard_as_inverted_if() {
        let source = "pub def main() void\n\tguard (1 == 2) else\n\t\treturn\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                assert!(else_body.is_empty());
                assert_eq!(then_body.len(), 1);
                assert!(matches!(
                    condition,
                    Expr::Unary {
                        op: UnaryOp::LogicalNot,
                        expr,
                    } if matches!(
                        expr.as_ref(),
                        Expr::Binary {
                            op: BinaryOp::Equal,
                            ..
                        }
                    )
                ));
            }
            other => panic!("expected inverted if statement, got {other:?}"),
        }
    }

    #[test]
    fn parses_bool_literals() {
        let source = "pub def main() void\n\tassert true\n\treturn false\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Assert { condition, .. } => assert!(matches!(condition, Expr::Bool(true))),
            other => panic!("expected assert statement, got {other:?}"),
        }

        match &program.functions[0].body[1] {
            Stmt::Return {
                value: Some(Expr::Bool(false)),
                ..
            } => {}
            other => panic!("expected false return, got {other:?}"),
        }
    }

    #[test]
    fn parses_char_literals_and_postfix_updates() {
        let source = "pub def main() void\n\tvar ch u8 = 'a'\n\tcounter++\n\tremaining--\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::VarDecl {
                init: Expr::Char(b'a'),
                ..
            } => {}
            other => panic!("expected char literal declaration, got {other:?}"),
        }
        assert!(matches!(
            program.functions[0].body[1],
            Stmt::Increment { .. }
        ));
        assert!(matches!(
            program.functions[0].body[2],
            Stmt::Decrement { .. }
        ));
    }

    #[test]
    fn parses_infer_type_argument() {
        let source = "pub def main() void\n\thelper[_](value)\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Expr {
                expr: Expr::Call { callee, .. },
                ..
            } => match callee.as_ref() {
                Expr::Specialize { type_args, .. } => {
                    assert!(matches!(type_args.as_slice(), [Type::Infer]));
                }
                other => panic!("expected specialized call, got {other:?}"),
            },
            other => panic!("expected expression statement, got {other:?}"),
        }
    }

    #[test]
    fn parses_break_statement() {
        let source = "pub def main() void\n\tfor\n\t\tbreak\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Loop { body, .. } => {
                assert!(matches!(body[0], Stmt::Break { .. }));
            }
            other => panic!("expected loop, got {other:?}"),
        }
    }

    #[test]
    fn parses_multi_pattern_match_arms() {
        let source = "pub def classify(op i32) i32\n\tmatch op\n\t\t1 | 2 | 3 =>\n\t\t\treturn 1\n\t\t4 | 5 =>\n\t\t\treturn 2\n\t\t_ =>\n\t\t\treturn 0\n\tend\nend\n";
        let program = parse_program(lex(source).unwrap()).unwrap();

        match &program.functions[0].body[0] {
            Stmt::Match { arms, .. } => {
                assert_eq!(arms.len(), 6);
                assert!(matches!(&arms[0].kind, crate::ast::MatchArmKind::Variant(v) if v == "1"));
                assert!(matches!(&arms[1].kind, crate::ast::MatchArmKind::Variant(v) if v == "2"));
                assert!(matches!(&arms[2].kind, crate::ast::MatchArmKind::Variant(v) if v == "3"));
                assert!(matches!(&arms[3].kind, crate::ast::MatchArmKind::Variant(v) if v == "4"));
                assert!(matches!(&arms[4].kind, crate::ast::MatchArmKind::Variant(v) if v == "5"));
                assert!(matches!(&arms[5].kind, crate::ast::MatchArmKind::Variant(v) if v == "_"));
            }
            other => panic!("expected match statement, got {other:?}"),
        }
    }
}
