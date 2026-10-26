use crate::CompileError;

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Pub,
    Def,
    Extern,
    Test,
    Match,
    Interface,
    Type,
    Typeset,
    Union,
    Enum,
    End,
    Var,
    Val,
    Return,
    Defer,
    If,
    Guard,
    Else,
    Elif,
    Break,
    Continue,
    Parallel,
    For,
    When,
    Link,
    In,
    As,
    Mut,
    Ref,
    Fn,
    List,
    Void,
    Bool,
    I8,
    I16,
    I32,
    I64,
    Isize,
    U16,
    U32,
    U64,
    Usize,
    U8,
    F32,
    F64,
    Ident(String),
    Int(u64),
    Char(u8),
    Float(f64),
    Str(String),
    Newline,
    At,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    ColonColon,
    Dot,
    DotDot,
    Assign,
    EqualEqual,
    BangEqual,
    Amp,
    AmpAmp,
    AmpEqual,
    Pipe,
    PipePipe,
    PipeEqual,
    Caret,
    CaretEqual,
    Bang,
    Tilde,
    Less,
    LessEqual,
    ShiftLeft,
    Greater,
    GreaterEqual,
    ShiftRight,
    Star,
    StarEqual,
    Slash,
    SlashEqual,
    Percent,
    Minus,
    MinusMinus,
    MinusEqual,
    Plus,
    PlusPlus,
    PlusEqual,
    FatArrow,
    Question,
    Eof,
}

pub fn lex(source: &str) -> Result<Vec<Token>, CompileError> {
    Lexer::new(source).lex()
}

struct Lexer {
    chars: Vec<char>,
    pos: usize,
    line: usize,
    column: usize,
}

impl Lexer {
    fn new(source: &str) -> Self {
        Self {
            chars: source.chars().collect(),
            pos: 0,
            line: 1,
            column: 1,
        }
    }

    fn lex(mut self) -> Result<Vec<Token>, CompileError> {
        let mut tokens = Vec::new();

        while let Some(ch) = self.peek() {
            match ch {
                ' ' | '\t' | '\r' => {
                    self.bump();
                }
                '\n' => {
                    let (line, column) = (self.line, self.column);
                    self.bump();
                    tokens.push(Token {
                        kind: TokenKind::Newline,
                        line,
                        column,
                    });
                }
                '#' => {
                    self.bump();
                    while let Some(current) = self.peek() {
                        if current == '\n' {
                            break;
                        }
                        self.bump();
                    }
                }
                '\\' => {
                    self.bump();
                    if self.peek() == Some('\\') {
                        self.bump();
                        let mut value = String::new();
                        let start_line = self.line;
                        let start_column = self.column;
                        loop {
                            let Some(ch) = self.peek() else {
                                return Err(self.error("unterminated multiline string"));
                            };
                            if ch == '\n' {
                                self.bump();
                                while let Some(ws) = self.peek() {
                                    if ws == ' ' || ws == '\t' {
                                        self.bump();
                                    } else {
                                        break;
                                    }
                                }
                                let next = self.peek();
                                let next2 = self.peek_next();
                                if next == Some('\\') && next2 == Some('\\') {
                                    self.bump();
                                    self.bump();
                                    value.push('\n');
                                    continue;
                                } else {
                                    break;
                                }
                            } else if ch == '\\' {
                                self.bump();
                                if let Some(next_ch) = self.peek() {
                                    match next_ch {
                                        'n' => {
                                            self.bump();
                                            value.push('\n');
                                        }
                                        't' => {
                                            self.bump();
                                            value.push('\t');
                                        }
                                        'r' => {
                                            self.bump();
                                            value.push('\r');
                                        }
                                        '"' => {
                                            self.bump();
                                            value.push('\"');
                                        }
                                        '\\' => {
                                            self.bump();
                                            value.push('\\');
                                        }
                                        _ => {
                                            value.push('\\');
                                        }
                                    }
                                } else {
                                    value.push('\\');
                                }
                            } else {
                                self.bump();
                                value.push(ch);
                            }
                        }
                        tokens.push(Token {
                            kind: TokenKind::Str(value),
                            line: start_line,
                            column: start_column,
                        });
                    }
                }
                '@' => tokens.push(self.single(TokenKind::At)),
                '(' => tokens.push(self.single(TokenKind::LParen)),
                ')' => tokens.push(self.single(TokenKind::RParen)),
                '[' => tokens.push(self.single(TokenKind::LBracket)),
                ']' => tokens.push(self.single(TokenKind::RBracket)),
                '{' => tokens.push(self.single(TokenKind::LBrace)),
                '}' => tokens.push(self.single(TokenKind::RBrace)),
                ',' => tokens.push(self.single(TokenKind::Comma)),
                ':' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some(':') {
                        self.bump();
                        TokenKind::ColonColon
                    } else {
                        TokenKind::Colon
                    };
                    tokens.push(Token { kind, line, column });
                }
                '.' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('.') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::DotDot,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Dot,
                            line,
                            column,
                        });
                    }
                }
                '=' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::EqualEqual,
                            line,
                            column,
                        });
                    } else if self.peek() == Some('>') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::FatArrow,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Assign,
                            line,
                            column,
                        });
                    }
                }
                '&' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some('&') {
                        self.bump();
                        TokenKind::AmpAmp
                    } else if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::AmpEqual
                    } else {
                        TokenKind::Amp
                    };
                    tokens.push(Token { kind, line, column });
                }
                '|' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some('|') {
                        self.bump();
                        TokenKind::PipePipe
                    } else if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::PipeEqual
                    } else {
                        TokenKind::Pipe
                    };
                    tokens.push(Token { kind, line, column });
                }
                '^' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::CaretEqual
                    } else {
                        TokenKind::Caret
                    };
                    tokens.push(Token { kind, line, column });
                }
                '!' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::BangEqual
                    } else {
                        TokenKind::Bang
                    };
                    tokens.push(Token { kind, line, column });
                }
                '~' => tokens.push(self.single(TokenKind::Tilde)),
                '<' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    let kind = if self.peek() == Some('<') {
                        self.bump();
                        TokenKind::ShiftLeft
                    } else if self.peek() == Some('=') {
                        self.bump();
                        TokenKind::LessEqual
                    } else {
                        TokenKind::Less
                    };
                    tokens.push(Token { kind, line, column });
                }
                '>' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::GreaterEqual,
                            line,
                            column,
                        });
                    } else if self.peek() == Some('>') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::ShiftRight,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Greater,
                            line,
                            column,
                        });
                    }
                }
                '*' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::StarEqual,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Star,
                            line,
                            column,
                        });
                    }
                }
                '/' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::SlashEqual,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Slash,
                            line,
                            column,
                        });
                    }
                }
                '%' => tokens.push(self.single(TokenKind::Percent)),
                '-' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('-') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::MinusMinus,
                            line,
                            column,
                        });
                    } else if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::MinusEqual,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Minus,
                            line,
                            column,
                        });
                    }
                }
                '+' => {
                    let line = self.line;
                    let column = self.column;
                    self.bump();
                    if self.peek() == Some('+') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::PlusPlus,
                            line,
                            column,
                        });
                    } else if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(Token {
                            kind: TokenKind::PlusEqual,
                            line,
                            column,
                        });
                    } else {
                        tokens.push(Token {
                            kind: TokenKind::Plus,
                            line,
                            column,
                        });
                    }
                }
                '?' => tokens.push(self.single(TokenKind::Question)),
                '"' => tokens.push(self.string()?),
                '\'' => tokens.push(self.char_literal()?),
                '0'..='9' => tokens.push(self.number()?),
                _ if is_ident_start(ch) => tokens.push(self.ident_or_keyword()),
                _ => {
                    return Err(self.error(format!("unexpected character `{ch}`")));
                }
            }
        }

        tokens.push(Token {
            kind: TokenKind::Eof,
            line: self.line,
            column: self.column,
        });
        Ok(tokens)
    }

    fn single(&mut self, kind: TokenKind) -> Token {
        let token = Token {
            kind,
            line: self.line,
            column: self.column,
        };
        self.bump();
        token
    }

    fn string(&mut self) -> Result<Token, CompileError> {
        let line = self.line;
        let column = self.column;
        self.bump();

        let mut value = String::new();
        loop {
            let Some(ch) = self.peek() else {
                return Err(self.error("unterminated string literal"));
            };
            match ch {
                '"' => {
                    self.bump();
                    break;
                }
                '\\' => {
                    self.bump();
                    value.push(self.escaped_char()?);
                }
                '\n' => return Err(self.error("newline in string literal")),
                other => {
                    self.bump();
                    value.push(other);
                }
            }
        }

        Ok(Token {
            kind: TokenKind::Str(value),
            line,
            column,
        })
    }

    fn char_literal(&mut self) -> Result<Token, CompileError> {
        let line = self.line;
        let column = self.column;
        self.bump();

        let Some(ch) = self.peek() else {
            return Err(self.error("unterminated character literal"));
        };
        if ch == '\'' {
            return Err(self.error("empty character literal"));
        }
        if ch == '\n' {
            return Err(self.error("newline in character literal"));
        }

        let value = if ch == '\\' {
            self.bump();
            self.escaped_char()?
        } else {
            self.bump();
            ch
        };

        if self.peek() != Some('\'') {
            return Err(self.error("character literal must contain exactly one character"));
        }
        self.bump();

        let byte = u8::try_from(value as u32)
            .map_err(|_| self.error("character literal must fit in u8"))?;
        Ok(Token {
            kind: TokenKind::Char(byte),
            line,
            column,
        })
    }

    fn escaped_char(&mut self) -> Result<char, CompileError> {
        let Some(escaped) = self.peek() else {
            return Err(self.error("unterminated escape sequence"));
        };
        let decoded = match escaped {
            'n' => {
                self.bump();
                '\n'
            }
            't' => {
                self.bump();
                '\t'
            }
            'r' => {
                self.bump();
                '\r'
            }
            'f' => {
                self.bump();
                '\x0c'
            }
            'b' => {
                self.bump();
                '\x08'
            }
            '"' => {
                self.bump();
                '"'
            }
            '\'' => {
                self.bump();
                '\''
            }
            '\\' => {
                self.bump();
                '\\'
            }
            'x' => {
                self.bump();
                let Some(high) = self.peek() else {
                    return Err(self.error("unterminated hex escape sequence"));
                };
                self.bump();
                let Some(low) = self.peek() else {
                    return Err(self.error("unterminated hex escape sequence"));
                };
                let value = hex_value(high)
                    .zip(hex_value(low))
                    .map(|(high, low)| (high << 4) | low)
                    .ok_or_else(|| self.error("invalid hex escape sequence"))?;
                self.bump();
                value as char
            }
            other => {
                return Err(self.error(format!("unsupported escape sequence `\\{other}`")));
            }
        };
        Ok(decoded)
    }

    fn number(&mut self) -> Result<Token, CompileError> {
        let line = self.line;
        let column = self.column;
        let start = self.pos;

        if self.peek() == Some('0') && matches!(self.peek_next(), Some('x' | 'X')) {
            self.bump();
            self.bump();
            let hex_start = self.pos;
            while matches!(self.peek(), Some('0'..='9' | 'a'..='f' | 'A'..='F' | '_')) {
                self.bump();
            }
            let digits: String = self.chars[hex_start..self.pos]
                .iter()
                .filter(|&&c| c != '_')
                .collect();
            if digits.is_empty() {
                return Err(self.error("hex literal has no digits"));
            }
            let value = u64::from_str_radix(&digits, 16).map_err(|error| {
                CompileError::new(format!("invalid hex literal at {line}:{column}: {error}"))
            })?;
            return Ok(Token {
                kind: TokenKind::Int(value),
                line,
                column,
            });
        }

        if self.peek() == Some('0') && matches!(self.peek_next(), Some('b' | 'B')) {
            self.bump();
            self.bump();
            let bin_start = self.pos;
            while matches!(self.peek(), Some('0' | '1' | '_')) {
                self.bump();
            }
            let digits: String = self.chars[bin_start..self.pos]
                .iter()
                .filter(|&&c| c != '_')
                .collect();
            if digits.is_empty() {
                return Err(self.error("binary literal has no digits"));
            }
            let value = u64::from_str_radix(&digits, 2).map_err(|error| {
                CompileError::new(format!(
                    "invalid binary literal at {line}:{column}: {error}"
                ))
            })?;
            return Ok(Token {
                kind: TokenKind::Int(value),
                line,
                column,
            });
        }

        while matches!(self.peek(), Some('0'..='9')) {
            self.bump();
        }
        let is_float = self.peek() == Some('.') && matches!(self.peek_next(), Some('0'..='9'));
        if is_float {
            self.bump();
            while matches!(self.peek(), Some('0'..='9')) {
                self.bump();
            }
        }
        if matches!(self.peek(), Some('e' | 'E'))
            && matches!(self.peek_next(), Some('0'..='9' | '+' | '-'))
        {
            self.bump();
            if matches!(self.peek(), Some('+' | '-')) {
                self.bump();
            }
            while matches!(self.peek(), Some('0'..='9')) {
                self.bump();
            }
        }
        let lexeme: String = self.chars[start..self.pos].iter().collect();
        if is_float {
            let value = lexeme.parse::<f64>().map_err(|error| {
                CompileError::new(format!(
                    "invalid float literal `{lexeme}` at {line}:{column}: {error}"
                ))
            })?;
            return Ok(Token {
                kind: TokenKind::Float(value),
                line,
                column,
            });
        }
        let value = lexeme.parse::<u64>().map_err(|error| {
            CompileError::new(format!(
                "invalid integer literal `{lexeme}` at {line}:{column}: {error}"
            ))
        })?;
        Ok(Token {
            kind: TokenKind::Int(value),
            line,
            column,
        })
    }

    fn ident_or_keyword(&mut self) -> Token {
        let line = self.line;
        let column = self.column;
        let start = self.pos;
        while matches!(self.peek(), Some(ch) if is_ident_continue(ch)) {
            self.bump();
        }
        let lexeme: String = self.chars[start..self.pos].iter().collect();
        let kind = match lexeme.as_str() {
            "pub" => TokenKind::Pub,
            "def" => TokenKind::Def,
            "extern" => TokenKind::Extern,
            "type" => TokenKind::Type,
            "typeset" => TokenKind::Typeset,
            "union" => TokenKind::Union,
            "enum" => TokenKind::Enum,
            "test" => TokenKind::Test,
            "match" => TokenKind::Match,
            "interface" => TokenKind::Interface,
            "end" => TokenKind::End,
            "var" => TokenKind::Var,
            "val" => TokenKind::Val,
            "return" => TokenKind::Return,
            "defer" => TokenKind::Defer,
            "if" => TokenKind::If,
            "guard" => TokenKind::Guard,
            "else" => TokenKind::Else,
            "elif" => TokenKind::Elif,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "parallel" => TokenKind::Parallel,
            "for" => TokenKind::For,
            "when" => TokenKind::When,
            "link" => TokenKind::Link,
            "in" => TokenKind::In,
            "as" => TokenKind::As,
            "mut" => TokenKind::Mut,
            "ref" => TokenKind::Ref,
            "fn" => TokenKind::Fn,
            "list" => TokenKind::List,
            "void" => TokenKind::Void,
            "bool" => TokenKind::Bool,
            "i8" => TokenKind::I8,
            "i16" => TokenKind::I16,
            "i32" => TokenKind::I32,
            "i64" => TokenKind::I64,
            "isize" => TokenKind::Isize,
            "u16" => TokenKind::U16,
            "u32" => TokenKind::U32,
            "u64" => TokenKind::U64,
            "usize" => TokenKind::Usize,
            "u8" => TokenKind::U8,
            "f32" => TokenKind::F32,
            "f64" => TokenKind::F64,
            _ => TokenKind::Ident(lexeme),
        };
        Token { kind, line, column }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_next(&self) -> Option<char> {
        self.chars.get(self.pos + 1).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += 1;
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn error(&self, message: impl Into<String>) -> CompileError {
        CompileError::new(format!(
            "{} at {}:{}",
            message.into(),
            self.line,
            self.column
        ))
    }
}

fn is_ident_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    is_ident_start(ch) || ch.is_ascii_digit()
}

fn hex_value(ch: char) -> Option<u8> {
    match ch {
        '0'..='9' => Some((ch as u8) - b'0'),
        'a'..='f' => Some((ch as u8) - b'a' + 10),
        'A'..='F' => Some((ch as u8) - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{TokenKind, lex};

    #[test]
    fn lexes_single_hash_comments() {
        let tokens = lex("# headline\nval value = 1 # trailing\n").unwrap();

        assert!(matches!(tokens[0].kind, TokenKind::Newline));
        assert!(matches!(tokens[1].kind, TokenKind::Val));
        assert!(matches!(tokens[2].kind, TokenKind::Ident(ref name) if name == "value"));
        assert!(matches!(tokens[3].kind, TokenKind::Assign));
        assert!(matches!(tokens[4].kind, TokenKind::Int(1)));
        assert!(matches!(tokens[5].kind, TokenKind::Newline));
    }

    #[test]
    fn still_accepts_double_hash_comments() {
        let tokens = lex("## docs\npub def main() void\nend\n").unwrap();

        assert!(matches!(tokens[0].kind, TokenKind::Newline));
        assert!(matches!(tokens[1].kind, TokenKind::Pub));
    }

    #[test]
    fn lexes_double_colon() {
        let tokens = lex("extern def sleep() void :: \"sleep\"\n").unwrap();

        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::ColonColon))
        );
    }

    #[test]
    fn lexes_char_literals_and_postfix_operators() {
        let tokens = lex("val a = 'a'\nvalue++\nother--\nval nl = '\\n'\n").unwrap();

        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::Char(b'a')))
        );
        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::Char(value) if value == b'\n'))
        );
        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::PlusPlus))
        );
        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::MinusMinus))
        );
    }

    #[test]
    fn lexes_break_keyword() {
        let tokens = lex("for\n\tbreak\nend\n").unwrap();

        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::Break))
        );
    }

    #[test]
    fn lexes_when_keyword() {
        let tokens = lex("when linux\nend\n").unwrap();

        assert!(
            tokens
                .iter()
                .any(|token| matches!(token.kind, TokenKind::When))
        );
    }
}
