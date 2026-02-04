// SPDX-FileCopyrightText: 2025 stfnw
// SPDX-License-Identifier: MIT

//! This module implements encoding/decoding routines for lambda terms in
//! typical text notation with named variables.

use std::rc::Rc;

/// Identifiers: used to represent variable names. Note that these are not
/// De-Bruijn indices, but simply integer names given to variables (the usual
/// scoping rules for named variables apply).
/// I think (but I'm not sure) that because of the way the abstract machine
/// works (lazily caching of evaluated terms identified by their variable name
/// in the current scope, support for open terms), De-Bruijn indices (that refer
/// to different variables depending on the nesting lambda depth) are not a
/// suitable representation here.
/// TODO test that out
/// Use a newtype and not a type alias for proper separation of types / to
/// prevent confusion.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub usize);

/// Untyped lambda calculus terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variable.
    Var { name: Identifier },
    /// Abstraction.
    Abs { var: Identifier, t: Rc<Term> },
    /// Application
    App { t1: Rc<Term>, t2: Rc<Term> },
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", encode(self))
    }
}

/// Parse a lambda expression AST from a string in text notation
/// This parser only handles lambda terms with all parenthesis explicitly and
/// unambiguously specified. The EBNF grammar is roughly (ignoring whitespace):
///
/// <term>   := <var> | <abs> | <app>
/// <var>    := [a-zA-Z] | "_" [0-9]+
/// <abs>    := "(" <lambda> <var> "." <term> ")"
/// <app>    := "(" <term> <term> ")"
/// <lambda> := "\" | "λ"
pub fn decode(named: &str) -> Term {
    let tokens = Lexer::new(named).lex();
    Parser::new(tokens).parse()
}

/// Print a lambda term to its string representation with named variables.
/// (Pre-order tree-traversal, explicitly iterative to prevent stack overflow
/// for large terms).
pub fn encode(term: &Term) -> String {
    enum Instr<'a> {
        T(&'a Term),
        Print(String),
    }
    let mut stack: Vec<Instr> = Vec::new();
    let mut result: Vec<String> = Vec::new();

    stack.push(Instr::T(term));

    while let Some(instr) = stack.pop() {
        match instr {
            Instr::Print(s) => result.push(s),
            Instr::T(Term::Var { name }) => {
                result.push(encode_identifier(name));
            }
            Instr::T(Term::Abs { var, t }) => {
                result.push(format!("(λ{}. ", encode_identifier(var)));
                stack.push(Instr::Print(")".to_string()));
                stack.push(Instr::T(t));
            }
            Instr::T(Term::App { t1, t2 }) => {
                stack.push(Instr::Print(")".to_string()));
                stack.push(Instr::T(t2));
                stack.push(Instr::Print(" ".to_string()));
                stack.push(Instr::T(t1));
                stack.push(Instr::Print("(".to_string()));
            }
        }
    }

    result.join("")
}

fn encode_identifier(id: &Identifier) -> String {
    let v = id.0;
    if (('a' as usize) <= v && v <= ('z' as usize)) || (('A' as usize) <= v && v <= ('Z' as usize))
    {
        format!("{}", (v as u8) as char)
    } else {
        format!("_{}", v)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Var(usize),
    Lambda,
    LParen,
    RParen,
    Dot,
}

struct Lexer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn current_char(&self) -> Option<char> {
        self.input.chars().nth(self.pos)
    }

    fn lex(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();

        let mut advance = true;

        loop {
            let c = self.current_char();
            match c {
                Some(' ') | Some('\t') | Some('\n') | Some('\r') => (),
                Some('(') => tokens.push(Token::LParen),
                Some(')') => tokens.push(Token::RParen),
                Some('\\') | Some('λ') => tokens.push(Token::Lambda),
                Some('.') => tokens.push(Token::Dot),
                Some('a'..='z') => tokens.push(Token::Var(c.unwrap() as usize)),
                Some('_') => {
                    self.advance();
                    let mut name = 0;
                    while let Some(c) = self.current_char() {
                        if c.is_ascii_digit() {
                            name *= 10;
                            name += (c as usize) - ('0' as usize);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    tokens.push(Token::Var(name));
                    advance = false;
                }
                None => break,
                _ => panic!("Unexpected character: {}", self.current_char().unwrap()),
            }

            if advance {
                self.advance();
            }
            advance = true;
        }

        tokens
    }
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }

    fn expect(&mut self, token: Option<Token>) {
        if self.current_token() == token {
            self.advance();
        } else {
            panic!(
                "Unexpected token: current token {:?} (expected {:?})",
                self.current_token(),
                token,
            );
        }
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn current_token(&self) -> Option<Token> {
        self.tokens.get(self.pos).cloned()
    }

    pub fn parse(&mut self) -> Term {
        let ast_named = self.parse_term();
        self.expect(None);
        ast_named
    }

    fn parse_term(&mut self) -> Term {
        match self.current_token() {
            Some(Token::Var(s)) => self.parse_var(s),
            Some(Token::LParen) => self.parse_abs_or_app(),
            t => panic!("Unexpected token: {:?} (expected Variable or LParen)", t),
        }
    }

    fn parse_abs_or_app(&mut self) -> Term {
        self.expect(Some(Token::LParen));
        let res = match self.current_token() {
            Some(Token::Lambda) => self.parse_abs(),
            _ => self.parse_app(),
        };
        self.expect(Some(Token::RParen));
        res
    }

    fn parse_abs(&mut self) -> Term {
        self.expect(Some(Token::Lambda));

        let var = Identifier(match self.current_token() {
            Some(Token::Var(var)) => var,
            _ => panic!(
                "Unexpected token: {:?} (expected Variable)",
                self.current_token()
            ),
        });
        self.advance();

        self.expect(Some(Token::Dot));

        let t = Rc::new(self.parse_term());

        Term::Abs { var, t }
    }

    fn parse_app(&mut self) -> Term {
        let t1 = Rc::new(self.parse_term());
        let t2 = Rc::new(self.parse_term());
        Term::App { t1, t2 }
    }

    fn parse_var(&mut self, name: usize) -> Term {
        self.advance();
        Term::Var {
            name: Identifier(name),
        }
    }
}
