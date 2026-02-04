// SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
// SPDX-License-Identifier: CC-BY-4.0
//
// SPDX-FileCopyrightText: 2025 This specific implementation: Stefan Walter
// SPDX-License-Identifier: MIT

//! This module implements encoding/decoding routines for lambda terms in
//! typical text notation with named variables.

use crate::eval::Identifier;
use crate::eval::Term;

use std::rc::Rc;

/// Parse a lambda expression AST from a string in text notation
/// This parser only handles lambda terms with all parenthesis explicitly and
/// unambiguously specified. The EBNF grammar is roughly (ignoring whitespace):
///
/// <term>   := <var> | <abs> | <app>
/// <var>    := [a-z][a-zA-Z0-9]*
/// <abs>    := "(" <lambda> "." <term> ")"
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
        Term(&'a Term),
        Print(String),
    }
    let mut stack: Vec<Instr> = Vec::new();
    let mut result: Vec<String> = Vec::new();

    stack.push(Instr::Term(term));

    while let Some(instr) = stack.pop() {
        match instr {
            Instr::Print(s) => result.push(s),
            Instr::Term(Term::Var { name }) => {
                result.push(encode_identifier(name));
            }
            Instr::Term(Term::Abs { var, t }) => {
                result.push(format!("(λ{}. ", encode_identifier(var)));
                stack.push(Instr::Print(")".to_string()));
                stack.push(Instr::Term(t));
            }
            Instr::Term(Term::App { t1, t2 }) => {
                stack.push(Instr::Print(")".to_string()));
                stack.push(Instr::Term(t2));
                stack.push(Instr::Print(" ".to_string()));
                stack.push(Instr::Term(t1));
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
        format!("v{}", v)
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
            match self.current_char() {
                Some(' ') | Some('\t') | Some('\n') | Some('\r') => (),
                Some('(') => tokens.push(Token::LParen),
                Some(')') => tokens.push(Token::RParen),
                Some('\\') | Some('λ') => tokens.push(Token::Lambda),
                Some('.') => tokens.push(Token::Dot),
                Some('a'..='z') => {
                    let mut varname = vec![self.current_char().unwrap()];
                    self.advance();
                    while let Some(c) = self.current_char() {
                        if c.is_alphanumeric() {
                            varname.push(c);
                            self.advance();
                        } else {
                            break;
                        }
                    }

                    let varname: String = varname.into_iter().collect();
                    // TODO
                    if varname.len() != 1 {
                        todo!();
                    }
                    let varname = varname.chars().nth(0).unwrap() as usize;
                    tokens.push(Token::Var(varname));
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
            Some(Token::Var(ref var)) => var.clone(),
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
