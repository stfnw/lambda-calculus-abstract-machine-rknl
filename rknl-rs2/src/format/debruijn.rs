// SPDX-FileCopyrightText: 2025 stfnw
// SPDX-License-Identifier: MIT

//! This module implements encoding/decoding routines for lambda terms in
//! nameless notation using De-Bruijn indices for representing variables.

use std::rc::Rc;

/// Untyped lambda calculus terms with variables as De-Bruijn indices
/// (nameless representation).
#[derive(Debug)]
pub enum TermDB {
    Var { debruijn: usize },
    Abs { t: Rc<TermDB> },
    App { t1: Rc<TermDB>, t2: Rc<TermDB> },
}

/// Convert BLC string into lambda term/expression AST.
pub fn decode_blc(blc: &str) -> TermDB {
    let tokens = lex(blc);
    parse(&tokens)
}

/// Encode a lambda term into John Tromp's Binary Lambda Calculus notation. See
/// https://tromp.github.io/cl/Binary_lambda_calculus.html#lambda_encoding. Note
/// that this is very limited and not a full evaluator of BLC like the
/// implementation from John Tromp available e.g. at
/// https://github.com/tromp/AIT/blob/master/uni.c: E.g. it does not implement
/// the input data decoding / output encoding of lambda terms as list of bits /
/// bit-strings. This pre-order AST traversal is implemented iteratively in
/// order to not run into stack limits for large terms.
pub fn encode_blc(term: &TermDB) -> String {
    let mut res = Vec::new();

    let mut stack = Vec::new();
    stack.push(term);

    while let Some(node) = stack.pop() {
        match node {
            TermDB::Var { debruijn } => {
                res.push(format!("{}0", "1".repeat(*debruijn + 1)));
            }
            TermDB::Abs { t } => {
                res.push("00".to_string());
                stack.push(t);
            }
            TermDB::App { t1, t2 } => {
                res.push("01".to_string());
                stack.push(t2);
                stack.push(t1);
            }
        }
    }

    res.join("")
}

/// Encode a lambda term into a notation adapted from the Bruijn Language
/// https://github.com/marvinborner/bruijn https://bruijn.marvinborner.de/
/// Lambda scope with `[]`, applications with `()`, variables as 0-based
/// De-Bruijn indices.
pub fn encode_bruijn(term: &TermDB) -> String {
    enum Instr<'a> {
        T(&'a TermDB),
        Print(String),
    }

    let mut stack: Vec<Instr> = Vec::new();
    stack.push(Instr::T(term));

    let mut res: Vec<String> = Vec::new();

    while let Some(term) = stack.pop() {
        match term {
            Instr::T(TermDB::Var { debruijn }) => stack.push(Instr::Print(format!("{}", debruijn))),
            Instr::T(TermDB::Abs { t }) => {
                res.push("[".to_string());
                stack.push(Instr::Print("]".to_string()));
                stack.push(Instr::T(t));
            }
            Instr::T(TermDB::App { t1, t2 }) => {
                res.push("(".to_string());
                stack.push(Instr::Print(")".to_string()));
                stack.push(Instr::T(t2));
                stack.push(Instr::Print(" ".to_string()));
                stack.push(Instr::T(t1));
            }
            Instr::Print(s) => res.push(s),
        }
    }

    res.join("")
}

#[derive(Debug, PartialEq)]
enum Token {
    Var { debruijn: usize }, // variable
    Abs,                     // abstraction
    App,                     // application
}

/// Tokenize a string in binary lambda calculus encoding.
fn lex(blc: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = blc.chars();

    while let Some(c) = chars.next() {
        match c {
            '0' => match chars.next().unwrap() {
                '0' => tokens.push(Token::Abs),
                '1' => tokens.push(Token::App),
                cc => panic!("Unexpected character {} (expected 0 or 1)", cc),
            },
            '1' => {
                let mut debruijn = 0;
                loop {
                    match chars.next().unwrap() {
                        '0' => break,
                        '1' => debruijn += 1,
                        cc => panic!("Unexpected character {} (exptected 0 or 1)", cc),
                    }
                }
                tokens.push(Token::Var { debruijn });
            }
            cc => panic!("Unexpected character {} (exptected 0 or 1)", cc),
        }
    }

    tokens
}

/// Parse a list of tokens into a lambda expression. This is done iteratively
/// in order to not run into stack limits for large terms. Also makes sure that
/// the term is closed / all variables are bound.
fn parse(tokens: &[Token]) -> TermDB {
    let mut stack: Vec<TermDB> = Vec::new();

    for token in tokens.iter().rev() {
        match token {
            Token::Var { debruijn } => stack.push(TermDB::Var {
                debruijn: *debruijn,
            }),
            Token::Abs => {
                let t = Rc::new(stack.pop().unwrap());
                stack.push(TermDB::Abs { t });
            }
            Token::App => {
                let t1 = Rc::new(stack.pop().unwrap());
                let t2 = Rc::new(stack.pop().unwrap());
                stack.push(TermDB::App { t1, t2 });
            }
        }
    }

    if stack.len() != 1 {
        panic!(
            "Stack contains not exactly one element after parsing! {:?}",
            stack
        );
    }

    let term = stack.pop().unwrap();

    verify_closed(&term);

    term
}

/// Make sure that the provided term is closed.
fn verify_closed(term: &TermDB) {
    let mut stack: Vec<(usize, &TermDB)> = Vec::new();
    stack.push((0, term));

    while let Some((depth, node)) = stack.pop() {
        match node {
            TermDB::Var { debruijn } => {
                if depth <= *debruijn {
                    panic!("Provided term {} is not closed", encode_bruijn(term));
                }
            }
            TermDB::Abs { t } => stack.push((depth + 1, t)),
            TermDB::App { t1, t2 } => {
                stack.push((depth, t2));
                stack.push((depth, t1));
            }
        }
    }
}
