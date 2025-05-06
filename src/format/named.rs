/// This module implements encoding/decoding routines for lambda terms in
/// typical text notation with named variables.
use crate::Term;

use std::rc::Rc;

/// Parse a lambda expression AST from a string in text notation (using
/// backslashes for lambda and requiring strict paranthesis accross each
/// abstraction and application).
pub fn decode(named: &str) -> Term {
    let tokens = Lexer::new(named).lex();
    Parser::new(tokens).parse()
}

/// Convert a lambda term to its string representation with named variables.
pub fn encode(term: &Term) -> String {
    encode_(term, 0)
}

fn encode_(term: &Term, curdepth: usize) -> String {
    match term {
        Term::Var { name } => name.clone(),
        Term::Abs { name, body } => format!("(λ{}. {})", name, encode_(body, curdepth + 1)),
        Term::App { func, arg } => {
            format!("({} {})", encode_(func, curdepth), encode_(arg, curdepth),)
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Var(String),
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

    /// Tokenize a string in binary lambda calculus encoding.
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
                    tokens.push(Token::Var(varname.into_iter().collect()));
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

    // This parser only handles lambda terms with all parenthesis explicitly and
    // unambiguously specified.
    //
    // term   = var | abs | app
    // abs    = '(' lambda '.' term ')'
    // app    = '(' term term ')'
    // lambda = '\' | 'λ'
    // var    = [a-zA-Z]*
    pub fn parse(&mut self) -> Term {
        let ast_named = self.parse_term();
        self.expect(None);
        ast_named
    }

    fn parse_term(&mut self) -> Term {
        match self.current_token() {
            Some(Token::Var(s)) => self.parse_var(s.clone()),
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

        let name = match self.current_token() {
            Some(Token::Var(ref var)) => var.clone(),
            _ => panic!(
                "Unexpected token: {:?} (expected Variable)",
                self.current_token()
            ),
        };
        self.advance();

        self.expect(Some(Token::Dot));

        let body = Rc::new(self.parse_term());

        Term::Abs { name, body }
    }

    fn parse_app(&mut self) -> Term {
        let func = Rc::new(self.parse_term());
        let arg = Rc::new(self.parse_term());
        Term::App { func, arg }
    }

    fn parse_var(&mut self, name: String) -> Term {
        self.advance();
        Term::Var { name }
    }
}
