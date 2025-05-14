// SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
// SPDX-License-Identifier: CC-BY-4.0
//
// SPDX-FileCopyrightText: 2025 This specific implementation: Stefan Walter
// SPDX-License-Identifier: MIT

//! This module implements the RKNL abstract machine for strong call by need
//! reduction of untyped lambda calculus terms, from the following paper:
//! M. Biernacka, W. Charatonik, and T. Drab, "A simple and efficient implementation of strong call by need by an abstract machine", Proc. ACM Program. Lang., vol. 6, no. ICFP, pp. 109–136, Aug. 2022, doi: 10.1145/3549822. (licensed CC-BY-4.0)
//! Especially Table 1 "The RKNL abstract machine, a reasonable and lazy variant of KN"
//! which lists the state transition rules.

use crate::format::named;

use std::collections::HashMap;
use std::rc::Rc;

// A note regarding garbage collection / reference counting:
//
// Terms and Envs are reference counted.
//
// For extension, Envs are fully cloned before modification; using a persistent
// data structure / hash table for Envs would be better to avoid this, but rusts
// standard library doesn't seem to have one.
//
// The other structures are either passed linearly and don't need cloning (like Stacks or Stores),
// or are made up mainly of Rc<Term> and Rc<Env>, for which cloning is cheap (e.g. Values).
// For Rc<T>, we use Rc::clone(T) explicitly, instead of calling it as `T.clone()`.
//
// This version does not automatically garbage collect cached references inside
// the Store map, which causes the Store to grow unnecessarily.
// This is addressed in the next iteration.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Identifiers: used to represent variable names.
// Use a newtype and not a type alias for proper separation of types / to
// prevent confusion.
pub struct Identifier(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
/// Untyped lambda calculus terms.
pub enum Term {
    /// Variable.
    Var { name: Identifier },
    /// Application
    App { t1: Rc<Term>, t2: Rc<Term> },
    /// Abstraction.
    Abs { var: Identifier, t: Rc<Term> },
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", named::encode(self))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
// Use a newtype and not a type alias for proper separation of types / to
// prevent confusion.
struct Location(usize);

#[derive(Debug)]
/// Environments.
struct Env(HashMap<Identifier, Location>);

#[derive(Debug)]
struct Closure((Rc<Term>, Rc<Env>));

#[derive(Debug, Clone)]
enum Value {
    Term(Rc<Term>),
    LocationAbs((Location, Identifier, Rc<Term>, Rc<Env>)),
}

#[derive(Debug)]
enum StorableValue {
    Todo_,
    Todo(Closure),
    Done(Value),
}

#[derive(Debug)]
struct Store(HashMap<Location, StorableValue>);

#[derive(Debug)]
enum Frame {
    F1(Closure),    // Box c
    F2(Rc<Term>),   // t Box
    F3(Identifier), // \x. Box
    F4(Location),   // l := Box
}

#[derive(Debug)]
enum Stack {
    Nil,
    Cons(Frame, Box<Stack>),
}

/// Configuration / state of the abstract machine.
#[derive(Debug)]
enum Conf {
    Down(Closure, Stack, Store),
    Up(Value, Stack, Store),
}

#[derive(Debug, PartialEq, Eq)]
pub struct EvalResult {
    /// Fully reduced lambda calculus term.
    pub reduced_term: Term,
    /// Number of steps taken by the abstract machine during term reduction.
    pub steps: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EvalResult_ {
    ReductionCompleted(EvalResult),
    StepLimitExceeded,
}

pub fn eval(term: Term) -> EvalResult {
    if let EvalResult_::ReductionCompleted(res) = eval_(term, None) {
        res
    } else {
        panic!("Can't happen");
    }
}

/// This is the main function of RKNL; it implementes Table 1
/// "The RKNL abstract machine, a reasonable and lazy variant of KN".
/// Besides the reduced term, the number of performed state transitions of the
/// abstract machine is also counted and returned.
/// It optionally takes a limit of steps that should not be exceeded; motivation
/// behind this is to allow attempts at reducing arbitrary potentially
/// non-halting lambda terms up to this limit, without actually getting stuck
/// in an infinite loop.
pub fn eval_(term: Term, max_steps: Option<usize>) -> EvalResult_ {
    // Closure for creating new unique locations by incrementing a counter.
    let mut cur_location: usize = 0;
    let mut fresh_location = move || {
        let res = Location(cur_location);
        cur_location += 1;
        res
    };

    // Closure for creating new unique identifiers (variable names) by
    // incrementing a counter (this assumes without checking that the given
    // lambda term does not already contain variables of the given form).
    // TODO verify this assumption for each input in order to avoid collisions.
    let mut cur_identifier: usize = 0;
    let mut fresh_identifier = move || {
        let res = Identifier(format!("v{}", cur_identifier));
        cur_identifier += 1;
        res
    };

    // Setup the initial state with provided term, empty environment,
    // empty stack, and empty store.
    let mut conf = Conf::Down(
        Closure((Rc::new(term), Rc::new(Env(HashMap::new())))),
        Stack::Nil,
        Store(HashMap::new()),
    );

    // Steps taken by the abstract machine during its execution / reduction of
    // the specified lambda calculus term. (That is, number of times a rule was
    // applied).
    let mut steps: usize = 0;

    loop {
        // Apply a state transition rule based on the current state/configuration.
        let newconf = match conf {
            // The pattern match is split up since we can't match inside the
            // `Rc<Term>` of the closure-`term` in one go.
            Conf::Down(Closure((term, e)), s, mut sigma) => match term.as_ref() {
                // Rule (1).
                Term::App { t1, t2 } => Conf::Down(
                    Closure((Rc::clone(t1), Rc::clone(&e))),
                    Stack::Cons(
                        Frame::F1(Closure((Rc::clone(t2), Rc::clone(&e)))),
                        Box::new(s),
                    ),
                    sigma,
                ),

                // Rule (2).
                Term::Abs { var: x, t } => {
                    let l = fresh_location();
                    sigma.0.insert(l.clone(), StorableValue::Todo_);
                    Conf::Up(
                        Value::LocationAbs((l, x.clone(), Rc::clone(t), e)),
                        s,
                        sigma,
                    )
                }

                Term::Var { name: x } => match e.0.get(x) {
                    Some(l) => match sigma.0.get(l).unwrap() {
                        // Rule (3).
                        StorableValue::Todo(Closure((t, e2))) => Conf::Down(
                            Closure((Rc::clone(t), Rc::clone(e2))),
                            Stack::Cons(Frame::F4(l.clone()), Box::new(s)),
                            sigma,
                        ),

                        // Rule (4).
                        StorableValue::Done(v) => Conf::Up(v.clone(), s, sigma),
                        StorableValue::Todo_ => panic!("Can't happen"),
                    },

                    // Rule (4).
                    None => {
                        // No entry in environment for current variable
                        // => variable is unbound => return as-is withoug modification.
                        Conf::Up(
                            Value::Term(Rc::new(Term::Var { name: x.clone() })),
                            s,
                            sigma,
                        )
                    }
                },
            },

            // Rule (5).
            Conf::Up(v, Stack::Cons(Frame::F4(l), s), mut sigma) => {
                sigma.0.insert(l, StorableValue::Done(v.clone()));
                Conf::Up(v, *s, sigma)
            }

            // Rule (6).
            Conf::Up(
                Value::LocationAbs((_l, x, t, e)),
                Stack::Cons(Frame::F1(Closure((t2, e2))), s),
                mut sigma,
            ) => {
                let l2 = fresh_location();
                // Note that we fully clone the environment before extension
                // (see note above on reference counting).
                let mut e_: Env = Env(e.0.clone());
                e_.0.insert(x, l2.clone());
                sigma.0.insert(l2, StorableValue::Todo(Closure((t2, e2))));
                Conf::Down(Closure((t, Rc::new(e_))), *s, sigma)
            }

            Conf::Up(Value::LocationAbs((l, x, t, e)), s, mut sigma) => {
                match sigma.0.get(&l).unwrap() {
                    // Rule (7).
                    StorableValue::Todo_ => {
                        let l2 = fresh_location();
                        let x_ = fresh_identifier();

                        // Note that we fully clone the environment before extension
                        // (see note above on reference counting).
                        let mut e_: Env = Env(e.0.clone());
                        e_.0.insert(x, l2.clone());

                        sigma.0.insert(
                            l2,
                            StorableValue::Done(Value::Term(Rc::new(Term::Var {
                                name: x_.clone(),
                            }))),
                        );

                        Conf::Down(
                            Closure((t, Rc::new(e_))),
                            Stack::Cons(
                                Frame::F3(x_),
                                Box::new(Stack::Cons(Frame::F4(l), Box::new(s))),
                            ),
                            sigma,
                        )
                    }

                    // Rule (8).
                    StorableValue::Done(v) => Conf::Up(v.clone(), s, sigma),

                    StorableValue::Todo(c) => {
                        panic!("Encountered unexpected closure {:?} in configuration", c)
                    }
                }
            }

            // Rule (9).
            Conf::Up(Value::Term(t), Stack::Cons(Frame::F1(Closure((t2, e2))), s), sigma) => {
                Conf::Down(Closure((t2, e2)), Stack::Cons(Frame::F2(t), s), sigma)
            }

            // Rule (10).
            Conf::Up(Value::Term(t2), Stack::Cons(Frame::F2(t1), s), sigma) => {
                Conf::Up(Value::Term(Rc::new(Term::App { t1, t2 })), *s, sigma)
            }

            // Rule (11).
            Conf::Up(Value::Term(t), Stack::Cons(Frame::F3(x), s), sigma) => {
                Conf::Up(Value::Term(Rc::new(Term::Abs { var: x, t })), *s, sigma)
            }

            // Return fully reduced term.
            Conf::Up(Value::Term(t), Stack::Nil, _sigma) => {
                let t_strong_count = Rc::strong_count(&t);
                return EvalResult_::ReductionCompleted(EvalResult {
                    reduced_term: Rc::try_unwrap(t).expect(&format!(
                        "Strong reference cound for term is {} != 1, can't unwrap",
                        t_strong_count
                    )),
                    steps,
                });
            }
        };

        // Update/advance machine state.
        conf = newconf;

        // Increment steps counter.
        steps += 1;

        // Stop if step-limit is reached.
        if let Some(max_steps_) = max_steps {
            if steps >= max_steps_ {
                return EvalResult_::StepLimitExceeded;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct EvalTestCase<'a> {
        comment: &'a str,
        term: &'a str,
        reduced: &'a str,
    }

    /// Test correct beta reduction for the example term given in the paper in
    /// section 4.1 "Elaborate Example Execution":
    ///
    /// > This is one of the simplest examples that uses all transitions of the
    /// > machine and demonstrates its main features
    ///
    /// This test not only tests that the expression is reduced to the correct
    /// lambda term, but also that this happens expected in the expected number
    /// of steps listed in the execution trace in Table 2. "Elaborate example
    /// execution in refocusing notation".
    #[test]
    fn test_eval_paper_example() {
        let test = EvalTestCase {
            comment: "Example term given in the paper in section 4.1",
            term: r"((\x. ((c x) x)) ((\y. (\z. ((\x. x) z))) ((\x. (x x)) (\x. (x x)))))",
            reduced: "((c (λv0. v0)) (λv0. v0))",
        };
        let test_steps = 27;

        println!("comment {}", test.comment);
        let ast = named::decode(test.term);
        println!("parsed  {}", ast);
        let res = eval(ast);
        println!(
            "reduced in {} steps to term {}",
            res.steps, res.reduced_term
        );

        assert_eq!(test.reduced, named::encode(&res.reduced_term));

        assert_eq!(test_steps, res.steps);
    }

    /// Test correct beta reduction of various hard-coded lambda terms.
    #[test]
    fn test_eval() {
        let cases = [
            EvalTestCase {
                comment: "I",
                term: "(λa. a)",
                reduced: "(λv0. v0)",
            },
            EvalTestCase {
                comment: "(ω I)",
                term: "((λa. (a a)) (λa. a))",
                reduced: "(λv0. v0)",
            },
            EvalTestCase {
                comment: "((I I) I)",
                term: "(((λa. a) (λa. a)) (λa. a))",
                reduced: "(λv0. v0)",
            },
            EvalTestCase {
                comment: "(false I)",
                term: "((λa. (λb. b)) (λa. a))",
                reduced: "(λv0. v0)",
            },
            EvalTestCase {
                comment: "(true I)",
                term: "((λa. (λb. a)) (λa. a))",
                reduced: "(λv0. (λv1. v1))",
            },
            EvalTestCase {
                comment: "((true I) I)",
                term: "(((λa. (λb. a)) (λa. a)) (λa. a))",
                reduced: "(λv0. v0)",
            },

            EvalTestCase {
                comment: "-",
                term: "((λa. (λb. (a b))) (λa. a))",
                reduced: "(λv0. v0)",
            },
            EvalTestCase {
                comment: "-",
                term: "((λa. (λb. (b a))) (λa. (λb. (a b))))",
                reduced: "(λv0. (v0 (λv1. (λv2. (v1 v2)))))",
            },

            /* Some more elaborate tests: generated in bash with the following
             * shortcuts, also see https://en.wikipedia.org/wiki/Church_encoding.

            # boolean logic
            TRUE="(λx. (λy. x))"
            FALSE="(λx. (λy. y))"
            AND="(λp. (λq. ((p q) p)))"
            OR="(λp. (λq. ((p p) q)))"
            IF="(λp. (λa. (λb. ((p a) b))))"

            # lists / bitstrings
            BIT0="$TRUE"
            BIT1="$FALSE"
            NIL="$FALSE"
            CONS="(λx. (λy. (λz. ((z x) y))))"
            CAR="(λp. (p (λx. (λy. x))))"
            CDR="(λp. (p (λx. (λy. y))))"

            # arithmetic / church numerals
            ZERO="(λf. (λx. x))"
            ONE="(λf. (λx. (f x)))"
            TWO="(λf. (λx. (f (f x))))"
            THREE="(λf. (λx. (f (f (f x)))))"
            FOUR="(λf. (λx. (f (f (f (f x))))))"
            ADD="(λm. (λn. (λf. (λx. ((m f) ((n f) x))))))"
            MUL="(λm. (λn. (λf. (λx. (m (n f))))))"

             */

            EvalTestCase {
                comment: "(($AND $TRUE) $FALSE)",
                term: "(((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f)))",
                reduced: "(λv0. (λv1. v1))", // $FALSE
            },
            EvalTestCase {
                comment: "($NOT (($AND $TRUE) $FALSE))",
                term: "((λp. (λa. (λb. ((p b) a)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f))))",
                reduced: "(λv0. (λv1. v0))", // $TRUE
            },
            EvalTestCase {
                comment: "($IF (($AND $TRUE) (($OR $TRUE) $FALSE)))",
                term: "((λp. (λa. (λb. ((p a) b)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (((λp. (λq. ((p p) q))) (λt. (λf. t))) (λt. (λf. f)))))",
                reduced: "(λv0. (λv1. v0))", // $TRUE
            },
            EvalTestCase {
                comment: "($IF (($AND $TRUE) (($AND $TRUE) $FALSE)))",
                term: "((λp. (λa. (λb. ((p a) b)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f)))))",
                reduced: "(λv0. (λv1. v1))", // $FALSE
            },

            EvalTestCase {
                comment: "(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL)))) -- binary string: [1101]",
                term: "(((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))",
                reduced: "(λv0. ((v0 (λv1. (λv2. v2))) (λv3. ((v3 (λv4. (λv5. v5))) (λv6. ((v6 (λv7. (λv8. v7))) (λv9. ((v9 (λv10. (λv11. v11))) (λv12. (λv13. v13))))))))))",
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR $LIST)\"",
                term: "((λp. (p (λx. (λy. x)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))",
                reduced: "(λv0. (λv1. v1))", // 1
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CDR $LIST)\"",
                term: "((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))",
                reduced: "(λv0. ((v0 (λv1. (λv2. v2))) (λv3. ((v3 (λv4. (λv5. v4))) (λv6. ((v6 (λv7. (λv8. v8))) (λv9. (λv10. v10))))))))", // [101]
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR $LIST))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))))",
                reduced: "(λv0. (λv1. v1))", // 1
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR ($CDR $LIST)))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))))",
                reduced: "(λv0. (λv1. v0))", // 0
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CDR ($CDR ($CDR $LIST)))\"",
                term: "((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f)))))))))",
                reduced: "(λv0. ((v0 (λv1. (λv2. v2))) (λv3. (λv4. v4))))", // [1]
            },
            EvalTestCase {
                comment: "LIST=\"(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))\"; echo \"($CAR ($CDR ($CDR ($CDR $LIST))))\"",
                term: "((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))))))",
                reduced: "(λv0. (λv1. v1))", // 1
            },

            EvalTestCase {
                comment: "(($ADD $TWO) $FOUR)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))", // 6
            },
            EvalTestCase {
                comment: "(($ADD (($ADD (($ADD $TWO) $FOUR)) $ONE)) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (λf. (λx. (f x))))) (λf. (λx. (f (f (f x))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($ADD (($ADD $TWO) $FOUR)) (($ADD $ONE) $THREE))",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f x)))) (λf. (λx. (f (f (f x)))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($MUL $TWO) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f x))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))", // 6
            },
            EvalTestCase {
                comment: "(($MUL $FOUR) $THREE)",
                term: "(((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f (f (f x))))))) (λf. (λx. (f (f (f x))))))", 
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))))", // 12
            },
            EvalTestCase {
                comment: "(($ADD (($MUL $TWO) $THREE)) $FOUR)",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f x))))))) (λf. (λx. (f (f (f (f x)))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))", // 10
            },
            EvalTestCase {
                comment: "(($ADD $FOUR) (($MUL $THREE) $TWO))",
                term: "(((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f (f (f x))))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f (f x)))))) (λf. (λx. (f (f x))))))",
                reduced: "(λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))", // 10
            },
        ];

        for case in cases {
            println!("comment {}", case.comment);
            let ast = named::decode(case.term);
            println!("parsed  {}", ast);

            let res = eval(ast);
            println!("reduced in {} steps to {}", res.steps, res.reduced_term);
            assert_eq!(case.reduced, named::encode(&res.reduced_term));

            println!();
        }
    }

    /// Test correct handling of step limit by trying to reduce ω ω.
    #[test]
    fn test_step_limit_handling() {
        let term = named::decode(r"((\x. (x x)) (\x. (x x)))");
        let steps = 100;
        println!(
            "Evaluating term {} for {} steps of the abstract machine",
            term, steps,
        );

        let res = eval_(term, Some(100));
        assert_eq!(EvalResult_::StepLimitExceeded, res);
    }
}
