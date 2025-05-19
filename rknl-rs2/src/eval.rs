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

use std::cell::RefCell;
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
// This version does also automatically garbage collect cached references inside
// the Store map, so that the Store does not grow unnecessarily.

/// Identifiers: used to represent variable names.
// Use a newtype and not a type alias for proper separation of types / to
// prevent confusion.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(pub String);

/// Untyped lambda calculus terms.
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// Manually implementing Drop for Term is needed because otherwise we run into
/// a stack overflow when dropping large trees, because the drop propagates
/// non-tail-recursively through the tree. The issue/solution is described here:
/// https://rust-unofficial.github.io/too-many-lists/first-drop.html
/// https://rust-unofficial.github.io/too-many-lists/third-final.html
/// TODO doc gist
impl Drop for Term {
    fn drop(&mut self) {
        let mut stack: Vec<Rc<Term>> = Vec::new();

        // TODO doc
        fn get_new_dummy_term() -> Rc<Term> {
            Rc::new(Term::Var {
                name: Identifier("".to_string()),
            })
        }

        match self {
            Term::Var { name: _ } => {}
            Term::Abs { var: _, t } => {
                stack.push(std::mem::replace(t, get_new_dummy_term()));
            }
            Term::App { t1, t2 } => {
                stack.push(std::mem::replace(t1, get_new_dummy_term()));
                stack.push(std::mem::replace(t2, get_new_dummy_term()));
            }
        }

        while let Some(term_rc) = stack.pop() {
            // TODO doc if unwrap fails
            if let Ok(mut term) = Rc::try_unwrap(term_rc) {
                match &mut term {
                    Term::Var { name: _ } => {}
                    Term::Abs { var: _, t } => {
                        stack.push(std::mem::replace(t, get_new_dummy_term()));
                    }
                    Term::App { t1, t2 } => {
                        stack.push(std::mem::replace(t1, get_new_dummy_term()));
                        stack.push(std::mem::replace(t2, get_new_dummy_term()));
                    }
                }
                // TODO doc drop
            }
        }
    }
}

// Use a newtype and not a type alias for proper separation of types / to
// prevent confusion. More specifically: use two different types of newtypes:

/// Location used as key in the Store mapping.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Location(usize);
/// Reference-counted location used throughout the other data structures (e.g.
/// Env, Value::LocationAbs and Frame::F4). This variant is used for keeping
/// track of the locations that are currently in scope; it is always reference
/// counted / wrapped in an Rc.
/// When a LocationRef goes fully out of scope (i.e. when its reference count
/// drops to zero), the corresponding Location is added to a list which is then
/// iterated at the end of each abstract machine rule and each of its entry is
/// removed from the Store mapping.
/// This indirection/intermediate manual "garbage collection list" avoids having
/// to store a circular reference to Store itself inside LocationRef.
/// Because of Rusts ownership semantics and the borrow-checker, we use interior
/// mutability to be able to have multiple owners of mutable data.
#[derive(Debug, Clone)]
struct LocationRef {
    i: usize,
    garbage_list: Rc<RefCell<Vec<Location>>>,
}

impl Drop for LocationRef {
    fn drop(&mut self) {
        (*(self.garbage_list)).borrow_mut().push(Location(self.i));
    }
}

/// Converts a LocationRef to a Location suitable for usage as a key inside the
/// Store mapping. Simply throws away the reference and only retains the usize.
impl std::convert::From<&LocationRef> for Location {
    fn from(item: &LocationRef) -> Self {
        Location(item.i)
    }
}

#[derive(Debug)]
struct Env(HashMap<Identifier, Rc<LocationRef>>);

#[derive(Debug)]
struct Closure((Rc<Term>, Rc<Env>));

#[derive(Debug, Clone)]
enum Value {
    Term(Rc<Term>),
    LocationAbs((Rc<LocationRef>, Identifier, Rc<Term>, Rc<Env>)),
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
    F1(Closure),         // Hole c
    F2(Rc<Term>),        // t Hole
    F3(Identifier),      // \x. Hole
    F4(Rc<LocationRef>), // l := Hole
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
    // Temporary list of LocationRef s that are dropped during the reduction.
    // It list is populated when the reference count for LocationRef becomes 0.
    // It is then checked in each loop iteration / after each step of the
    // abstract machine, and contained elements are removed from the cache /
    // mapping Store. Also see the comment in LocationRef.
    let garbage_locations = Rc::new(RefCell::new(Vec::new()));

    // Closure for creating new unique locations by incrementing a counter.
    let mut cur_location: usize = 0;
    let mut fresh_location = {
        let (cur_location, garbage_locations) = (&mut cur_location, &garbage_locations);
        move || {
            let res = LocationRef {
                i: *cur_location,
                garbage_list: Rc::clone(garbage_locations),
            };
            *cur_location += 1;
            Rc::new(res)
        }
    };

    // Closure for creating new unique identifiers (variable names) by
    // incrementing a counter (this assumes without checking that the given
    // lambda term does not already contain variables of the given form).
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
                Term::App { t1, t2 } => {
                    // println!("Rule (1)");
                    Conf::Down(
                        Closure((Rc::clone(t1), Rc::clone(&e))),
                        Stack::Cons(
                            Frame::F1(Closure((Rc::clone(t2), Rc::clone(&e)))),
                            Box::new(s),
                        ),
                        sigma,
                    )
                }

                Term::Abs { var: x, t } => {
                    // println!("Rule (2)");
                    let l = fresh_location();
                    sigma.0.insert((&*l).into(), StorableValue::Todo_);
                    Conf::Up(
                        Value::LocationAbs((l, x.clone(), Rc::clone(t), e)),
                        s,
                        sigma,
                    )
                }

                Term::Var { name: x } => match e.0.get(x) {
                    Some(l) => match sigma.0.get(&((&**l).into())).unwrap() {
                        StorableValue::Todo(Closure((t, e2))) => {
                            // println!("Rule (3)");
                            Conf::Down(
                                Closure((Rc::clone(t), Rc::clone(e2))),
                                Stack::Cons(Frame::F4(Rc::clone(l)), Box::new(s)),
                                sigma,
                            )
                        }

                        StorableValue::Done(v) => {
                            // println!("Rule (4)");
                            Conf::Up(v.clone(), s, sigma)
                        }

                        StorableValue::Todo_ => panic!("Can't happen"),
                    },

                    None => {
                        // No entry in environment for current variable
                        // => variable is unbound => return as-is withoug modification.
                        // println!("Rule (4)");
                        Conf::Up(
                            Value::Term(Rc::new(Term::Var { name: x.clone() })),
                            s,
                            sigma,
                        )
                    }
                },
            },

            Conf::Up(v, Stack::Cons(Frame::F4(l), s), mut sigma) => {
                // println!("Rule (5)");
                sigma.0.insert((&*l).into(), StorableValue::Done(v.clone()));
                Conf::Up(v, *s, sigma)
            }

            Conf::Up(
                Value::LocationAbs((_l, x, t, e)),
                Stack::Cons(Frame::F1(Closure((t2, e2))), s),
                mut sigma,
            ) => {
                // println!("Rule (6)");
                let l2 = fresh_location();
                // Note that we fully clone the environment before extension
                // (see note above on reference counting).
                let mut e_: Env = Env(e.0.clone());
                e_.0.insert(x, Rc::clone(&l2));
                sigma
                    .0
                    .insert((&*l2).into(), StorableValue::Todo(Closure((t2, e2))));
                Conf::Down(Closure((t, Rc::new(e_))), *s, sigma)
            }

            Conf::Up(Value::LocationAbs((l, x, t, e)), s, mut sigma) => {
                match sigma.0.get(&((&*l).into())).unwrap() {
                    StorableValue::Todo_ => {
                        // println!("Rule (7)");
                        let l2 = fresh_location();
                        let x_ = fresh_identifier();

                        // Note that we fully clone the environment before extension
                        // (see note above on reference counting).
                        let mut e_: Env = Env(e.0.clone());
                        e_.0.insert(x, Rc::clone(&l2));

                        sigma.0.insert(
                            (&*l2).into(),
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

                    StorableValue::Done(v) => {
                        // println!("Rule (8)");
                        Conf::Up(v.clone(), s, sigma)
                    }

                    StorableValue::Todo(c) => {
                        panic!("Encountered unexpected closure {:?} in configuration", c)
                    }
                }
            }

            Conf::Up(Value::Term(t), Stack::Cons(Frame::F1(Closure((t2, e2))), s), sigma) => {
                // println!("Rule (9)");
                Conf::Down(Closure((t2, e2)), Stack::Cons(Frame::F2(t), s), sigma)
            }

            Conf::Up(Value::Term(t2), Stack::Cons(Frame::F2(t1), s), sigma) => {
                // println!("Rule (10)");
                Conf::Up(Value::Term(Rc::new(Term::App { t1, t2 })), *s, sigma)
            }

            Conf::Up(Value::Term(t), Stack::Cons(Frame::F3(x), s), sigma) => {
                // println!("Rule (11)");
                Conf::Up(Value::Term(Rc::new(Term::Abs { var: x, t })), *s, sigma)
            }

            Conf::Up(Value::Term(t), Stack::Nil, _sigma) => {
                // println!("Return fully reduced term");
                let t_strong_count = Rc::strong_count(&t);
                // Note that since `eval` takes a `Term` (owned) and constructs
                // an Rc of it internally, the unwrap should always succeed
                // (there can't be any outside references to (sub-)terms).
                return EvalResult_::ReductionCompleted(EvalResult {
                    reduced_term: Rc::try_unwrap(t).unwrap_or_else(|_| {
                        panic!(
                            "Strong reference cound for term is {} != 1, can't unwrap",
                            t_strong_count
                        )
                    }),
                    steps,
                });
            }
        };

        // Update/advance machine state.
        conf = newconf;

        // Increment steps counter.
        steps += 1;

        // Remove Locations that went out of scope in the current step
        // from the cache / mapping in the Conf Store.
        {
            // Copy the intermediate list of Locations dropped during the
            // current abstract machine step.
            //
            // Note that copying is indeed necessary; simply iterating over
            // `garbage_locations` directly while removing map entries can
            // result in a double-mutable-borrow of the RefCell when the
            // Location that is dropped and therefore removed from the Store
            // itself maps to a StorableValue that contains the last LocationRef
            // to another Location index. This leads to the reference count of
            // the latter going to 0, which in turn tries to borrow the Store
            // inside drop mutably (while we are iterating over the store).
            //
            // In the current implementation, these Locations that are dropped
            // during removing Locations from the Store, are not in turn
            // recursively dropped in *this* iteration, but rather at the
            // cleanup stage of the *next* abstract machine step.
            let tmp: Vec<_> = garbage_locations.borrow_mut().drain(..).collect();

            // Get mutable reference to Store.
            let store = match conf {
                Conf::Down(_, _, ref mut store) => store,
                Conf::Up(_, _, ref mut store) => store,
            };

            // Remove dropped locations from Store mapping.
            for l in tmp {
                store.0.remove(&l);
            }
        }

        // Stop abstract machine if step-limit is reached.
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
    fn test_eval_hardcoded() {
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

    // Short-hand function for constructing Term::Var.
    fn var(v: &str) -> Term {
        Term::Var {
            name: Identifier(v.to_string()),
        }
    }
    // Short-hand function for constructing Term::Abs.
    fn abs(var: &str, t: Term) -> Term {
        Term::Abs {
            var: Identifier(var.to_string()),
            t: Rc::new(t),
        }
    }
    // Short-hand function for constructing Term::App.
    fn app(t1: Term, t2: Term) -> Term {
        Term::App {
            t1: Rc::new(t1),
            t2: Rc::new(t2),
        }
    }

    // Definitions from the paper from section 4.2 Empirical Execution Lengths.
    // (and some more).

    #[allow(non_snake_case)]
    fn I() -> Term {
        abs("x", var("x"))
    }

    fn omega() -> Term {
        abs("x", app(var("x"), var("x")))
    }

    #[allow(non_snake_case)]
    fn K() -> Term {
        abs("x", abs("y", var("x")))
    }

    #[allow(non_snake_case)]
    fn K_() -> Term {
        abs("x", abs("y", var("y")))
    }

    #[rustfmt::skip]
    fn pair() -> Term {
        abs("x", abs("y", abs("f",
                    app(app(var("f"), var("x")), var("y")))))
    }

    fn dub() -> Term {
        abs("x", abs("f", app(app(var("f"), var("x")), var("x"))))
    }

    #[rustfmt::skip]
    // Note that compared to the definition in the paper in section 4.2, I had
    // to swap K and K_ in the definition of pred for it to work correctly.
    // This is also consistent with the actual code accompanying the paper;
    // compare source.tar.xz 8ecee8214d76e1acde57b67635feea5d common/term.rkt
    // - lines 93/94 definition of yes/no (K/K_)
    // - line 154-158 definition of Church-pred-aux and Church-pred
    fn pred() -> Term {
        abs("n", abs("f", abs("x",
                    app(
                        app(
                            app(
                                var("n"),
                                abs("e", app(
                                        app(pair(), app(var("e"), K_())),
                                        app(var("f"), app(var("e"), K_()))))),
                            app(app(pair(), var("x")), var("x"))),
                        K()))))
    }

    /// Build lambda term for n-th Church numeral.
    fn church_encode(n: usize) -> Term {
        if n == 0 {
            abs("f", abs("x", var("x")))
        } else {
            let f = var("f");
            let x = var("x");
            let mut body = x;

            // Apply f n times
            for _ in 0..n {
                body = app(f.clone(), body);
            }

            abs("f", abs("x", body))
        }
    }

    /// Decode Church numeral lambda term to number
    fn church_decode(t: Term) -> Option<usize> {
        match t {
            Term::Abs {
                var: ref f,
                t: ref body,
            } => match &**body {
                Term::Abs { var: x, t: t2 } => {
                    let mut count = 0;
                    let mut cur = Rc::clone(t2);

                    loop {
                        match &*cur {
                            Term::Var { name } => {
                                if name == x {
                                    break;
                                } else {
                                    return None;
                                }
                            }
                            Term::App { t1, t2 } => match &**t1 {
                                Term::Var { name } => {
                                    if *name == *f {
                                        count += 1;
                                        cur = Rc::clone(t2);
                                    } else {
                                        return None;
                                    }
                                }
                                _ => return None,
                            },

                            _ => return None,
                        }
                    }

                    Some(count)
                }

                _ => None,
            },

            _ => None,
        }
    }

    /// Add two Church numerals.
    #[rustfmt::skip]
    fn church_add() -> Term {
        abs("m", abs("n", abs("f", abs("x",
            app(
                app(var("m"), var("f")),
                app(app(var("n"), var("f")), var("x")))))))
    }

    /// Multiply two Church numerals.
    #[rustfmt::skip]
    fn church_mul() -> Term {
        abs("m", abs("n", abs("f", abs("x",
            app(
                app(var("m"), app(var("n"), var("f"))),
                var("x"))))))
    }

    struct EvalTestCaseFamily<'a> {
        comment: &'a str,
        // Function that builds the n-term of this term family given an integer n.
        term_f: fn(usize) -> Term,
        // Function that computes the number of steps for reducing the n-term
        // of this term family given an integer n.
        steps_f: fn(usize) -> usize,
    }

    /// Test correct beta reduction and number of steps for the various
    /// term families given in the paper in Table 3.
    #[test]
    fn test_eval_paper_term_families() {
        let cases = [
            EvalTestCaseFamily {
                comment: "c_n c_2 I",
                term_f: |n| app(app(church_encode(n), church_encode(2)), I()),
                steps_f: |n| 10 * 2_usize.pow(n as u32) + 5 * n + 5,
            },
            EvalTestCaseFamily {
                comment: "pred c_n",
                term_f: |n| app(pred(), church_encode(n)),
                steps_f: |n| 30 * n + 41,
            },
            EvalTestCaseFamily {
                comment: r"\x. c_n ω x",
                term_f: |n| abs("x", app(app(church_encode(n), omega()), var("x"))),
                steps_f: |n| 9 * n + 15,
            },
            EvalTestCaseFamily {
                comment: "c_n dub I",
                term_f: |n| app(app(church_encode(n), dub()), I()),
                steps_f: |n| 18 * n + 15,
            },
            EvalTestCaseFamily {
                comment: r"c_n dub (\x. I x)",
                term_f: |n| app(app(church_encode(n), dub()), abs("x", app(I(), var("x")))),
                steps_f: |n| 18 * n + 20,
            },
        ];

        for case in cases.into_iter() {
            println!("[+] Term family: {}", case.comment);

            for n in 1..=9 {
                println!();

                let term = (case.term_f)(n);
                println!("  - term {}: {}", n, term);

                // clone() is only needed for allowing printing in assert.
                let res = eval(term.clone());
                println!("    reduced in {} steps", res.steps);
                println!("    reduced term: {}", res.reduced_term);

                assert_eq!(
                    (case.steps_f)(n),
                    res.steps,
                    "Term: {}, reduced: {}, steps: {}",
                    term,
                    res.reduced_term,
                    res.steps
                );
            }

            println!();
        }
    }

    /// Test correct beta reduction of randomly generated arithmetic expressions.
    #[test]
    fn test_eval_random_arithmetic_expression() {
        let mut rng = Rng::seeded(42);
        for _ in 0..100 {
            let expr = Expr::random(&mut rng, 9);
            println!("Random arithmetic expression: {}", expr);

            let res1 = expr.eval_interpret();
            println!("  - result by interpretation of AST:   {}", res1);

            let res2 = expr.eval_lambda();
            println!(
                "  - result by evaluating lambda terms: {} ({} steps)",
                res2.0, res2.1
            );

            assert_eq!(res1, res2.0);

            println!();
        }
    }

    pub struct Rng {
        pub state: u64,
    }

    #[allow(dead_code)]
    impl Rng {
        /// Create a new PRNG with a seed based on current time.
        pub fn new() -> Self {
            Self::seeded(unsafe { core::arch::x86_64::_rdtsc() })
        }

        /// Create a new PRNG from a seed value.
        pub fn seeded(seed: u64) -> Self {
            Self { state: seed }
        }

        /// Create new random number and advance the internal state.
        // xorshift64 implementation from G. Marsaglia, “Xorshift RNGs,” J. Stat. Soft., vol. 8, no. 14, pp. 1–6, Jul. 2003, doi: 10.18637/jss.v008.i14.
        // SPDX-License-Identifier: MIT
        pub fn next(&mut self) -> u64 {
            self.state ^= self.state << 13;
            self.state ^= self.state >> 7;
            self.state ^= self.state << 17;
            self.state
        }

        /// Create random u64.
        pub fn u64(&mut self) -> u64 {
            self.next()
        }

        /// Create random number in given range [min,max).
        /// Uses naive way that leads to slightly non-uniform distribution.
        pub fn range(&mut self, min: u64, max: u64) -> u64 {
            assert!(min < max, "{} >= {}", min, max);
            let range = max - min;
            min + (self.next() % range)
        }

        /// Create random number in range [0,max).
        pub fn int(&mut self, max: u64) -> u64 {
            self.range(0, max)
        }
    }

    /// Arithmetic expression.
    enum Expr {
        Val(u32),
        Add(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
    }

    impl std::fmt::Display for Expr {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Expr::Val(i) => write!(f, "{}", i),
                Expr::Add(op1, op2) => write!(f, "({} + {})", op1, op2),
                Expr::Mul(op1, op2) => write!(f, "({} * {})", op1, op2),
            }
        }
    }

    impl Expr {
        /// Create a random arithmetic expression of a rough size.
        fn random(rng: &mut Rng, size: usize) -> Expr {
            if size == 0 {
                Expr::Val(rng.range(2, 6) as u32)
            } else {
                let op1 = Box::new(Expr::random(rng, size / 2));
                let op2 = Box::new(Expr::random(rng, size / 2));
                match rng.int(4) {
                    0 => Expr::Mul(op1, op2),
                    // Prefer addition with higher probability; this leads to
                    // smaller numbers; this is important because Church
                    // numerals are a unary encoding.
                    _ => Expr::Add(op1, op2),
                }
            }
        }

        fn church_encode(&self) -> Term {
            match self {
                Expr::Val(i) => church_encode(*i as usize),
                Expr::Add(op1, op2) => {
                    let op1 = op1.church_encode();
                    let op2 = op2.church_encode();
                    app(app(church_add(), op1), op2)
                }
                Expr::Mul(op1, op2) => {
                    let op1 = op1.church_encode();
                    let op2 = op2.church_encode();
                    app(app(church_mul(), op1), op2)
                }
            }
        }

        /// Evaluate arithmetic expression by converting it to a lambda term and
        /// running RKNL to reduce the term.
        fn eval_lambda(&self) -> (i32, usize) {
            let term = self.church_encode();
            let res = eval(term);
            (church_decode(res.reduced_term).unwrap() as i32, res.steps)
        }

        /// Evaluate arithmetic expression by walking and interpreting the AST.
        fn eval_interpret(&self) -> i32 {
            match self {
                Expr::Val(i) => *i as i32,
                Expr::Add(op1, op2) => op1.eval_interpret() + op2.eval_interpret(),
                Expr::Mul(op1, op2) => op1.eval_interpret() * op2.eval_interpret(),
            }
        }
    }
}
