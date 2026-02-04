// SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
// SPDX-License-Identifier: CC-BY-4.0
//
// SPDX-FileCopyrightText: 2025 This specific implementation: Stefan Walter
// SPDX-License-Identifier: MIT

pub mod debruijn;
pub mod named;

use crate::format::debruijn::TermDB;
use crate::format::named::{Identifier, Term};

impl From<&TermDB> for Term {
    fn from(tdb: &TermDB) -> Term {
        // Incomplete lambda terms (without child nodes).
        enum Tmp {
            Var(Identifier),
            Abs(Identifier),
            App,
        }

        let mut stack1: Vec<(&TermDB, usize)> = Vec::new();
        stack1.push((tdb, 0));

        let mut stack2: Vec<Tmp> = Vec::new();

        let mut stack3: Vec<Term> = Vec::new();

        while let Some((term, curdepth)) = stack1.pop() {
            match term {
                TermDB::Var { debruijn } => {
                    stack2.push(Tmp::Var(Identifier(curdepth - debruijn - 1)))
                }
                TermDB::Abs { t } => {
                    stack1.push((t, curdepth + 1));
                    stack2.push(Tmp::Abs(Identifier(curdepth)));
                }
                TermDB::App { t1, t2 } => {
                    stack1.push((t2, curdepth));
                    stack1.push((t1, curdepth));
                    stack2.push(Tmp::App);
                }
            }
        }

        while let Some(tmp) = stack2.pop() {
            match tmp {
                Tmp::Var(name) => stack3.push(Term::Var { name }),
                Tmp::Abs(var) => {
                    let t = stack3.pop().unwrap();
                    stack3.push(Term::Abs { var, t: t.into() });
                }
                Tmp::App => {
                    let t1 = stack3.pop().unwrap();
                    let t2 = stack3.pop().unwrap();
                    stack3.push(Term::App {
                        t1: t1.into(),
                        t2: t2.into(),
                    });
                }
            }
        }

        if stack3.len() != 1 {
            panic!(
                "Stack contains not exactly one element after parsing! {:?}",
                stack3
            );
        }

        stack3.pop().unwrap()
    }
}

impl From<&Term> for TermDB {
    fn from(term: &Term) -> TermDB {
        enum Instr<'a> {
            T(&'a Term),
            PopEnv,
        }

        enum Tmp {
            Var(usize),
            Abs,
            App,
        }

        let mut env: Vec<Identifier> = Vec::new();

        let mut stack1: Vec<Instr> = Vec::new();
        stack1.push(Instr::T(term));

        let mut stack2: Vec<Tmp> = Vec::new();

        let mut stack3: Vec<TermDB> = Vec::new();

        while let Some(instr) = stack1.pop() {
            match instr {
                Instr::T(Term::Var { name }) => {
                    let debruijn = match env.iter().rev().position(|var| *var == *name) {
                        Some(i) => i, // 0-based De-Bruijn index
                        None => panic!("Provided term is not closed (free/unbound variable found)"),
                    };
                    stack2.push(Tmp::Var(debruijn));
                }
                Instr::T(Term::Abs { var, t }) => {
                    env.push(var.clone());
                    stack1.push(Instr::PopEnv);
                    stack1.push(Instr::T(t));
                    stack2.push(Tmp::Abs);
                }
                Instr::T(Term::App { t1, t2 }) => {
                    stack1.push(Instr::T(t2));
                    stack1.push(Instr::T(t1));
                    stack2.push(Tmp::App);
                }
                Instr::PopEnv => {
                    env.pop();
                }
            }
        }

        while let Some(tmp) = stack2.pop() {
            match tmp {
                Tmp::Var(debruijn) => stack3.push(TermDB::Var { debruijn }),
                Tmp::Abs => {
                    let t = stack3.pop().unwrap();
                    stack3.push(TermDB::Abs { t: t.into() });
                }
                Tmp::App => {
                    let t1 = stack3.pop().unwrap();
                    let t2 = stack3.pop().unwrap();
                    stack3.push(TermDB::App {
                        t1: t1.into(),
                        t2: t2.into(),
                    });
                }
            }
        }

        if stack3.len() != 1 {
            panic!(
                "Stack contains not exactly one element after parsing! {:?}",
                stack3
            );
        }

        stack3.pop().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ConvertTestCase {
        blc: &'static str,
        bruijn: &'static str,
        named: &'static str,
    }

    /// Test conversions from/to various
    /// formats. Test cases are built from the examples in
    /// https://tromp.github.io/cl/Binary_lambda_calculus.html
    /// and https://justine.lol/lambda/.
    #[test]
    fn test_convert() {
        let cases = [
            ConvertTestCase {
                blc: "0010",
                bruijn: "[0]",
                named: "(λ_0. _0)",
            },
            ConvertTestCase {
                blc: "010001101000011010",
                bruijn: "([(0 0)] [(0 0)])",
                named: "((λ_0. (_0 _0)) (λ_0. (_0 _0)))",
            },
            ConvertTestCase {
                // addition
                blc: "000000000101111101100101111011010",
                bruijn: "[[[[((3 1) ((2 1) 0))]]]]",
                named: "(λ_0. (λ_1. (λ_2. (λ_3. ((_0 _2) ((_1 _2) _3))))))",
            },
            ConvertTestCase {
                // even predicate
                blc: "00010001101000000101100000100001011000001100111101110",
                bruijn: "[([(0 0)] [[((0 [[0]]) [((0 [[1]]) (2 2))])]])]",
                named: "(λ_0. ((λ_1. (_1 _1)) (λ_1. (λ_2. ((_2 (λ_3. (λ_4. _4))) (λ_3. ((_3 (λ_4. (λ_5. _4))) (_1 _1))))))))",
            },
            // universal machine
            ConvertTestCase {
                blc: "0101000110100000000101011000000000011110000101111110011110000101110011110000001111000010110110111001111100001111100001011110100111010010110011100001101100001011111000011111000011100110111101111100111101110110000110010001101000011010",
                bruijn: "(([(0 0)] [[[(((0 [[[[(2 [((4 (2 [((1 (2 [[(2 [((0 1) 2)])]])) (3 [(3 [((2 0) (1 0))])]))])) ((0 (1 [(0 1)])) [((3 [(3 [(1 (0 3))])]) 4)]))])]]]]) (2 2)) 1)]]]) [(0 ([(0 0)] [(0 0)]))])",
                named: "(((λ_0. (_0 _0)) (λ_0. (λ_1. (λ_2. (((_2 (λ_3. (λ_4. (λ_5. (λ_6. (_4 (λ_7. ((_3 (_5 (λ_8. ((_7 (_6 (λ_9. (λ_10. (_8 (λ_11. ((_11 _10) _9))))))) (_5 (λ_9. (_6 (λ_10. ((_8 _10) (_9 _10)))))))))) ((_7 (_6 (λ_8. (_8 _7)))) (λ_8. ((_5 (λ_9. (_6 (λ_10. (_9 (_10 _7)))))) _4))))))))))) (_0 _0)) _1))))) (λ_0. (_0 ((λ_1. (_1 _1)) (λ_1. (_1 _1))))))",
            },
        ];

        for case in cases {
            let ast = debruijn::decode_blc(case.blc).unwrap();
            println!("{}", debruijn::encode_bruijn(&ast));
            println!("{}", debruijn::encode_blc(&ast));
            // println!("AST from binary {:?}", ast);
            assert_eq!(case.blc, debruijn::encode_blc(&ast));
            assert_eq!(case.bruijn, debruijn::encode_bruijn(&ast));
            assert_eq!(case.named, named::encode(&((&ast).into())));

            let ast = named::decode(case.named);
            // println!("AST from text {:?}", ast);
            assert_eq!(case.blc, debruijn::encode_blc(&(&ast).into()));
            assert_eq!(case.bruijn, debruijn::encode_bruijn(&((&ast).into())));
            assert_eq!(case.named, named::encode(&ast));
        }
    }
}
