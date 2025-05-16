<!--
SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
SPDX-License-Identifier: CC-BY-4.0

SPDX-FileCopyrightText: 2025 This specific implementation: Stefan Walter
SPDX-License-Identifier: MIT
-->

This iteration/version of RKNL is a direct implementation of the paper in Rust.
It uses fully explicit types (newtypes instead of type aliases), which makes the code very verbose, but helped me in better understanding how the machine works.


# Usage

To reduce an untyped lambda calculus term, simply provided it as only argument to the program on the commandline (note that the parser is dumb and requires verbose explicit paranthesis for abstraction and application).
For example to reduce the example term given in the paper -- which is "one of the simplest examples that uses all transitions of the machine and demonstrates its main features" -- we can run the program as follows:

```
$ cargo run -- "((λx. ((c x) x)) ((λy. (λz. ((λx. x) z))) ((λx. (x x)) (λx. (x x)))))"
   Compiling lambda-calculus-abstract-machine-rknl v0.1.0 (/data/rknl1)
...
Parsed term: ((λx. ((c x) x)) ((λy. (λz. ((λx. x) z))) ((λx. (x x)) (λx. (x x)))))
Reduced term in 27 steps to: ((c (λv0. v0)) (λv0. v0))
```

This term has also been incorporated in the tests (see following sections).


# Tests

`src/eval.rs` contains a bunch of tests to make sure that my implementation is correct.
All tests can be run with:

```
cargo test
```

With the following invocation, the verbose output is printed:

```
cargo test -- --nocapture
```

The rest of this sections shows some example output from some implemented tests:


## Previously shown term from section 4.1 of the paper

```
$ cargo test test_eval_paper_example -- --nocapture                                   
   Compiling lambda-calculus-abstract-machine-rknl v0.1.0 (/data/rknl1)
...
running 1 test
comment Example term given in the paper in section 4.1
parsed  ((λx. ((c x) x)) ((λy. (λz. ((λx. x) z))) ((λx. (x x)) (λx. (x x)))))
reduced in 27 steps to term ((c (λv0. v0)) (λv0. v0))
test eval::tests::test_eval_paper_example ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out; finished in 0.01s
```


## Reduction of some hard-coded lambda terms

The terms are mainly constructed for boolean, arithmetic and list manipulation operations.
The following listing shows an excerpt of the output:

```
$ cargo test test_eval_hardcoded -- --nocapture
   Compiling lambda-calculus-abstract-machine-rknl v0.1.0 (/data/rknl1)
...
comment (ω I)
parsed  ((λa. (a a)) (λa. a))
reduced in 27 steps to term ((c (λv0. v0)) (λv0. v0))
reduced in 15 steps to (λv0. v0)
test eval::tests::test_eval_paper_example ...
comment ((I I) I)
parsed  (((λa. a) (λa. a)) (λa. a))
ok
reduced in 15 steps to (λv0. v0)

comment (false I)
parsed  ((λa. (λb. b)) (λa. a))
reduced in 8 steps to (λv0. v0)

comment (true I)
parsed  ((λa. (λb. a)) (λa. a))
reduced in 14 steps to (λv0. (λv1. v1))

...

comment ($IF (($AND $TRUE) (($AND $TRUE) $FALSE)))
parsed  ((λp. (λa. (λb. ((p a) b)))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (((λp. (λq. ((p q) p))) (λt. (λf. t))) (λt. (λf. f)))))
reduced in 58 steps to (λv0. (λv1. v1))

comment (($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL)))) -- binary string: [1101]
parsed  (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))
reduced in 129 steps to (λv0. ((v0 (λv1. (λv2. v2))) (λv3. ((v3 (λv4. (λv5. v5))) (λv6. ((v6 (λv7. (λv8. v7))) (λv9. ((v9 (λv10. (λv11. v11))) (λv12. (λv13. v13))))))))))

...

comment LIST="(($CONS $BIT1) (($CONS $BIT1) (($CONS $BIT0) (($CONS $BIT1) $NIL))))"; echo "($CAR ($CDR ($CDR ($CDR $LIST))))"
parsed  ((λp. (p (λx. (λy. x)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) ((λp. (p (λx. (λy. y)))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. t))) (((λx. (λy. (λz. ((z x) y)))) (λt. (λf. f))) (λt. (λf. f))))))))))
reduced in 113 steps to (λv0. (λv1. v1))

...

comment (($ADD $TWO) $FOUR)
parsed  (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))
reduced in 63 steps to (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))

comment (($ADD (($ADD (($ADD $TWO) $FOUR)) $ONE)) $THREE)
parsed  (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (λf. (λx. (f x))))) (λf. (λx. (f (f (f x))))))
reduced in 139 steps to (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))

comment (($ADD (($ADD $TWO) $FOUR)) (($ADD $ONE) $THREE))
parsed  (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f (f x)))))))) (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f x)))) (λf. (λx. (f (f (f x)))))))
reduced in 139 steps to (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))

...

comment (($ADD (($MUL $TWO) $THREE)) $FOUR)
parsed  (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f x))))) (λf. (λx. (f (f (f x))))))) (λf. (λx. (f (f (f (f x)))))))
reduced in 114 steps to (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))

comment (($ADD $FOUR) (($MUL $THREE) $TWO))
parsed  (((λm. (λn. (λf. (λx. ((m f) ((n f) x)))))) (λf. (λx. (f (f (f (f x))))))) (((λm. (λn. (λf. (λx. ((m (n f)) x))))) (λf. (λx. (f (f (f x)))))) (λf. (λx. (f (f x))))))
reduced in 119 steps to (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))))

test eval::tests::test_eval_hardcoded ... ok
```


## Reduction of a given non-terminating term until a maximum of steps is reached

The implementation allows limiting the steps taken during execution in order to attempt reducing non-terminating terms like "ω ω".

```
$ cargo test test_step_limit_handling -- --nocapture   
...
running 1 test
Evaluating term ((λx. (x x)) (λx. (x x))) for 100 steps of the abstract machine
test eval::tests::test_step_limit_handling ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out; finished in 0.00s
```


# Reduction of term families from section 4.2 of the paper

Here is some example output for testing this implementation against the provided term families in section 4.2 "Empirical Execution Lengths" and asserting that the number of steps match the expected ones:

```
$ cargo test test_eval_paper_term_families -- --nocapture
  Compiling lambda-calculus-abstract-machine-rknl v0.1.0 (/data/rknl1)
...
running 1 test
[+] Term family: c_n c_2 I

  - term 1: (((λf. (λx. (f x))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 30 steps
    reduced term: (λv0. v0)

  - term 2: (((λf. (λx. (f (f x)))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 55 steps
    reduced term: (λv0. v0)

  - term 3: (((λf. (λx. (f (f (f x))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 100 steps
    reduced term: (λv0. v0)

  - term 4: (((λf. (λx. (f (f (f (f x)))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 185 steps
    reduced term: (λv0. v0)

  - term 5: (((λf. (λx. (f (f (f (f (f x))))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 350 steps
    reduced term: (λv0. v0)

  - term 6: (((λf. (λx. (f (f (f (f (f (f x)))))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 675 steps
    reduced term: (λv0. v0)

  - term 7: (((λf. (λx. (f (f (f (f (f (f (f x))))))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 1320 steps
    reduced term: (λv0. v0)

  - term 8: (((λf. (λx. (f (f (f (f (f (f (f (f x)))))))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 2605 steps
    reduced term: (λv0. v0)

  - term 9: (((λf. (λx. (f (f (f (f (f (f (f (f (f x))))))))))) (λf. (λx. (f (f x))))) (λx. x))
    reduced in 5170 steps
    reduced term: (λv0. v0)

[+] Term family: pred c_n

  - term 1: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f x))))
    reduced in 71 steps
    reduced term: (λv0. (λv1. v1))

  - term 2: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f x)))))
    reduced in 101 steps
    reduced term: (λv0. (λv1. (v0 v1)))

  - term 3: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f x))))))
    reduced in 131 steps
    reduced term: (λv0. (λv1. (v0 (v0 v1))))

  - term 4: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f x)))))))
    reduced in 161 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 v1)))))

  - term 5: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f (f x))))))))
    reduced in 191 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 (v0 v1))))))

  - term 6: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f (f (f x)))))))))
    reduced in 221 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 v1)))))))

  - term 7: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f (f (f (f x))))))))))
    reduced in 251 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))

  - term 8: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f (f (f (f (f x)))))))))))
    reduced in 281 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1)))))))))

  - term 9: ((λn. (λf. (λx. (((n (λe. (((λx. (λy. (λf. ((f x) y)))) (e (λx. (λy. y)))) (f (e (λx. (λy. y))))))) (((λx. (λy. (λf. ((f x) y)))) x) x)) (λx. (λy. x)))))) (λf. (λx. (f (f (f (f (f (f (f (f (f x))))))))))))
    reduced in 311 steps
    reduced term: (λv0. (λv1. (v0 (v0 (v0 (v0 (v0 (v0 (v0 (v0 v1))))))))))

[+] Term family: \x. c_n ω x

  - term 1: (λx. (((λf. (λx. (f x))) (λx. (x x))) x))
    reduced in 24 steps
    reduced term: (λv0. (v0 v0))

  - term 2: (λx. (((λf. (λx. (f (f x)))) (λx. (x x))) x))
    reduced in 33 steps
    reduced term: (λv0. ((v0 v0) (v0 v0)))

  - term 3: (λx. (((λf. (λx. (f (f (f x))))) (λx. (x x))) x))
    reduced in 42 steps
    reduced term: (λv0. (((v0 v0) (v0 v0)) ((v0 v0) (v0 v0))))

  - term 4: (λx. (((λf. (λx. (f (f (f (f x)))))) (λx. (x x))) x))
    reduced in 51 steps
    reduced term: (λv0. ((((v0 v0) (v0 v0)) ((v0 v0) (v0 v0))) (((v0 v0) (v0 v0)) ((v0 v0) (v0 v0)))))

...

[+] Term family: c_n dub I

  - term 1: (((λf. (λx. (f x))) (λx. (λf. ((f x) x)))) (λx. x))
    reduced in 33 steps
    reduced term: (λv0. ((v0 (λv1. v1)) (λv1. v1)))

  - term 2: (((λf. (λx. (f (f x)))) (λx. (λf. ((f x) x)))) (λx. x))
    reduced in 51 steps
    reduced term: (λv0. ((v0 (λv1. ((v1 (λv2. v2)) (λv2. v2)))) (λv1. ((v1 (λv2. v2)) (λv2. v2)))))

  - term 3: (((λf. (λx. (f (f (f x))))) (λx. (λf. ((f x) x)))) (λx. x))
    reduced in 69 steps
    reduced term: (λv0. ((v0 (λv1. ((v1 (λv2. ((v2 (λv3. v3)) (λv3. v3)))) (λv2. ((v2 (λv3. v3)) (λv3. v3)))))) (λv1. ((v1 (λv2. ((v2 (λv3. v3)) (λv3. v3)))) (λv2. ((v2 (λv3. v3)) (λv3. v3)))))))

...

[+] Term family: c_n dub (\x. I x)

  - term 1: (((λf. (λx. (f x))) (λx. (λf. ((f x) x)))) (λx. ((λx. x) x)))
    reduced in 38 steps
    reduced term: (λv0. ((v0 (λv1. v1)) (λv1. v1)))

  - term 2: (((λf. (λx. (f (f x)))) (λx. (λf. ((f x) x)))) (λx. ((λx. x) x)))
    reduced in 56 steps
    reduced term: (λv0. ((v0 (λv1. ((v1 (λv2. v2)) (λv2. v2)))) (λv1. ((v1 (λv2. v2)) (λv2. v2)))))

  - term 3: (((λf. (λx. (f (f (f x))))) (λx. (λf. ((f x) x)))) (λx. ((λx. x) x)))
    reduced in 74 steps
    reduced term: (λv0. ((v0 (λv1. ((v1 (λv2. ((v2 (λv3. v3)) (λv3. v3)))) (λv2. ((v2 (λv3. v3)) (λv3. v3)))))) (λv1. ((v1 (λv2. ((v2 (λv3. v3)) (λv3. v3)))) (λv2. ((v2 (λv3. v3)) (λv3. v3)))))))

...

test eval::tests::test_eval_paper_term_families ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 3 filtered out; finished in 0.04s
```
