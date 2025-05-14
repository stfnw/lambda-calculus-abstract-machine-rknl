// SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
// SPDX-License-Identifier: CC-BY-4.0
//
// SPDX-FileCopyrightText: 2025 This specific implementation: Stefan Walter
// SPDX-License-Identifier: MIT

mod eval;
mod format;

fn main() {
    let term = "((λx. ((c x) x)) ((λy. (λz. ((λx. x) z))) ((λx. (x x)) (λx. (x x)))))";

    let ast = format::named::decode(term);
    println!("Reducing example term from paper from section 4.1: {}", ast);

    let res = eval::eval(ast);
    println!("Reduced in {} steps to {}", res.steps, res.reduced_term);
}
