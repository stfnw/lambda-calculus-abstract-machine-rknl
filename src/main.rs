mod format;

use format::named;

use std::rc::Rc;

fn main() {
    // Example term given in 4.1 Elaborate Example Execution
    // > This is one of the simplest examples that uses all transitions of the
    // > machine and demonstrates its main features
    let testcase = EvalTestCase {
        comment: "TODO",
        term: r"((\x. ((c x) x)) ((\y. (\z. ((\x. x) z))) ((\x. (x x)) (\x. (x x)))))",
        reduced: r"c (\z. z) (\z. z)",
    };

    println!("comment {}", testcase.comment);
    let ast = named::decode(testcase.term);
    println!("parsed  {}", ast);
    let reduced = eval(ast);
    println!("reduced {}", reduced);
    assert_eq!(testcase.reduced, named::encode(&reduced));
    println!();
}

struct EvalTestCase<'a> {
    comment: &'a str,
    term: &'a str,
    reduced: &'a str,
}

#[derive(Clone)]
pub enum Term {
    Var { name: String },
    Abs { name: String, body: Rc<Term> },
    App { func: Rc<Term>, arg: Rc<Term> },
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", named::encode(self))
    }
}

#[derive(Clone)]
enum Closure {
    Proper { term: Rc<Term>, env: Rc<Env> },
    Level(usize),
    Res { term: Rc<Term>, level: usize },
}

type Env = Vec<Closure>;

enum Frame {
    Closure { term: Rc<Term>, env: Rc<Env> },
    Lambda,
    Res { term: Rc<Term>, level: usize },
}

pub fn eval(term: Term) -> Term {
    todo!();
}
