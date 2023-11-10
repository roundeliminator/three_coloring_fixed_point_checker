use itertools::Itertools;
use std::hash::Hash;
use std::fmt::Display;
use std::collections::HashMap;
use std::collections::BTreeSet as Set;


// the labels of the problem are all right-closed (w.r.t. D) subsets of the following set
#[derive(Copy, Clone, Ord, Eq, PartialEq, PartialOrd, Hash, Debug)]
enum L {
    A,
    B,
    C,
    X,
    Y,
    P,
}

// Expr(x,y,z,w) represents the expression    x + y d + z Delta + w free_param
#[derive(Eq, PartialEq, Clone, Debug)]
struct Expr(isize, isize, isize, isize); 


// a line is described as follows
// the first element is a pair actually describing the line, and it is as an array of pairs
//   where the first element of the pair is a right-closed subset of L,
//   and the second element is the multiplicity (its exponent)
// the second element of the pair is an array describing the constraints on the exponents of the line.
//    each element is an expression, and the represented constraint is expression >= 0
struct Line<'a>(Vec<(&'a Set<L>, Expr)>, Vec<Expr>);

impl<'a> Line<'a> {
    // this function computes all right-closed cuts of the line
    fn cuts(&self) -> Vec<(Set<Set<L>>, Expr)> {
        let mut cuts = vec![];
        for possible_cut in self.0.iter().cloned().powerset() {
            let sets: Set<_> = possible_cut.iter().map(|x| x.0.clone()).collect();
            let mut is_cut = true;
            for (group, _) in &self.0 {
                if !sets.contains(&group) && sets.iter().any(|set| set.is_superset(group)) {
                    is_cut = false;
                }
            }
            if is_cut {
                let mut sum = Expr(0, 0, 0, 0);
                for (_, exp) in possible_cut {
                    sum.0 += exp.0;
                    sum.1 += exp.1;
                    sum.2 += exp.2;
                    sum.3 += exp.3;
                }
                cuts.push((sets, sum));
            }
        }
        cuts
    }
}


// code for printing an expression
impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let write_coeff =
            |f: &mut std::fmt::Formatter<'_>, x: isize| write!(f, "{:+}", x);
        if self.2 != 0 {
            write_coeff(f, self.2)?;
            write!(f, "*Δ")?;
        }
        if self.1 != 0 {
            write_coeff(f, self.1)?;
            write!(f, "*d")?;
        }
        if self.3 != 0 {
            write_coeff(f, self.3)?;
            write!(f, "*k")?;
        }
        if self.0 != 0 {
            write_coeff(f, self.0)?;
        }
        if *self == Expr(0, 0, 0, 0) {
            write!(f, "0")?;
        }
        Ok(())
    }
}

// code for printing a label
impl Display for L {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            L::X => write!(f, "X"),
            L::Y => write!(f, "Y"),
            L::A => write!(f, "A"),
            L::B => write!(f, "B"),
            L::C => write!(f, "C"),
            L::P => write!(f, "+"),
        }
    }
}
struct DisplaySetL<'a>(&'a Set<L>);
impl<'a> Display for DisplaySetL<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for label in self.0.iter().sorted() {
            write!(f, "{}", label)?;
        }
        if self.0.is_empty() {
            write!(f, "∅")?;
        }
        Ok(())
    }
}


// code for printing a line
impl<'a> Display for Line<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for group in &self.0 {
            write!(f,"{}",DisplaySetL(&group.0))?;
            write!(f, "^({}) ", group.1)?;
        }
        write!(f, "   ")?;
        if !self.1.is_empty() {
            write!(f, "     ( ")?;
            for (i,constr) in self.1.iter().enumerate() {
                if i != self.1.len() - 1 {
                    write!(f, "{} >= 0,   ", constr)?;
                } else {
                    write!(f, "{} >= 0   ", constr)?;
                }
            }
            write!(f, " )")?;
        }
        Ok(())
    }
}



// matchconstr aims at representing an expression of the form:
// constant + sum x_ij = exponent of a line
// matchconstr represents this as a triple (x, constant, pair) where
// x is a vector containing the pairs (i,j) for which we sum x_ij
// the first element of pair is a value t in {0,1}, where 0 (resp. 1) indicates that we are referring to the first (resp. second) line that we are combining
// expr is value of the the exponent
#[derive(Debug)]
struct MatchConstr(Vec<(usize, usize)>, isize, (usize, Expr));

// newline represents the result of combining two lines
// int is the result of the Sup operation
// unions are all the possible results of the Inf operations
// constraints is an array of what the exponents of the unions must satisfy
// original_constraints are the constraints on the exponents of the two lines that we combined (the first element of each pair is 0 or 1 and indicates from which line the constraint comes from)
// range is a pair that keeps track of how many different labels are in the two lines that we combined
struct NewLine {
    int: Set<L>,
    unions: Vec<((usize, usize), Set<L>)>,
    constraints: Vec<MatchConstr>,
    original_constraints: Vec<(usize, Expr)>,
    range: (usize, usize),
}


// this function combines two lines by taking the Sup in positions int1 and int2
// it returns the combination line, with all its constraints in it
fn combine_lines_at(l1: &Line, l2: &Line, int1: usize, int2: usize) -> NewLine {
    let g1 = &l1.0[int1];
    let g2 = &l2.0[int2];
    let group1 = &g1.0;
    let group2 = &g2.0;
    let mut eqs = vec![];
    let mut sets_union = vec![];
    let set_itersection = intersection(group1, group2);
    for i in 0..l1.0.len() {
        let mut vars = vec![];
        for j in 0..l2.0.len() {
            vars.push((i, j));
        }
        let plus1 = if i == int1 { 1 } else { 0 };
        let eq = MatchConstr(vars, plus1, (0, l1.0[i].1.clone()));
        eqs.push(eq);
    }
    for j in 0..l2.0.len() {
        let mut vars = vec![];
        for i in 0..l1.0.len() {
            vars.push((i, j));
        }
        let plus1 = if j == int2 { 1 } else { 0 };
        let eq = MatchConstr(vars, plus1, (1, l2.0[j].1.clone()));
        eqs.push(eq);
    }
    for i in 0..l1.0.len() {
        for j in 0..l2.0.len() {
            sets_union.push(((i, j), union(&l1.0[i].0.clone(), &l2.0[j].0.clone())))
        }
    }
    let mut orig: Vec<_> = l1.1.iter().cloned().map(|x| (0, x)).collect();
    orig.extend(l2.1.iter().cloned().map(|x| (1, x)));
    let newline = NewLine {
        range: (l1.0.len(), l2.0.len()),
        int: set_itersection,
        unions: sets_union,
        constraints: eqs,
        original_constraints: orig,
    };
    newline
}

// this function returns a pair:
// the first element is an array of constraints, that, if satisfied, indicate that line dominates newline (the constraints P_{i,2})
// the second element are the constraints that need to be satisfied in order to use this line as a target (the constraints P_{i,1})
fn is_contained(
    newline: &NewLine,
    line: &Line,
    freshvar: usize,
) -> (Vec<MatchConstr>, Vec<(usize, Expr)>) {
    let mut cover: HashMap<Set<L>, Set<Set<L>>> = HashMap::new();
    cover.entry(newline.int.clone()).or_default();
    for g in &line.0 {
        let target_set = g.0;
        if target_set.is_subset(&newline.int) {
            cover
                .entry(newline.int.clone())
                .or_default()
                .insert(target_set.clone());
        }
        for (_, set) in &newline.unions {
            if target_set.is_subset(&set) {
                cover
                    .entry(set.clone())
                    .or_default()
                    .insert(target_set.clone());
            }
        }
    }

    let mut constraints = vec![];
    for (cut, sum) in line.cuts() {
        let plus1 = if cut.is_superset(&cover[&newline.int]) {
            1
        } else {
            0
        };
        let mut vars = vec![];
        for (var, union) in &newline.unions {
            //println!("cut : {:?}, var : {:?}, union : {:?}",cut,var,union);
            if !cover.contains_key(&union) || cut.is_superset(&cover[&union]) {
                vars.push(var.clone());
            }
        }
        let constr = MatchConstr(vars, plus1, (freshvar, sum));
        constraints.push(constr);
    }

    (
        constraints,
        line.1.iter().cloned().map(|x| (freshvar, x)).collect(),
    )
}

// this function generates the inequalities A
fn generate_assumptions(newline: &NewLine, additional: &Vec<Expr>) -> String {
    let mut v = vec![];
    v.push("p = MixedIntegerLinearProgram()".into());
    // we do not actually need the variables to be integers
    // v.push("v = p.new_variable(integer=True, nonnegative=True)".into());
    // v.push("w = p.new_variable(integer=True)".into());
    v.push("v = p.new_variable(nonnegative=True)".into());
    v.push("w = p.new_variable()".into());
    v.push(format!("Δ = v['Δ']"));
    v.push(format!("d = v['d']"));
    v.push(format!("k_0 = v['k_0']"));
    v.push(format!("k_1 = v['k_1']"));

    for i in 0..newline.range.0 {
        for j in 0..newline.range.1 {
            v.push(format!("x_{}{} = v['x_{}{}']", i, j, i, j));
        }
    }
    v.push("p.set_objective(0)".into());

    // equalities A_1
    v.push("# generic assumptions".into());
    for expr in additional {
        v.push(format!("p.add_constraint({} >= 0)", expr));
    }
    
    // inequalities A_2
    v.push("# assumptions of original lines".into());
    for expr in &newline.original_constraints {
        let e = format!("{}", expr.1);
        let e_r = e.replace("k", &format!("k_{}", expr.0));
        v.push(format!("p.add_constraint({} >= 0)", e_r));
    }

    // equalities A_3
    v.push("# assumptions of new line".into());
    for constr in &newline.constraints {
        let vars = &constr.0;
        let add = &constr.1;
        let result = &constr.2;
        let vars = vars.iter().map(|(a, b)| format!("x_{}{}", a, b)).join("+");
        let e = format!("{}", result.1);
        let e_r = e.replace("k", &format!("k_{}", result.0));
        v.push(format!("p.add_constraint({} + {} == {})", vars, add, e_r));
    }
    v.join("\n")
}

// this function generates the inequalities P
fn generate_requirements(reqs: &(Vec<MatchConstr>, Vec<(usize, Expr)>)) -> String {
    let mut v = vec![];
    // equalities P_{i,2}
    v.push("# requirements of target line".into());
    for expr in &reqs.1 {
        let e = format!("{}", expr.1);
        let e_r = e.replace("k", &format!("k_{}", expr.0));
        v.push(format!("p.add_constraint({} >= 0)", e_r));
    }
    // equalities P_{i,1}
    v.push("# requirements of mapping".into());
    for constr in &reqs.0 {
        let vars = &constr.0;
        let add = &constr.1;
        let result = &constr.2;
        let vars = vars.iter().map(|(a, b)| format!("x_{}{}", a, b)).join("+");
        let e = format!("{}", result.1);
        let e_r = e.replace("k", &format!("k_{}", result.0));
        v.push(format!("p.add_constraint({} + {} <= {})", vars, add, e_r));
    }
    v.join("\n")
}

// we run sage to test that the systems of inequalities that we generate have no solution
struct Solver {
    _c: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: std::io::BufReader<std::process::ChildStdout>,
}
impl Solver {
    fn init() -> Self {
        let mut child = std::process::Command::new("sage")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("Failed to spawn child process");

        let stdin = child.stdin.take().expect("Failed to open stdin");
        let stdout =
            std::io::BufReader::new(child.stdout.take().expect("Failed to open stdout"));
        Self {
            _c: child,
            stdin,
            stdout,
        }
    }
    fn is_feasible(&mut self, case: &str) -> bool {
        std::io::Write::write_all(&mut self.stdin, b"sage.misc.reset.reset()\n")
            .expect("Failed to write to stdin");
        let init = "def f(p):\n    try:\n        p.solve()\n        return False;\n    except Exception as e:\n        return \"The problem or its dual has been proven infeasible\" in str(e)\n\n";
        std::io::Write::write_all(&mut self.stdin, init.as_bytes())
            .expect("Failed to write to stdin");
        std::io::Write::write_all(&mut self.stdin, case.as_bytes())
            .expect("Failed to write to stdin");
        std::io::Write::write_all(
            &mut self.stdin,
            "\nprint(\"Result is \" + str(f(p)))\n".as_bytes(),
        )
        .expect("Failed to write to stdin");
        let mut override_isfalse = false;
        let result = loop {
            let mut line = String::new();
            std::io::BufRead::read_line(&mut self.stdout, &mut line).unwrap();
            if line.contains("Result is ") {
                break line.contains("False");
            }
            if line.contains("argument must be a linear function or constraint, got False") {
                override_isfalse = true;
            }
            if line.contains("argument must be a linear function or constraint, got True") {
                panic!("argument must be a linear function or constraint, got True");
            }
        };
        if override_isfalse {
            return false;
        }
        result
    }
}

// this function converts (A implies Or(P_1 .. ) into many separate systems of inequalities to check
fn prove_cover(
    s: &str,
    cases: &Vec<String>,
    solver: &mut Solver,
    freevars: &Vec<&str>,
    print_only : bool
) -> bool {
    if cases.is_empty() {
        return false;
    }

    // here we generate A_4
    let mut vfree = vec![];
    for i in 0..cases.len() {
        vfree.push(format!("k_{} = w['k_{}']", i + 2, i + 2));
    }
    for s in freevars {
        vfree.push(format!("p.add_constraint({})", s));
    }

    // each case is a P_i
    let cases: Vec<Vec<&str>> = cases
        .iter()
        .map(|case| {
            case.split("\n")
                .filter(|s| !s.starts_with("#"))
                .collect::<Vec<_>>()
        })
        .collect();

    // we take one inequality from each P_i in all possible way, and we negate it
    let prod = cases
        .iter()
        .map(|case| case.iter())
        .multi_cartesian_product();
    for case in prod {
        let mut v = vec![s.into(), vfree.join("\n")];
        v.push("# negated one per target case".into());
        for eq in case {
            let rev = if eq.contains(">=") {
                eq.replace(">=", "+1 <=")
            } else {
                eq.replace("<=", "-1 >=")
            };
            v.push(rev);
        }
        let case = v.join("\n");
        // the obtained system of inequalities must NOT be solvable
        if print_only {
            println!("\n\nsage.misc.reset.reset()\n{}\np.solve()\n\n",case);
        } else {
            if solver.is_feasible(&case) {
                panic!("{}", case);
            }
        }
    }
    return true;
}

// this function uses the observations of the paper to discard some Sup that are not worth to be considered
fn good_intersections(l1: &Line, l2: &Line) -> HashMap<Set<L>, Vec<(usize, usize)>> {
    let s1: Vec<_> = l1.0.iter().map(|part| &part.0).collect();
    let s2: Vec<_> = l2.0.iter().map(|part| &part.0).collect();
    let is_subset = |a: &Set<L>, b: &Set<L>| a.is_subset(b);
    let mut ints = HashMap::new();

    for (i, x) in s1.iter().enumerate() {
        for (j, y) in s2.iter().enumerate() {
            if x.is_superset(y) || y.is_superset(x) {
                continue;
            }

            let int = intersection(x, y);
            let same_int: &mut Vec<(usize, usize)> = ints.entry(int).or_default();

            let len = same_int.len();
            same_int.retain(|&(xc, yc)| !(is_subset(s1[xc], x) && is_subset(s2[yc], y)));
            if same_int.len() != len
                || same_int
                    .iter()
                    .all(|&(xc, yc)| !(is_subset(x, &s1[xc]) && is_subset(y, &s2[yc])))
            {
                same_int.push((i, j));
            }
        }
    }

    ints
}

// this function tests all possible pairs of lines, takes the Sup in all possible ways, and check that the result is dominated by some existing line
fn test_all(
    lines: &Vec<Vec<Line>>,
    additional: &Vec<Expr>,
    mapping: &Vec<(
        (usize, usize, &Set<L>),
        (usize, usize, &Set<L>),
        Vec<(usize, usize)>,
        Vec<&str>,
    )>,
) {
    let mut solver = Solver::init();

    let mapping: HashMap<_, _> = mapping
        .iter()
        .map(|(line1, line2, target, freevars)| {
            (
                (
                    (line1.0, line1.1, line1.2.clone()),
                    (line2.0, line2.1, line2.2.clone()),
                ),
                (target, freevars),
            )
        })
        .collect();

    for ci in 0..7 {
        for cj in ci..7 {
            for si in 0..lines[ci].len() {
                for sj in 0..lines[cj].len() {
                    // when we consider the same group of lines twice, we can discard symmetric cases
                    if ci == cj && sj < si {
                        continue;
                    }
                    // discarding 2 because it is symmetric to 1
                    if ci + 1 == 2 {
                        continue;
                    }
                    // discarding 4 because it is symmetric to 3
                    if ci + 1 == 4 {
                        continue;
                    }
                    // more symmetric cases, e.g. combining 1.3 with 2.1 is symmetric to 1.1 with 2.3
                    if ci + 1 == 1 && cj + 1 == 2 && si > sj {
                        continue;
                    }
                    if ci + 1 == 3 && cj + 1 == 4 && si > sj {
                        continue;
                    }
                    let l1 = &lines[ci][si];
                    let l2 = &lines[cj][sj];
                    let ints = good_intersections(l1, l2);
                    for (_, cases) in ints {
                        for (p1, p2) in cases {
                            println!("Testing the following pair of lines:\n {}.{})    {}\n {}.{})    {}\nSup on {} and {}\n",ci+1,si+1,l1,cj+1,sj+1,l2,DisplaySetL(&l1.0[p1].0),DisplaySetL(&l2.0[p2].0));
                            test_combination(ci,si,cj,sj,l1,l2,p1,p2,&mapping,additional,&mut solver, lines,false);
                        }
                    }
                }
            }
        }
    }
}


// we test the combination of two specific lines for a specific sup
fn test_combination(ci : usize, si : usize, cj : usize, sj : usize, l1 : &Line, l2 : &Line, p1 : usize, p2 : usize,
    mapping : &HashMap<((usize, usize, Set<L>), (usize, usize, Set<L>)), (&Vec<(usize, usize)>, &Vec<&str>)>,
    additional : &Vec<Expr>,
    solver : &mut Solver,
    lines : &Vec<Vec<Line>>,
    print_only : bool
){
    
    let key = (
        (ci + 1, si + 1, l1.0[p1].0.clone()),
        (cj + 1, sj + 1, l2.0[p2].0.clone()),
    );
    let set_to_string = |set: &Set<L>| {
        "s_".chars()
            .chain(
                set.iter()
                    .map(|l| {
                        l.to_string()
                            .to_lowercase()
                            .chars()
                            .next()
                            .unwrap()
                    })
                    .sorted_by_key(|c| match c {
                        'a' => 1,
                        'b' => 2,
                        'c' => 3,
                        'x' => 4,
                        'y' => 5,
                        '+' => 6,
                        _ => unreachable!(),
                    }),
            )
            .collect::<String>()
            .replace("+", "p")
    };
    let mut notinlist = false;
    let (target, freevars) = if !mapping.contains_key(&key) {
        notinlist = true;
        (vec![(1, 1)], vec![])
        // if it is not in the list it may be that the two lines have incompatible requirements
        // so we just target an arbitrary line and the solver may derive a contradiction in the requirements
    } else {
        let (t, v) = mapping[&key];
        (t.clone(), v.clone())
    };
    let newline = combine_lines_at(&l1, &l2, p1, p2);
    let assumptions = generate_assumptions(&newline, &additional);
    let target = target
        .iter()
        .enumerate()
        .map(|(i, t)| {
            generate_requirements(&is_contained(
                &newline,
                &lines[t.0 - 1][t.1 - 1],
                i + 2,
            ))
        })
        .collect();
    if ["k_2", "k_3"].iter().any(|fv| {
        freevars.iter().filter(|expr| expr.contains(fv)).count() > 1
    }) {
        panic!("Broken assumptions on k_2 or k_3");
    }
    if !prove_cover(&assumptions, &target, solver, &freevars,print_only) {
        let reason = if notinlist {
            "not in the list"
        } else {
            "is broken"
        };
        println!(
            "Case ({},{},{}),({},{},{}) {}!",
            key.0 .0,
            key.0 .1,
            set_to_string(&key.0 .2),
            key.1 .0,
            key.1 .1,
            set_to_string(&key.1 .2),
            reason
        );
        panic!("Not proved!");
    }
}


fn intersection(g1: &Set<L>, g2: &Set<L>) -> Set<L> {
    g1.intersection(g2).cloned().collect()
}

fn union(g1: &Set<L>, g2: &Set<L>) -> Set<L> {
    let mut r: Set<L> = g2.union(g1).cloned().collect();
    if r.contains(&L::X) && r.contains(&L::Y) && !r.contains(&L::P) && r.len() > 2 {
        r.insert(L::P);
    }
    r
}


fn main() {
   
    // we define one variable for each possible label
    let s_e: &Set<L> = &Set::new();
    let s_x = &Set::from([L::X]);
    let s_cx = &Set::from([L::C, L::X]);
    let s_acx = &Set::from([L::A, L::C, L::X]);
    let s_ax = &Set::from([L::A, L::X]);
    let s_by = &Set::from([L::B, L::Y]);
    let s_y = &Set::from([L::Y]);
    let s_cxy = &Set::from([L::C, L::X, L::Y]);
    let s_cy = &Set::from([L::C, L::Y]);
    let s_bcy = &Set::from([L::B, L::C, L::Y]);
    let s_acxyp = &Set::from([L::A, L::C, L::X, L::Y, L::P]);
    let s_axyp = &Set::from([L::A, L::X, L::Y, L::P]);
    let s_abxyp = &Set::from([L::A, L::B, L::X, L::Y, L::P]);
    let s_bcxyp = &Set::from([L::B, L::C, L::X, L::Y, L::P]);
    let s_bxyp = &Set::from([L::B, L::X, L::Y, L::P]);
    let s_abcxyp = &Set::from([L::A, L::B, L::C, L::X, L::Y, L::P]);
    let s_xyp = &Set::from([L::X, L::Y, L::P]);
    let s_xy = &Set::from([L::X, L::Y]);
    let s_c = &Set::from([L::C]);
    let s_cxyp = &Set::from([L::C, L::X, L::Y, L::P]);


    
    // these are the lines of the fixed point, grouped in 7 cases
    let lines = vec![
        //type 1
        vec![
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cx, Expr(0, 1, 0, 0)),
                    (s_acx, Expr(-1, -2, 1, 0)),
                ],
                vec![],
            ),
            Line(
                vec![(s_x, Expr(1, 2, 0, 0)), (s_acx, Expr(-1, -2, 1, 0))],
                vec![],
            ),
            Line(
                vec![(s_x, Expr(0, 1, 0, 0)), (s_ax, Expr(0, -1, 1, 0))],
                vec![],
            ),
        ],
        //type 2
        vec![
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cy, Expr(0, 1, 0, 0)),
                    (s_bcy, Expr(-1, -2, 1, 0)),
                ],
                vec![],
            ),
            Line(
                vec![(s_y, Expr(1, 2, 0, 0)), (s_bcy, Expr(-1, -2, 1, 0))],
                vec![],
            ),
            Line(
                vec![(s_y, Expr(0, 1, 0, 0)), (s_by, Expr(0, -1, 1, 0))],
                vec![],
            ),
        ],
        //type 3
        vec![
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cx, Expr(1, 1, 0, 0)),
                    (s_acxyp, Expr(0, 1, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cx, Expr(1, 1, 0, 0)),
                    (s_acxyp, Expr(-2, -2, 1, 0)),
                ],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_x, Expr(2, 2, 0, 0)),
                    (s_acxyp, Expr(0, 1, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![(s_x, Expr(2, 2, 0, 0)), (s_acxyp, Expr(-2, -2, 1, 0))],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_x, Expr(1, 1, 0, 0)),
                    (s_axyp, Expr(1, 2, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![(s_x, Expr(1, 1, 0, 0)), (s_axyp, Expr(-1, -1, 1, 0))],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_x, Expr(1, 1, 0, 0)),
                    (s_axyp, Expr(0, 1, 0, 0)),
                    (s_abxyp, Expr(-1, -2, 1, 0)),
                ],
                vec![],
            ),
        ],
        //type 4
        vec![
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cy, Expr(1, 1, 0, 0)),
                    (s_bcxyp, Expr(0, 1, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cy, Expr(1, 1, 0, 0)),
                    (s_bcxyp, Expr(-2, -2, 1, 0)),
                ],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_y, Expr(2, 2, 0, 0)),
                    (s_bcxyp, Expr(0, 1, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![(s_y, Expr(2, 2, 0, 0)), (s_bcxyp, Expr(-2, -2, 1, 0))],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_y, Expr(1, 1, 0, 0)),
                    (s_bxyp, Expr(1, 2, 0, 0)),
                    (s_abcxyp, Expr(-2, -3, 1, 0)),
                ],
                vec![Expr(-3, -3, 1, 0)],
            ),
            Line(
                vec![(s_y, Expr(1, 1, 0, 0)), (s_bxyp, Expr(-1, -1, 1, 0))],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_y, Expr(1, 1, 0, 0)),
                    (s_bxyp, Expr(0, 1, 0, 0)),
                    (s_abxyp, Expr(-1, -2, 1, 0)),
                ],
                vec![],
            ),
        ],
        //type 5
        vec![
            Line(
                vec![
                    (s_e, Expr(2, 1, 0, 0)),
                    (s_cxy, Expr(0, 0, 0, 1)),
                    (s_acxyp, Expr(0, 1, 0, -1)),
                    (s_bcxyp, Expr(0, 1, 0, -1)),
                    (s_abcxyp, Expr(-2, -3, 1, 1)),
                ],
                vec![Expr(0, 0, 0, 1), Expr(0, 1, 0, -1), Expr(-2, -3, 1, 1)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 0, 0, 0)),
                    (s_xy, Expr(1, 1, 0, 1)),
                    (s_acxyp, Expr(0, 1, 0, -1)),
                    (s_bcxyp, Expr(0, 1, 0, -1)),
                    (s_abcxyp, Expr(-2, -3, 1, 1)),
                ],
                vec![Expr(0, 0, 0, 1), Expr(0, 1, 0, -1), Expr(-2, -3, 1, 1)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 0, 0, 0)),
                    (s_xy, Expr(0, 0, 0, 1)),
                    (s_axyp, Expr(1, 2, 0, -1)),
                    (s_bcxyp, Expr(0, 1, 0, -1)),
                    (s_abcxyp, Expr(-2, -3, 1, 1)),
                ],
                vec![Expr(0, 0, 0, 1), Expr(0, 1, 0, -1), Expr(-2, -3, 1, 1)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 0, 0, 0)),
                    (s_xy, Expr(0, 0, 0, 1)),
                    (s_acxyp, Expr(0, 1, 0, -1)),
                    (s_bxyp, Expr(1, 2, 0, -1)),
                    (s_abcxyp, Expr(-2, -3, 1, 1)),
                ],
                vec![Expr(0, 0, 0, 1), Expr(0, 1, 0, -1), Expr(-2, -3, 1, 1)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 0, 0, 0)),
                    (s_xy, Expr(0, 0, 0, 1)),
                    (s_axyp, Expr(0, 1, 0, -1)),
                    (s_bxyp, Expr(0, 1, 0, -1)),
                    (s_abxyp, Expr(-1, -2, 1, 1)),
                ],
                vec![Expr(0, 0, 0, 1), Expr(0, 1, 0, -1), Expr(-1, -2, 1, 1)],
            ),
        ],
        //type 6
        // x + y d + z Delta + w free_param
        vec![
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cxy, Expr(1, 1, 0, 0)),
                    (s_cxyp, Expr(1, 0, 0, 0)),
                    (s_abcxyp, Expr(1, 0, 0, 0)),
                ],
                vec![Expr(4, 2, -1, 0), Expr(-4, -2, 1, 0)],
            ),
            Line(
                vec![
                    (s_e, Expr(1, 1, 0, 0)),
                    (s_cxy, Expr(4, 3, -1, 0)),
                    (s_cxyp, Expr(-5, -4, 2, 0)),
                ],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_xy, Expr(2, 2, 0, 0)),
                    (s_cxyp, Expr(1, 0, 0, 0)),
                    (s_abcxyp, Expr(1, 0, 0, 0)),
                ],
                vec![Expr(4, 2, -1, 0), Expr(-4, -2, 1, 0)],
            ),
            Line(
                vec![
                    (s_xy, Expr(5, 4, -1, 0)), 
                    (s_cxyp, Expr(-5, -4, 2, 0))
                ],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_xy, Expr(1, 1, 0, 0)),
                    (s_xyp, Expr(2, 1, 0, 0)),
                    (s_abcxyp, Expr(1, 0, 0, 0)),
                ],
                vec![Expr(4, 2, -1, 0), Expr(-4, -2, 1, 0)],
            ),
            Line(
                vec![
                    (s_xy, Expr(4, 3, -1, 0)), 
                    (s_xyp, Expr(-4, -3, 2, 0))
                ],
                vec![Expr(2, 3, -1, 0)],
            ),
            Line(
                vec![
                    (s_xy, Expr(0, 0, 0, 1)),
                    (s_xyp, Expr(3, 2, 0, -2)),
                    (s_abxyp, Expr(-3, -2, 1, 1)),
                ],
                vec![Expr(-2, 0, 0, 1), Expr(1, 1, 0, -1)],
            )
        ],
        //type 7
        vec![Line(
            vec![(s_e, Expr(0, 1, 0, 0)), (s_c, Expr(0, -1, 1, 0))],
            vec![],
        )],
    ];

    // these are the expressions for the constraints A_1 (expr >= 0)
    let additional = vec![
        Expr(-1, 1, 0, 0),
        Expr(4, 2, -1, 0),
        Expr(-3, -2, 1, 0),
        Expr(-5, 0, 1, 0),
    ]; 

    // this is the table stating where we plan to map the combinations (symmetries are not here)
    // For example:
    // ((1,1,s_acx),(2,1,s_bcy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
    // this is stating that if we combine the first line of case 1 with the first line of case 2
    // by taking Sup between ACX (of line 1.1)  and BCY (of line 2.1),
    // then all the configurations given by the combination line should be included in lines 5.1 and 7.1,
    // and that for case 5.1 we should set k_2 equal to x_11
    let mapping : Vec<((usize, usize, &Set<L>), (usize, usize, &Set<L>), Vec<(usize, usize)>, Vec<&str>)> = vec![
            ((1,1,s_cx),(1,3,s_ax),vec![(1, 2)],vec![]),
            ((1,1,s_acx),(2,1,s_bcy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
            ((1,1,s_acx),(2,2,s_y),vec![(5, 1),(7, 1)],vec!["k_2 == d-x_20"]),
            ((1,1,s_acx),(2,2,s_bcy),vec![(5, 1), (7, 1)],vec!["k_2 == x_10"]),
            ((1,1,s_acx),(2,3,s_by),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((1,2,s_x),(2,2,s_bcy),vec![(5, 2),(7, 1)],vec!["k_2 == d-x_01"]),
            ((1,2,s_acx),(2,2,s_y),vec![(5, 2),(7, 1)],vec!["k_2 == d-x_10"]),
            ((1,2,s_acx),(2,2,s_bcy),vec![(5, 2), (7, 1)],vec!["k_2 == d-x_01"]),
            ((1,2,s_acx),(2,3,s_by),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(2,3,s_by),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((1,1,s_acx),(3,5,s_axyp),vec![(1, 3), (3, 3)],vec![]),
            ((1,1,s_cx),(3,5,s_axyp),vec![(1, 2)],vec![]),
            ((1,1,s_cx),(3,6,s_axyp),vec![(1, 2)],vec![]),
            ((1,1,s_acx),(3,6,s_axyp),vec![(1, 3), (3, 4)],vec![]),
            ((1,1,s_acx),(3,7,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,1,s_cx),(3,7,s_abxyp),vec![(1, 2)],vec![]),
            ((1,2,s_acx),(3,5,s_axyp),vec![(1, 3), (3, 3)],vec![]),
            ((1,2,s_acx),(3,6,s_axyp),vec![(1, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(3,7,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(3,1,s_cx),vec![(3, 3)],vec![]),
            ((1,3,s_ax),(3,2,s_cx),vec![(3, 4)],vec![]),
            ((1,1,s_acx),(4,1,s_bcxyp),vec![(3, 1), (7, 1)],vec![]),
            ((1,1,s_acx),(4,1,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
            ((1,1,s_acx),(4,2,s_bcxyp),vec![(3, 2), (7, 1)],vec![]),
            ((1,1,s_acx),(4,2,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
            ((1,1,s_acx),(4,3,s_y),vec![(5, 1)],vec!["k_2 == x_21"]),
            ((1,1,s_acx),(4,3,s_bcxyp),vec![(3, 1)],vec![]),
            ((1,1,s_acx),(4,4,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((1,1,s_acx),(4,4,s_bcxyp),vec![(3, 2)],vec![]),
            ((1,1,s_acx),(4,5,s_y),vec![(5, 1)],vec!["k_2 == x_10"]),
            ((1,1,s_acx),(4,5,s_bxyp),vec![(5, 1), (3, 3)],vec!["k_2 == x_10"]),
            ((1,1,s_acx),(4,6,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((1,1,s_acx),(4,6,s_bxyp),vec![(5, 1), (3, 4)],vec!["k_2 == d-x_20"]),
            ((1,1,s_acx),(4,7,s_abxyp),vec![(5, 1), (1, 3), (3, 3), (3, 4)],vec!["k_2 == d-x_20"]),
            ((1,1,s_acx),(4,7,s_bxyp),vec![(5, 1), (3, 3),(3, 4)],vec!["k_2 == d-x_20"]), 
            ((1,1,s_acx),(4,7,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((1,2,s_x),(4,1,s_cy),vec![(5, 1),(7, 1)],vec!["k_2 == x_01"]),
            ((1,2,s_acx),(4,1,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_01"]),
            ((1,2,s_acx),(4,1,s_bcxyp),vec![(7, 1),(3, 1)],vec![]), 
            ((1,2,s_x),(4,2,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == d-x_02"]), 
            ((1,2,s_acx),(4,2,s_bcxyp),vec![(7, 1),(3, 2)],vec![]),
            ((1,2,s_acx),(4,2,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_01"]),
            ((1,2,s_acx),(4,3,s_bcxyp),vec![(3, 3)],vec![]),
            ((1,2,s_acx),(4,3,s_y),vec![(5, 2)],vec!["k_2 == x_11"]),
            ((1,2,s_acx),(4,4,s_bcxyp),vec![(3, 4)],vec![]),
            ((1,2,s_acx),(4,4,s_y),vec![(5, 2)],vec!["k_2 == d-x_01"]),
            ((1,2,s_acx),(4,5,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((1,2,s_acx),(4,5,s_bxyp),vec![(3, 3)],vec![]),
            ((1,2,s_acx),(4,6,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((1,2,s_acx),(4,6,s_bxyp),vec![(3, 4)],vec![]),
            ((1,2,s_acx),(4,7,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(4,7,s_y),vec![(5, 4)],vec!["k_2 == x_00"]), 
            ((1,2,s_acx),(4,7,s_bxyp),vec![(3, 4),(3, 3), (3, 7)],vec![]),
            ((1,3,s_ax),(4,1,s_bcxyp),vec![(3, 3)],vec![]),
            ((1,3,s_ax),(4,1,s_cy),vec![(5, 1)],vec!["k_2 == x_01"]),
            ((1,3,s_ax),(4,2,s_cy),vec![(5, 1)],vec!["k_2 == d-x_02"]),
            ((1,3,s_ax),(4,2,s_bcxyp),vec![(3, 4)],vec![]),
            ((1,3,s_ax),(4,3,s_y),vec![(5, 3)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(4,3,s_bcxyp),vec![(3, 5)],vec![]),
            ((1,3,s_ax),(4,4,s_bcxyp),vec![(3, 6)],vec![]),
            ((1,3,s_ax),(4,4,s_y),vec![(5, 3)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(4,5,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(4,5,s_bxyp),vec![(3, 5)],vec![]),
            ((1,3,s_ax),(4,6,s_bxyp),vec![(3, 6)],vec![]),
            ((1,3,s_ax),(4,6,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(4,7,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((1,3,s_ax),(4,7,s_bxyp),vec![(3, 7)],vec![]),
            ((1,1,s_acx),(5,1,s_bcxyp),vec![(3, 1), (3, 2)],vec![]),
            ((1,1,s_acx),(5,1,s_cxy),vec![(3, 1), (3, 2)],vec![]),
            ((1,1,s_acx),(5,2,s_bcxyp),vec![(3, 1), (3, 2)],vec![]),
            ((1,1,s_acx),(5,2,s_xy),vec![(5, 1), (3, 3), (3, 4)],vec!["k_2 == k_1"]),
            ((1,1,s_acx),(5,3,s_bcxyp),vec![(1, 1),(3, 2),(3, 3)],vec![]),
            ((1,1,s_acx),(5,3,s_axyp),vec![(5, 1), (1, 3), (3, 3), (3, 4)],vec!["k_2 == k_1"]),
            ((1,1,s_cx),(5,3,s_axyp),vec![(5, 1), (1, 2)],vec!["k_2 == k_1"]),
            ((1,1,s_acx),(5,4,s_bxyp),vec![(5, 1), (3, 3), (3, 4)],vec!["k_2 == k_1"]),
            ((1,2,s_acx),(5,1,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,1,s_cxy),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,2,s_xy),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,2,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,3,s_bcxyp),vec![(1, 3),(3, 3),(3, 4)],vec![]), 
            ((1,2,s_acx),(5,3,s_axyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,3,s_xy),vec![(1, 3),(3, 3),(3, 4)],vec![]),
            ((1,2,s_acx),(5,4,s_bxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,5,s_xy),vec![(3, 7)],vec![]),
            ((1,2,s_acx),(5,5,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(5,5,s_bxyp),vec![(3, 7)],vec![]),
            ((1,3,s_ax),(5,1,s_cxy),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(5,1,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(5,2,s_xy),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(5,2,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(5,3,s_bcxyp),vec![(3, 5), (3, 6)],vec![]),
            ((1,3,s_ax),(5,3,s_xy),vec![(3, 3),(3,4),(3,5),(3,6)],vec![]),
            ((1,3,s_ax),(5,4,s_bxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(5,5,s_xy),vec![(3, 7)],vec![]),
            ((1,3,s_ax),(5,5,s_bxyp),vec![(3, 7)],vec![]),
            ((1,1,s_acx),(6,1,s_cxyp),vec![(3, 1), (3, 2), (7, 1)],vec![]),
            ((1,1,s_acx),(6,2,s_cxyp),vec![(3, 2), (7, 1)],vec![]),
            ((1,1,s_acx),(6,3,s_xy),vec![(3, 3), (3, 4)],vec![]),
            ((1,1,s_acx),(6,4,s_xy),vec![(3, 4)],vec![]),
            ((1,1,s_acx),(6,5,s_xyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,1,s_acx),(6,6,s_xyp),vec![(3, 4)],vec![]),
            ((1,1,s_acx),(6,7,s_xyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,1,s_cx),(6,7,s_abxyp),vec![(1, 2)],vec![]),
            ((1,1,s_acx),(6,7,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(6,1,s_cxyp),vec![(7, 1),(3, 1),(3, 2)],vec![]),
            ((1,2,s_acx),(6,2,s_cxyp),vec![(7, 1), (3, 2)],vec![]), 
            ((1,2,s_acx),(6,3,s_xy),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(6,4,s_xy),vec![(3, 4)],vec![]),
            ((1,2,s_acx),(6,4,s_cxyp),vec![(3, 4)],vec![]),
            ((1,2,s_acx),(6,5,s_xyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(6,6,s_xyp),vec![(3, 4)],vec![]),
            ((1,2,s_acx),(6,7,s_abxyp),vec![(1, 3), (3, 3), (3, 4)],vec![]),
            ((1,2,s_acx),(6,7,s_xyp),vec![(3, 4),(3, 7),(3, 3)],vec![]),
            ((1,3,s_ax),(6,1,s_cxyp),vec![(3, 3), (3, 4)],vec![]),
            ((1,3,s_ax),(6,2,s_cxyp),vec![(3, 4)],vec![]),
            ((1,3,s_ax),(6,3,s_cxyp),vec![(3, 5), (3, 6)],vec![]),
            ((1,3,s_ax),(6,4,s_cxyp),vec![(3, 6)],vec![]),
            ((1,3,s_ax),(6,5,s_xyp),vec![(3, 5), (3, 6)],vec![]),
            ((1,3,s_ax),(6,6,s_xyp),vec![(3, 6)],vec![]),
            ((1,3,s_ax),(6,7,s_xyp),vec![(3, 7)],vec![]),
            ((1,2,s_x),(7,1,s_c),vec![(1, 1)],vec![]),
            ((1,3,s_ax),(7,1,s_c),vec![(1, 1)],vec![]),
            ((3,1,s_cx),(3,5,s_axyp),vec![(3, 3)],vec![]),
            ((3,1,s_acxyp),(3,7,s_abxyp),vec![(3, 5)],vec![]),
            ((3,1,s_cx),(3,7,s_abxyp),vec![(3, 3)],vec![]),
            ((3,2,s_cx),(3,6,s_axyp),vec![(3, 4)],vec![]),
            ((3,2,s_acxyp),(3,7,s_abxyp),vec![(3, 6)],vec![]),
            ((3,2,s_cx),(3,7,s_abxyp),vec![(3, 4)],vec![]),
            ((3,3,s_acxyp),(3,7,s_abxyp),vec![(3, 5)],vec![]),
            ((3,4,s_acxyp),(3,7,s_abxyp),vec![(3, 6)],vec![]),
            ((3,1,s_cx),(4,1,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
            ((3,1,s_acxyp),(4,1,s_bcxyp),vec![(6, 1), (7, 1)],vec!["k_2 == x_00"]),
            ((3,1,s_cx),(4,3,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((3,1,s_acxyp),(4,3,s_bcxyp),vec![(6, 1)],vec!["k_2 == d+d"]),
            ((3,1,s_acxyp),(4,5,s_bxyp),vec![(6, 3),(4, 3)],vec!["k_2 == x_01"]),
            ((3,1,s_cx),(4,5,s_bxyp),vec![(5, 1), (3, 3)],vec!["k_2 == x_10"]),
            ((3,1,s_cx),(4,5,s_y),vec![(5, 1)],vec!["k_2 == x_10"]),
            ((3,1,s_cx),(4,7,s_abxyp),vec![(5, 1), (3, 3)],vec!["k_2 == x_10"]),
            ((3,1,s_acxyp),(4,7,s_abxyp),vec![(6, 3),(4, 3)],vec!["k_2 == x_10"]), 
            ((3,1,s_cx),(4,7,s_y),vec![(5, 1)],vec!["k_2 == x_10"]),
            ((3,2,s_cx),(4,2,s_cy),vec![(5, 1), (7, 1)],vec!["k_2 == x_11"]),
            ((3,2,s_acxyp),(4,2,s_bcxyp),vec![(6, 2), (7, 1)],vec!["k_2 == x_11-x_22"]),
            ((3,2,s_cx),(4,4,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((3,2,s_acxyp),(4,4,s_bcxyp),vec![(6, 2)],vec!["k_2 == 1+1"]),
            ((3,2,s_cx),(4,6,s_bxyp),vec![(5, 1), (3, 4)],vec!["k_2 == d-x_20"]),
            ((3,2,s_acxyp),(4,6,s_bxyp),vec![(6, 4),(4, 4)],vec!["k_2 == x_10-x_21"]),
            ((3,2,s_cx),(4,6,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((3,2,s_cx),(4,7,s_abxyp),vec![(5, 1), (3, 4)],vec!["k_2 == d-x_20"]),
            ((3,2,s_acxyp),(4,7,s_bxyp),vec![(6, 4),(4, 4)],vec!["k_2 == 1+1"]),
            ((3,2,s_cx),(4,7,s_y),vec![(5, 1)],vec!["k_2 == d-x_20"]),
            ((3,2,s_acxyp),(4,7,s_abxyp),vec![(6, 4),(4, 4)],vec!["k_2 == 1+1"]), 
            ((3,3,s_x),(4,3,s_y),vec![(5, 2)],vec!["k_2 == d-x_01"]),
            ((3,3,s_acxyp),(4,3,s_bcxyp),vec![(6, 3)],vec!["k_2 == d+d"]),
            ((3,3,s_acxyp),(4,5,s_bxyp),vec![(6, 5)],vec!["k_2 == d+d"]),
            ((3,3,s_x),(4,5,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((3,3,s_acxyp),(4,7,s_bxyp),vec![(6, 5)],vec!["k_2 == d+d"]), 
            ((3,3,s_x),(4,7,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((3,3,s_acxyp),(4,7,s_abxyp),vec![(6, 5)],vec!["k_2 == d+d"]),
            ((3,4,s_x),(4,4,s_y),vec![(5, 2)],vec!["k_2 == d-x_01"]),
            ((3,4,s_x),(4,6,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((3,4,s_x),(4,7,s_y),vec![(5, 4)],vec!["k_2 == x_00"]),
            ((3,5,s_x),(4,5,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((3,5,s_axyp),(4,5,s_bxyp),vec![(6, 5)],vec!["k_2 == d+d"]),
            ((3,5,s_x),(4,7,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((3,5,s_axyp),(4,7,s_bxyp),vec![(6, 5)],vec!["k_2 == d+d"]), 
            ((3,6,s_x),(4,6,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((3,6,s_x),(4,7,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((3,6,s_axyp),(4,7,s_bxyp),vec![(6, 7)],vec!["k_2 == x_00+x_02"]),
            ((3,7,s_x),(4,7,s_y),vec![(5, 5)],vec!["k_2 == x_00"]),
            ((3,7,s_axyp),(4,7,s_bxyp),vec![(6, 7)],vec!["k_2 == x_00+x_02"]),
            ((3,1,s_acxyp),(5,1,s_bcxyp),vec![(3, 1)],vec![]),
            ((3,1,s_cx),(5,2,s_xy),vec![(5, 1), (3, 3)],vec!["k_2 == k_1"]),
            ((3,1,s_acxyp),(5,2,s_bcxyp),vec![(3, 1)],vec![]),
            ((3,1,s_acxyp),(5,3,s_bcxyp),vec![(3, 1)],vec![]),
            ((3,1,s_cx),(5,3,s_axyp),vec![(5, 1), (3, 3)],vec!["k_2 == k_1"]),
            ((3,1,s_cx),(5,4,s_bxyp),vec![(5, 1), (3, 3)],vec!["k_2 == k_1"]),
            ((3,1,s_cx),(5,5,s_abxyp),vec![(5, 1), (3, 3)],vec!["k_2 == k_1"]),
            ((3,2,s_acxyp),(5,1,s_bcxyp),vec![(3, 2)],vec![]),
            ((3,2,s_cx),(5,2,s_xy),vec![(5, 1), (3, 4)],vec!["k_2 == k_1"]),
            ((3,2,s_acxyp),(5,2,s_bcxyp),vec![(3, 2)],vec![]),
            ((3,2,s_cx),(5,3,s_axyp),vec![(5, 1), (3, 4)],vec!["k_2 == k_1"]),
            ((3,2,s_acxyp),(5,3,s_bcxyp),vec![(3, 2)],vec![]),
            ((3,2,s_cx),(5,4,s_bxyp),vec![(5, 1), (3, 4)],vec!["k_2 == k_1"]),
            ((3,3,s_acxyp),(5,1,s_bcxyp),vec![(3, 3)],vec![]),
            ((3,3,s_acxyp),(5,2,s_bcxyp),vec![(3, 3)],vec![]),
            ((3,3,s_acxyp),(5,3,s_bcxyp),vec![(3, 5)],vec![]),
            ((3,3,s_acxyp),(5,4,s_bxyp),vec![(3, 3)],vec![]),
            ((3,3,s_acxyp),(5,5,s_abxyp),vec![(3, 5)],vec![]),
            ((3,3,s_acxyp),(5,5,s_bxyp),vec![(3, 5)],vec![]), 
            ((3,4,s_acxyp),(5,1,s_bcxyp),vec![(3, 4)],vec![]),
            ((3,4,s_acxyp),(5,2,s_bcxyp),vec![(3, 4)],vec![]),
            ((3,4,s_acxyp),(5,3,s_bcxyp),vec![(3, 6)],vec![]),
            ((3,4,s_acxyp),(5,4,s_bxyp),vec![(3, 4)],vec![]),
            ((3,4,s_acxyp),(5,5,s_abxyp),vec![(3, 6)],vec![]),
            ((3,4,s_acxyp),(5,5,s_bxyp),vec![(3, 6)],vec![]),
            ((3,5,s_axyp),(5,1,s_bcxyp),vec![(3, 3)],vec![]),
            ((3,5,s_axyp),(5,1,s_cxy),vec![(3, 3)],vec![]),
            ((3,5,s_axyp),(5,2,s_bcxyp),vec![(3, 3)],vec![]),
            ((3,5,s_axyp),(5,3,s_bcxyp),vec![(3, 5)],vec![]),
            ((3,5,s_axyp),(5,4,s_bxyp),vec![(3, 3)],vec![]),
            ((3,5,s_axyp),(5,5,s_bxyp),vec![(3, 5)],vec![]), 
            ((3,6,s_axyp),(5,1,s_bcxyp),vec![(3, 4)],vec![]),
            ((3,6,s_axyp),(5,1,s_cxy),vec![(3, 4)],vec![]),
            ((3,6,s_axyp),(5,2,s_bcxyp),vec![(3, 4)],vec![]),
            ((3,6,s_axyp),(5,3,s_bcxyp),vec![(3, 6)],vec![]),
            ((3,6,s_axyp),(5,4,s_bxyp),vec![(3, 4)],vec![]),
            ((3,6,s_axyp),(5,5,s_bxyp),vec![(3, 6)],vec![]),
            ((3,7,s_abxyp),(5,1,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((3,7,s_axyp),(5,1,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((3,7,s_abxyp),(5,1,s_cxy),vec![(3, 3), (3, 4)],vec![]),
            ((3,7,s_abxyp),(5,1,s_acxyp),vec![(3, 5),(3, 6)],vec![]),
            ((3,7,s_axyp),(5,2,s_bcxyp),vec![(3, 4),(3, 3)],vec![]),
            ((3,7,s_abxyp),(5,2,s_acxyp),vec![(5, 3)],vec!["k_2 == d-x_03"]),
            ((3,7,s_abxyp),(5,2,s_bcxyp),vec![(3, 3), (3, 4)],vec![]),
            ((3,7,s_abxyp),(5,3,s_bcxyp),vec![(3, 5), (3, 6)],vec![]),
            ((3,7,s_axyp),(5,3,s_bcxyp),vec![(3, 7)],vec![]),
            ((3,7,s_abxyp),(5,4,s_acxyp),vec![(3, 5),(3, 6)],vec![]), 
            ((3,7,s_axyp),(5,4,s_bxyp),vec![(3, 3), (3, 4)],vec![]),
            ((3,7,s_axyp),(5,5,s_bxyp),vec![(3, 7)],vec![]),
            ((3,1,s_cx),(6,3,s_xy),vec![(3, 3)],vec![]),
            ((3,1,s_cx),(6,5,s_xyp),vec![(3, 3)],vec![]),
            ((3,1,s_cx),(6,7,s_abxyp),vec![(3, 3)],vec![]),
            ((3,1,s_acxyp),(6,7,s_abxyp),vec![(6, 3)],vec!["k_2 == d+d"]), 
            ((3,2,s_cx),(6,3,s_xy),vec![(3, 4)],vec![]),
            ((3,2,s_cx),(6,4,s_xy),vec![(3, 4)],vec![]),
            ((3,2,s_cx),(6,5,s_xyp),vec![(3, 4)],vec![]),
            ((3,2,s_cx),(6,6,s_xyp),vec![(3, 4)],vec![]),
            ((3,2,s_cx),(6,7,s_abxyp),vec![(3, 4)],vec![]),
            ((3,2,s_acxyp),(6,7,s_abxyp),vec![(6, 4)],vec!["k_2 == 1+1"]), 
            ((3,3,s_acxyp),(6,7,s_abxyp),vec![(6, 5)],vec!["k_2 == d+d"]),
            ((3,5,s_axyp),(6,1,s_cxy),vec![(6, 3), (3, 3)],vec!["k_2 == x_10"]), 
            ((3,5,s_axyp),(6,3,s_cxyp),vec![(6, 5)],vec!["k_2 == d+d"]),
            ((3,6,s_axyp),(6,1,s_cxy),vec![(6, 3),(3, 4)],vec!["k_2 == x_10"]), 
            ((3,6,s_axyp),(6,2,s_cxy),vec![(6, 4),(3, 4)],vec!["k_2 == 1+1"]),
            ((3,6,s_axyp),(6,3,s_cxyp),vec![(6, 5)],vec!["k_2 == d+1"]),
            ((3,6,s_axyp),(6,4,s_cxyp),vec![(6, 6), (3, 4)],vec!["k_2 == x_10-x_01"]),
            ((3,7,s_abxyp),(6,1,s_cxy),vec![(6, 3), (3, 3), (3, 4)],vec!["k_2 == d+x_02"]), 
            ((3,7,s_abxyp),(6,2,s_cxy),vec![(6, 4), (3, 4)],vec!["k_2 == 1+1"]),
            ((3,7,s_abxyp),(6,3,s_cxyp),vec![(6, 5)],vec!["k_2 == d+1"]),
            ((3,7,s_abxyp),(6,4,s_cxyp),vec![(6, 6), (3, 4)],vec!["k_2 == k_1"]),
            ((3,3,s_x),(7,1,s_c),vec![(3, 1)],vec![]),
            ((3,4,s_x),(7,1,s_c),vec![(3, 2)],vec![]),
            ((3,5,s_axyp),(7,1,s_c),vec![(3, 1)],vec![]),
            ((3,6,s_axyp),(7,1,s_c),vec![(3, 2)],vec![]),
            ((3,7,s_abxyp),(7,1,s_c),vec![(3, 1), (3, 2)],vec![]),
            ((5,1,s_cxy),(5,3,s_axyp),vec![(5, 2)],vec!["k_2 == k_0"]),
            ((5,1,s_cxy),(5,4,s_bxyp),vec![(5, 2)],vec!["k_2 == k_0"]),
            ((5,1,s_cxy),(5,5,s_abxyp),vec![(5, 2)],vec!["k_2 == k_0"]),
            ((5,3,s_bcxyp),(5,5,s_abxyp),vec![(5, 5),(3,5),(4,6)],vec!["k_2 == x_11"]),
            ((5,4,s_acxyp),(5,5,s_abxyp),vec![(5, 5),(3,5),(4,6)],vec!["k_2 == x_11"]),
            ((5,1,s_cxy),(6,5,s_xyp),vec![(5, 2)],vec!["k_2 == k_0"]), 
            ((5,1,s_cxy),(6,6,s_xyp),vec![(3, 4)],vec![]), 
            ((5,1,s_acxyp),(6,7,s_abxyp),vec![(4,3),(4,4)],vec![]),
            ((5,1,s_cxy),(6,7,s_abxyp),vec![(5, 2)],vec!["k_2 == k_0"]),
            ((5,1,s_bcxyp),(6,7,s_abxyp),vec![(3,3),(3,4),(4,4)],vec![]),
            ((5,2,s_bcxyp),(6,7,s_abxyp),vec![(3,3),(3,4)],vec![]), 
            ((5,2,s_acxyp),(6,7,s_abxyp),vec![(3,4),(4,3),(4,4)],vec![]), 
            ((5,3,s_axyp),(6,1,s_cxy),vec![(5,1),(4,3),(4,4)],vec!["k_2 == k_0"]), 
            ((5,3,s_axyp),(6,2,s_cxy),vec![(5,1),(4,4)],vec!["k_2 == k_0"]), 
            ((5,3,s_axyp),(6,3,s_cxyp),vec![(6, 3)],vec!["k_2 == k_1"]), 
            ((5,3,s_axyp),(6,4,s_cxyp),vec![(4, 4)],vec![]),
            ((5,3,s_bcxyp),(6,7,s_abxyp),vec![(3,5),(3,6)],vec![]),
            ((5,4,s_bxyp),(6,1,s_cxy),vec![(5,1),(3,3),(3,4)],vec!["k_2 == k_0"]),
            ((5,4,s_bxyp),(6,2,s_cxy),vec![(5,1),(3,4)],vec!["k_2 == k_0"]),
            ((5,4,s_bxyp),(6,3,s_cxyp),vec![(6, 3)],vec!["k_2 == k_1"]),
            ((5,4,s_bxyp),(6,4,s_cxyp),vec![(3, 4)],vec![]),
            ((5,4,s_acxyp),(6,7,s_abxyp),vec![(4,5),(4,6)],vec![]),
            ((5,5,s_abxyp),(6,3,s_cxyp),vec![(6, 5)],vec!["k_2 == k_1"]),
            ((5,5,s_abxyp),(6,4,s_cxyp),vec![(6, 6),(3, 4)],vec!["k_2 == k_1"]),
            ((5,2,s_xy),(7,1,s_c),vec![(5, 1)],vec!["k_2 == k_0"]),
            ((5,3,s_axyp),(7,1,s_c),vec![(5, 1)],vec!["k_2 == k_0"]),
            ((5,4,s_bxyp),(7,1,s_c),vec![(5, 1)],vec!["k_2 == k_0"]),
            ((6,1,s_cxy),(6,5,s_xyp),vec![(6, 3)],vec!["k_2 == k_0"]),
            ((6,1,s_cxy),(6,6,s_xyp),vec![(6, 3)],vec!["k_2 == k_0"]), 
            ((6,1,s_cxy),(6,7,s_abxyp),vec![(6, 3)],vec!["k_2 == k_0"]),
            ((6,2,s_cxy),(6,5,s_xyp),vec![(6, 3)],vec!["k_2 == k_1"]),
            ((6,2,s_cxy),(6,6,s_xyp),vec![(6, 4)],vec!["k_2 == k_0"]),
            ((6,2,s_cxy),(6,7,s_abxyp),vec![(6, 4)],vec!["k_2 == k_0"]),
            ((6,3,s_cxyp),(6,7,s_abxyp),vec![(6, 5)],vec!["k_2 == k_0"]),
            ((6,3,s_xy),(7,1,s_c),vec![(6, 1)],vec!["k_2 == k_0"]),
            ((6,4,s_xy),(7,1,s_c),vec![(6, 2)],vec!["k_2 == k_0"]),
            ((6,5,s_xyp),(7,1,s_c),vec![(6, 1)],vec!["k_2 == k_0"]),
            ((6,6,s_xyp),(7,1,s_c),vec![(6, 2)],vec!["k_2 == k_0"]),
            ((5,1,s_bcxyp),(5,1,s_acxyp),vec![(5, 1)],vec!["k_2 == k_0+x_23+x_24"]),
            ((1,1,s_acx),(5,5,s_xy),vec![(5, 1),(3, 7)],vec!["k_2 == d-x_21-x_22"]),
            ((5,1,s_bcxyp),(5,3,s_axyp),vec![(5, 2)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,1,s_acxyp),(5,3,s_bcxyp),vec![(5, 3),(5, 3)],vec!["k_2 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2","k_3 == d"]),
            ((5,1,s_bcxyp),(5,4,s_acxyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,1,s_acxyp),(5,4,s_bxyp),vec![(5, 2),(5,2)],vec!["k_2 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2","k_3 == d"]),
            ((5,1,s_bcxyp),(5,5,s_axyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,1,s_bcxyp),(5,5,s_abxyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_bcxyp),(5,2,s_acxyp),vec![(5, 2)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_bcxyp),(5,3,s_axyp),vec![(5, 2)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_bcxyp),(5,4,s_acxyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_bcxyp),(5,5,s_axyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_bcxyp),(5,5,s_abxyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,4,s_bxyp),(5,4,s_acxyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,4,s_bxyp),(5,5,s_axyp),vec![(5, 4)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,2,s_acxyp),(5,2,s_bcxyp),vec![(5, 2),(5, 2)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,2,s_acxyp),(5,3,s_bcxyp),vec![(5, 3),(5, 3)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,2,s_acxyp),(5,4,s_bxyp),vec![(5, 2),(5, 2)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,2,s_acxyp),(5,5,s_bxyp),vec![(5, 3),(5, 3)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,3,s_bcxyp),(5,3,s_axyp),vec![(5, 3),(5, 3)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,3,s_axyp),(5,3,s_bcxyp),vec![(5, 3),(5, 3)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,4,s_acxyp),(5,4,s_bxyp),vec![(5, 4),(5, 4)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,1,s_acxyp),(5,5,s_bxyp),vec![(5, 3),(5, 3)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,1,s_bcxyp),(5,2,s_acxyp),vec![(5, 1)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,1,s_acxyp),(5,1,s_bcxyp),vec![(5, 1),(5,1)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,1,s_acxyp),(5,2,s_bcxyp),vec![(5, 2),(5,2)],vec!["k_2 == d","k_3 == x_23 + x_24 + x_32 + x_34 + x_42 + x_43 + x_44 - Δ + 3*d + 2"]),
            ((5,5,s_bxyp),(5,5,s_axyp),vec![(5, 5)],vec!["k_2 == k_0+x_23+x_24"]),
            ((5,5,s_axyp),(5,5,s_bxyp),vec![(5, 5)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,5,s_axyp),(5,5,s_bxyp),vec![(5, 5)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,3,s_axyp),(5,5,s_bxyp),vec![(5, 3)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,3,s_axyp),(5,4,s_bxyp),vec![(5, 2)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,1,s_acxyp),(5,5,s_abxyp),vec![(5, 3)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,2,s_acxyp),(5,5,s_abxyp),vec![(5, 3)],vec!["k_2 == k_0+x_32+x_34"]),
            ((5,4,s_acxyp),(5,5,s_bxyp),vec![(5, 5)],vec!["k_2 == k_1+x_32+x_42"]),
            ((5,3,s_bcxyp),(5,5,s_axyp),vec![(5, 5)],vec!["k_2 == k_1+x_23+x_43"]),
            ((3,4,s_acxyp),(4,4,s_bcxyp),vec![(6, 3), (6, 4)],vec!["k_2 == d+1-x_01","k_3 == d+1-x_01"]),
            ((3,4,s_acxyp),(4,6,s_bxyp),vec![(6, 5), (6, 6)],vec!["k_2 == x_00","k_3 == x_00"]),
            ((3,4,s_acxyp),(4,7,s_bxyp),vec![(6, 5), (6, 6)],vec!["k_2 == x_00","k_3 == x_00"]),
            ((3,4,s_acxyp),(4,7,s_abxyp),vec![(6, 5), (6, 6)],vec!["k_2 == x_00","k_3 == x_00"]),
            ((3,2,s_cx),(5,5,s_abxyp),vec![(5, 1), (3, 4)],vec!["k_2 == d-x_21-x_22"]),
            ((1,1,s_acx),(5,3,s_xy),vec![(5, 1), (3, 3), (3, 6)],vec!["k_2 == k_1"]),
            ((3,1,s_acxyp),(4,7,s_bxyp),vec![(6, 5), (4, 3)],vec!["k_2 == 2*d"]),
            ((3,4,s_acxyp),(6,7,s_abxyp),vec![(6, 5), (6, 6),(3,6)],vec!["k_2 == k_1","k_3 == k_1"]),
            ((6,7,s_abxyp),(7,1,s_c),vec![(6, 1), (6, 2)],vec!["k_2 == k_0","k_3 == k_0"]),
            ((3,1,s_acxyp),(5,5,s_abxyp),vec![(5,1),(3,5)],vec!["k_2 == k_1"]),
            ((1,1,s_acx),(5,5,s_bxyp),vec![(5, 1), (3, 7)],vec!["k_2 == d-x_21-x_22"]), 
            ((1,2,s_acx),(6,3,s_cxyp),vec![(3, 3), (3, 4)],vec![]),
            ((3,1,s_acxyp),(5,4,s_bxyp),vec![(5, 1),(3, 3)],vec!["k_2 == x_11"]),
            ((3,2,s_acxyp),(5,4,s_bxyp),vec![(5, 1),(3, 4)],vec!["k_2 == k_1"]),
            ((3,5,s_axyp),(6,1,s_cxyp),vec![(6, 3),(3, 3)],vec!["k_2 == x_10"]), 
            ((3,6,s_axyp),(6,1,s_cxyp),vec![(6, 3),(3, 4)],vec!["k_2 == x_10"]),
            ((3,6,s_axyp),(6,2,s_cxyp),vec![(6, 4),(3, 4)],vec!["k_2 == k_1"]), 
            ((3,7,s_abxyp),(6,1,s_cxyp),vec![(6, 3),(3, 3), (3, 4)],vec!["k_2 == x_01"]), 
            ((3,7,s_abxyp),(6,2,s_cxyp),vec![(6, 4),(3, 4)],vec!["k_2 == k_1"]),
            ((6,1,s_cxyp),(6,7,s_abxyp),vec![(6, 3)],vec!["k_2 == d+1"]),
            ((6,2,s_cxyp),(6,7,s_abxyp),vec![(6, 4)],vec!["k_2 == 1+1"]),
            ((3,1,s_acxyp),(5,5,s_bxyp),vec![(5,1),(3,3)],vec!["k_2 == x_11"]),
            ((5,3,s_axyp),(6,1,s_cxyp),vec![(5,1),(4,3),(4,4)],vec!["k_2 == k_0"]), 
            ((5,3,s_axyp),(6,2,s_cxyp),vec![(5,1),(4,4)],vec!["k_2 == k_0"]),
            ((5,4,s_bxyp),(6,1,s_cxyp),vec![(5,1),(3,3),(3,4)],vec!["k_2 == k_0"]), 
            ((5,4,s_bxyp),(6,2,s_cxyp),vec![(5,1),(3,4)],vec!["k_2 == k_0"]),
            ((1,1,s_acx),(6,4,s_cxyp),vec![(3, 2)],vec![]),
            ((1,1,s_acx),(6,3,s_cxyp),vec![(3, 2),(3, 3)],vec![]),
            ((3,6,s_axyp),(4,6,s_bxyp),vec![(6, 6), (6, 7)],vec!["k_2 == 1+1","k_3 == x_00"]),
            ((1,1,s_acx),(5,5,s_abxyp),vec![(5, 1), (1, 3), (3, 3), (3, 4)],vec!["k_2 == d-x_21-x_22"]),
            ((6,4,s_cxyp),(6,7,s_abxyp),vec![(6, 6),(6, 3)],vec!["k_2 == 3*d + 4 - Δ", "k_3 == d+1"]),
            ((5,5,s_abxyp),(7,1,s_c),vec![(5, 1),(5,1)],vec!["k_2 == d + k_0 - x_40","k_3 == d"]),
            ((1,1,s_cx),(4,7,s_abxyp),vec![(5, 1),(5, 1), (1, 2)],vec!["k_2 == 3*d + 2 - Δ + x_12 + x_22 + x_21","k_3 == d"]),
            ((1,1,s_cx),(5,5,s_abxyp),vec![(5, 1),(5, 1), (1, 2)],vec!["k_2 == 3*d + 2 - Δ + x_14 + x_24 + x_23","k_3 == d"]),
            ((5,3,s_bcxyp),(5,4,s_acxyp),vec![(5, 5),(5, 5)],vec!["k_2 == 2*d + 1 - Δ + x_23 + x_32 + x_04 + x_14 + x_24 + x_34 + x_44 + x_43 + x_42 + x_41 + x_40","k_3 == d"]),
            ((3,2,s_acxyp),(5,5,s_bxyp),vec![(5,1),(5,1),(3,7)],vec!["k_2 == 3*d + 2 - Δ + x_14 + x_24 + x_23","k_3 == d"]), 
            ((3,2,s_acxyp),(5,5,s_abxyp),vec![(5,1),(5,1),(3,6)],vec!["k_2 == 3*d + 2 - Δ + x_14 + x_24 + x_23","k_3 == d"]), 
            ((5,5,s_abxyp),(6,1,s_cxy),vec![(6,3),(5,1),(5,1)],vec!["k_2 == d + 1", "k_3 ==  3*d + 2 - Δ +  x_41 + x_42 + x_43 + x_33 + x_23 + x_13 + x_03", "k_4 == d"]), 
            ((5,5,s_abxyp),(6,1,s_cxyp),vec![(6,5),(5,1),(5,1)],vec!["k_2 == d + 1", "k_3 ==  3*d + 2 - Δ +  x_41 + x_42 + x_43 + x_33 + x_23 + x_13 + x_03", "k_4 == d"]), 
            ((5,5,s_abxyp),(6,2,s_cxy),vec![(6,4),(5,1),(5,1)],vec!["k_2 == 3*d + 4 - Δ", "k_3 ==  3*d + 2 - Δ +  x_41 + x_42", "k_4 == d"]),
            ((5,5,s_abxyp),(6,2,s_cxyp),vec![(6,4),(5,1),(5,1)],vec!["k_2 == 3*d + 4 - Δ", "k_3 ==  3*d + 2 - Δ +  x_41 + x_42", "k_4 == d"]),
        ];


    for (case_num,case) in lines.iter().enumerate() {
        println!("Case {}",case_num+1);
        for line in case.iter() {
            println!("{}",line);
        }
        println!();
    }

    use std::io::{self, BufRead};
    let stdin = io::stdin();

    println!("What do you want to do? (write 1 or 2 and press enter)");
    println!("1) Test all cases (takes roughly 5 minutes, requires sage to be installed)");
    println!("2) Choose a pair of lines and see the generated inequalities\n");

    let line = stdin.lock().lines().next().unwrap().unwrap();
    if line.parse::<isize>().unwrap() == 1 {
        println!("\nTesting all cases! This may take a while...");
        test_all(&lines, &additional, &mapping);
        println!("Done! Everything appears to be correct.");
    } else if line.parse::<isize>().unwrap() == 2 {
        println!("\nFrom which case do you want the first line? (write a number from 1 to 7 and press enter)\n");
        let c1 = stdin.lock().lines().next().unwrap().unwrap().parse::<isize>().unwrap();
        println!("\nPlease choose a line among the following ones: (write a number from 1 to {} and press enter)", lines[c1 as usize-1].len());
        for (i,line) in lines[c1 as usize-1].iter().enumerate() {
            println!("{}) {}",i+1,line);
        }
        println!();
        let s1 = stdin.lock().lines().next().unwrap().unwrap().parse::<isize>().unwrap();
        println!("\nFrom which case do you want the second line? (write a number from 1 to 7 and press enter)\n");
        let c2 = stdin.lock().lines().next().unwrap().unwrap().parse::<isize>().unwrap();
        println!("\nPlease choose a line among the following ones: (write a number from 1 to {} and press enter)", lines[c2 as usize-1].len());
        for (i,line) in lines[c2 as usize-1].iter().enumerate() {
            println!("{}) {}",i+1,line);
        }
        println!();
        let s2 = stdin.lock().lines().next().unwrap().unwrap().parse::<isize>().unwrap();
        println!("\nYou chose to combine {}.{} with {}.{}, that is, the following two lines:", c1,s1,c2,s2);
        let l1 = &lines[c1 as usize - 1][s1 as usize - 1];
        let l2 = &lines[c2 as usize - 1][s2 as usize - 1];
        println!("{}\n{}\n",l1,l2);

        if c1 == c2 && s2 < s1 {
            println!("This case is symmetric to {}.{} with {}.{}",c1,s2,c2,s1);
        } else if c1 == 2 {
            println!("The first line is of group 2: this case is symmetric to the case in which group 1 is considered");
        } else if c1 == 4 {
            println!("The first line is of group 4: this case is symmetric to the case in which group 3 is considered");
        } else if c1 == 1 && c2 == 2 && s1 > s2 {
            println!("This case is symmetric to {}.{} with {}.{}",c1,s2,c2,s1);
        } else if c1 == 3 && c2 == 4 && s1 > s2 {
            println!("This case is symmetric to {}.{} with {}.{}",c1,s2,c2,s1);
        } else {
            let ints = good_intersections(l1, l2);
            if ints.is_empty() {
                println!("\nFrom the observations in the paper, in this case, no Sup are worth being considered.");
            } else {
                println!("\nFrom the observations in the paper, only the following Sup are worth being considered:");
                let mut i = 1;
                let mut h = HashMap::new();
                for (int,cases) in ints {
                    for (p1,p2) in cases {
                        println!("{}) Sup({},{}) = {}",i,DisplaySetL(&l1.0[p1].0),DisplaySetL(&l2.0[p2].0), DisplaySetL(&int));
                        h.insert(i,(p1,p2));
                        i += 1;
                    }
                }
                println!("\nPlease choose which one you want to consider (write a number from 1 to {} and press enter)\n",i-1);
                let n = stdin.lock().lines().next().unwrap().unwrap().parse::<isize>().unwrap();

                println!("\nIn the following, you will find written the input that is given to sage to test unsolvability.");
                println!("Please note that, if, while providing the input to sage, it fails with the message\n  'argument must be a linear function or constraint, got False',\nit means that one of the generated constrains already evaluated to False, and hence the system of inequalities is unsolvable.\nOtherwise, non-solvability is given by the error\n  'The problem or its dual has been proven infeasible'.");
                println!("Press enter to see the inputs.");
                stdin.lock().lines().next().unwrap().unwrap();

                let (p1,p2) = h[&n];

                let mapping: HashMap<_, _> = mapping
                    .iter()
                    .map(|(line1, line2, target, freevars)| {
                        (
                            (
                                (line1.0, line1.1, line1.2.clone()),
                                (line2.0, line2.1, line2.2.clone()),
                            ),
                            (target, freevars),
                        )
                    })
                    .collect();
                let mut solver = Solver::init();

                test_combination((c1-1) as usize,(s1-1) as usize,(c2-1) as usize,(s2-1) as usize,l1,l2,p1,p2,&mapping,&additional,&mut solver, &lines,true);
            }
        }
    } else {
        println!("\nSorry, you chose an invalid option.");
    }


}

