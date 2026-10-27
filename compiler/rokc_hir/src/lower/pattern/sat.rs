//! Bounded SAT for Boolean products. Earlier arms are negated predicates;
//! the queried arm is an assumption. Or-patterns use Tseitin variables,
//! so nested alternatives do not expand into a product of rows.

use super::{Ctor, HirTy, Pat, PrimTy};

const MAX_VARS: usize = 512;
const MAX_LITERALS: usize = 32_768;
const MAX_WORK: usize = 200_000;

/// Variable index in the high bits, required Boolean value in the low bit.
#[derive(Clone, Copy)]
struct Lit(usize);

impl Lit {
    const fn not(self) -> Self {
        Self(self.0 ^ 1)
    }

    const fn var(self) -> usize {
        self.0 / 2
    }

    const fn value(self) -> u8 {
        if self.0 & 1 == 0 { 1 } else { 2 }
    }
}

enum Domain {
    Bool(usize),
    Tuple(Vec<Self>),
}

impl Domain {
    fn new(ty: &HirTy, vars: &mut usize) -> Option<Self> {
        match ty {
            HirTy::Prim(PrimTy::Bool) if *vars < MAX_VARS => {
                let var = *vars;
                *vars += 1;
                Some(Self::Bool(var))
            }
            HirTy::Tuple(fields) if fields.len() <= MAX_VARS => fields
                .iter()
                .map(|t| Self::new(t, vars))
                .collect::<Option<Vec<_>>>()
                .map(Self::Tuple),
            _ => None,
        }
    }
}

enum Term {
    Constant(bool),
    Literal(Lit),
}

struct Cnf {
    clauses: Vec<Vec<Lit>>,
    vars: usize,
    literals: usize,
}

impl Cnf {
    fn clause(&mut self, lits: Vec<Lit>) -> Option<()> {
        // Empty clauses also consume the budget.
        let size = lits.len().max(1);
        if size > MAX_LITERALS - self.literals {
            return None;
        }
        self.literals += size;
        self.clauses.push(lits);
        Some(())
    }

    fn junction(&mut self, terms: Vec<Term>, all: bool) -> Option<Term> {
        let mut lits = Vec::new();
        for term in terms {
            match term {
                Term::Constant(b) if b != all => return Some(Term::Constant(b)),
                Term::Constant(_) => {}
                Term::Literal(lit) => lits.push(lit),
            }
        }
        lits.sort_unstable_by_key(|l| l.0);
        lits.dedup_by_key(|l| l.0);
        if lits.windows(2).any(|ls| ls[0].0 ^ 1 == ls[1].0) {
            return Some(Term::Constant(!all));
        }
        match lits.as_slice() {
            [] => Some(Term::Constant(all)),
            [lit] => Some(Term::Literal(*lit)),
            _ if self.vars >= MAX_VARS => None,
            _ => {
                let result = Lit(self.vars * 2);
                self.vars += 1;
                for &lit in &lits {
                    self.clause(if all {
                        vec![result.not(), lit]
                    } else {
                        vec![result, lit.not()]
                    })?;
                }
                let mut last = Vec::with_capacity(lits.len() + 1);
                last.push(if all { result } else { result.not() });
                last.extend(lits.into_iter().map(|l| if all { l.not() } else { l }));
                self.clause(last)?;
                Some(Term::Literal(result))
            }
        }
    }

    /// A conjunction of predicates; tuples flatten without auxiliary vars.
    fn conjuncts(&mut self, p: &Pat, domain: &Domain, out: &mut Vec<Term>) -> Option<()> {
        match (p, domain) {
            (Pat::Wild, _) => {}
            (Pat::C(Ctor::Bool(b), args), Domain::Bool(var)) if args.is_empty() => {
                out.push(Term::Literal(Lit(var * 2 + usize::from(*b))));
            }
            (Pat::C(Ctor::Single, args), Domain::Tuple(fields)) if args.len() == fields.len() => {
                for (p, d) in args.iter().zip(fields) {
                    self.conjuncts(p, d, out)?;
                }
            }
            (Pat::Or(alts), _) if alts.len() <= MAX_LITERALS => {
                let mut terms = Vec::new();
                for p in alts {
                    let mut parts = Vec::new();
                    self.conjuncts(p, domain, &mut parts)?;
                    terms.push(self.junction(parts, true)?);
                }
                out.push(self.junction(terms, false)?);
            }
            _ => return None,
        }
        Some(())
    }
}

pub(super) struct Checker {
    domain: Domain,
    cnf: Cnf,
    bits: usize,
}

impl Checker {
    pub(super) fn new(ty: &HirTy) -> Option<Self> {
        let mut bits = 0;
        let domain = Domain::new(ty, &mut bits)?;
        Some(Self {
            domain,
            cnf: Cnf {
                clauses: Vec::new(),
                vars: bits,
                literals: 0,
            },
            bits,
        })
    }

    pub(super) const fn bits(&self) -> usize {
        self.bits
    }

    /// Exclude an unguarded arm from later queries.
    pub(super) fn exclude(&mut self, p: &Pat) -> Option<()> {
        if let Pat::Or(alts) = p {
            for alt in alts {
                self.exclude(alt)?;
            }
            return Some(());
        }
        let mut terms = Vec::new();
        self.cnf.conjuncts(p, &self.domain, &mut terms)?;
        let mut clause = Vec::new();
        for term in terms {
            match term {
                Term::Constant(false) => return Some(()),
                Term::Constant(true) => {}
                Term::Literal(lit) => clause.push(lit.not()),
            }
        }
        self.cnf.clause(clause)
    }

    /// `None` means unsupported input or exhausted work, never UNSAT.
    pub(super) fn useful(&mut self, p: &Pat) -> Option<bool> {
        #[cfg(test)]
        if super::tests::empty_budget() {
            return self.useful_with_budget(p, 0);
        }
        self.useful_with_budget(p, MAX_WORK)
    }

    fn useful_with_budget(&mut self, p: &Pat, work: usize) -> Option<bool> {
        let mark = (self.cnf.clauses.len(), self.cnf.vars, self.cnf.literals);
        let result = self.query(p, work);
        self.cnf.clauses.truncate(mark.0);
        self.cnf.vars = mark.1;
        self.cnf.literals = mark.2;
        result
    }

    fn query(&mut self, p: &Pat, work: usize) -> Option<bool> {
        let mut terms = Vec::new();
        self.cnf.conjuncts(p, &self.domain, &mut terms)?;
        let mut search = Search {
            clauses: &self.cnf.clauses,
            values: vec![0; self.cnf.vars],
            trail: Vec::new(),
            work,
        };
        for term in terms {
            match term {
                Term::Constant(false) => return Some(false),
                Term::Literal(lit) if !search.assign(lit) => return Some(false),
                Term::Literal(_) | Term::Constant(true) => {}
            }
        }
        search.solve()
    }
}

struct Search<'a> {
    clauses: &'a [Vec<Lit>],
    /// 0 unassigned, 1 false, 2 true.
    values: Vec<u8>,
    trail: Vec<usize>,
    work: usize,
}

enum Propagation {
    Conflict,
    Solved,
    Branch(Lit),
}

impl Search<'_> {
    fn assign(&mut self, lit: Lit) -> bool {
        let value = &mut self.values[lit.var()];
        if *value == 0 {
            *value = lit.value();
            self.trail.push(lit.var());
        }
        *value == lit.value()
    }

    fn propagate(&mut self) -> Option<Propagation> {
        loop {
            let mut changed = false;
            let mut branch: Option<(usize, Lit)> = None;
            for clause in self.clauses {
                self.work = self.work.checked_sub(1)?;
                let (mut satisfied, mut unset, mut candidate) = (false, 0, Lit(0));
                for &lit in clause {
                    self.work = self.work.checked_sub(1)?;
                    let value = *self.values.get(lit.var())?;
                    match value {
                        0 => {
                            unset += 1;
                            candidate = lit;
                        }
                        value if value == lit.value() => {
                            satisfied = true;
                            break;
                        }
                        _ => {}
                    }
                }
                if satisfied {
                    continue;
                }
                match unset {
                    0 => return Some(Propagation::Conflict),
                    1 => {
                        if !self.assign(candidate) {
                            return Some(Propagation::Conflict);
                        }
                        changed = true;
                    }
                    _ if branch.is_none_or(|(n, _)| unset < n) => branch = Some((unset, candidate)),
                    _ => {}
                }
            }
            if !changed {
                return Some(
                    branch.map_or(Propagation::Solved, |(_, lit)| Propagation::Branch(lit)),
                );
            }
        }
    }

    fn solve(&mut self) -> Option<bool> {
        match self.propagate()? {
            Propagation::Conflict => Some(false),
            Propagation::Solved => Some(true),
            Propagation::Branch(lit) => {
                let mark = self.trail.len();
                for lit in [lit, lit.not()] {
                    self.assign(lit);
                    if self.solve()? {
                        return Some(true);
                    }
                    for var in self.trail.drain(mark..) {
                        self.values[var] = 0;
                    }
                }
                Some(false)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn work_limit_restores_temporary_query_clauses() {
        let boolean = |b| Pat::C(Ctor::Bool(b), Vec::new());
        let ty = HirTy::Tuple(vec![HirTy::Prim(PrimTy::Bool); 2]);
        let mut checker = Checker::new(&ty).unwrap();
        let p = Pat::Or(vec![
            Pat::C(Ctor::Single, vec![boolean(true), boolean(false)]),
            Pat::C(Ctor::Single, vec![boolean(false), boolean(true)]),
        ]);
        assert_eq!(checker.useful_with_budget(&p, 0), None);
        assert_eq!(checker.cnf.vars, 2);
        assert!(checker.cnf.clauses.is_empty());
        assert_eq!(checker.cnf.literals, 0);
        assert_eq!(checker.useful(&p), Some(true));
        checker.exclude(&p).unwrap();
        assert_eq!(checker.useful(&p), Some(false));
    }
}
