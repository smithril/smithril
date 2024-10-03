use crate::generalized::Context;
use crate::generalized::Interrupter;
use crate::generalized::Options;
use crate::term;
use crate::term::Term;
use std::hash::Hash;
use std::sync::Arc;
use std::thread::sleep;
use std::time::Duration;

use crate::generalized::Factory;
use crate::generalized::Solver;
use crate::generalized::SolverResult;
use std::collections::HashSet;

#[derive(PartialEq, Eq, Hash)]
pub struct DummyContext {}

impl Context for DummyContext {}

impl DummyContext {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for DummyContext {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default)]
pub struct DummyFactory {
    contexts: HashSet<Arc<DummyContext>>,
    solvers: HashSet<Arc<DummySolver>>,
}

impl Factory<DummyContext, DummySolver, DummyInterrupter> for DummyFactory {
    fn new_context(&mut self) -> Arc<DummyContext> {
        let context = Arc::new(DummyContext::default());
        self.contexts.insert(context.clone());
        context
    }

    fn delete_context(&mut self, context: Arc<DummyContext>) {
        self.contexts.remove(&context);
        assert_eq!(Arc::strong_count(&context), 1);
    }

    fn delete_solver(&mut self, solver: Arc<DummySolver>) {
        self.solvers.remove(&solver);
        assert_eq!(Arc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, _solver: Arc<DummySolver>) -> DummyInterrupter {
        DummyInterrupter {}
    }

    fn new_solver(&mut self, context: Arc<DummyContext>, options: &Options) -> Arc<DummySolver> {
        let solver = Arc::new(DummySolver::new(context, options));
        self.solvers.insert(solver.clone());
        solver
    }
}

pub struct DummySolver {
    pub context: Arc<DummyContext>,
}

impl DummySolver {
    pub fn new(context: Arc<DummyContext>, _options: &Options) -> Self {
        Self { context }
    }
}

impl PartialEq for DummySolver {
    fn eq(&self, other: &Self) -> bool {
        self.context.eq(&other.context)
    }
}

impl Eq for DummySolver {}

impl Hash for DummySolver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state);
    }
}

pub struct DummyInterrupter {}

impl Interrupter for DummyInterrupter {
    fn interrupt(&self) {}
}

impl Solver for DummySolver {
    fn unsat_core(&self) -> Vec<Term> {
        Vec::new()
    }

    fn assert(&self, _term: &term::Term) {}

    fn check_sat(&self) -> SolverResult {
        sleep(Duration::from_secs(100));
        SolverResult::Unknown
    }

    fn eval(&self, _term: &Term) -> Option<Term> {
        None
    }

    fn reset(&self) {}

    fn push(&self) {}

    fn pop(&self) {}
}
