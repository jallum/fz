## A Good Plan
- A _good_ plan **requires** a goal, a signal and a strategy. 
- A _good_ plan starts with a goal, and works backwards to the current state: the answer to "what do i need to do _this_?" at each point will inform the changes that must be made at each step -- those steps, when organized into a DAG, will then lead inexorably to the goal. Hard things are tractable if broken into steps. This pattern is fractal. A difficult step can be broken down further. If two steps cannot be performed in an atomic fashion, then we have learned that they are _one_ step.
- A _good_ plan is simple, elegant and holistic -- no quick-fixes, shims, shams, shortcuts.
- A _good_ plan contains all of the necessary references, details, strategies and tactics -- it is grounded in fact because it is the fruit of research and due-diligence. 
- A _good_ plan cares as much about what we _remove_ as what we add or change. What goes away? What _could_ go away?
- A _good_ plan leaves guideposts for the future -- what documentation needs to be updated? What topics help us in the future?

## Work Rules
- Don't commit work you're not proud of.
- Understand each task thoroughly before undertaking it. Do not guess. No hidden surprises.
- Elegance, simplicity and "correct by construction" are what we push for.
- Research material can be found in the .agent/docs.md (agent facing) and in the guides (user facing).
- TDD is the law. Prove things work the way you say they do. Tests must pass.
- Deferrals and omissions **REQUIRE** prior authorization.
- Warnings are _errors_ if it's something we control.
- Documentation must be updated along with code. Before committing, consider the agent docs and guides that must be updated. All information presented must be provable fact, grounded in the code itself.
- Refrain from even attempting to estimate time to accomplish work -- that is my concern.

## Tickets and Plans
- Plans decompose into bw tickets (`bw --help`) that are executed in dependency order
- One ticket == one commit, one close.
- Ready tickets are surfaced as their dependencies are closed.
- Tickets are persistent memory beyond context and free you from having to worry about context usage.
