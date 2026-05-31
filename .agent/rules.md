## A _Good_ Plan...
- **Requires** a goal, a signal and a strategy. 
- Starts with a goal, and works backwards to the current state: the answer to "what do i need to do _this_?" at each point will inform the changes that must be made at each step -- those steps, when organized into a DAG, will then lead inexorably to the goal. Hard things are tractable if broken into steps. This pattern is fractal. A difficult step can be broken down further. If two steps cannot be performed in an atomic fashion, then we have learned that they are _one_ step.
- Is simple, elegant and holistic -- no quick-fixes, shims, shams, shortcuts.
- Contains all of the necessary references, details, strategies and tactics -- it is grounded in fact because it is the fruit of research and due-diligence. 
- Cares as much about what we _remove_ as what we add or change. What goes away? What _could_ go away?
- Leaves guideposts for the future -- what documentation needs to be updated? What topics help us in the future?
- Considers adding measurements/metrics/telemetry to provide better signal.
- Tracks and *removes* the temporary fixtures, scaffolding and affordances put in place during construction.

## Work Rules
- Don't commit until you're proud of the work.
- Understand each task thoroughly before undertaking it. Do not guess; research and verify No hidden surprises.
- Elegance, simplicity and "correct by construction" are what we push for.
- Research material can be found in the .agent/docs.md (agent facing) and in the guides (user facing).
- TDD is the law. Prove things work the way you say they do. Tests must pass.
- Deferrals and omissions **REQUIRE** prior authorization.
- Warnings are _errors_ if it's something we control.
- Documentation must be updated along with code. Before committing, consider the agent docs and guides that must be updated. All information presented must be provable fact, grounded in the code itself.
- Refrain from even attempting to estimate time to accomplish work -- that is my concern.
- If affordances/scaffolding are added on the fly, that's fine, but tickets to remove / collapse them *must be added* -- that's the price.
- Find a _problem_? See something, say something. New issues deserve new tickets -- If they block us, we deal with them _first_. If they _don't_, then they go at the end of the epic so we don't lose them (like we would if we just dropped a comment in a place we'll never look again.)

## Tickets and Plans
- Plans decompose into bw tickets (`bw --help`) that are executed in dependency order
- One ticket == one commit, one close.
- Ready tickets are surfaced as their dependencies are closed.
- Tickets are persistent memory beyond context and free you from having to worry about context usage.

# Pull Requests
- Should have titles "<ticket>: ..."
- Are produced after examining the diff against the branch-root.
- Have descriptions that explain in eli5 _style_ (no need to _say it) why we're making the change, what we've changed, and how it works -- with examples.

## Best Practices
- Data-model -> up, so that the problem is correct-by-construction.
- Prefer short functions with crisp names over comments.
- Modules should have a coherent focus.
- Deeply nested code is a smell.
- Data should be immutable where possible (esp. after construction).
- Code should live in the right modules, modules should live in the right places.
- Tests should observe telemetry wherever possible. Not available? Consider judiciously adding (or extending) events.
- Tests should clearly state the _intent_ that they're capturing, and not just mechanically assert it.