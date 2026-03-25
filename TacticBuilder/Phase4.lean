import Lean
open Lean Elab Tactic Meta

/-!
# Phase 4: Inspecting the goal and the local context

Lean tactics run in monads (`TacticM`, `MetaM`) that carry the *current goals* and
*metavariable state*. Two things often feel difficult at first:

1. **The goal is not a string.** It is an `MVarId` (a metavariable to assign), and the
   proposition you see in the info view is the **type** of that metavariable, as an `Expr`
   (an abstract syntax tree). You inspect it with predicates like `isConstOf` / `isAppOf`.

2. **Hypotheses live in a separate structure**, the **local context** (`LocalContext`).
   You get it with `getLCtx`, but only after you switch to the right “scope” with
   `goal.withContext` or `withMainContext`, so the context matches the goal you are looking at.

This file builds the same ideas in small steps: **look → classify → act**, first for the
goal type, then for hypotheses.

Try in the editor: place the cursor on an `example` and watch the **Messages** / info panel
when a tactic calls `logInfo`.
-/

-- -----------------------------------------------------------------------
-- Step 1 — “Which metavariable?” and “What is its type?”
-- -----------------------------------------------------------------------
/-
  * `getMainGoal` — returns the **first unsolved** goal as `MVarId`.
  * `goal.getType` — type of that metavariable as stored (`MetaM`); good for structural checks.
  * `getMainTarget` — `instantiateMVars` on that type; often nicer when the type still had
    metavariables you want filled in for display or comparison.

  For many small tactics you can use either `goal.getType` or `getMainTarget`; pick one style
  and stay consistent. This file uses both so you see them in the wild.
-/

/-- Print the pretty-printed main goal type (uses `getMainTarget`). -/
elab "trace_goal_pp" : tactic => do
  withMainContext do
    let target ← getMainTarget
    logInfo m!"Main goal (pretty): ⊢ {← ppExpr target}"

example (n : Nat) : n = n := by
  trace_goal_pp
  rfl

/-- Compare `MVarId.getType` vs `getMainTarget` on the same goal (usually similar text). -/
elab "compare_goal_type_reads" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let viaGetType ← g.getType
    let viaMainTarget ← getMainTarget
    logInfo m!"from `g.getType`:      {← ppExpr viaGetType}"
    logInfo m!"from `getMainTarget`: {← ppExpr viaMainTarget}"

example : True := by
  compare_goal_type_reads
  trivial

-- -----------------------------------------------------------------------
-- Step 2 — Classifying the goal: `Expr.isConstOf` vs `Expr.isAppOf`
-- -----------------------------------------------------------------------
/-
  * `target.isConstOf ``True` — the outermost constructor of the `Expr` is *exactly* the
    constant `True` (no arguments). Good for `True`, `False`, etc.

  * `target.isAppOf ``Eq` — after stripping all arguments from the outside, the head is the
    constant `Eq`. Equalities `a = b` are `@Eq α a b`, i.e. `Eq` applied, **not** bare `Eq`.

  * `target.isAppOf ``And` — head is `And`; conjunction `P ∧ Q` is `And P Q`.

  These are **syntactic** on the `Expr` tree. If the goal is *definitionally* the same but not
  built with that head (e.g. unfolded abbreviations), you may need `whnf` / `unfold` or
  definitional checks (`isExprDefEq`) — later phases.
-/

elab "prove_true" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
  else
    throwError "goal is not syntactically `True`"

example : True := by prove_true

-- -----------------------------------------------------------------------
-- Step 3 — Branch on shape, then delegate to an existing tactic
-- -----------------------------------------------------------------------

elab "prove_eq_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isAppOf ``Eq then
    evalTactic (← `(tactic| rfl))
  else
    throwError "goal is not syntactically an equality"

example (n : Nat) : n = n := by prove_eq_rfl

elab "split_and" : tactic => do
  let target ← getMainTarget
  if target.isAppOf ``And then
    evalTactic (← `(tactic| constructor))
  else
    throwError "goal is not syntactically a conjunction"

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  split_and
  · assumption
  · assumption

-- If the goal is `True`, close it; otherwise try `rfl` (useful for definitional equalities).

elab "prove_true_or_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  if target.isConstOf ``True then
    evalTactic (← `(tactic| exact True.intro))
  else
    evalTactic (← `(tactic| rfl))

example : True := by prove_true_or_rfl
example (n : Nat) : n = n := by prove_true_or_rfl

-- -----------------------------------------------------------------------
-- Step 4 — The local context: `getLCtx` inside `goal.withContext`
-- -----------------------------------------------------------------------
/-
  Each goal metavariable carries a **local context**: the hypotheses in scope for *that* goal.

  * `for localDecl in (← getLCtx) do ...` iterates them in order.
  * `localDecl.userName` — what you write in the editor (`h`, `n`, …).
  * `localDecl.type` — the `Expr` for the hypothesis type (what you see after `:`).
  * `localDecl.toExpr` — the `Expr` for the hypothesis itself (what you’d pass to `exact`).

  **Why `withContext`?** `getLCtx` reads the context from the current `MetaM` state. Running
  under `goal.withContext` (or `withMainContext`) sets that state to match the chosen goal.

  * `inferType e` — infer the type of an arbitrary expression `e` (useful for compound terms).
    For a hypothesis `h`, `inferType h.toExpr` should match `h.type` up to definitional equality.

  * `isExprDefEq t s` — definitional equality of types/terms (may assign metavariables).
    Same as `isDefEq`. Use it to ask “is this hypothesis’s type *defeq* to `False`?” etc.

  Skip “implementation detail” locals (macro temps) with `unless localDecl.isImplementationDetail`.
-/

/-- List hypotheses visible to the main goal (check the Messages panel). -/
elab "trace_locals" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        logInfo m!"local {localDecl.userName} : {← ppExpr localDecl.type}"

example (a _b : Nat) (_ha : a = 0) : True := by
  trace_locals
  trivial

/-- Close the goal if any hypothesis is definitionally `False` (no check on the goal type). -/
elab "exact_false_hyp" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let falseTy := mkConst ``False
    for localDecl in (← getLCtx) do
      if (← isExprDefEq localDecl.type falseTy) then
        goal.assign localDecl.toExpr
        return
    throwError "no hypothesis of type False"

example (h : False) : False := by exact_false_hyp

/-- Find a `Nat` hypothesis and show `inferType` on its `Expr`. -/
elab "trace_first_nat_hyp" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let natTy := mkConst ``Nat
    for localDecl in (← getLCtx) do
      if (← isExprDefEq localDecl.type natTy) then
        let inferred ← inferType localDecl.toExpr
        logInfo m!"found {localDecl.userName}, `inferType` gives: {← ppExpr inferred}"
        return
    logInfo "no `Nat` hypothesis found"

example (_n : Nat) : True := by
  trace_first_nat_hyp
  trivial

-- -----------------------------------------------------------------------
-- Step 5 — Stepping stones toward “search the context, then close”
-- -----------------------------------------------------------------------
/-
  Exercise 1 below asks for `prove_false`. Here we split that into two **read-only** tactics so
  you can validate each piece before combining with `goal.assign`.
-/

/-- Only succeed (with a log message) when the goal is syntactically `False`. -/
elab "prove_false_check_goal" : tactic => do
  let target ← getMainTarget
  if target.isConstOf ``False then
    logInfo "Goal is `False`. Next: search `getLCtx` for a hypothesis of type `False`."
  else
    throwError "Goal is not syntactically `False`"

example (h : False) : False := by
  prove_false_check_goal
  exact_false_hyp

/-- Under the goal’s context, log every hypothesis that is defeq to `False`. -/
elab "prove_false_list_hyps" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let falseTy := mkConst ``False
    for localDecl in (← getLCtx) do
      if (← isExprDefEq localDecl.type falseTy) then
        logInfo m!"candidate: {localDecl.userName} : False"

example (_h : False) : True := by
  prove_false_list_hyps
  trivial

-- -----------------------------------------------------------------------
-- Exercises (tiered)
-- -----------------------------------------------------------------------
/-
  **Warm-up A.** Uncomment and fix the example: implement `count_visible_locals` so it logs the
  number of non-implementation-detail entries in `getLCtx` (hint: use a counter in a `for` loop).

  **Warm-up B.** Implement `log_prop_hyps`: log the names of all hypotheses whose **type** is a
  proposition (`Meta.isProp localDecl.type`).

  **Main 1 — `prove_false`.** Goal must be syntactically `False`. Find a hypothesis of type
  `False` with `isExprDefEq` against `mkConst ``False`, then `goal.assign localDecl.toExpr`.

  **Main 2 — `split_iff`.** If the goal is an `Iff`, run `constructor`.

  **Main 3 — `try_trivial`.** If the goal is `True`, `exact True.intro`; else `return ()` without error.

  **Main 4 — `split_and_verbose`.** If `And`, `constructor`; else `throwError` with `m!` including
  the pretty-printed goal type.

  Stub tactics (`count_visible_locals`, …) `throwError` until you implement them; reference
  implementations (`*_ref`) are below so you can compare after trying.
-/

-- Warm-up A (your turn): copy `count_visible_locals_ref`’s body here, then compare.
elab "count_visible_locals" : tactic => do
  throwError "Exercise: implement `count_visible_locals` (Warm-up A — see `count_visible_locals_ref` below)"

-- example : True := by count_visible_locals; trivial

-- Warm-up B (your turn): log every `localDecl.userName` where `← isProp localDecl.type`.
elab "log_prop_hyps" : tactic => do
  throwError "Exercise: implement `log_prop_hyps` (Warm-up B — see `log_prop_hyps_ref` below)"

-- example (_n : Nat) (P : Prop) (_h : P) : True := by log_prop_hyps; trivial

-- Main exercises (your turn): fill in; each has a `*_ref` solution below.

elab "prove_false" : tactic => do
  throwError "Exercise: implement `prove_false` (Main 1 — see `prove_false_ref` below)"

-- example (_P : Prop) (h : False) : False := by prove_false

elab "split_iff" : tactic => do
  throwError "Exercise: implement `split_iff` (Main 2 — see `split_iff_ref` below)"

-- example (P Q : Prop) (pq : P → Q) (qp : Q → P) : P ↔ Q := by split_iff; exact pq; exact qp

elab "try_trivial" : tactic => do
  throwError "Exercise: implement `try_trivial` (Main 3 — see `try_trivial_ref` below)"

-- example : True := by try_trivial

elab "split_and_verbose" : tactic => do
  throwError "Exercise: implement `split_and_verbose` (Main 4 — see `split_and_verbose_ref` below)"

-- example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by split_and_verbose; assumption; assumption

-- -- -----------------------------------------------------------------------
-- -- Reference solutions (peek after you try)
-- -- -----------------------------------------------------------------------

-- elab "count_visible_locals_ref" : tactic => do
--   let goal ← getMainGoal
--   goal.withContext do
--     let mut n : Nat := 0
--     for localDecl in (← getLCtx) do
--       unless localDecl.isImplementationDetail do
--         n := n + 1
--     logInfo m!"visible local hypotheses: {n}"

-- example : True := by count_visible_locals_ref; trivial

-- elab "log_prop_hyps_ref" : tactic => do
--   let goal ← getMainGoal
--   goal.withContext do
--     for localDecl in (← getLCtx) do
--       unless localDecl.isImplementationDetail do
--         if (← isProp localDecl.type) then
--           logInfo m!"Prop hyp: {localDecl.userName}"

-- example (_n : Nat) (P : Prop) (_h : P) : True := by
--   log_prop_hyps_ref
--   trivial

-- elab "prove_false_ref" : tactic => do
--   let target ← getMainTarget
--   if target.isConstOf ``False then
--     let goal ← getMainGoal
--     goal.withContext do
--       let falseTy := mkConst ``False
--       for localDecl in (← getLCtx) do
--         if (← isExprDefEq localDecl.type falseTy) then
--           goal.assign localDecl.toExpr
--           return
--       throwError "no local hypothesis of type False"
--   else
--     throwError "goal is not False"

-- example (_P : Prop) (h : False) : False := by prove_false_ref

-- elab "split_iff_ref" : tactic => do
--   let target ← getMainTarget
--   if target.isAppOf ``Iff then
--     evalTactic (← `(tactic| constructor))
--   else
--     throwError "goal is not an iff"

-- example (P Q : Prop) (pq : P → Q) (qp : Q → P) : P ↔ Q := by
--   split_iff_ref
--   exact pq
--   exact qp

-- elab "try_trivial_ref" : tactic => do
--   let target ← getMainTarget
--   if target.isConstOf ``True then
--     evalTactic (← `(tactic| exact True.intro))
--   else
--     return ()

-- example : True := by try_trivial_ref

-- elab "split_and_verbose_ref" : tactic => do
--   let goal ← getMainGoal
--   let target ← goal.getType
--   if target.isAppOf ``And then
--     evalTactic (← `(tactic| constructor))
--   else
--     throwError m!"goal is not a conjunction: {← ppExpr target}"

-- example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
--   split_and_verbose_ref
--   assumption
--   assumption
