/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.FreshFrontierSpec
public import JH.Oracle.TrialProgram

/-!
# Fresh query frontiers and exact record budgets

`nextFresh` follows cached answers to the next cache miss or terminal action. The bounded run
spends one unit of fuel per new pair and permits termination at zero fuel. The key bound uses
the number of records added to the supplied transcript.
-/

@[expose] public section

namespace JH.TrialProgram

variable {α n : ℕ}

/-- A query at the frontier has no cached answer. -/
theorem nextFresh_miss : FreshFrontierSpec.QueryIsFresh := by
  intro n program old request resume
  induction program with
  | done terminal => simp [nextFresh]
  | query head resumeHead ih =>
    cases cache : old.cachedReply head with
    | none =>
      intro reached
      have equal : FreshFrontier.query head resumeHead = .query request resume := by
        simpa only [nextFresh, cache] using reached
      exact (FreshFrontier.query.inj equal).1 ▸ cache
    | some answer =>
      simpa only [nextFresh, cache] using ih answer

/-- Resolving the cached prefix preserves the result against a consistent permutation. -/
theorem nextFresh_run : FreshFrontierSpec.PreservesRun := by
  intro n program permutation old consistent
  induction program with
  | done => rfl
  | query request resume ih =>
    cases cache : old.cachedReply request with
    | none =>
      simp only [nextFresh, cache, FreshFrontier.toProgram]
    | some answer =>
      rw [nextFresh, cache, run_query_of_hit permutation old request resume consistent cache]
      exact ih answer

theorem run_eq_of_nextFresh_done (program : TrialProgram n) (permutation : Permutation n)
    (old : Transcript n) (consistent : old.Consistent permutation) {terminal : Option (State n)}
    (reached : program.nextFresh old = .done terminal) :
    program.run permutation old = ⟨old, terminal⟩ := by
  simpa only [reached, FreshFrontier.toProgram, run] using
    (nextFresh_run program permutation old consistent).symm

theorem run_eq_of_nextFresh_query (program : TrialProgram n) (permutation : Permutation n)
    (old : Transcript n) (consistent : old.Consistent permutation) {request : Query n}
    {resume : State n → TrialProgram n} (reached : program.nextFresh old = .query request resume) :
    program.run permutation old =
      (resume (request.reply permutation)).run permutation (old ++
        [request.record permutation]) := by
  rw [← nextFresh_run program permutation old consistent, reached, FreshFrontier.toProgram]
  exact run_query_of_miss permutation old request resume
    (nextFresh_miss program old request resume reached)

/-- The bounded run returns the full outcome exactly when its new records fit in the budget. -/
theorem runFreshBounded_eq_by_budget : FreshFrontierSpec.BoundedRun := by
  intro n permutation fuel program old consistent
  induction fuel generalizing program old with
  | zero =>
    cases reached : program.nextFresh old with
    | done terminal =>
      simp [runFreshBounded, reached,
        run_eq_of_nextFresh_done program permutation old consistent reached]
    | query request resume =>
      -- A fresh query with no fuel would already add a record to the unbounded run.
      have grows : old.length + 1 ≤ (program.run permutation old).records.length := by
        rw [run_eq_of_nextFresh_query program permutation old consistent reached]
        simpa using List.IsPrefix.length_le
          ((resume (request.reply permutation)).run_extends permutation
            (old ++ [request.record permutation]))
      have overBudget : ¬ (program.run permutation old).records.length ≤ old.length + 0 := by
        omega
      simp only [runFreshBounded, reached, overBudget, ite_false]
  | succ fuel ih =>
    cases reached : program.nextFresh old with
    | done terminal =>
      simp [runFreshBounded, reached,
        run_eq_of_nextFresh_done program permutation old consistent reached]
    | query request resume =>
      let logged := old ++ [request.record permutation]
      have fresh := (old.cachedReply_eq_none_iff request).mp
        (nextFresh_miss program old request resume reached)
      have loggedConsistent : logged.Consistent permutation := by
        simpa only [Transcript.logAccess, fresh, Bool.false_eq_true, ite_false] using
          old.logAccess_consistent permutation request consistent
      -- One new pair shifts the initial length up by the unit of fuel spent here.
      have budget : logged.length + fuel = old.length + (fuel + 1) := by
        simp only [logged, List.length_append, List.length_singleton]
        omega
      rw [runFreshBounded, reached,
        run_eq_of_nextFresh_query program permutation old consistent reached,
        ← budget]
      exact ih (resume (request.reply permutation)) logged loggedConsistent

theorem runFreshBounded_eq_some_iff (permutation : Permutation n) (fuel : ℕ)
    (program : TrialProgram n) (old : Transcript n) (consistent : old.Consistent permutation) :
    runFreshBounded permutation fuel program old = some (program.run permutation old) ↔
      (program.run permutation old).records.length ≤ old.length + fuel := by
  rw [runFreshBounded_eq_by_budget permutation fuel program old consistent]
  by_cases enough :
    (program.run permutation old).records.length ≤ old.length + fuel <;> simp [enough]

theorem runFreshBounded_ofStrategy (strategy : Strategy α n) (permutation : Permutation n)
    (initial : State n) (padding : Padding α n) (fuel : ℕ) :
    runFreshBounded permutation fuel (ofStrategy strategy initial padding) [] =
        some (fixedTargetTrial strategy permutation initial padding) ↔
      (fixedTargetTrial strategy permutation initial padding).WithinBudget fuel := by
  have same := ofStrategy_run strategy permutation initial padding
  simpa only [same, List.length_nil, Nat.zero_add, TrialResult.WithinBudget] using
    runFreshBounded_eq_some_iff permutation fuel (ofStrategy strategy initial padding) []
      (fun index ↦ Fin.elim0 index)

end JH.TrialProgram
