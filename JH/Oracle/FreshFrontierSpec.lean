/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.TrialProgramSpec

/-!
# Fresh query frontiers and exact record budgets

The next fresh query and its contribution to the record budget.
-/

@[expose] public section

namespace JH

/-- The next action after all preceding cache hits have been resolved. -/
inductive FreshFrontier (n : ℕ) where
  | done (terminal : Option (State n))
  | query (request : Query n) (resume : State n → TrialProgram n)

/-- View the action and its continuation as a query program. -/
def FreshFrontier.toProgram {n : ℕ} : FreshFrontier n → TrialProgram n
  | .done terminal => .done terminal
  | .query request resume => .query request resume

namespace TrialProgram

variable {n : ℕ}

/-- Resolve cache hits with the existing records up to the next fresh query or termination. -/
def nextFresh (program : TrialProgram n) (old : Transcript n) : FreshFrontier n :=
  match program with
  | .done terminal => .done terminal
  | .query request resume =>
      match old.cachedReply request with
      | none => .query request resume
      | some answer => nextFresh (resume answer) old
termination_by structural program

/-- Run at most the specified number of fresh accesses. A terminal frontier still returns
a result at fuel zero. An attempted fresh access at fuel zero returns `none`. -/
def runFreshBounded (permutation : Permutation n) (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n) : Option (TrialResult n) :=
  match program.nextFresh old with
  | .done terminal => some ⟨old, terminal⟩
  | .query request resume =>
      match fuel with
      | 0 => none
      | remaining + 1 =>
          runFreshBounded permutation remaining (resume (request.reply permutation))
            (old ++ [request.record permutation])
termination_by structural fuel

end TrialProgram

namespace FreshFrontierSpec

/-- A query at the frontier has no cached answer. -/
def QueryIsFresh : Prop :=
  ∀ {n : ℕ} (program : TrialProgram n) (old : Transcript n) (request : Query n)
    (resume : State n → TrialProgram n), program.nextFresh old = .query request resume →
      old.cachedReply request = none

/-- The skipped queries leave the fixed-permutation result unchanged. -/
def PreservesRun : Prop :=
  ∀ {n : ℕ} (program : TrialProgram n) (permutation : Permutation n) (old : Transcript n),
    old.Consistent permutation →
      (program.nextFresh old).toProgram.run permutation old = program.run permutation old

/-- The bounded run returns the full result exactly when the record budget suffices. -/
def BoundedRun : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n), old.Consistent permutation →
      TrialProgram.runFreshBounded permutation fuel program old =
        if (program.run permutation old).records.length ≤ old.length + fuel then
          some (program.run permutation old)
        else none

end FreshFrontierSpec

end JH
