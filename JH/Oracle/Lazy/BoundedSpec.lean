/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.FreshFrontierSpec
public import JH.Oracle.Lazy.TrialSpec

/-!
# The law of lazy sampling with a fresh-access budget

Lazy sampling with a bound on the number of fresh accesses.
-/

@[expose] public section

namespace JH

namespace TrialProgram

variable {n : ℕ}

/-- Resolve the cache before spending any fuel. Each new record consumes one unit. -/
noncomputable def lazyBounded (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) : PMF (Option (TrialResult n)) :=
  match program.nextFresh old with
  | .done terminal => PMF.pure (some ⟨old, terminal⟩)
  | .query request resume =>
      match fuel with
      | 0 => PMF.pure none
      | remaining + 1 =>
          ((old.posterior possible).map request.reply).bindOnSupport fun answer supported ↦
            lazyBounded remaining (resume answer) (old.appendReply request answer)
              (old.appendReply_possible possible request supported)
termination_by structural fuel

end TrialProgram

namespace BoundedLazySpec

/-- The bounded lazy sampler has the law of the bounded run with a fixed sampled permutation. -/
def BoundedLaw : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π),
    TrialProgram.lazyBounded fuel program old possible =
      (old.posterior possible).map (fun π ↦ TrialProgram.runFreshBounded π fuel program old)

/-- Starting with an empty cache gives the real fixed-target result restricted to the budget. -/
def FixedTrialLaw : Prop :=
  ∀ {α n : ℕ} (strategy : Strategy α n) (initial : State n) (padding : Padding α n) (fuel : ℕ),
    TrialProgram.lazyBounded fuel (TrialProgram.ofStrategy strategy initial padding) []
        (Transcript.empty_possible n) =
      (uniformPermutation n).map fun π ↦
        let result := fixedTargetTrial strategy π initial padding
        if result.records.length ≤ fuel then some result else none

end BoundedLazySpec

end JH
