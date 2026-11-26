/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.FreshStep
public import JH.Oracle.FreshFrontier
public import JH.Oracle.Independent.TrialSpec
public import JH.Oracle.Lazy.BoundedSpec
public import JH.Oracle.Lazy.Trial
public import JH.Probability.SeparationSpec

/-!
# Coupling complete adaptive trials

The bounded coupling of the adaptive experiments in Section 3.2.
-/

@[expose] public section

namespace JH

open scoped ENNReal BigOperators

variable {n : ℕ}

/-- An outcome from each trial and the flag recording whether their replies ever differed. -/
structure CoupledResult (n : ℕ) where
  /-- The outcome on the permutation side. -/
  permutation : Option (TrialResult n)
  /-- The outcome on the independent-reply side. -/
  independent : Option (TrialResult n)
  /-- Whether the two trials have already taken different replies. -/
  separated : Bool

namespace CoupledResult

/-- The diagonal coupled outcome for two trials that have stayed together. -/
def agreed (result : Option (TrialResult n)) : CoupledResult n := ⟨result, result, false⟩

/-- After the first differing reply, the remaining trials evolve independently. -/
noncomputable def afterSeparation (permutation independent : PMF (Option (TrialResult n))) :
    PMF (CoupledResult n) :=
  (ReplyCoupling.independentPair permutation independent).map fun results ↦
    ⟨results.1, results.2, true⟩

end CoupledResult

namespace Transcript

/-- At a common transcript, the two reply laws use the same proposal when it is unused. -/
noncomputable def coupledReplies (old : Transcript n) (possible : ∃ π : Permutation n,
    old.Consistent π) (request : Query n) (miss : old.cachedReply request = none) :
    PMF (State n × State n) :=
  old.coupleFresh possible.choose possible.choose_spec request miss

theorem coupledReplies_map_fst (old : Transcript n) (possible : ∃ π : Permutation n,
    old.Consistent π) (request : Query n) (miss : old.cachedReply request = none) :
    (old.coupledReplies possible request miss).map Prod.fst =
      (old.posterior possible).map request.reply := by
  rw [old.posterior_eq_conditionedUniform possible possible.choose possible.choose_spec]
  exact (fresh_step_marginals old possible.choose possible.choose_spec request miss).1

theorem coupledReply_possible (old : Transcript n) (possible : ∃ π : Permutation n,
    old.Consistent π) (request : Query n) (miss : old.cachedReply request = none)
    (replies : State n × State n) (supported : replies ∈
      (old.coupledReplies possible request miss).support) :
    ∃ π : Permutation n, (old.appendReply request replies.1).Consistent π := by
  apply old.appendReply_possible possible request
  rw [← old.coupledReplies_map_fst possible request miss]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨replies, supported, rfl⟩

end Transcript

namespace TrialProgram

/-- Use one common frontier until the first differing fresh reply. Both trials have the
same bound on the number of fresh accesses, and cache hits cost no fuel. -/
noncomputable def coupledBounded (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) : PMF (CoupledResult n) :=
  match reached : program.nextFresh old with
  | .done terminal => PMF.pure (CoupledResult.agreed (some ⟨old, terminal⟩))
  | .query request resume =>
      match fuel with
      | 0 => PMF.pure (CoupledResult.agreed none)
      | remaining + 1 =>
          let miss := nextFresh_miss program old request resume reached
          (old.coupledReplies possible request miss).bindOnSupport fun replies supported ↦
            let nextOld := old.appendReply request replies.1
            let nextPossible := old.coupledReply_possible possible request miss replies supported
            if replies.1 = replies.2 then
              coupledBounded remaining (resume replies.1) nextOld nextPossible
            else
              CoupledResult.afterSeparation
                (lazyBounded remaining (resume replies.1) nextOld nextPossible)
                (independentBounded remaining (resume replies.2)
                  (old.appendReply request replies.2))
termination_by structural fuel

end TrialProgram

namespace CoupledTrialSpec

/-- The marginal laws are the bounded permutation and independent trials from the common cache. -/
def Marginals : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π),
    let joint := TrialProgram.coupledBounded fuel program old possible
    joint.map CoupledResult.permutation = TrialProgram.lazyBounded fuel program old possible ∧
      joint.map CoupledResult.independent = TrialProgram.independentBounded fuel program old

/-- A supported outcome with no separation has identical results in both trials. -/
def Agreement : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) (result : CoupledResult n),
    result ∈ (TrialProgram.coupledBounded fuel program old possible).support →
    result.separated = false → result.permutation = result.independent

/-- A common initial history of length `old.length` shifts the starting allowance. -/
def ShiftedBound : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π),
    Separation.mass (TrialProgram.coupledBounded fuel program old possible)
      CoupledResult.separated ≤
      ∑ i ∈ Finset.range fuel, ((old.length + i : ℕ) : ℝ≥0∞) / (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞)

/-- Equation (8) for the actual bounded coupled trials starting from the empty cache. -/
def SeparationBound : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n),
    Separation.mass (TrialProgram.coupledBounded fuel program [] (Transcript.empty_possible n))
      CoupledResult.separated ≤
      ((fuel * (fuel - 1) : ℕ) : ℝ≥0∞) / (2 * (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞))

end CoupledTrialSpec

end JH
