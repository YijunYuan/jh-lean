/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.TrialSpec
public import JH.PreimageSpec

/-!
# Transfer of acceptance and verification to independent replies

Transfer fixed-target acceptance from the permutation experiment to independent replies.
-/

@[expose] public section

namespace JH

open scoped ENNReal

/-- Accept a completed successful result. Exhausting the query budget rejects. -/
noncomputable def TrialResult.accepts {n : ℕ} (target : Word n) :
    Option (TrialResult n) → Bool := by
  classical
  exact fun outcome ↦ match outcome with
    | none => false
    | some result => decide (result.Success target)

/-- The acceptance law of a single strategy against a uniform full permutation. -/
noncomputable def permutationAcceptanceLaw {α n : ℕ} (target : Word n) (initial : State n)
    (padding : Padding α n) (strategy : Strategy α n) : PMF Bool := by
  classical
  exact (uniformPMF (Permutation n)).map fun permutation ↦
    decide ((fixedTargetTrial strategy permutation initial padding).Success target)

/-- The bounded independent-reply experiment executes the same program, including verification. -/
noncomputable def independentAcceptanceLaw {α n : ℕ} (q : ℕ) (target : Word n)
    (initial : State n) (padding : Padding α n) (strategy : Strategy α n) : PMF Bool :=
  (TrialProgram.independentBounded q (TrialProgram.ofStrategy strategy initial padding) []).map
    (TrialResult.accepts target)

/-- Average independent-trial acceptance over the adversary's original tape law. -/
noncomputable def independentFixedTargetSuccessProbability {α n : ℕ} (q : ℕ) (target : Word n)
    (initial : State n) (padding : Padding α n) (strategies : PMF (Strategy α n)) : ℝ :=
  ((strategies.bind (independentAcceptanceLaw q target initial padding)) true).toReal

namespace SuccessTransferSpec

/-- An acceptance test on bounded outcomes can change only on the separation event. -/
def BoundedAcceptance : Prop :=
  ∀ {n : ℕ} (q : ℕ) (program : TrialProgram n) (accept : Option (TrialResult n) → Bool),
    Separation.mass (TrialProgram.lazyBounded q program [] (Transcript.empty_possible n)) accept ≤
      Separation.mass (TrialProgram.independentBounded q program []) accept +
        ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞))

/-- A fixed tape satisfying the budget incurs the separation term of equation (8). -/
def StrategyTransfer : Prop :=
  ∀ {α n : ℕ} (q : ℕ) (target : Word n) (initial : State n) (padding : Padding α n)
    (strategy : Strategy α n),
    (∀ permutation, (fixedTargetTrial strategy permutation initial padding).WithinBudget q) →
    ((permutationAcceptanceLaw target initial padding strategy) true).toReal ≤
      ((independentAcceptanceLaw q target initial padding strategy) true).toReal +
        (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 : ℝ) ^ n) ^ 2)

/-- The same comparison after averaging over the supported strategies. -/
def Transfer : Prop :=
  ∀ {α n : ℕ} (q : ℕ) (target : Word n) (initial : State n) (padding : Padding α n)
    (strategies : PMF (Strategy α n)),
    FixedTargetBudget q initial padding strategies →
    fixedTargetSuccessProbability target initial padding strategies ≤
      independentFixedTargetSuccessProbability q target initial padding strategies +
        (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 : ℝ) ^ n) ^ 2)

/-- The comparison in the notation of the finite-parameter certificates. -/
def ParameterTransfer : Prop :=
  ∀ {α : ℕ} (params : Parameters.Params) (q : ℕ) (target : Word params.n)
    (initial : State params.n) (padding : Padding α params.n)
    (strategies : PMF (Strategy α params.n)),
    FixedTargetBudget q initial padding strategies →
    fixedTargetSuccessProbability target initial padding strategies ≤
      independentFixedTargetSuccessProbability q target initial padding strategies +
        params.separationTail q

/-- Verification on independent replies traces a path in its own record graph. -/
def IndependentTrace : Prop :=
  ∀ {α n : ℕ} (q : ℕ) (target : Word n) (initial : State n) (padding : Padding α n)
    (strategy : Strategy α n) (result : TrialResult n),
    some result ∈ (TrialProgram.independentBounded q
      (TrialProgram.ofStrategy strategy initial padding) []).support →
    result.Success target →
    ∃ rate : Word n,
      Nonempty (Walk (result.records.edge {initial}) (startCopy initial) (.inl (target, rate)))

end SuccessTransferSpec

end JH
