/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.WeightedConstantSpec
public import JH.PreimageSpec
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Nat.Find

/-!
# Optimal certificate loss and the resulting query bound

The least weighted certificate loss and its fixed-target query bound.
-/

@[expose] public section

namespace JH.Parameters

open Filter

/-- Feasibility of the prescribed loss at advantage one half. The zero budget isolates
the certificate's parameter inequalities from the adversary's actual query budget. -/
def WeightedFeasible (n s : ℕ) : Prop :=
  ∃ (params : Params) (theta : ℝ),
    params.n = n ∧ params.lambda = 1 ∧ params.s = s ∧ params.WeightedPreCertificate 0 theta

/-- The least feasible certificate loss, using zero for an empty feasible set. -/
noncomputable def leastWeightedLoss (n : ℕ) : ℕ := by
  classical
  exact if existsFeasible : ∃ s, WeightedFeasible n s then Nat.find existsFeasible else 0

/-- The leading and logarithmic terms C∗√n + log₂ n of the weighted loss in (A.12). -/
noncomputable def weightedLossMain (n : ℕ) : ℝ :=
  Analysis.WeightedConstant.Cstar * Real.sqrt (n : ℝ) + Real.logb 2 (n : ℝ)

namespace WeightedOptimalitySpec

/-- For every sufficiently large width the least feasible weighted loss is attained. -/
def EventualFeasibility : Prop :=
  ∀ᶠ n : ℕ in atTop, WeightedFeasible n (leastWeightedLoss n)

/-- Equation (A.12), with a bounded error as the state word length tends to infinity. -/
def LossAsymptotic : Prop :=
  Asymptotics.IsBigO atTop
    (fun n : ℕ ↦ (leastWeightedLoss n : ℝ) - weightedLossMain n) (fun _ ↦ (1 : ℝ))

/-- A feasible loss gives a strict logarithmic lower bound for every real trial attaining
success probability at least one half. -/
def FixedTargetQueryBound : Prop :=
  ∀ (n s q α : ℕ) (target : Word n) (initial : State n) (padding : Padding α n)
    (strategies : PMF (Strategy α n)),
    WeightedFeasible n s → FixedTargetBudget q initial padding strategies →
    (1 / 2 : ℝ) ≤ fixedTargetSuccessProbability target initial padding strategies →
      0 < q ∧ (n : ℝ) - (s : ℝ) < Real.logb 2 (q : ℝ)

/-- The eventual logarithmic lower bound on the total-query budget of a fixed-target trial. -/
def QueryLowerBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (q α : ℕ) (target : Word n) (initial : State n) (padding : Padding α n)
      (strategies : PMF (Strategy α n)),
      FixedTargetBudget q initial padding strategies →
      (1 / 2 : ℝ) ≤ fixedTargetSuccessProbability target initial padding strategies →
        0 < q ∧ (n : ℝ) - weightedLossMain n - K ≤ Real.logb 2 (q : ℝ)

end WeightedOptimalitySpec

end JH.Parameters
