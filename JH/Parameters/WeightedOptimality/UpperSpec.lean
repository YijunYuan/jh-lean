/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.WeightedConstantSpec
public import JH.Parameters.CertificateSpec

/-!
# Rounded parameters for the weighted upper bound

Rounded parameters for the upper asymptotic loss in Appendix A.4.
-/

@[expose] public section

namespace JH.Parameters

open Filter
open JH.Analysis.WeightedConstant

namespace WeightedUpper

/-- The rounded degree ⌈√(n/R(y))⌉ in the construction attaining the weighted upper bound. -/
noncomputable def degree (y : ℝ) (n : ℕ) : ℕ := ⌈Real.sqrt ((n : ℝ) / R y)⌉₊

/-- The implementation's rounded log₂ μ, equal to ⌈R(y)d⌉. -/
noncomputable def muExponent (y : ℝ) (n : ℕ) : ℕ := ⌈R y * (degree y n : ℝ)⌉₊

/-- The rounded log₂ Binh, equal to ⌈yd⌉. -/
noncomputable def nuExponent (y : ℝ) (n : ℕ) : ℕ := ⌈y * (degree y n : ℝ)⌉₊

/-- The integer exponent loss for the upper construction, with a sixteen-bit constant margin. -/
noncomputable def loss (y : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * y * (degree y n : ℝ) + Real.logb 2 (4 * (n : ℝ)) + 16⌉₊

/-- The rounded weighted certificate parameters at λ = 1 and Bpath = 4n. -/
noncomputable def parameters (y : ℝ) (n : ℕ) : Params where
  n := n
  lambda := 1
  pi := 4 * n
  d := degree y n
  mu := 2 ^ muExponent y n
  nu := 2 ^ nuExponent y n
  s := loss y n

/-- The minimizing weight (A.11) evaluated at the rounded parameters. -/
noncomputable def weight (y : ℝ) (n : ℕ) : ℝ :=
  JH.Analysis.optimalTheta ((parameters y n).Pi : ℝ) ((parameters y n).Gamma : ℝ)
    (parameters y n).d

/-- The disjoint-path inequality (33) for the chosen parameters. -/
def FlowCondition (p : Params) : Prop :=
  2 ^ (2 * p.n + p.lambda + 3) * p.h.factorial * (2 * p.Pi ^ 2) ^ p.h ≤ p.U ^ p.h

end WeightedUpper

namespace WeightedUpperSpec

open WeightedUpper

/-- The ceiling in the degree and the loss changes their contribution by a bounded amount. -/
def LossBound : Prop :=
  ∀ (y : ℝ) (n : ℕ), Minimizer y → 0 < n →
    ((parameters y n).s : ℝ) ≤ objective y * Real.sqrt (n : ℝ) + Real.logb 2 (n : ℝ) + (2 * y + 19)

/-- The power balance and a constant reserve pay the finite constraints once the growth
and flow comparisons hold. -/
def CertificateFromGrowth : Prop :=
  ∀ (y : ℝ) (n : ℕ), Minimizer y → 4 ≤ n →
    let p := parameters y n
    p.NuChoice → (p.pi : ℝ) ≤ (2 : ℝ) ^ (g y * (p.d : ℝ)) → FlowCondition p →
    p.WeightedPreCertificate 0 (weight y n)

/-- At a minimizing y the rounded parameters eventually satisfy the inheritance, growth, and path
inequalities used for feasibility. -/
def EventualGrowth : Prop :=
  ∀ (y : ℝ), Minimizer y → ∀ᶠ n : ℕ in atTop,
    let p := parameters y n
    p.NuChoice ∧ (p.pi : ℝ) ≤ (2 : ℝ) ^ (g y * (p.d : ℝ)) ∧ FlowCondition p

/-- At a minimizer, the same rounded parameters are feasible for all sufficiently large lengths. -/
def EventualConstruction : Prop :=
  ∀ (y : ℝ), Minimizer y → ∀ᶠ n : ℕ in atTop,
    let p := parameters y n
    p.WeightedPreCertificate 0 (weight y n) ∧
      (p.s : ℝ) ≤ objective y * Real.sqrt (n : ℝ) + Real.logb 2 (n : ℝ) + (2 * y + 19)

/-- The upper half of the asymptotic certificate loss in (A.12). -/
def OptimalUpper : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (p : Params) (theta : ℝ), p.n = n ∧ p.lambda = 1 ∧ p.WeightedPreCertificate 0 theta ∧
      (p.s : ℝ) ≤ Cstar * Real.sqrt (n : ℝ) + Real.logb 2 (n : ℝ) + K

/-- The construction's certificate applies to any query budget it can support. -/
def BudgetTransfer : Prop :=
  ∀ (p : Params) (theta : ℝ) (q : ℕ), p.WeightedPreCertificate 0 theta → p.QueryBudget q →
    p.WeightedPreCertificate q theta

end WeightedUpperSpec

end JH.Parameters
