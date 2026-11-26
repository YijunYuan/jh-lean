/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constant in the weighted certificate loss

The asymptotic constant from the one-variable minimization in (A.14).
-/

@[expose] public section

namespace JH.Analysis

namespace WeightedConstant

/-- The logarithmic correction g(y) = log₂(1 + 2^(−y)) in (A.13). -/
noncomputable def g (y : ℝ) : ℝ := Real.logb 2 (1 + (2 : ℝ) ^ (-y))

/-- The value of x/d at which the two losses in (A.13) agree. -/
noncomputable def R (y : ℝ) : ℝ := y - g y / 2

/-- The leading coefficient 2y/√R(y) minimized in (A.14). -/
noncomputable def objective (y : ℝ) : ℝ := 2 * y / Real.sqrt (R y)

/-- The domain R(y) > 0 of the minimization in (A.14). -/
def domain : Set ℝ := {y | 0 < R y}

/-- The infimum C∗ of the leading coefficients in (A.14). -/
noncomputable def Cstar : ℝ := sInf (objective '' domain)

/-- The parameter y attains C∗ on the domain R(y) > 0. -/
def Minimizer (y : ℝ) : Prop :=
  y ∈ domain ∧ ∀ z ∈ domain, objective y ≤ objective z

end WeightedConstant

namespace WeightedConstantSpec

open WeightedConstant

/-- At each nonnegative ratio the two losses balance at a unique argument. -/
def Balance : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∃! y : ℝ, R y = r

/-- The infimum in (A.14) is attained in its positive-denominator domain. -/
def Attainment : Prop := ∃ y : ℝ, Minimizer y ∧ objective y = Cstar

/-- Exactly one feasible value of y minimizes the coefficient in (A.14). -/
def UniqueMinimizer : Prop := ∃! y : ℝ, Minimizer y

/-- The larger of the two drift and intersection losses bounds C∗ times the square root of x/d.
-/
def MinMaxLowerBound : Prop :=
  ∀ r y : ℝ, 0 < r → Cstar * Real.sqrt r ≤
    max (2 * r + g y) (r + y + g y / 2)

/-- A minimizer in (A.14) satisfies the stationary equation 2R(y) = yR′(y). -/
def CriticalPoint : Prop :=
  ∀ y : ℝ, Minimizer y → 2 * R y = y * deriv R y

/-- The spare coefficient in the flow constraint for the choice `pi = 4 * n`. -/
def FlowSlack : Prop :=
  ∀ y : ℝ, Minimizer y → (1 / 2 : ℝ) < g y / Real.sqrt (R y)

end WeightedConstantSpec

end JH.Analysis
