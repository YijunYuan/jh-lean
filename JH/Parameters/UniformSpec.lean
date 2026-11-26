/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.PreimageSpec
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform equal-weight parameter choices

The uniform parameter choice and the loss in Appendix A.2.
-/

@[expose] public section

namespace JH.Parameters

noncomputable section

/-- The degree d = max(2, ⌈n/χ⌉) in (37). -/
def uniformPower (n x : ℕ) : ℕ :=
  max 2 ⌈(n : ℝ) / (x : ℝ)⌉₊

/-- The rounded binary logarithm used in the loss exponent of (37). -/
def uniformLog (n : ℕ) : ℕ :=
  ⌈Real.log (n : ℝ) / Real.log 2⌉₊

/-- The explicit loss in (37) for the choices χ and λ. -/
def uniformLossFor (n x lambda : ℕ) : ℕ :=
  2 * x + max (uniformPower n x) lambda + 5 * uniformLog n + 12

/-- The common parameter choices from (37), at a specified budget loss. -/
def uniformParamsAt (n x lambda s : ℕ) : Params where
  n := n
  lambda := lambda
  mu := 2 ^ x
  d := uniformPower n x
  pi := n ^ 2
  s := s
  nu := 8 * ((n + 1) * (n ^ 2 * (2 ^ x - 1)) + n + lambda + 4)

/-- The square-root choice of χ and λ substituted into the parameters of (37). -/
def explicitParams (n : ℕ) : Params :=
  uniformParamsAt n ⌈Real.sqrt ((n : ℝ) / 2)⌉₊ ⌊Real.sqrt (2 * (n : ℝ))⌋₊
    (PreimageSpec.uniformLoss n)

namespace UniformSpec

/-- The choices in (37) satisfy the fixed-target certificate. -/
def ParameterFeasibility : Prop :=
  ∀ n x lambda q : ℕ, 4 ≤ n → 1 ≤ x → x ≤ n → 1 ≤ lambda → lambda ≤ n →
    q * 2 ^ uniformLossFor n x lambda ≤ 2 ^ n →
      (uniformParamsAt n x lambda (uniformLossFor n x lambda)).PreCertificate q

/-- The rounded square-root parameters meet the unweighted certificate at the budget stated
below (39). -/
def ExplicitCertificate : Prop :=
  ∀ n q : ℕ, 4 ≤ n → q * 2 ^ PreimageSpec.uniformLoss n ≤ 2 ^ n →
    (explicitParams n).PreCertificate q

/-- Completing the square gives the minimum of 2χ + n/χ used in the optimization below (39). -/
def UnroundedLoss : Prop :=
  ∀ n x : ℝ, 0 ≤ n → 0 < x →
    2 * x + n / x = 2 * Real.sqrt (2 * n) + (2 / x) * (x - Real.sqrt (n / 2)) ^ 2

/-- The rounded explicit loss below (39) is 2√(2n) + O(log n). -/
def LossAsymptotic : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ ↦ (PreimageSpec.uniformLoss n : ℝ) - 2 * Real.sqrt (2 * (n : ℝ)))
    (fun n : ℕ ↦ Real.log (n : ℝ))

end UniformSpec

end

end JH.Parameters
