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
# Necessary conditions for weighted certificate loss

Necessary conditions on a weighted certificate in Appendix A.4.
-/

@[expose] public section

namespace JH.Parameters.WeightedLowerSpec

open JH.Analysis.WeightedConstant

/-- Retain the optimized portion of the weighted drift and intersection conditions. -/
def PowerRequirements : Prop :=
  ∀ (p : Params) (q : ℕ) (theta : ℝ), p.WeightedPreCertificate q theta →
    let amplification := (1 + (p.nu : ℝ) ^ (-(1 / (p.d : ℝ)))) ^ p.d
    4 * (p.Theta : ℝ) * amplification ≤ (p.U : ℝ) ∧
      (2 : ℝ) ^ (p.lambda + 6) * (p.Gamma : ℝ) ^ 2 * amplification ≤ (p.U : ℝ) ^ 2 ∧
      (p.Gamma : ℝ) ≤ (p.U : ℝ)

/-- Logarithmic balance, the initial-potential constraint and the flow constraint. -/
def Necessary : Prop :=
  ∀ (p : Params) (q : ℕ) (theta : ℝ), p.WeightedPreCertificate q theta →
    let x := Real.logb 2 (p.mu : ℝ)
    let y := Real.logb 2 (p.nu : ℝ) / (p.d : ℝ)
    let r := x / (p.d : ℝ)
    Real.logb 2 (p.pi : ℝ) + (p.d : ℝ) * max (2 * r + g y) (r + y + g y / 2) ≤ (p.s : ℝ) ∧
      (p.n : ℝ) + 1 - (p.s : ℝ) ≤ (p.d : ℝ) * x ∧
      2 * p.n ≤ p.h * p.s

/-- Every weighted certificate at advantage one half pays the same asymptotic lower bound. -/
def UniformLower : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : Params) (q : ℕ) (theta : ℝ),
    p.lambda = 1 → p.WeightedPreCertificate q theta →
    Cstar * Real.sqrt (p.n : ℝ) + Real.logb 2 (p.n : ℝ) - K ≤ (p.s : ℝ)

end JH.Parameters.WeightedLowerSpec
