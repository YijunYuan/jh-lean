/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convexity and the optimal grafting weight

Convexity bounds and the weight that minimizes the one-step cost.
-/

@[expose] public section

namespace JH.Analysis

noncomputable section

/-- Equal-weight convexity for the two ancestor sets in Lemma 4. -/
def TwoConvex : Prop :=
  ∀ (a b : ℝ) (d : ℕ), 0 ≤ a → 0 ≤ b → 1 ≤ d →
    (a + b) ^ d ≤ (2 : ℝ) ^ (d - 1) * (a ^ d + b ^ d)

/-- Weighted convexity for the two ancestor sets in Appendix A.3. -/
def WeightedConvex : Prop :=
  ∀ (a b theta : ℝ) (d : ℕ), 0 ≤ a → 0 ≤ b → 1 ≤ d → 0 < theta →
    (a + b) ^ d ≤ (1 + theta) ^ (d - 1) * a ^ d + (1 + theta⁻¹) ^ (d - 1) * b ^ d

/-- The ratio Binh = Bpot / Bver from (A.1). -/
def weightRatio (pi gamma : ℝ) : ℝ :=
  gamma / pi

/-- The coefficient $J$ in `eq:weighted`. The arguments `pi` and `gamma` are
$B_{\mathrm{ver}}$ and $B_{\mathrm{pot}}$. -/
def weightedCost (pi gamma : ℝ) (d : ℕ) (theta : ℝ) : ℝ :=
  pi * (1 + theta) ^ (d - 1) + gamma * (1 + theta⁻¹) ^ (d - 1)

/-- The weight θ* in equation (A.11). The exponent is real. -/
def optimalTheta (pi gamma : ℝ) (d : ℕ) : ℝ :=
  weightRatio pi gamma ^ (1 / (d : ℝ))

/-- The specified weight is positive and globally minimizes the graft coefficient J over
positive weights. -/
def ThetaOptimal : Prop :=
  ∀ (pi gamma : ℝ) (d : ℕ), 0 < pi → 0 < gamma → 2 ≤ d →
    let thetaStar := optimalTheta pi gamma d
    0 < thetaStar ∧
      (∀ (theta : ℝ), 0 < theta → weightedCost pi gamma d thetaStar ≤
        weightedCost pi gamma d theta) ∧
      weightedCost pi gamma d thetaStar = gamma * (1 + thetaStar⁻¹) ^ d

/-- The minimum in the real-power notation of equation (A.11). -/
def ThetaOptimalValue : Prop :=
  ∀ (pi gamma : ℝ) (d : ℕ), 0 < pi → 0 < gamma → 2 ≤ d →
    weightedCost pi gamma d (optimalTheta pi gamma d) =
      gamma * (1 + weightRatio pi gamma ^ (-(1 / (d : ℝ)))) ^ d

end

end JH.Analysis
