/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Parameters.WeightedOptimality.UpperSpec
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits of the rounded weighted parameters

Limits of the rounded weighted parameters and the optimal weight.
-/

@[expose] public section

namespace JH.Parameters.WeightedLimitsSpec

open Filter
open scoped Topology
open JH.Analysis.WeightedConstant
open WeightedUpper (degree parameters weight)

/-- The three parameter equivalents and the limit of the optimal weights in Appendix A.4. -/
def ParameterLimits : Prop :=
  ∀ y : ℝ, Minimizer y →
    Tendsto (fun n : ℕ ↦ (degree y n : ℝ) / Real.sqrt ((n : ℝ) / R y)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ ↦ Real.logb 2 ((parameters y n).mu : ℝ) / (R y * (degree y n : ℝ)))
      atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ ↦ Real.logb 2 ((parameters y n).nu : ℝ) / (y * (degree y n : ℝ)))
      atTop (𝓝 1) ∧
    Tendsto (weight y) atTop (𝓝 ((2 : ℝ) ^ y))

end JH.Parameters.WeightedLimitsSpec
