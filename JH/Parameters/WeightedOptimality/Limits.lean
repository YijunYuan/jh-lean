/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.WeightedConstant
public import JH.Parameters.WeightedOptimality.LimitsSpec
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Limits of the rounded weighted parameters

The degree and the base-two logarithms of `mu` and `nu` are ceilings of quantities tending to
infinity. Their relative rounding errors vanish. The ratio `Gamma / Pi = nu` then gives the
limit of the chosen weight.
-/

@[expose] public section

namespace JH.Parameters

open Filter
open scoped Topology
open JH.Analysis.WeightedConstant
open WeightedUpper (degree muExponent nuExponent parameters weight)

/-- For a minimizer in (A.14), the rounded degree and logarithms are asymptotic to their
continuous choices, and the weight tends to `2 ^ y`. -/
theorem rounded_weighted_parameter_limits : WeightedLimitsSpec.ParameterLimits := by
  intro y minimum
  have hR : 0 < R y := minimum.1
  have hy : 0 < y := hR.trans (R_lt_self y)
  have realN : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have root : Tendsto (fun n : ℕ ↦ Real.sqrt ((n : ℝ) / R y)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (realN.atTop_div_const hR)
  have hd : Tendsto (fun n : ℕ ↦ (degree y n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_ceil (Real.sqrt ((n : ℝ) / R y))) root
  have rScale : Tendsto (fun n : ℕ ↦ R y * (degree y n : ℝ)) atTop atTop := hd.const_mul_atTop hR
  have yScale : Tendsto (fun n : ℕ ↦ y * (degree y n : ℝ)) atTop atTop := hd.const_mul_atTop hy
  have logTwo (a : ℕ) : Real.logb 2 ((2 ^ a : ℕ) : ℝ) = (a : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ)), mul_one]
  refine ⟨(tendsto_nat_ceil_div_atTop (R := ℝ)).comp root, ?_, ?_, ?_⟩
  · refine ((tendsto_nat_ceil_div_atTop (R := ℝ)).comp rScale).congr fun n ↦ ?_
    exact congrArg (· / (R y * (degree y n : ℝ))) (logTwo (muExponent y n)).symm
  · refine ((tendsto_nat_ceil_div_atTop (R := ℝ)).comp yScale).congr fun n ↦ ?_
    exact congrArg (· / (y * (degree y n : ℝ))) (logTwo (nuExponent y n)).symm
  -- The weight exponent is the rounded exponent of `nu` divided by the degree.
  · have exponent : Tendsto (fun n : ℕ ↦ (nuExponent y n : ℝ) / (degree y n : ℝ))
        atTop (𝓝 y) := (tendsto_nat_ceil_mul_div_atTop hy.le).comp hd
    have continuous : ContinuousAt (fun t : ℝ ↦ (2 : ℝ) ^ t) y :=
      Real.continuousAt_const_rpow (by norm_num)
    refine (continuous.tendsto.comp exponent).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ), hd.eventually_ge_atTop 1] with n hn positiveD
    let p := parameters y n
    have positiveExponent : 1 ≤ muExponent y n :=
      Nat.one_le_ceil_iff.mpr (mul_pos hR (zero_lt_one.trans_le positiveD))
    have hMu : 2 ≤ p.mu := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) positiveExponent
    have hPi : 0 < p.Pi := by
      have hpi : 0 < p.pi := Nat.mul_pos (by decide) hn
      exact Nat.mul_pos hpi (Nat.sub_pos_of_lt hMu)
    have ratio : Analysis.weightRatio (p.Pi : ℝ) (p.Gamma : ℝ) = (p.nu : ℝ) := by
      unfold Analysis.weightRatio Params.Gamma
      rw [Nat.cast_mul]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hPi.ne')
    have hnupow : (p.nu : ℝ) = (2 : ℝ) ^ (nuExponent y n : ℝ) := by
      simp [p, parameters, Real.rpow_natCast]
    change (2 : ℝ) ^ ((nuExponent y n : ℝ) / (degree y n : ℝ)) =
      Analysis.weightRatio (p.Pi : ℝ) (p.Gamma : ℝ) ^ (1 / (degree y n : ℝ))
    rw [ratio, hnupow, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring

end JH.Parameters
