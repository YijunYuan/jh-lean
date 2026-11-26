/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.ConvexSpec
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Tactic.Ring

/-!
# Convexity and the optimal grafting weight

Jensen's inequality applied to two rescaled nonnegative summands gives the weighted inequality
in Appendix A.3. Setting the weight parameter to one recovers the estimate in Lemma 4. A second
application of the weighted inequality gives the global optimum in (A.11).
-/

@[expose] public section

namespace JH.Analysis

/-- The weighted power bound from Appendix A.3 for nonnegative summands, positive weight and
degree at least one. -/
theorem weighted_convex : WeightedConvex := by
  intro a b theta d ha hb hd htheta
  have hleft : 0 < 1 + theta := add_pos zero_lt_one htheta
  have hright : 0 < 1 + theta⁻¹ := add_pos zero_lt_one (inv_pos.mpr htheta)
  have hdenom : 1 + theta⁻¹ = (1 + theta) / theta := by
    rw [add_div, div_self htheta.ne', one_div, add_comm]
  have hweights : (1 + theta)⁻¹ + (1 + theta⁻¹)⁻¹ = 1 := by
    rw [hdenom, inv_div, ← one_div, ← add_div, div_self hleft.ne']
  -- Apply convexity at the rescaled points with reciprocal weights.
  have hjensen := (convexOn_pow (𝕜 := ℝ) d).2
    (Set.mem_Ici.mpr (mul_nonneg hleft.le ha))
    (Set.mem_Ici.mpr (mul_nonneg hright.le hb))
    (inv_nonneg.mpr hleft.le) (inv_nonneg.mpr hright.le) hweights
  -- The reciprocal Jensen weight cancels one scaling factor, leaving the exponent `d - 1`.
  have hscalePow (c x : ℝ) (hc : c ≠ 0) :
      c⁻¹ * (c * x) ^ d = c ^ (d - 1) * x ^ d := by
    rw [mul_pow, ← mul_pow_sub_one (Nat.ne_of_gt hd) c, mul_assoc, inv_mul_cancel_left₀ hc]
  simpa only [smul_eq_mul, inv_mul_cancel_left₀ hleft.ne', inv_mul_cancel_left₀ hright.ne',
    hscalePow _ _ hleft.ne', hscalePow _ _ hright.ne'] using hjensen

/-- The equal-weight power bound used in Lemma 4. -/
theorem two_convex : TwoConvex := by
  intro a b d ha hb hd
  simpa only [inv_one, one_add_one_eq_two, mul_add] using
    weighted_convex a b 1 d ha hb hd zero_lt_one

/-- For positive coefficients and degree at least two, the weight satisfying `pi * theta ^ d =
gamma` minimizes the weighted grafting coefficient. -/
theorem theta_optimal : ThetaOptimal := by
  intro pi gamma d hpi hgamma hd
  let thetaStar := optimalTheta pi gamma d
  have hd_one : 1 ≤ d := le_trans (by decide : 1 ≤ 2) hd
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.succ_le_iff.mp hd_one))
  have hratio : 0 < weightRatio pi gamma := div_pos hgamma hpi
  have hthetaStar : 0 < thetaStar := Real.rpow_pos_of_pos hratio _
  have hthetaPower : thetaStar ^ d = weightRatio pi gamma := by
    change (weightRatio pi gamma ^ (1 / (d : ℝ))) ^ d = weightRatio pi gamma
    rw [← Real.rpow_mul_natCast hratio.le, one_div_mul_cancel hd_ne, Real.rpow_one]
  -- The balancing identity matches the second coefficient of the convexity bound to `gamma`.
  have hbalance : pi * thetaStar ^ d = gamma := by
    rw [hthetaPower, weightRatio, mul_comm pi, div_mul_cancel₀ gamma hpi.ne']
  have hfactor : 1 + thetaStar = thetaStar * (1 + thetaStar⁻¹) := by
    rw [mul_add, mul_one, mul_inv_cancel₀ hthetaStar.ne', add_comm]
  have hcoefficient : pi * thetaStar ^ (d - 1) = gamma * thetaStar⁻¹ := by
    rw [← hbalance, ← pow_sub_one_mul (Nat.ne_of_gt hd_one) thetaStar, mul_assoc pi,
      mul_assoc (thetaStar ^ (d - 1)), mul_inv_cancel₀ hthetaStar.ne', mul_one]
  have hvalue : weightedCost pi gamma d thetaStar = gamma * (1 + thetaStar⁻¹) ^ d := by
    unfold weightedCost
    calc
      _ = (pi * thetaStar ^ (d - 1) + gamma) * (1 + thetaStar⁻¹) ^ (d - 1) := by
        rw [hfactor, mul_pow]
        ring
      _ = gamma * (1 + thetaStar⁻¹) ^ d := by
        rw [hcoefficient, ← pow_sub_one_mul (Nat.ne_of_gt hd_one) (1 + thetaStar⁻¹)]
        ring
  refine ⟨hthetaStar, ?_, hvalue⟩
  intro theta htheta
  -- Convexity at (1, θ*) gives the same lower bound for every positive θ.
  calc
    weightedCost pi gamma d thetaStar = gamma * (1 + thetaStar⁻¹) ^ d := hvalue
    _ = pi * (1 + thetaStar) ^ d := by rw [hfactor, mul_pow, ← hbalance, mul_assoc]
    _ ≤ pi * ((1 + theta) ^ (d - 1) * (1 : ℝ) ^ d +
        (1 + theta⁻¹) ^ (d - 1) * thetaStar ^ d) :=
      mul_le_mul_of_nonneg_left
        (weighted_convex 1 thetaStar theta d zero_le_one hthetaStar.le hd_one htheta) hpi.le
    _ = weightedCost pi gamma d theta := by
      rw [weightedCost, ← hbalance, one_pow]
      ring

/-- The minimum coefficient in the real-power form of (A.11). -/
theorem theta_optimal_value : ThetaOptimalValue := by
  intro pi gamma d hpi hgamma hd
  have hratio : 0 ≤ weightRatio pi gamma := div_nonneg hgamma.le hpi.le
  rw [Real.rpow_neg hratio]
  exact (theta_optimal pi gamma d hpi hgamma hd).2.2

end JH.Analysis
