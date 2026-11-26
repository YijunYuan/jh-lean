/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.Convex
public import JH.Analysis.WeightedConstant
public import JH.Parameters.Certificate
public import JH.Parameters.WeightedOptimality.UpperSpec
public import Mathlib.Analysis.Complex.Exponential

/-!
# Rounded parameters for the weighted upper bound

At the minimizer y of (A.14), take Bpath = 4n and d = ⌈√(n/R(y))⌉. For the upper bound in
(A.12), this construction rounds log₂ μ to ⌈R(y)d⌉ and log₂ Binh to ⌈yd⌉. A sixteen-bit margin
in the loss absorbs the finite constants. Appendix A.4 uses the asymptotically equivalent
choice ⌈n/d⌉ for log₂ μ.
-/

@[expose] public section

namespace JH.Parameters.WeightedUpper

open Filter JH.Analysis JH.Analysis.WeightedConstant

private theorem y_pos {y : ℝ} (minimum : Minimizer y) : 0 < y := minimum.1.trans (R_lt_self y)

private theorem degree_lower {y : ℝ} (n : ℕ) :
    Real.sqrt (n : ℝ) / Real.sqrt (R y) ≤ (degree y n : ℝ) := by
  rw [← Real.sqrt_div (Nat.cast_nonneg n)]
  exact Nat.le_ceil _

private theorem degree_upper {y : ℝ} (n : ℕ) :
    (degree y n : ℝ) ≤ Real.sqrt (n : ℝ) / Real.sqrt (R y) + 1 := by
  rw [← Real.sqrt_div (Nat.cast_nonneg n)]
  exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le

private theorem log_four {n : ℕ} (positive : 0 < n) :
    Real.logb 2 (4 * (n : ℝ)) = 2 + Real.logb 2 (n : ℝ) := by
  have nPos : 0 < (n : ℝ) := Nat.cast_pos.mpr positive
  rw [Real.logb_mul (by norm_num) nPos.ne']
  congr 1
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- The ceilings and the sixteen-bit reserve add at most `2 * y + 19` to the leading square-root
and logarithmic loss. -/
theorem rounded_loss_bound : WeightedUpperSpec.LossBound := by
  intro y n minimum positive
  have posY := y_pos minimum
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast positive
  have logNonneg : 0 ≤ Real.logb 2 (4 * (n : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
  have sBound : ((parameters y n).s : ℝ) ≤
      2 * y * (degree y n : ℝ) + Real.logb 2 (4 * (n : ℝ)) + 16 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    _ ≤ 2 * y * (degree y n : ℝ) + Real.logb 2 (4 * (n : ℝ)) + 16 + 1 := sBound
    _ ≤ 2 * y * (Real.sqrt (n : ℝ) / Real.sqrt (R y) + 1) + Real.logb 2 (4 * (n : ℝ)) + 16 + 1 :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (degree_upper (y := y) n) (by positivity)) le_rfl) le_rfl) le_rfl
    _ = _ := by rw [log_four positive]; unfold objective; ring

/-- Reuse the zero-budget certificate with any fresh-query budget satisfying `QueryBudget` for
the same parameters. -/
theorem budget_transfer : WeightedUpperSpec.BudgetTransfer := by
  intro p theta q cert budget
  exact { cert with toCommonCertificate := {cert.toCommonCertificate with budget := budget} }

private theorem degree_at_least_two {y : ℝ} {n : ℕ} (minimum : Minimizer y) (large : 4 ≤ n) :
    2 ≤ degree y n := by
  have posR : 0 < R y := minimum.1
  have belowOne : R y ≤ 1 := ((R_lt_self y).trans (minimizer_lt_one minimum)).le
  have nGe : (4 : ℝ) ≤ n := by exact_mod_cast large
  have enlargement : (n : ℝ) ≤ (n : ℝ) / R y :=
    (le_div_iff₀ posR).mpr (mul_le_of_le_one_right (by positivity) belowOne)
  have root := Real.sqrt_le_sqrt (nGe.trans enlargement)
  have root4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [root4] at root
  have castBound : (2 : ℝ) ≤ (degree y n : ℝ) := root.trans (Nat.le_ceil _)
  exact_mod_cast castBound

private theorem admissible {y : ℝ} {n : ℕ} (minimum : Minimizer y) (large : 4 ≤ n) :
    (parameters y n).Admissible := by
  have dBig := degree_at_least_two minimum large
  have positiveR : 0 < R y := minimum.1
  have dPos : 0 < (degree y n : ℝ) := by exact_mod_cast (by omega : 0 < degree y n)
  have xPos : 1 ≤ muExponent y n := Nat.ceil_pos.mpr (mul_pos positiveR dPos)
  refine ⟨by change 1 ≤ n; omega, by change (1 : ℕ) ≤ 1; exact le_rfl, ?_, dBig, ?_⟩
  · change 2 ^ (1 : ℕ) ≤ 2 ^ muExponent y n
    exact Nat.pow_le_pow_right (by decide) xPos
  · change 1 ≤ 4 * n
    omega

private theorem initial_scale {y : ℝ} (n : ℕ) (minimum : Minimizer y) :
    (parameters y n).N ≤ (parameters y n).mu ^ (parameters y n).d := by
  have positiveR : 0 < R y := minimum.1
  have rootBound : Real.sqrt ((n : ℝ) / R y) ≤ (degree y n : ℝ) := Nat.le_ceil _
  have powerBound := pow_le_pow_left₀ (Real.sqrt_nonneg _) rootBound 2
  rw [Real.sq_sqrt (by positivity)] at powerBound
  have degreeBound := (div_le_iff₀ positiveR).mp powerBound
  have xBound := mul_le_mul_of_nonneg_right (Nat.le_ceil (R y * (degree y n : ℝ)))
    (Nat.cast_nonneg (degree y n) : (0 : ℝ) ≤ degree y n)
  have exponent : (n : ℝ) ≤ (muExponent y n : ℝ) * (degree y n : ℝ) := by
    calc
      _ ≤ (degree y n : ℝ) ^ 2 * R y := degreeBound
      _ = (R y * (degree y n : ℝ)) * (degree y n : ℝ) := by ring
      _ ≤ _ := xBound
  have natExponent : n ≤ muExponent y n * degree y n := by exact_mod_cast exponent
  change 2 ^ n ≤ (2 ^ muExponent y n) ^ degree y n
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide) natExponent

/-- The unrounded scale of `mu`. -/
private noncomputable def A (y : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (R y * (degree y n : ℝ))

/-- The unrounded scale of `nu`. -/
private noncomputable def B (y : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (y * (degree y n : ℝ))

/-- The optimized amplification at the unrounded ratio `y`. -/
private noncomputable def G (y : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (g y * (degree y n : ℝ))

private theorem scale_balance (y : ℝ) (n : ℕ) : (A y n) ^ 2 * G y n = (B y n) ^ 2 := by
  have twoPos : 0 < (2 : ℝ) := by norm_num
  calc
    _ = (2 : ℝ) ^ ((R y * (degree y n : ℝ)) * 2 + g y * (degree y n : ℝ)) := by
      rw [Real.rpow_add twoPos, Real.rpow_mul twoPos.le, Real.rpow_two]
      rfl
    _ = (2 : ℝ) ^ ((y * (degree y n : ℝ)) * 2) := by congr 1; unfold R; ring
    _ = _ := by rw [Real.rpow_mul twoPos.le, Real.rpow_two]; rfl

private theorem mu_le_scale {y : ℝ} (n : ℕ) (positiveR : 0 < R y) :
    ((parameters y n).mu : ℝ) ≤ 2 * A y n := by
  have exponent : (muExponent y n : ℝ) ≤ R y * (degree y n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    _ = (2 : ℝ) ^ (muExponent y n :
      ℝ) := by simp only [parameters, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (R y * (degree y n : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = _ := by unfold A; rw [Real.rpow_add_one (by norm_num)]; ring

private theorem scale_le_nu (y : ℝ) (n : ℕ) : B y n ≤ ((parameters y n).nu : ℝ) := by
  unfold B
  rw [show ((parameters y n).nu : ℝ) = (2 : ℝ) ^ (nuExponent y n : ℝ) by
    simp only [parameters, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)

private theorem nu_le_scale {y : ℝ} (n : ℕ) (positiveY : 0 < y) :
    ((parameters y n).nu : ℝ) ≤ 2 * B y n := by
  have exponent : (nuExponent y n : ℝ) ≤ y * (degree y n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    _ = (2 : ℝ) ^ (nuExponent y n :
      ℝ) := by simp only [parameters, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (y * (degree y n : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
    _ = _ := by unfold B; rw [Real.rpow_add_one (by norm_num)]; ring

private theorem scale_le_U {y : ℝ} {n : ℕ} (positive : 0 < n) :
    65536 * ((parameters y n).pi : ℝ) * (B y n) ^ 2 ≤ ((parameters y n).U : ℝ) := by
  have piPos : 0 < 4 * (n : ℝ) := by positivity
  have powLog := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) piPos
  have basePos : (0 : ℝ) < 2 := by norm_num
  calc
    _ = (2 : ℝ) ^ (2 * y * (degree y n : ℝ) + Real.logb 2 (4 * (n : ℝ)) + 16) := by
      rw [Real.rpow_add basePos, Real.rpow_add basePos, powLog,
        show 2 * y * (degree y n : ℝ) = (y * (degree y n : ℝ)) * 2 by ring,
        Real.rpow_mul basePos.le, Real.rpow_two,
        show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only [parameters, Nat.cast_mul, Nat.cast_ofNat, B]
      norm_num
      ring
    _ ≤ (2 : ℝ) ^ (loss y n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = _ := by simp only [parameters, Params.U, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]

private theorem pi_le_scale {y : ℝ} (n : ℕ) (positiveR : 0 < R y) :
    ((parameters y n).Pi : ℝ) ≤ 2 * ((parameters y n).pi : ℝ) * A y n := by
  let p := parameters y n
  have threshold : ((p.mu - 1 : ℕ) : ℝ) ≤ 2 * A y n :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (mu_le_scale n positiveR)
  calc
    _ = (p.pi : ℝ) * ((p.mu - 1 : ℕ) : ℝ) := by rw [Params.Pi, Nat.cast_mul]
    _ ≤ (p.pi : ℝ) * (2 * A y n) := mul_le_mul_of_nonneg_left threshold (by positivity)
    _ = _ := by ring

private theorem theta_le_scale {y : ℝ} (n : ℕ) (positiveR : 0 < R y) :
    ((parameters y n).Theta : ℝ) ≤ 4 * ((parameters y n).pi : ℝ) * (A y n) ^ 2 := by
  let p := parameters y n
  have threshold : ((p.mu - 1 : ℕ) : ℝ) ≤ 2 * A y n :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (mu_le_scale n positiveR)
  calc
    _ = (p.pi : ℝ) * (((p.mu - 1 : ℕ) : ℝ) ^ 2) := by rw [Params.Theta, Nat.cast_mul, Nat.cast_pow]
    _ ≤ (p.pi : ℝ) * (2 * A y n) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) threshold 2) (by positivity)
    _ = _ := by ring

private theorem gamma_le_scale {y : ℝ} (n : ℕ) (minimum : Minimizer y) :
    ((parameters y n).Gamma : ℝ) ≤ 4 * ((parameters y n).pi : ℝ) * A y n * B y n := by
  let p := parameters y n
  have step := mul_le_mul (pi_le_scale n minimum.1) (nu_le_scale n (y_pos minimum))
    (by positivity : 0 ≤ (p.nu : ℝ)) (by unfold A; positivity)
  calc
    _ = (p.Pi : ℝ) * (p.nu : ℝ) := by rw [Params.Gamma, Nat.cast_mul]
    _ ≤ _ := step
    _ = _ := by ring

private theorem scale_A_le_B {y : ℝ} (n : ℕ) : A y n ≤ B y n := by
  unfold A B
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right (R_lt_self y).le (by positivity))

private theorem G_ge_one (y : ℝ) (n : ℕ) : 1 ≤ G y n := by
  unfold G
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) (show 0 ≤ g y *
      (degree y n : ℝ) from mul_nonneg (g_pos y).le (by positivity))

private theorem optimized_weight_bound {y : ℝ} {n : ℕ} (minimum : Minimizer y) (large : 4 ≤ n) :
    0 < weight y n ∧ (parameters y n).weightedCoefficient (weight y n) ≤
      ((parameters y n).Gamma : ℝ) * G y n := by
  let p := parameters y n
  have valid := admissible minimum large
  have piPositive : 0 < (p.Pi : ℝ) := Nat.cast_pos.mpr (p.Pi_pos valid)
  have nuPositive : 0 < p.nu := by change 0 < 2 ^ nuExponent y n; positivity
  have gammaPositive : 0 < (p.Gamma : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (p.Pi_pos valid) nuPositive)
  have dPositive : 0 < (p.d : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) valid.d_ge_two)
  have ratio : weightRatio (p.Pi : ℝ) (p.Gamma : ℝ) = (p.nu : ℝ) := by
    unfold weightRatio Params.Gamma
    rw [Nat.cast_mul, mul_comm, mul_div_cancel_right₀ _ piPositive.ne']
  -- Rounding the exponent of `nu` upward can only decrease the reciprocal factor in the optimal
  -- weight cost.
  have inverseRate : (p.nu : ℝ) ^ (-(1 / (p.d : ℝ))) ≤ (2 : ℝ) ^ (-y) := by
    have nuEq : (p.nu : ℝ) = (2 : ℝ) ^ (nuExponent y n : ℝ) := by
      simp only [p, parameters, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    rw [nuEq, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have exponentBound : y * (p.d : ℝ) ≤ (nuExponent y n : ℝ) := Nat.le_ceil _
    have divided := (le_div_iff₀ dPositive).mpr exponentBound
    linarith only [divided, show (nuExponent y n : ℝ) * -(1 / (p.d : ℝ)) =
      -((nuExponent y n : ℝ) / (p.d : ℝ)) by ring]
  have amplify : (1 + (2 : ℝ) ^ (-y)) ^ p.d = G y n := by
    unfold G
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    unfold g
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    rfl
  refine ⟨(theta_optimal _ _ p.d piPositive gammaPositive valid.d_ge_two).1, ?_⟩
  change weightedCost (p.Pi : ℝ) (p.Gamma : ℝ) p.d
    (optimalTheta (p.Pi : ℝ) (p.Gamma : ℝ) p.d) ≤ (p.Gamma : ℝ) * G y n
  rw [theta_optimal_value _ _ _ piPositive gammaPositive valid.d_ge_two, ratio, ← amplify]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl inverseRate) p.d) gammaPositive.le

/-- Given the growth and flow conditions, the common reserve pays the remaining finite
certificate inequalities. -/
theorem certificate_from_growth : WeightedUpperSpec.CertificateFromGrowth := by
  intro y n minimum large
  dsimp only
  intro grows paidPi flow
  let p := parameters y n
  let pi : ℝ := (p.pi : ℝ)
  let gamma : ℝ := (p.Gamma : ℝ)
  let U : ℝ := (p.U : ℝ)
  let volume := pi * (B y n) ^ 2
  let W := p.weightedCoefficient (weight y n)
  have valid := admissible minimum large
  have nPositive : 0 < n := by omega
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have hU : 0 < U := Nat.cast_pos.mpr p.U_pos
  have reserve : 65536 * volume ≤ U := by
    simpa only [volume, pi, mul_assoc] using scale_le_U (y := y) nPositive
  have volumeNonneg : 0 ≤ volume := by dsimp [volume, pi]; positivity
  have balance := scale_balance y n
  have nonnegativeG : 0 ≤ G y n := (zero_le_one.trans (G_ge_one y n))
  have scaleTheta : (p.Theta : ℝ) ≤ 4 * pi * A y n ^ 2 := theta_le_scale n minimum.1
  have scalePi : (p.Pi : ℝ) ≤ 2 * pi * A y n := pi_le_scale n minimum.1
  have scaleGamma : gamma ≤ 4 * pi * A y n * B y n := gamma_le_scale n minimum
  obtain ⟨weightPos, scaleW⟩ := optimized_weight_bound minimum large
  have nuOne : 1 ≤ p.nu := by
    change 0 < 2 ^ nuExponent y n
    positivity
  have piGamma : p.Pi ≤ p.Gamma := by
    unfold Params.Gamma
    exact Nat.le_mul_of_pos_right p.Pi nuOne
  have piGammaReal : (p.Pi : ℝ) ≤ gamma := Nat.cast_le.mpr piGamma
  have gammaNonneg : 0 ≤ gamma := Nat.cast_nonneg _
  have gammaScale : gamma ≤ 4 * volume := by
    calc
      _ ≤ 4 * pi * A y n * B y n := scaleGamma
      _ ≤ 4 * pi * B y n * B y n := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (scale_A_le_B n)
          (by dsimp [pi]; positivity))
        unfold B
        positivity
      _ = _ := by dsimp only [volume]; ring
  -- The power balance moves the amplification `G` into the common scale of the intersection term.
  have gammaSquared : gamma ^ 2 * G y n ≤ 16 * volume ^ 2 := by
    calc
      _ ≤ (4 * pi * A y n * B y n) ^ 2 * G y n :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ gammaNonneg scaleGamma 2) nonnegativeG
      _ = 16 * (pi * B y n) ^ 2 * (A y n ^ 2 * G y n) := by ring
      _ = _ := by rw [balance]; dsimp only [volume]; ring
  have thresholdSquare : (p.Theta : ℝ) * G y n ≤ 4 * volume := by
    calc
      _ ≤ (4 * pi * A y n ^ 2) * G y n := mul_le_mul_of_nonneg_right scaleTheta nonnegativeG
      _ = 4 * pi * (A y n ^ 2 * G y n) := by ring
      _ = _ := by rw [balance]; dsimp only [volume]; ring
  have thresholdSmall : (p.Theta : ℝ) ≤ U := by
    calc
      _ ≤ (p.Theta : ℝ) * G y n := le_mul_of_one_le_right (by positivity) (G_ge_one y n)
      _ ≤ 4 * volume := thresholdSquare
      _ ≤ 65536 * volume := by linarith only [volumeNonneg]
      _ ≤ U := reserve
  -- The degree and exponent ceilings give `mu ^ d ≥ N`, which pays for the initial potential.
  have nOverMu : (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ 1 := by
    have almost := initial_scale n minimum
    have muPositive : 0 < (p.mu : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) valid.mu_ge_two)
    apply (div_le_iff₀ (pow_pos muPositive _)).mpr
    simpa only [one_mul, ← Nat.cast_pow] using (Nat.cast_le.mpr almost : (p.N : ℝ) ≤ ↑(p.mu ^ p.d))
  have gammaTwo : (2 : ℝ) ≤ gamma := by
    have piBig : 2 ≤ p.pi := by change 2 ≤ 4 * n; omega
    have growsPi : p.pi ≤ p.Pi := Nat.le_mul_of_pos_right _
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) valid.mu_ge_two))
    dsimp only [gamma]
    exact_mod_cast piBig.trans (growsPi.trans piGamma)
  have initialPotential : 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ gamma := by
    rw [mul_div_assoc]
    linarith only [nOverMu, gammaTwo]
  have drift : 4 * p.weightedDriftNumerator (weight y n) ≤ gamma * U := by
    have useBound : W + (p.Pi : ℝ) ≤ 2 * gamma * G y n := by
      calc
        _ ≤ gamma * G y n + gamma := add_le_add scaleW piGammaReal
        _ ≤ gamma * G y n + gamma * G y n :=
          add_le_add le_rfl (le_mul_of_one_le_right gammaNonneg (G_ge_one y n))
        _ = _ := by ring
    have thresholdReserve : 8 * (p.Theta : ℝ) * G y n ≤ U := by
      calc
        _ = 8 * ((p.Theta : ℝ) * G y n) := by ring
        _ ≤ 8 * (4 * volume) := mul_le_mul_of_nonneg_left thresholdSquare (by norm_num)
        _ ≤ 65536 * volume := by linarith only [volumeNonneg]
        _ ≤ U := reserve
    change 4 * ((p.Theta : ℝ) * (W + (p.Pi : ℝ))) ≤ gamma * U
    calc
      _ ≤ 4 * ((p.Theta : ℝ) * (2 * gamma * G y n)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left useBound (by positivity)) (by norm_num)
      _ = gamma * (8 * (p.Theta : ℝ) * G y n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left thresholdReserve gammaNonneg
  -- The growth condition `pi ≤ G` absorbs the extra factor of `pi` in the squared endpoint bound.
  have occupancyReserve : 18 * (p.Pi : ℝ) ^ 2 ≤ U := by
    calc
      _ ≤ 18 * (2 * pi * A y n) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) scalePi 2) (by norm_num)
      _ = (72 * pi * A y n ^ 2) * pi := by ring
      _ ≤ (72 * pi * A y n ^ 2) * G y n :=
        mul_le_mul_of_nonneg_left paidPi (by dsimp only [pi]; positivity)
      _ = 72 * volume := by
        rw [show (72 * pi * A y n ^ 2) * G y n = 72 * pi * (A y n ^ 2 * G y n) by ring, balance]
        dsimp only [volume]
        ring
      _ ≤ 65536 * volume := by linarith only [volumeNonneg]
      _ ≤ U := reserve
  have psiEq : (p.Psi : ℝ) = 2 *
      gamma := by unfold Params.Psi gamma; rw [Nat.cast_mul, Nat.cast_ofNat]
  have occupancyReal : 6 * (p.Pi : ℝ) * ((p.Psi : ℝ) + (p.Pi : ℝ)) ≤ (p.nu : ℝ) * U := by
    calc
      _ ≤ 6 * (p.Pi : ℝ) * (2 * gamma + gamma) := by
        rw [psiEq]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl piGammaReal) (by positivity)
      _ = (p.nu : ℝ) *
        (18 * (p.Pi : ℝ) ^ 2) := by unfold gamma Params.Gamma; rw [Nat.cast_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left occupancyReserve (by positivity)
  have occupancy : 6 * p.Pi * (p.Psi + p.Pi) ≤ p.nu * p.U := by
    dsimp only [U] at occupancyReal
    exact_mod_cast occupancyReal
  have intersection : p.IntersectionCondition p.Psi 4 W := by
    -- Allocate half the intersection budget to the constant part and half to the amplified growth
    -- term.
    have firstPart : 384 * gamma ≤ U := by
      calc
        _ ≤ 384 * (4 * volume) := mul_le_mul_of_nonneg_left gammaScale (by norm_num)
        _ ≤ 65536 * volume := by linarith only [volumeNonneg]
        _ ≤ U := reserve
    have secondPart : 1280 * (gamma ^ 2 * G y n) ≤ U ^ 2 := by
      calc
        _ ≤ 1280 * (16 * volume ^ 2) := mul_le_mul_of_nonneg_left gammaSquared (by norm_num)
        _ ≤ (65536 * volume) ^ 2 := by nlinarith only [sq_nonneg volume]
        _ ≤ U ^ 2 := pow_le_pow_left₀ (mul_nonneg (by norm_num) volumeNonneg) reserve 2
    have charge : W + (p.Psi : ℝ) + 2 * (p.Pi : ℝ) ≤ 5 * gamma * G y n := by
      rw [psiEq]
      have raise := le_mul_of_one_le_right gammaNonneg (G_ge_one y n)
      linarith only [scaleW, piGammaReal, raise]
    have factor : p.intersectionFactor p.Psi 4 W ≤ 6 + (20 / U) * gamma * G y n := by
      have ratioCharge := mul_le_mul_of_nonneg_left charge (show 0 ≤ 4 / U from by positivity)
      change 4 + 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d +
        (4 / U) * (W + (p.Psi : ℝ) + 2 * (p.Pi : ℝ)) ≤ _
      rw [mul_div_assoc]
      linarith only [ratioCharge, nOverMu,
        show (4 / U) * (5 * gamma * G y n) = (20 / U) * gamma * G y n by ring]
    have lambdaEq : p.lambda = 1 := rfl
    unfold Params.IntersectionCondition
    rw [show (2 : ℝ) ^ (p.lambda + 3) = 16 by norm_num [lambdaEq], psiEq]
    calc
      _ ≤ 16 * (2 * gamma) * (6 + (20 / U) * gamma * G y n) :=
        mul_le_mul_of_nonneg_left factor (by positivity)
      _ = 192 * gamma + 640 * (gamma ^ 2 * G y n) / U := by ring
      _ ≤ U / 2 + U / 2 := by
        apply add_le_add (by linarith only [firstPart])
        apply (div_le_iff₀ hU).mpr
        nlinarith only [secondPart]
      _ = _ := by ring
  have sLarge : 16 ≤ p.s := by
    have logNonneg : 0 ≤ Real.logb 2 (4 * (n : ℝ)) := Real.logb_nonneg (by norm_num) (by linarith)
    have lower : (16 : ℝ) ≤ (p.s : ℝ) := by
      have base : 0 ≤ 2 * y * (degree y n : ℝ) := by have := y_pos minimum; positivity
      exact (show 16 ≤ 2 * y * (degree y n : ℝ) + Real.logb 2 (4 * (n : ℝ)) + 16 by linarith).trans
        (Nat.le_ceil _)
    exact_mod_cast lower
  exact
    { admissible := valid
      budget := by unfold Params.QueryBudget; norm_num; positivity
      nu_choice := grows
      initial_potential := initialPotential
      endpoint_budget := Nat.cast_le.mp thresholdSmall
      flow := flow
      theta_pos := weightPos
      separation := by change 1 + 2 ≤ 2 * p.s; omega
      drift := drift
      occupancy := occupancy
      intersection := intersection }

-- The sixth term of the exponential series supplies a cubic in the length.
private theorem eventually_quadratic_le_rpow {a : ℝ} (aPos : 0 < a) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ (a * Real.sqrt (n : ℝ)) := by
  let b := Real.log 2 * a
  have bPos : 0 < b := mul_pos (Real.log_pos (by norm_num)) aPos
  filter_upwards [eventually_ge_atTop ⌈720 * c / b ^ 6⌉₊] with n nLarge
  have threshold : 720 * c / b ^ 6 ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr nLarge)
  have paid := (div_le_iff₀ (pow_pos bPos 6)).mp threshold
  have rootPower : Real.sqrt (n : ℝ) ^ 6 = (n : ℝ) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ (b * Real.sqrt (n : ℝ)) ^ 6 / 720 := by
      apply (le_div_iff₀ (by norm_num)).mpr
      rw [mul_pow, rootPower]
      calc
        _ = (720 * c) * (n : ℝ) ^ 2 := by ring
        _ ≤ ((n : ℝ) * b ^ 6) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right paid (by positivity)
        _ = _ := by ring
    _ ≤ Real.exp (b * Real.sqrt (n : ℝ)) := by
      simpa only [show ((6 : ℕ).factorial : ℝ) = 720 by norm_num [Nat.factorial]] using
        Real.pow_div_factorial_le_exp (b * Real.sqrt (n : ℝ))
          (mul_nonneg bPos.le (Real.sqrt_nonneg (n : ℝ))) 6
    _ = _ := by simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), b, mul_assoc]

private theorem nu_choice_of_gap {y : ℝ} {n : ℕ} (positiveR : 0 < R y) (large : 4 ≤ n)
    (gap : 256 * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ ((y - R y) * (degree y n : ℝ))) :
    (parameters y n).NuChoice := by
  let p := parameters y n
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have aOne : 1 ≤ A y n := by
    unfold A
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show 0 ≤ R y * (degree y n : ℝ) by positivity)
  have nSquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr nOne) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have nScale : (n : ℝ) ≤ (n : ℝ) ^ 2 * A y n :=
    nSquare.trans (le_mul_of_one_le_right (by positivity) aOne)
  have piEq : (p.pi : ℝ) = 4 * (n : ℝ) := by
    simp only [p, parameters, Nat.cast_mul, Nat.cast_ofNat]
  have product : ((n : ℝ) + 1) * (p.Pi : ℝ) ≤ 16 * (n : ℝ) ^ 2 * A y n := by
    calc
      _ ≤ (2 * (n : ℝ)) * (2 * (p.pi : ℝ) * A y n) :=
        mul_le_mul (by linarith only [nOne]) (pi_le_scale n positiveR)
          (by positivity) (by positivity)
      _ = _ := by rw [piEq]; ring
  have choice : (8 : ℝ) * (((n : ℝ) + 1) * (p.Pi : ℝ) + n + 1 + 4) ≤ (p.nu : ℝ) := by
    calc
      _ ≤ (256 * (n : ℝ) ^ 2) * A y n := by linarith only [product, nScale, nOne]
      _ ≤ (2 : ℝ) ^ ((y - R y) * (degree y n : ℝ)) * A y n :=
        mul_le_mul_of_nonneg_right gap (by unfold A; positivity)
      _ = B y n := by
        unfold A B
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      _ ≤ _ := scale_le_nu y n
  change 8 * ((n + 1) * p.Pi + n + 1 + 4) ≤ p.nu
  exact_mod_cast choice

private theorem witness_bounds {y : ℝ} {n : ℕ} (large : 4 ≤ n) :
    4 * Real.sqrt (n : ℝ) - 2 ≤ ((parameters y n).h : ℝ) ∧
    ((parameters y n).h : ℝ) ≤ 8 * (n : ℝ) := by
  let m := Real.sqrt (n : ℝ)
  let root := Real.sqrt (4 * (n : ℝ) + 1)
  let k := ⌈2 * root⌉₊
  have size : (parameters y n).h = k - 2 := by
    simp only [Params.h, parameters, Nat.cast_mul, Nat.cast_ofNat, k, root]
  have nLarge : (4 : ℝ) ≤ n := by exact_mod_cast large
  have mSquare : m ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have twoLeM : 2 ≤ m := Real.le_sqrt_of_sq_le (by linarith only [nLarge])
  have lowerRoot : 2 * m ≤ root := Real.le_sqrt_of_sq_le (by nlinarith only [mSquare])
  have lower : 4 * m ≤ (k : ℝ) :=
    (show 4 * m ≤ 2 * root by linarith only [lowerRoot]).trans (Nat.le_ceil _)
  have kTwo : 2 ≤ k := by
    exact_mod_cast (show (2 : ℝ) ≤ (k : ℝ) by linarith only [lower, twoLeM])
  have nSquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith only [nLarge])
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have upperRoot : root ≤ 4 * (n : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith only [nSquare, nLarge]⟩
  have ceilUpper : k ≤ 8 * n := Nat.ceil_le.mpr (by push_cast; linarith only [upperRoot])
  constructor
  · rw [size, Nat.cast_sub kTwo, Nat.cast_ofNat]
    exact sub_le_sub_right lower 2
  · have bound : k - 2 ≤ 8 * n := (Nat.sub_le _ _).trans ceilUpper
    rw [size]
    exact_mod_cast bound

private theorem flow_of_growth {y : ℝ} {n : ℕ} (positiveR : 0 < R y) (large : 4 ≤ n)
    (growth : (n : ℝ) ^ 2 * (2 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) ≤ G y n) :
    FlowCondition (parameters y n) := by
  let p := parameters y n
  let m := Real.sqrt (n : ℝ)
  obtain ⟨lower, upper⟩ := witness_bounds (y := y) large
  have nLarge : (4 : ℝ) ≤ n := by exact_mod_cast large
  have nPos : 0 < n := by omega
  have mSquare : m ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have twoLeM : 2 ≤ m := Real.le_sqrt_of_sq_le (by linarith only [nLarge])
  have exponent : ((2 * p.n + p.lambda + 3 : ℕ) : ℝ) ≤ (m / 2 + 4) * (p.h : ℝ) := by
    change ((2 * n + 1 + 3 : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (m / 2 + 4) * (4 * m - 2) := by nlinarith only [mSquare, twoLeM]
      _ ≤ _ := mul_le_mul_of_nonneg_left lower (by positivity)
  have piEq : (p.pi : ℝ) = 4 * (n : ℝ) := by
    simp only [p, parameters, Nat.cast_mul, Nat.cast_ofNat]
  have twoPos : (0 : ℝ) < 2 := by norm_num
  have flowBase : (2 : ℝ) ^ (m / 2 + 4) * (p.h : ℝ) * (2 * (p.Pi : ℝ) ^ 2) ≤ (p.U : ℝ) := by
    have piSquared := pow_le_pow_left₀ (Nat.cast_nonneg p.Pi : (0 : ℝ) ≤ p.Pi)
      (pi_le_scale n positiveR) 2
    calc
      _ ≤ (2 : ℝ) ^ (m / 2 + 4) * (8 * (n : ℝ)) * (2 * (2 * (p.pi : ℝ) * A y n) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left upper (by positivity))
          (mul_le_mul_of_nonneg_left piSquared (by norm_num)) (by positivity) (by positivity)
      _ = (4096 * (p.pi : ℝ) * A y n ^ 2) * ((n : ℝ) ^ 2 * (2 : ℝ) ^ (m / 2)) := by
        rw [Real.rpow_add twoPos, show (2 : ℝ) ^ (4 : ℝ) = 16 by norm_num [Real.rpow_ofNat], piEq]
        ring
      _ ≤ (4096 * (p.pi : ℝ) * A y n ^ 2) * G y n :=
        mul_le_mul_of_nonneg_left growth (by positivity)
      _ = 4096 * (p.pi : ℝ) * (B y n) ^ 2 := by rw [mul_assoc (4096 * (p.pi : ℝ)), scale_balance]
      _ ≤ 65536 * (p.pi : ℝ) * (B y n) ^ 2 := by gcongr; norm_num
      _ ≤ _ := scale_le_U (y := y) nPos
  -- The lower bound on witness length distributes the prefactor over the `h` witness steps.
  have expBound : (2 : ℝ) ^ (2 * p.n + p.lambda + 3 : ℕ) ≤ ((2 : ℝ) ^ (m / 2 + 4)) ^ p.h := by
    rw [← Real.rpow_natCast 2 (2 * p.n + p.lambda + 3), ← Real.rpow_mul_natCast twoPos.le]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) exponent
  have factorial : (p.h.factorial : ℝ) ≤ (p.h : ℝ) ^ p.h := by
    exact_mod_cast Nat.factorial_le_pow p.h
  have flow : (2 : ℝ) ^ (2 * p.n + p.lambda + 3 : ℕ) * (p.h.factorial : ℝ) *
      (2 * (p.Pi : ℝ) ^ 2) ^ p.h ≤ (p.U : ℝ) ^ p.h := by
    calc
      _ ≤ ((2 : ℝ) ^ (m / 2 + 4)) ^ p.h * (p.h : ℝ) ^ p.h * (2 * (p.Pi : ℝ) ^ 2) ^ p.h :=
        mul_le_mul_of_nonneg_right (mul_le_mul expBound factorial (by positivity)
          (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ (m / 2 + 4) * (p.h : ℝ) * (2 * (p.Pi : ℝ) ^ 2)) ^ p.h := by simp only [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) flowBase _
  unfold FlowCondition
  exact_mod_cast flow

/-- The strict exponent margins eventually supply the choice of `nu`, the bound on `pi`, and the
flow inequality. -/
theorem eventual_growth : WeightedUpperSpec.EventualGrowth := by
  intro y minimum
  -- The gap for `nu` and the strict flow slack each give a power of two growing faster than the
  -- relevant polynomial factors.
  let gap := (y - R y) / Real.sqrt (R y)
  let slack := g y / Real.sqrt (R y) - 1 / 2
  have gapPos : 0 < gap := div_pos (sub_pos.mpr (R_lt_self y)) (Real.sqrt_pos.mpr minimum.1)
  have slackPos : 0 < slack := sub_pos.mpr (flow_slack y minimum)
  filter_upwards [eventually_ge_atTop (4 : ℕ), eventually_quadratic_le_rpow gapPos 256,
    eventually_quadratic_le_rpow slackPos 1] with n large nuGrowth flowGrowth
  let p := parameters y n
  let m := Real.sqrt (n : ℝ)
  have gapExponent : gap * m ≤ (y - R y) * (degree y n : ℝ) := by
    calc
      _ = (y - R y) * (m / Real.sqrt (R y)) := by dsimp only [gap]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (degree_lower n) (sub_nonneg.mpr (R_lt_self y).le)
  have nuGap := nuGrowth.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) gapExponent)
  have slackExponent : slack * m + m / 2 ≤ g y * (degree y n : ℝ) := by
    calc
      _ = g y * (m / Real.sqrt (R y)) := by dsimp only [slack]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (degree_lower n) (g_pos y).le
  have flowGap : (n : ℝ) ^ 2 * (2 : ℝ) ^ (m / 2) ≤ G y n := by
    calc
      _ ≤ (2 : ℝ) ^ (slack * m) * (2 : ℝ) ^ (m / 2) :=
        mul_le_mul_of_nonneg_right (by simpa only [one_mul] using flowGrowth) (by positivity)
      _ = (2 : ℝ) ^ (slack * m + m / 2) := (Real.rpow_add (by norm_num) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) slackExponent
  have piSquare : (p.pi : ℝ) ≤ (n : ℝ) ^ 2 := by
    have nLarge : (4 : ℝ) ≤ n := by exact_mod_cast large
    simp only [p, parameters, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [mul_nonneg (sub_nonneg.mpr nLarge) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have powerOne : 1 ≤ (2 : ℝ) ^ (m / 2) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show 0 ≤ m / 2 by positivity)
  have paidPi : (p.pi : ℝ) ≤ G y n :=
    piSquare.trans ((le_mul_of_one_le_right (by positivity) powerOne).trans flowGap)
  exact ⟨nu_choice_of_gap minimum.1 large nuGap, paidPi, flow_of_growth minimum.1 large flowGap⟩

/-- At the minimizing argument, the rounded parameters eventually give a feasible certificate
with bounded additive loss. -/
theorem eventual_construction : WeightedUpperSpec.EventualConstruction := by
  intro y minimum
  filter_upwards [eventual_growth y minimum, eventually_ge_atTop (4 : ℕ)] with n growth large
  obtain ⟨nu, paidPi, flow⟩ := growth
  exact ⟨certificate_from_growth y n minimum large nu paidPi flow,
    rounded_loss_bound y n minimum (by omega)⟩

/-- The upper side of (A.12) for the weighted certificate, with leading coefficient `Cstar`. -/
theorem optimal_upper : WeightedUpperSpec.OptimalUpper := by
  obtain ⟨y, minimum, value⟩ := attainment
  refine ⟨2 * y + 19, by have := y_pos minimum; positivity, ?_⟩
  filter_upwards [eventual_construction y minimum] with n result
  obtain ⟨cert, lossBound⟩ := result
  exact ⟨parameters y n, weight y n, rfl, rfl, cert, by rwa [value] at lossBound⟩

end JH.Parameters.WeightedUpper
