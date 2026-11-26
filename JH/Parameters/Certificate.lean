/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Parameters.CertificateSpec
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite security certificates

The finite certificates of Theorem 2 and Appendix A.1 bound each stopping event by 2^(−λ−3).
The inherited and grafted populations enter through the common occupancy threshold in (24).
-/

@[expose] public section

namespace JH.Parameters.Params

variable {p : Params} {q L : ℕ} {theta : ℝ}

theorem N_pos (p : Params) : 0 < p.N := by
  unfold N
  positivity

theorem U_pos (p : Params) : 0 < p.U := by
  unfold U
  positivity

private theorem real_N_pos (p : Params) : 0 < (p.N : ℝ) := Nat.cast_pos.mpr p.N_pos

private theorem real_U_pos (p : Params) : 0 < (p.U : ℝ) := Nat.cast_pos.mpr p.U_pos

private theorem cast_N (p : Params) : (p.N : ℝ) = (2 : ℝ) ^ p.n := by simp [N]

private theorem cast_U (p : Params) : (p.U : ℝ) = (2 : ℝ) ^ p.s := by simp [U]

theorem Pi_pos (ha : p.Admissible) : 0 < p.Pi := by
  have hmu := ha.mu_ge_two
  exact Nat.mul_pos ha.pi_pos (by omega)

theorem NuChoice.nu_pos (hnu : p.NuChoice) : 0 < p.nu := by
  unfold NuChoice at hnu
  omega

theorem Gamma_pos (ha : p.Admissible) (hnu : p.NuChoice) : 0 < p.Gamma :=
  Nat.mul_pos (Pi_pos ha) hnu.nu_pos

/-- The last inequality in the counting argument of Lemma 3 implies that the witness size is at
least h. -/
theorem h_le_of_flow_grid {r : ℕ} (hr : (p.pi : ℝ) + 1 ≤ ((r : ℝ) + 2) ^ 2 / 4) : p.h ≤ r := by
  have hsqrt : Real.sqrt ((p.pi : ℝ) + 1) ≤ ((r : ℝ) + 2) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hr]
  have hceil : ⌈2 * Real.sqrt ((p.pi : ℝ) + 1)⌉₊ ≤ r + 2 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith only [hsqrt]
  unfold h
  omega

theorem h_pos (ha : p.Admissible) : 0 < p.h := by
  have hpi : (1 : ℝ) ≤ (p.pi : ℝ) := by exact_mod_cast ha.pi_pos
  have hroot : 1 < Real.sqrt ((p.pi : ℝ) + 1) := calc
    1 = Real.sqrt 1 := Real.sqrt_one.symm
    _ < _ := Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hceil : 2 < ⌈2 * Real.sqrt ((p.pi : ℝ) + 1)⌉₊ := by
    apply Nat.lt_ceil.mpr
    norm_num only [Nat.cast_ofNat]
    linarith only [hroot]
  unfold h
  omega

/-- Express the query budget as a bound on the fraction `q / N` of the word space. -/
theorem QueryBudget.fraction_le (hq : p.QueryBudget q) :
    (q : ℝ) / (p.N : ℝ) ≤ 1 / (p.U : ℝ) := by
  apply (div_le_div_iff₀ p.real_N_pos p.real_U_pos).mpr
  simpa only [one_mul] using (le_div_iff₀ p.real_U_pos).mp hq

theorem CommonCertificate.initial_potential_le (hc : p.CommonCertificate q) :
    (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ (p.Gamma : ℝ) / 2 := by
  have hstart := hc.initial_potential
  rw [mul_div_assoc] at hstart
  linarith only [hstart]

theorem CommonCertificate.endpoint_average_le (hc : p.CommonCertificate q) :
    (q : ℝ) * (p.Theta : ℝ) / (p.N : ℝ) ≤ 1 := by
  have htheta : (p.Theta : ℝ) ≤ (p.U : ℝ) := by exact_mod_cast hc.endpoint_budget
  calc
    _ = ((q : ℝ) / (p.N : ℝ)) * (p.Theta : ℝ) := by ring
    _ ≤ (1 / (p.U : ℝ)) * (p.Theta : ℝ) :=
      mul_le_mul_of_nonneg_right hc.budget.fraction_le (Nat.cast_nonneg _)
    _ = (p.Theta : ℝ) / (p.U : ℝ) := by ring
    _ ≤ 1 := (div_le_one p.real_U_pos).mpr htheta

private theorem drift_le {numerator : ℝ} (hq : p.QueryBudget q) (hnum : 0 ≤ numerator)
    (hbudget : 4 * numerator ≤ (p.Gamma : ℝ) * (p.U : ℝ)) :
    (q : ℝ) * (numerator / (p.N : ℝ)) ≤ (p.Gamma : ℝ) / 4 := by
  calc
    _ = ((q : ℝ) / (p.N : ℝ)) * numerator := by ring
    _ ≤ (1 / (p.U : ℝ)) * numerator := mul_le_mul_of_nonneg_right hq.fraction_le hnum
    _ = numerator / (p.U : ℝ) := by ring
    _ ≤ (p.Gamma : ℝ) / 4 := by
      apply (div_le_div_iff₀ p.real_U_pos (by norm_num)).mpr
      simpa only [mul_comm] using hbudget

theorem PreCertificate.cumulative_drift_le (hc : p.PreCertificate q) :
    (q : ℝ) * ((p.driftNumerator : ℝ) / (p.N : ℝ)) ≤ (p.Gamma : ℝ) / 4 :=
  drift_le hc.budget (Nat.cast_nonneg _) (by exact_mod_cast hc.drift)

theorem SPRCertificate.cumulative_drift_le (hc : p.SPRCertificate q L) :
    (q : ℝ) * ((p.driftNumerator : ℝ) / (p.N : ℝ)) ≤ (p.Gamma : ℝ) / 4 :=
  drift_le hc.budget (Nat.cast_nonneg _) (by exact_mod_cast hc.drift)

theorem WeightedPreCertificate.cumulative_drift_le (hc : p.WeightedPreCertificate q theta) :
    (q : ℝ) * (p.weightedDriftNumerator theta / (p.N : ℝ)) ≤ (p.Gamma : ℝ) / 4 := by
  have htheta := hc.theta_pos
  apply drift_le hc.budget _ hc.drift
  unfold weightedDriftNumerator weightedCoefficient JH.Analysis.weightedCost
  positivity

private theorem separationTail_le_square (p : Params) (q : ℕ) :
    p.separationTail q ≤ ((q : ℝ) / (p.N : ℝ)) ^ 2 / 2 := by
  unfold separationTail
  rw [div_pow, div_div, mul_comm ((p.N : ℝ) ^ 2) 2, pow_two (q : ℝ)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (Nat.cast_nonneg _)) (by positivity)

private theorem separation_le (hq : p.QueryBudget q) (hs : p.lambda + 2 ≤ 2 * p.s) :
    p.separationTail q ≤ p.tailBudget := by
  calc
    _ ≤ ((q : ℝ) / (p.N : ℝ)) ^ 2 / 2 := separationTail_le_square p q
    _ ≤ (1 / (p.U : ℝ)) ^ 2 / 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hq.fraction_le _) (by norm_num)
    _ = ((2 : ℝ) ^ (2 * p.s + 1))⁻¹ := by
      rw [p.cast_U, div_pow, one_pow, ← pow_mul, Nat.mul_comm p.s 2,
        div_div, ← pow_succ, one_div]
    _ ≤ p.tailBudget := by
      unfold tailBudget
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))

theorem PreCertificate.separation_tail_le (hc : p.PreCertificate q) :
    p.separationTail q ≤ p.tailBudget := separation_le hc.budget hc.separation

theorem WeightedPreCertificate.separation_tail_le (hc : p.WeightedPreCertificate q theta) :
    p.separationTail q ≤ p.tailBudget := separation_le hc.budget hc.separation

/-- The separation bound uses both the original `ell` accesses and the later `q` fresh accesses. -/
theorem SPRCertificate.separation_tail_le (hc : p.SPRCertificate q L) {ell : ℕ} (hell : ell ≤ L) :
    p.separationTail (q + ell) ≤ p.tailBudget := by
  have hL : (L : ℝ) * (p.U : ℝ) ≤ (p.N : ℝ) := by exact_mod_cast hc.length_budget
  have hellBudget : p.QueryBudget ell :=
    le_trans (Nat.cast_le.mpr hell) ((le_div_iff₀ p.real_U_pos).mpr hL)
  -- The query and length budgets each contribute at most `1 / U` to the fraction of the word
  -- space.
  have hsum : ((q + ell : ℕ) : ℝ) / (p.N : ℝ) ≤ 2 / (p.U : ℝ) := by
    rw [Nat.cast_add, add_div, ← one_add_one_eq_two, add_div]
    exact add_le_add hc.budget.fraction_le hellBudget.fraction_le
  have hsep := hc.separation
  have hpow : (2 : ℝ) ^ ((p.lambda + 3) + 1) ≤ (p.U : ℝ) ^ 2 := by
    rw [p.cast_U, ← pow_mul]
    exact pow_le_pow_right₀ one_le_two (by omega)
  calc
    _ ≤ (((q + ell : ℕ) : ℝ) / (p.N : ℝ)) ^ 2 / 2 := separationTail_le_square p (q + ell)
    _ ≤ (2 / (p.U : ℝ)) ^ 2 / 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsum _) (by norm_num)
    _ = 2 / (p.U : ℝ) ^ 2 := by rw [div_pow]; ring
    _ ≤ p.tailBudget := by
      unfold tailBudget
      rw [← one_div]
      apply (div_le_div_iff₀ (pow_pos p.real_U_pos _) (by positivity)).mpr
      simpa only [pow_succ', one_mul] using hpow

/-- The integer flow condition pays the witness-count tail to the common probability budget. -/
theorem CommonCertificate.flow_tail_le (hc : p.CommonCertificate q) :
    p.flowTail ≤ p.tailBudget := by
  have hflow : (2 : ℝ) ^ (2 * p.n + p.lambda + 3) * (p.h.factorial : ℝ) *
      (2 * (p.Pi : ℝ) ^ 2) ^ p.h ≤ (p.U : ℝ) ^ p.h := by exact_mod_cast hc.flow
  unfold flowTail tailBudget
  rw [div_pow, ← mul_div_assoc, ← one_div]
  apply (div_le_div_iff₀ (pow_pos p.real_U_pos _) (by positivity)).mpr
  rw [one_mul]
  calc
    _ = (2 : ℝ) ^ (2 * p.n + p.lambda + 3) * (p.h.factorial : ℝ) *
        (2 * (p.Pi : ℝ) ^ 2) ^ p.h := by
      rw [p.cast_N, ← pow_mul, Nat.mul_comm p.n 2,
        show 2 * p.n + p.lambda + 3 = 2 * p.n + (p.lambda + 3) by omega,
        pow_add (2 : ℝ) (2 * p.n) (p.lambda + 3)]
      ring
    _ ≤ _ := hflow

theorem IntersectionCondition.tail_le {psi : ℕ} {initial coefficient : ℝ}
    (hc : p.IntersectionCondition psi initial coefficient) :
    p.intersectionTail psi initial coefficient ≤ p.tailBudget := by
  unfold IntersectionCondition at hc
  unfold intersectionTail tailBudget
  rw [div_mul_eq_mul_div, ← one_div]
  apply (div_le_div_iff₀ p.real_U_pos (by positivity)).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm, one_mul] using hc

/-- The length certificate pays the probability of a capacity collision during the original
evaluation. -/
theorem SPRCertificate.collision_tail_le (hc : p.SPRCertificate q L) {ell : ℕ} (hell : ell ≤ L) :
    p.collisionTail ell ≤ p.tailBudget := by
  have hlength : (ell : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hell
  have hcert : (2 : ℝ) ^ (p.lambda + 2) * (L : ℝ) * ((L : ℝ) + 1) ≤ (p.N : ℝ) := by
    exact_mod_cast hc.collision
  unfold collisionTail tailBudget
  rw [← one_div]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) p.real_N_pos) (by positivity)).mpr
  rw [one_mul]
  calc
    _ ≤ (L : ℝ) * ((L : ℝ) + 1) * (2 : ℝ) ^ (p.lambda + 3) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hlength (add_le_add hlength le_rfl) (by positivity) (by positivity))
        (by positivity)
    _ = 2 * ((2 : ℝ) ^ (p.lambda + 2) * (L : ℝ) * ((L : ℝ) + 1)) := by
      rw [show p.lambda + 3 = (p.lambda + 2) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcert (by norm_num)

theorem tailBudget_eq_rpow (p : Params) : p.tailBudget = (2 : ℝ) ^ (-(p.lambda : ℝ) - 3) := by
  unfold tailBudget
  rw [show -(p.lambda : ℝ) - 3 = -((p.lambda + 3 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- The choice of `nu` absorbs the number of possible patterns in the potential-barrier bound. -/
theorem NuChoice.barrier_tail_le (hnu : p.NuChoice) : p.barrierTail ≤ p.tailBudget := by
  let k := (p.n + 1) * p.Pi + p.n + p.lambda + 4
  let m := (p.n + 1) * p.Pi + p.n + 1
  have hkNat : 8 * k ≤ p.nu := hnu
  have hk : (8 : ℝ) * (k : ℝ) ≤ (p.nu : ℝ) := by exact_mod_cast hkNat
  have hpower : (2 : ℝ) ^ (-(p.nu : ℝ) / 8) ≤ ((2 : ℝ) ^ k)⁻¹ := by
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hk])
  have hN_one : (1 : ℝ) ≤ (p.N : ℝ) := by
    rw [p.cast_N]
    exact one_le_pow₀ (by norm_num)
  have hN_succ : (p.N : ℝ) + 1 ≤ (2 : ℝ) ^ (p.n + 1) := by
    rw [pow_succ, ← p.cast_N]
    linarith only [hN_one]
  -- Bound the two orientations and the possible patterns by a power of two.
  have hcoefficient : 2 * (p.N : ℝ) * ((p.N : ℝ) + 1) ^ p.Pi ≤ (2 : ℝ) ^ m := by
    calc
      _ ≤ 2 * (p.N : ℝ) * ((2 : ℝ) ^ (p.n + 1)) ^ p.Pi :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hN_succ _) (by positivity)
      _ = _ := by
        rw [p.cast_N, ← pow_mul, show m = (p.n + 1) * p.Pi + (p.n + 1) by dsimp [m]; omega,
          pow_add (2 : ℝ) ((p.n + 1) * p.Pi) (p.n + 1), pow_succ (2 : ℝ) p.n]
        ring
  calc
    p.barrierTail ≤ (2 * (p.N : ℝ) * ((p.N : ℝ) + 1) ^ p.Pi) * ((2 : ℝ) ^ k)⁻¹ :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ k)⁻¹ := mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ = p.tailBudget := by
      rw [tailBudget, show k = m + (p.lambda + 3) by dsimp [k, m]; omega,
        pow_add (2 : ℝ) m (p.lambda + 3), mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (by positivity), one_mul]

private theorem factorial_lower (r : ℕ) : ((r : ℝ) / 3) ^ r ≤ (r.factorial : ℝ) := by
  have hseries := Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r
  have h_exp : Real.exp (r : ℝ) ≤ (3 : ℝ) ^ r := by
    rw [← mul_one (r : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hfactorial_pos : 0 < (r.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos r)
  have hbound := (div_le_iff₀ hfactorial_pos).mp (hseries.trans h_exp)
  rw [div_pow]
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hbound)

private theorem occupancy_le {psi : ℕ} (hnu : p.NuChoice) (hq : p.QueryBudget q)
    (hcond : 6 * p.Pi * (psi + p.Pi) ≤ p.nu * p.U) :
    p.occupancyTail q psi ≤ p.tailBudget := by
  let a : ℝ := (p.Pi : ℝ) * ((psi : ℝ) + (p.Pi : ℝ))
  have ha : 0 ≤ a := by positivity
  have hcondR : (6 : ℝ) * (p.Pi : ℝ) * ((psi : ℝ) + (p.Pi : ℝ)) ≤
      (p.nu : ℝ) * (p.U : ℝ) := by exact_mod_cast hcond
  have hstep : (q : ℝ) * (a / (p.N : ℝ)) ≤ (p.nu : ℝ) / 6 := by
    calc
      _ = ((q : ℝ) / (p.N : ℝ)) * a := by ring
      _ ≤ (1 / (p.U : ℝ)) * a := mul_le_mul_of_nonneg_right hq.fraction_le ha
      _ = a / (p.U : ℝ) := by ring
      _ ≤ (p.nu : ℝ) / 6 := by
        apply (div_le_div_iff₀ p.real_U_pos (by norm_num)).mpr
        dsimp [a]
        nlinarith only [hcondR]
  have hchoose : (q.choose p.nu : ℝ) ≤ (q : ℝ) ^ p.nu / (p.nu.factorial : ℝ) := by
    exact_mod_cast Nat.choose_le_pow_div (α := ℝ) p.nu q
  -- The factorial lower bound makes the one-row or one-column tail at most `2 ^ (-nu)` before the
  -- union bound.
  have hsingle : (q.choose p.nu : ℝ) * (a / (p.N : ℝ)) ^ p.nu ≤ ((2 : ℝ) ^ p.nu)⁻¹ := by
    calc
      _ ≤ ((q : ℝ) ^ p.nu / (p.nu.factorial : ℝ)) * (a / (p.N : ℝ)) ^ p.nu :=
        mul_le_mul_of_nonneg_right hchoose (by positivity)
      _ = ((q : ℝ) * (a / (p.N : ℝ))) ^ p.nu / (p.nu.factorial : ℝ) := by
        rw [mul_pow]
        ring
      _ ≤ ((p.nu : ℝ) / 6) ^ p.nu / (p.nu.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hstep _) (by positivity)
      _ = (((p.nu : ℝ) / 3) ^ p.nu / (p.nu.factorial : ℝ)) * ((2 : ℝ) ^ p.nu)⁻¹ := by
        rw [show (p.nu : ℝ) / 6 = ((p.nu : ℝ) / 3) / 2 by ring, div_pow]
        ring
      _ ≤ _ := by
        have hfactorial : ((p.nu : ℝ) / 3) ^ p.nu / (p.nu.factorial : ℝ) ≤ 1 :=
          (div_le_one (Nat.cast_pos.mpr (Nat.factorial_pos _))).mpr (factorial_lower p.nu)
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hfactorial (by positivity : 0 ≤ ((2 : ℝ) ^ p.nu)⁻¹)
  calc
    p.occupancyTail q psi ≤ 2 * (p.N : ℝ) * ((2 : ℝ) ^ p.nu)⁻¹ :=
      mul_le_mul_of_nonneg_left hsingle (by positivity)
    _ ≤ p.tailBudget := by
      rw [← div_eq_mul_inv, tailBudget, ← one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [one_mul, p.cast_N, mul_comm 2, ← pow_succ, ← pow_add]
      apply pow_le_pow_right₀ one_le_two
      unfold NuChoice at hnu
      omega

theorem PreCertificate.occupancy_tail_le (hc : p.PreCertificate q) :
    p.occupancyTail q p.Psi ≤ p.tailBudget := occupancy_le hc.nu_choice hc.budget hc.occupancy

theorem WeightedPreCertificate.occupancy_tail_le (hc : p.WeightedPreCertificate q theta) :
    p.occupancyTail q p.Psi ≤ p.tailBudget := occupancy_le hc.nu_choice hc.budget hc.occupancy

theorem SPRCertificate.occupancy_tail_le (hc : p.SPRCertificate q L) :
    p.occupancyTail q (p.sprPsi L) ≤ p.tailBudget := by
  have hnu_one : 1 ≤ p.nu := hc.nu_choice.nu_pos
  have hgamma : p.Pi ≤ p.Gamma := by
    unfold Gamma
    simpa only [mul_one] using Nat.mul_le_mul_left p.Pi hnu_one
  have hpsi : p.Pi ≤ p.sprPsi L := by
    unfold sprPsi
    omega
  apply occupancy_le hc.nu_choice hc.budget
  calc
    _ ≤ 6 * p.Pi * (2 * p.sprPsi L) := Nat.mul_le_mul_left _ (by omega)
    _ = 12 * p.Pi * p.sprPsi L := by ring
    _ ≤ _ := hc.occupancy

end JH.Parameters.Params
