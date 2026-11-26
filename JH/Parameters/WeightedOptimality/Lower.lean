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
public import JH.Parameters.WeightedOptimality.LowerSpec

/-!
# Necessary conditions for weighted certificate loss

Minimize the grafting coefficient over positive weights before taking logarithms. The resulting
drift and intersection constraints give the two losses in (A.13), balanced in deriving (A.14).
The initial potential fixes the scale of their square-root contribution.

The flow inequality also forces `pi` to grow at least linearly in `n` whenever the loss is of
square-root size. This yields the coefficient of `log₂ n` in the lower side of (A.12).
-/

@[expose] public section

namespace JH.Parameters.WeightedLower

open JH.Analysis
open JH.Analysis.WeightedConstant

variable {p : Params} {q : ℕ} {theta : ℝ}

private theorem weighted_optimum_le (cert : p.WeightedPreCertificate q theta) :
    (p.Gamma : ℝ) * (1 + (p.nu : ℝ) ^ (-(1 / (p.d : ℝ)))) ^ p.d ≤ p.weightedCoefficient theta := by
  have piPos : 0 < (p.Pi : ℝ) := Nat.cast_pos.mpr (p.Pi_pos cert.admissible)
  have gammaPos : 0 < (p.Gamma : ℝ) := Nat.cast_pos.mpr (p.Gamma_pos cert.admissible cert.nu_choice)
  have ratio : weightRatio (p.Pi : ℝ) (p.Gamma : ℝ) = (p.nu : ℝ) := by
    rw [weightRatio, Params.Gamma, Nat.cast_mul, mul_comm (p.Pi : ℝ),
      mul_div_cancel_right₀ _ piPos.ne']
  have optimum := (theta_optimal (p.Pi : ℝ) (p.Gamma : ℝ) p.d piPos gammaPos
      cert.admissible.d_ge_two).2.1
    theta cert.theta_pos
  rw [theta_optimal_value (p.Pi : ℝ) (p.Gamma : ℝ) p.d piPos gammaPos cert.admissible.d_ge_two,
    ratio] at optimum
  exact optimum

/-- Positive weighted certificates must satisfy the drift and intersection power inequalities
obtained using the least grafting coefficient. -/
theorem power_requirements : WeightedLowerSpec.PowerRequirements := by
  intro p q theta cert
  let amplification := (1 + (p.nu : ℝ) ^ (-(1 / (p.d : ℝ)))) ^ p.d
  let gamma := (p.Gamma : ℝ)
  let U := (p.U : ℝ)
  let W := p.weightedCoefficient theta
  have gammaPos : 0 < gamma := Nat.cast_pos.mpr (p.Gamma_pos cert.admissible cert.nu_choice)
  have Upos : 0 < U := Nat.cast_pos.mpr p.U_pos
  have amplified : 0 ≤ amplification := by unfold amplification; positivity
  have optimum : gamma * amplification ≤ W := weighted_optimum_le cert
  have Wnonneg : 0 ≤ W := (mul_nonneg gammaPos.le amplified).trans optimum
  have PiNonneg : 0 ≤ (p.Pi : ℝ) := Nat.cast_nonneg _
  have psiEq : (p.Psi : ℝ) = 2 *
      gamma := by simp only [Params.Psi, Nat.cast_mul, Nat.cast_ofNat, gamma]
  have drift : 4 * (p.Theta : ℝ) * (W + (p.Pi : ℝ)) ≤ gamma * U := by
    simpa only [Params.weightedDriftNumerator, mul_assoc] using cert.drift
  -- Keep the optimized weighted contribution and use nonnegativity of the other terms.
  have driftDrop : (4 * (p.Theta : ℝ)) * (gamma * amplification) ≤ gamma * U :=
    (mul_le_mul_of_nonneg_left (show gamma * amplification ≤ W +
      (p.Pi : ℝ) by linarith only [optimum, PiNonneg])
      (by positivity)).trans drift
  have driftPart : 4 * (p.Theta : ℝ) * amplification ≤ U := by
    apply (mul_le_mul_iff_right₀ gammaPos).mp
    convert driftDrop using 1
    ring
  let prefactor := (2 : ℝ) ^ (p.lambda + 3) * (p.Psi : ℝ)
  let factor := p.intersectionFactor p.Psi 4 W
  have nonneg : 0 ≤ prefactor := by unfold prefactor; positivity
  have intersect : prefactor * factor ≤ U := cert.intersection
  have initialNonneg : 0 ≤ 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d := by positivity
  have otherNonneg : 0 ≤ 4 / U * (W + (p.Psi : ℝ) + 2 * (p.Pi : ℝ)) := by positivity
  have tailLe : 4 / U * (gamma * amplification) ≤ factor := by
    have middle : gamma * amplification ≤ W + (p.Psi : ℝ) + 2 * (p.Pi : ℝ) := by
      linarith only [optimum, (Nat.cast_nonneg p.Psi : 0 ≤ (p.Psi : ℝ)), PiNonneg]
    have compares := mul_le_mul_of_nonneg_left middle (show 0 ≤ 4 / U by positivity)
    change _ ≤ 4 + 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d + 4 / U * _
    linarith only [compares, initialNonneg]
  have usesTail : prefactor * (4 / U * (gamma * amplification)) ≤ U :=
    (mul_le_mul_of_nonneg_left tailLe nonneg).trans intersect
  have factorIdentity : prefactor * (4 / U * (gamma * amplification)) =
      (2 : ℝ) ^ (p.lambda + 6) * gamma ^ 2 * amplification / U := by
    unfold prefactor
    rw [psiEq, show p.lambda + 6 = (p.lambda + 3) + 3 by omega, pow_add]
    norm_num only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num]
    ring
  rw [factorIdentity] at usesTail
  have intersectionPart : (2 : ℝ) ^ (p.lambda + 6) * gamma ^ 2 * amplification ≤ U ^ 2 := by
    simpa only [pow_two] using (div_le_iff₀ Upos).mp usesTail
  have gammaPart : gamma ≤ U := by
    have factorOne : 1 ≤ factor := by
      change (1 : ℝ) ≤ 4 + 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d + 4 / U * _
      linarith only [initialNonneg, otherNonneg]
    have gammaPrefactor : gamma ≤ prefactor := calc
      _ ≤ (p.Psi : ℝ) := by rw [psiEq]; linarith only [gammaPos]
      _ = 1 * (p.Psi : ℝ) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)
    have prefactorLe : prefactor ≤ prefactor * factor := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left factorOne nonneg
    exact gammaPrefactor.trans (prefactorLe.trans intersect)
  exact ⟨driftPart, intersectionPart, gammaPart⟩

private theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ)), mul_one]

private theorem flow_exponents (cert : p.CommonCertificate q) : 2 * p.n ≤ p.h * p.s := by
  have base : (1 : ℕ) ≤ 2 * p.Pi ^ 2 := by
    have positive := p.Pi_pos cert.admissible
    exact Nat.succ_le_of_lt (by positivity)
  have limited : (2 : ℕ) ^ (2 * p.n) ≤ (p.U : ℕ) ^ p.h := by
    calc
      _ = (2 : ℕ) ^ (2 * p.n) * 1 * 1 := by simp
      _ ≤ (2 : ℕ) ^ (2 * p.n + p.lambda + 3) * p.h.factorial * (2 * p.Pi ^ 2) ^ p.h :=
        Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_right₀ (by decide) (by omega))
          (Nat.factorial_pos _)) (one_le_pow₀ base)
      _ ≤ _ := cert.flow
  rw [Params.U, ← pow_mul, Nat.mul_comm p.s p.h] at limited
  exact (Nat.pow_le_pow_iff_right (by decide)).mp limited

/-- Translate the optimized drift and intersection bounds to logarithmic losses, together with
the initial-potential and flow requirements. -/
theorem necessary : WeightedLowerSpec.Necessary := by
  intro p q theta cert
  let d := (p.d : ℝ)
  let x := Real.logb 2 (p.mu : ℝ)
  let y := Real.logb 2 (p.nu : ℝ) / d
  let r := x / d
  let a := 1 + (p.nu : ℝ) ^ (-(1 / d))
  let muMinus := ((p.mu - 1 : ℕ) : ℝ)
  change Real.logb 2 (p.pi : ℝ) + d * max (2 * r + g y) (r + y + g y / 2) ≤ (p.s : ℝ) ∧
    (p.n : ℝ) + 1 - (p.s : ℝ) ≤ d * x ∧ 2 * p.n ≤ p.h * p.s
  have two : (1 : ℝ) < 2 := by norm_num
  have dPos : 0 < d := Nat.cast_pos.mpr (by have := cert.admissible.d_ge_two; omega)
  have muAtLeastTwo : 2 ≤ (p.mu : ℝ) := by exact_mod_cast cert.admissible.mu_ge_two
  have muPos : 0 < (p.mu : ℝ) := by linarith only [muAtLeastTwo]
  have nuPos : 0 < (p.nu : ℝ) := Nat.cast_pos.mpr (Params.NuChoice.nu_pos cert.nu_choice)
  have piPos : 0 < (p.pi : ℝ) := Nat.cast_pos.mpr cert.admissible.pi_pos
  have aPos : 0 < a := by unfold a; positivity
  have dr : d * r = x := by unfold r; field_simp [dPos.ne']
  have dy : d * y = Real.logb 2 (p.nu : ℝ) := by unfold y; field_simp [dPos.ne']
  have logA : Real.logb 2 a = g y := by
    have exponent : -y = Real.logb 2 (p.nu : ℝ) * (-(1 / d)) := by unfold y; ring
    unfold a g
    rw [exponent, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) nuPos]
  have logN : Real.logb 2 (p.N : ℝ) = (p.n : ℝ) := by
    simp only [Params.N, Nat.cast_pow, Nat.cast_ofNat, logb_two_pow]
  have logU : Real.logb 2 (p.U : ℝ) = (p.s : ℝ) := by
    simp only [Params.U, Nat.cast_pow, Nat.cast_ofNat, logb_two_pow]
  have doubled : (p.mu : ℝ) ≤ 2 * muMinus := by
    unfold muMinus
    rw [Nat.cast_sub (by have := cert.admissible.mu_ge_two; omega), Nat.cast_one]
    linarith only [muAtLeastTwo]
  have thetaSize : (p.pi : ℝ) * (p.mu : ℝ) ^ 2 ≤ 4 * (p.Theta : ℝ) := by
    rw [Params.Theta, Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ (p.pi : ℝ) * (2 * muMinus) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ muPos.le doubled 2) piPos.le
      _ = _ := by unfold muMinus; ring
  have gammaSize : (p.pi : ℝ) * (p.mu : ℝ) * (p.nu : ℝ) ≤ 2 * (p.Gamma : ℝ) := by
    calc
      _ ≤ (p.pi : ℝ) * (2 * muMinus) * (p.nu : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left doubled piPos.le) nuPos.le
      _ = _ := by simp only [Params.Gamma, Params.Pi, Nat.cast_mul, muMinus]; ring
  obtain ⟨drift, intersect, gammaLe⟩ := power_requirements p q theta cert
  have firstPower : (p.pi : ℝ) * (p.mu : ℝ) ^ 2 * a ^ p.d ≤ (p.U : ℝ) :=
    (mul_le_mul_of_nonneg_right thetaSize (pow_nonneg aPos.le _)).trans drift
  have secondPower : ((p.pi : ℝ) * (p.mu : ℝ) * (p.nu : ℝ)) ^ 2 * a ^ p.d ≤ (p.U : ℝ) ^ 2 := by
    have four : (4 : ℝ) ≤ (2 : ℝ) ^ (p.lambda + 6) := calc
      _ = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ (2 * (p.Gamma : ℝ)) ^ 2 * a ^ p.d :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) gammaSize 2)
          (pow_nonneg aPos.le _)
      _ = 4 * (p.Gamma : ℝ) ^ 2 * a ^ p.d := by ring
      _ ≤ (2 : ℝ) ^ (p.lambda + 6) * (p.Gamma : ℝ) ^ 2 * a ^ p.d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right four (sq_nonneg _))
          (pow_nonneg aPos.le _)
      _ ≤ _ := intersect
  -- Taking base-two logarithms turns the weighted amplification into `d * g y`.
  have firstLoss : Real.logb 2 (p.pi : ℝ) + d * (2 * r + g y) ≤ (p.s : ℝ) := by
    have hlog := Real.logb_le_logb_of_le two (by positivity) firstPower
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul piPos.ne' (by positivity),
      Real.logb_pow, Real.logb_pow, logA, logU] at hlog
    have expanded : d * (2 * r + g y) = 2 * x + d * g y := calc
      _ = 2 * (d * r) + d * g y := by ring
      _ = _ := by rw [dr]
    rw [expanded]
    simpa only [Nat.cast_ofNat, add_assoc] using hlog
  have secondLoss : Real.logb 2 (p.pi : ℝ) + d * (r + y + g y / 2) ≤ (p.s : ℝ) := by
    have hlog := Real.logb_le_logb_of_le two (by positivity) secondPower
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_mul (by positivity) nuPos.ne', Real.logb_mul piPos.ne' muPos.ne',
      logA, Real.logb_pow, logU] at hlog
    have scaled : (2 : ℝ) * (Real.logb 2 (p.pi : ℝ) + d * (r + y + g y / 2)) =
        2 * (Real.logb 2 (p.pi : ℝ) + x + Real.logb 2 (p.nu : ℝ)) + d * g y := calc
      _ = 2 * (Real.logb 2 (p.pi : ℝ) + d * r + d * y) + d * g y := by ring
      _ = _ := by rw [dr, dy]
    have doubledLoss : (2 : ℝ) * (Real.logb 2 (p.pi : ℝ) + x + Real.logb 2 (p.nu : ℝ)) +
        d * g y ≤ 2 * (p.s : ℝ) := by simpa only [Nat.cast_ofNat] using hlog
    linarith only [doubledLoss, scaled]
  have balanceLoss : Real.logb 2 (p.pi : ℝ) + d * max (2 * r + g y)
      (r + y + g y / 2) ≤ (p.s : ℝ) := by
    rcases le_total (2 * r + g y) (r + y + g y / 2) with le | le
    · simpa only [max_eq_right le] using secondLoss
    · simpa only [max_eq_left le] using firstLoss
  -- The intersection bound gives `Gamma ≤ U`. Combined with the initial potential it gives the
  -- lower bound on `d * log₂ mu`.
  have initialPower : 2 * (p.N : ℝ) ≤ (p.U : ℝ) * (p.mu : ℝ) ^ p.d :=
    ((div_le_iff₀ (pow_pos muPos _)).mp cert.initial_potential).trans
      (mul_le_mul_of_nonneg_right gammaLe (pow_nonneg muPos.le _))
  have Npos : 0 < (p.N : ℝ) := Nat.cast_pos.mpr p.N_pos
  have Upos : 0 < (p.U : ℝ) := Nat.cast_pos.mpr p.U_pos
  have hlog := Real.logb_le_logb_of_le two (mul_pos (by norm_num) Npos) initialPower
  rw [Real.logb_mul (by norm_num) Npos.ne', Real.logb_mul Upos.ne' (by positivity),
    Real.logb_self_eq_one two, logN, logU, Real.logb_pow] at hlog
  refine ⟨balanceLoss, ?_, flow_exponents cert.toCommonCertificate⟩
  change 1 + (p.n : ℝ) ≤ (p.s : ℝ) + d * x at hlog
  linarith only [hlog]

private theorem logb_sqrt_bound {x : ℝ} (positive : 0 < x) :
    Real.logb 2 x ≤ (2 / Real.log 2) * Real.sqrt x := by
  have eq : Real.log x = 2 * Real.log (Real.sqrt x) := calc
    _ = Real.log (Real.sqrt x ^ 2) := congrArg Real.log (Real.sq_sqrt positive.le).symm
    _ = _ := by rw [Real.log_pow]; norm_num
  have small := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr positive)
  calc
    _ ≤ (2 * Real.sqrt x) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith only [eq, small]) (Real.log_nonneg (by norm_num))
    _ = _ := by ring

private theorem witness_length_le (p : Params) : (p.h : ℝ) ≤ 2 * Real.sqrt ((p.pi : ℝ) + 1) := by
  let a := 2 * Real.sqrt ((p.pi : ℝ) + 1)
  have nonneg : 0 ≤ a := by unfold a; positivity
  change (↑(⌈a⌉₊ - 2) : ℝ) ≤ a
  by_cases enough : 2 ≤ ⌈a⌉₊
  · rw [Nat.cast_sub enough]
    have ceiling := Nat.ceil_lt_add_one nonneg
    norm_num
    linarith only [ceiling]
  · have eq : ⌈a⌉₊ - 2 = 0 := by omega
    simpa only [eq, Nat.cast_zero] using nonneg

/-- At advantage one half, every weighted certificate pays at least `Cstar * sqrt n + log₂ n`
up to a uniform additive constant. -/
theorem uniform_lower : WeightedLowerSpec.UniformLower := by
  let B := Cstar + 1 + 2 / Real.log 2
  let K := Cstar * B + Real.logb 2 (2 * B ^ 2)
  have two : (1 : ℝ) < 2 := by norm_num
  have logTwo : 0 < Real.log 2 := Real.log_pos two
  have Cnn := Cstar_pos.le
  have Blarge : 1 ≤ B := by
    unfold B
    linarith only [Cnn, (show 0 ≤ (2 : ℝ) / Real.log 2 by positivity)]
  have Bpos : 0 < B := zero_lt_one.trans_le Blarge
  have Bsquare : 1 ≤ 2 * B ^ 2 := by
    have hsquare : 1 ≤ B ^ 2 := one_le_pow₀ Blarge
    linarith only [hsquare]
  refine ⟨K, add_nonneg (mul_nonneg Cnn Bpos.le) (Real.logb_nonneg two Bsquare), ?_⟩
  intro p q theta _ cert
  let x := Real.logb 2 (p.mu : ℝ)
  let d := (p.d : ℝ)
  let r := x / d
  let y := Real.logb 2 (p.nu : ℝ) / d
  let nRoot := Real.sqrt (p.n : ℝ)
  let piRoot := Real.sqrt ((p.pi : ℝ) + 1)
  have nPos : 0 < (p.n : ℝ) := Nat.cast_pos.mpr cert.admissible.n_pos
  have nRootPos : 0 < nRoot := Real.sqrt_pos.mpr nPos
  have nSquare : nRoot ^ 2 = (p.n : ℝ) := Real.sq_sqrt nPos.le
  have xPos : 0 < x := Real.logb_pos two (by
    have minimum : (2 : ℝ) ≤ (p.mu : ℝ) := by exact_mod_cast cert.admissible.mu_ge_two
    exact two.trans_le minimum)
  have dPos : 0 < d := Nat.cast_pos.mpr (by have := cert.admissible.d_ge_two; omega)
  have piOne : 1 ≤ (p.pi : ℝ) := by exact_mod_cast cert.admissible.pi_pos
  obtain ⟨balance, initial, flow⟩ := necessary p q theta cert
  have minmax := minmax_lower_bound r y (div_pos xPos dPos)
  have volume : d * x = d ^ 2 * r := by unfold r; field_simp [dPos.ne']
  have scale : d * (Cstar * Real.sqrt r) = Cstar * Real.sqrt (d * x) := by
    rw [volume, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq dPos.le]
    ring
  have paid : Real.logb 2 (p.pi : ℝ) + Cstar * Real.sqrt (d * x) ≤ (p.s : ℝ) := by
    rw [← scale]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left minmax dPos.le)).trans balance
  -- At square-root loss scale, the witness-count bound forces `pi` to be of order at least `n`.
  -- Above this loss scale, the desired lower bound follows directly.
  by_cases small : (p.s : ℝ) ≤ B * nRoot
  · have flowReal : 2 * (p.n : ℝ) ≤ (p.h : ℝ) * (p.s : ℝ) := by exact_mod_cast flow
    have countRoot : nRoot ≤ B * piRoot := by
      have nn : 0 < 2 * nRoot := by positivity
      apply (mul_le_mul_iff_left₀ nn).mp
      calc
        _ = 2 * (p.n : ℝ) := by rw [← nSquare]; ring
        _ ≤ (p.h : ℝ) * (p.s : ℝ) := flowReal
        _ ≤ (2 * piRoot) * (B * nRoot) :=
          mul_le_mul (witness_length_le p) small (Nat.cast_nonneg _) (by unfold piRoot; positivity)
        _ = _ := by ring
    have count : (p.n : ℝ) ≤ (2 * B ^ 2) * (p.pi : ℝ) := by
      calc
        _ = nRoot ^ 2 := nSquare.symm
        _ ≤ (B * piRoot) ^ 2 := pow_le_pow_left₀ nRootPos.le countRoot 2
        _ = B ^ 2 * ((p.pi : ℝ) +
          1) := by rw [mul_pow]; unfold piRoot; rw [Real.sq_sqrt (by positivity)]
        _ ≤ B ^ 2 * (2 * (p.pi : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith only [piOne]) (sq_nonneg B)
        _ = _ := by ring
    have logCount := Real.logb_le_logb_of_le two nPos count
    rw [Real.logb_mul (by positivity) (by linarith only [piOne] : (p.pi : ℝ) ≠ 0)] at logCount
    -- The initial-potential bound makes replacing `sqrt (d * log₂ mu)` by `sqrt n` cost only a
    -- bounded amount in this case.
    have rootLoss : nRoot ≤ Real.sqrt (d * x) + B := by
      by_cases tiny : nRoot ≤ B
      · linarith only [tiny, Real.sqrt_nonneg (d * x)]
      · have larger : B ≤ nRoot := (lt_of_not_ge tiny).le
        have prod : B ^ 2 ≤ B * nRoot := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left larger Bpos.le
        have loss : (nRoot - B) ^ 2 ≤ d * x := by
          change (p.n : ℝ) + 1 - (p.s : ℝ) ≤ d * x at initial
          nlinarith only [nSquare, small, prod, initial]
        have bounded := (Real.le_sqrt (sub_nonneg.mpr larger) (mul_nonneg dPos.le xPos.le)).mpr loss
        linarith only [bounded]
    have scaledRoot := mul_le_mul_of_nonneg_left rootLoss Cnn
    rw [mul_add] at scaledRoot
    change Cstar * nRoot + Real.logb 2 (p.n : ℝ) - (Cstar * B + Real.logb 2 (2 * B ^ 2)) ≤ (p.s : ℝ)
    linarith only [logCount, scaledRoot, paid]
  · have large : B * nRoot ≤ (p.s : ℝ) := (lt_of_not_ge small).le
    have logBound : Real.logb 2 (p.n : ℝ) ≤ (2 / Real.log 2) * nRoot := logb_sqrt_bound nPos
    have major : Cstar * nRoot + (2 / Real.log 2) * nRoot ≤ B * nRoot := by
      unfold B
      nlinarith only [nRootPos]
    have Knn : 0 ≤ K := add_nonneg (mul_nonneg Cnn Bpos.le) (Real.logb_nonneg two Bsquare)
    change Cstar * nRoot + Real.logb 2 (p.n : ℝ) - K ≤ (p.s : ℝ)
    linarith only [large, logBound, major, Knn]

end JH.Parameters.WeightedLower
