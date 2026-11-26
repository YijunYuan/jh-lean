/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Parameters.Certificate
public import JH.Parameters.UniformSpec

/-!
# Uniform equal-weight parameter choices

In (37), choose `mu = 2 ^ x` and a degree at least `ceil (n / x)`, so `mu ^ d` covers the word
space. The loss in the certificate absorbs the common scale of the remaining constraints.

`explicit_certificate` instantiates these choices at `x = ceil (sqrt (n / 2))` and the
advantage exponent `floor (sqrt (2 * n))`, giving the budget in the square-root specialization
of (39).
-/

@[expose] public section

namespace JH.Parameters

open Params

private theorem two_pow_le {a b : ℕ} (h : a ≤ b) : (2 : ℕ) ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private theorem le_pow_uniformLog {n : ℕ} (hn : 0 < n) : n ≤ 2 ^ uniformLog n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hceil := Nat.le_ceil (Real.log (n : ℝ) / Real.log 2)
  have hcompare : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ uniformLog n) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog).mp hceil
  exact_mod_cast (Real.log_le_log_iff hnreal (by positivity)).mp hcompare

private theorem uniformPower_mul_ge {n x : ℕ} (hx : 0 < x) :
    n ≤ x * uniformPower n x := by
  have hxreal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hceil := Nat.le_ceil ((n : ℝ) / (x : ℝ))
  have hcross := (div_le_iff₀ hxreal).mp hceil
  have h : n ≤ ⌈(n : ℝ) / (x : ℝ)⌉₊ * x := by exact_mod_cast hcross
  calc
    n ≤ x * ⌈(n : ℝ) / (x : ℝ)⌉₊ := by simpa [Nat.mul_comm] using h
    _ ≤ x * uniformPower n x := Nat.mul_le_mul_left _ (le_max_right _ _)

private theorem uniform_witness_size {n x lambda s : ℕ} (hn : 4 ≤ n) :
    (uniformParamsAt n x lambda s).h = 2 * n - 1 := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hroot := Real.sq_sqrt (show 0 ≤ (n : ℝ) ^ 2 + 1 by positivity)
  have hpos := Real.sqrt_nonneg ((n : ℝ) ^ 2 + 1)
  have hlow : 2 * (n : ℝ) < 2 * Real.sqrt ((n : ℝ) ^ 2 + 1) := by
    by_contra! hh
    have hn' : 0 ≤ (n : ℝ) := by positivity
    have hsq := mul_nonneg (show 0 ≤ (n : ℝ) - Real.sqrt ((n : ℝ) ^ 2 + 1) by linarith)
      (add_nonneg hn' hpos)
    nlinarith
  have hhigh : 2 * Real.sqrt ((n : ℝ) ^ 2 + 1) ≤ 2 * (n : ℝ) + 1 := by
    by_contra! hh
    have hsq := mul_pos (show 0 < Real.sqrt ((n : ℝ) ^ 2 + 1) - ((n : ℝ) + 1 / 2) by
      linarith) (show 0 < Real.sqrt ((n : ℝ) ^ 2 + 1) + ((n : ℝ) + 1 / 2) by linarith)
    nlinarith
  have hceil : ⌈2 * Real.sqrt ((n : ℝ) ^ 2 + 1)⌉₊ = 2 * n + 1 := by
    apply (Nat.ceil_eq_iff (by omega)).2
    rw [Nat.add_sub_cancel]
    push_cast
    exact ⟨hlow, hhigh⟩
  unfold Params.h
  simp only [uniformParamsAt, Nat.cast_pow]
  rw [hceil]
  omega

private theorem certificate_at_loss {n x lambda s q : ℕ}
    (hn : 4 ≤ n) (hx : 1 ≤ x) (hlambda : 1 ≤ lambda) (hlambdaN : lambda ≤ n)
    (hs : uniformLossFor n x lambda ≤ s) (hq : q * 2 ^ s ≤ 2 ^ n) :
    (uniformParamsAt n x lambda s).PreCertificate q := by
  let p := uniformParamsAt n x lambda s
  change p.PreCertificate q
  have hnpos : 0 < n := by omega
  have hmu : 2 ≤ p.mu := two_pow_le hx
  have hd : 2 ≤ p.d := le_max_left _ _
  have hpi : 1 ≤ p.pi := by
    change 1 ≤ n ^ 2
    exact Nat.pow_pos hnpos
  have ha : p.Admissible := ⟨show 1 ≤ n by omega, hlambda, hmu, hd, hpi⟩
  have hnu : p.NuChoice := le_rfl
  have hnu_one : 1 ≤ p.nu := hnu.nu_pos
  have hPiN : n ^ 2 ≤ p.Pi := by
    rw [Params.Pi, ← mul_one (n ^ 2)]
    exact Nat.mul_le_mul_left _ (by omega)
  have hPi : 1 ≤ p.Pi := p.Pi_pos ha
  have hPiGamma : p.Pi ≤ p.Gamma := by
    simpa only [Params.Gamma, mul_one] using Nat.mul_le_mul_left p.Pi hnu_one
  have hTheta : p.Theta ≤ p.Pi ^ 2 := by
    rw [Params.Theta, Params.Pi, mul_pow]
    exact Nat.mul_le_mul_right _ (by
      simpa only [mul_one, pow_two] using Nat.mul_le_mul_left p.pi hpi)
  -- Use a common scale for the potential threshold and the factors in the flow, occupancy and
  -- intersection bounds.
  let scale := n * p.Pi ^ 2
  have hPiScale : p.Pi ≤ scale := by
    calc
      p.Pi = 1 * (1 * p.Pi) := by simp
      _ ≤ n * p.Pi ^ 2 := by rw [pow_two]; gcongr; omega
  have hPiSqScale : p.Pi ^ 2 ≤ scale := by
    have hnOne : 1 ≤ n := hnpos
    simpa only [one_mul] using Nat.mul_le_mul_right (p.Pi ^ 2) hnOne
  have hNuUpper : p.nu ≤ 16 * n * p.Pi := by
    have hnPi : n ≤ p.Pi := by
      calc
        n = n * 1 := by simp
        _ ≤ n ^ 2 := by rw [pow_two]; gcongr; omega
        _ ≤ p.Pi := hPiN
    have hsmall : n + lambda + 4 ≤ (n - 1) * p.Pi := by
      calc
        n + lambda + 4 ≤ 3 * n := by omega
        _ ≤ (n - 1) * p.Pi := by gcongr; omega
    change 8 * ((n + 1) * p.Pi + n + lambda + 4) ≤ 16 * n * p.Pi
    calc
      _ ≤ 8 * ((n + 1) * p.Pi + (n - 1) * p.Pi) := by
        rw [show (n + 1) * p.Pi + n + lambda + 4 =
          (n + 1) * p.Pi + (n + lambda + 4) by ring]
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hsmall _)
      _ = 16 * n * p.Pi := by
        rw [← add_mul, show n + 1 + (n - 1) = 2 * n by omega]
        ring
  have hGammaUpper : p.Gamma ≤ 16 * scale := by
    calc
      p.Gamma ≤ p.Pi * (16 * n * p.Pi) := Nat.mul_le_mul_left _ hNuUpper
      _ = 16 * scale := by dsimp [scale]; ring
  have hPsiUpper : p.Psi ≤ 32 * scale := by
    calc
      p.Psi ≤ 2 * (16 * scale) := Nat.mul_le_mul_left _ hGammaUpper
      _ = 32 * scale := by ring
  have hPiUpper : p.Pi ≤ n ^ 2 * 2 ^ x :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hScaleUpper : scale ≤ 2 ^ (2 * x + 5 * uniformLog n) := by
    calc
      scale ≤ n * (n ^ 2 * 2 ^ x) ^ 2 := by dsimp [scale]; gcongr
      _ = 2 ^ (2 * x) * n ^ 5 := by rw [Nat.mul_comm 2 x, pow_mul]; ring
      _ ≤ 2 ^ (2 * x) * (2 ^ uniformLog n) ^ 5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_pow_uniformLog hnpos) _)
      _ = 2 ^ (2 * x + 5 * uniformLog n) := by
        rw [pow_add, Nat.mul_comm 5 (uniformLog n), pow_mul 2 (uniformLog n) 5]
  -- The logarithmic term pays for the common scale. The remaining bits pay for the degree,
  -- advantage and fixed factors.
  have hU : 2 ^ (12 + max p.d p.lambda) * scale ≤ p.U := by
    calc
      _ ≤ 2 ^ (12 + max p.d p.lambda) * 2 ^ (2 * x + 5 * uniformLog n) :=
        Nat.mul_le_mul_left _ hScaleUpper
      _ = 2 ^ uniformLossFor n x lambda := by
        rw [← pow_add]
        congr 1
        change 12 + max (uniformPower n x) lambda + (2 * x + 5 * uniformLog n) =
          2 * x + max (uniformPower n x) lambda + 5 * uniformLog n + 12
        omega
      _ ≤ p.U := two_pow_le hs
  have hUscale {k : ℕ} (hk : k ≤ 12 + max p.d p.lambda) : 2 ^ k * scale ≤ p.U :=
    (Nat.mul_le_mul_right scale (two_pow_le hk)).trans hU
  have hU64 : 64 * scale ≤ p.U := hUscale (k := 6) (by omega)
  have hdmax : p.d ≤ max p.d p.lambda := le_max_left _ _
  have hlmax : p.lambda ≤ max p.d p.lambda := le_max_right _ _
  have hN : (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ 1 := by
    have hnat : p.N ≤ p.mu ^ p.d := by
      change (2 : ℕ) ^ n ≤ (2 ^ x) ^ uniformPower n x
      rw [← pow_mul]
      exact two_pow_le (uniformPower_mul_ge hx)
    have hmuPos : 0 < (p.mu : ℝ) := by exact_mod_cast (show 0 < p.mu by omega)
    apply (div_le_iff₀ (pow_pos hmuPos _)).2
    simpa only [one_mul, ← Nat.cast_pow] using (show (p.N : ℝ) ≤ ↑(p.mu ^ p.d) by
      exact_mod_cast hnat)
  have hinitial : 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ (p.Gamma : ℝ) := by
    have hPiTwo : 2 ≤ p.Pi := by
      calc
        2 ≤ n ^ 2 := by
          have hn' : 2 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega : 2 ≤ n) _
          omega
        _ ≤ p.Pi := hPiN
    have htwo : (2 : ℝ) ≤ p.Gamma := by exact_mod_cast hPiTwo.trans hPiGamma
    rw [mul_div_assoc]
    linarith
  have hUpos : 0 < (p.U : ℝ) := by exact_mod_cast p.U_pos
  have hbudget : p.QueryBudget q := by
    apply (le_div_iff₀ hUpos).2
    exact_mod_cast hq
  have hwitness : p.h = 2 * n - 1 := uniform_witness_size hn
  -- Use the exact witness size to bound the prefactor by `8 ^ h`. Bound `h!` by `h ^ h` to put
  -- the full witness tail over a single power.
  have hflowExponent : 2 * p.n + p.lambda + 3 ≤ 3 * p.h := by
    rw [hwitness]
    change 2 * n + lambda + 3 ≤ 3 * (2 * n - 1)
    omega
  have hflowBase : 8 * p.h * (2 * p.Pi ^ 2) ≤ p.U := by
    have hle : p.h ≤ 2 * n := by omega
    calc
      _ ≤ 8 * (2 * n) * (2 * p.Pi ^ 2) := by gcongr
      _ ≤ 64 * scale := by
        rw [show 8 * (2 * n) * (2 * p.Pi ^ 2) = 32 * scale by dsimp [scale]; ring]
        exact Nat.mul_le_mul_right _ (by decide)
      _ ≤ p.U := hU64
  have hflow : 2 ^ (2 * p.n + p.lambda + 3) * p.h.factorial *
      (2 * p.Pi ^ 2) ^ p.h ≤ p.U ^ p.h := by
    have hexp : 2 ^ (2 * p.n + p.lambda + 3) ≤ 8 ^ p.h := by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, ← pow_mul]
      exact two_pow_le hflowExponent
    calc
      _ ≤ (8 : ℕ) ^ p.h * p.h ^ p.h * (2 * p.Pi ^ 2) ^ p.h := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul hexp (Nat.factorial_le_pow p.h))
      _ = (8 * p.h * (2 * p.Pi ^ 2)) ^ p.h := by simp only [mul_pow]
      _ ≤ p.U ^ p.h := Nat.pow_le_pow_left hflowBase _
  have hdriftBudget : 2 ^ (p.d + 3) * p.Pi ^ 2 ≤ p.U :=
    (Nat.mul_le_mul_left _ hPiSqScale).trans (hUscale (by omega))
  let power := (2 : ℕ) ^ (p.d - 1)
  have hpower : 1 ≤ power := Nat.pow_pos (by decide : 0 < 2)
  have hdrift : 4 * p.driftNumerator ≤ p.Gamma * p.U := by
    calc
      _ ≤ 4 * (power * p.Gamma * (p.Pi ^ 2 + p.Pi ^ 2) + p.Gamma * p.Pi ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add
          (Nat.mul_le_mul_left _ (Nat.add_le_add_left hTheta _)) (Nat.mul_le_mul hPiGamma hTheta))
      _ = p.Gamma * ((8 * power + 4) * p.Pi ^ 2) := by ring
      _ ≤ p.Gamma * ((16 * power) * p.Pi ^ 2) := by gcongr; omega
      _ = p.Gamma * (2 ^ (p.d + 3) * p.Pi ^ 2) := by
        rw [show p.d + 3 = 4 + (p.d - 1) by omega, pow_add]
        rfl
      _ ≤ p.Gamma * p.U := Nat.mul_le_mul_left _ hdriftBudget
  have hoccupancy : 6 * p.Pi * (p.Psi + p.Pi) ≤ p.nu * p.U := by
    calc
      _ ≤ 6 * p.Pi * (2 * p.Gamma + p.Gamma) := by
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hPiGamma _)
      _ = p.nu * (18 * p.Pi ^ 2) := by unfold Params.Gamma; ring
      _ ≤ p.nu * p.U := by
        apply Nat.mul_le_mul_left
        exact (Nat.mul_le_mul (by decide : 18 ≤ 64) hPiSqScale).trans hU64
  have hcharge : power * (p.Pi + p.Gamma) + p.Psi + 2 * p.Pi ≤ p.U := by
    calc
      _ ≤ power * (scale + 16 * scale) + 32 * scale + 2 * scale := by
        exact Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add hPiScale hGammaUpper))
            hPsiUpper) (Nat.mul_le_mul_left _ hPiScale)
      _ = (17 * power + 34) * scale := by ring
      _ ≤ (64 * power) * scale := by gcongr; omega
      _ = 2 ^ (p.d + 5) * scale := by
        rw [show p.d + 5 = 6 + (p.d - 1) by omega, pow_add]
        rfl
      _ ≤ p.U := hUscale (by omega)
  have hchargeReal : p.graftCoefficient + (p.Psi : ℝ) + 2 * (p.Pi : ℝ) ≤ (p.U : ℝ) := by
    unfold Params.graftCoefficient
    exact_mod_cast hcharge
  -- The initial boundary, expected potential growth and later grafts all fit in the constant
  -- intersection factor.
  have hfactor : p.intersectionFactor p.Psi 4 p.graftCoefficient ≤ 10 := by
    have htail : 4 / (p.U : ℝ) * (p.graftCoefficient + (p.Psi : ℝ) + 2 * (p.Pi : ℝ)) ≤ 4 :=
      calc
        _ ≤ 4 / (p.U : ℝ) * (p.U : ℝ) :=
          mul_le_mul_of_nonneg_left hchargeReal (by positivity)
        _ = 4 := div_mul_cancel₀ _ hUpos.ne'
    unfold Params.intersectionFactor
    rw [mul_div_assoc]
    linarith
  have hintersection : p.IntersectionCondition p.Psi 4 p.graftCoefficient := by
    have hPsiReal : (p.Psi : ℝ) ≤ 32 * (scale : ℝ) := by exact_mod_cast hPsiUpper
    have hUb : (2 : ℝ) ^ (12 + p.lambda) * (scale : ℝ) ≤ (p.U : ℝ) := by
      exact_mod_cast hUscale (k := 12 + p.lambda) (by omega)
    unfold Params.IntersectionCondition
    calc
      _ ≤ (2 : ℝ) ^ (p.lambda + 3) * (p.Psi : ℝ) * 10 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ (2 : ℝ) ^ (p.lambda + 3) * (32 * (scale : ℝ)) * 10 := by gcongr
      _ ≤ (2 : ℝ) ^ (12 + p.lambda) * (scale : ℝ) := by
        rw [pow_add, pow_add]
        norm_num
        nlinarith [show 0 ≤ (2 : ℝ) ^ p.lambda * (scale : ℝ) by positivity]
      _ ≤ (p.U : ℝ) := hUb
  have hsep : p.lambda + 2 ≤ 2 * p.s := by
    unfold uniformLossFor at hs
    change lambda + 2 ≤ 2 * s
    have h : lambda ≤ max (uniformPower n x) lambda := le_max_right _ _
    omega
  exact
    { admissible := ha
      budget := hbudget
      nu_choice := hnu
      initial_potential := hinitial
      endpoint_budget := hTheta.trans ((by omega : p.Pi ^ 2 ≤ 64 * scale).trans hU64)
      flow := hflow
      separation := hsep
      drift := hdrift
      occupancy := hoccupancy
      intersection := hintersection }

/-- The Appendix A.2 construction supplies the equal-weight certificate uniformly in its allowed
lengths and exponents. -/
theorem uniform_parameter_feasibility : UniformSpec.ParameterFeasibility := by
  intro n x lambda q hn hx _ hlambda hlambdaN hq
  exact certificate_at_loss hn hx hlambda hlambdaN le_rfl hq

private theorem sqrt_double (n : ℝ) : Real.sqrt (2 * n) = 2 * Real.sqrt (n / 2) := by
  rw [show 2 * n = 4 * (n / 2) by ring, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)),
    show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- The square-root choices below (39) provide a finite unweighted certificate for every total
budget satisfying the rounded loss inequality. -/
theorem explicit_certificate : UniformSpec.ExplicitCertificate := by
  intro n q hn hq
  let root := Real.sqrt ((n : ℝ) / 2)
  let doubleRoot := Real.sqrt (2 * (n : ℝ))
  let x := ⌈root⌉₊
  let lambda := ⌊doubleRoot⌋₊
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hrootSq : root ^ 2 = (n : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hdroot : doubleRoot = 2 * root := sqrt_double _
  have hrootPos : 0 < root := Real.sqrt_pos.2 (by linarith)
  have hdoubleTwo : 2 ≤ doubleRoot := by
    calc
      (2 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ doubleRoot := Real.sqrt_le_sqrt (by linarith)
  have hlambda : 1 ≤ lambda := (Nat.one_le_floor_iff _).2 (by linarith)
  have hlambdaN : lambda ≤ n := by
    apply Nat.floor_le_of_le
    calc
      doubleRoot ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = n := Real.sqrt_sq (by positivity)
  have hx : 1 ≤ x := (Nat.one_le_ceil_iff).2 hrootPos
  have hxreal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hdx : (n : ℝ) / (x : ℝ) ≤ doubleRoot := by
    apply (div_le_iff₀ hxreal).2
    calc
      (n : ℝ) = doubleRoot * root := by rw [hdroot]; nlinarith only [hrootSq]
      _ ≤ doubleRoot * x := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by linarith)
  -- The ceiling of `sqrt (2 * n)` pays for both the degree and the chosen advantage exponent.
  have hd : uniformPower n x ≤ ⌈doubleRoot⌉₊ := by
    apply max_le
    · simpa only [Nat.ceil_ofNat] using Nat.ceil_le_ceil hdoubleTwo
    · exact Nat.ceil_le_ceil hdx
  have hs : uniformLossFor n x lambda ≤ PreimageSpec.uniformLoss n := by
    change 2 * x + max (uniformPower n x) lambda + 5 * uniformLog n + 12 ≤
      2 * x + ⌈doubleRoot⌉₊ + 5 * uniformLog n + 12
    have hmax : max (uniformPower n x) lambda ≤ ⌈doubleRoot⌉₊ :=
      max_le hd (Nat.floor_le_ceil doubleRoot)
    omega
  exact certificate_at_loss hn hx hlambda hlambdaN hs hq

/-- Removing the ceilings gives the loss expression with leading term `2 * sqrt (2 * n)`. -/
theorem unrounded_loss : UniformSpec.UnroundedLoss := by
  intro n x hn hx
  rw [sqrt_double]
  field_simp
  nlinarith only [Real.sq_sqrt (show 0 ≤ n / 2 by positivity)]

/-- The rounded loss below (39) differs from `2 * sqrt (2 * n)`
by `O(log n)`. -/
theorem uniform_loss_asymptotic : UniformSpec.LossAsymptotic := by
  unfold UniformSpec.LossAsymptotic
  apply Asymptotics.IsBigO.of_bound (25 / Real.log 2)
  filter_upwards [Filter.eventually_ge_atTop (4 : ℕ)] with n hn
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by linarith)
  let a := Real.sqrt ((n : ℝ) / 2)
  let b := Real.sqrt (2 * (n : ℝ))
  let c := Real.log (n : ℝ) / Real.log 2
  have hb : b = 2 * a := sqrt_double _
  have hc : 1 ≤ c := (le_div_iff₀ hlogPos).2 (by simpa only [one_mul] using hlog)
  simp only [Real.norm_eq_abs, PreimageSpec.uniformLoss]
  push_cast
  change |2 * (⌈a⌉₊ : ℝ) + (⌈b⌉₊ : ℝ) + 5 * (⌈c⌉₊ : ℝ) + 12 - 2 * b| ≤
    25 / Real.log 2 * |Real.log (n : ℝ)|
  rw [abs_of_nonneg (by linarith [Nat.le_ceil a, Nat.le_ceil b, Nat.le_ceil c]),
    abs_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ))]
  calc
    _ ≤ 5 * c + 20 := by
      linarith [Nat.ceil_lt_add_one (Real.sqrt_nonneg ((n : ℝ) / 2)),
        Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * (n : ℝ))),
        Nat.ceil_lt_add_one (show 0 ≤ c by linarith)]
    _ ≤ 25 * c := by linarith
    _ = 25 / Real.log 2 * Real.log (n : ℝ) := by dsimp [c]; ring

end JH.Parameters
