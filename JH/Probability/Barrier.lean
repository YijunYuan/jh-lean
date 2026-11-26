/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.BarrierSpec
public import JH.Probability.Stopping
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Exponential supermartingale for a ledger

Section 3.4 controls a ledger with bounded nonnegative costs and predictable means. The
exponential chord bounds the conditional moment of each cost. Subtracting the accumulated means
in the exponent makes the resulting process a supermartingale, so the maximal inequality from
Section 2.4 applies.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace JH.Probability

universe u

variable {Ω : Type u} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m} {cost ledger : ℕ → Ω → ℝ} {B Γ : ℝ}

/-- The chord of the exponential between zero and `log 2`. -/
theorem exp_log_two_mul_le_one_add {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) :
    Real.exp (Real.log 2 * x) ≤ 1 + x := by
  calc
    _ = Real.exp ((1 - x) • (0 : ℝ) + x • Real.log 2) := by
      simp [smul_eq_mul, mul_comm]
    _ ≤ (1 - x) • Real.exp 0 + x • Real.exp (Real.log 2) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr h₁) h₀ (by ring)
    _ = _ := by
      rw [Real.exp_zero, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [smul_eq_mul]
      ring

/-- The one-step exponential moment of a cost in `[0, B]` is bounded by
the exponential of its conditional mean divided by `B`. -/
theorem condExp_exp_cost_le [IsFiniteMeasure μ] {m' : MeasurableSpace Ω} (hm' : m' ≤ m)
    {X : Ω → ℝ} (hB : 0 < B) (hX : AEMeasurable X μ)
    (hBound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 B) :
    Integrable (fun ω ↦ Real.exp (Real.log 2 * (X ω / B))) μ ∧
      μ[(fun ω ↦ Real.exp (Real.log 2 * (X ω / B))) | m'] ≤ᵐ[μ]
        fun ω ↦ Real.exp (μ[X | m'] ω / B) := by
  let g : Ω → ℝ := fun ω ↦ Real.exp (Real.log 2 * (X ω / B))
  let a : Ω → ℝ := (fun _ ↦ 1) + B⁻¹ • X
  have hXInt := Integrable.of_mem_Icc 0 B hX hBound
  have hAInt : Integrable a μ := (integrable_const (1 : ℝ)).add (hXInt.smul B⁻¹)
  have hNorm (ω : Ω) (hω : X ω ∈ Set.Icc 0 B) : 0 ≤ X ω / B ∧ X ω / B ≤ 1 :=
    ⟨div_nonneg hω.1 hB.le, (div_le_iff₀ hB).mpr (by simpa using hω.2)⟩
  -- The affine majorant passes through conditional expectation by monotonicity and linearity.
  have hChord : g ≤ᵐ[μ] a := hBound.mono fun ω hω ↦ by
    change Real.exp (Real.log 2 * (X ω / B)) ≤ 1 + B⁻¹ * X ω
    rw [mul_comm B⁻¹, ← div_eq_mul_inv]
    exact exp_log_two_mul_le_one_add (hNorm ω hω).1 (hNorm ω hω).2
  have hGMeas : AEMeasurable g μ :=
    (show Continuous (fun x : ℝ ↦ Real.exp (Real.log 2 * (x / B))) by fun_prop)
      |>.measurable.comp_aemeasurable hX
  have hGInt : Integrable g μ := Integrable.of_mem_Icc 0 2 hGMeas <|
    hBound.mono fun ω hω ↦ ⟨Real.exp_nonneg _, calc
      g ω ≤ 1 + X ω / B := exp_log_two_mul_le_one_add (hNorm ω hω).1 (hNorm ω hω).2
      _ ≤ 2 := by linarith [(hNorm ω hω).2]⟩
  have hAffine : μ[a | m'] =ᵐ[μ] (fun _ ↦ 1) + B⁻¹ • μ[X | m'] := by
    calc
      μ[a | m'] =ᵐ[μ] μ[(fun _ : Ω ↦ (1 : ℝ)) | m'] + μ[B⁻¹ • X | m'] :=
        condExp_add (integrable_const (1 : ℝ)) (hXInt.smul B⁻¹) m'
      _ =ᵐ[μ] _ := by
        rw [condExp_const hm']
        exact (Filter.EventuallyEq.refl _ _).add (condExp_smul B⁻¹ X m')
  refine ⟨hGInt, ?_⟩
  filter_upwards [condExp_mono hGInt hAInt hChord, hAffine] with ω hle heq
  calc
    μ[g | m'] ω ≤ μ[a | m'] ω := hle
    _ = 1 + μ[X | m'] ω / B := by
      change μ[a | m'] ω = 1 + B⁻¹ * μ[X | m'] ω at heq
      simpa only [div_eq_mul_inv, mul_comm B⁻¹] using heq
    _ ≤ _ := by
      rw [add_comm 1]
      exact Real.add_one_le_exp _

/-- With no sampled costs or predictable means, the exponential process starts at one. -/
@[simp]
theorem compensatedExp_zero : compensatedExp μ ℱ cost B 0 = fun _ ↦ 1 := by
  funext ω
  simp [compensatedExp]

private theorem compensatedExp_succ (i : ℕ) :
    compensatedExp μ ℱ cost B (i + 1) =
      (compensatedExp μ ℱ cost B i *
        (fun ω ↦ Real.exp (-(μ[cost (i + 1) | ℱ i] ω / B)))) *
        fun ω ↦ Real.exp (Real.log 2 * (cost (i + 1) ω / B)) := by
  funext ω
  simp only [compensatedExp, Finset.sum_range_succ, Pi.mul_apply, ← Real.exp_add]
  congr 1
  ring

private theorem condExp_cost_nonneg (hBound : ∀ i, ∀ᵐ ω ∂μ, cost i ω ∈ Set.Icc 0 B)
    (i : ℕ) : 0 ≤ᵐ[μ] μ[cost (i + 1) | ℱ i] :=
  condExp_nonneg ((hBound (i + 1)).mono fun _ hω ↦ hω.1)

/-- The compensated exponential process of Section 3.4 is adapted, integrable, and has
nonincreasing conditional expectation. -/
theorem compensatedExp_supermartingale [IsProbabilityMeasure μ] (hB : 0 < B)
    (hCost : StronglyAdapted ℱ cost)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, cost i ω ∈ Set.Icc 0 B) :
    Supermartingale (compensatedExp μ ℱ cost B) ℱ μ := by
  let Y := compensatedExp μ ℱ cost B
  let p (i : ℕ) (ω : Ω) := Real.exp (-(μ[cost (i + 1) | ℱ i] ω / B))
  let g (i : ℕ) (ω : Ω) := Real.exp (Real.log 2 * (cost (i + 1) ω / B))
  have hStep (i : ℕ) : Y (i + 1) = (Y i * p i) * g i := compensatedExp_succ i
  have hpMeas (i : ℕ) : StronglyMeasurable[ℱ i] (p i) :=
    (show Continuous (fun x : ℝ ↦ Real.exp (-(x / B))) by fun_prop)
      |>.comp_stronglyMeasurable stronglyMeasurable_condExp
  have hgMeas (i : ℕ) : StronglyMeasurable[ℱ (i + 1)] (g i) :=
    (show Continuous (fun x : ℝ ↦ Real.exp (Real.log 2 * (x / B))) by fun_prop)
      |>.comp_stronglyMeasurable (hCost (i + 1))
  have hYMeas : StronglyAdapted ℱ Y := by
    intro i
    induction i with
    | zero =>
      change StronglyMeasurable[ℱ 0] (compensatedExp μ ℱ cost B 0)
      rw [compensatedExp_zero]
      exact stronglyMeasurable_const
    | succ i ih =>
      rw [hStep i]
      exact ((ih.mul (hpMeas i)).mono (ℱ.mono (Nat.le_succ i))).mul (hgMeas i)
  have hLogCoeff : 0 ≤ Real.log 2 / B := div_nonneg (Real.log_nonneg (by norm_num)) hB.le
  have hYInt (i : ℕ) : Integrable (Y i) μ := by
    apply Integrable.of_mem_Icc 0 (Real.exp (Real.log 2 * i))
      hYMeas.stronglyMeasurable.measurable.aemeasurable
    filter_upwards [ae_all_iff.mpr hBound,
      ae_all_iff.mpr (condExp_cost_nonneg (ℱ := ℱ) hBound)] with ω hω hMeanNonneg
    refine ⟨Real.exp_nonneg _, Real.exp_le_exp.mpr ?_⟩
    have hSumCost : (∑ j ∈ Finset.range i, cost (j + 1) ω) ≤ (i : ℝ) * B := by
      calc
        _ ≤ ∑ _j ∈ Finset.range i, B := Finset.sum_le_sum fun j _ ↦ (hω (j + 1)).2
        _ = _ := by simp
    have hSumMean : 0 ≤ ∑ j ∈ Finset.range i, μ[cost (j + 1) | ℱ j] ω :=
      Finset.sum_nonneg fun j _ ↦ hMeanNonneg j
    calc
      _ ≤ Real.log 2 / B * (∑ j ∈ Finset.range i, cost (j + 1) ω) :=
        sub_le_self _ (div_nonneg hSumMean hB.le)
      _ ≤ Real.log 2 / B * ((i : ℝ) * B) := mul_le_mul_of_nonneg_left hSumCost hLogCoeff
      _ = _ := by field_simp
  refine supermartingale_nat hYMeas hYInt fun i ↦ ?_
  have ⟨hGInt, hMoment⟩ := condExp_exp_cost_le (ℱ.le i) hB
    (hCost.stronglyMeasurable (i := i + 1)).measurable.aemeasurable (hBound (i + 1))
  have hProductInt : Integrable (Y i * p i * g i) μ := by
    rw [← hStep i]
    exact hYInt (i + 1)
  -- The old process and the next compensation are both measurable in the old filtration.
  have hPullOut :=
    condExp_mul_of_stronglyMeasurable_left ((hYMeas i).mul (hpMeas i)) hProductInt hGInt
  change μ[Y (i + 1) | ℱ i] ≤ᵐ[μ] Y i
  rw [hStep i]
  filter_upwards [hPullOut, hMoment] with ω hPull hMomentω
  change μ[Y i * p i * g i | ℱ i] ω = (Y i ω * p i ω) * μ[g i | ℱ i] ω at hPull
  rw [hPull]
  calc
    _ ≤ (Y i ω * p i ω) * Real.exp (μ[cost (i + 1) | ℱ i] ω / B) :=
      mul_le_mul_of_nonneg_left hMomentω (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = Y i ω := by
      rw [mul_assoc]
      change Y i ω * (Real.exp (-(μ[cost (i + 1) | ℱ i] ω / B)) *
        Real.exp (μ[cost (i + 1) | ℱ i] ω / B)) = Y i ω
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- The initial value and supermartingale property of the compensated process used in (22). -/
theorem compensated_exp_supermartingale : CompensatedExpSupermartingale.{u} := by
  intro Ω m μ _ ℱ cost B hB hCost hBound
  exact ⟨compensatedExp_supermartingale hB hCost hBound, by simp⟩

@[deprecated (since := "2026-11-25")]
alias compensatedExpSupermartingale := compensated_exp_supermartingale

/-- A single ledger with the Section 3.4 initial and cumulative drift bounds crosses `Γ` by time
`q` with at most the stated exponential probability. -/
theorem single_barrier_tail [IsProbabilityMeasure μ] (hB : 0 < B)
    (hCost : StronglyAdapted ℱ cost) (hBound : ∀ i, ∀ᵐ ω ∂μ, cost i ω ∈ Set.Icc 0 B)
    (q : ℕ) (hInitial : ∀ᵐ ω ∂μ, ledger 0 ω ≤ Γ / 2)
    (hIncrease : ∀ᵐ ω ∂μ, ∀ i < q, ledger (i + 1) ω - ledger i ω ≤ cost (i + 1) ω)
    (hDrift : ∀ᵐ ω ∂μ, (∑ i ∈ Finset.range q, μ[cost (i + 1) | ℱ i] ω) ≤ Γ / 4) :
    μ.real {ω | ∃ i ≤ q, Γ ≤ ledger i ω} ≤
      Real.exp (-((Real.log 2 / 2 - 1 / 4) * (Γ / B))) := by
  let b : ℝ := (Real.log 2 / 2 - 1 / 4) * (Γ / B)
  let Y := compensatedExp μ ℱ cost B
  have hLogCoeff : 0 ≤ Real.log 2 / B := div_nonneg (Real.log_nonneg (by norm_num)) hB.le
  have hCross :
      {ω | ∃ i ≤ q, Γ ≤ ledger i ω} ≤ᵐ[μ] {ω | ∃ i ≤ q, Real.exp b ≤ Y i ω} := by
    filter_upwards [hInitial, hIncrease, hDrift,
      ae_all_iff.mpr (condExp_cost_nonneg (ℱ := ℱ) hBound)] with ω hInit hStep hDriftω hMean
    rintro ⟨i, hiq, hi⟩
    have hLedger (n : ℕ) (hn : n ≤ q) :
        ledger n ω ≤ Γ / 2 + ∑ j ∈ Finset.range n, cost (j + 1) ω := by
      induction n with
      | zero => simpa using hInit
      | succ n ih =>
        rw [Finset.sum_range_succ]
        linarith [ih (Nat.le_of_succ_le hn), hStep n (Nat.lt_of_succ_le hn)]
    -- A ledger crossing forces the cumulative cost through that round to reach half the barrier.
    have hActual : Γ / 2 ≤ ∑ j ∈ Finset.range i, cost (j + 1) ω := by
      linarith [hLedger i hiq]
    -- Nonnegative predictable means let the horizon drift bound apply to the crossing prefix.
    have hMeanPrefix : (∑ j ∈ Finset.range i, μ[cost (j + 1) | ℱ j] ω) ≤ Γ / 4 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hiq) fun j _ _ ↦
        hMean j).trans hDriftω
    refine ⟨i, hiq, Real.exp_le_exp.mpr ?_⟩
    calc
      b = Real.log 2 / B * (Γ / 2) - (Γ / 4) / B := by dsimp [b]; ring
      _ ≤ Real.log 2 / B * (∑ j ∈ Finset.range i, cost (j + 1) ω) -
          (∑ j ∈ Finset.range i, μ[cost (j + 1) | ℱ j] ω) / B :=
        sub_le_sub (mul_le_mul_of_nonneg_left hActual hLogCoeff)
          (div_le_div_of_nonneg_right hMeanPrefix hB.le)
  have hY : Supermartingale Y ℱ μ := compensatedExp_supermartingale hB hCost hBound
  have hYNonneg (i : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ Y i ω :=
    ae_of_all μ fun _ ↦ Real.exp_nonneg _
  calc
    _ ≤ μ.real {ω | ∃ i ≤ q, Real.exp b ≤ Y i ω} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hCross)
    _ ≤ (∫ ω, Y 0 ω ∂μ) / Real.exp b := ville hY hYNonneg (Real.exp_pos b) q
    _ = _ := by simp [Y, b, Real.exp_neg, one_div]

/-- A single account with the initial and cumulative drift bounds of Section 3.4 satisfies the
exponential crossing estimate used in (22). -/
theorem single_barrier_tail_spec : SingleBarrierTail.{u} := by
  intro Ω m μ _ ℱ cost ledger B Γ q hB _hΓ hCost _hLedger hBound hInit hIncrease hDrift
  exact single_barrier_tail hB hCost hBound q hInit hIncrease hDrift

@[deprecated (since := "2026-11-25")] alias singleBarrierTail := single_barrier_tail_spec

end JH.Probability
