/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.StoppingSpec
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# The finite-horizon maximal inequality

To obtain the maximal inequality (5), cap the first hitting time at the horizon.
Optional stopping bounds the expectation there, and Markov's inequality bounds
the probability of crossing.
-/

@[expose] public section

open MeasureTheory

namespace JH.Probability

universe u

variable {Ω : Type u} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m} {Y : ℕ → Ω → ℝ}

/-- Reaching the barrier within the horizon is equivalent to being at least the barrier
at the capped first hitting time. -/
theorem reachesBy_iff_stoppedValue_ge (Y : ℕ → Ω → ℝ) (t : ℝ) (q : ℕ) (ω : Ω) :
    (∃ i ≤ q, t ≤ Y i ω) ↔
      t ≤ stoppedValue Y (fun ω' ↦ (hittingBtwn Y (Set.Ici t) 0 q ω' : ℕ)) ω := by
  constructor
  · rintro ⟨i, hi, hHit⟩
    exact stoppedValue_hittingBtwn_mem (s := Set.Ici t) ⟨i, ⟨Nat.zero_le i, hi⟩, hHit⟩
  · exact fun hHit ↦ ⟨hittingBtwn Y (Set.Ici t) 0 q ω, hittingBtwn_le ω, hHit⟩

/-- Ville's finite-horizon inequality for a real supermartingale that is nonnegative
almost everywhere at each time. -/
theorem ville [IsProbabilityMeasure μ] (hY : Supermartingale Y ℱ μ)
    (hNonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Y i ω) {t : ℝ} (ht : 0 < t) (q : ℕ) :
    μ.real {ω | ∃ i ≤ q, t ≤ Y i ω} ≤ (∫ ω, Y 0 ω ∂μ) / t := by
  let τ : Ω → ℕ∞ := fun ω ↦ (hittingBtwn Y (Set.Ici t) 0 q ω : ℕ)
  have hτ : IsStoppingTime ℱ τ :=
    hY.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτq (ω : Ω) : τ ω ≤ (q : ℕ∞) := ENat.natCast_le_natCast.mpr (hittingBtwn_le ω)
  -- The horizon bounds the stopping time, including on paths that miss the barrier.
  have hIntegrable := integrable_stoppedValue ℕ hτ hY.integrable hτq
  have hNonnegStopped : 0 ≤ᵐ[μ] stoppedValue Y τ :=
    (ae_all_iff.mpr hNonneg).mono fun ω hω ↦ hω (τ ω).untopA
  have hExpectation : (∫ ω, stoppedValue Y τ ω ∂μ) ≤ ∫ ω, Y 0 ω ∂μ := by
    -- Optional stopping for the submartingale `-Y` reverses the expectation bound.
    have h := hY.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
      (fun _ ↦ bot_le) hτq
    rw [stoppedValue_const] at h
    change (∫ ω, -(Y 0 ω) ∂μ) ≤ ∫ ω, -(stoppedValue Y τ ω) ∂μ at h
    simpa only [integral_neg, neg_le_neg_iff] using h
  -- Apply Markov's inequality to the stopped value on the original crossing event.
  have hEvent : {ω | ∃ i ≤ q, t ≤ Y i ω} = {ω | t ≤ stoppedValue Y τ ω} :=
    Set.ext fun ω ↦ reachesBy_iff_stoppedValue_ge Y t q ω
  rw [hEvent, le_div_iff₀ ht, mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg hNonnegStopped hIntegrable t).trans hExpectation

/-- **Ville's inequality** (5). At a positive threshold, the crossing probability up to any
finite horizon is at most the initial mean divided by the threshold. -/
theorem ville_bound : VilleBound.{u} := by
  intro Ω m μ _ ℱ Y hY hNonneg t ht q
  exact ville hY hNonneg ht q

@[deprecated (since := "2026-11-25")] alias villeBound := ville_bound

end JH.Probability
