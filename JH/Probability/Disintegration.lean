/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.DisintegrationSpec

/-!
# Discrete conditioning on an observed reply

Section 3.2 compares independent replies with the permutation experiment. The latter can be
sampled by drawing the observed reply first, then filtering the permutation law to those that
produce it. These identities justify that step and the accumulation of successive observations
in the lazy replay.
-/

@[expose] public section

namespace JH.Probability

open scoped ENNReal

variable {α β γ : Type*}

/-- The mass of a given observation is the total prior mass of its fiber. -/
private theorem observation_mass (p : PMF α) (observe : α → β) (y : β) :
    (p.map observe) y = ∑' x, (observe ⁻¹' {y}).indicator p x := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]

/-- The posterior mixture over the observation's support gives the original result law. -/
theorem map_bindOnSupport_filter (p : PMF α) (observe : α → β) (result : α → γ) :
    (p.map observe).bindOnSupport
      (fun y hy ↦ (p.filter (observe ⁻¹' {y}) (fiber_witness p observe hy)).map result) =
    p.map result := by
  classical
  apply PMF.ext
  intro z
  rw [PMF.bindOnSupport_apply, PMF.map_apply result p z]
  calc
    _ = ∑' y, ∑' x, if z = result x then (observe ⁻¹' {y}).indicator p x else 0 := by
      refine tsum_congr fun y ↦ ?_
      by_cases hy : (p.map observe) y = 0
      -- On a zero-mass fiber, each summand vanishes.
      · rw [dite_eq_left hy, mul_zero]
        refine (tsum_eq_zero_iff.mpr fun x ↦ ?_).symm
        have hx := tsum_eq_zero_iff.mp ((observation_mass p observe y).symm.trans hy) x
        simp [hx]
      -- The observation mass cancels the inverse introduced by filtering its fiber.
      · rw [dite_eq_right hy, PMF.map_apply result, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun x ↦ ?_
        by_cases hz : z = result x
        · simp only [ite_eq_left hz, PMF.filter_apply]
          rw [← observation_mass p observe y, mul_left_comm,
            ENNReal.mul_inv_cancel hy ((p.map observe).apply_ne_top y), mul_one]
        · simp only [ite_eq_right hz, mul_zero]
    _ = _ := by
      -- After exchanging sums, each original sample contributes to its unique observation.
      rw [tsum_comm]
      refine tsum_congr fun x ↦ ?_
      by_cases hx : z = result x <;> simp [hx, Set.indicator_apply]

/-- The first normalization cancels when the second event is imposed. -/
theorem filter_filter (p : PMF α) (s t : Set α)
    (hs : ∃ x ∈ s, x ∈ p.support) (ht : ∃ x ∈ t, x ∈ (p.filter s hs).support) :
    (p.filter s hs).filter t ht = p.filter (s ∩ t) (inter_witness p s t hs ht) := by
  classical
  let massS := ∑' x, s.indicator p x
  have hne : massS ≠ 0 := by simpa [massS] using hs
  have hfin : massS ≠ ⊤ := p.tsum_coe_indicator_ne_top s
  -- Restriction to the second event keeps exactly the weights on the intersection.
  have restricted (x : α) :
      t.indicator (p.filter s hs) x = (s ∩ t).indicator p x * massS⁻¹ := by
    by_cases hxt : x ∈ t <;> by_cases hxs : x ∈ s <;> simp [hxt, hxs, massS]
  apply PMF.ext
  intro x
  simp only [PMF.filter_apply, restricted, ENNReal.tsum_mul_right]
  simpa only [div_eq_mul_inv] using
    ENNReal.mul_div_mul_right ((s ∩ t).indicator p x) (∑' y, (s ∩ t).indicator p y)
      (ENNReal.inv_ne_zero.mpr hfin) (ENNReal.inv_ne_top.mpr hne)

end JH.Probability
