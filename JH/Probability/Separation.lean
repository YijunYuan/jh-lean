/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.SeparationSpec
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Accumulating separation probabilities

Section 3.2 bounds the first discrepancy between the independent-reply and permutation
experiments by a sum of conditional hazards. The generic recursion below charges existing bad
mass once and adds a one-step allowance on the remaining supported states.
-/

@[expose] public section

namespace JH.Separation

open scoped ENNReal BigOperators

universe u

/-- Read the Boolean failure mass as the probability of its preimage event. -/
theorem mass_eq_toOuterMeasure {α : Type u} (law : PMF α) (bad : α → Bool) :
    mass law bad = law.toOuterMeasure {a | bad a = true} := by
  calc
    mass law bad = (law.map bad).toOuterMeasure {true} :=
      (PMF.toOuterMeasure_apply_singleton _ _).symm
    _ = _ := PMF.toOuterMeasure_map_apply _ _ _

theorem mass_eq_zero_of_good_on_support {α : Type u} (law : PMF α) (bad : α → Bool)
    (good : ∀ a ∈ law.support, bad a = false) : mass law bad = 0 := by
  rw [mass, PMF.apply_eq_zero_iff]
  intro supported
  obtain ⟨a, reaches, badNow⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rw [good a reaches] at badNow
  contradiction

/-- A step adds at most its allowance to the existing bad mass. -/
theorem mass_bind_le : OneStep := by
  intro α law step bad allowance localBound
  let badStates : Set α := {a | bad a = true}
  -- A bad state can contribute at most its full mass. A good state pays the local hazard.
  have contribution (a : α) : law a * mass (step a) bad ≤
      badStates.indicator law a + law a * allowance := by
    by_cases supported : a ∈ law.support
    · cases flag : bad a with
      | false =>
        have absent : a ∉ badStates := by simp [badStates, flag]
        rw [Set.indicator_of_notMem absent, zero_add]
        exact mul_le_mul_right (localBound a supported flag) (law a)
      | true =>
        have present : a ∈ badStates := flag
        rw [Set.indicator_of_mem present]
        calc
          _ ≤ law a * 1 := mul_le_mul_right (((step a).map bad).coe_le_one true) (law a)
          _ ≤ _ := by simp
    · have zero : law a = 0 := (law.apply_eq_zero_iff a).mpr supported
      simp [zero]
  calc
    mass (law.bind step) bad = ∑' a, law a * mass (step a) bad := by
      rw [mass, PMF.map_bind, PMF.bind_apply]
      rfl
    _ ≤ ∑' a, (badStates.indicator law a + law a * allowance) :=
      tsum_le_tsum contribution
    _ = mass law bad + allowance := by
      simp only [badStates, tsum_add, ENNReal.tsum_mul_right, law.tsum_coe, one_mul,
        mass_eq_toOuterMeasure, PMF.toOuterMeasure_apply]

/-- Iterate the one-step bound from a law supported on good states. -/
theorem mass_states_le : FiniteTime := by
  intro α init step bad q allowance initiallyGood localBound
  induction q with
  | zero => simp [states, mass_eq_zero_of_good_on_support init bad initiallyGood]
  | succ q ih =>
    rw [states, Finset.sum_range_succ]
    have previous := ih (fun i hi ↦ localBound i (Nat.lt_succ_of_lt hi))
    exact (mass_bind_le (states init step q) (step q) bad (allowance q)
      (localBound q (Nat.lt_succ_self q))).trans (add_le_add_left previous (allowance q))

/-- Sum the per-round allowances `i / K` over the first `Q` rounds. -/
theorem sum_hazards : AllowanceSum := by
  intro q K
  have doubled : (∑ i ∈ Finset.range q, (i : ℝ≥0∞)) * 2 =
      ((q * (q - 1) : ℕ) : ℝ≥0∞) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using
      congrArg (fun n : ℕ ↦ (n : ℝ≥0∞)) (Finset.sum_range_id_mul_two q)
  rw [← doubled, div_eq_mul_inv, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (by simp)),
    ← mul_assoc, ENNReal.mul_inv_cancel_right two_ne_zero (by simp)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Specialize the finite-time estimate to the hazards from equation (8). -/
theorem mass_states_le_formula4 : Formula4 := by
  intro α init step bad q K initiallyGood localBound
  rw [← sum_hazards q K]
  exact mass_states_le init step bad q (fun i ↦ (i : ℝ≥0∞) / K) initiallyGood localBound

/-- Express the separation estimate in real arithmetic for the final union bound. -/
theorem mass_states_le_formula4_real : Formula4Real := by
  intro α init step bad q K positive initiallyGood localBound
  have finite : (((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * (K : ℝ≥0∞))) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Nat.ne_of_gt positive])
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    using ENNReal.toReal_mono finite
      (mass_states_le_formula4 init step bad q (K : ℝ≥0∞) initiallyGood localBound)

end JH.Separation
