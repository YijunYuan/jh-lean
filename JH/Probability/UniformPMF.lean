/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform draws from finite types

Uniform probability mass functions for finite draws in the oracle experiments.
-/

@[expose] public section

namespace JH

open scoped ENNReal

/-- Each outcome of a nonempty finite type has mass equal to the inverse cardinality. -/
noncomputable def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp))

variable {α : Type*} [Fintype α] [Nonempty α]

@[simp] theorem uniformPMF_apply (a : α) : uniformPMF α a = (Fintype.card α : ℝ≥0∞)⁻¹ := rfl

@[simp] theorem mem_support_uniformPMF (a : α) : a ∈ (uniformPMF α).support := by
  simp [PMF.mem_support_iff]

theorem toOuterMeasure_uniformPMF_apply (s : Set α) [Fintype s] :
    (uniformPMF α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  conv_lhs => rw [← Set.coe_toFinset s, PMF.toOuterMeasure_apply_finset]
  simp [nsmul_eq_mul, div_eq_mul_inv]

end JH
