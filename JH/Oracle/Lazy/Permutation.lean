/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.PermutationSpec

/-!
# Fresh replies of a conditioned permutation

Swapping two unused outputs pairs completions giving different forward replies, so each
possible fresh reply has the same mass. Inversion gives the backward case. The completion
condition is equivalent to consistency with every record of the transcript.
-/

@[expose] public section

namespace JH.PartialPermutation

open scoped ENNReal

universe u

variable {α : Type u}

/-- Postcomposition by a transposition of two unused outputs fixes every old pair. -/
noncomputable def swapUnusedOutputs (known : PartialPermutation α)
    (y z : known.UnusedOutput) (completion : known.Completion) : known.Completion := by
  classical
  refine ⟨completion.val.trans (Equiv.swap y.val z.val), ?_⟩
  intro x
  rw [Equiv.trans_apply, completion.property]
  exact Equiv.swap_apply_of_ne_of_ne
    (fun eq ↦ y.property (eq ▸ (known.matching x).property))
    (fun eq ↦ z.property (eq ▸ (known.matching x).property))

/-- The forward-reply fibers are in bijection by swapping the two requested outputs. -/
noncomputable def forwardFiberEquiv (known : PartialPermutation α) (x : known.UnusedInput)
    (y z : known.UnusedOutput) :
    {π : known.Completion // known.forward x π = y} ≃
      {π : known.Completion // known.forward x π = z} := by
  classical
  refine
    { toFun := fun π ↦ ⟨known.swapUnusedOutputs y z π.val, ?_⟩
      invFun := fun π ↦ ⟨known.swapUnusedOutputs y z π.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    change Equiv.swap y.val z.val (π.val.val x.val) = z.val
    rw [show π.val.val x.val = y.val from congrArg Subtype.val π.property, Equiv.swap_apply_left]
  · apply Subtype.ext
    change Equiv.swap y.val z.val (π.val.val x.val) = y.val
    rw [show π.val.val x.val = z.val from congrArg Subtype.val π.property, Equiv.swap_apply_right]
  · intro π
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext fun a ↦ Equiv.swap_apply_self y.val z.val (π.val.val a)
  · intro π
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext fun a ↦ Equiv.swap_apply_self y.val z.val (π.val.val a)

/-- Inversion reduces a backward-reply fiber to a forward-reply fiber. -/
noncomputable def backwardFiberEquiv (known : PartialPermutation α) (y : known.UnusedOutput)
    (x z : known.UnusedInput) :
    {π : known.Completion // known.backward y π = x} ≃
      {π : known.Completion // known.backward y π = z} :=
  let reversedFiber (a : known.UnusedInput) :
      {π : known.Completion // known.backward y π = a} ≃
        {π : known.symm.Completion // known.symm.forward y π = a} :=
    Equiv.subtypeEquiv known.completionSymm (fun _ ↦ Iff.rfl)
  (reversedFiber x).trans ((known.symm.forwardFiberEquiv y x z).trans (reversedFiber z).symm)

/-- All unused forward replies have equally many compatible full permutations. -/
theorem forward_fibers : LazyPermutationSpec.ForwardFibers := by
  intro α _ known x y z
  exact ⟨known.forwardFiberEquiv x y z⟩

/-- All unused backward replies have equally many compatible full permutations. -/
theorem backward_fibers : LazyPermutationSpec.BackwardFibers := by
  intro α _ known y x z
  exact ⟨known.backwardFiberEquiv y x z⟩

theorem uniformFinite_apply {β : Type*} [Finite β] [Nonempty β] (b : β) :
    uniformFinite β b = (Nat.card β : ℝ≥0∞)⁻¹ := by
  let := Fintype.ofFinite β
  rw [uniformFinite, uniformPMF_apply, Nat.card_eq_fintype_card]

/-- The expression using finiteness agrees with any enumeration of the same type. -/
theorem uniformFinite_eq_uniformOfFintype (β : Type*) [Fintype β] [Nonempty β] :
    uniformFinite β = uniformPMF β := by
  apply PMF.ext
  intro b
  rw [uniformFinite_apply, uniformPMF_apply, Nat.card_eq_fintype_card]

/-- The probability of an event is its fraction of the finite sample space. -/
theorem uniformFinite_event {β : Type*} [Finite β] [Nonempty β] (s : Set β) :
    (uniformFinite β).toOuterMeasure s = (Nat.card s : ℝ≥0∞) / Nat.card β := by
  let := Fintype.ofFinite β
  let := Fintype.ofFinite s
  rw [uniformFinite_eq_uniformOfFintype, toOuterMeasure_uniformPMF_apply,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- Filtering a uniform law is the uniform law on the subtype, included back into its ambient type.
-/
private theorem uniform_subtype_map {β : Type*} [Finite β] [Nonempty β]
    (s : Set β) [Nonempty s] (witness : ∃ a ∈ s, a ∈ (uniformFinite β).support) :
    (uniformFinite s).map Subtype.val = (uniformFinite β).filter s witness := by
  classical
  apply PMF.ext
  intro b
  by_cases hb : b ∈ s
  · have at_subtype (x : s) : ((uniformFinite s).map Subtype.val) x.val = uniformFinite s x := by
      simp [PMF.map_apply, Subtype.coe_inj]
    rw [at_subtype ⟨b, hb⟩, PMF.filter_apply, Set.indicator_of_mem hb,
      ← PMF.toOuterMeasure_apply, uniformFinite_event, uniformFinite_apply, uniformFinite_apply]
    have hβ : (Nat.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [ENNReal.inv_div (Or.inl (by simp)) (Or.inl hβ), div_eq_mul_inv,
      ENNReal.inv_mul_cancel_left hβ (by simp)]
  · rw [PMF.filter_apply_eq_zero_of_notMem witness hb, PMF.apply_eq_zero_iff]
    simp [PMF.support_map, hb]

/-- Pushing forward a uniform law through equal-sized fibers gives a uniform law. -/
private theorem uniform_map_of_fibers {A B : Type*} [Finite A] [Finite B] [Nonempty A] [Nonempty B]
    (f : A → B)
    (fibers : ∀ b c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})) :
    (uniformFinite A).map f = uniformFinite B := by
  let := Fintype.ofFinite B
  let law := (uniformFinite A).map f
  have mass (b : B) : law b = (Nat.card {a : A // f a = b} : ℝ≥0∞) / Nat.card A := by
    dsimp only [law]
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, uniformFinite_event]
    rfl
  apply PMF.ext
  intro b
  have constant (c : B) : law c = law b := by
    rw [mass, mass, Nat.card_congr (fibers c b).some]
  rw [uniformFinite_apply, Nat.card_eq_fintype_card]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  simpa only [tsum_fintype, constant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_comm] using law.tsum_coe

private theorem uniform_completion_map [Finite α] (known : PartialPermutation α) :
    letI : Nonempty known.Completion := ⟨known.complete⟩
    (uniformFinite known.Completion).map Subtype.val = known.conditionedUniform := by
  let : Nonempty ↑{π : Equiv.Perm α | known.Extends π} := ⟨known.complete⟩
  let : Nonempty (Equiv.Perm α) := ⟨Equiv.refl α⟩
  unfold conditionedUniform
  exact uniform_subtype_map {π | known.Extends π} _

/-- A uniform permutation conditioned on the known pairs answers a fresh forward query
uniformly among unused outputs. -/
theorem forward_uniform : LazyPermutationSpec.ForwardUniform := by
  intro α finite known x
  let : Nonempty known.Completion := ⟨known.complete⟩
  let : Nonempty known.UnusedOutput := ⟨known.forward x known.complete⟩
  have reply_uniform : (uniformFinite known.Completion).map (known.forward x) =
      known.uniformUnusedOutputs x :=
    uniform_map_of_fibers (known.forward x) (fun y z ↦ ⟨known.forwardFiberEquiv x y z⟩)
  rw [← uniform_completion_map known, ← reply_uniform, PMF.map_comp, PMF.map_comp]
  rfl

/-- A uniform permutation conditioned on the known pairs answers a fresh backward query
uniformly among unused inputs. -/
theorem backward_uniform : LazyPermutationSpec.BackwardUniform := by
  intro α finite known y
  let : Nonempty known.Completion := ⟨known.complete⟩
  let : Nonempty known.UnusedInput := ⟨known.backward y known.complete⟩
  have reply_uniform : (uniformFinite known.Completion).map (known.backward y) =
      known.uniformUnusedInputs y :=
    uniform_map_of_fibers (known.backward y) (fun x z ↦ ⟨known.backwardFiberEquiv y x z⟩)
  rw [← uniform_completion_map known, ← reply_uniform, PMF.map_comp, PMF.map_comp]
  rfl

end JH.PartialPermutation

namespace JH.Transcript

/-- Completing the partial bijection extracted from the log is equivalent to satisfying all
its records. The consistent witness supplies the values on the observed inputs. -/
theorem partialPermutation_extends_iff : LazyPermutationSpec.TranscriptCompletions := by
  intro n transcript witness consistent permutation
  constructor
  · intro completes i
    exact (completes ⟨(transcript.get i).input, ⟨i, rfl⟩⟩).trans (consistent i)
  · intro agrees x
    obtain ⟨i, equal⟩ := x.property
    change permutation x.val = witness x.val
    rw [← equal]
    exact (agrees i).trans (Eq.symm (consistent i))

end JH.Transcript
