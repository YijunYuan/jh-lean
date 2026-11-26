/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.ReplySpec
public import JH.Oracle.Lazy.Permutation

/-!
# Couple a fresh permutation reply with a uniform reply

The independent experiment uses a uniform proposal from the whole state space. The permutation
experiment shares it when unused and uses a uniform unused replacement otherwise. Exchanging
the proposal and a spare unused reply on the accepted branch proves the permutation marginal.
The same module identifies the independent reply law with two independent uniform words.
-/

@[expose] public section

namespace JH

open scoped ENNReal

universe u v

namespace ReplyCoupling

open PartialPermutation (uniformFinite uniformFinite_apply)

variable {α : Type u} {β : Type v}

private theorem map_apply_of_injective (law : PMF α) {f : α → β}
    (injective : Function.Injective f) (a : α) : (law.map f) (f a) = law a := by
  classical
  simp [PMF.map_apply, injective.eq_iff]

theorem independentPair_apply (first : PMF α) (second : PMF β) (a : α) (b : β) :
    independentPair first second (a, b) = first a * second b := by
  classical
  rw [independentPair, PMF.bind_apply, tsum_eq_single a]
  · simp [PMF.map_apply]
  · intro other ne
    simp [PMF.map_apply, Ne.symm ne]

theorem independentPair_map_fst (first : PMF α) (second : PMF β) :
    (independentPair first second).map Prod.fst = first := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp]
  change first.bind (fun a ↦ second.map (Function.const β a)) = first
  simp

theorem independentPair_map_snd (first : PMF α) (second : PMF β) :
    (independentPair first second).map Prod.snd = second := by
  simp only [independentPair, PMF.map_bind, PMF.map_comp]
  change (first.bind fun _ ↦ second.map id) = second
  rw [PMF.map_id, PMF.bind_const]

theorem uniformFinite_map_equiv [Finite α] [Finite β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) : (uniformFinite α).map e = uniformFinite β := by
  apply PMF.ext
  intro b
  have atPreimage := map_apply_of_injective (uniformFinite α) e.injective (e.symm b)
  rw [Equiv.apply_symm_apply] at atPreimage
  rw [atPreimage, uniformFinite_apply, uniformFinite_apply, Nat.card_congr e]

theorem independentPair_uniform [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    independentPair (uniformFinite α) (uniformFinite β) = uniformFinite (α × β) := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [independentPair_apply, uniformFinite_apply, uniformFinite_apply, uniformFinite_apply,
    Nat.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]

/-- Draw a full-space proposal and draw a replacement only if the proposal is forbidden. -/
theorem sample_eq_conditional_replacement : ReplyCouplingSpec.ConditionalReplacement := by
  intro α _ _ unused _
  classical
  rw [sample, independentPair, PMF.map_bind]
  congr 1
  funext proposal
  rw [PMF.map_comp]
  by_cases available : proposal ∈ unused
  · simpa only [Function.comp_def, Function.const_def, ite_eq_left available] using
      PMF.map_const (uniformFinite unused) (proposal, proposal)
  · simp only [Function.comp_def, ite_eq_right available]

/-- When the full-space proposal is unused, exchanging it with the spare
is an involution of the full reply space times the unused reply space. -/
private noncomputable def exchangeUnused (unused : Set α) : (α × unused) ≃ (α × unused) := by
  classical
  let exchange (pair : α × unused) : α × unused :=
    if mem : pair.1 ∈ unused then (pair.2.val, ⟨pair.1, mem⟩) else pair
  have twice : Function.Involutive exchange := by
    rintro ⟨proposal, spare⟩
    by_cases mem : proposal ∈ unused
    · simp [exchange, mem, spare.property]
    · simp [exchange, mem]
  exact ⟨exchange, exchange, twice, twice⟩

/-- The permutation marginal is uniform on the unused replies. -/
theorem sample_map_fst : ReplyCouplingSpec.FirstMarginal := by
  intro α _ _ unused _
  classical
  let draws := independentPair (uniformFinite α) (uniformFinite unused)
  let exchange := exchangeUnused unused
  -- Swapping an accepted proposal with the spare preserves the uniform law on the product.
  have invariant : draws.map exchange = draws := by
    dsimp only [draws]
    rw [independentPair_uniform, uniformFinite_map_equiv]
  calc
    (sample unused).map Prod.fst = (draws.map exchange).map (Subtype.val ∘ Prod.snd) := by
      unfold sample
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext pair
      by_cases mem : pair.1 ∈ unused <;> simp [exchange, exchangeUnused, mem]
    _ = (uniformFinite unused).map Subtype.val := by
      rw [invariant, ← PMF.map_comp, independentPair_map_snd]

/-- The independent marginal has the full uniform reply law because it retains the proposal. -/
theorem sample_map_snd : ReplyCouplingSpec.SecondMarginal := by
  intro α _ _ unused _
  unfold sample
  rw [PMF.map_comp]
  exact independentPair_map_fst _ _

/-- In every supported pair, the permutation reply is unused and the two replies agree exactly
when the independent reply is unused. -/
theorem sample_support : ReplyCouplingSpec.SupportedReplies := by
  intro α _ _ unused _ pair supported
  classical
  rw [sample] at supported
  obtain ⟨⟨proposal, spare⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  by_cases mem : proposal ∈ unused
  · simp [mem]
  · have distinct : spare.val ≠ proposal := fun equal ↦ mem (equal ▸ spare.property)
    simp [mem, spare.property, distinct]

theorem uniformFinite_event [Finite α] [Nonempty α] (s : Set α) :
    (uniformFinite α).toOuterMeasure s = (Nat.card s : ℝ≥0∞) / Nat.card α :=
  PartialPermutation.uniformFinite_event s

/-- Disagreement has the same probability as proposing a forbidden reply. -/
theorem sample_disagreement : ReplyCouplingSpec.Disagreement := by
  intro α _ _ unused _
  calc
    (sample unused).toOuterMeasure {pair | pair.1 ≠ pair.2} =
        (sample unused).toOuterMeasure (Prod.snd ⁻¹' unusedᶜ) := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext pair
      change (pair.1 ≠ pair.2 ∧ pair ∈ (sample unused).support) ↔
        (pair.2 ∉ unused ∧ pair ∈ (sample unused).support)
      exact and_congr_left fun supported ↦ (sample_support unused pair supported).2.not
    _ = (uniformFinite α).toOuterMeasure unusedᶜ := by
      rw [← PMF.toOuterMeasure_map_apply, sample_map_snd]
    _ = _ := uniformFinite_event _

end ReplyCoupling

namespace PartialPermutation

variable {α : Type u} [Finite α]

theorem coupleForward_map_fst (known : PartialPermutation α) (x : known.UnusedInput) :
    (known.coupleForward x).map Prod.fst = (known.uniformUnusedOutputs x).map Subtype.val := by
  let : Nonempty α := ⟨x.val⟩
  let : Nonempty ↥(known.outputsᶜ) := ⟨known.forward x known.complete⟩
  exact ReplyCoupling.sample_map_fst known.outputsᶜ

theorem coupleForward_map_snd (known : PartialPermutation α) (x : known.UnusedInput) :
    letI : Nonempty α := ⟨x.val⟩
    (known.coupleForward x).map Prod.snd = uniformFinite α := by
  let : Nonempty α := ⟨x.val⟩
  let : Nonempty ↥(known.outputsᶜ) := ⟨known.forward x known.complete⟩
  exact ReplyCoupling.sample_map_snd known.outputsᶜ

theorem coupleForward_support (known : PartialPermutation α) (x : known.UnusedInput)
    (pair : α × α) (supported : pair ∈ (known.coupleForward x).support) :
    pair.1 ∉ known.outputs ∧ (pair.1 = pair.2 ↔ pair.2 ∉ known.outputs) := by
  let : Nonempty α := ⟨x.val⟩
  let : Nonempty ↥(known.outputsᶜ) := ⟨known.forward x known.complete⟩
  exact ReplyCoupling.sample_support known.outputsᶜ pair supported

theorem coupleForward_disagreement (known : PartialPermutation α) (x : known.UnusedInput) :
    (known.coupleForward x).toOuterMeasure {pair | pair.1 ≠ pair.2} =
      (Nat.card known.outputs : ℝ≥0∞) / Nat.card α := by
  let : Nonempty α := ⟨x.val⟩
  let : Nonempty ↥(known.outputsᶜ) := ⟨known.forward x known.complete⟩
  simpa only [coupleForward, compl_compl] using ReplyCoupling.sample_disagreement known.outputsᶜ

theorem coupleBackward_map_fst (known : PartialPermutation α) (y : known.UnusedOutput) :
    (known.coupleBackward y).map Prod.fst = (known.uniformUnusedInputs y).map Subtype.val :=
  known.symm.coupleForward_map_fst y

theorem coupleBackward_map_snd (known : PartialPermutation α) (y : known.UnusedOutput) :
    letI : Nonempty α := ⟨y.val⟩
    (known.coupleBackward y).map Prod.snd = uniformFinite α :=
  known.symm.coupleForward_map_snd y

theorem coupleBackward_support (known : PartialPermutation α) (y : known.UnusedOutput)
    (pair : α × α) (supported : pair ∈ (known.coupleBackward y).support) :
    pair.1 ∉ known.inputs ∧ (pair.1 = pair.2 ↔ pair.2 ∉ known.inputs) :=
  known.symm.coupleForward_support y pair supported

theorem coupleBackward_disagreement (known : PartialPermutation α) (y : known.UnusedOutput) :
    (known.coupleBackward y).toOuterMeasure {pair | pair.1 ≠ pair.2} =
      (Nat.card known.inputs : ℝ≥0∞) / Nat.card α :=
  known.symm.coupleForward_disagreement y

/-- The first marginal agrees with the full permutation conditioned on the old pairs. -/
theorem coupleForward_permutation_marginal : ReplyCouplingSpec.ForwardPermutationMarginal := by
  intro α _ known x
  exact (known.coupleForward_map_fst x).trans (forward_uniform known x).symm

/-- The first marginal of the inverse coupling is the inverse reply of a uniform completion. -/
theorem coupleBackward_permutation_marginal : ReplyCouplingSpec.BackwardPermutationMarginal := by
  intro α _ known y
  exact (known.coupleBackward_map_fst y).trans (backward_uniform known y).symm

end PartialPermutation

namespace Query

/-- In either direction, the intrinsic coordinate and the XOR offset are uniform and independent. -/
theorem uniform_reply_coords : ReplyCouplingSpec.IndependentCoordinates := by
  intro n request
  rw [ReplyCoupling.uniformFinite_map_equiv, ReplyCoupling.independentPair_uniform]

/-- A uniform reply gives independent uniform intrinsic and offset coordinates. -/
theorem uniform_reply_coords_mass : ReplyCouplingSpec.IndependentCoordinatesMass := by
  intro n request coordinate shift
  rw [uniform_reply_coords, ReplyCoupling.independentPair_apply]

/-- Reconstructing a reply from the independent coordinate and shift gives a uniform state. -/
theorem uniform_reply_from_coords : ReplyCouplingSpec.UniformReplyFromCoordinates := by
  intro n request
  rw [ReplyCoupling.independentPair_uniform, ReplyCoupling.uniformFinite_map_equiv]

end Query

end JH
