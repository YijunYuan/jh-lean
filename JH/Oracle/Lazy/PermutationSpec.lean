/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.ExperimentSpec
public import JH.Probability.UniformPMF
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fintype

/-!
# Fresh replies of a conditioned permutation

The conditional reply laws for the permutation oracle in Section 3.2.
-/

@[expose] public section

namespace JH

universe u

/-- The pairs already revealed by either direction of a permutation oracle. -/
structure PartialPermutation (α : Type u) where
  /-- Inputs whose images have been disclosed. -/
  inputs : Set α
  /-- Outputs whose preimages have been disclosed. -/
  outputs : Set α
  /-- The disclosed bijection between known inputs and outputs. -/
  matching : inputs ≃ outputs

namespace PartialPermutation

variable {α : Type u}

/-- An address outside the known inputs of the partial permutation. -/
abbrev UnusedInput (known : PartialPermutation α) := { x : α // x ∉ known.inputs }

/-- An address outside the known outputs of the partial permutation. -/
abbrev UnusedOutput (known : PartialPermutation α) := { y : α // y ∉ known.outputs }

/-- A full permutation agrees with all the revealed pairs. -/
def Extends (known : PartialPermutation α) (permutation : Equiv.Perm α) : Prop :=
  ∀ x : known.inputs, permutation x = (known.matching x : α)

/-- A full permutation extending all known pairs. -/
abbrev Completion (known : PartialPermutation α) :=
  { permutation : Equiv.Perm α // known.Extends permutation }

/-- Reverse all the revealed pairs. -/
def symm (known : PartialPermutation α) : PartialPermutation α :=
  ⟨known.outputs, known.inputs, known.matching.symm⟩

/-- Inverting a full permutation preserves agreement with the reversed pairs. -/
def completionSymm (known : PartialPermutation α) :
    known.Completion ≃ known.symm.Completion where
  toFun completion := ⟨completion.val.symm, fun y ↦ by
    apply completion.val.injective
    rw [completion.val.apply_symm_apply]
    change _ = completion.val (known.matching.symm y)
    rw [completion.property (known.matching.symm y)]
    exact (congrArg Subtype.val (known.matching.apply_symm_apply y)).symm⟩
  invFun completion := ⟨completion.val.symm, fun x ↦ by
    apply completion.val.injective
    rw [completion.val.apply_symm_apply, completion.property (known.matching x)]
    exact (congrArg Subtype.val (known.matching.symm_apply_apply x)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fresh forward query can only return an unused output. -/
def forward (known : PartialPermutation α) (x : known.UnusedInput)
    (completion : known.Completion) : known.UnusedOutput :=
  ⟨completion.val x.val, fun used ↦ by
    let old := known.matching.symm ⟨completion.val x.val, used⟩
    have same : completion.val old.val = completion.val x.val :=
      (completion.property old).trans (congrArg Subtype.val (known.matching.apply_symm_apply _))
    exact x.property (completion.val.injective same ▸ old.property)⟩

/-- A fresh backward query can only return an unused input. -/
def backward (known : PartialPermutation α) (y : known.UnusedOutput)
    (completion : known.Completion) : known.UnusedInput :=
  known.symm.forward y (known.completionSymm completion)

/-- Combine the revealed bijection with a bijection of the two complements. -/
noncomputable def complete [Finite α] (known : PartialPermutation α) : known.Completion := by
  classical
  exact ⟨known.matching.extendSubtype,
    fun x ↦ known.matching.extendSubtype_apply_of_mem x.val x.property⟩

/-- Uniform law with the enumeration supplied by finiteness. -/
noncomputable def uniformFinite (β : Type*) [Finite β] [Nonempty β] : PMF β :=
  @uniformPMF β (Fintype.ofFinite β) _

/-- The full uniform permutation conditioned on agreeing with all revealed pairs. -/
noncomputable def conditionedUniform [Finite α] (known : PartialPermutation α) :
    PMF (Equiv.Perm α) := by
  letI := Fintype.ofFinite α
  classical
  letI : Nonempty (Equiv.Perm α) := ⟨Equiv.refl α⟩
  refine (uniformFinite (Equiv.Perm α)).filter {π | known.Extends π} ?_
  exact ⟨known.complete.val, known.complete.property,
    @mem_support_uniformPMF (Equiv.Perm α) (Fintype.ofFinite _) _ _⟩

/-- The fresh forward input itself guarantees that the unused output set is nonempty. -/
noncomputable def uniformUnusedOutputs [Finite α] (known : PartialPermutation α)
    (x : known.UnusedInput) : PMF known.UnusedOutput :=
  letI : Nonempty known.UnusedOutput := ⟨known.forward x known.complete⟩
  uniformFinite _

/-- The fresh backward output itself guarantees that the unused input set is nonempty. -/
noncomputable def uniformUnusedInputs [Finite α] (known : PartialPermutation α)
    (y : known.UnusedOutput) : PMF known.UnusedInput :=
  known.symm.uniformUnusedOutputs y

end PartialPermutation

namespace Transcript

variable {n : ℕ}

/-- The input addresses in the old records, regardless of the access directions. -/
def observedInputs (transcript : Transcript n) : Set (State n) :=
  {x | ∃ i : Fin transcript.length, (transcript.get i).input = x}

/-- The output addresses in the old records, regardless of the access directions. -/
def observedOutputs (transcript : Transcript n) : Set (State n) :=
  {y | ∃ i : Fin transcript.length, (transcript.get i).output = y}

/-- Read the revealed pairs from a transcript that is consistent with a permutation. -/
def partialPermutation (transcript : Transcript n) (witness : Permutation n)
    (consistent : transcript.Consistent witness) : PartialPermutation (State n) := by
  refine ⟨transcript.observedInputs, transcript.observedOutputs,
    Equiv.subtypeEquiv witness (fun x ↦ ?_)⟩
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, Eq.symm (consistent i)⟩
  · rintro ⟨i, equal⟩
    exact ⟨i, witness.injective ((consistent i).trans equal)⟩

end Transcript

namespace LazyPermutationSpec

/-- The consistent full permutations are exactly the completions of the recorded pairs. -/
def TranscriptCompletions : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (witness : Permutation n)
    (consistent : transcript.Consistent witness) (permutation : Permutation n),
    (transcript.partialPermutation witness consistent).Extends permutation ↔
      transcript.Consistent permutation

/-- All unused forward replies have equally many compatible full permutations. -/
def ForwardFibers : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (x : known.UnusedInput)
    (y z : known.UnusedOutput),
    Nonempty ({π : known.Completion // known.forward x π = y} ≃
      {π : known.Completion // known.forward x π = z})

/-- All unused backward replies have equally many compatible full permutations. -/
def BackwardFibers : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (y : known.UnusedOutput)
    (x z : known.UnusedInput),
    Nonempty ({π : known.Completion // known.backward y π = x} ≃
      {π : known.Completion // known.backward y π = z})

/-- A fresh forward query under the conditioned uniform permutation is uniform on unused outputs. -/
def ForwardUniform : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (x : known.UnusedInput),
    known.conditionedUniform.map (fun π ↦ π x.val) =
      (known.uniformUnusedOutputs x).map Subtype.val

/-- The reverse reply law gives uniformity on unused inputs. -/
def BackwardUniform : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (y : known.UnusedOutput),
    known.conditionedUniform.map (fun π ↦ π.symm y.val) =
      (known.uniformUnusedInputs y).map Subtype.val

end LazyPermutationSpec

end JH
