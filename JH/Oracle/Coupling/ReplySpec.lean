/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.PermutationSpec

/-!
# Couple a fresh permutation reply with a uniform reply

A fresh permutation reply coupled with an independent reply, as in Section 3.2.
-/

@[expose] public section

namespace JH

open scoped ENNReal

universe u v

namespace ReplyCoupling

/-- Draw the two coordinates independently from their respective laws. -/
noncomputable def independentPair {α : Type u} {β : Type v} (first : PMF α)
    (second : PMF β) : PMF (α × β) :=
  first.bind fun a ↦ second.map fun b ↦ (a, b)

/-- Use a uniform proposal for the independent experiment. The permutation experiment
uses the proposal if available and an independent uniform spare otherwise. -/
noncomputable def sample {α : Type u} [Finite α] [Nonempty α]
    (unused : Set α) [Nonempty unused] : PMF (α × α) := by
  classical
  exact (independentPair (PartialPermutation.uniformFinite α)
    (PartialPermutation.uniformFinite unused)).map fun pair ↦
      (if pair.1 ∈ unused then pair.1 else pair.2.val, pair.1)

end ReplyCoupling

namespace PartialPermutation

variable {α : Type u} [Finite α]

/-- Couple a fresh forward permutation reply with a uniform proposal at an unused input. -/
noncomputable def coupleForward (known : PartialPermutation α) (x : known.UnusedInput) :
    PMF (α × α) :=
  letI : Nonempty α := ⟨x.val⟩
  letI : Nonempty ↥(known.outputsᶜ) := ⟨known.forward x known.complete⟩
  ReplyCoupling.sample known.outputsᶜ

/-- Couple a fresh inverse reply with a uniform proposal by inverting the partial permutation. -/
noncomputable def coupleBackward (known : PartialPermutation α) (y : known.UnusedOutput) :
    PMF (α × α) :=
  known.symm.coupleForward y

end PartialPermutation

namespace Query

/-- Given the forward input, record a reply by its rate and the record shift. -/
def forwardReplyCoords {n : ℕ} (x : State n) : State n ≃ (Word n × Word n) where
  toFun y := (y.2, x.2 ^^^ y.1)
  invFun coords := (x.2 ^^^ coords.2, coords.1)
  left_inv y := by simp [← BitVec.xor_assoc]
  right_inv coords := by simp [← BitVec.xor_assoc]

/-- Given the backward output, record a reply by its capacity and the record shift. -/
def backwardReplyCoords {n : ℕ} (y : State n) : State n ≃ (Word n × Word n) where
  toFun x := (x.1, x.2 ^^^ y.1)
  invFun coords := (coords.1, coords.2 ^^^ y.1)
  left_inv x := by simp [BitVec.xor_assoc]
  right_inv coords := by simp [BitVec.xor_assoc]

/-- Convert a reply to the random coordinate and shift for the requested direction. -/
def replyCoords {n : ℕ} (request : Query n) : State n ≃ (Word n × Word n) :=
  match request.direction with
  | .forward => forwardReplyCoords request.address
  | .backward => backwardReplyCoords request.address

end Query

namespace ReplyCouplingSpec

/-- Draw a full-space proposal and draw a replacement only if the proposal is forbidden. -/
def ConditionalReplacement : Prop := by
  classical
  exact ∀ {α : Type u} [Finite α] [Nonempty α] (unused : Set α) [Nonempty unused],
    ReplyCoupling.sample unused = (PartialPermutation.uniformFinite α).bind fun proposal ↦
      if proposal ∈ unused then PMF.pure (proposal, proposal)
      else (PartialPermutation.uniformFinite unused).map fun spare ↦ (spare.val, proposal)

/-- The permutation marginal is uniform on the unused replies. -/
def FirstMarginal : Prop :=
  ∀ {α : Type u} [Finite α] [Nonempty α] (unused : Set α) [Nonempty unused],
    (ReplyCoupling.sample unused).map Prod.fst =
      (PartialPermutation.uniformFinite unused).map Subtype.val

/-- The independent marginal is uniform on the entire reply space. -/
def SecondMarginal : Prop :=
  ∀ {α : Type u} [Finite α] [Nonempty α] (unused : Set α) [Nonempty unused],
    (ReplyCoupling.sample unused).map Prod.snd = PartialPermutation.uniformFinite α

/-- In every supported pair, the permutation reply is unused and the two replies agree
exactly when the independent reply is unused. -/
def SupportedReplies : Prop :=
  ∀ {α : Type u} [Finite α] [Nonempty α] (unused : Set α) [Nonempty unused] (pair : α × α),
    pair ∈ (ReplyCoupling.sample unused).support →
      pair.1 ∈ unused ∧ (pair.1 = pair.2 ↔ pair.2 ∈ unused)

/-- The probability of disagreement is the fraction of forbidden replies. -/
def Disagreement : Prop :=
  ∀ {α : Type u} [Finite α] [Nonempty α] (unused : Set α) [Nonempty unused],
    (ReplyCoupling.sample unused).toOuterMeasure {pair | pair.1 ≠ pair.2} =
      (Nat.card ↑(unusedᶜ) : ℝ≥0∞) / Nat.card α

/-- The first marginal agrees with the full permutation conditioned on the old pairs. -/
def ForwardPermutationMarginal : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (x : known.UnusedInput),
    (known.coupleForward x).map Prod.fst = known.conditionedUniform.map (fun π ↦ π x.val)

/-- The first marginal of the inverse coupling is the inverse reply of a uniform completion. -/
def BackwardPermutationMarginal : Prop :=
  ∀ {α : Type u} [Finite α] (known : PartialPermutation α) (y : known.UnusedOutput),
    (known.coupleBackward y).map Prod.fst = known.conditionedUniform.map (fun π ↦ π.symm y.val)

/-- For either query direction, the random coordinate and shift are independent uniform words. -/
def IndependentCoordinates : Prop :=
  ∀ {n : ℕ} (request : Query n),
    (PartialPermutation.uniformFinite (State n)).map request.replyCoords =
      ReplyCoupling.independentPair (PartialPermutation.uniformFinite (Word n))
        (PartialPermutation.uniformFinite (Word n))

/-- A uniform reply gives independent uniform intrinsic and offset coordinates. -/
def IndependentCoordinatesMass : Prop :=
  ∀ {n : ℕ} (request : Query n) (coordinate shift : Word n),
    ((PartialPermutation.uniformFinite (State n)).map request.replyCoords) (coordinate, shift) =
      PartialPermutation.uniformFinite (Word n) coordinate *
        PartialPermutation.uniformFinite (Word n) shift

/-- Reconstructing a reply from the independent coordinate and shift gives a uniform state. -/
def UniformReplyFromCoordinates : Prop :=
  ∀ {n : ℕ} (request : Query n),
    (ReplyCoupling.independentPair (PartialPermutation.uniformFinite (Word n))
      (PartialPermutation.uniformFinite (Word n))).map request.replyCoords.symm =
        PartialPermutation.uniformFinite (State n)

end ReplyCouplingSpec

end JH
