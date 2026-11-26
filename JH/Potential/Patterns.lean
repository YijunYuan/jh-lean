/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.Endpoints
public import JH.Graph.AddedPath
public import JH.Graph.Evolution.Round
public import JH.Potential.PatternsSpec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Translated patterns and ancestor groups

A pattern fixes a target column and a translated set of target rates. Old endpoint supports
identify eligible new inputs by XOR translation. The proof of Lemma 4 uses this identification
to group the ancestors, and (21) bounds the number and total size of the nonempty restricted
supports across translations.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

theorem xor_right_cancel (a b : Word n) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_left_cancel (a b : Word n) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem mem_xorTranslate {offset word : Word n} {mode : Finset (Word n)} :
    word ∈ xorTranslate offset mode ↔ offset ^^^ word ∈ mode := by
  constructor
  · intro present
    obtain ⟨delta, hdelta, rfl⟩ := Finset.mem_image.mp present
    simpa only [xor_left_cancel] using hdelta
  · intro present
    exact Finset.mem_image.mpr ⟨offset ^^^ word, present, xor_left_cancel offset word⟩

theorem mem_restrictedLeftSupport {pairs : Finset (Word n × Word n)}
    {rates : Finset (Word n)} {capacity : Word n} :
    capacity ∈ restrictedLeftSupport pairs rates ↔
      ∃ rate ∈ rates, (capacity, rate) ∈ pairs := by
  constructor
  · intro member
    obtain ⟨⟨a, b⟩, hpair, rfl⟩ := Finset.mem_image.mp member
    exact ⟨b, (Finset.mem_filter.mp hpair).2, (Finset.mem_filter.mp hpair).1⟩
  · rintro ⟨rate, allowed, related⟩
    exact Finset.mem_image.mpr ⟨(capacity, rate), Finset.mem_filter.mpr ⟨related, allowed⟩, rfl⟩

/-- The new inputs whose outputs reach the target pattern by old edges form a
pattern in the current record's input column. -/
theorem input_pattern_identification : PatternsSpec.InputIdentification := by
  intro n transcript record vertices column mode offset
  ext x
  constructor
  · rintro ⟨y, newEdge, b, inside, suffix⟩
    have step : record.edge x.val y.val := newEdge
    have capacity := congrArg (fun state : State n ↦ state.1) step.2
    have outputRow := congrArg (fun state : State n ↦ state.2) step.2
    change y.val.1 = x.val.2 ^^^ record.shift at capacity
    change y.val.2 = record.output.2 at outputRow
    obtain ⟨_, targetColumn, targetRate⟩ := inside
    have paired : (y.val.1, b.val.2) ∈
        endpointPairs (realRecordRelation transcript) vertices y.val.2 b.val.1 :=
      mem_endpointPairs.mpr (reachesWithin_iff_residual.mpr suffix)
    rw [outputRow, targetColumn] at paired
    have support := mem_restrictedLeftSupport.mpr ⟨b.val.2, targetRate, paired⟩
    refine ⟨x.property, step.1, mem_xorTranslate.mpr ?_⟩
    simpa only [capacity, BitVec.xor_comm record.shift x.val.2] using support
  · rintro ⟨_, inputColumn, inputRate⟩
    obtain ⟨rate, allowed, paired⟩ :=
      mem_restrictedLeftSupport.mp (mem_xorTranslate.mp inputRate)
    have reach := mem_endpointPairs.mp paired
    let y : vertices := ⟨(record.shift ^^^ x.val.2, record.output.2), reach.1⟩
    let b : vertices := ⟨(column, rate), reach.2.1⟩
    have oldSuffix : Reaches (residualRelation (realRecordRelation transcript) vertices) y b :=
      (reachesWithin_iff_residual (a := y) (b := b)).mp reach
    refine ⟨y, ⟨inputColumn, ?_⟩, b, ⟨b.property, rfl, allowed⟩, oldSuffix⟩
    exact Prod.ext (BitVec.xor_comm _ _) rfl

private theorem appended_residual_relation (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) :
    residualRelation (realRecordRelation (transcript ++ [record])) vertices =
      addedRelation (residualRecordEdge transcript vertices) (residualNewEdge record vertices) := by
  funext a b
  exact propext (realRecordRelation_append transcript record a.val b.val)

private theorem rowAncestorsTo_as_image (edge : State n → State n → Prop)
    (vertices : Set (State n)) (row : Word n) (targets : Set (State n)) :
    rowAncestorsTo edge vertices row targets =
      Subtype.val '' (rowVertices vertices row ∩
        ancestorsOf (residualRelation edge vertices) (Subtype.val ⁻¹' targets)) := by
  ext source
  constructor
  · rintro ⟨fromRow, target, ht, reach⟩
    let a : vertices := ⟨source, reach.1⟩
    let b : vertices := ⟨target, reach.2.1⟩
    exact ⟨a, ⟨fromRow, b, ht, reachesWithin_iff_residual.mp reach⟩, rfl⟩
  · rintro ⟨a, ⟨fromRow, b, ht, reach⟩, rfl⟩
    exact ⟨fromRow, b.val, ht, reachesWithin_iff_residual.mpr reach⟩

/-- When every walk to the pattern uses the current label at most once, the enlarged
row-ancestor set is exactly the union of the two old-graph groups in the proof of Lemma 4. -/
theorem pattern_two_groups : PatternsSpec.TwoGroups := by
  intro n transcript record vertices row column mode offset noReuse
  let targets := columnPattern vertices column mode offset
  -- Apply the generic split on the residual subtype before restricting the source row.
  have splitAncestor :=
    no_reuse_ancestors (residualRecordEdge transcript vertices) (residualNewEdge record vertices)
      (Subtype.val ⁻¹' targets) (fun {a b} inside walk ↦ by
        exact le_of_not_gt (fun twice ↦ noReuse ⟨a, b, inside, walk, twice⟩))
  rw [input_pattern_identification transcript record vertices column mode offset] at splitAncestor
  simp only [rowAncestorsTo_as_image]
  rw [appended_residual_relation, splitAncestor, Set.inter_union_distrib_left, Set.image_union]
  rfl

/-- Bound restricted support size at one offset, the number of offsets with nonempty
support, and the sum of support sizes over all offsets. -/
theorem translation_counts : PatternsSpec.TranslationCounts := by
  intro n pairs mode
  classical
  constructor
  · intro offset
    apply Finset.card_le_card
    exact Finset.image_mono Prod.fst (Finset.filter_subset _ _)
  constructor
  · let possible := ((rightSupport pairs) ×ˢ mode).image fun p ↦ p.1 ^^^ p.2
    have included : nonemptySupportOffsets pairs mode ⊆ possible := by
      intro offset appears
      obtain ⟨capacity, inSupport⟩ := (Finset.mem_filter.mp appears).2
      obtain ⟨rate, translated, pair⟩ := mem_restrictedLeftSupport.mp inSupport
      obtain ⟨delta, inMode, rfl⟩ := Finset.mem_image.mp translated
      have right : offset ^^^ delta ∈ rightSupport pairs :=
        Finset.mem_image.mpr ⟨(capacity, offset ^^^ delta), pair, rfl⟩
      exact Finset.mem_image.mpr
        ⟨(offset ^^^ delta, delta), Finset.mem_product.mpr ⟨right, inMode⟩, xor_right_cancel _ _⟩
    calc
      _ ≤ possible.card := Finset.card_le_card included
      _ ≤ ((rightSupport pairs) ×ˢ mode).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_product, Nat.mul_comm]
  · let atOffset (offset : Word n) := pairs.filter fun p ↦ p.2 ∈ xorTranslate offset mode
    -- Charge a pair at this offset to the pair and the unique mode element producing
    -- its final rate. XOR cancellation recovers the offset.
    let incidences := (Finset.univ : Finset (Word n)).sigma atOffset
    let charge (entry : Σ _ : Word n, Word n × Word n) :=
      (entry.2, entry.1 ^^^ entry.2.2)
    have charged : Set.MapsTo charge (incidences : Set (Σ _ : Word n, Word n × Word n))
        (↑(pairs ×ˢ mode) : Set ((Word n × Word n) × Word n)) := by
      intro entry present
      obtain ⟨pair, translates⟩ := Finset.mem_filter.mp (Finset.mem_sigma.mp present).2
      exact Finset.mem_product.mpr ⟨pair, mem_xorTranslate.mp translates⟩
    have injective : Function.Injective charge := by
      rintro ⟨offset1, pair1⟩ ⟨offset2, pair2⟩ equal
      have samePair := congrArg Prod.fst equal
      change pair1 = pair2 at samePair
      subst pair2
      have sameShift := congrArg (fun p : (Word n × Word n) × Word n ↦ p.2) equal
      change offset1 ^^^ pair1.2 = offset2 ^^^ pair1.2 at sameShift
      have sameOffset := congrArg (fun word ↦ word ^^^ pair1.2) sameShift
      simp only [xor_right_cancel] at sameOffset
      subst offset2
      rfl
    calc
      _ ≤ ∑ offset : Word n, (atOffset offset).card :=
        Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
      _ = incidences.card := (Finset.card_sigma _ _).symm
      _ ≤ (pairs ×ˢ mode).card :=
        Finset.card_le_card_of_injOn charge charged injective.injOn
      _ = _ := by rw [Finset.card_product, Nat.mul_comm]

end JH.Graph
