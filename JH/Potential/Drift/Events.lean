/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.ShiftTest
public import JH.ModelProofs
public import JH.Potential.Drift.EventsSpec
public import JH.Potential.Patterns

/-!
# Shift events for a fixed pattern

Fix the old graph, the new record's exposed coordinates and a target pattern. An old path to an
eligible new input constrains the shift by two endpoint supports. Reuse of the current label
implies such an old path from the new output row, by looking between its last two uses.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

theorem uniform_shift_mass_card (event : Set (Word n)) :
    uniformShiftMass event = (event.ncard : ℝ) / (2 : ℝ) ^ n := by
  classical
  let : Fintype event := Fintype.ofFinite _
  rw [uniformShiftMass, toOuterMeasure_uniformPMF_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ← Nat.card_eq_fintype_card (α := event),
    Nat.card_coe_set_eq, word_card n, Nat.cast_pow, Nat.cast_ofNat]

theorem uniform_shift_mass_le {event : Set (Word n)} {candidates : Finset (Word n)}
    {bound : ℕ} (subset : event ⊆ (candidates : Set (Word n))) (size : candidates.card ≤ bound) :
    uniformShiftMass event ≤ (bound : ℝ) / (2 : ℝ) ^ n := by
  rw [uniform_shift_mass_card]
  have eventSize : event.ncard ≤ candidates.card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_mono subset
  exact div_le_div_of_nonneg_right (by exact_mod_cast eventSize.trans size) (by positivity)

theorem uniform_shift_mass_mono {first second : Set (Word n)} (subset : first ⊆ second) :
    uniformShiftMass first ≤ uniformShiftMass second := by
  rw [uniform_shift_mass_card, uniform_shift_mass_card]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Set.ncard_mono subset)) (by positivity)

private theorem input_ancestor_shift {transcript : Transcript n} {record : Record n}
    {vertices : Set (State n)} {row column : Word n} {mode : Finset (Word n)} {offset : Word n}
    (nonempty : (rowAncestorsTo (realRecordRelation transcript) vertices row
      (inputPattern transcript record vertices column mode offset)).Nonempty) :
    record.shift ∈ xorOffsets
      (rightSupport (endpointPairs (realRecordRelation transcript) vertices row record.input.1))
      (patternOutletSupport transcript vertices record.output.2 column mode offset) := by
  obtain ⟨source, fromRow, input, inputIn, reach⟩ := nonempty
  obtain ⟨_, inputColumn, inputRate⟩ := inputIn
  have pair : (source.1, input.2) ∈
      endpointPairs (realRecordRelation transcript) vertices source.2 input.1 :=
    mem_endpointPairs.mpr reach
  rw [fromRow, inputColumn] at pair
  have rateMem : input.2 ∈ rightSupport
      (endpointPairs (realRecordRelation transcript) vertices row record.input.1) :=
    Finset.mem_image.mpr ⟨_, pair, rfl⟩
  obtain ⟨capacity, capMem, shiftEq⟩ := Finset.mem_image.mp inputRate
  have recovered : input.2 ^^^ capacity = record.shift := by
    rw [← shiftEq, xor_right_cancel]
  exact Finset.mem_image.mpr
    ⟨(input.2, capacity), Finset.mem_product.mpr ⟨rateMem, capMem⟩, recovered⟩

/-- Between the last two new uses, an old path leads from the output row of the
current record to an eligible input for the target pattern. -/
theorem reuse_implies_output_row_ancestor {transcript : Transcript n} {record : Record n}
    {vertices : Set (State n)} {column : Word n} {mode : Finset (Word n)} {offset : Word n}
    (reused : ReuseToPattern transcript record vertices column mode offset) :
    (rowAncestorsTo (realRecordRelation transcript) vertices record.output.2
      (inputPattern transcript record vertices column mode offset)).Nonempty := by
  obtain ⟨_, target, inPattern, walk, multiple⟩ := reused
  obtain ⟨x, y, step, after, before⟩ := last_new_segments walk (by omega)
  have earlier : ∃ a b, residualNewEdge record vertices a b ∧
      Reaches (oldRelation (residualRecordEdge transcript vertices)) b x := by
    rcases before with ⟨one, _⟩ | ⟨_, existsOld⟩
    · omega
    · exact existsOld
  obtain ⟨a, b, edge, path⟩ := earlier
  have output := congrArg (fun s : State n ↦ s.2) (show record.edge a.val b.val from edge).2
  -- The old suffix from the last new output makes its input eligible for this pattern.
  have inputMem : x.val ∈ inputPattern transcript record vertices column mode offset := by
    change x ∈ Subtype.val ⁻¹' inputPattern transcript record vertices column mode offset
    rw [← input_pattern_identification transcript record vertices column mode offset]
    exact ⟨y, step, target, inPattern, after⟩
  exact ⟨b.val, output, x.val, inputMem, reachesWithin_iff_residual.mpr path⟩

/-- For a fixed source row, bound the probability of old ancestry of the new inputs
by the product of the input and restricted outlet support sizes, divided by `2 ^ n`. -/
theorem ancestor_row_probability : DriftEventsSpec.AncestorRowProbability := by
  intro n transcript vertices inputColumn outputRow row column mode offset recordFor fixed
  let left := rightSupport (endpointPairs (realRecordRelation transcript) vertices row inputColumn)
  let right := patternOutletSupport transcript vertices outputRow column mode offset
  let allowed := xorOffsets left right
  have covered : {shift | (rowAncestorsTo (realRecordRelation transcript) vertices row
      (inputPattern transcript (recordFor shift) vertices column mode offset)).Nonempty} ⊆
      (allowed : Set (Word n)) := by
    intro shift nonempty
    obtain ⟨input_eq, output_eq, shift_eq⟩ := fixed shift
    simpa only [Finset.mem_coe, allowed, left, right, input_eq, output_eq, shift_eq] using
      (input_ancestor_shift (record := recordFor shift) nonempty)
  have cardBound : allowed.card ≤ left.card * right.card :=
    card_xorOffsets_le left right
  calc
    _ ≤ uniformShiftMass (allowed : Set (Word n)) := uniform_shift_mass_mono covered
    _ = (allowed.card : ℝ) / (2 : ℝ) ^ n := by
      rw [uniform_shift_mass_card, Set.ncard_coe_finset]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast cardBound) (by positivity)

/-- The reuse bound in the proof of Lemma 4, retaining the actual right support cardinal for the
return segment. -/
theorem reuse_probability : DriftEventsSpec.ReuseProbability := by
  intro n transcript vertices inputColumn outputRow column mode offset recordFor fixed
  refine (uniform_shift_mass_mono (second := {shift |
    (rowAncestorsTo (realRecordRelation transcript) vertices outputRow
      (inputPattern transcript (recordFor shift) vertices column mode offset)).Nonempty}) ?_).trans
    (ancestor_row_probability transcript vertices inputColumn outputRow outputRow column
      mode offset recordFor fixed)
  intro shift reused
  rw [← (fixed shift).2.1]
  exact reuse_implies_output_row_ancestor reused

/-- An empty restricted outlet support rules out eligible new inputs, so the pattern's
row-ancestor set stays the same after adding the record. -/
theorem empty_support_no_growth : DriftEventsSpec.EmptySupportNoGrowth := by
  intro n transcript record vertices row column mode offset empty
  have noInput : inputPattern transcript record vertices column mode offset = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro state ⟨_, _, inputRate⟩
    change state.2 ∈ xorTranslate record.shift
      (patternOutletSupport transcript vertices record.output.2 column mode offset) at inputRate
    simp [empty, xorTranslate] at inputRate
  have noReuse : ¬ ReuseToPattern transcript record vertices column mode offset := by
    intro reused
    obtain ⟨a, _, b, hb, _⟩ := reuse_implies_output_row_ancestor reused
    rw [noInput] at hb
    exact hb
  rw [pattern_two_groups transcript record vertices row column mode offset noReuse, noInput]
  ext source
  simp [rowAncestorsTo]

end JH.Graph
