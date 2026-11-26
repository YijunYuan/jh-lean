/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.Endpoints
public import JH.Connectivity.ShiftTestSpec
public import JH.Graph.AddedPath

/-!
# A necessary shift test for new paths

Fix a source row, a target column, the old residual graph, and the current record's input
column and output row. A path that uses the current label forces its shift to be the XOR of a
rate and a capacity from old endpoint supports. Counting those pairs gives the conditional
bound in Lemma 2 under a uniform shift.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

private theorem pair_of_old_reach {transcript : Transcript n} {vertices : Set (State n)}
    {a b : vertices} (path : Reaches (oldRelation (residualRecordEdge transcript vertices)) a b) :
    (a.val.1, b.val.2) ∈ endpointPairs (realRecordRelation transcript) vertices a.val.2 b.val.1 :=
  mem_endpointPairs.mpr (reachesWithin_iff_residual.mpr path)

theorem mem_xorOffsets {rates caps : Finset (Word n)} {rate cap shift : Word n}
    (inRates : rate ∈ rates) (inCaps : cap ∈ caps) (matchesShift : rate ^^^ cap = shift) :
    shift ∈ xorOffsets rates caps :=
  Finset.mem_image.mpr ⟨(rate, cap), Finset.mem_product.mpr ⟨inRates, inCaps⟩, matchesShift⟩

theorem card_xorOffsets_le (rates caps : Finset (Word n)) :
    (xorOffsets rates caps).card ≤ rates.card * caps.card :=
  Finset.card_image_le.trans_eq (Finset.card_product _ _)

/-- A path using the current record puts its shift in the candidate set formed from
old-path endpoint supports. -/
theorem necessary_shift : ShiftTestSpec.NecessaryShift := by
  intro n transcript record vertices row column witness
  obtain ⟨a, b, aRow, bColumn, path, used⟩ := witness
  obtain ⟨x, y, newStep, after, before⟩ := last_new_segments path used
  have step : record.edge x.val y.val := newStep
  have input_eq : x.val.1 = record.input.1 := step.1
  have output_eq := congrArg (fun state : State n ↦ state.2) step.2
  change y.val.2 = record.output.2 at output_eq
  have afterPair := pair_of_old_reach after
  rw [output_eq, bColumn] at afterPair
  have outSupport : y.val.1 ∈ leftSupport
      (endpointPairs (realRecordRelation transcript) vertices record.output.2 column) :=
    Finset.mem_image.mpr ⟨(y.val.1, b.val.2), afterPair, rfl⟩
  -- The final new edge starts after an old path from the original row, or after
  -- an old path from the current record's output row if the label was reused.
  have inSupport : x.val.2 ∈
      rightSupport (endpointPairs (realRecordRelation transcript) vertices row record.input.1) ∪
        rightSupport (endpointPairs (realRecordRelation transcript) vertices record.output.2
          record.input.1) := by
    rcases before with ⟨_, fromSource⟩ | ⟨_, _, previousOutput, previousStep, fromOutput⟩
    · have pair := pair_of_old_reach fromSource
      rw [aRow, input_eq] at pair
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a.val.1, x.val.2), pair, rfl⟩)
    · have previousOutputRow :=
        congrArg (fun state : State n ↦ state.2) (show record.edge _ _ from previousStep).2
      change previousOutput.val.2 = record.output.2 at previousOutputRow
      have pair := pair_of_old_reach fromOutput
      rw [previousOutputRow, input_eq] at pair
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(previousOutput.val.1, x.val.2), pair, rfl⟩)
  have capacity_eq : y.val.1 = x.val.2 ^^^ record.shift := congrArg Prod.fst step.2
  have shift_eq : x.val.2 ^^^ y.val.1 = record.shift := by
    rw [capacity_eq, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  exact Finset.mem_image.mpr
    ⟨(x.val.2, y.val.1), Finset.mem_product.mpr ⟨inSupport, outSupport⟩, shift_eq⟩

/-- The two possible input supports have total size at most twice the support bound.
Multiplying by the output-support bound gives at most $2B_{\mathrm{ver}}^2$ candidate shifts. -/
theorem shift_candidate_card : ShiftTestSpec.CandidateCard := by
  intro n transcript vertices Pi supportBound inputColumn outputRow row column
  let pairs := endpointPairs (realRecordRelation transcript) vertices
  let rates := rightSupport (pairs row inputColumn) ∪ rightSupport (pairs outputRow inputColumn)
  let capacities := leftSupport (pairs outputRow column)
  have rateCount : rates.card ≤ 2 * Pi := by
    calc
      _ ≤ (rightSupport (pairs row inputColumn)).card +
          (rightSupport (pairs outputRow inputColumn)).card := Finset.card_union_le _ _
      _ ≤ Pi + Pi := Nat.add_le_add (supportBound row inputColumn).2
        (supportBound outputRow inputColumn).2
      _ = _ := (two_mul Pi).symm
  calc
    _ ≤ rates.card * capacities.card := card_xorOffsets_le rates capacities
    _ ≤ (2 * Pi) * Pi := Nat.mul_le_mul rateCount (supportBound outputRow column).1
    _ = 2 * Pi ^ 2 := by rw [pow_two, Nat.mul_assoc]

/-- The probability in Lemma 2 once the remaining coordinate and old history are fixed and the
shift is uniform. -/
theorem uniform_candidate_probability : ShiftTestSpec.UniformCandidateProbability := by
  intro n Pi event candidates contains size
  classical
  let : Fintype event := Fintype.ofFinite event
  have count : Fintype.card event ≤ candidates.card := by
    simpa using Fintype.card_subtype_mono _ _ contains
  have countReal : (Fintype.card event : ℝ) ≤ 2 * (Pi : ℝ) ^ 2 := by
    exact_mod_cast count.trans size
  simp only [uniformShiftMass, toOuterMeasure_uniformPMF_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, word_card n, Nat.cast_pow, Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right countReal (by positivity)

/-- Lemma 2 bounds the probability of a new path by $2B_{\mathrm{ver}}^2/N$ when the
input column and output row are fixed and the fresh shift is uniform. -/
theorem uniform_new_path_probability : ShiftTestSpec.UniformNewPathProbability := by
  intro n transcript vertices Pi bounded inputColumn outputRow row column recordFor coordinates
  apply uniform_candidate_probability Pi _
    (shiftCandidates transcript vertices inputColumn outputRow row column) ?_
    (shift_candidate_card transcript vertices Pi bounded inputColumn outputRow row column)
  intro shift witness
  obtain ⟨input_eq, output_eq, shift_eq⟩ := coordinates shift
  simpa only [Finset.mem_coe, input_eq, output_eq, shift_eq] using
    necessary_shift transcript (recordFor shift) vertices row column witness

end JH.Graph
