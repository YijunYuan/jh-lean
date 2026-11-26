/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.FlowTailBounds
public import JH.Connectivity.FlowWitness

/-!
# From a path-count stop to a flow witness

Lemma 3 extracts a decreasing sequence of record labels from the disjoint paths. Each boundary
of a test is either the original boundary or a coordinate of a record already chosen in this
reverse order. To certify the tests, each path is transported to the larger residual graph
immediately before its record was sampled.
-/

@[expose] public section

namespace JH.Graph.FlowTail

open Parameters Probability
open scoped ENNReal

variable {n q h : ℕ}

private theorem prefix_tapes_eq (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (i : Fin q) (k : ℕ) (within : k ≤ i.val) :
    initial.runPrefix (TapeTests.prefixAt intrinsic i) (TapeTests.prefixAt offsets i) k within =
      initial.runPrefix intrinsic offsets k (within.trans (Nat.le_of_lt i.isLt)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have lt : k < q := Nat.lt_trans (Nat.lt_of_succ_le within) i.isLt
    let index : Fin q := ⟨k, lt⟩
    change (initial.runPrefix (TapeTests.prefixAt intrinsic i) (TapeTests.prefixAt offsets i)
        k (by omega)).step (intrinsic index) (offsets index) =
      (initial.runPrefix intrinsic offsets k (by omega)).step (intrinsic index) (offsets index)
    rw [ih (by omega)]

/-- Recover the actual query, reply, and preceding records from a transcript label. -/
private theorem label_round (program : TrialProgram n) (intrinsic offsets : CoordinateTape n q)
    {records : Transcript n}
    (recordPrefix : records <+:
      ((⟨program, []⟩ : TapeState n).runPrefix intrinsic offsets q le_rfl).records)
    (label : records.Label) (i : Fin q) (index : i.val = label.val) :
    let before := beforeRound program intrinsic i (TapeTests.prefixAt offsets i)
    ∃ (request : Query n) (resume : State n → TrialProgram n),
      before.frontier = .query request resume ∧
      records.get label =
        request.recordOfReply (request.replyCoords.symm (intrinsic i, offsets i)) ∧
      before.records = records.take label.val := by
  let initial : TapeState n := ⟨program, []⟩
  let final := initial.runPrefix intrinsic offsets q le_rfl
  let finalLabel : Transcript.Label final.records :=
    ⟨label.val, label.isLt.trans_le recordPrefix.length_le⟩
  obtain ⟨actual, request, resume, earlier, time, reached, same⟩ :=
    initial.recorded_round intrinsic offsets q le_rfl finalLabel (Nat.zero_le _)
  have timeEq : actual.val = i.val := by
    simpa only [initial, finalLabel, List.length_nil, Nat.zero_add, index] using time
  have actualEq : actual = i := Fin.ext timeEq
  subst actual
  have earlierTape : beforeRound program intrinsic i (TapeTests.prefixAt offsets i) =
      initial.runPrefix intrinsic offsets i.val (Nat.le_of_lt i.isLt) :=
    prefix_tapes_eq initial intrinsic offsets i i.val le_rfl
  dsimp only
  rw [earlierTape]
  refine ⟨request, resume, reached, ?_, ?_⟩
  · exact (recordPrefix.getElem label.isLt).trans same
  · have pre := initial.records_prefix intrinsic offsets i.val q (Nat.le_of_lt i.isLt) le_rfl
    have size := initial.records_length_of_live intrinsic offsets i.val
        (Nat.le_of_lt i.isLt) reached
    have len : (initial.runPrefix intrinsic offsets i.val
        (Nat.le_of_lt i.isLt)).records.length = label.val := by
      simpa only [initial, List.length_nil, Nat.zero_add, index] using size
    have uptake := List.prefix_iff_eq_take.mp pre
    rw [len] at uptake
    change _ = records.take label.val
    rw [uptake]
    obtain ⟨rest, appendRest⟩ := recordPrefix
    rw [← appendRest, List.take_append_of_le_length label.isLt.le]

/-- The first flow stop retains its decisive record and has an active prefix before each label. -/
private theorem stop_snapshot {params : Params} (psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (records : Transcript params.n) (snapshot :
      GraphSnapshot initials)
    (stopped : GraphTracker.replay params psi initials targets records =
      .stopped .overConnected snapshot) :
    ¬ snapshot.PathsBounded params.pi ∧ snapshot.records <+: records ∧
      ∀ label : Transcript.Label snapshot.records, ∃ older : GraphSnapshot initials,
        GraphTracker.replay params psi initials targets
          (snapshot.records.take label.val) = .active older ∧
          snapshot.sides.realResidual ⊆ older.sides.realResidual := by
  obtain ⟨earlier, decisive, later, before, split, active, transition⟩ :=
    graph_earliest_record params psi initials targets records .overConnected snapshot stopped
  obtain ⟨written, overflow⟩ := GraphTracker.advance_over_connected transition
  have oldRecords := (graph_active_replay params psi initials targets earlier before active).1
  rw [oldRecords] at written
  have atStop : GraphTracker.replay params psi initials targets snapshot.records =
      .stopped .overConnected snapshot := by
    rw [written, GraphTracker.replay_append, active]
    exact transition
  refine ⟨overflow, ⟨later, by rw [written, split]⟩, ?_⟩
  intro label
  let prior := snapshot.records.take label.val
  have size : label.val ≤ earlier.length := by
    have lt := label.isLt
    change label.val < snapshot.records.length at lt
    have len := congrArg List.length written
    rw [List.length_append, List.length_singleton] at len
    omega
  have prior_eq : prior = earlier.take label.val := by
    simp only [prior, written, List.take_append_of_le_length size]
  change ∃ older : GraphSnapshot initials,
    GraphTracker.replay params psi initials targets prior = .active older ∧ _
  cases reached : GraphTracker.replay params psi initials targets prior with
  | active older =>
    -- Residual vertices only disappear, so the stop's residual set lies in each old set.
    have smaller := graph_residual_monotone params psi initials targets prior
      (snapshot.records.drop label.val)
    have concat : prior ++ snapshot.records.drop label.val = snapshot.records :=
        List.take_append_drop _ _
    rw [concat, atStop, reached] at smaller
    exact ⟨older, rfl, smaller⟩
  | stopped reason older =>
    have absorb := GraphTracker.replay_stopped_append psi targets prior (earlier.drop label.val)
      reason older reached
    rw [prior_eq, List.take_append_drop, active] at absorb
    contradiction

private theorem valid_tests_at {transcript : Transcript n} {vertices : Set (State n)}
    {row column : Word n} (tests : List (FlowTest transcript vertices))
    (j : Fin tests.length) (previous : List transcript.Label)
    (valid : ValidFlowTests row column previous tests) :
    (tests.get j).Valid row column (previous ++ (tests.take j.val).map FlowTest.label) := by
  induction tests generalizing previous with
  | nil => exact Fin.elim0 j
  | cons test rest ih =>
    refine Fin.cases ?_ (fun rank ↦ ?_) j
    · simpa only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero,
        List.take_zero, List.map_nil, List.append_nil] using valid.1
    · have chosen := ih rank (previous ++ [test.label]) valid.2
      simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ, List.take_succ_cons,
        List.map_cons, List.append_assoc, List.singleton_append] using chosen

/-- Keep the first `h` tests of the decreasing witness sequence. -/
private def selectedTest {transcript : Transcript n} {vertices : Set (State n)}
    {tests : List (FlowTest transcript vertices)} (enough : h ≤ tests.length) (rank : Fin h) :
    FlowTest transcript vertices := tests.get ⟨rank.val, rank.isLt.trans_le enough⟩

private theorem earlier_label {transcript : Transcript n} {vertices : Set (State n)}
    {tests : List (FlowTest transcript vertices)} (enough : h ≤ tests.length) (rank : Fin h)
    (label : transcript.Label) (seen : label ∈ (tests.take rank.val).map FlowTest.label) :
    ∃ previous : Fin h, previous < rank ∧ (selectedTest enough previous).label = label := by
  obtain ⟨test, member, labelEq⟩ := List.mem_map.mp seen
  obtain ⟨j, hj, testEq⟩ := List.mem_iff_getElem.mp member
  have ltRank := hj.trans_le (List.length_take_le _ _)
  refine ⟨⟨j, ltRank.trans rank.isLt⟩, ltRank, ?_⟩
  have sameTest : selectedTest enough ⟨j, ltRank.trans rank.isLt⟩ = test := by
    simpa only [selectedTest, List.get_eq_getElem, List.getElem_take] using testEq
  exact (congrArg FlowTest.label sameTest).trans labelEq

/-- Use code zero for the original boundary, and one plus a preceding rank otherwise. -/
private theorem encode_origin {transcript : Transcript n} {vertices : Set (State n)}
    {tests : List (FlowTest transcript vertices)} (enough : h ≤ tests.length)
    (selected : Selected q h) (recordRound : transcript.Label → Fin q)
    (indexes : ∀ rank, roundAt selected rank = recordRound (selectedTest enough rank).label)
    (intrinsic : CoordinateTape n q) (rank : Fin h) (original : Word n)
    (source : Option transcript.Label)
    (seen : ∀ label, source = some label → label ∈ (tests.take rank.val).map FlowTest.label) :
    ∃ origin : Fin (rank.val + 1), boundaryValue selected intrinsic original rank origin =
      source.elim original (fun label ↦ intrinsic (recordRound label)) := by
  cases source with
  | none => exact ⟨0, rfl⟩
  | some label =>
    obtain ⟨previous, earlier, labelEq⟩ := earlier_label enough rank label (seen label rfl)
    let code : Fin (rank.val + 1) := ⟨previous.val + 1, Nat.succ_lt_succ earlier⟩
    refine ⟨code, ?_⟩
    unfold boundaryValue
    rw [ite_eq_right (by simp [code])]
    change intrinsic (roundAt selected previous) = intrinsic (recordRound label)
    rw [indexes, labelEq]

/-- Every first path-count stop satisfies all tests of some Lemma 3 encoding. -/
theorem witness_covered : FlowTailSpec.WitnessCovered := by
  classical
  intro params q psi initials targets program tapes stop
  let initial : TapeState params.n := ⟨program, []⟩
  let final := initial.runPrefix tapes.1 tapes.2 q le_rfl
  let tracker := GraphTracker.replay params psi initials targets final.records
  have reason : tracker.stopReason = some .overConnected := stop
  obtain ⟨snapshot, stopped⟩ : ∃ snapshot, tracker = .stopped .overConnected snapshot := by
    cases reached : tracker with
    | active snapshot =>
      simp only [reached, GraphTracker.stopReason] at reason
      contradiction
    | stopped label snapshot =>
      have same : label = .overConnected := Option.some.inj
        (by simpa only [reached, GraphTracker.stopReason] using reason)
      subst label
      exact ⟨snapshot, rfl⟩
  obtain ⟨overflow, recorded, history⟩ :=
    stop_snapshot psi initials targets final.records snapshot stopped
  unfold GraphSnapshot.PathsBounded PathsWithinThreshold at overflow
  obtain ⟨row, fails⟩ := not_forall.mp overflow
  obtain ⟨column, fails⟩ := not_forall.mp fails
  obtain ⟨witness⟩ := extract_flow_witness snapshot.records snapshot.sides.realResidual row column
    (params.pi + 1) (Classical.not_not.mp fails)
  have enough := flow_witness_record_count params snapshot.records
      snapshot.sides.realResidual row column witness
  have finalBound : final.records.length ≤ q := by
    simpa only [initial, List.length_nil, Nat.zero_add] using
      initial.records_length_le_round tapes.1 tapes.2 q le_rfl
  let indexOf (label : Transcript.Label snapshot.records) : Fin q :=
    ⟨label.val, label.isLt.trans_le (recorded.length_le.trans finalBound)⟩
  let pick (rank : Fin params.h) := selectedTest enough rank
  -- The first `h` witness labels are distinct and already ordered for the encoding.
  have sorted : StrictAnti (fun rank ↦ indexOf (pick rank).label) := by
    intro first later ordered
    exact witness.decreasing.rel_get_of_lt ordered
  obtain ⟨selected, enumerate⟩ := roundAt_of_strictAnti sorted
  have indexes (rank : Fin params.h) : roundAt selected rank = indexOf (pick rank).label :=
    congrFun enumerate rank
  have valid (rank : Fin params.h) :
      (pick rank).Valid row column ((witness.tests.take rank.val).map FlowTest.label) := by
    simpa only [pick, selectedTest, List.nil_append] using
      valid_tests_at witness.tests ⟨rank.val, rank.isLt.trans_le enough⟩ [] witness.valid
  have intrinsic_eq (label : Transcript.Label snapshot.records) :
      tapes.1 (indexOf label) = (snapshot.records.get label).intrinsicCoordinate := by
    obtain ⟨request, _, _, recordEq, _⟩ :=
      label_round program tapes.1 tapes.2 recorded label (indexOf label) rfl
    rw [recordEq]
    have equality := (request.recordOfReply_coords _).trans
      (request.replyCoords.apply_symm_apply (tapes.1 (indexOf label), tapes.2 (indexOf label)))
    exact (congrArg Prod.fst equality).symm
  -- An earlier choice in reverse order supplies an intrinsic coordinate even when its
  -- round is later in time. The test treats the intrinsic tape as fixed.
  have choices (rank : Fin params.h) : ∃ pair : Fin (rank.val + 1) × Fin (rank.val + 1),
      boundaryValue selected tapes.1 row rank pair.1 =
        flowRow snapshot.records row (pick rank).path.rowFrom ∧
      boundaryValue selected tapes.1 column rank pair.2 =
        flowColumn snapshot.records column (pick rank).path.columnFrom := by
    let boundaries := (valid rank).boundaries
    obtain ⟨rowOrigin, rowEq⟩ := encode_origin enough selected indexOf indexes tapes.1 rank row
      (pick rank).path.rowFrom (fun label same ↦ (boundaries.row_from label same).1)
    obtain ⟨columnOrigin, columnEq⟩ :=
      encode_origin enough selected indexOf indexes tapes.1 rank column
      (pick rank).path.columnFrom (fun label same ↦ (boundaries.column_from label same).1)
    refine ⟨(rowOrigin, columnOrigin), ?_, ?_⟩
    · rw [rowEq]
      cases origin : (pick rank).path.rowFrom with
      | none => rfl
      | some label =>
        have direction := (boundaries.row_from label origin).2
        change tapes.1 (indexOf label) = (snapshot.records.get label).output.2
        rw [intrinsic_eq, Record.intrinsicCoordinate, direction]
    · rw [columnEq]
      cases origin : (pick rank).path.columnFrom with
      | none => rfl
      | some label =>
        have direction := (boundaries.column_from label origin).2
        change tapes.1 (indexOf label) = (snapshot.records.get label).input.1
        rw [intrinsic_eq, Record.intrinsicCoordinate, direction]
  choose origins originEq using choices
  let code : Code params.n q params.h := ((row, column), selected, origins)
  refine Set.mem_iUnion.mpr ⟨code, ?_⟩
  intro i present
  obtain ⟨rank, rfl⟩ := exists_roundAt selected present
  let i := roundAt selected rank
  have matchIndex : i.val = (pick rank).label.val := congrArg Fin.val (indexes rank)
  obtain ⟨request, resume, reached, recordEq, prefixEq⟩ :=
    label_round program tapes.1 tapes.2 recorded (pick rank).label i matchIndex
  obtain ⟨older, active, contains⟩ := history (pick rank).label
  have olderRecords := (graph_active_replay params psi initials targets _ older active).1
  have sameActive : GraphTracker.replay params psi initials targets
      (beforeRound program tapes.1 i (TapeTests.prefixAt tapes.2 i)).records = .active older := by
    rw [prefixEq, active]
  -- Move the path to the selected round's old residual set using the prefix inclusion.
  have tested := flow_test_on_prefix snapshot.records snapshot.sides.realResidual
      older.sides.realResidual
    row column ((witness.tests.take rank.val).map FlowTest.label) (pick rank) contains (valid rank)
  change test psi initials targets program code tapes.1 i (TapeTests.prefixAt tapes.2 i) (tapes.2 i)
  simp only [test, reached, sameActive]
  refine ⟨rank, rfl, ?_⟩
  change HasNewPath older.records
    (request.recordOfReply (request.replyCoords.symm (tapes.1 i, tapes.2 i)))
    older.sides.realResidual (boundaryValue selected tapes.1 row rank (origins rank).1)
    (boundaryValue selected tapes.1 column rank (origins rank).2)
  rw [olderRecords, ← recordEq, (originEq rank).1, (originEq rank).2]
  exact tested

/-- Combine witness coverage with the encoded union and the query-budget bound. -/
theorem first_stop_bound : FlowTailSpec.FirstStopBound := by
  intro params q psi initials targets program cert occupancy
  let law := CoordinateTape.law params.n q
  let events := ⋃ code : Code params.n q params.h, codeEvent psi initials targets program code
  have subset := witness_covered params q psi initials targets program
  have valid := graph_initial_parameters params q psi initials targets cert occupancy
  refine (ENNReal.toReal_mono (mass_ne_top law events)
    (MeasureTheory.measure_mono (μ := law.toOuterMeasure) subset)).trans ?_
  exact (encoded_union params q psi initials targets program valid).trans
    (union_bound_le_flowTail params q cert.budget)

end JH.Graph.FlowTail
