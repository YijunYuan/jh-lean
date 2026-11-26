/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.ForwardEventsSpec
public import JH.Connectivity.ShiftTest
public import JH.Graph.Evolution.Round
public import JH.Potential.Drift.Events

/-!
# Forward inheritance and intersection witnesses

Follow a path from the old forward side, then trim it to isolate its crossings of the old
boundaries. The old boundaries are closed, so a crossing uses the current record. For
inheritance, the last use leaves an old residual suffix. For intersection, the exit from the
forward boundary either lands in the backward boundary or begins an old residual return to the
new input column.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ} {initials : Finset (State n)}

namespace BoundaryEvents

private theorem relation_append (transcript : Transcript n) (record : Record n)
    {a b : Vertex initials} :
    recordRelation (transcript ++ [record]) initials a b ↔
      recordRelation transcript initials a b ∨ vertexEdge record a b := by
  cases b with
  | inl target => exact realRecordRelation_append transcript record a.state target
  | inr _ => simp [recordRelation, Transcript.edge, vertexEdge]

private theorem real_outlet {record : Record n} {a b : Vertex initials}
    (step : vertexEdge record a b) : b = Sum.inl b.state := by
  cases b with
  | inl state => rfl
  | inr start => exact step.elim

private theorem vertex_step {record : Record n} {a b : Vertex initials}
    (step : vertexEdge record a b) : record.edge a.state b.state := by
  cases b with
  | inl state => exact step
  | inr start => exact step.elim

private theorem coordinates {record : Record n} {a b : State n} (step : record.edge a b) :
    a.1 = record.input.1 ∧ b.2 = record.output.2 ∧ a.2 ^^^ b.1 = record.shift := by
  obtain ⟨input, rfl⟩ := step
  exact ⟨input, rfl, xor_left_cancel _ _⟩

private theorem residual_real {before : Boundary (Vertex initials)}
    (hasStarts : before.ContainsVirtualStarts) {v : Vertex initials}
      (resident : v ∈ before.residual) :
    v = Sum.inl v.state := by
  cases v with
  | inl state => rfl
  | inr start => exact (resident (Or.inl (hasStarts start))).elim

private theorem residual_state {before : Boundary (Vertex initials)}
    (hasStarts : before.ContainsVirtualStarts) {v : Vertex initials}
      (resident : v ∈ before.residual) :
    v.state ∈ before.realResidual := by
  change Sum.inl v.state ∈ before.residual
  rw [← residual_real hasStarts resident]
  exact resident

private theorem residual_path_to_states {transcript : Transcript n}
    {before : Boundary (Vertex initials)} (hasStarts : before.ContainsVirtualStarts)
    {a b : Vertex initials}
    (path : ReachesWithin (recordRelation transcript initials) before.residual a b) :
    ReachesWithin (realRecordRelation transcript) before.realResidual a.state b.state := by
  refine ⟨residual_state hasStarts path.1, residual_state hasStarts path.2.1,
    path.2.2.lift Vertex.state ?_⟩
  rintro x y ⟨hx, hy, label, step⟩
  refine ⟨residual_state hasStarts hx, residual_state hasStarts hy, label, ?_⟩
  cases y with
  | inl state => exact step
  | inr start => exact step.elim

private theorem residual_walk (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) {a b : vertices}
    (path : ReachesWithin (realRecordRelation (transcript ++ [record])) vertices a.val b.val) :
    Nonempty (AddedWalk (residualRecordEdge transcript vertices)
      (residualNewEdge record vertices) a b) := by
  apply (added_walk_iff_reaches _ _ _ _).mpr
  refine Relation.ReflTransGen.mono ?_ a b ((reachesWithin_iff_residual (a := a) (b := b)).mp path)
  intro x y step
  exact (relation_append transcript record (initials := ∅) (a := .inl x.val) (b :=
    .inl y.val)).mp step

private theorem endpoint_pair {transcript : Transcript n} {vertices : Set (State n)}
    {a b : State n} {row column : Word n}
      (path : ReachesWithin (realRecordRelation transcript) vertices a b)
    (onRow : a.2 = row) (onColumn : b.1 = column) :
    (a.1, b.2) ∈ endpointPairs (realRecordRelation transcript) vertices row column := by
  have present : (a.1, b.2) ∈ endpointPairs (realRecordRelation transcript) vertices a.2 b.1 :=
    mem_endpointPairs.mpr path
  simpa only [onRow, onColumn] using present

private theorem leaves_forward {A : Type*} {edge : A → A → Prop} {before : Boundary A}
    {source target : A} (path : ReachesWithin edge before.backwardᶜ source target)
    (start : source ∈ before.forward) (outside : target ∉ before.forward) :
    ∃ x ∈ before.forward, ∃ y, edge x y ∧ ReachesWithin edge before.residual y target := by
  obtain ⟨sourceOutside, targetOutside, reached⟩ := path
  clear sourceOutside targetOutside
  induction reached with
  | refl => exact (outside start).elim
  | @tail middle target _ step ih =>
    have residual : target ∈ before.residual := by
      rintro (inForward | inBackward)
      · exact outside inForward
      · exact step.2.1 inBackward
    by_cases stillForward : middle ∈ before.forward
    · exact ⟨middle, stillForward, target, step.2.2, residual, residual, .refl⟩
    · obtain ⟨x, inForward, y, first, suffix⟩ := ih stillForward
      exact ⟨x, inForward, y, first, suffix.1, residual,
        suffix.2.2.tail ⟨suffix.2.1, residual, step.2.2⟩⟩

private theorem stays_outside_backward {A : Type*} {edge : A → A → Prop} {before : Boundary A}
    (separate : ¬ (before.inherit edge).Intersects) {a b : A} (started : a ∈ before.forward)
    (path : Reaches edge a b) : ReachesWithin edge before.backwardᶜ a b := by
  have outside {v : A} (reached : Reaches edge a v) : v ∈ before.backwardᶜ := by
    intro inBackward
    exact separate ⟨v, ⟨a, started, reached⟩, ⟨v, inBackward, .refl⟩⟩
  refine ⟨outside .refl, outside path, ?_⟩
  induction path with
  | refl => exact .refl
  | tail earlier step ih => exact ih.tail ⟨outside earlier, outside (earlier.tail step), step⟩

private theorem enters_backward {A : Type*} {edge : A → A → Prop} {backward : Set A}
    {source target : A} (path : Reaches edge source target) (outside : source ∉ backward)
    (inside : target ∈ backward) :
    ∃ x y, y ∈ backward ∧ ReachesWithin edge backwardᶜ source x ∧ edge x y := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact (outside inside).elim
  | @head first next step _ ih =>
    by_cases member : next ∈ backward
    · exact ⟨first, next, member, ⟨outside, outside, .refl⟩, step⟩
    · obtain ⟨x, y, hy, prefixPath, last⟩ := ih member
      exact ⟨x, y, hy, ⟨outside, prefixPath.2.1,
        prefixPath.2.2.head ⟨outside, member, step⟩⟩, last⟩

private theorem first_new_prefix {A Label : Type*} {oldEdge : Label → A → A → Prop}
    {newEdge : A → A → Prop} {source target : A} (walk : AddedWalk oldEdge newEdge source target)
    (positive : 0 < walk.newUses) :
    ∃ a b, newEdge a b ∧ Reaches (oldRelation oldEdge) source a := by
  induction walk with
  | nil => simp at positive
  | cons label step rest ih =>
    cases label with
    | old label =>
      obtain ⟨a, b, current, before⟩ := ih (by simpa only [AddedWalk.newUses_old] using positive)
      exact ⟨a, b, current, before.head ⟨label, step⟩⟩
    | new => exact ⟨_, _, step, .refl⟩

/-- When inheritance stays disjoint, take the last exit from the old forward side.
The new edge is followed by a walk inside the old residual graph. -/
theorem forward_trim : BoundaryEventsSpec.ForwardTrim := by
  intro n initials transcript record threshold before finish column rate closed continued inherited
  obtain ⟨⟨a, started, path⟩, outside⟩ := inherited
  obtain ⟨x, hx, y, step, suffix⟩ := leaves_forward
    (stays_outside_backward continued.1 started path) started outside
  exact ⟨x, hx, y, ((relation_append transcript record).mp step).resolve_left
    (fun oldStep ↦ suffix.1 (Or.inl (closed.1 hx oldStep))), suffix⟩

/-- A newly inherited rate has a witness ending with an old path from the new output
row. The final new input comes from the old forward boundary or a residual return. -/
theorem forward_inheritance_witness : BoundaryEventsSpec.ForwardInheritanceWitness := by
  intro n initials transcript record threshold before finish column rate
    hasStarts closed continued inherited
  obtain ⟨start, inForward, outlet, first, suffix⟩ :=
    forward_trim transcript record threshold before finish column rate closed continued inherited
  obtain ⟨firstColumn, firstRow, firstShift⟩ := coordinates (vertex_step first)
  have realSuffix := residual_path_to_states hasStarts suffix
  let outPoint : before.realResidual := ⟨outlet.state, realSuffix.1⟩
  let target : before.realResidual := ⟨(column, rate), realSuffix.2.1⟩
  obtain ⟨walk⟩ := residual_walk transcript record before.realResidual (a :=
    outPoint) (b := target) realSuffix
  -- Use the exiting edge if it is the last new use. Otherwise two successive new
  -- uses expose an old path from the new output row back to the new input column.
  by_cases noFurther : walk.newUses = 0
  · exact ⟨start.state.2, outlet.state.1, Or.inl ⟨start, inForward, firstColumn, rfl⟩,
      endpoint_pair (reachesWithin_iff_residual.mpr (walk.old_reaches noFurther)) firstRow rfl,
      firstShift⟩
  · obtain ⟨input, output, last, after, preceding⟩ :=
      last_new_segments walk (Nat.pos_of_ne_zero noFurther)
    have lastEdge : record.edge input.val output.val := last
    obtain ⟨inputColumn, outputRow, lastShift⟩ := coordinates lastEdge
    have returned : ∃ previous : before.realResidual, previous.val.2 = record.output.2 ∧
        Reaches (oldRelation (residualRecordEdge transcript before.realResidual))
          previous input := by
      rcases preceding with ⟨_, single⟩ | ⟨_, earlier, previous, step, between⟩
      · exact ⟨outPoint, firstRow, single⟩
      · have previousEdge : record.edge earlier.val previous.val := step
        exact ⟨previous, (coordinates previousEdge).2.1, between⟩
    obtain ⟨previous, previousRow, oldReturn⟩ := returned
    have inSupport : input.val.2 ∈ rightSupport (endpointPairs (realRecordRelation transcript)
        before.realResidual record.output.2 record.input.1) :=
      Finset.mem_image.mpr ⟨(previous.val.1, input.val.2),
        endpoint_pair (reachesWithin_iff_residual.mpr oldReturn) previousRow inputColumn, rfl⟩
    exact ⟨input.val.2, output.val.1, Or.inr inSupport,
      endpoint_pair (reachesWithin_iff_residual.mpr after) outputRow rfl, lastShift⟩

/-- Witness intersection by an exit from the old forward side using the new record.
Its outlet lies on the old backward side or can reach a new input by old edges. -/
theorem forward_intersection_witness : BoundaryEventsSpec.ForwardIntersectionWitness := by
  intro n initials transcript record threshold before hasStarts closed oldSeparate stopped
  let updated := recordRelation (transcript ++ [record]) initials
  have intersects : (before.inherit updated).Intersects := stopped
  obtain ⟨a, ha, b, hb, path⟩ := (Boundary.inheritance updated before).2.2.mp intersects
  obtain ⟨entry, inside, inBackward, beforeEntry, finalStep⟩ :=
    enters_backward path (fun haBack ↦ oldSeparate ⟨a, ha, haBack⟩) hb
  have finalNew : vertexEdge record entry inside := ((relation_append transcript record).mp
      finalStep).resolve_left
    (fun oldStep ↦ beforeEntry.2.1 (closed.2 inBackward oldStep))
  by_cases entryInForward : entry ∈ before.forward
  · obtain ⟨column, row, shift⟩ := coordinates (vertex_step finalNew)
    have cap : inside.state.1 ∈ backwardCaps before record.output.2 := by
      change Sum.inl (inside.state.1, record.output.2) ∈ before.backward
      rw [← row, show (inside.state.1, inside.state.2) = inside.state from rfl,
        ← real_outlet finalNew]
      exact inBackward
    exact ⟨entry.state.2, inside.state.1, ⟨entry, entryInForward, column, rfl⟩, Or.inl cap, shift⟩
  · obtain ⟨start, startForward, outlet, firstStep, suffix⟩ :=
      leaves_forward beforeEntry ha entryInForward
    have firstNew : vertexEdge record start outlet :=
      ((relation_append transcript record).mp firstStep).resolve_left
        (fun oldStep ↦ suffix.1 (Or.inl (closed.1 startForward oldStep)))
    obtain ⟨inputColumn, outputRow, shift⟩ := coordinates (vertex_step firstNew)
    have realSuffix := residual_path_to_states hasStarts suffix
    let origin : before.realResidual := ⟨outlet.state, realSuffix.1⟩
    let nextInput : before.realResidual := ⟨entry.state, realSuffix.2.1⟩
    obtain ⟨walk⟩ := residual_walk transcript record before.realResidual
      (a := origin) (b := nextInput) realSuffix
    -- Cut at the first new use after leaving the forward boundary, or at the final
    -- entry edge if the intervening residual walk uses only old labels.
    have returned : ∃ x : before.realResidual, x.val.1 = record.input.1 ∧
        Reaches (oldRelation (residualRecordEdge transcript before.realResidual)) origin x := by
      by_cases noNew : walk.newUses = 0
      · exact ⟨nextInput, (vertex_step finalNew).1, walk.old_reaches noNew⟩
      · obtain ⟨x, y, step, reached⟩ := first_new_prefix walk (Nat.pos_of_ne_zero noNew)
        have newEdge : record.edge x.val y.val := step
        exact ⟨x, newEdge.1, reached⟩
    obtain ⟨x, returningColumn, oldReturn⟩ := returned
    have oldReach :
        ReachesWithin (realRecordRelation transcript) before.realResidual outlet.state x.val :=
      (reachesWithin_iff_residual (a := origin) (b := x)).mpr oldReturn
    have cap : outlet.state.1 ∈ leftSupport (endpointPairs (realRecordRelation transcript)
        before.realResidual record.output.2 record.input.1) :=
      Finset.mem_image.mpr ⟨(outlet.state.1, x.val.2),
        endpoint_pair oldReach outputRow returningColumn, rfl⟩
    exact ⟨start.state.2, outlet.state.1,
      ⟨start, startForward, inputColumn, rfl⟩, Or.inr cap, shift⟩

/-- An inherited column has at most as many new rates as the old right support. -/
theorem forward_inherited_count : BoundaryEventsSpec.ForwardInheritedCount := by
  intro n initials transcript record threshold before finish column hasStarts closed continued
  let right := rightSupport (endpointPairs (realRecordRelation transcript) before.realResidual
    record.output.2 column)
  have subset : forwardInheritedRates transcript record before column ⊆ (right : Set (Word n)) := by
    intro rate inherited
    obtain ⟨_, outputCapacity, _, pair, _⟩ :=
      forward_inheritance_witness transcript record threshold before finish column rate
        hasStarts closed continued inherited
    exact Finset.mem_image.mpr ⟨(outputCapacity, rate), pair, rfl⟩
  change _ ≤ right.card
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_mono subset

/-- At fixed exposed coordinates the shift probability for forward inheritance in a column of a
disjoint round is at most $B_{\mathrm{ver}}(C+B_{\mathrm{ver}})/N$ with common threshold `C`. -/
theorem forward_inheritance_probability : BoundaryEventsSpec.ForwardInheritanceProbability := by
  intro n initials transcript threshold before inputColumn outputRow column Psi Pi recordFor
    hasStarts closed coordinatesFixed occupied returnBound outletBound
  let pairs := endpointPairs (realRecordRelation transcript) before.realResidual
  let forward := (Set.toFinite (forwardRates before inputColumn)).toFinset
  let inputs := forward ∪ rightSupport (pairs outputRow inputColumn)
  let outlets := leftSupport (pairs outputRow column)
  let event : Set (Word n) := {shift | ∃ finish,
    RoundStep transcript (recordFor shift) threshold before (.continued finish) ∧
      (forwardInheritedRates transcript (recordFor shift) before column).Nonempty}
  have subset : event ⊆ (xorOffsets inputs outlets : Set (Word n)) := by
    rintro shift ⟨finish, continued, rate, inherited⟩
    obtain ⟨input, output, atInput, endpoint, shiftEq⟩ :=
      forward_inheritance_witness transcript (recordFor shift) threshold before finish column rate
        hasStarts closed continued inherited
    obtain ⟨columnEq, rowEq, fixedShift⟩ := coordinatesFixed shift
    rw [columnEq, rowEq] at atInput
    rw [rowEq] at endpoint
    have inputMem : input ∈ inputs := by
      rcases atInput with occupiedRate | returned
      · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr occupiedRate)
      · exact Finset.mem_union_right _ returned
    have outputMem : output ∈ outlets := Finset.mem_image.mpr ⟨(output, rate), endpoint, rfl⟩
    exact mem_xorOffsets inputMem outputMem (shiftEq.trans fixedShift)
  have forwardBound : forward.card ≤ Psi := by
    dsimp only [forward]
    rw [← Set.ncard_eq_toFinset_card]
    exact occupied
  have inputBound : inputs.card ≤ Psi + Pi :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add forwardBound returnBound)
  have candidateBound : (xorOffsets inputs outlets).card ≤ Pi * (Psi + Pi) :=
    (card_xorOffsets_le inputs outlets).trans
      ((Nat.mul_le_mul inputBound outletBound).trans_eq (Nat.mul_comm _ _))
  simpa only [Nat.cast_mul, Nat.cast_add] using uniform_shift_mass_le subset candidateBound

/-- At fixed exposed coordinates, bound intersection by the old forward occupancy
limit times the number of candidate capacities, divided by `2 ^ n`. -/
theorem forward_intersection_probability : BoundaryEventsSpec.ForwardIntersectionProbability := by
  intro n initials transcript threshold before inputColumn outputRow Psi recordFor
    hasStarts closed disjoint coordinatesFixed occupied
  let pairs := endpointPairs (realRecordRelation transcript)
      before.realResidual outputRow inputColumn
  let rates := (Set.toFinite (forwardRates before inputColumn)).toFinset
  let backward := (Set.toFinite (backwardCaps before outputRow)).toFinset
  let caps := backward ∪ leftSupport pairs
  let event : Set (Word n) :=
    {shift | RoundStep transcript (recordFor shift) threshold before .intersected}
  have subset : event ⊆ (xorOffsets rates caps : Set (Word n)) := by
    intro shift stopped
    obtain ⟨rate, cap, atRate, atCap, shiftEq⟩ :=
      forward_intersection_witness transcript (recordFor shift) threshold before
        hasStarts closed disjoint stopped
    obtain ⟨columnEq, rowEq, fixedShift⟩ := coordinatesFixed shift
    rw [columnEq] at atRate
    rw [columnEq, rowEq] at atCap
    have rateMem : rate ∈ rates := (Set.Finite.mem_toFinset _).mpr atRate
    have capMem : cap ∈ caps := by
      rcases atCap with wasBackward | residual
      · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr wasBackward)
      · exact Finset.mem_union_right _ residual
    exact mem_xorOffsets rateMem capMem (shiftEq.trans fixedShift)
  have rateBound : rates.card ≤ Psi := by
    dsimp only [rates]
    rw [← Set.ncard_eq_toFinset_card]
    exact occupied
  have capBound : caps.card ≤ (backwardCaps before outputRow).ncard + (leftSupport pairs).card := by
    have count := Finset.card_union_le backward (leftSupport pairs)
    simpa only [backward, ← Set.ncard_eq_toFinset_card] using count
  simpa only [Nat.cast_mul] using uniform_shift_mass_le subset
    ((card_xorOffsets_le rates caps).trans (Nat.mul_le_mul rateBound capBound))

end BoundaryEvents

end JH.Graph
