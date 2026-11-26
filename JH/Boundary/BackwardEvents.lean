/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.BackwardEventsSpec
public import JH.Connectivity.ShiftTest
public import JH.Graph.Evolution.Round
public import JH.Potential.Drift.Events

/-!
# Backward inheritance and intersection witnesses

Trim a path to its entry into the old backward side. Old closure forces this edge to use the
current record. On the residual prefix, labelled walks can be reversed to reuse the
last-new-step decomposition. The resulting input and output supports give the backward bounds
for a uniform shift.
-/

@[expose] public section

namespace JH.Graph.BackwardBoundaryEvents

open BoundaryEvents (backwardCaps forwardRates vertexEdge)

variable {n : ℕ} {initials : Finset (State n)}

private theorem relation_append (transcript : Transcript n) (record : Record n)
    {a b : Vertex initials} :
    recordRelation (transcript ++ [record]) initials a b ↔
      recordRelation transcript initials a b ∨ vertexEdge record a b := by
  cases b with
  | inl target => exact realRecordRelation_append transcript record a.state target
  | inr _ => simp [recordRelation, Transcript.edge, vertexEdge]

private theorem coordinates {record : Record n} {a b : State n} (step : record.edge a b) :
    a.1 = record.input.1 ∧ b.2 = record.output.2 ∧ a.2 ^^^ b.1 = record.shift := by
  obtain ⟨input, rfl⟩ := step
  exact ⟨input, rfl, xor_left_cancel _ _⟩

private theorem vertex_coordinates {record : Record n} {a b : Vertex initials}
    (step : vertexEdge record a b) :
    a.state.1 = record.input.1 ∧ b.state.2 = record.output.2 ∧
      a.state.2 ^^^ b.state.1 = record.shift := by
  cases b with
  | inl state => exact coordinates (show record.edge a.state state from step)
  | inr start => exact step.elim

private theorem cap_in_backward {before : Boundary (Vertex initials)} {record : Record n}
    {a b : Vertex initials} (step : vertexEdge record a b) (backward : b ∈ before.backward) :
    b.state.1 ∈ backwardCaps before record.output.2 := by
  cases b with
  | inl state =>
    have row := (vertex_coordinates step).2.1
    change state.2 = record.output.2 at row
    change Sum.inl (state.1, record.output.2) ∈ before.backward
    rw [← row, show (state.1, state.2) = state from rfl]
    exact backward
  | inr start => exact step.elim

private theorem state_residual {before : Boundary (Vertex initials)}
    (hasStarts : before.ContainsVirtualStarts) {v : Vertex initials}
      (resident : v ∈ before.residual) :
    v.state ∈ before.realResidual := by
  cases v with
  | inl state => exact resident
  | inr start => exact (resident (Or.inl (hasStarts start))).elim

private theorem residual_path_to_states {transcript : Transcript n}
    {before : Boundary (Vertex initials)} (hasStarts : before.ContainsVirtualStarts)
    {a b : Vertex initials}
    (path : ReachesWithin (recordRelation transcript initials) before.residual a b) :
    ReachesWithin (realRecordRelation transcript) before.realResidual a.state b.state := by
  refine ⟨state_residual hasStarts path.1, state_residual hasStarts path.2.1,
    path.2.2.lift Vertex.state ?_⟩
  rintro x y ⟨hx, hy, label, step⟩
  refine ⟨state_residual hasStarts hx, state_residual hasStarts hy, label, ?_⟩
  cases y with
  | inl state => exact step
  | inr start => exact step.elim

/-- An old residual edge traversed in the reverse direction. -/
private abbrev reverseOld (transcript : Transcript n) (vertices : Set (State n))
    (label : transcript.Label) (a b : vertices) : Prop :=
  residualRecordEdge transcript vertices label b a

/-- An edge of the new record traversed backwards on residual vertices. -/
private abbrev reverseNew (record : Record n) (vertices : Set (State n)) (a b : vertices) : Prop :=
  residualNewEdge record vertices b a

private theorem reversed_walk (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) {a b : vertices}
    (path : ReachesWithin (realRecordRelation (transcript ++ [record])) vertices a.val b.val) :
    Nonempty (AddedWalk (reverseOld transcript vertices) (reverseNew record vertices) b a) := by
  have realPath :
      Reaches (residualRelation (realRecordRelation (transcript ++ [record])) vertices) a b :=
    reachesWithin_iff_residual.mp path
  apply (added_walk_iff_reaches _ _ _ _).mpr
  refine Relation.ReflTransGen.mono ?_ b a realPath.swap
  intro x y step
  exact (relation_append transcript record (initials := ∅) (a := .inl y.val) (b :=
    .inl x.val)).mp step

private theorem endpoint_of_old_reverse {transcript : Transcript n} {vertices : Set (State n)}
    {a b : vertices} {row column : Word n}
    (path : Reaches (oldRelation (reverseOld transcript vertices)) b a)
    (sourceRow : a.val.2 = row) (targetColumn : b.val.1 = column) :
    (a.val.1, b.val.2) ∈ endpointPairs (realRecordRelation transcript) vertices row column := by
  have reach : ReachesWithin (realRecordRelation transcript) vertices a.val b.val :=
    (reachesWithin_iff_residual (a := a) (b := b)).mpr path.swap
  have pair : (a.val.1, b.val.2) ∈
      endpointPairs (realRecordRelation transcript) vertices a.val.2 b.val.1 :=
    mem_endpointPairs.mpr reach
  simpa only [sourceRow, targetColumn] using pair

/-- Stop at the first old-backward vertex on a walk outside the old forward side. -/
private theorem enters_backward {A : Type*} {edge : A → A → Prop} {before : Boundary A}
    {source target : A} (path : ReachesWithin edge before.forwardᶜ source target)
    (outside : source ∉ before.backward) (inside : target ∈ before.backward) :
    ∃ y ∈ before.backward, ∃ x, edge x y ∧ ReachesWithin edge before.residual source x := by
  obtain ⟨sourceOutside, targetOutside, reached⟩ := path
  clear sourceOutside targetOutside
  induction reached using Relation.ReflTransGen.head_induction_on with
  | refl => exact (outside inside).elim
  | @head first next step _ ih =>
    have residual : first ∈ before.residual := by
      rintro (forward | backward)
      · exact step.1 forward
      · exact outside backward
    by_cases nextBackward : next ∈ before.backward
    · exact ⟨next, nextBackward, first, step.2.2, residual, residual, .refl⟩
    · obtain ⟨y, hy, x, last, beforeLast⟩ := ih nextBackward
      exact ⟨y, hy, x, last, residual, beforeLast.2.1,
        beforeLast.2.2.head ⟨residual, beforeLast.1, step.2.2⟩⟩

private theorem stays_outside_forward {A : Type*} {edge : A → A → Prop} {before : Boundary A}
    (separate : ¬ (before.inherit edge).Intersects) {a b : A} (endsBackward : b ∈ before.backward)
    (path : Reaches edge a b) : ReachesWithin edge before.forwardᶜ a b := by
  have outside {v : A} (reached : Reaches edge v b) : v ∈ before.forwardᶜ := by
    intro inForward
    exact separate ⟨v, ⟨v, inForward, .refl⟩, ⟨b, endsBackward, reached⟩⟩
  refine ⟨outside path, outside .refl, ?_⟩
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head step rest ih => exact ih.head ⟨outside (rest.head step), outside rest, step⟩

private theorem leaves_forward {A : Type*} {edge : A → A → Prop} {forward : Set A}
    {source target : A} (path : Reaches edge source target) (inForward : source ∈ forward)
    (outside : target ∉ forward) :
    ∃ x ∈ forward, ∃ y, edge x y ∧ ReachesWithin edge forwardᶜ y target := by
  induction path with
  | refl => exact (outside inForward).elim
  | @tail middle target _ step ih =>
    by_cases middleForward : middle ∈ forward
    · exact ⟨middle, middleForward, target, step, outside, outside, .refl⟩
    · obtain ⟨x, hx, y, first, rest⟩ := ih middleForward
      exact ⟨x, hx, y, first, rest.1, outside, rest.2.2.tail ⟨rest.2.1, outside, step⟩⟩

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

/-- For backward inheritance in a disjoint round, take the first entry into the old
backward side. A residual prefix leads to that new edge. -/
theorem backward_trim : BackwardBoundaryEventsSpec.BackwardTrim := by
  intro n initials transcript record threshold before finish row capacity closed continued inherited
  obtain ⟨⟨endVertex, inBackward, path⟩, outside⟩ := inherited
  obtain ⟨outlet, outletBackward, inlet, step, beforeLast⟩ :=
    enters_backward (stays_outside_forward continued.1 inBackward path) outside inBackward
  exact ⟨outlet, outletBackward, inlet, ((relation_append transcript record).mp step).resolve_left
    (fun oldStep ↦ beforeLast.2.1 (Or.inr (closed.2 outletBackward oldStep))), beforeLast⟩

/-- A newly inherited capacity has an old-path witness to the new input column.
The corresponding new outlet lies in the old backward side or an old return support. -/
theorem backward_inheritance_witness : BackwardBoundaryEventsSpec.BackwardInheritanceWitness := by
  intro n initials transcript record threshold before finish row capacity
    hasStarts closed continued inherited
  obtain ⟨outlet, inBackward, inlet, last, beforeLast⟩ :=
    backward_trim transcript record threshold before finish row capacity closed continued inherited
  obtain ⟨lastColumn, _, lastShift⟩ := vertex_coordinates last
  have prefixReal := residual_path_to_states hasStarts beforeLast
  let inheritedPoint : before.realResidual := ⟨(capacity, row), prefixReal.1⟩
  let finalInput : before.realResidual := ⟨inlet.state, prefixReal.2.1⟩
  obtain ⟨walk⟩ := reversed_walk transcript record before.realResidual
    (a := inheritedPoint) (b := finalInput) prefixReal
  -- Work backwards from the entry edge. A further new use gives an old segment
  -- between consecutive new uses in the original orientation.
  by_cases noEarlier : walk.newUses = 0
  · exact ⟨inlet.state.2, outlet.state.1,
      endpoint_of_old_reverse (walk.old_reaches noEarlier) rfl lastColumn,
      Or.inl (cap_in_backward last inBackward), lastShift⟩
  · obtain ⟨output, input, first, earlier, following⟩ :=
      last_new_segments walk (Nat.pos_of_ne_zero noEarlier)
    have firstEdge : record.edge input.val output.val := first
    obtain ⟨inputColumn, outputRow, firstShift⟩ := coordinates firstEdge
    have returned : ∃ next : before.realResidual, next.val.1 = record.input.1 ∧
        Reaches (oldRelation (reverseOld transcript before.realResidual)) next output := by
      rcases following with ⟨_, single⟩ | ⟨_, nextOutput, nextInput, step, between⟩
      · exact ⟨finalInput, lastColumn, single⟩
      · have nextEdge : record.edge nextInput.val nextOutput.val := step
        exact ⟨nextInput, nextEdge.1, between⟩
    obtain ⟨next, nextColumn, oldReturn⟩ := returned
    have support : output.val.1 ∈ leftSupport (endpointPairs (realRecordRelation transcript)
        before.realResidual record.output.2 record.input.1) :=
      Finset.mem_image.mpr ⟨(output.val.1, next.val.2),
        endpoint_of_old_reverse oldReturn outputRow nextColumn, rfl⟩
    exact ⟨input.val.2, output.val.1,
      endpoint_of_old_reverse earlier rfl inputColumn, Or.inr support, firstShift⟩

/-- Witness intersection at an entry into the old backward side using the new record.
Its input is either forward-occupied or reached from the new output row by old edges. -/
theorem backward_intersection_witness : BackwardBoundaryEventsSpec.BackwardIntersectionWitness := by
  intro n initials transcript record threshold before hasStarts closed oldSeparate stopped
  let updated := recordRelation (transcript ++ [record]) initials
  have intersects : (before.inherit updated).Intersects := stopped
  obtain ⟨a, ha, b, hb, path⟩ := (Boundary.inheritance updated before).2.2.mp intersects
  obtain ⟨start, startForward, firstOutlet, firstStep, afterFirst⟩ :=
    leaves_forward path ha (fun inForward ↦ oldSeparate ⟨b, inForward, hb⟩)
  have firstNew : vertexEdge record start firstOutlet :=
    ((relation_append transcript record).mp firstStep).resolve_left
      (fun oldStep ↦ afterFirst.1 (closed.1 startForward oldStep))
  by_cases immediate : firstOutlet ∈ before.backward
  · obtain ⟨column, _, shift⟩ := vertex_coordinates firstNew
    exact ⟨start.state.2, firstOutlet.state.1, Or.inl ⟨start, startForward, column, rfl⟩,
      cap_in_backward firstNew immediate, shift⟩
  · obtain ⟨outlet, outletBackward, inlet, lastStep, beforeLast⟩ :=
      enters_backward afterFirst immediate hb
    have lastNew : vertexEdge record inlet outlet :=
      ((relation_append transcript record).mp lastStep).resolve_left
        (fun oldStep ↦ beforeLast.2.1 (Or.inr (closed.2 outletBackward oldStep)))
    obtain ⟨inputColumn, _, shift⟩ := vertex_coordinates lastNew
    have between := residual_path_to_states hasStarts beforeLast
    let startPoint : before.realResidual := ⟨firstOutlet.state, between.1⟩
    let lastInput : before.realResidual := ⟨inlet.state, between.2.1⟩
    obtain ⟨walk⟩ := reversed_walk transcript record before.realResidual
      (a := startPoint) (b := lastInput) between
    -- Between two new uses, an old path reaches the entry edge's input from the new
    -- output row. Reversing the walk makes that segment an initial old stretch.
    have returned : ∃ previous : before.realResidual, previous.val.2 = record.output.2 ∧
        Reaches (oldRelation (reverseOld transcript before.realResidual)) lastInput previous := by
      by_cases noNew : walk.newUses = 0
      · exact ⟨startPoint, (vertex_coordinates firstNew).2.1, walk.old_reaches noNew⟩
      · obtain ⟨output, input, step, returnPath⟩ := first_new_prefix walk (Nat.pos_of_ne_zero noNew)
        have previous : record.edge input.val output.val := step
        exact ⟨output, (coordinates previous).2.1, returnPath⟩
    obtain ⟨previous, previousRow, oldReturn⟩ := returned
    have rate : inlet.state.2 ∈ rightSupport (endpointPairs (realRecordRelation transcript)
        before.realResidual record.output.2 record.input.1) :=
      Finset.mem_image.mpr ⟨(previous.val.1, inlet.state.2),
        endpoint_of_old_reverse oldReturn previousRow inputColumn, rfl⟩
    exact ⟨inlet.state.2, outlet.state.1, Or.inr rate,
      cap_in_backward lastNew outletBackward, shift⟩

/-- An inherited row has at most as many new capacities as the old left support. -/
theorem backward_inherited_count : BackwardBoundaryEventsSpec.BackwardInheritedCount := by
  intro n initials transcript record threshold before finish row hasStarts closed continued
  let left := leftSupport (endpointPairs (realRecordRelation transcript) before.realResidual
    row record.input.1)
  have subset : backwardInheritedCaps transcript record before row ⊆ (left : Set (Word n)) := by
    intro capacity inherited
    obtain ⟨inputRate, _, pair, _, _⟩ :=
      backward_inheritance_witness transcript record threshold before finish row capacity
        hasStarts closed continued inherited
    exact Finset.mem_image.mpr ⟨(capacity, inputRate), pair, rfl⟩
  change _ ≤ left.card
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_mono subset

/-- At fixed exposed coordinates the shift probability for backward inheritance in a row of a
disjoint round is at most $B_{\mathrm{ver}}(C+B_{\mathrm{ver}})/N$ with common threshold `C`. -/
theorem backward_inheritance_probability :
    BackwardBoundaryEventsSpec.BackwardInheritanceProbability := by
  intro n initials transcript threshold before inputColumn outputRow row Psi Pi recordFor
    hasStarts closed coordinatesFixed occupied returnedBound inputBound
  let pairs := endpointPairs (realRecordRelation transcript) before.realResidual
  let backward := (Set.toFinite (backwardCaps before outputRow)).toFinset
  let inputs := rightSupport (pairs row inputColumn)
  let outlets := backward ∪ leftSupport (pairs outputRow inputColumn)
  let event : Set (Word n) := {shift | ∃ finish,
    RoundStep transcript (recordFor shift) threshold before (.continued finish) ∧
      (backwardInheritedCaps transcript (recordFor shift) before row).Nonempty}
  have subset : event ⊆ (xorOffsets inputs outlets : Set (Word n)) := by
    rintro shift ⟨finish, continued, capacity, inherited⟩
    obtain ⟨input, output, endpoint, atOutlet, shiftEq⟩ :=
      backward_inheritance_witness transcript (recordFor shift) threshold before finish row capacity
        hasStarts closed continued inherited
    obtain ⟨columnEq, rowEq, fixedShift⟩ := coordinatesFixed shift
    rw [columnEq] at endpoint
    rw [columnEq, rowEq] at atOutlet
    have inputMem : input ∈ inputs := Finset.mem_image.mpr ⟨(capacity, input), endpoint, rfl⟩
    have outputMem : output ∈ outlets := by
      rcases atOutlet with occupiedCap | returned
      · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr occupiedCap)
      · exact Finset.mem_union_right _ returned
    exact mem_xorOffsets inputMem outputMem (shiftEq.trans fixedShift)
  have backwardBound : backward.card ≤ Psi := by
    dsimp only [backward]
    rw [← Set.ncard_eq_toFinset_card]
    exact occupied
  have outletBound : outlets.card ≤ Psi + Pi :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add backwardBound returnedBound)
  have candidateBound : (xorOffsets inputs outlets).card ≤ Pi * (Psi + Pi) :=
    (card_xorOffsets_le inputs outlets).trans (Nat.mul_le_mul inputBound outletBound)
  simpa only [Nat.cast_mul, Nat.cast_add] using uniform_shift_mass_le subset candidateBound

/-- At fixed exposed coordinates, bound intersection by the old backward occupancy
limit times the number of candidate rates, divided by `2 ^ n`. -/
theorem backward_intersection_probability :
    BackwardBoundaryEventsSpec.BackwardIntersectionProbability := by
  intro n initials transcript threshold before inputColumn outputRow Psi recordFor
    hasStarts closed disjoint coordinatesFixed occupied
  let pairs := endpointPairs (realRecordRelation transcript)
      before.realResidual outputRow inputColumn
  let forward := (Set.toFinite (forwardRates before inputColumn)).toFinset
  let caps := (Set.toFinite (backwardCaps before outputRow)).toFinset
  let rates := forward ∪ rightSupport pairs
  let event : Set (Word n) :=
    {shift | RoundStep transcript (recordFor shift) threshold before .intersected}
  have subset : event ⊆ (xorOffsets rates caps : Set (Word n)) := by
    intro shift stopped
    obtain ⟨rate, cap, atRate, atCap, shiftEq⟩ :=
      backward_intersection_witness transcript (recordFor shift) threshold before
        hasStarts closed disjoint stopped
    obtain ⟨columnEq, rowEq, fixedShift⟩ := coordinatesFixed shift
    rw [columnEq, rowEq] at atRate
    rw [rowEq] at atCap
    have rateMem : rate ∈ rates := by
      rcases atRate with wasForward | returned
      · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr wasForward)
      · exact Finset.mem_union_right _ returned
    have capMem : cap ∈ caps := (Set.Finite.mem_toFinset _).mpr atCap
    exact mem_xorOffsets rateMem capMem (shiftEq.trans fixedShift)
  have capBound : caps.card ≤ Psi := by
    dsimp only [caps]
    rw [← Set.ncard_eq_toFinset_card]
    exact occupied
  have rateBound : rates.card ≤ (forwardRates before inputColumn).ncard +
      (rightSupport pairs).card := by
    have count := Finset.card_union_le forward (rightSupport pairs)
    simpa only [forward, ← Set.ncard_eq_toFinset_card] using count
  have bound := (card_xorOffsets_le rates caps).trans
    ((Nat.mul_le_mul rateBound capBound).trans_eq (Nat.mul_comm _ _))
  simpa only [Nat.cast_mul] using uniform_shift_mass_le subset bound

end JH.Graph.BackwardBoundaryEvents
