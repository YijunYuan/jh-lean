/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.Round
public import JH.Parameters.CertificateSpec
public import JH.Potential.Drift.ChargeSpec
public import JH.Potential.GraftLedgerSpec

/-!
# Replay and the first stopping round

Deterministic evolution and first-stop classification for the record graph.
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters

variable {n : ℕ} {initials : Finset (State n)}

/-- In the forward occupancy, each virtual start contributes the coordinates of its state. -/
def Boundary.forwardRates (sides : Boundary (Vertex initials)) (column : Word n) :
    Set (Word n) :=
  {rate | ∃ vertex ∈ sides.forward, vertex.state.1 = column ∧ vertex.state.2 = rate}

/-- Capacities of the real backward vertices in the given row. -/
def Boundary.backwardCaps (sides : Boundary (Vertex initials)) (row : Word n) :
    Set (Word n) :=
  {capacity | Sum.inl (capacity, row) ∈ sides.backward}

/-- The transcript, boundary, and graft counts after a prefix of the graph replay. -/
structure GraphSnapshot {n : ℕ} (initials : Finset (State n)) where
  /-- The records received by this point in the replay. -/
  records : Transcript n
  /-- The forward and backward vertex sets. -/
  sides : Boundary (Vertex initials)
  /-- Cumulative forward graft count in each column. -/
  forwardGrafts : Word n → ℕ
  /-- Cumulative backward graft count in each row. -/
  backwardGrafts : Word n → ℕ

namespace GraphSnapshot

/-- The empty transcript with the initial boundary and zero grafts on every line. -/
def initial (initials : Finset (State n)) (targetColumns : Set (Word n)) :
    GraphSnapshot initials :=
  ⟨[], initialBoundary initials targetColumns, fun _ ↦ 0, fun _ ↦ 0⟩

/-- The sides are closed and disjoint, with all virtual starts forward and all target columns
backward. -/
def ValidBoundary (snapshot : GraphSnapshot initials) (targetColumns : Set (Word n)) : Prop :=
  snapshot.sides.ContainsVirtualStarts ∧ snapshot.sides.Closed (recordRelation snapshot.records
    initials) ∧ ¬ snapshot.sides.Intersects ∧
    ∀ state : State n, state.1 ∈ targetColumns → Sum.inl state ∈ snapshot.sides.backward

/-- The account Λ in (18). Add the cumulative graft count for this line exactly when the pattern
is the singleton {0}. -/
noncomputable def ledger (snapshot : GraphSnapshot initials) (mu d : ℕ) (direction : Direction)
    (line : Word n) (mode : Finset (Word n)) : ℝ :=
  let edge := realRecordRelation snapshot.records
  let vertices := snapshot.sides.realResidual
  match direction with
  | .forward => translatedPotential edge vertices mu d line mode +
      if mode = {0} then (snapshot.forwardGrafts line : ℝ) else 0
  | .backward => backwardTranslatedPotential edge vertices mu d line mode +
      if mode = {0} then (snapshot.backwardGrafts line : ℝ) else 0

/-- Every account for an admissible nonempty pattern is strictly below Bpot. -/
def BelowBarrier (params : Params) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) : Prop :=
  ∀ direction line (mode : Finset (Word params.n)), mode.Nonempty → mode.card ≤ params.Pi →
    snapshot.ledger params.mu params.d direction line mode < params.Gamma

/-- The current residual graph satisfies the row-to-column disjoint-path bound. -/
def PathsBounded (snapshot : GraphSnapshot initials) (pi : ℕ) : Prop :=
  PathsWithinThreshold (realRecordRelation snapshot.records) snapshot.sides.realResidual pi

/-- Every forward column and backward row satisfies the common occupancy threshold. -/
def OccupancyBounded (snapshot : GraphSnapshot initials) (psi : ℕ) : Prop :=
  (∀ column, (snapshot.sides.forwardRates column).ncard ≤ psi) ∧
    (∀ row, (snapshot.sides.backwardCaps row).ncard ≤ psi)

/-- The residual graft, potential, path, and occupancy bounds hold at this snapshot. -/
def ValidParameters (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) : Prop :=
  snapshot.sides.WithinGraftThreshold snapshot.records params.mu ∧ snapshot.BelowBarrier params ∧
    snapshot.PathsBounded params.pi ∧ snapshot.OccupancyBounded psi

/-- Counts refer to the transfers after inheritance, during all grafts of this round. -/
noncomputable def afterGrafting (snapshot : GraphSnapshot initials) (record : Record n)
    (finish : Boundary (Vertex initials)) : GraphSnapshot initials :=
  let records := snapshot.records ++ [record]
  let inherited := snapshot.sides.inherit (recordRelation records initials)
  ⟨records, finish, fun column ↦ snapshot.forwardGrafts column +
    forwardGraftCount inherited finish column, fun row ↦ snapshot.backwardGrafts row +
    backwardGraftCount inherited finish row⟩

end GraphSnapshot

/-- The four first stopping events from Section 3.2. -/
inductive FirstGraphStop
  | intersect
  | overPotential
  | overConnected
  | overCrowded
  deriving DecidableEq

/-- An active snapshot or the snapshot and reason recorded at the first stop. -/
inductive GraphTracker {n : ℕ} (initials : Finset (State n))
  | active (snapshot : GraphSnapshot initials)
  | stopped (reason : FirstGraphStop) (snapshot : GraphSnapshot initials)

namespace GraphTracker

/-- The current snapshot, frozen at the first stop if one has occurred. -/
def snapshot : GraphTracker initials → GraphSnapshot initials
  | .active snapshot | .stopped _ snapshot => snapshot

/-- The recorded first stop, if the graph has stopped. -/
def stopReason : GraphTracker initials → Option FirstGraphStop
  | .active _ => none
  | .stopped reason _ => some reason

variable (params : Params) {initials : Finset (State params.n)}

/-- After a disjoint round, apply the three checks in priority order used by the stopped replay. -/
noncomputable def classify (psi : ℕ) (snapshot : GraphSnapshot initials) :
    GraphTracker initials := by
  classical
  exact
    if ¬ snapshot.BelowBarrier params then .stopped .overPotential snapshot
    else if ¬ snapshot.PathsBounded params.pi then .stopped .overConnected snapshot
    else if ¬ snapshot.OccupancyBounded psi then .stopped .overCrowded snapshot
    else .active snapshot

/-- Fix a choice of legal graft sequence from the current history and the current record. -/
noncomputable def selectRound (snapshot : GraphSnapshot initials) (record : Record params.n) :
    RoundOutcome (Vertex initials) :=
  (round_exists snapshot.records record params.mu initials snapshot.sides).choose

/-- An intersection is checked before grafting. States with a first stop are absorbing. -/
noncomputable def advance (psi : ℕ) (tracker : GraphTracker initials) (record : Record params.n) :
    GraphTracker initials :=
  match tracker with
  | .stopped reason snapshot => .stopped reason snapshot
  | .active snapshot =>
    match selectRound params snapshot record with
    | .intersected =>
      let updated := snapshot.records ++ [record]
      let inherited := snapshot.sides.inherit (recordRelation updated initials)
      .stopped .intersect ⟨updated, inherited, snapshot.forwardGrafts, snapshot.backwardGrafts⟩
    | .continued finish => classify params psi (snapshot.afterGrafting record finish)

/-- The increment is assessed while the old history is active, including the round
that first stops the graph. -/
noncomputable def charge (tracker : GraphTracker initials) (record : Record params.n)
    (direction : Direction) (line : Word params.n) (mode : Finset (Word params.n)) : ℝ :=
  match tracker with
  | .stopped _ _ => 0
  | .active snapshot =>
    match direction with
    | .forward => translatedIncrement snapshot.records record snapshot.sides.realResidual
        params.mu params.d line mode
    | .backward => translatedIncrement (snapshot.records.map transposeRecord)
        (transposeRecord record) (Prod.swap ⁻¹' snapshot.sides.realResidual)
          params.mu params.d line mode

/-- Run the stopped graph evolution through a transcript in record order. -/
noncomputable def replay (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)) (records : Transcript params.n) : GraphTracker initials :=
  records.foldl (advance params psi) (.active (GraphSnapshot.initial initials targetColumns))

end GraphTracker

namespace StoppedGraphSpec

/-- Classify simultaneous threshold crossings after grafting in potential, path, then occupancy
order. -/
def ThresholdPriority : Prop :=
  ∀ (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials),
    (GraphTracker.classify params psi snapshot = .stopped .overPotential snapshot ↔
      ¬ snapshot.BelowBarrier params) ∧
    (GraphTracker.classify params psi snapshot = .stopped .overConnected snapshot ↔
      snapshot.BelowBarrier params ∧ ¬ snapshot.PathsBounded params.pi) ∧
    (GraphTracker.classify params psi snapshot = .stopped .overCrowded snapshot ↔
      snapshot.BelowBarrier params ∧ snapshot.PathsBounded params.pi ∧
        ¬ snapshot.OccupancyBounded psi) ∧
    (GraphTracker.classify params psi snapshot = .active snapshot ↔
      snapshot.BelowBarrier params ∧ snapshot.PathsBounded params.pi ∧
        snapshot.OccupancyBounded psi)

/-- An active replay has consumed the supplied transcript and retains a valid boundary. -/
def ActiveReplay : Prop :=
  ∀ (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)) (records : Transcript params.n)
    (snapshot : GraphSnapshot initials),
    GraphTracker.replay params psi initials targetColumns records = .active snapshot →
      snapshot.records = records ∧ snapshot.ValidBoundary targetColumns

/-- Active replay preserves the initial bounds on grafts, potential, paths, and occupancy. -/
def ActiveParameters : Prop :=
  ∀ (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)),
    (GraphSnapshot.initial initials targetColumns).ValidParameters params psi →
    ∀ (records : Transcript params.n) (snapshot : GraphSnapshot initials),
      GraphTracker.replay params psi initials targetColumns records = .active snapshot →
      snapshot.ValidParameters params psi

/-- The common certificate and initial occupancy bound give valid parameters on the empty
transcript. -/
def InitialParameters : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)), params.CommonCertificate q →
    (GraphSnapshot.initial initials targetColumns).OccupancyBounded psi →
    (GraphSnapshot.initial initials targetColumns).ValidParameters params psi

/-- One initial state and one target column have occupancy at most one on every line. -/
def FixedInitialOccupancy : Prop :=
  ∀ {n : ℕ} (initial : State n) (target : Word n) (psi : ℕ), 1 ≤ psi →
    (GraphSnapshot.initial {initial} {target}).OccupancyBounded psi

/-- This includes the residual graph in the first stopping round. -/
def ResidualMonotone : Prop :=
  ∀ (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)) (earlier later : Transcript params.n),
    (GraphTracker.replay params psi initials targetColumns
      (earlier ++ later)).snapshot.sides.realResidual
      ⊆ (GraphTracker.replay params psi initials targetColumns earlier).snapshot.sides.realResidual

/-- The first stop is caused by a particular record following an active prefix. -/
def EarliestRecord : Prop :=
  ∀ (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)) (records : Transcript params.n)
    (reason : FirstGraphStop) (snapshot : GraphSnapshot initials),
    GraphTracker.replay params psi initials targetColumns records = .stopped reason snapshot →
    ∃ earlier record later before, records = earlier ++ [record] ++ later ∧
      GraphTracker.replay params psi initials targetColumns earlier = .active before ∧
      GraphTracker.advance params psi (.active before) record = .stopped reason snapshot

/-- A walk from a virtual start to a real target column forces the replay to stop. -/
def SuccessStops : Prop :=
  ∀ (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targetColumns : Set (Word params.n)) (records : Transcript params.n),
    (∃ start : {state : State params.n // state ∈ initials}, ∃ target : State params.n,
      target.1 ∈ targetColumns ∧ Reaches (recordRelation records initials)
        (.inr start) (.inl target)) →
      ∃ reason snapshot, GraphTracker.replay params psi initials targetColumns records =
        .stopped reason snapshot

end StoppedGraphSpec

end JH.Graph
