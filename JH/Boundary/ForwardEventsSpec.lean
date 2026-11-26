/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.EndpointsSpec
public import JH.Connectivity.ShiftTestSpec
public import JH.Graph.Evolution.RoundSpec

/-!
# Forward inheritance and intersection witnesses

Old-boundary witnesses for forward inheritance and intersection in Section 3.4.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ} {initials : Finset (State n)}

namespace BoundaryEvents

/-- Rates in a forward column, including the rates of virtual starts there. -/
def forwardRates (before : Boundary (Vertex initials)) (column : Word n) : Set (Word n) :=
  {rate | ∃ v ∈ before.forward, v.state.1 = column ∧ v.state.2 = rate}

/-- Capacities of real backward vertices in a fixed row. -/
def backwardCaps (before : Boundary (Vertex initials)) (row : Word n) : Set (Word n) :=
  {capacity | Sum.inl (capacity, row) ∈ before.backward}

/-- Rates newly inherited before grafting in this round. -/
def forwardInheritedRates (transcript : Transcript n) (record : Record n)
    (before : Boundary (Vertex initials)) (column : Word n) : Set (Word n) :=
  {rate | Sum.inl (column, rate) ∈
      (before.inherit (recordRelation (transcript ++ [record]) initials)).forward ∧
    Sum.inl (column, rate) ∉ before.forward}

/-- A new record supplies edges from real and virtual sources to real targets. -/
def vertexEdge (record : Record n) (a b : Vertex initials) : Prop :=
  match b with
  | .inl target => record.edge a.state target
  | .inr _ => False

end BoundaryEvents

namespace BoundaryEventsSpec

/-- Trim the path at its last old-forward vertex. Its first edge uses this record
and the remaining path stays in the old residual set. -/
def ForwardTrim : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (column rate : Word n),
    before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    rate ∈ BoundaryEvents.forwardInheritedRates transcript record before column →
    ∃ (start : Vertex initials), start ∈ before.forward ∧
      ∃ outlet : Vertex initials, BoundaryEvents.vertexEdge record start outlet ∧
        ReachesWithin (recordRelation (transcript ++ [record]) initials) before.residual
          outlet (.inl (column, rate))

/-- The old suffix after the final new edge gives an endpoint pair for the inherited rate.
The input rate comes from the old forward side or a return path after a previous new edge. -/
def ForwardInheritanceWitness : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (column rate : Word n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    rate ∈ BoundaryEvents.forwardInheritedRates transcript record before column →
    ∃ inputRate outputCapacity : Word n,
      (inputRate ∈ BoundaryEvents.forwardRates before record.input.1 ∨
        inputRate ∈ rightSupport (endpointPairs (realRecordRelation transcript)
          before.realResidual record.output.2 record.input.1)) ∧
      (outputCapacity, rate) ∈ endpointPairs (realRecordRelation transcript)
        before.realResidual record.output.2 column ∧
      inputRate ^^^ outputCapacity = record.shift

/-- An intersecting round uses a new edge leaving the old forward side. Its output is
already backward or starts an old residual path to the next new input. -/
def ForwardIntersectionWitness : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before : Boundary (Vertex initials)),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects → RoundStep transcript record threshold before .intersected →
    ∃ inputRate outputCapacity : Word n,
      inputRate ∈ BoundaryEvents.forwardRates before record.input.1 ∧
      (outputCapacity ∈ BoundaryEvents.backwardCaps before record.output.2 ∨
        outputCapacity ∈ leftSupport (endpointPairs (realRecordRelation transcript)
          before.realResidual record.output.2 record.input.1)) ∧
      inputRate ^^^ outputCapacity = record.shift

/-- An inherited column has at most as many new rates as the old right support. -/
def ForwardInheritedCount : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (column : Word n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    (BoundaryEvents.forwardInheritedRates transcript record before column).ncard ≤
      (rightSupport (endpointPairs (realRecordRelation transcript) before.realResidual
        record.output.2 column)).card

/-- The forward one-round inheritance estimate used for (23), with the request and output row
fixed before drawing the shift. -/
def ForwardInheritanceProbability : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow column : Word n)
    (Psi Pi : ℕ) (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    (∀ shift, (recordFor shift).input.1 = inputColumn ∧
      (recordFor shift).output.2 = outputRow ∧ (recordFor shift).shift = shift) →
    (BoundaryEvents.forwardRates before inputColumn).ncard ≤ Psi →
    (rightSupport (endpointPairs (realRecordRelation transcript) before.realResidual
      outputRow inputColumn)).card ≤ Pi →
    (leftSupport (endpointPairs (realRecordRelation transcript) before.realResidual
      outputRow column)).card ≤ Pi →
    uniformShiftMass {shift | ∃ finish,
      RoundStep transcript (recordFor shift) threshold before (.continued finish) ∧
        (BoundaryEvents.forwardInheritedRates transcript (recordFor shift)
          before column).Nonempty} ≤
      (Pi : ℝ) * ((Psi : ℝ) + (Pi : ℝ)) / (2 : ℝ) ^ n

/-- The forward intersection estimate for a fixed output row, prior to averaging over rows. -/
def ForwardIntersectionProbability : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow : Word n)
    (Psi : ℕ) (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects →
    (∀ shift, (recordFor shift).input.1 = inputColumn ∧
      (recordFor shift).output.2 = outputRow ∧ (recordFor shift).shift = shift) →
    (BoundaryEvents.forwardRates before inputColumn).ncard ≤ Psi →
    uniformShiftMass
      {shift | RoundStep transcript (recordFor shift) threshold before .intersected} ≤
      (Psi : ℝ) * ((BoundaryEvents.backwardCaps before outputRow).ncard +
        (leftSupport (endpointPairs (realRecordRelation transcript) before.realResidual
          outputRow inputColumn)).card : ℕ) / (2 : ℝ) ^ n

end BoundaryEventsSpec

end JH.Graph
