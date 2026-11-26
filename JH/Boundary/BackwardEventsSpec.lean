/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.ForwardEventsSpec

/-!
# Backward inheritance and intersection witnesses

Backward inheritance and intersection witnesses for an inverse access.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ} {initials : Finset (State n)}

namespace BackwardBoundaryEvents

/-- Capacities newly inherited into a backward row before the round's grafts. -/
def backwardInheritedCaps (transcript : Transcript n) (record : Record n)
    (before : Boundary (Vertex initials)) (row : Word n) : Set (Word n) :=
  {capacity | Sum.inl (capacity, row) ∈
      (before.inherit (recordRelation (transcript ++ [record]) initials)).backward ∧
    Sum.inl (capacity, row) ∉ before.backward}

end BackwardBoundaryEvents

namespace BackwardBoundaryEventsSpec

open BackwardBoundaryEvents (backwardInheritedCaps)
open BoundaryEvents (backwardCaps forwardRates vertexEdge)

/-- The prefix up to the first old-backward vertex stays residual until its final edge. -/
def BackwardTrim : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (row capacity : Word n),
    before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    capacity ∈ backwardInheritedCaps transcript record before row →
    ∃ outlet ∈ before.backward, ∃ inlet, vertexEdge record inlet outlet ∧
      ReachesWithin (recordRelation (transcript ++ [record]) initials) before.residual
        (.inl (capacity, row)) inlet

/-- The prefix before the first new edge gives an old endpoint pair for the inherited capacity. -/
def BackwardInheritanceWitness : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (row capacity : Word n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    capacity ∈ backwardInheritedCaps transcript record before row →
    ∃ inputRate outputCapacity : Word n,
      (capacity, inputRate) ∈ endpointPairs (realRecordRelation transcript)
        before.realResidual row record.input.1 ∧
      (outputCapacity ∈ backwardCaps before record.output.2 ∨
        outputCapacity ∈ leftSupport (endpointPairs (realRecordRelation transcript)
          before.realResidual record.output.2 record.input.1)) ∧
      inputRate ^^^ outputCapacity = record.shift

/-- The final new edge enters the old backward side. Its input is on the old forward
side or is reached by an old residual path from the preceding new output. -/
def BackwardIntersectionWitness : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before : Boundary (Vertex initials)),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects → RoundStep transcript record threshold before .intersected →
    ∃ inputRate outputCapacity : Word n,
      (inputRate ∈ forwardRates before record.input.1 ∨
        inputRate ∈ rightSupport (endpointPairs (realRecordRelation transcript)
          before.realResidual record.output.2 record.input.1)) ∧
      outputCapacity ∈ backwardCaps before record.output.2 ∧
      inputRate ^^^ outputCapacity = record.shift

/-- An inherited row has at most as many new capacities as the old left support. -/
def BackwardInheritedCount : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials)) (row : Word n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    RoundStep transcript record threshold before (.continued finish) →
    (backwardInheritedCaps transcript record before row).ncard ≤
      (leftSupport (endpointPairs (realRecordRelation transcript) before.realResidual
        row record.input.1)).card

/-- The backward inheritance bound with the request and input column held fixed. -/
def BackwardInheritanceProbability : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow row : Word n)
    (Psi Pi : ℕ) (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    (∀ shift, (recordFor shift).input.1 = inputColumn ∧
      (recordFor shift).output.2 = outputRow ∧ (recordFor shift).shift = shift) →
    (backwardCaps before outputRow).ncard ≤ Psi →
    (leftSupport (endpointPairs (realRecordRelation transcript) before.realResidual
      outputRow inputColumn)).card ≤ Pi →
    (rightSupport (endpointPairs (realRecordRelation transcript) before.realResidual
      row inputColumn)).card ≤ Pi →
    uniformShiftMass {shift | ∃ finish,
      RoundStep transcript (recordFor shift) threshold before (.continued finish) ∧
        (backwardInheritedCaps transcript (recordFor shift) before row).Nonempty} ≤
      (Pi : ℝ) * ((Psi : ℝ) + (Pi : ℝ)) / (2 : ℝ) ^ n

/-- The backward intersection estimate for a fixed input column. -/
def BackwardIntersectionProbability : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow : Word n)
    (Psi : ℕ) (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects →
    (∀ shift, (recordFor shift).input.1 = inputColumn ∧
      (recordFor shift).output.2 = outputRow ∧ (recordFor shift).shift = shift) →
    (backwardCaps before outputRow).ncard ≤ Psi →
    uniformShiftMass
      {shift | RoundStep transcript (recordFor shift) threshold before .intersected} ≤
      (Psi : ℝ) * ((forwardRates before inputColumn).ncard +
        (rightSupport (endpointPairs (realRecordRelation transcript) before.realResidual
          outputRow inputColumn)).card : ℕ) / (2 : ℝ) ^ n

end BackwardBoundaryEventsSpec

end JH.Graph
