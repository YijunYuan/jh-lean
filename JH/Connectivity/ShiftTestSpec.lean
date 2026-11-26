/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.EndpointsSpec
public import JH.Graph.AddedPathSpec
public import JH.Probability.UniformPMF

/-!
# A necessary shift test for new paths

Necessary conditions on the shift for a walk to use the new record.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

/-- The edge of a specified old record on the residual vertex subtype. -/
def residualRecordEdge (transcript : Transcript n) (vertices : Set (State n))
    (label : transcript.Label) (a b : vertices) : Prop :=
  transcript.realEdge label a.val b.val

/-- The edge of the incoming record on the same residual vertex subtype. -/
def residualNewEdge (record : Record n) (vertices : Set (State n))
    (a b : vertices) : Prop :=
  record.edge a.val b.val

/-- Some walk from the source row to the target column uses the incoming record. -/
def HasNewPath (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (row column : Word n) : Prop :=
  ∃ a b : vertices, a.val.2 = row ∧ b.val.1 = column ∧
    ∃ path : AddedWalk (residualRecordEdge transcript vertices)
      (residualNewEdge record vertices) a b, 0 < path.newUses

/-- All XOR offsets between a source rate and a target capacity. -/
def xorOffsets (rates caps : Finset (Word n)) : Finset (Word n) :=
  (rates ×ˢ caps).image fun pair ↦ pair.1 ^^^ pair.2

/-- Candidate shifts for a path using the new record, as in Lemma 2. The three endpoint
relations all belong to the old residual graph. -/
noncomputable def shiftCandidates (transcript : Transcript n) (vertices : Set (State n))
    (inputColumn outputRow row column : Word n) : Finset (Word n) :=
  let pairs := endpointPairs (realRecordRelation transcript) vertices
  let rates := rightSupport (pairs row inputColumn) ∪ rightSupport (pairs outputRow inputColumn)
  let capacities := leftSupport (pairs outputRow column)
  xorOffsets rates capacities

/-- The probability of a set of offsets under a uniform n-bit word. -/
noncomputable def uniformShiftMass (event : Set (Word n)) : ℝ :=
  ((uniformPMF (Word n)).toOuterMeasure event).toReal

namespace ShiftTestSpec

/-- A row-to-column walk using the new record forces its offset to lie among the candidates of
Lemma 2. -/
def NecessaryShift : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (row column : Word n),
    HasNewPath transcript record vertices row column →
      record.shift ∈ shiftCandidates transcript vertices record.input.1 record.output.2 row column

/-- Two endpoint support bounds of size Bver give at most 2 Bver² candidate offsets. -/
def CandidateCard : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (Pi : ℕ),
    (∀ row column,
      (leftSupport (endpointPairs (realRecordRelation transcript) vertices row column)).card ≤ Pi ∧
      (rightSupport (endpointPairs (realRecordRelation transcript)
        vertices row column)).card ≤ Pi) →
    ∀ inputColumn outputRow row column,
      (shiftCandidates transcript vertices inputColumn outputRow row column).card ≤ 2 * Pi ^ 2

/-- The probability in Lemma 2 once the remaining coordinate and old history are fixed and the
shift is uniform. -/
def UniformCandidateProbability : Prop :=
  ∀ {n : ℕ} (Pi : ℕ) (event : Set (Word n)) (candidates : Finset (Word n)),
    event ⊆ (candidates : Set (Word n)) → candidates.card ≤ 2 * Pi ^ 2 →
      uniformShiftMass event ≤ 2 * (Pi : ℝ) ^ 2 / (2 : ℝ) ^ n

/-- With the exposed coordinates fixed, the probability of such a new walk is at most 2 Bver²/N.
-/
def UniformNewPathProbability : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (Pi : ℕ),
    (∀ row column,
      (leftSupport (endpointPairs (realRecordRelation transcript) vertices row column)).card ≤ Pi ∧
      (rightSupport (endpointPairs (realRecordRelation transcript)
        vertices row column)).card ≤ Pi) →
    ∀ (inputColumn outputRow row column : Word n) (recordFor : Word n → Record n),
      (∀ shift, (recordFor shift).input.1 = inputColumn ∧ (recordFor shift).output.2 = outputRow ∧
        (recordFor shift).shift = shift) →
      uniformShiftMass {shift | HasNewPath transcript (recordFor shift) vertices row column} ≤
        2 * (Pi : ℝ) ^ 2 / (2 : ℝ) ^ n

end ShiftTestSpec

end JH.Graph
