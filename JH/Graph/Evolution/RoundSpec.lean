/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.RecordEvolutionSpec

/-!
# A record-graph round

Inheritance, grafting, and stopping during one record-graph round.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

/-- An old label keeps its position when the current record is appended. -/
def priorLabel (transcript : Transcript n) (record : Record n) (label : transcript.Label) :
    Transcript.Label (transcript ++ [record]) :=
  ⟨label.val, Nat.lt_of_lt_of_le label.isLt (by simp)⟩

/-- The position of the newly appended record in the extended transcript. -/
def newLabel (transcript : Transcript n) (record : Record n) :
    Transcript.Label (transcript ++ [record]) :=
  ⟨transcript.length, by simp⟩

/-- The add-only graph (Arg) on the real residual vertices from before the round. -/
def argumentEdge (transcript : Transcript n) (record : Record n) {initials : Finset (State n)}
    (before : Boundary (Vertex initials)) : State n → State n → Prop :=
  inducedEdge (realRecordRelation (transcript ++ [record])) before.realResidual

/-- A round either detects an intersection during inheritance or returns the boundary after
grafting. -/
inductive RoundOutcome (A : Type) where
  | intersected
  | continued (finish : Boundary A)

/-- A single update appends one labelled record, tests intersection after inheritance, and
grafts only when the inherited sets are disjoint. Graft order may be chosen from the round state. -/
def RoundStep (transcript : Transcript n) (record : Record n) (threshold : ℕ)
    {initials : Finset (State n)} (before : Boundary (Vertex initials)) :
    RoundOutcome (Vertex initials) → Prop :=
  let updated := transcript ++ [record]
  let edge := recordRelation updated initials
  let inherited := before.inherit edge
  let eligible := recordGraftEligible updated threshold
  fun outcome ↦
    match outcome with
    | .intersected => inherited.Intersects
    | .continued finish =>
        ¬ inherited.Intersects ∧
          GraftSequence edge eligible inherited finish ∧
          ∀ direction root, ¬ eligible finish direction root

namespace RoundSpec

/-- Appending a record preserves all old labels and introduces exactly one new label. -/
def RecordIndices : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n),
    (∀ label : transcript.Label,
      (transcript ++ [record]).get (priorLabel transcript record label) = transcript.get label) ∧
    (transcript ++ [record]).get (newLabel transcript record) = record ∧
    ∀ label : Transcript.Label (transcript ++ [record]),
      label = newLabel transcript record ∨
        ∃ earlier : transcript.Label, label = priorLabel transcript record earlier

/-- Every fresh record and incoming boundary admit a legal graph round. -/
def Existence : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (threshold : ℕ)
    (initials : Finset (State n)) (before : Boundary (Vertex initials)),
    ∃ outcome, RoundStep transcript record threshold before outcome

/-- The graph after a continuing round has the intended closures and strict residual bounds.
The old real residual set is still used for argumentEdge in that same round. -/
def Continuation : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (threshold : ℕ)
    (initials : Finset (State n)) (before finish : Boundary (Vertex initials)),
    before.ContainsVirtualStarts →
      RoundStep transcript record threshold before (.continued finish) →
        let updated := transcript ++ [record]
        before.GrowsTo finish ∧ finish.ContainsVirtualStarts ∧
          finish.realResidual ⊆ before.realResidual ∧
          finish.Closed (recordRelation updated initials) ∧ ¬ finish.Intersects ∧
          finish.WithinGraftThreshold updated threshold

end RoundSpec

end JH.Graph
