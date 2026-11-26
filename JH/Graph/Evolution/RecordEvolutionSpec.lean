/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.EvolutionSpec
public import Mathlib.Data.Fintype.Sum

/-!
# Graft thresholds in the record graph

Graft eligibility and the terminal thresholds for a record graph.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

/-- An edge carrying some transcript label, including outgoing edges from virtual starts. -/
def recordRelation (transcript : Transcript n) (initials : Finset (State n))
    (a b : Vertex initials) : Prop :=
  ∃ label, transcript.edge initials label a b

/-- An edge between real states contributed by a record of the transcript. -/
def realRecordRelation (transcript : Transcript n) (a b : State n) : Prop :=
  ∃ label, transcript.realEdge label a b

/-- Virtual copies of the starts form the forward side. Real states in the target columns form
the backward side. -/
def initialBoundary (initials : Finset (State n)) (targetColumns : Set (Word n)) :
    Boundary (Vertex initials) where
  forward := Set.range Sum.inr
  backward := {v | ∃ state : State n, v = Sum.inl state ∧ state.1 ∈ targetColumns}

/-- The real states outside both sides of the boundary. -/
def Boundary.realResidual {initials : Finset (State n)} (sides : Boundary (Vertex initials)) :
    Set (State n) :=
  {state | Sum.inl state ∈ sides.residual}

/-- Every virtual starting vertex belongs to the forward set. -/
def Boundary.ContainsVirtualStarts {initials : Finset (State n)}
    (sides : Boundary (Vertex initials)) : Prop :=
  ∀ initial : {state : State n // state ∈ initials}, Sum.inr initial ∈ sides.forward

/-- Ancestors of the root in a given row, connected by paths inside the residual set. -/
def rowAncestors (edge : State n → State n → Prop) (vertices : Set (State n))
    (row : Word n) (root : State n) : Set (State n) :=
  {source | source.2 = row ∧ ReachesWithin edge vertices source root}

/-- Descendants of the root in a given column, connected by paths inside the residual set. -/
def columnDescendants (edge : State n → State n → Prop) (vertices : Set (State n))
    (column : Word n) (root : State n) : Set (State n) :=
  {target | target.1 = column ∧ ReachesWithin edge vertices root target}

/-- A real residual root qualifies for grafting when its row-ancestor or column-descendant count
reaches μ in the chosen direction. -/
def recordGraftEligible (transcript : Transcript n) (threshold : ℕ)
    {initials : Finset (State n)} (sides : Boundary (Vertex initials)) (direction : Direction) :
    Vertex initials → Prop
  | .inr _ => False
  | .inl root =>
    root ∈ sides.realResidual ∧
      match direction with
      | .forward =>
        ∃ row, threshold ≤ (rowAncestors (realRecordRelation transcript)
          sides.realResidual row root).ncard
      | .backward =>
        ∃ column, threshold ≤ (columnDescendants (realRecordRelation transcript)
          sides.realResidual column root).ncard

/-- The two residual cardinality bounds in equation (7). -/
def Boundary.WithinGraftThreshold {initials : Finset (State n)}
    (sides : Boundary (Vertex initials)) (transcript : Transcript n) (threshold : ℕ) : Prop :=
  ∀ root ∈ sides.realResidual,
    (∀ row, (rowAncestors (realRecordRelation transcript)
      sides.realResidual row root).ncard < threshold) ∧
    (∀ column, (columnDescendants (realRecordRelation transcript)
      sides.realResidual column root).ncard < threshold)

namespace RecordEvolutionSpec

/-- In the empty transcript the initial sides are closed and disjoint and contain all virtual
starts on the forward side. -/
def InitialBoundary : Prop :=
  ∀ {n : ℕ} (initials : Finset (State n)) (targetColumns : Set (Word n)),
    let sides := initialBoundary initials targetColumns
    sides.ContainsVirtualStarts ∧ ¬ sides.Intersects ∧
      sides.Closed (recordRelation ([] : Transcript n) initials)

/-- At the end of grafting, both strict inequalities of equation (7) hold. -/
def GraftThresholds : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (initials : Finset (State n)) (threshold : ℕ)
    (start : Boundary (Vertex initials)),
    start.ContainsVirtualStarts → start.Closed (recordRelation transcript initials) →
      ¬ start.Intersects →
      ∃ finish : Boundary (Vertex initials),
        GraftSequence (recordRelation transcript initials)
          (recordGraftEligible transcript threshold) start finish ∧
        start.GrowsTo finish ∧ finish.ContainsVirtualStarts ∧
        finish.Closed (recordRelation transcript initials) ∧ ¬ finish.Intersects ∧
        finish.WithinGraftThreshold transcript threshold

end RecordEvolutionSpec

end JH.Graph
