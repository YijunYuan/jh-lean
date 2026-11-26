/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.RecordEvolutionSpec
public import JH.Graph.MengerSpec
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Prod

/-!
# Endpoint supports of the residual graph

Endpoint pairs in the residual graph and their row and column bounds.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

/-- The endpoint relation of Lemma 1, whose entries are a source capacity and a target rate. -/
noncomputable def endpointPairs (edge : State n → State n → Prop) (vertices : Set (State n))
    (row column : Word n) : Finset (Word n × Word n) := by
  classical
  exact Finset.univ.filter fun pair ↦ ReachesWithin edge vertices (pair.1, row) (column, pair.2)

/-- The first-coordinate support of an endpoint relation in Lemma 1. -/
def leftSupport {A B : Type*} [DecidableEq A] (pairs : Finset (A × B)) : Finset A :=
  pairs.image Prod.fst

/-- The second-coordinate support of an endpoint relation in Lemma 1. -/
def rightSupport {A B : Type*} [DecidableEq B] (pairs : Finset (A × B)) : Finset B :=
  pairs.image Prod.snd

/-- The vertex type of the induced graph is the residual subtype. -/
def residualRelation (edge : State n → State n → Prop) (vertices : Set (State n))
    (a b : vertices) : Prop :=
  edge a.val b.val

/-- Vertices of the residual subtype with the given rate. -/
def rowVertices (vertices : Set (State n)) (row : Word n) : Set vertices :=
  {state | state.val.2 = row}

/-- Vertices of the residual subtype with the given capacity. -/
def columnVertices (vertices : Set (State n)) (column : Word n) : Set vertices :=
  {state | state.val.1 = column}

/-- Every residual row-to-column packing has at most the given number of disjoint paths. -/
def PathsWithinThreshold (edge : State n → State n → Prop) (vertices : Set (State n))
    (threshold : ℕ) : Prop :=
  ∀ row column,
    ¬ HasDisjointPaths (residualRelation edge vertices)
      (rowVertices vertices row) (columnVertices vertices column) (threshold + 1)

/-- Reverse a record and swap the roles of capacity and rate. -/
def transposeRecord (record : Record n) : Record n :=
  ⟨record.output.swap, record.input.swap,
    match record.direction with
    | .forward => .backward
    | .backward => .forward⟩

namespace EndpointsSpec

/-- The quantitative bounds in Lemma 1. Both endpoints participate in the vertex packing. -/
def SupportBounds : Prop :=
  ∀ {n : ℕ} (edge : State n → State n → Prop) (vertices : Set (State n)) (mu pi : ℕ),
    (∀ root ∈ vertices,
      (∀ row, (rowAncestors edge vertices row root).ncard < mu) ∧
      (∀ column, (columnDescendants edge vertices column root).ncard < mu)) →
    PathsWithinThreshold edge vertices pi →
    ∀ row column,
      let pairs := endpointPairs edge vertices row column
      (leftSupport pairs).card ≤ pi * (mu - 1) ∧
        (rightSupport pairs).card ≤ pi * (mu - 1) ∧
        pairs.card ≤ pi * (mu - 1) ^ 2

/-- The two sums in (13), using only the per-cell bound from Lemma 1. -/
def TotalBounds : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (theta : ℕ),
    (∀ row column, (endpointPairs (realRecordRelation transcript) vertices row column).card
      ≤ theta) →
    (∀ row, (∑ column : Word n,
      (endpointPairs (realRecordRelation transcript) vertices row column).card) ≤
      2 ^ n + transcript.length * theta) ∧
    (∀ column, (∑ row : Word n,
      (endpointPairs (realRecordRelation transcript) vertices row column).card) ≤
      2 ^ n + transcript.length * theta)

end EndpointsSpec

end JH.Graph
