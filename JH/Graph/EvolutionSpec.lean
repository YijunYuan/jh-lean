/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Model
public import Mathlib.Data.Set.Card

/-!
# Boundary closure and graft termination

Boundary closure under inheritance and termination of grafting.
-/

@[expose] public section

namespace JH.Graph

universe u

variable {Vertex : Type u}

/-- Directed reachability, including the zero-edge walk from a vertex to itself. -/
abbrev Reaches (edge : Vertex → Vertex → Prop) := Relation.ReflTransGen edge

/-- An edge of the induced graph, with both endpoints in the given set. -/
def inducedEdge (edge : Vertex → Vertex → Prop) (vertices : Set Vertex) (a b : Vertex) :
    Prop :=
  a ∈ vertices ∧ b ∈ vertices ∧ edge a b

/-- The membership conditions also apply to a zero-edge walk. -/
def ReachesWithin (edge : Vertex → Vertex → Prop) (vertices : Set Vertex) (a b : Vertex) :
    Prop :=
  a ∈ vertices ∧ b ∈ vertices ∧ Reaches (inducedEdge edge vertices) a b

/-- The forward and backward sets in the array graph of Section 3.1. -/
structure Boundary (Vertex : Type u) where
  /-- Vertices on the forward side. -/
  forward : Set Vertex
  /-- Vertices on the backward side. -/
  backward : Set Vertex

namespace Boundary

/-- The vertices outside both sides of the boundary. -/
def residual (sides : Boundary Vertex) : Set Vertex :=
  (sides.forward ∪ sides.backward)ᶜ

/-- The forward set contains successors and the backward set contains predecessors. -/
def Closed (sides : Boundary Vertex) (edge : Vertex → Vertex → Prop) : Prop :=
  (∀ ⦃a b⦄, a ∈ sides.forward → edge a b → b ∈ sides.forward) ∧
    (∀ ⦃a b⦄, b ∈ sides.backward → edge a b → a ∈ sides.backward)

/-- The forward and backward sets share a vertex. -/
def Intersects (sides : Boundary Vertex) : Prop :=
  ∃ vertex, vertex ∈ sides.forward ∧ vertex ∈ sides.backward

/-- Both sides of the boundary grow by inclusion. -/
def GrowsTo (before after : Boundary Vertex) : Prop :=
  before.forward ⊆ after.forward ∧ before.backward ⊆ after.backward

/-- The inherited forward and backward sets after adding the current record. -/
def inherit (sides : Boundary Vertex) (edge : Vertex → Vertex → Prop) : Boundary Vertex where
  forward := {b | ∃ a ∈ sides.forward, Reaches edge a b}
  backward := {a | ∃ b ∈ sides.backward, Reaches edge a b}

/-- Transfer the entire residual successor or predecessor set of the selected root. -/
def graft (sides : Boundary Vertex) (edge : Vertex → Vertex → Prop) :
    Direction → Vertex → Boundary Vertex
  | .forward, root =>
      ⟨sides.forward ∪ {b | ReachesWithin edge sides.residual root b}, sides.backward⟩
  | .backward, root =>
      ⟨sides.forward, sides.backward ∪ {a | ReachesWithin edge sides.residual a root}⟩

end Boundary

/-- A finite sequence of eligible grafts in the fixed graph for this round. -/
inductive GraftSequence (edge : Vertex → Vertex → Prop)
    (eligible : Boundary Vertex → Direction → Vertex → Prop) :
    Boundary Vertex → Boundary Vertex → Prop where
  | nil (sides) : GraftSequence edge eligible sides sides
  | cons {before after} (direction : Direction) (root : Vertex)
      (ready : eligible before direction root)
      (rest : GraftSequence edge eligible (before.graft edge direction root) after) :
      GraftSequence edge eligible before after

namespace EvolutionSpec

/-- Closing the sides under reachability yields an intersection exactly when an old forward
vertex reaches an old backward vertex. -/
def Inheritance : Prop :=
  ∀ {Vertex : Type u} (edge : Vertex → Vertex → Prop) (sides : Boundary Vertex),
    let next := sides.inherit edge
    sides.GrowsTo next ∧ next.Closed edge ∧
      (next.Intersects ↔ ∃ a ∈ sides.forward, ∃ b ∈ sides.backward, Reaches edge a b)

/-- Grafting preserves closure and disjointness and strictly shrinks the residual set when the
root is residual. -/
def Graft : Prop :=
  ∀ {Vertex : Type u} (edge : Vertex → Vertex → Prop) (sides : Boundary Vertex)
    (direction : Direction) (root : Vertex),
    sides.Closed edge → ¬ sides.Intersects →
      let next := sides.graft edge direction root
      sides.GrowsTo next ∧ next.Closed edge ∧ ¬ next.Intersects ∧
        (root ∈ sides.residual → next.residual ⊂ sides.residual)

/-- On a finite graph, grafts at eligible residual roots reach a boundary with no eligible root.
-/
def GraftTermination : Prop :=
  ∀ {Vertex : Type u} [Finite Vertex] (edge : Vertex → Vertex → Prop)
    (eligible : Boundary Vertex → Direction → Vertex → Prop),
    (∀ sides direction root, eligible sides direction root → root ∈ sides.residual) →
      ∀ start : Boundary Vertex, start.Closed edge → ¬ start.Intersects →
        ∃ finish : Boundary Vertex, GraftSequence edge eligible start finish ∧
          start.GrowsTo finish ∧ finish.Closed edge ∧ ¬ finish.Intersects ∧
          ∀ direction root, ¬ eligible finish direction root

end EvolutionSpec

end JH.Graph
