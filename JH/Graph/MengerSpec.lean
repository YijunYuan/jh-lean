/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Set.Basic

/-!
# Finite directed vertex Menger

A labelled walk in the record graph gives a vertex list by forgetting the labels. The adjacency
relation asserts existence of a label for each consecutive pair, so choosing such labels
reconstructs a walk. The separator statement uses simple paths. Erasing cycles of a walk
preserves its endpoints and keeps a subset of its vertices, hence preserves avoidance and
pairwise vertex disjointness.
-/

@[expose] public section

namespace JH.Graph

variable {V : Type*}

/-- A simple directed path from `A` to `B`. The endpoint conditions force the
list to be nonempty. A singleton list is the zero-edge path at a common vertex. -/
structure IsPath (E : V → V → Prop) (A B : Set V) (vertices : List V) : Prop where
  /-- Consecutive vertices follow directed edges. -/
  chain : vertices.IsChain E
  /-- A simple path has no repeated vertex. -/
  nodup : vertices.Nodup
  /-- The first vertex is in the source set. -/
  starts : ∃ a ∈ A, vertices.head? = some a
  /-- The last vertex is in the target set. -/
  ends : ∃ b ∈ B, vertices.getLast? = some b

/-- The paths have no common vertices, including their first and last vertices. -/
def HasDisjointPaths (E : V → V → Prop) (A B : Set V) (n : ℕ) : Prop :=
  ∃ paths : Fin n → List V,
    (∀ i, IsPath E A B (paths i)) ∧
      Pairwise (fun i j ↦ ∀ v ∈ paths i, v ∉ paths j)

/-- A separator meets every directed path from `A` to `B`.
It may contain vertices of either endpoint set. -/
def IsSeparator (E : V → V → Prop) (A B : Set V) (S : Finset V) : Prop :=
  ∀ vertices : List V, IsPath E A B vertices → ∃ v ∈ S, v ∈ vertices

/-- The finite directed vertex form of Theorem 1, stated at each threshold. The endpoint sets
may overlap, and the edge relation is arbitrary. -/
def DirectedVertexMenger (V : Type*) [Finite V] : Prop :=
  ∀ (E : V → V → Prop) (A B : Set V) (k : ℕ),
    (¬ HasDisjointPaths E A B (k + 1)) ↔
      ∃ S : Finset V, IsSeparator E A B S ∧ S.card ≤ k

end JH.Graph
