/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.EvolutionSpec

/-!
# Boundary closure and graft termination

Inheritance closes both boundary sets under directed reachability. A graft moves a residual
successor or predecessor set into one boundary. Closed, disjoint boundaries stay disjoint
through grafting, and the number of remaining vertices is a termination measure.
-/

@[expose] public section

namespace JH.Graph

universe u

variable {Vertex : Type u}

theorem walk_iff_reaches {Label : Type*} (edge : Label → Vertex → Vertex → Prop)
    (a b : Vertex) :
    Nonempty (Walk edge a b) ↔ Reaches (fun x y ↦ ∃ label, edge label x y) a b := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact .refl
    | cons label step _ ih => exact Relation.ReflTransGen.head ⟨label, step⟩ ih
  · intro path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil _⟩
    | head step _ ih =>
        obtain ⟨label, step⟩ := step
        obtain ⟨rest⟩ := ih
        exact ⟨.cons label step rest⟩

namespace Boundary

theorem grows_refl (sides : Boundary Vertex) : sides.GrowsTo sides :=
  ⟨Set.Subset.rfl, Set.Subset.rfl⟩

theorem GrowsTo.trans {a b c : Boundary Vertex} (ab : a.GrowsTo b) (bc : b.GrowsTo c) :
    a.GrowsTo c :=
  ⟨ab.1.trans bc.1, ab.2.trans bc.2⟩

/-- Growing either boundary can only shrink the residual vertex set. -/
theorem GrowsTo.residual_subset {before after : Boundary Vertex}
    (grows : before.GrowsTo after) : after.residual ⊆ before.residual :=
  Set.compl_subset_compl.mpr (Set.union_subset_union grows.1 grows.2)

private theorem mem_residual {sides : Boundary Vertex} {vertex : Vertex} :
    vertex ∈ sides.residual ↔ vertex ∉ sides.forward ∧ vertex ∉ sides.backward := by
  simp [residual]

/-- Inheritance is closed under one more edge. It intersects precisely when an updated
path joins the two old boundaries. -/
theorem inheritance : EvolutionSpec.Inheritance.{u} := by
  intro α edge sides
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    exact ⟨a, ha, .refl⟩
  · intro b hb
    exact ⟨b, hb, .refl⟩
  · rintro a _ ⟨start, hs, path⟩ step
    exact ⟨start, hs, path.tail step⟩
  · rintro _ b ⟨target, ht, path⟩ step
    exact ⟨target, ht, path.head step⟩
  · constructor
    · rintro ⟨_, ⟨a, ha, leftPath⟩, ⟨b, hb, rightPath⟩⟩
      exact ⟨a, ha, b, hb, leftPath.trans rightPath⟩
    · rintro ⟨a, ha, b, hb, path⟩
      exact ⟨a, ⟨a, ha, .refl⟩, ⟨b, hb, path⟩⟩

/-- A graft preserves boundary closure and disjointness. Grafting a residual root
strictly shrinks the residual set because its zero-edge path includes the root. -/
theorem graft_invariants : EvolutionSpec.Graft.{u} := by
  intro α edge sides direction root closed separate
  classical
  cases direction with
  | forward =>
      let next := sides.graft edge Direction.forward root
      have grows : sides.GrowsTo next := ⟨fun _ h ↦ Or.inl h, fun _ h ↦ h⟩
      refine ⟨grows, ⟨?_, closed.2⟩, ?_, ?_⟩
      · intro a b inNext step
        rcases inNext with wasForward | ⟨rootResidual, aResidual, path⟩
        · exact Or.inl (closed.1 wasForward step)
        by_cases bForward : b ∈ sides.forward
        · exact Or.inl bForward
        -- Backward closure would put the residual source in the backward set if its successor
        -- lay there.
        have bBackward : b ∉ sides.backward := fun hb ↦
          (mem_residual.mp aResidual).2 (closed.2 hb step)
        have bResidual := mem_residual.mpr ⟨bForward, bBackward⟩
        exact Or.inr ⟨rootResidual, bResidual, path.tail ⟨aResidual, bResidual, step⟩⟩
      · rintro ⟨a, inNext, inBackward⟩
        rcases inNext with wasForward | ⟨_, aResidual, _⟩
        · exact separate ⟨a, wasForward, inBackward⟩
        · exact (mem_residual.mp aResidual).2 inBackward
      · intro rootResidual
        apply lt_of_le_not_ge grows.residual_subset
        intro reversed
        have inForward : root ∈ next.forward :=
          Or.inr ⟨rootResidual, rootResidual, Relation.ReflTransGen.refl⟩
        exact (reversed rootResidual) (Or.inl inForward)
  | backward =>
      let next := sides.graft edge Direction.backward root
      have grows : sides.GrowsTo next := ⟨fun _ h ↦ h, fun _ h ↦ Or.inl h⟩
      refine ⟨grows, ⟨closed.1, ?_⟩, ?_, ?_⟩
      · intro a b inNext step
        rcases inNext with wasBackward | ⟨bResidual, rootResidual, path⟩
        · exact Or.inl (closed.2 wasBackward step)
        by_cases aBackward : a ∈ sides.backward
        · exact Or.inl aBackward
        -- Forward closure rules out a predecessor in the forward set.
        have aForward : a ∉ sides.forward := fun ha ↦
          (mem_residual.mp bResidual).1 (closed.1 ha step)
        have aResidual := mem_residual.mpr ⟨aForward, aBackward⟩
        exact Or.inr ⟨aResidual, rootResidual, path.head ⟨aResidual, bResidual, step⟩⟩
      · rintro ⟨b, inForward, inNext⟩
        rcases inNext with wasBackward | ⟨bResidual, _, _⟩
        · exact separate ⟨b, inForward, wasBackward⟩
        · exact (mem_residual.mp bResidual).1 inForward
      · intro rootResidual
        apply lt_of_le_not_ge grows.residual_subset
        intro reversed
        have inBackward : root ∈ next.backward :=
          Or.inr ⟨rootResidual, rootResidual, Relation.ReflTransGen.refl⟩
        exact (reversed rootResidual) (Or.inr inBackward)

/-- Repeatedly graft eligible roots until the fixed graph has no eligible root. The eligibility
hypothesis ensures that each chosen graft removes at least its own root. -/
theorem graft_termination : EvolutionSpec.GraftTermination.{u} := by
  intro α _ edge eligible readyResidual start closed separate
  classical
  generalize cardinality : start.residual.ncard = count
  induction count using Nat.strong_induction_on generalizing start with
  | ind count ih =>
    by_cases canGraft : ∃ direction root, eligible start direction root
    · obtain ⟨direction, root, ready⟩ := canGraft
      let next := start.graft edge direction root
      obtain ⟨grows, nextClosed, nextSeparate, strict⟩ :=
        graft_invariants edge start direction root closed separate
      -- The graph stays fixed during this process. Induction is on the remaining vertices.
      have decreases : next.residual.ncard < count :=
        cardinality ▸ Set.ncard_lt_ncard (strict (readyResidual start direction root ready))
      obtain ⟨finish, steps, nextGrows, finishClosed, finishSeparate, done⟩ :=
        ih next.residual.ncard decreases next nextClosed nextSeparate rfl
      exact ⟨finish, .cons direction root ready steps, grows.trans nextGrows,
        finishClosed, finishSeparate, done⟩
    · exact ⟨start, .nil _, grows_refl start, closed, separate, fun d v h ↦ canGraft ⟨d, v, h⟩⟩

end Boundary

theorem GraftSequence.invariants {edge : Vertex → Vertex → Prop}
    {eligible : Boundary Vertex → Direction → Vertex → Prop} {start finish : Boundary Vertex}
    (steps : GraftSequence edge eligible start finish)
    (closed : start.Closed edge) (separate : ¬ start.Intersects) :
    start.GrowsTo finish ∧ finish.Closed edge ∧ ¬ finish.Intersects := by
  induction steps with
  | nil sides => exact ⟨sides.grows_refl, closed, separate⟩
  | @cons before _ direction root _ _ ih =>
    obtain ⟨grows, nextClosed, nextSeparate, _⟩ :=
      Boundary.graft_invariants edge before direction root closed separate
    obtain ⟨restGrows, finishClosed, finishSeparate⟩ := ih nextClosed nextSeparate
    exact ⟨grows.trans restGrows, finishClosed, finishSeparate⟩

end JH.Graph
