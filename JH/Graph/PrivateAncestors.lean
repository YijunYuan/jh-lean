/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Menger
public import JH.Graph.PrivateAncestorsSpec
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

/-!
# Private ancestors for a minimal cover

A smallest target subcover retains all sources that could reach the original target set. Each
retained target has a private ancestor. Paths from those ancestors are pairwise
vertex-disjoint, so a packing bound limits the size of the subcover. This is an auxiliary
result about the finite directed graphs of Section 3.3.
-/

@[expose] public section

namespace JH.Graph

/-- Follow the first path to the shared vertex and the second path from it. -/
private theorem reaches_of_shared_vertex {V : Type*} {E : V → V → Prop}
    {a b c d v : V} {left right : List V}
    (hl : IsPath E ({a} : Set V) ({b} : Set V) left)
    (hr : IsPath E ({c} : Set V) ({d} : Set V) right)
    (hvl : v ∈ left) (hvr : v ∈ right) : Relation.ReflTransGen E a d := by
  obtain ⟨pre, _, hp⟩ := hl.prefix_of_mem hvl
  obtain ⟨revSuffix, _, hq⟩ := hr.reverse.prefix_of_mem (List.mem_reverse.mpr hvr)
  have hleft := reaches_iff_exists_isPath.mpr ⟨pre, hp⟩
  have hright : Relation.ReflTransGen E v d :=
    reaches_iff_exists_isPath.mpr ⟨revSuffix.reverse, hq.reverse⟩
  exact hleft.trans hright

/-- A least-cardinality cover gives one private ancestor per target. Their
witness paths are vertex-disjoint, so the packing bound applies to the cover. -/
theorem private_ancestor_subcover (V : Type*) [Finite V] : PrivateAncestorSubcover V := by
  classical
  intro E A B k hno
  let Covers (C : Finset V) : Prop :=
    ∀ a ∈ A, (∃ b ∈ B, Relation.ReflTransGen E a b) → ∃ b ∈ C, Relation.ReflTransGen E a b
  let covers := B.powerset.filter Covers
  have hB : B ∈ covers :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset_self B, fun _ _ h ↦ h⟩
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image covers Finset.card ⟨B, hB⟩
  obtain ⟨hpow, hcover⟩ := Finset.mem_filter.mp hC
  have hCB := Finset.mem_powerset.mp hpow
  -- Deleting a retained target breaks the cover at some source. That source can
  -- reach the deleted target and no other retained target.
  have hprivate (b : V) (hb : b ∈ C) :
      ∃ a ∈ A, Relation.ReflTransGen E a b ∧
        ∀ c ∈ C, c ≠ b → ¬ Relation.ReflTransGen E a c := by
    have hnotcover : ¬ Covers (C.erase b) := by
      intro herase
      have hsub := (Finset.erase_subset b C).trans hCB
      have hmem : C.erase b ∈ covers :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, herase⟩
      exact (Finset.card_erase_lt_of_mem hb).not_ge (hmin _ hmem)
    simp only [Covers, not_forall] at hnotcover
    obtain ⟨a, ha, hreachB, hmissing⟩ := hnotcover
    obtain ⟨c, hc, hac⟩ := hcover a ha hreachB
    have hcb : c = b := by
      by_contra hne
      exact hmissing ⟨c, Finset.mem_erase.mpr ⟨hne, hc⟩, hac⟩
    exact ⟨a, ha, hcb ▸ hac, fun c hc hne hreach ↦
      hmissing ⟨c, Finset.mem_erase.mpr ⟨hne, hc⟩, hreach⟩⟩
  choose ancestor hA hreach hother using fun b : C ↦ hprivate b.val b.property
  choose paths hpaths using fun b : C ↦ reaches_iff_exists_isPath.mp (hreach b)
  -- A shared vertex would let one private source reach the other retained target.
  have hdisjoint : Pairwise (fun i j : C ↦ ∀ v ∈ paths i, v ∉ paths j) := by
    intro i j hij v hvi hvj
    have hji : j.val ≠ i.val := fun h ↦ hij (Subtype.ext h.symm)
    exact hother i j.val j.property hji (reaches_of_shared_vertex (hpaths i) (hpaths j) hvi hvj)
  have hcard : C.card ≤ k := by
    by_contra hnot
    have hle : k + 1 ≤ C.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    let index (i : Fin (k + 1)) : C := C.equivFin.symm (Fin.castLE hle i)
    apply hno
    refine ⟨fun i ↦ paths (index i), ?_, ?_⟩
    · intro i
      exact (hpaths (index i)).mono (fun {_ _} h ↦ h)
        (Set.singleton_subset_iff.mpr (hA (index i)))
        (Set.singleton_subset_iff.mpr (hCB (index i).property))
    · intro i j hij
      have hne : index i ≠ index j := fun h ↦
        hij (Fin.castLE_injective hle (C.equivFin.symm.injective h))
      exact hdisjoint hne
  refine ⟨C, hCB, hcard, ?_, hprivate⟩
  intro a ha
  constructor
  · rintro ⟨b, hb, hab⟩
    exact ⟨b, hCB hb, hab⟩
  · exact hcover a ha

@[deprecated (since := "2026-11-25")] alias privateAncestorSubcover := private_ancestor_subcover

end JH.Graph
