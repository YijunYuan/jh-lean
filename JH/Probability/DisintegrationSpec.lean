/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Discrete conditioning on an observed reply

Conditioning on the result of a discrete observation.
-/

@[expose] public section

namespace JH.Probability

universe u v w

/-- A supported observation comes from a supported sample in its fiber. -/
theorem fiber_witness {α : Type u} {β : Type v} (p : PMF α) (observe : α → β)
    {y : β} (hy : y ∈ (p.map observe).support) : ∃ x ∈ observe ⁻¹' {y}, x ∈ p.support := by
  obtain ⟨x, hx, hxy⟩ := (PMF.mem_support_map_iff observe p y).mp hy
  exact ⟨x, Set.mem_singleton_iff.mpr hxy, hx⟩

@[deprecated (since := "2026-11-25")] alias filterFiberWitness := fiber_witness

/-- Two supported conditioning events share a supported sample. -/
theorem inter_witness {α : Type u} (p : PMF α) (s t : Set α)
    (hs : ∃ x ∈ s, x ∈ p.support) (ht : ∃ x ∈ t, x ∈ (p.filter s hs).support) :
    ∃ x ∈ s ∩ t, x ∈ p.support := by
  obtain ⟨x, hxt, hx⟩ := ht
  have ⟨hxs, hxp⟩ := (PMF.mem_support_filter_iff hs).mp hx
  exact ⟨x, ⟨hxs, hxt⟩, hxp⟩

@[deprecated (since := "2026-11-25")] alias filterInterWitness := inter_witness

namespace DisintegrationSpec

/-- Drawing the observation first and then sampling within its fiber recovers the result law. -/
def MapBindFilter : Prop :=
  ∀ {α : Type u} {β : Type v} {γ : Type w} (p : PMF α) (observe : α → β) (result : α → γ),
    (p.map observe).bindOnSupport
      (fun y hy ↦ (p.filter (observe ⁻¹' {y}) (fiber_witness p observe hy)).map result) =
    p.map result

/-- Conditioning on two events in sequence agrees with conditioning on their intersection. -/
def FilterFilter : Prop :=
  ∀ {α : Type u} (p : PMF α) (s t : Set α)
    (hs : ∃ x ∈ s, x ∈ p.support) (ht : ∃ x ∈ t, x ∈ (p.filter s hs).support),
    (p.filter s hs).filter t ht = p.filter (s ∩ t) (inter_witness p s t hs ht)

end DisintegrationSpec

end JH.Probability
