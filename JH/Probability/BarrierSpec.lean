/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# Exponential supermartingale for a ledger

Exponential supermartingales and the finite-horizon ledger bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace JH.Probability

universe u

/-- The exponential process in Section 3.4. The increment with index `i + 1` is compensated by
its conditional expectation with respect to the information at time `i`. -/
noncomputable def compensatedExp {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m) (cost : ℕ → Ω → ℝ) (B : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  Real.exp (Real.log 2 / B * (∑ i ∈ Finset.range j, cost (i + 1) ω) -
    (∑ i ∈ Finset.range j, μ[cost (i + 1) | ℱ i] ω) / B)

/-- The process with the displayed compensation in Section 3.4 is a supermartingale starting at
one when each adapted cost lies in `[0, B]` almost surely. -/
def CompensatedExpSupermartingale : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (cost : ℕ → Ω → ℝ) (B : ℝ),
    0 < B → StronglyAdapted ℱ cost → (∀ i, ∀ᵐ ω ∂μ, cost i ω ∈ Set.Icc 0 B) →
    Supermartingale (compensatedExp μ ℱ cost B) ℱ μ ∧
      ∀ ω, compensatedExp μ ℱ cost B 0 ω = 1

/-- The Section 3.4 tail bound for one ledger, with its initial value at most `Γ / 2` and the
sum of its conditional mean costs through `q` at most `Γ / 4`. -/
def SingleBarrierTail : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (cost ledger : ℕ → Ω → ℝ) (B Γ : ℝ) (q : ℕ),
    0 < B → 0 < Γ → StronglyAdapted ℱ cost → StronglyAdapted ℱ ledger →
    (∀ i, ∀ᵐ ω ∂μ, cost i ω ∈ Set.Icc 0 B) →
    (∀ᵐ ω ∂μ, ledger 0 ω ≤ Γ / 2) →
    (∀ᵐ ω ∂μ, ∀ i < q, ledger (i + 1) ω - ledger i ω ≤ cost (i + 1) ω) →
    (∀ᵐ ω ∂μ, (∑ i ∈ Finset.range q, μ[cost (i + 1) | ℱ i] ω) ≤ Γ / 4) →
    μ.real {ω | ∃ i ≤ q, Γ ≤ ledger i ω} ≤
      Real.exp (-((Real.log 2 / 2 - 1 / 4) * (Γ / B)))

end JH.Probability
