/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Accumulating separation probabilities

A finite-time separation bound for probability mass functions, as in equation (8).
-/

@[expose] public section

namespace JH.Separation

open scoped ENNReal BigOperators

universe u

/-- Probability that the state has the bad flag. -/
noncomputable def mass {α : Type u} (law : PMF α) (bad : α → Bool) : ℝ≥0∞ :=
  (law.map bad) true

/-- State laws for time-dependent transitions. -/
noncomputable def states {α : Type u} (init : PMF α) (step : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => init
  | i + 1 => (states init step i).bind (step i)

/-- The bound charges all previously bad states and the specified allowance for each good state. -/
def OneStep : Prop :=
  ∀ {α : Type u} (law : PMF α) (step : α → PMF α) (bad : α → Bool) (allowance : ℝ≥0∞),
    (∀ a ∈ law.support, bad a = false → mass (step a) bad ≤ allowance) →
      mass (law.bind step) bad ≤ mass law bad + allowance

/-- Sum the round allowances when every reachable initial state is good. -/
def FiniteTime : Prop :=
  ∀ {α : Type u} (init : PMF α) (step : ℕ → α → PMF α) (bad : α → Bool)
    (q : ℕ) (allowance : ℕ → ℝ≥0∞),
    (∀ a ∈ init.support, bad a = false) →
    (∀ i < q, ∀ a ∈ (states init step i).support,
      bad a = false → mass (step i a) bad ≤ allowance i) →
    mass (states init step q) bad ≤ ∑ i ∈ Finset.range q, allowance i

/-- The arithmetic sum of the separation allowances in equation (8). -/
def AllowanceSum : Prop :=
  ∀ (q : ℕ) (K : ℝ≥0∞),
    (∑ i ∈ Finset.range q, (i : ℝ≥0∞) / K) = ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * K)

/-- Equation (8) for reachable good states with per-round separation probability at most `i / K`. -/
def Formula4 : Prop :=
  ∀ {α : Type u} (init : PMF α) (step : ℕ → α → PMF α) (bad : α → Bool)
    (q : ℕ) (K : ℝ≥0∞),
    (∀ a ∈ init.support, bad a = false) →
    (∀ i < q, ∀ a ∈ (states init step i).support,
      bad a = false → mass (step i a) bad ≤ (i : ℝ≥0∞) / K) →
    mass (states init step q) bad ≤ ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * K)

/-- The same finite bound as a real probability for a positive finite reply-space size. -/
def Formula4Real : Prop :=
  ∀ {α : Type u} (init : PMF α) (step : ℕ → α → PMF α) (bad : α → Bool)
    (q K : ℕ), 0 < K →
    (∀ a ∈ init.support, bad a = false) →
    (∀ i < q, ∀ a ∈ (states init step i).support,
      bad a = false → mass (step i a) bad ≤ (i : ℝ≥0∞) / K) →
    (mass (states init step q) bad).toReal ≤ ((q * (q - 1) : ℕ) : ℝ) / (2 * (K : ℝ))

end JH.Separation
