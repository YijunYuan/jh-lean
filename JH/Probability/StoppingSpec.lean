/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# The finite-horizon maximal inequality

The finite-horizon maximal inequality for a nonnegative supermartingale.
-/

@[expose] public section

open MeasureTheory

namespace JH.Probability

universe u

/-- Equation (5). The event that a nonnegative supermartingale reaches `t` by time `q` has
probability at most its initial expectation divided by `t`. -/
def VilleBound : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    Supermartingale Y ℱ μ → (∀ i, ∀ᵐ ω ∂μ, 0 ≤ Y i ω) →
    ∀ (t : ℝ), 0 < t → ∀ q : ℕ,
      μ.real {ω | ∃ i ≤ q, t ≤ Y i ω} ≤ (∫ ω, Y 0 ω ∂μ) / t

end JH.Probability
