/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.Tape.TestsSpec
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Conditional averages on uniform tapes

Adapted finite expectations on a uniform tape.
-/

@[expose] public section

namespace JH.Probability

open PartialPermutation (uniformFinite)
open scoped BigOperators

universe u

namespace AdaptiveMean

/-- A cost or multiplicative factor can see the old prefix and the current sample. -/
abbrev Quantity (A : Type u) (q : ℕ) := (i : Fin q) → (Fin i.val → A) → A → ℝ

/-- Product of the adapted factors evaluated along one tape. -/
def product {A : Type u} {q : ℕ} (factor : Quantity A q) (tape : Fin q → A) : ℝ :=
  ∏ i : Fin q, factor i (TapeTests.prefixAt tape i) (tape i)

/-- Sum of the adapted costs evaluated along one tape. -/
def total {A : Type u} {q : ℕ} (cost : Quantity A q) (tape : Fin q → A) : ℝ :=
  ∑ i : Fin q, cost i (TapeTests.prefixAt tape i) (tape i)

end AdaptiveMean

namespace AdaptiveMeanSpec

/-- Iterate a uniform conditional mean bound over a nonnegative adapted product. -/
def ProductBound : Prop :=
  ∀ {A : Type u} [Fintype A] [Nonempty A] {q : ℕ}
    (factor : AdaptiveMean.Quantity A q) (bound : ℝ), 0 ≤ bound →
    (∀ i prior word, 0 ≤ factor i prior word) →
    (∀ i prior, (𝔼 word : A, factor i prior word) ≤ bound) →
    (𝔼 tape : Fin q → A, AdaptiveMean.product factor tape) ≤ bound ^ q

/-- The single-account exponential tail on the finite tape space. Nonnegative charges remain in
the total after a stopping round, and the total conditional allowance is at most Γ/4. -/
def FiniteBarrier : Prop :=
  ∀ {A : Type u} [Fintype A] [Nonempty A] {q : ℕ}
    (cost : AdaptiveMean.Quantity A q) (B Gamma mean : ℝ), 0 < B →
    (∀ i prior word, cost i prior word ∈ Set.Icc 0 B) →
    (∀ i prior, (𝔼 word : A, cost i prior word) ≤ mean) →
    (q : ℝ) * mean ≤ Gamma / 4 →
    ((uniformFinite (Fin q → A)).toOuterMeasure
      {tape | Gamma / 2 ≤ AdaptiveMean.total cost tape}).toReal ≤
      Real.exp (-((Real.log 2 / 2 - 1 / 4) * (Gamma / B)))

end AdaptiveMeanSpec

end JH.Probability
