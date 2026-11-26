/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.PermutationSpec
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Products of past-conditioned test probabilities

Successive conditional bounds for tests on a finite uniform tape.
-/

@[expose] public section

namespace JH.Probability

open scoped ENNReal

universe u

namespace TapeTests

/-- At a round, a test can inspect the entire preceding prefix and the new word. -/
abbrev Test (α : Type u) (q : ℕ) := (i : Fin q) → (Fin i.val → α) → α → Prop

/-- The tape strictly before the selected index. -/
def prefixAt {α : Type u} {q : ℕ} (tape : Fin q → α) (i : Fin q) : Fin i.val → α :=
  fun j ↦ tape ⟨j.val, j.isLt.trans i.isLt⟩

/-- The words that pass the current test after the given prefix. -/
def approving {α : Type u} {q : ℕ} (test : Test α q) (i : Fin q)
    (prior : Fin i.val → α) : Set α :=
  {word | test i prior word}

/-- The full tapes passing the test at every selected index. -/
def passes {α : Type u} {q : ℕ} (test : Test α q) (selected : Finset (Fin q)) :
    Set (Fin q → α) :=
  {tape | ∀ i ∈ selected, test i (prefixAt tape i) (tape i)}

end TapeTests

namespace TapeTestsSpec

open PartialPermutation (uniformFinite)

/-- If every selected test approves at most mass `δ` of the new word at every prefix,
the probability of passing all the selected tests is at most `δ` to their number. -/
def AdaptedProduct : Prop :=
  ∀ {α : Type u} [Finite α] [Nonempty α] {q : ℕ} (test : TapeTests.Test α q)
    (selected : Finset (Fin q)) (δ : ℝ≥0∞),
    (∀ i ∈ selected, ∀ prior : Fin i.val → α,
      (uniformFinite α).toOuterMeasure (TapeTests.approving test i prior) ≤ δ) →
    (uniformFinite (Fin q → α)).toOuterMeasure (TapeTests.passes test selected) ≤ δ ^ selected.card

end TapeTestsSpec

end JH.Probability
