/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.Reply
public import JH.Probability.Tape.TestsSpec
public import Mathlib.Data.Fin.Embedding

/-!
# Products of past-conditioned test probabilities

For the selected rounds in the proofs of (23) and Lemma 3, each test sees the preceding prefix
and one fresh word. Exposing the last word gives a product bound from uniform bounds on the
conditional pass probabilities.
-/

@[expose] public section

namespace JH.Probability.TapeTests

open PartialPermutation (uniformFinite)
open scoped ENNReal

universe u

variable {α : Type u} {q : ℕ}

private theorem mass_le_one (p : PMF α) (event : Set α) : p.toOuterMeasure event ≤ 1 :=
  (p.toOuterMeasure.mono (Set.subset_univ event)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).mpr (Set.subset_univ _))

private theorem prefix_snoc_castSucc (tape : Fin q → α) (word : α) (i : Fin q) :
    prefixAt (Fin.snoc tape word) i.castSucc = prefixAt tape i := by
  funext j
  exact @Fin.snoc_castSucc q (fun _ ↦ α) word tape ⟨j.val, j.isLt.trans i.isLt⟩

private theorem prefix_snoc_last (tape : Fin q → α) (word : α) :
    prefixAt (Fin.snoc tape word) (Fin.last q) = tape := by
  funext j
  exact @Fin.snoc_castSucc q (fun _ ↦ α) word tape j

/-- Split the tests of an extended tape into the preceding tests and its optional last test. -/
private theorem passes_snoc (test : Test α (q + 1)) {selected : Finset (Fin (q + 1))}
    {earlier : Finset (Fin q)} (mem_earlier : ∀ i, i ∈ earlier ↔ i.castSucc ∈ selected)
    (tape : Fin q → α) (word : α) :
    Fin.snoc tape word ∈ passes test selected ↔
      tape ∈ passes (fun i ↦ test i.castSucc) earlier ∧
        (Fin.last q ∈ selected → test (Fin.last q) tape word) := by
  constructor
  · intro allPass
    refine ⟨?_, ?_⟩
    · intro i member
      simpa only [prefix_snoc_castSucc, Fin.snoc_castSucc] using
        allPass i.castSucc ((mem_earlier i).mp member)
    · intro member
      simpa only [prefix_snoc_last, Fin.snoc_last] using allPass (Fin.last q) member
  · rintro ⟨before, last⟩ i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · intro member
      simpa only [prefix_snoc_last, Fin.snoc_last] using last member
    · intro member
      simpa only [prefix_snoc_castSucc, Fin.snoc_castSucc]
        using before j ((mem_earlier j).mpr member)

/-- Identify a prefix and its next sample with a tape one position longer. -/
private def appendWord (α : Type u) (q : ℕ) : ((Fin q → α) × α) ≃ (Fin (q + 1) → α) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ α)

/-- Isolate the last sample, summing over the complete preceding prefix. -/
private theorem mass_last_word [Finite α] [Nonempty α] (event : Set (Fin (q + 1) → α)) :
    (uniformFinite (Fin (q + 1) → α)).toOuterMeasure event =
      ∑' tape : Fin q → α, uniformFinite (Fin q → α) tape *
        (uniformFinite α).toOuterMeasure ((fun word ↦ Fin.snoc tape word) ⁻¹' event) := by
  have uniform : (ReplyCoupling.independentPair (uniformFinite (Fin q → α)) (uniformFinite α)).map
      (appendWord α q) = uniformFinite (Fin (q + 1) → α) := by
    rw [ReplyCoupling.independentPair_uniform, ReplyCoupling.uniformFinite_map_equiv]
  rw [← uniform, PMF.toOuterMeasure_map_apply, ReplyCoupling.independentPair,
    PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun tape ↦ ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- Passing all selected tests costs at most one factor of the conditional bound per round. -/
theorem adapted_product_bound : TapeTestsSpec.AdaptedProduct.{u} := by
  intro α _ _ q
  classical
  induction q with
  | zero =>
    intro test selected δ _
    have empty : selected = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i ↦ Fin.elim0 i
    rw [empty, Finset.card_empty, pow_zero]
    exact mass_le_one _ _
  | succ q ih =>
    intro test selected δ conditional
    let earlier := Finset.univ.filter fun i : Fin q ↦ i.castSucc ∈ selected
    have mem_earlier (i : Fin q) : i ∈ earlier ↔ i.castSucc ∈ selected := by simp [earlier]
    have erase : selected.erase (Fin.last q) = earlier.map Fin.castSuccEmb := by
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [Finset.mem_map, Fin.castSucc_ne_last]
      · simp [Finset.mem_map, Fin.castSucc_ne_last, mem_earlier]
    have count : earlier.card = (selected.erase (Fin.last q)).card := by
      rw [erase, Finset.card_map]
    let priorTest : Test α q := fun i ↦ test i.castSucc
    let before := passes priorTest earlier
    let factor := if Fin.last q ∈ selected then δ else 1
    have before_bound : (uniformFinite (Fin q → α)).toOuterMeasure before ≤ δ ^ earlier.card :=
      ih priorTest earlier δ (fun i present tape ↦
        conditional i.castSucc ((mem_earlier i).mp present) tape)
    -- A failed prefix makes this section empty. A passing prefix pays for the last test
    -- exactly when its index is selected.
    have section_bound (tape : Fin q → α) :
        (uniformFinite α).toOuterMeasure ((fun word ↦
          Fin.snoc tape word) ⁻¹' passes test selected) ≤
          before.indicator (fun _ ↦ factor) tape := by
      by_cases passed : tape ∈ before
      · rw [Set.indicator_of_mem passed]
        by_cases tested : Fin.last q ∈ selected
        · have subset : ((fun word ↦ Fin.snoc tape word) ⁻¹' passes test selected) ⊆
              approving test (Fin.last q) tape := by
            intro word present
            exact ((passes_snoc test mem_earlier tape word).mp present).2 tested
          exact ((uniformFinite α).toOuterMeasure.mono subset).trans
            (by simpa only [MeasureTheory.OuterMeasure.measureOf_eq_coe, factor, ite_eq_left tested]
              using conditional (Fin.last q) tested tape)
        · simpa only [factor, ite_eq_right tested] using mass_le_one (uniformFinite α)
            ((fun word ↦ Fin.snoc tape word) ⁻¹' passes test selected)
      · rw [Set.indicator_of_notMem passed]
        have empty : ((fun word ↦ Fin.snoc tape word) ⁻¹' passes test selected) = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun word hit ↦
            passed ((passes_snoc test mem_earlier tape word).mp hit).1
        rw [empty, MeasureTheory.measure_empty]
    calc
      _ = ∑' tape : Fin q → α, uniformFinite (Fin q → α) tape *
          (uniformFinite α).toOuterMeasure ((fun word ↦
            Fin.snoc tape word) ⁻¹' passes test selected) :=
        mass_last_word _
      _ ≤ ∑' tape : Fin q → α, uniformFinite (Fin q → α) tape *
        before.indicator (fun _ ↦ factor) tape :=
        tsum_le_tsum fun tape ↦ mul_le_mul_right (section_bound tape) _
      _ = (uniformFinite (Fin q → α)).toOuterMeasure before * factor := by
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun tape ↦ ?_
        by_cases passed : tape ∈ before <;> simp [passed]
      _ ≤ δ ^ earlier.card * factor := mul_le_mul_left before_bound _
      -- The last index contributes to the exponent precisely when it contributes a test.
      _ = δ ^ selected.card := by
        by_cases tested : Fin.last q ∈ selected
        · have size : earlier.card + 1 = selected.card :=
            (congrArg (· + 1) count).trans (Finset.card_erase_add_one tested)
          simp only [factor, ite_eq_left tested, ← pow_succ, size]
        · have size : earlier.card = selected.card :=
            count.trans (congrArg Finset.card (Finset.erase_eq_of_notMem tested))
          simp only [factor, ite_eq_right tested, mul_one, size]

end JH.Probability.TapeTests
