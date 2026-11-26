/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.Reply
public import JH.Probability.Barrier
public import JH.Probability.Tape.AdaptiveMeanSpec

/-!
# Conditional averages on uniform tapes

On a finite tape, conditioning on a prefix fixes the past while the next sample remains
uniform. Iterating the conditional estimate bounds products of adapted factors. Section 3.4
uses these products to estimate the cumulative charge of an account.
-/

@[expose] public section

namespace JH.Probability.AdaptiveMean

open PartialPermutation (uniformFinite)
open scoped BigOperators ENNReal

universe u

variable {A : Type u} {q : ℕ}

/-- Average the second uniform coordinate with the first coordinate held fixed. -/
theorem expect_product [Fintype A] {B : Type*} [Fintype B] (f : A × B → ℝ) :
    (𝔼 sample : A × B, f sample) = 𝔼 a : A, 𝔼 b : B, f (a, b) := by
  rw [← Finset.expect_product, Finset.univ_product_univ]

/-- Expose the last uniform sample, with the preceding prefix held fixed. -/
theorem expect_last [Fintype A] (f : (Fin (q + 1) → A) → ℝ) :
    (𝔼 tape : Fin (q + 1) → A, f tape) =
      𝔼 prior : Fin q → A, 𝔼 word : A, f (Fin.snoc prior word) := by
  let e : ((Fin q → A) × A) ≃ (Fin (q + 1) → A) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ A)
  calc
    _ = 𝔼 pair : (Fin q → A) × A, f (e pair) :=
      (Fintype.expect_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = _ := expect_product _

private theorem earlier_snoc (tape : Fin q → A) (word : A) (i : Fin q) :
    TapeTests.prefixAt (Fin.snoc tape word) i.castSucc = TapeTests.prefixAt tape i := by
  funext j
  exact @Fin.snoc_castSucc q (fun _ ↦ A) word tape ⟨j.val, j.isLt.trans i.isLt⟩

private theorem last_snoc (tape : Fin q → A) (word : A) :
    TapeTests.prefixAt (Fin.snoc tape word) (Fin.last q) = tape := by
  funext j
  exact @Fin.snoc_castSucc q (fun _ ↦ A) word tape j

private theorem product_snoc (factor : Quantity A (q + 1)) (tape : Fin q → A) (word : A) :
    product factor (Fin.snoc tape word) =
      product (fun i ↦ factor i.castSucc) tape * factor (Fin.last q) tape word := by
  simp only [product, Fin.prod_univ_castSucc, earlier_snoc, last_snoc,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- The conditional mean at round i is averaged over exactly the preceding prefix. -/
theorem expect_adapted_round [Fintype A] [Nonempty A] (cost : Quantity A q) (i : Fin q) :
    (𝔼 tape : Fin q → A, cost i (TapeTests.prefixAt tape i) (tape i)) =
      𝔼 prior : Fin i.val → A, 𝔼 word : A, cost i prior word := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [expect_last]
        simp only [last_snoc, Fin.snoc_last]
        rfl
      · rw [expect_last]
        -- The shortened tape determines both arguments to the earlier cost.
        simp only [earlier_snoc, Fin.snoc_castSucc, Fintype.expect_const]
        exact ih (fun k ↦ cost k.castSucc) j

/-- A uniform tape of pairs is equivalent to two independent uniform tapes. -/
theorem uniform_pair_tape {B : Type*} [Finite A] [Nonempty A] [Finite B] [Nonempty B] :
    (uniformFinite (Fin q → A × B)).map (fun tape ↦ (fun i ↦ (tape i).1, fun i ↦ (tape i).2)) =
      ReplyCoupling.independentPair (uniformFinite (Fin q → A)) (uniformFinite (Fin q → B)) := by
  change (uniformFinite _).map (Equiv.arrowProdEquivProdArrow (Fin q) (fun _ ↦ A) (fun _ ↦ B)) = _
  rw [ReplyCoupling.uniformFinite_map_equiv, ReplyCoupling.independentPair_uniform]

/-- Multiply the uniform upper bounds for the conditional means of nonnegative factors. -/
theorem adapted_product : AdaptiveMeanSpec.ProductBound.{u} := by
  intro A _ _ q
  induction q with
  | zero =>
      intro factor bound _ _ _
      simp [product]
  | succ q ih =>
      intro factor bound hbound nonneg each
      -- The earlier factors depend only on the prefix, so they can leave the last-word average.
      let earlier : Quantity A q := fun i ↦ factor i.castSucc
      have hprior := ih earlier bound hbound (fun i ↦ nonneg i.castSucc)
        (fun i ↦ each i.castSucc)
      rw [expect_last]
      calc
        _ ≤ 𝔼 tape : Fin q → A, product earlier tape * bound := by
          apply Finset.expect_le_expect
          intro tape _
          simp only [product_snoc, ← Finset.mul_expect]
          exact mul_le_mul_of_nonneg_left (each (Fin.last q) tape)
            (Finset.prod_nonneg (fun i _ ↦ nonneg i.castSucc _ _))
        _ = (𝔼 tape : Fin q → A, product earlier tape) * bound :=
          (Finset.expect_mul _ _ _).symm
        _ ≤ bound ^ q * bound := mul_le_mul_of_nonneg_right hprior hbound
        _ = bound ^ (q + 1) := (pow_succ _ _).symm

/-- Identify the uniform probability of an event with the average of its indicator. -/
theorem uniform_mass_eq_expect [Fintype A] [Nonempty A] (event : Set A) :
    ((uniformFinite A).toOuterMeasure event).toReal =
      (𝔼 word : A, event.indicator (fun _ ↦ (1 : ℝ)) word) := by
  classical
  rw [PartialPermutation.uniformFinite_eq_uniformOfFintype, toOuterMeasure_uniformPMF_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simpa only [Pi.one_def, Set.coe_toFinset, Finset.nnratCast_dens, Set.toFinset_card] using
    (Finset.expect_indicator_one (K := ℝ) event.toFinset).symm

/-- Bound a finite union by the number of events times their common probability bound. -/
theorem probability_iUnion_le_card_mul {I : Type*} [Fintype I] (law : PMF A)
    (events : I → Set A) (bound : ℝ) (hbound : 0 ≤ bound)
    (each : ∀ i, (law.toOuterMeasure (events i)).toReal ≤ bound) :
    (law.toOuterMeasure (⋃ i, events i)).toReal ≤ (Fintype.card I : ℝ) * bound := by
  have estimate (i : I) : law.toOuterMeasure (events i) ≤ ENNReal.ofReal bound := by
    have finite := law.tsum_coe_indicator_ne_top (events i)
    rw [← PMF.toOuterMeasure_apply] at finite
    exact (ENNReal.le_ofReal_iff_toReal_le finite hbound).2 (each i)
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) hbound)
  refine (MeasureTheory.measure_iUnion_fintype_le _ _).trans ?_
  simpa [nsmul_eq_mul, ENNReal.ofReal_mul] using
    Finset.sum_le_card_nsmul Finset.univ _ (ENNReal.ofReal bound) (fun i _ ↦ estimate i)

/-- Bound the total-cost event using the Section 3.4 exponential estimate on a finite tape. -/
theorem finite_barrier : AdaptiveMeanSpec.FiniteBarrier.{u} := by
  intro A _ _ q cost B Gamma mean hB range conditional htotal
  classical
  let coefficient := Real.log 2 / B
  let factor : Quantity A q := fun i prior word ↦ Real.exp (coefficient * cost i prior word)
  let event : Set (Fin q → A) := {tape | Gamma / 2 ≤ total cost tape}
  let threshold := Real.exp (coefficient * (Gamma / 2))
  have hcoeff : 0 ≤ coefficient := div_nonneg (Real.log_nonneg (by norm_num)) hB.le
  have hthreshold : 0 < threshold := Real.exp_pos _
  -- Use the exponential chord bound before taking the next-word average.
  have factorMean (i : Fin q) (prior : Fin i.val → A) :
      (𝔼 word : A, factor i prior word) ≤ Real.exp (mean / B) := by
    calc
      _ ≤ 𝔼 word : A, (1 + cost i prior word / B) := by
        apply Finset.expect_le_expect
        intro word _
        have hrange := range i prior word
        have interval : cost i prior word / B ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨div_nonneg hrange.1 hB.le, (div_le_one hB).2 hrange.2⟩
        have convex := exp_log_two_mul_le_one_add interval.1 interval.2
        change Real.exp (coefficient * cost i prior word) ≤ _
        rw [show coefficient * cost i prior word = Real.log 2 * (cost i prior word / B) by
          dsimp only [coefficient]; ring]
        exact convex
      _ = 1 + (𝔼 word : A, cost i prior word) / B := by
        rw [Finset.expect_add_distrib, Fintype.expect_one, ← Finset.expect_div]
      _ ≤ 1 + mean / B := add_le_add le_rfl (div_le_div_of_nonneg_right (conditional i prior) hB.le)
      _ ≤ Real.exp (mean / B) := by simpa only [add_comm] using Real.add_one_le_exp (mean / B)
  have productBound := adapted_product factor (Real.exp (mean / B)) (Real.exp_nonneg _)
    (fun _ _ _ ↦ Real.exp_nonneg _) factorMean
  -- Once the total cost reaches half the barrier, its exponential pays the event indicator.
  have eventCharge (tape : Fin q → A) :
      event.indicator (fun _ ↦ (1 : ℝ)) tape * threshold ≤ product factor tape := by
    by_cases crossed : tape ∈ event
    · rw [Set.indicator_of_mem crossed, one_mul]
      change threshold ≤ ∏ i : Fin q,
        Real.exp (coefficient * cost i (TapeTests.prefixAt tape i) (tape i))
      rw [← Real.exp_sum, ← Finset.mul_sum, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left crossed hcoeff
    · rw [Set.indicator_of_notMem crossed, zero_mul]
      exact Finset.prod_nonneg fun _ _ ↦ Real.exp_nonneg _
  have markov :
      (𝔼 tape : Fin q → A, event.indicator (fun _ ↦ (1 : ℝ)) tape) * threshold ≤
        (Real.exp (mean / B)) ^ q := by
    rw [Finset.expect_mul]
    exact (Finset.expect_le_expect fun tape _ ↦ eventCharge tape).trans productBound
  rw [show {tape | _} = event from rfl, uniform_mass_eq_expect]
  calc
    _ ≤ Real.exp (mean / B) ^ q / threshold := (le_div_iff₀ hthreshold).2 markov
    _ = Real.exp ((q : ℝ) * (mean / B) - coefficient * (Gamma / 2)) := by
      rw [← Real.exp_nat_mul, Real.exp_sub]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have bound := div_le_div_of_nonneg_right htotal hB.le
      dsimp only [coefficient]
      calc
        _ = ((q : ℝ) * mean) / B - Real.log 2 / B * (Gamma / 2) := by ring
        _ ≤ (Gamma / 4) / B - Real.log 2 / B * (Gamma / 2) := sub_le_sub_right bound _
        _ = _ := by ring

end JH.Probability.AdaptiveMean
