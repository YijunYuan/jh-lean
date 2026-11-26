/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.Convex
public import JH.Potential.Drift.ChargeSpec
public import JH.Potential.Drift.Events
public import JH.Potential.Weights

/-!
# Pointwise charges for potential growth

The add-only graph keeps the old residual vertices while adding the current record's edges. For
one translated pattern, charge one unit for reuse. The two other terms come from old ancestors
of the original targets and of the new inputs. The rowwise convexity bound yields both the
weighted charge and its equal-weight specialization.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

private theorem relation_of_append {transcript : Transcript n} (record : Record n)
    {source target : State n} (step : realRecordRelation transcript source target) :
    realRecordRelation (transcript ++ [record]) source target := by
  obtain ⟨label, edge⟩ := step
  refine ⟨priorLabel transcript record label, ?_⟩
  change ((transcript ++ [record]).get (priorLabel transcript record label)).edge source target
  rw [(appended_record_indices transcript record).1 label]
  exact edge

/-- Adding edges on a fixed residual vertex set increases a capped weight by at most one. -/
theorem pattern_increment_range (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n)
    (mode : Finset (Word n)) (offset : Word n) :
    0 ≤ patternIncrement transcript record vertices mu d column mode offset ∧
      patternIncrement transcript record vertices mu d column mode offset ≤ 1 := by
  let targets := columnPattern vertices column mode offset
  have mono : forwardWeight (realRecordRelation transcript) vertices mu d targets ≤
      forwardWeight (realRecordRelation (transcript ++ [record])) vertices mu d targets :=
    forward_weight_mono (fun _ m ↦ m) (fun _ m ↦ m) (fun _ _ e ↦ relation_of_append record e)
  exact ⟨sub_nonneg.mpr mono, (sub_le_self _ (forward_weight_range _ _ _ _ _).1).trans
    (forward_weight_range _ _ _ _ _).2⟩

theorem old_row_charge_nonneg (transcript : Transcript n) (vertices : Set (State n))
    (mu d : ℕ) (targets inputs : Set (State n)) (row : Word n) :
    0 ≤ oldRowCharge transcript vertices mu d targets inputs row := by
  unfold oldRowCharge
  split
  · exact normalized_row_nonneg _ _ _ _ _ _
  · rfl

/-- Bound the increment by the reuse indicator, the charged old pattern weight and
the translated input weight, with the two coefficients from weighted convexity. -/
theorem pattern_increment_pointwise : DriftChargeSpec.Pointwise := by
  intro n transcript record vertices mu d column mode offset theta degree pos
  classical
  let oldEdge := realRecordRelation transcript
  let newEdge := realRecordRelation (transcript ++ [record])
  let targets := columnPattern vertices column mode offset
  let inputs := inputPattern transcript record vertices column mode offset
  let alpha := (1 + theta) ^ (d - 1)
  let beta := (1 + theta⁻¹) ^ (d - 1)
  let old := forwardWeight oldEdge vertices mu d targets
  let new := forwardWeight newEdge vertices mu d targets
  let input := forwardWeight oldEdge vertices mu d inputs
  let charge := ∑ row : Word n, oldRowCharge transcript vertices mu d targets inputs row
  have alpha_nonneg : 0 ≤ alpha := by dsimp [alpha]; positivity
  have beta_one : 1 ≤ beta := by
    have base : (1 : ℝ) ≤ 1 + theta⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr pos.le)
    simpa [beta] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) base (d - 1)
  have input_nonneg : 0 ≤ input := (forward_weight_range _ _ _ _ _).1
  have charge_nonneg : 0 ≤ charge :=
    Finset.sum_nonneg fun row _ ↦ old_row_charge_nonneg _ _ _ _ _ _ _
  have range := pattern_increment_range transcript record vertices mu d column mode offset
  change new - old ≤ reuseCharge transcript record vertices column mode offset +
    alpha * oldPatternCharge transcript record vertices mu d column mode offset + beta * input
  -- On reuse, the indicator can pay the entire increase because the weight is capped.
  by_cases reused : ReuseToPattern transcript record vertices column mode offset
  · rw [reuseCharge, ite_eq_left reused]
    have oldChargeNonneg : 0 ≤
        oldPatternCharge transcript record vertices mu d column mode offset := by
      change 0 ≤ if old < 1 then charge else 0
      split
      · exact charge_nonneg
      · rfl
    have addition1 := mul_nonneg alpha_nonneg oldChargeNonneg
    have addition2 := mul_nonneg (zero_le_one.trans beta_one) input_nonneg
    have atMostOne : new - old ≤ 1 := range.2
    linarith
  rw [reuseCharge, ite_eq_right reused, zero_add]
  by_cases openWeight : old < 1
  · rw [oldPatternCharge, ite_eq_left openWeight]
    change new - old ≤ alpha * charge + beta * input
    let oldSum := ∑ row : Word n, normalizedRowWeight oldEdge vertices mu d targets row
    let newSum := ∑ row : Word n, normalizedRowWeight newEdge vertices mu d targets row
    let inputSum := ∑ row : Word n, normalizedRowWeight oldEdge vertices mu d inputs row
    have untruncated : old = oldSum := by
      change min 1 oldSum = oldSum
      by_contra different
      have tooLarge : 1 ≤ oldSum := le_of_not_ge (fun h ↦ different (min_eq_right h))
      have closed : old = 1 := min_eq_left tooLarge
      exact (lt_irrefl _ (closed ▸ openWeight))
    -- A saturated input weight already pays for at most one unit of growth.
    -- Otherwise the uncapped input sum can be combined row by row with the old sum.
    by_cases inputCap : 1 ≤ inputSum
    · have capped : input = 1 := min_eq_left inputCap
      rw [capped, mul_one]
      have addNonneg := mul_nonneg alpha_nonneg charge_nonneg
      have atMostOne : new - old ≤ 1 := range.2
      linarith
    · have inputRaw : input = inputSum := min_eq_right (le_of_not_ge inputCap)
      have perRow (ancestorRow : Word n) :
          normalizedRowWeight newEdge vertices mu d targets ancestorRow ≤
            normalizedRowWeight oldEdge vertices mu d targets ancestorRow +
            alpha * oldRowCharge transcript vertices mu d targets inputs ancestorRow +
            beta * normalizedRowWeight oldEdge vertices mu d inputs ancestorRow := by
        have union_eq : rowAncestorsTo newEdge vertices ancestorRow targets =
            rowAncestorsTo oldEdge vertices ancestorRow targets ∪
              rowAncestorsTo oldEdge vertices ancestorRow inputs :=
          pattern_two_groups transcript record vertices ancestorRow column mode offset reused
        -- A row can gain ancestors only when it reaches some eligible new input.
        -- In that case apply convexity to the two group sizes in the proof of Lemma 4.
        by_cases reached : (rowAncestorsTo oldEdge vertices ancestorRow inputs).Nonempty
        · rw [oldRowCharge, ite_eq_left reached, normalizedRowWeight, union_eq]
          let a : ℝ := (rowAncestorsTo oldEdge vertices ancestorRow targets).ncard
          let b : ℝ := (rowAncestorsTo oldEdge vertices ancestorRow inputs).ncard
          have count : ((rowAncestorsTo oldEdge vertices ancestorRow targets ∪
              rowAncestorsTo oldEdge vertices ancestorRow inputs).ncard : ℝ) ≤ a + b := by
            dsimp [a, b]
            exact_mod_cast Set.ncard_union_le
              (rowAncestorsTo oldEdge vertices ancestorRow targets)
              (rowAncestorsTo oldEdge vertices ancestorRow inputs)
          have powers := pow_le_pow_left₀ (by positivity) count d
          have weighted := Analysis.weighted_convex a b theta d
            (by dsimp [a]; positivity) (by dsimp [b]; positivity) degree pos
          have lifted := div_le_div_of_nonneg_right (powers.trans weighted)
            (by positivity : 0 ≤ (mu : ℝ)^d)
          change _ ≤ a ^ d / ((mu : ℝ)^d) + alpha * (a ^ d / ((mu : ℝ)^d)) +
            beta * (b ^ d / ((mu : ℝ)^d))
          rw [add_div, mul_div_assoc, mul_div_assoc] at lifted
          have extra : 0 ≤ a ^ d / (mu : ℝ)^d := by dsimp [a]; positivity
          exact lifted.trans (by linarith)
        · rw [oldRowCharge, ite_eq_right reached, mul_zero, add_zero]
          have empt : rowAncestorsTo oldEdge vertices ancestorRow inputs = ∅ :=
            Set.not_nonempty_iff_eq_empty.mp reached
          have unchanged : normalizedRowWeight newEdge vertices mu d targets ancestorRow =
              normalizedRowWeight oldEdge vertices mu d targets ancestorRow := by
            simp only [normalizedRowWeight, union_eq, empt, Set.union_empty]
          rw [unchanged]
          exact le_add_of_nonneg_right
            (mul_nonneg (zero_le_one.trans beta_one) (normalized_row_nonneg _ _ _ _ _ _))
      have sums := Finset.sum_le_sum (s := Finset.univ) (fun ancestorRow _ ↦ perRow ancestorRow)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum] at sums
      have summed : newSum ≤ oldSum + alpha * charge + beta * inputSum := sums
      have notAbove : new ≤ newSum := min_le_right _ _
      rw [untruncated, inputRaw]
      linarith
  · rw [oldPatternCharge, ite_eq_right openWeight, mul_zero, zero_add]
    have oldOne : old = 1 := le_antisymm (forward_weight_range _ _ _ _ _).2
        (le_of_not_gt openWeight)
    have nonpositive : new - old ≤ 0 := by
      rw [oldOne]
      exact sub_nonpos.mpr (forward_weight_range _ _ _ _ _).2
    exact nonpositive.trans (mul_nonneg (zero_le_one.trans beta_one) input_nonneg)

/-- The translated charge lies between zero and $B_{\mathrm{ver}}$ and is the difference of the
two potentials on the old residual set. -/
theorem translated_increment_bounded : DriftChargeSpec.BoundedIncrement := by
  intro n transcript record vertices mu d Pi column mode bound
  classical
  let inc := patternIncrement transcript record vertices mu d column mode
  let pairs := endpointPairs (realRecordRelation transcript) vertices record.output.2 column
  let offsets := nonemptySupportOffsets pairs mode
  have range (offset : Word n) : 0 ≤ inc offset ∧ inc offset ≤ 1 :=
    pattern_increment_range transcript record vertices mu d column mode offset
  -- Only offsets with nonempty outlet support can change their pattern weight.
  have sum_le_count : (∑ offset : Word n, inc offset) ≤ (offsets.card : ℝ) := by
    calc
      _ ≤ ∑ offset : Word n, if offset ∈ offsets then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro offset _
        by_cases occurs : offset ∈ offsets
        · rw [ite_eq_left occurs]
          exact (range offset).2
        · rw [ite_eq_right occurs]
          have none : patternOutletSupport transcript vertices record.output.2
              column mode offset = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro supported
            exact occurs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, supported⟩)
          have same (row : Word n) :=
            empty_support_no_growth transcript record vertices row column mode offset none
          have zero : inc offset = 0 := by
            dsimp only [inc, patternIncrement, forwardWeight, normalizedRowWeight]
            simp only [same, sub_self]
          exact zero.le
      _ = _ := by
        rw [← Finset.sum_filter]
        have filter_eq : Finset.univ.filter (fun offset ↦ offset ∈ offsets) = offsets := by
          ext offset
          simp
        rw [filter_eq]
        simp
  refine ⟨div_nonneg (Finset.sum_nonneg fun offset _ ↦ (range offset).1) (by positivity), ?_, ?_⟩
  · by_cases empty : mode.card = 0
    · simp [translatedIncrement, empty]
    have positive : 0 < (mode.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero empty)
    have count_le : offsets.card ≤ mode.card * Pi :=
      (translation_counts pairs mode).2.1.trans (Nat.mul_le_mul_left _ bound)
    have real_le : (offsets.card : ℝ) ≤ (mode.card : ℝ) * Pi := by exact_mod_cast count_le
    apply (div_le_iff₀ positive).2
    rw [mul_comm (Pi : ℝ)]
    exact sum_le_count.trans real_le
  · simp only [translatedIncrement, translatedPotential, patternIncrement, Finset.sum_sub_distrib,
      sub_div]

end JH.Graph
