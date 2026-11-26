/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.BackwardEvents
public import JH.Boundary.ForwardEvents
public import JH.Boundary.MeanSpec
public import JH.Potential.Drift.Mean
public import JH.Potential.Patterns

/-!
# Conditional means for boundary growth and intersection

The mean number of inherited coordinates comes from averaging restricted endpoint supports over
the shift and summing over lines. For intersection, average the shift-probability bound over
the random output row or input column. The resulting bound uses the total size of the opposite
old boundary, as in Section 3.4.
-/

@[expose] public section

namespace JH.Graph.BoundaryMean

open scoped BigOperators
open BoundaryEvents (forwardRates backwardCaps forwardInheritedRates)
open BackwardBoundaryEvents (backwardInheritedCaps)

variable {n : ℕ} {initials : Finset (State n)}

theorem inheritedCount_of_continued {transcript : Transcript n} {record : Record n} {threshold : ℕ}
    {before finish : Boundary (Vertex initials)}
    (continued : RoundStep transcript record threshold before (.continued finish))
    (side : Direction) (line : Word n) :
    inheritedCount transcript record threshold before side line =
      match side with
      | .forward => (forwardInheritedRates transcript record before line).ncard
      | .backward => (backwardInheritedCaps transcript record before line).ncard := by
  have existsFinish : ∃ finish, RoundStep transcript record threshold before (.continued finish) :=
    ⟨finish, continued⟩
  unfold inheritedCount
  rw [ite_eq_left existsFinish]
  cases side <;> rfl

/-- An intersecting round contributes zero to the inheritance count used for
boundary growth on the disjoint branch. -/
theorem inheritedCount_of_intersected {transcript : Transcript n}
    {record : Record n} {threshold : ℕ}
    {before : Boundary (Vertex initials)}
      (stopped : RoundStep transcript record threshold before .intersected)
    (side : Direction) (line : Word n) :
      inheritedCount transcript record threshold before side line = 0 := by
  unfold inheritedCount
  rw [ite_eq_right]
  rintro ⟨_, continued⟩
  exact continued.1 stopped

/-- Summing line occupancies gives at most the size of the corresponding boundary.
On the forward side, different vertices can project to the same coordinates. -/
theorem occupancy_totals : BoundaryMeanSpec.OccupancyTotals := by
  intro n initials before
  let forwardProjection : before.forward → (Σ column : Word n, forwardRates before column) :=
    fun v ↦ ⟨v.val.state.1, ⟨v.val.state.2, v.val, v.property, rfl, rfl⟩⟩
  have onto : Function.Surjective forwardProjection := by
    rintro ⟨column, rate, inColumn⟩
    obtain ⟨vertex, member, columnEq, rateEq⟩ := inColumn
    subst column
    subst rate
    exact ⟨⟨vertex, member⟩, rfl⟩
  let backwardInclusion : (Σ row : Word n, backwardCaps before row) → before.backward :=
    fun position ↦ ⟨Sum.inl (position.2.val, position.1), position.2.property⟩
  have injective : Function.Injective backwardInclusion := by
    rintro ⟨firstRow, firstCap, firstMem⟩ ⟨secondRow, secondCap, secondMem⟩ same
    have samePosition : ((firstCap, firstRow) : State n) = (secondCap, secondRow) :=
      Sum.inl.inj (congrArg Subtype.val same)
    cases samePosition
    rfl
  have forwardBound := Nat.card_le_card_of_surjective forwardProjection onto
  have backwardBound := Nat.card_le_card_of_injective backwardInclusion injective
  rw [Nat.card_sigma] at forwardBound backwardBound
  exact ⟨forwardBound, backwardBound⟩

private theorem ncard_le_card {s : Set (Word n)} {f : Finset (Word n)}
    (subset : s ⊆ (f : Set (Word n))) : s.ncard ≤ f.card := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_mono subset

/-- Average the possible endpoints over all translations, then sum over lines. -/
private theorem inherited_mean_le (pairs : Word n → Finset (Word n × Word n))
    (mode : Finset (Word n)) (limit length Theta : ℕ) (modeBound : mode.card ≤ limit)
    (pairBound : (∑ line : Word n, (pairs line).card) ≤ 2 ^ n + length * Theta) :
    wordMean (fun shift ↦ ∑ line : Word n,
      ((restrictedLeftSupport (pairs line) (xorTranslate shift mode)).card : ℝ)) ≤
      (1 + (length : ℝ) * Theta / (2 : ℝ) ^ n) * (limit : ℝ) := by
  let N : ℝ := (2 : ℝ) ^ n
  have hN : 0 < N := by dsimp [N]; positivity
  have lineBound (line : Word n) :
      wordMean (fun shift ↦
        ((restrictedLeftSupport (pairs line) (xorTranslate shift mode)).card : ℝ)) ≤
        (limit : ℝ) / N * (pairs line).card := by
    have sumBound : (∑ shift : Word n,
        (restrictedLeftSupport (pairs line) (xorTranslate shift mode)).card) ≤
        limit * (pairs line).card :=
      (translation_counts (pairs line) mode).2.2.trans (Nat.mul_le_mul_right _ modeBound)
    unfold wordMean
    rw [div_mul_eq_mul_div, ← Nat.cast_mul, ← Nat.cast_sum]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr sumBound) hN.le
  have total : (∑ line : Word n, ((pairs line).card : ℝ)) ≤ N + (length : ℝ) * Theta := by
    dsimp only [N]
    exact_mod_cast pairBound
  rw [wordMean_sum]
  calc
    _ ≤ ∑ line : Word n, (limit : ℝ) / N * (pairs line).card :=
      Finset.sum_le_sum fun line _ ↦ lineBound line
    _ ≤ (limit : ℝ) / N * (N + (length : ℝ) * Theta) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left total (div_nonneg (Nat.cast_nonneg _) hN.le)
    _ = _ := by
      change (limit : ℝ) / N * (N + (length : ℝ) * Theta) =
        (1 + (length : ℝ) * Theta / N) * (limit : ℝ)
      field_simp

/-- Fix the input column and output row, then average the total number of new
forward-occupied rates over the shift. -/
theorem forward_inheritance_mean : BoundaryMeanSpec.ForwardInheritanceMean := by
  intro n initials transcript threshold before inputColumn outputRow Psi Pi Theta recordFor
    hasStarts closed fixed bounded occupied
  let endpoints := endpointPairs (realRecordRelation transcript) before.realResidual
  let forward := (Set.toFinite (forwardRates before inputColumn)).toFinset
  let mode := forward ∪ rightSupport (endpoints outputRow inputColumn)
  -- Exchange the free coordinates so each translated support counts inherited rates.
  let pairs (column : Word n) := (endpoints outputRow column).image Prod.swap
  have modeBound : mode.card ≤ Psi + Pi := by
    have forwardBound : forward.card ≤ Psi := by
      dsimp only [forward]
      rw [← Set.ncard_eq_toFinset_card]
      exact occupied
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add forwardBound (bounded outputRow inputColumn).2.1)
  have each (column : Word n) : (pairs column).card = (endpoints outputRow column).card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have total : (∑ column : Word n, (pairs column).card) ≤ 2 ^ n + transcript.length * Theta := by
    simp only [each]
    exact (endpoint_total_bounds transcript before.realResidual Theta
      (fun row column ↦ (bounded row column).2.2)).1 outputRow
  have pointwise (shift column : Word n) :
      (inheritedCount transcript (recordFor shift) threshold before .forward column : ℝ) ≤
        ((restrictedLeftSupport (pairs column) (xorTranslate shift mode)).card : ℝ) := by
    by_cases proceeds : ∃ finish,
      RoundStep transcript (recordFor shift) threshold before (.continued finish)
    · obtain ⟨finish, continued⟩ := proceeds
      rw [inheritedCount_of_continued continued]
      change ((forwardInheritedRates transcript (recordFor shift) before column).ncard : ℝ) ≤ _
      apply Nat.cast_le.mpr
      apply ncard_le_card
      intro rate inherited
      obtain ⟨input, output, inInput, pair, shiftEq⟩ := BoundaryEvents.forward_inheritance_witness
        transcript (recordFor shift) threshold before finish column rate
          hasStarts closed continued inherited
      obtain ⟨columnEq, rowEq, fixedShift⟩ := fixed shift
      rw [columnEq, rowEq] at inInput
      rw [rowEq] at pair
      have inputMem : input ∈ mode := by
        rcases inInput with occupiedRate | returnedRate
        · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr occupiedRate)
        · exact Finset.mem_union_right _ returnedRate
      have recover : shift ^^^ output = input := by rw [← fixedShift, ← shiftEq, xor_right_cancel]
      exact mem_restrictedLeftSupport.mpr ⟨output,
        mem_xorTranslate.mpr (recover.symm ▸ inputMem),
        Finset.mem_image.mpr ⟨(output, rate), pair, rfl⟩⟩
    · unfold inheritedCount
      rw [ite_eq_right proceeds, Nat.cast_zero]
      positivity
  refine (wordMean_mono (fun shift ↦ Finset.sum_le_sum (fun column _ ↦
    pointwise shift column))).trans ?_
  simpa only [Nat.cast_add] using inherited_mean_le pairs mode
    (Psi + Pi) transcript.length Theta modeBound total

/-- At fixed exposed coordinates, average the total number of new backward-occupied
capacities over the remaining shift. -/
theorem backward_inheritance_mean : BoundaryMeanSpec.BackwardInheritanceMean := by
  intro n initials transcript threshold before inputColumn outputRow Psi Pi Theta recordFor
    hasStarts closed fixed bounded occupied
  let endpoints := endpointPairs (realRecordRelation transcript) before.realResidual
  let backward := (Set.toFinite (backwardCaps before outputRow)).toFinset
  let mode := backward ∪ leftSupport (endpoints outputRow inputColumn)
  let pairs (row : Word n) := endpoints row inputColumn
  have modeBound : mode.card ≤ Psi + Pi := by
    have backwardBound : backward.card ≤ Psi := by
      dsimp only [backward]
      rw [← Set.ncard_eq_toFinset_card]
      exact occupied
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add backwardBound (bounded outputRow inputColumn).1)
  have total : (∑ row : Word n, (pairs row).card) ≤ 2 ^ n + transcript.length * Theta :=
    (endpoint_total_bounds transcript before.realResidual Theta
      (fun row column ↦ (bounded row column).2.2)).2 inputColumn
  have pointwise (shift row : Word n) :
      (inheritedCount transcript (recordFor shift) threshold before .backward row : ℝ) ≤
        ((restrictedLeftSupport (pairs row) (xorTranslate shift mode)).card : ℝ) := by
    by_cases proceeds : ∃ finish,
      RoundStep transcript (recordFor shift) threshold before (.continued finish)
    · obtain ⟨finish, continued⟩ := proceeds
      rw [inheritedCount_of_continued continued]
      change ((backwardInheritedCaps transcript (recordFor shift) before row).ncard : ℝ) ≤ _
      apply Nat.cast_le.mpr
      apply ncard_le_card
      intro capacity inherited
      obtain ⟨input, output, pair, atOutlet, shiftEq⟩ :=
        BackwardBoundaryEvents.backward_inheritance_witness
        transcript (recordFor shift) threshold before finish row capacity
          hasStarts closed continued inherited
      obtain ⟨columnEq, rowEq, fixedShift⟩ := fixed shift
      rw [columnEq] at pair
      rw [columnEq, rowEq] at atOutlet
      have outputMem : output ∈ mode := by
        rcases atOutlet with occupiedCap | returnedCap
        · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr occupiedCap)
        · exact Finset.mem_union_right _ returnedCap
      have recover : shift ^^^ input = output := by
        rw [← fixedShift, ← shiftEq, BitVec.xor_comm input output, xor_right_cancel]
      exact mem_restrictedLeftSupport.mpr
        ⟨input, mem_xorTranslate.mpr (recover.symm ▸ outputMem), pair⟩
    · unfold inheritedCount
      rw [ite_eq_right proceeds, Nat.cast_zero]
      positivity
  refine (wordMean_mono (fun shift ↦
    Finset.sum_le_sum (fun row _ ↦ pointwise shift row))).trans ?_
  simpa only [Nat.cast_add] using inherited_mean_le pairs mode
    (Psi + Pi) transcript.length Theta modeBound total

private theorem intersection_mean_le {f : Word n → ℝ} (occupancy support : Word n → ℕ)
    (Psi length Theta population : ℕ)
    (localBound : ∀ word, f word ≤ (Psi : ℝ) *
      ((occupancy word + support word : ℕ) : ℝ) / (2 : ℝ) ^ n)
    (totalOccupancy : (∑ word : Word n, occupancy word) ≤ population)
    (totalSupport : (∑ word : Word n, support word) ≤ 2 ^ n + length * Theta) :
    wordMean f ≤ (Psi : ℝ) / (2 : ℝ) ^ n *
      (1 + (length : ℝ) * Theta / (2 : ℝ) ^ n + (population : ℝ) / (2 : ℝ) ^ n) := by
  let N : ℝ := (2 : ℝ) ^ n
  have hN : 0 < N := by dsimp [N]; positivity
  let count (word : Word n) : ℝ := ((occupancy word + support word : ℕ) : ℝ)
  have scaled : wordMean f ≤ wordMean (fun word ↦ (Psi : ℝ) / N * count word) := by
    apply wordMean_mono
    intro word
    rw [div_mul_eq_mul_div]
    exact localBound word
  -- Separate the sum into old occupied coordinates and residual return candidates.
  have total : (∑ word : Word n, (occupancy word + support word)) ≤
      population + (2 ^ n + length * Theta) := by
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add totalOccupancy totalSupport
  have totalReal : (∑ word : Word n, count word) ≤ (population : ℝ) +
      (N + (length : ℝ) * Theta) := by
    dsimp only [count, N]
    exact_mod_cast total
  have average : wordMean count ≤ 1 + (length : ℝ) * Theta / N + (population : ℝ) / N := by
    calc
      _ ≤ ((population : ℝ) + (N + (length : ℝ) * Theta)) / N :=
        div_le_div_of_nonneg_right totalReal hN.le
      _ = _ := by
        field_simp
        ring
  rw [wordMean_mul] at scaled
  exact scaled.trans (mul_le_mul_of_nonneg_left average (div_nonneg (Nat.cast_nonneg _) hN.le))

/-- Average the forward intersection bound over the uniform output row. The mean
uses the old backward population and the total return support. -/
theorem forward_intersection_mean : BoundaryMeanSpec.ForwardIntersectionMean := by
  intro n initials transcript threshold before inputColumn Psi Theta recordFor
    hasStarts closed disjoint fixed pairBound occupied
  let pairs (row : Word n) :=
    endpointPairs (realRecordRelation transcript) before.realResidual row inputColumn
  refine intersection_mean_le (fun row ↦ (backwardCaps before row).ncard) (fun row ↦
    (leftSupport (pairs row)).card)
    Psi transcript.length Theta before.backward.ncard ?_ (occupancy_totals before).2 ?_
  · intro row
    exact BoundaryEvents.forward_intersection_probability transcript threshold
      before inputColumn row Psi
      (recordFor row) hasStarts closed disjoint (fixed row) occupied
  · exact (Finset.sum_le_sum (fun row _ ↦
      Finset.card_image_le (f := Prod.fst) (s := pairs row))).trans
      ((endpoint_total_bounds transcript before.realResidual Theta pairBound).2 inputColumn)

/-- Average the backward bound over the uniform input column, using the old forward
population and the total return support. -/
theorem backward_intersection_mean : BoundaryMeanSpec.BackwardIntersectionMean := by
  intro n initials transcript threshold before outputRow Psi Theta recordFor
    hasStarts closed disjoint fixed pairBound occupied
  let pairs (column : Word n) :=
    endpointPairs (realRecordRelation transcript) before.realResidual outputRow column
  refine intersection_mean_le (fun column ↦ (forwardRates before column).ncard)
    (fun column ↦ (rightSupport (pairs column)).card)
      Psi transcript.length Theta before.forward.ncard
    ?_ (occupancy_totals before).1 ?_
  · intro column
    exact BackwardBoundaryEvents.backward_intersection_probability transcript
      threshold before column outputRow Psi
      (recordFor column) hasStarts closed disjoint (fixed column) occupied
  · exact (Finset.sum_le_sum (fun column _ ↦
      Finset.card_image_le (f := Prod.snd) (s := pairs column))).trans
      ((endpoint_total_bounds transcript before.realResidual Theta pairBound).1 outputRow)

end JH.Graph.BoundaryMean
