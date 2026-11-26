/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.Endpoints
public import JH.Potential.Drift.Charge
public import JH.Potential.Drift.MeanSpec

/-!
# Conditional mean of the translated charge

Keep the old transcript and the new record's input column and output row fixed. Average the
three pointwise charge terms over the remaining uniform shift, then sum over target-pattern
offsets using the translation count. This gives the equal-weight and weighted single-round
bounds and the weighted sum over singleton modes.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

theorem wordMean_mono {f g : Word n → ℝ} (h : ∀ word, f word ≤ g word) :
    wordMean f ≤ wordMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun word _ ↦ h word) (by positivity)

theorem wordMean_sum {ι : Type*} [Fintype ι] (f : Word n → ι → ℝ) :
    wordMean (fun word ↦ ∑ i, f word i) = ∑ i, wordMean (fun word ↦ f word i) := by
  unfold wordMean
  rw [← Finset.sum_div, Finset.sum_comm]

theorem wordMean_add (f g : Word n → ℝ) :
    wordMean (fun word ↦ f word + g word) = wordMean f + wordMean g := by
  simp only [wordMean, Finset.sum_add_distrib, add_div]

theorem wordMean_mul (f : Word n → ℝ) (c : ℝ) :
    wordMean (fun word ↦ c * f word) = c * wordMean f := by
  simp only [wordMean, ← Finset.mul_sum, mul_div_assoc]

theorem wordMean_indicator (event : Set (Word n)) (c : ℝ) [DecidablePred (· ∈ event)] :
    wordMean (fun word ↦ if word ∈ event then c else 0) = uniformShiftMass event * c := by
  classical
  let support := Finset.univ.filter fun word ↦ word ∈ event
  have hset : (support : Set (Word n)) = event := by
    ext word
    simp [support]
  have hcard : support.card = event.ncard := by rw [← hset, Set.ncard_coe_finset]
  rw [wordMean, ← Finset.sum_filter]
  change (∑ _ ∈ support, c) / (2 : ℝ) ^ n = _
  rw [Finset.sum_const, nsmul_eq_mul, hcard, uniform_shift_mass_card]
  ring

private theorem pattern_support_le (transcript : Transcript n) (vertices : Set (State n))
    (Pi Theta : ℕ) (outputRow column : Word n) (mode : Finset (Word n)) (offset : Word n)
    (bounds : EndpointBounds transcript vertices Pi Theta) :
    (patternOutletSupport transcript vertices outputRow column mode offset).card ≤ Pi :=
  ((translation_counts _ mode).1 offset).trans (bounds outputRow column).1

/-- Compute shift means for the reuse, charged old pattern and new input terms.
Equation (17) gives the new input term as a scaled translated potential in the input column. -/
theorem pattern_charge_means : DriftMeanSpec.PatternParts := by
  intro n transcript vertices mu d Pi Theta inputColumn outputRow column mode offset recordFor
    hd fixed bounds
  classical
  let support := patternOutletSupport transcript vertices outputRow column mode offset
  let edge := realRecordRelation transcript
  let targets := columnPattern vertices column mode offset
  let old := forwardWeight edge vertices mu d targets
  let N : ℝ := (2 : ℝ) ^ n
  let rate := (Pi : ℝ) * support.card / N
  have hrate : 0 ≤ rate := by dsimp [rate, N]; positivity
  have hright (row : Word n) : (rightSupport (endpointPairs edge vertices row inputColumn)).card
      ≤ Pi := (bounds row inputColumn).2.1
  have scale (row : Word n) :
      (rightSupport (endpointPairs edge vertices row inputColumn)).card *
        (support.card : ℝ) / N ≤ rate :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hright row)) (by positivity)) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · change wordMean (fun shift ↦ reuseCharge transcript (recordFor shift) vertices column
      mode offset) ≤ rate
    let event : Set (Word n) := {shift |
      ReuseToPattern transcript (recordFor shift) vertices column mode offset}
    have hmean : wordMean (fun shift ↦ reuseCharge transcript (recordFor shift) vertices column
        mode offset) = uniformShiftMass event := by
      simpa only [event, reuseCharge, Set.mem_ofPred_eq, mul_one] using wordMean_indicator event 1
    rw [hmean]
    exact (reuse_probability transcript vertices inputColumn outputRow column mode offset
      recordFor fixed).trans (scale outputRow)
  · change wordMean (fun shift ↦ if old < 1 then
      ∑ row, oldRowCharge transcript vertices mu d targets
        (inputPattern transcript (recordFor shift) vertices column mode offset) row
      else 0) ≤ rate * old
    have holdNonneg : 0 ≤ old := (forward_weight_range _ _ _ _ _).1
    by_cases unsaturated : old < 1
    · let normalized := normalizedRowWeight edge vertices mu d targets
      have hraw : (∑ row, normalized row) = old := by
        change min 1 (∑ row, normalized row) < 1 at unsaturated
        change _ = min 1 (∑ row, normalized row)
        exact (min_eq_right (le_of_lt ((min_lt_iff.mp unsaturated).resolve_left
          (lt_irrefl 1)))).symm
      -- With the old weight below its cap, the old term sums row weights. A row is
      -- charged only on shifts that give it an old path to a new input.
      have hrow (row : Word n) :
          wordMean (fun shift ↦ oldRowCharge transcript vertices mu d targets
            (inputPattern transcript (recordFor shift) vertices column mode offset) row) ≤
          rate * normalized row := by
        let event : Set (Word n) := {shift |
          (rowAncestorsTo edge vertices row
            (inputPattern transcript (recordFor shift) vertices column mode offset)).Nonempty}
        have hmean : wordMean (fun shift ↦ oldRowCharge transcript vertices mu d targets
            (inputPattern transcript (recordFor shift) vertices column mode offset) row) =
            uniformShiftMass event * normalized row := wordMean_indicator event _
        rw [hmean]
        exact mul_le_mul_of_nonneg_right
          ((ancestor_row_probability transcript vertices inputColumn outputRow row column mode
            offset recordFor fixed).trans (scale row)) (normalized_row_nonneg _ _ _ _ _ _)
      simp only [ite_eq_left unsaturated]
      rw [wordMean_sum]
      calc
        _ ≤ ∑ row, rate * normalized row := Finset.sum_le_sum fun row _ ↦ hrow row
        _ = _ := by rw [← Finset.mul_sum, hraw]
    · simp only [ite_eq_right unsaturated, wordMean, Finset.sum_const_zero, zero_div]
      exact mul_nonneg hrate holdNonneg
  · change wordMean (fun shift ↦ forwardWeight edge vertices mu d
      (inputPattern transcript (recordFor shift) vertices column mode offset)) =
      (support.card : ℝ) / N *
        translatedPotential edge vertices mu d inputColumn support
    -- The outlet support is fixed here. Varying the shift translates this same support
    -- through the input column, as in the definition of translated potential.
    have hinput (shift : Word n) :
        inputPattern transcript (recordFor shift) vertices column mode offset =
          columnPattern vertices inputColumn support shift := by
      simp only [inputPattern, support, patternOutletSupport,
        (fixed shift).1, (fixed shift).2.1, (fixed shift).2.2]
    simp only [wordMean, hinput, translatedPotential]
    by_cases empty : support.card = 0
    · have noSupport := Finset.card_eq_zero.mp empty
      have hzero (shift : Word n) :
          forwardWeight edge vertices mu d
            (columnPattern vertices inputColumn support shift) = 0 := by
        have hempty : columnPattern vertices inputColumn support shift = ∅ := by
          ext state
          simp [columnPattern, xorTranslate, noSupport]
        rw [hempty]
        exact forward_weight_empty hd
      simp only [empty, Nat.cast_zero, hzero, Finset.sum_const_zero, zero_div, zero_mul]
    · have hne : (support.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr empty
      dsimp only [N]
      field_simp [hne]

private theorem pattern_increment_mean (transcript : Transcript n) (vertices : Set (State n))
    (mu d Pi Theta : ℕ) (Gamma theta : ℝ) (inputColumn outputRow column : Word n)
    (mode : Finset (Word n)) (offset : Word n) (recordFor : Word n → Record n)
    (hd : 0 < d) (htheta : 0 < theta) (fixed : SharesExposedCoordinates recordFor inputColumn
      outputRow) (bounds : EndpointBounds transcript vertices Pi Theta)
    (active : ForwardPotentialBound transcript vertices mu d Pi Gamma) :
    let support := patternOutletSupport transcript vertices outputRow column mode offset
    let old := forwardWeight (realRecordRelation transcript) vertices mu d
      (columnPattern vertices column mode offset)
    wordMean (fun shift ↦ patternIncrement transcript (recordFor shift) vertices mu d column
      mode offset) ≤
      (Pi : ℝ) * support.card / (2 : ℝ) ^ n +
      (1 + theta) ^ (d - 1) * ((Pi : ℝ) * support.card / (2 : ℝ) ^ n * old) +
      (1 + theta⁻¹) ^ (d - 1) * ((support.card : ℝ) / (2 : ℝ) ^ n * Gamma) := by
  dsimp only
  obtain ⟨reuse, old, input⟩ := pattern_charge_means transcript vertices mu d Pi Theta inputColumn
    outputRow column mode offset recordFor hd fixed bounds
  let support := patternOutletSupport transcript vertices outputRow column mode offset
  let A := (1 + theta) ^ (d - 1)
  let B := (1 + theta⁻¹) ^ (d - 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hInput :
      wordMean (fun shift ↦ forwardWeight (realRecordRelation transcript) vertices mu d
        (inputPattern transcript (recordFor shift) vertices column mode offset)) ≤
        (support.card : ℝ) / (2 : ℝ) ^ n * Gamma := by
    rw [input]
    exact mul_le_mul_of_nonneg_left
      (active inputColumn support (pattern_support_le _ _ _ _ _ _ _ _ bounds)) (by positivity)
  have hp := wordMean_mono (fun shift ↦ pattern_increment_pointwise transcript (recordFor shift)
    vertices mu d column mode offset theta hd htheta)
  rw [wordMean_add, wordMean_add, wordMean_mul, wordMean_mul] at hp
  exact hp.trans (add_le_add (add_le_add reuse (mul_le_mul_of_nonneg_left old hA))
    (mul_le_mul_of_nonneg_left hInput hB))

private theorem translated_mean_le (transcript : Transcript n) (vertices : Set (State n))
    (mu d : ℕ) (outputRow column : Word n) (mode : Finset (Word n))
    (recordFor : Word n → Record n) (a b : ℝ) (ha : 0 ≤ a)
    (each : ∀ offset, wordMean (fun shift ↦ patternIncrement transcript (recordFor shift)
      vertices mu d column mode offset) ≤
      a * (patternOutletSupport transcript vertices outputRow column mode offset).card +
        b * forwardWeight (realRecordRelation transcript) vertices mu d
          (columnPattern vertices column mode offset)) :
    wordMean (fun shift ↦ translatedIncrement transcript (recordFor shift) vertices mu d
      column mode) ≤
      a * (endpointPairs (realRecordRelation transcript) vertices outputRow column).card +
      b * translatedPotential (realRecordRelation transcript) vertices mu d column mode := by
  classical
  let pairs := endpointPairs (realRecordRelation transcript) vertices outputRow column
  let outlets := fun offset ↦ (patternOutletSupport transcript vertices outputRow
    column mode offset).card
  let weight := fun offset ↦ forwardWeight (realRecordRelation transcript) vertices mu d
    (columnPattern vertices column mode offset)
  by_cases empty : mode.card = 0
  · simp only [translatedIncrement, translatedPotential, empty, Nat.cast_zero, div_zero,
      wordMean, Finset.sum_const_zero, mul_zero, add_zero]
    rw [zero_div]
    exact mul_nonneg ha (by positivity)
  have hcard : 0 < (mode.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero empty)
  -- The incidence bound removes the mode-size factor when summing over offsets.
  have hsum : (∑ offset, (outlets offset : ℝ)) / mode.card ≤ (pairs.card : ℝ) := by
    apply (div_le_iff₀ hcard).2
    rw [mul_comm]
    exact_mod_cast (translation_counts pairs mode).2.2
  have hcommute : wordMean (fun shift ↦ translatedIncrement transcript (recordFor shift)
      vertices mu d column mode) =
      (∑ offset, wordMean (fun shift ↦ patternIncrement transcript (recordFor shift)
        vertices mu d column mode offset)) / mode.card := by
    simp only [translatedIncrement, div_eq_inv_mul, wordMean_mul, wordMean_sum]
  rw [hcommute]
  have hs := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.univ) (fun offset _ ↦ each offset)) hcard.le
  refine hs.trans ?_
  change (∑ offset : Word n, (a * (outlets offset : ℝ) + b * weight offset)) / mode.card ≤
    a * (pairs.card : ℝ) + b * ((∑ offset, weight offset) / mode.card)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, add_div, mul_div_assoc,
    mul_div_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left hsum ha) le_rfl

/-- The equal-weight drift bound combines the mean charges and the active potential cap. -/
theorem translated_eq_mean : DriftMeanSpec.EqualMean := by
  intro n transcript vertices mu d Pi Theta Gamma inputColumn outputRow column mode recordFor
    hd hGamma fixed bounds active hmode
  let N : ℝ := (2 : ℝ) ^ n
  let A : ℝ := 2 ^ (d - 1)
  let a : ℝ := ((Pi : ℝ) + A * Gamma) / N
  let b : ℝ := A * (Pi : ℝ) ^ 2 / N
  have ha : 0 ≤ a := by dsimp [a, A, N]; positivity
  have hb : 0 ≤ b := by dsimp [b, A, N]; positivity
  have each (offset : Word n) :
      wordMean (fun shift ↦ patternIncrement transcript (recordFor shift) vertices mu d column
        mode offset) ≤
      a * (patternOutletSupport transcript vertices outputRow column mode offset).card +
      b * forwardWeight (realRecordRelation transcript) vertices mu d
        (columnPattern vertices column mode offset) := by
    let l := (patternOutletSupport transcript vertices outputRow column mode offset).card
    let w := forwardWeight (realRecordRelation transcript) vertices mu d
      (columnPattern vertices column mode offset)
    have hw : 0 ≤ w := (forward_weight_range _ _ _ _ _).1
    have hl : (l : ℝ) ≤ (Pi : ℝ) := by
      exact_mod_cast pattern_support_le _ _ _ _ _ _ _ offset bounds
    have main := pattern_increment_mean transcript vertices mu d Pi Theta Gamma 1 inputColumn
      outputRow column mode offset recordFor hd (by norm_num) fixed bounds active
    have hmain : wordMean (fun shift ↦ patternIncrement transcript (recordFor shift) vertices
        mu d column mode offset) ≤
        (Pi : ℝ) * l / N + A * ((Pi : ℝ) * l / N * w) + A * ((l : ℝ) / N * Gamma) := by
      simpa only [inv_one, show (1 : ℝ) + 1 = 2 by norm_num] using main
    change _ ≤ a * (l : ℝ) + b * w
    calc
      _ ≤ (Pi : ℝ) * l / N + A * ((Pi : ℝ) * l / N * w) + A * ((l : ℝ) / N * Gamma) := hmain
      _ ≤ (Pi : ℝ) * l / N + A * ((Pi : ℝ) * Pi / N * w) + A * ((l : ℝ) / N * Gamma) := by
        gcongr
      _ = _ := by dsimp [a, b]; ring
  calc
    _ ≤ a * (endpointPairs (realRecordRelation transcript) vertices outputRow column).card +
        b * translatedPotential (realRecordRelation transcript) vertices mu d column mode :=
      translated_mean_le transcript vertices mu d outputRow column mode recordFor a b ha each
    _ ≤ a * Theta + b * Gamma :=
      add_le_add (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (bounds outputRow column).2.2) ha)
        (mul_le_mul_of_nonneg_left (active column mode hmode) hb)
    _ = _ := by dsimp [a, b, A, N]; ring

private theorem weighted_column_mean (transcript : Transcript n) (vertices : Set (State n))
    (mu d Pi Theta : ℕ) (Gamma theta : ℝ) (inputColumn outputRow column : Word n)
    (mode : Finset (Word n)) (recordFor : Word n → Record n)
    (hd : 0 < d) (hGamma : 0 ≤ Gamma) (htheta : 0 < theta)
    (fixed : SharesExposedCoordinates recordFor inputColumn outputRow)
    (bounds : EndpointBounds transcript vertices Pi Theta)
    (active : ForwardPotentialBound transcript vertices mu d Pi Gamma) :
    wordMean (fun shift ↦ translatedIncrement transcript (recordFor shift) vertices
      mu d column mode) ≤
    ((Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ)) / (2 : ℝ) ^ n) *
      (endpointPairs (realRecordRelation transcript) vertices outputRow column).card := by
  let N : ℝ := (2 : ℝ) ^ n
  let A := (1 + theta) ^ (d - 1)
  let B := (1 + theta⁻¹) ^ (d - 1)
  let a := (Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ)) / N
  have ha : 0 ≤ a := by dsimp [a, Analysis.weightedCost, N]; positivity
  have each (offset : Word n) :
      wordMean (fun shift ↦ patternIncrement transcript (recordFor shift) vertices mu d column
        mode offset) ≤
      a * (patternOutletSupport transcript vertices outputRow column mode offset).card +
      0 * forwardWeight (realRecordRelation transcript) vertices mu d
        (columnPattern vertices column mode offset) := by
    let l := (patternOutletSupport transcript vertices outputRow column mode offset).card
    let w := forwardWeight (realRecordRelation transcript) vertices mu d
      (columnPattern vertices column mode offset)
    -- The weighted form uses the pointwise cap on the old weight. Its column-wise
    -- bound is proportional to the actual endpoint count, which can then be summed.
    have hw : w ≤ 1 := (forward_weight_range _ _ _ _ _).2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hl : 0 ≤ (Pi : ℝ) * l / N := by dsimp [N]; positivity
    change _ ≤ a * (l : ℝ) + 0 * w
    calc
      _ ≤ (Pi : ℝ) * l / N + A * ((Pi : ℝ) * l / N * w) + B * ((l : ℝ) / N * Gamma) :=
        pattern_increment_mean transcript vertices mu d Pi Theta Gamma theta inputColumn outputRow
          column mode offset recordFor hd htheta fixed bounds active
      _ ≤ (Pi : ℝ) * l / N + A * ((Pi : ℝ) * l / N * 1) + B * ((l : ℝ) / N * Gamma) := by
        gcongr
      _ = _ := by dsimp [a, A, B, Analysis.weightedCost]; ring
  simpa only [zero_mul, add_zero] using
    translated_mean_le transcript vertices mu d outputRow column mode recordFor a 0 ha each

/-- Bound the mean charge for one translated mode using weighted convexity and
the endpoint pair bound. -/
theorem translated_weighted_mean : DriftMeanSpec.WeightedMean := by
  intro n transcript vertices mu d Pi Theta Gamma theta inputColumn outputRow column mode recordFor
    hd hGamma htheta fixed bounds active _
  let a := (Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ)) / (2 : ℝ) ^ n
  have ha : 0 ≤ a := by dsimp [a, Analysis.weightedCost]; positivity
  calc
    _ ≤ a * (endpointPairs (realRecordRelation transcript) vertices outputRow column).card :=
      weighted_column_mean transcript vertices mu d Pi Theta Gamma theta inputColumn outputRow
        column mode recordFor hd hGamma htheta fixed bounds active
    _ ≤ a * (Theta : ℝ) := mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (bounds outputRow column).2.2) ha
    _ = _ := by dsimp [a]; ring

/-- Sum the weighted charge over all singleton-zero modes, using the total row
endpoint bound to control the sum over columns. -/
theorem total_point_weighted_mean : DriftMeanSpec.WeightedTotalPointMean := by
  intro n transcript vertices mu d Pi Theta Gamma theta inputColumn outputRow recordFor
    hd hGamma htheta fixed bounds active
  let cost := Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ)
  let N : ℝ := (2 : ℝ) ^ n
  let pairs := fun column ↦ endpointPairs (realRecordRelation transcript) vertices outputRow column
  have ht : (∑ column, (pairs column).card) ≤ 2 ^ n + transcript.length * Theta :=
    (endpoint_total_bounds transcript vertices Theta (fun row column ↦
      (bounds row column).2.2)).1 outputRow
  have htr : (∑ column, ((pairs column).card : ℝ)) ≤ N + (transcript.length : ℝ) * Theta := by
    dsimp only [N]
    exact_mod_cast ht
  have hcost : 0 ≤ cost / N := by dsimp [cost, N, Analysis.weightedCost]; positivity
  rw [wordMean_sum]
  calc
    _ ≤ ∑ column, (cost / N) * (pairs column).card :=
      Finset.sum_le_sum (fun column _ ↦ weighted_column_mean transcript vertices mu d Pi Theta
        Gamma theta inputColumn outputRow column {0} recordFor hd hGamma htheta fixed bounds active)
    _ ≤ (cost / N) * (N + (transcript.length : ℝ) * Theta) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left htr hcost
    _ = _ := by
      have hN : N ≠ 0 := by dsimp [N]; positivity
      change cost / N * (N + (transcript.length : ℝ) * Theta) =
        (1 + (transcript.length : ℝ) * Theta / N) * cost
      field_simp

end JH.Graph
