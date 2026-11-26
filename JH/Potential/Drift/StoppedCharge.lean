/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.Drift.Mean
public import JH.Potential.Drift.StoppedChargeSpec
public import JH.Potential.GraftLedger
public import Mathlib.Tactic.Linarith

/-!
# Charges on the stopped graph replay

Each round with an active old snapshot is charged the add-only potential increase, including
the round that first stops the graph. On a disjoint round this increase bounds ledger growth
after inheritance and grafting. The active bounds from the old snapshot then yield the
conditional means in both directions.
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters
open scoped BigOperators

variable {n : ℕ}

/-- The charge adds the record while holding the residual vertex set fixed. -/
theorem translated_increment_eq_difference (records : Transcript n) (record : Record n)
    (vertices : Set (State n)) (mu d : ℕ) (line : Word n) (mode : Finset (Word n)) :
    translatedIncrement records record vertices mu d line mode =
      translatedPotential (realRecordRelation (records ++ [record])) vertices mu d line mode -
        translatedPotential (realRecordRelation records) vertices mu d line mode := by
  simp only [translatedIncrement, translatedPotential, patternIncrement, Finset.sum_sub_distrib,
    sub_div]

/-- A legal disjoint round increases the ledger by at most its add-only charge.
The singleton-zero mode includes a graft count, paid by point potential. -/
theorem afterGrafting_ledger_le : StoppedChargeSpec.LedgerGrowth := by
  intro params initials snapshot record finish positiveMu positiveD continued direction line mode
  -- The zero singleton needs quantitative payment for counted grafts. For every
  -- other mode, monotonicity under residual deletion suffices.
  obtain ⟨forwardPayment, backwardPayment⟩ :=
    round_graft_payment snapshot.records record params.mu params.d snapshot.sides finish
      positiveMu continued
  obtain ⟨forwardDecrease, backwardDecrease⟩ :=
    round_mode_decrease_after_deletion snapshot.records record params.mu params.d snapshot.sides
      finish continued
  cases direction with
  | forward =>
    have charge_eq :
        GraphTracker.charge params (.active snapshot) record .forward line mode =
          translatedPotential (realRecordRelation (snapshot.records ++ [record]))
              snapshot.sides.realResidual params.mu params.d line mode -
            translatedPotential (realRecordRelation snapshot.records)
              snapshot.sides.realResidual params.mu params.d line mode :=
      translated_increment_eq_difference _ _ _ _ _ _ _
    by_cases singleton : mode = {0}
    · subst mode
      have singleton_eq (edge : State params.n → State params.n → Prop)
          (vertices : Set (State params.n)) :
          pointColumnPotential edge vertices params.mu params.d line =
            translatedPotential edge vertices params.mu params.d line {0} :=
        (singleton_mode_is_point_column edge vertices params.mu params.d line positiveD).symm
      have paid := forwardPayment line
      rw [argumentEdge, pointColumnPotential_induced] at paid
      simp only [singleton_eq] at paid
      simp only [GraphSnapshot.ledger, GraphSnapshot.afterGrafting, ite_true, Nat.cast_add,
        charge_eq]
      linarith only [paid]
    · have decrease := forwardDecrease line mode
      simp only [argumentEdge, translatedPotential_induced] at decrease
      simp only [GraphSnapshot.ledger, GraphSnapshot.afterGrafting, singleton, ite_false, add_zero,
        charge_eq]
      linarith only [decrease]
  | backward =>
    have charge_eq :
        GraphTracker.charge params (.active snapshot) record .backward line mode =
          backwardTranslatedPotential (realRecordRelation (snapshot.records ++ [record]))
              snapshot.sides.realResidual params.mu params.d line mode -
            backwardTranslatedPotential (realRecordRelation snapshot.records)
              snapshot.sides.realResidual params.mu params.d line mode := by
      simp only [GraphTracker.charge, translated_increment_eq_difference,
        backwardTranslatedPotential,
        transposeStateEdge_realRecordRelation, List.map_append, List.map_cons, List.map_nil]
    by_cases singleton : mode = {0}
    · subst mode
      have singleton_eq (edge : State params.n → State params.n → Prop)
          (vertices : Set (State params.n)) :
          backwardPointRowPotential edge vertices params.mu params.d line =
            backwardTranslatedPotential edge vertices params.mu params.d line {0} :=
        (backward_singleton_mode_is_point_row edge vertices params.mu params.d line positiveD).symm
      have paid := backwardPayment line
      rw [argumentEdge, backwardPointRowPotential_induced] at paid
      simp only [singleton_eq] at paid
      simp only [GraphSnapshot.ledger, GraphSnapshot.afterGrafting, ite_true, Nat.cast_add,
        charge_eq]
      linarith only [paid]
    · have decrease := backwardDecrease line mode
      simp only [argumentEdge, backwardTranslatedPotential_induced] at decrease
      simp only [GraphSnapshot.ledger, GraphSnapshot.afterGrafting, singleton, ite_false, add_zero,
        charge_eq]
      linarith only [decrease]

theorem SharesExposedCoordinates.transpose {recordFor : Word n → Record n}
    {inputColumn outputRow : Word n}
      (shares : SharesExposedCoordinates recordFor inputColumn outputRow) :
    SharesExposedCoordinates (fun shift ↦
      transposeRecord (recordFor shift)) outputRow inputColumn := by
  intro shift
  obtain ⟨input, output, shift_eq⟩ := shares shift
  refine ⟨output, input, ?_⟩
  change (recordFor shift).output.1 ^^^ (recordFor shift).input.2 = shift
  rw [BitVec.xor_comm]
  exact shift_eq

theorem EndpointBounds.transpose {records : Transcript n} {vertices : Set (State n)}
    {Pi Theta : ℕ} (bounds : EndpointBounds records vertices Pi Theta) :
    EndpointBounds (records.map transposeRecord) (Prod.swap ⁻¹' vertices) Pi Theta := by
  intro row column
  dsimp only
  rw [← transposed_endpoint_pairs records vertices column row]
  let pairs := endpointPairs (realRecordRelation records) vertices column row
  have left : leftSupport (pairs.image Prod.swap) = rightSupport pairs := by
    simp [leftSupport, rightSupport, Finset.image_image, Function.comp_def]
  have right : rightSupport (pairs.image Prod.swap) = leftSupport pairs := by
    simp [leftSupport, rightSupport, Finset.image_image, Function.comp_def]
  change (leftSupport (pairs.image Prod.swap)).card ≤ Pi ∧
    (rightSupport (pairs.image Prod.swap)).card ≤ Pi ∧ (pairs.image Prod.swap).card ≤ Theta
  rw [left, right, Finset.card_image_of_injective _ Prod.swap_injective]
  exact ⟨(bounds column row).2.1, (bounds column row).1, (bounds column row).2.2⟩

namespace GraphSnapshot

variable (params : Params) {initials : Finset (State params.n)}

/-- The active path-count and graft-threshold invariants give the endpoint bounds. -/
theorem endpoint_bounds (psi : ℕ) (snapshot : GraphSnapshot initials)
    (valid : snapshot.ValidParameters params psi) :
    EndpointBounds snapshot.records snapshot.sides.realResidual params.Pi params.Theta :=
  endpoint_support_bounds (realRecordRelation snapshot.records) snapshot.sides.realResidual
    params.mu params.pi valid.1 valid.2.2.1

private theorem graft_count_nonneg (mode : Finset (Word n)) (grafts : ℕ) :
    (0 : ℝ) ≤ if mode = {0} then (grafts : ℝ) else 0 := by
  split <;> positivity

theorem forward_potential_bound (snapshot : GraphSnapshot initials)
    (below : snapshot.BelowBarrier params) :
    ForwardPotentialBound snapshot.records snapshot.sides.realResidual params.mu params.d params.Pi
      (params.Gamma : ℝ) := by
  intro column mode size
  by_cases nonempty : mode.Nonempty
  · exact (le_add_of_nonneg_right (graft_count_nonneg mode (snapshot.forwardGrafts column))).trans
      (below .forward column mode nonempty size).le
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    simp [translatedPotential]

theorem backward_potential_bound (snapshot : GraphSnapshot initials)
    (below : snapshot.BelowBarrier params) :
    ForwardPotentialBound (snapshot.records.map transposeRecord)
      (Prod.swap ⁻¹' snapshot.sides.realResidual)
      params.mu params.d params.Pi (params.Gamma : ℝ) := by
  intro row mode size
  by_cases nonempty : mode.Nonempty
  · have bound : backwardTranslatedPotential (realRecordRelation snapshot.records)
        snapshot.sides.realResidual params.mu params.d row mode ≤ (params.Gamma : ℝ) :=
      (le_add_of_nonneg_right (graft_count_nonneg mode (snapshot.backwardGrafts row))).trans
        (below .backward row mode nonempty size).le
    simpa only [backwardTranslatedPotential, transposeStateEdge_realRecordRelation] using bound
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    simp [translatedPotential]

end GraphSnapshot

/-- In either direction the charge from an active snapshot lies in $[0,B_{\mathrm{ver}}]$
by Lemma 1 and the pointwise part of Lemma 4. -/
theorem active_charge_range : StoppedChargeSpec.ActiveChargeRange := by
  intro params psi initials snapshot valid record direction line mode
  let vertices := snapshot.sides.realResidual
  have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
  cases direction with
  | forward =>
    have bounded := translated_increment_bounded snapshot.records record vertices
      params.mu params.d params.Pi line mode (bounds record.output.2 line).2.1
    exact ⟨bounded.1, bounded.2.1⟩
  | backward =>
    have bounded := translated_increment_bounded (snapshot.records.map transposeRecord)
      (transposeRecord record) (Prod.swap ⁻¹' vertices) params.mu params.d params.Pi line mode
      (bounds.transpose (transposeRecord record).output.2 line).2.1
    exact ⟨bounded.1, bounded.2.1⟩

/-- For a mode within the size bound, the old active snapshot gives the equal-weight
mean bound over a uniform shift with fixed exposed coordinates. -/
theorem active_charge_mean : StoppedChargeSpec.ActiveChargeMean := by
  intro params psi initials snapshot inputColumn outputRow recordFor positiveD valid shares
    direction line mode size
  let vertices := snapshot.sides.realResidual
  have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
  have gammaNonneg : 0 ≤ (params.Gamma : ℝ) := Nat.cast_nonneg _
  cases direction with
  | forward =>
    have mean := translated_eq_mean snapshot.records vertices params.mu params.d params.Pi
      params.Theta (params.Gamma : ℝ) inputColumn outputRow line mode recordFor positiveD
      gammaNonneg shares bounds
        (GraphSnapshot.forward_potential_bound params snapshot valid.2.1) size
    simpa only [GraphTracker.charge, Params.driftNumerator, Params.N, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] using mean
  | backward =>
    have mean := translated_eq_mean (snapshot.records.map transposeRecord) (Prod.swap ⁻¹' vertices)
      params.mu params.d params.Pi params.Theta (params.Gamma : ℝ) outputRow inputColumn line mode
      (fun shift ↦ transposeRecord (recordFor shift)) positiveD gammaNonneg shares.transpose
      bounds.transpose (GraphSnapshot.backward_potential_bound params snapshot valid.2.1) size
    simpa only [GraphTracker.charge, Params.driftNumerator, Params.N, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat] using mean

/-- The weighted analogue of `active_charge_mean`, with positive convexity weight. -/
theorem active_charge_weighted_mean : StoppedChargeSpec.ActiveChargeWeightedMean := by
  intro params psi initials snapshot inputColumn outputRow recordFor theta positiveD positiveTheta
    valid shares direction line mode size
  let vertices := snapshot.sides.realResidual
  have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
  have gammaNonneg : 0 ≤ (params.Gamma : ℝ) := Nat.cast_nonneg _
  cases direction with
  | forward =>
    have mean := translated_weighted_mean snapshot.records vertices params.mu params.d params.Pi
      params.Theta (params.Gamma : ℝ) theta inputColumn outputRow line mode recordFor positiveD
      gammaNonneg positiveTheta shares bounds
      (GraphSnapshot.forward_potential_bound params snapshot valid.2.1) size
    simpa only [GraphTracker.charge, Params.weightedDriftNumerator, Params.weightedCoefficient,
      Params.N, Nat.cast_pow, Nat.cast_ofNat] using mean
  | backward =>
    have mean := translated_weighted_mean (snapshot.records.map transposeRecord)
      (Prod.swap ⁻¹' vertices) params.mu params.d params.Pi params.Theta (params.Gamma : ℝ)
      theta outputRow inputColumn line mode (fun shift ↦ transposeRecord (recordFor shift))
      positiveD gammaNonneg positiveTheta shares.transpose bounds.transpose
      (GraphSnapshot.backward_potential_bound params snapshot valid.2.1) size
    simpa only [GraphTracker.charge, Params.weightedDriftNumerator, Params.weightedCoefficient,
      Params.N, Nat.cast_pow, Nat.cast_ofNat] using mean

/-- Take the weighted mean of the sum of singleton charges over all lines,
swapping rows and columns for the backward direction. -/
theorem active_total_point_weighted_mean : StoppedChargeSpec.ActiveTotalPointWeightedMean := by
  intro params psi initials snapshot inputColumn outputRow recordFor theta positiveD positiveTheta
    valid shares direction
  let vertices := snapshot.sides.realResidual
  have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
  have gammaNonneg : 0 ≤ (params.Gamma : ℝ) := Nat.cast_nonneg _
  cases direction with
  | forward =>
    have mean := total_point_weighted_mean snapshot.records vertices params.mu params.d params.Pi
      params.Theta (params.Gamma : ℝ) theta inputColumn outputRow recordFor positiveD gammaNonneg
      positiveTheta shares bounds (GraphSnapshot.forward_potential_bound params snapshot valid.2.1)
    simpa only [GraphTracker.charge, Params.weightedCoefficient, Params.N, Nat.cast_pow,
      Nat.cast_ofNat] using mean
  | backward =>
    have mean := total_point_weighted_mean (snapshot.records.map transposeRecord)
      (Prod.swap ⁻¹' vertices) params.mu params.d params.Pi params.Theta (params.Gamma : ℝ)
      theta outputRow inputColumn (fun shift ↦ transposeRecord (recordFor shift)) positiveD
      gammaNonneg positiveTheta shares.transpose bounds.transpose
      (GraphSnapshot.backward_potential_bound params snapshot valid.2.1)
    simpa only [GraphTracker.charge, Params.weightedCoefficient, Params.N, Nat.cast_pow,
      Nat.cast_ofNat, List.length_map] using mean

end JH.Graph
