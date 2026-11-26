/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.BackwardEventsSpec
public import JH.Potential.Drift.MeanSpec

/-!
# Conditional means for boundary growth and intersection

The averaged single-round inheritance and intersection estimates of Section 3.4.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

namespace BoundaryMean

/-- Number of real vertices newly inherited on one line, charged on disjoint rounds. -/
noncomputable def inheritedCount {n : ℕ} {initials : Finset (State n)}
    (transcript : Transcript n) (record : Record n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (side : Direction) (line : Word n) : ℕ := by
  classical
  exact if ∃ finish, RoundStep transcript record threshold before (.continued finish) then
    match side with
    | .forward => (BoundaryEvents.forwardInheritedRates transcript record before line).ncard
    | .backward => (BackwardBoundaryEvents.backwardInheritedCaps transcript
        record before line).ncard
  else 0

end BoundaryMean

namespace BoundaryMeanSpec

open BoundaryEvents (forwardRates backwardCaps)
open BoundaryMean (inheritedCount)

/-- Summed column and row occupancies are bounded by the corresponding old-side populations. -/
def OccupancyTotals : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (before : Boundary (Vertex initials)),
    (∑ column : Word n, (forwardRates before column).ncard) ≤ before.forward.ncard ∧
      (∑ row : Word n, (backwardCaps before row).ncard) ≤ before.backward.ncard

/-- Mean total forward inheritance after exposing the input column and output row. -/
def ForwardInheritanceMean : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow : Word n) (Psi Pi Theta : ℕ)
    (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript before.realResidual Pi Theta →
    (forwardRates before inputColumn).ncard ≤ Psi →
    wordMean (fun shift ↦ ∑ column : Word n,
      (inheritedCount transcript (recordFor shift) threshold before .forward column : ℝ)) ≤
      (1 + (transcript.length : ℝ) * Theta / (2 : ℝ) ^ n) * ((Psi : ℝ) + Pi)

/-- Mean total backward inheritance after exposing the same coordinates. -/
def BackwardInheritanceMean : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn outputRow : Word n) (Psi Pi Theta : ℕ)
    (recordFor : Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript before.realResidual Pi Theta →
    (backwardCaps before outputRow).ncard ≤ Psi →
    wordMean (fun shift ↦ ∑ row : Word n,
      (inheritedCount transcript (recordFor shift) threshold before .backward row : ℝ)) ≤
      (1 + (transcript.length : ℝ) * Theta / (2 : ℝ) ^ n) * ((Psi : ℝ) + Pi)

/-- The forward part of Section 3.4's intersection estimate averages the output row. -/
def ForwardIntersectionMean : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (inputColumn : Word n) (Psi Theta : ℕ)
    (recordFor : Word n → Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects →
    (∀ outputRow, SharesExposedCoordinates (recordFor outputRow) inputColumn outputRow) →
    (∀ row column, (endpointPairs (realRecordRelation transcript)
      before.realResidual row column).card
      ≤ Theta) → (forwardRates before inputColumn).ncard ≤ Psi →
    wordMean (fun outputRow ↦ uniformShiftMass {shift |
      RoundStep transcript (recordFor outputRow shift) threshold before .intersected}) ≤
      (Psi : ℝ) / (2 : ℝ) ^ n * (1 + (transcript.length : ℝ) * Theta / (2 : ℝ) ^ n +
        (before.backward.ncard : ℝ) / (2 : ℝ) ^ n)

/-- The backward part averages the input column and uses the old forward population. -/
def BackwardIntersectionMean : Prop :=
  ∀ {n : ℕ} {initials : Finset (State n)} (transcript : Transcript n) (threshold : ℕ)
    (before : Boundary (Vertex initials)) (outputRow : Word n) (Psi Theta : ℕ)
    (recordFor : Word n → Word n → Record n),
    before.ContainsVirtualStarts → before.Closed (recordRelation transcript initials) →
    ¬ before.Intersects →
    (∀ inputColumn, SharesExposedCoordinates (recordFor inputColumn) inputColumn outputRow) →
    (∀ row column, (endpointPairs (realRecordRelation transcript)
      before.realResidual row column).card
      ≤ Theta) → (backwardCaps before outputRow).ncard ≤ Psi →
    wordMean (fun inputColumn ↦ uniformShiftMass {shift |
      RoundStep transcript (recordFor inputColumn shift) threshold before .intersected}) ≤
      (Psi : ℝ) / (2 : ℝ) ^ n * (1 + (transcript.length : ℝ) * Theta / (2 : ℝ) ^ n +
        (before.forward.ncard : ℝ) / (2 : ℝ) ^ n)

end BoundaryMeanSpec

end JH.Graph
