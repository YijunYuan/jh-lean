/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.ConvexSpec
public import JH.Potential.Drift.ChargeSpec

/-!
# Conditional mean of the translated charge

Conditional mean bounds for the translated charge.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

/-- Conditional mean over the uniform word after the other coordinate is exposed. -/
noncomputable def wordMean (f : Word n → ℝ) : ℝ :=
  (∑ word : Word n, f word) / (2 : ℝ) ^ n

/-- The three simultaneous old-residual endpoint bounds in Lemma 1. -/
def EndpointBounds (transcript : Transcript n) (vertices : Set (State n)) (Pi Theta : ℕ) : Prop :=
  ∀ row column,
    let pairs := endpointPairs (realRecordRelation transcript) vertices row column
    (leftSupport pairs).card ≤ Pi ∧ (rightSupport pairs).card ≤ Pi ∧ pairs.card ≤ Theta

/-- Every forward translated potential with pattern size at most Bver is bounded by Bpot. -/
def ForwardPotentialBound (transcript : Transcript n) (vertices : Set (State n))
    (mu d Pi : ℕ) (Gamma : ℝ) : Prop :=
  ∀ column (mode : Finset (Word n)), mode.card ≤ Pi →
    translatedPotential (realRecordRelation transcript) vertices mu d column mode ≤ Gamma

namespace DriftMeanSpec

/-- The terms of the one-record charge in Lemma 4 at one fixed translate, retaining the actual
left support. -/
def PatternParts : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (mu d Pi Theta : ℕ)
    (inputColumn outputRow column : Word n) (mode : Finset (Word n)) (offset : Word n)
    (recordFor : Word n → Record n), 0 < d →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript vertices Pi Theta →
      let support := patternOutletSupport transcript vertices outputRow column mode offset
      let old := forwardWeight (realRecordRelation transcript) vertices mu d
        (columnPattern vertices column mode offset)
      wordMean (fun shift ↦ reuseCharge transcript (recordFor shift) vertices column mode offset) ≤
        (Pi : ℝ) * support.card / (2 : ℝ) ^ n ∧
      wordMean (fun shift ↦ oldPatternCharge transcript (recordFor shift)
        vertices mu d column mode offset) ≤ (Pi : ℝ) * support.card / (2 : ℝ) ^ n * old ∧
      wordMean (fun shift ↦ forwardWeight (realRecordRelation transcript) vertices mu d
        (inputPattern transcript (recordFor shift) vertices column mode offset)) =
        (support.card : ℝ) / (2 : ℝ) ^ n *
          translatedPotential (realRecordRelation transcript) vertices mu d inputColumn support

/-- The conditional mean in (19) before inheritance and grafting. -/
def EqualMean : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (mu d Pi Theta : ℕ)
    (Gamma : ℝ) (inputColumn outputRow column : Word n) (mode : Finset (Word n))
    (recordFor : Word n → Record n), 0 < d → 0 ≤ Gamma →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript vertices Pi Theta →
    ForwardPotentialBound transcript vertices mu d Pi Gamma → mode.card ≤ Pi →
      wordMean (fun shift ↦ translatedIncrement transcript (recordFor shift) vertices
        mu d column mode) ≤
      ((2 : ℝ) ^ (d - 1) * Gamma * ((Pi : ℝ) ^ 2 + (Theta : ℝ)) + (Pi : ℝ) * Theta) /
        (2 : ℝ) ^ n

/-- Equation (A.3), with the same potential and increment as in (19). -/
def WeightedMean : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (mu d Pi Theta : ℕ)
    (Gamma theta : ℝ) (inputColumn outputRow column : Word n) (mode : Finset (Word n))
    (recordFor : Word n → Record n), 0 < d → 0 ≤ Gamma → 0 < theta →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript vertices Pi Theta →
    ForwardPotentialBound transcript vertices mu d Pi Gamma → mode.card ≤ Pi →
      wordMean (fun shift ↦ translatedIncrement transcript (recordFor shift) vertices
        mu d column mode) ≤
      (Theta : ℝ) * (Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ)) / (2 : ℝ) ^ n

/-- The sum of the actual single-point increments, used to count grafted vertices in Section
3.4. For θ = 1 the coefficient is 2^(d−1)(Bver + Bpot), as in (A.2). -/
def WeightedTotalPointMean : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n)) (mu d Pi Theta : ℕ)
    (Gamma theta : ℝ) (inputColumn outputRow : Word n) (recordFor : Word n → Record n),
    0 < d → 0 ≤ Gamma → 0 < theta →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    EndpointBounds transcript vertices Pi Theta →
    ForwardPotentialBound transcript vertices mu d Pi Gamma →
      wordMean (fun shift ↦ ∑ column : Word n, translatedIncrement transcript (recordFor shift)
        vertices mu d column {0}) ≤
      (1 + (transcript.length : ℝ) * Theta / (2 : ℝ) ^ n) *
        (Analysis.weightedCost (Pi : ℝ) Gamma d theta + (Pi : ℝ))

end DriftMeanSpec

end JH.Graph
