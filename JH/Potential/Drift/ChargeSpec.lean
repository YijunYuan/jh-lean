/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.Drift.EventsSpec
public import JH.Potential.WeightsSpec

/-!
# Pointwise charges for potential growth

Pointwise upper bounds on the increase in graph potential.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

/-- Change in the weight of a fixed translate when a record is added on the old residual set. -/
noncomputable def patternIncrement (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n)
    (mode : Finset (Word n)) (offset : Word n) : ℝ :=
  let targets := columnPattern vertices column mode offset
  forwardWeight (realRecordRelation (transcript ++ [record])) vertices mu d targets -
    forwardWeight (realRecordRelation transcript) vertices mu d targets

/-- Sum of the weight increments over all offsets, normalized by the pattern size as in (16). -/
noncomputable def translatedIncrement (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n) (mode : Finset (Word n)) : ℝ :=
  (∑ offset : Word n, patternIncrement transcript record vertices mu d column mode offset) /
    mode.card

/-- Unit charge when a walk to this translate uses the new record more than once. -/
noncomputable def reuseCharge (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (column : Word n) (mode : Finset (Word n))
      (offset : Word n) : ℝ := by
  classical
  exact if ReuseToPattern transcript record vertices column mode offset then 1 else 0

/-- Old target weight in a row that can reach an eligible input, and zero otherwise. -/
noncomputable def oldRowCharge (transcript : Transcript n) (vertices : Set (State n))
    (mu d : ℕ) (targets inputs : Set (State n)) (row : Word n) : ℝ := by
  classical
  exact if (rowAncestorsTo (realRecordRelation transcript) vertices row inputs).Nonempty
    then normalizedRowWeight (realRecordRelation transcript) vertices mu d targets row else 0

/-- Contribution of the old row weights to the charge for this translate in Lemma 4. -/
noncomputable def oldPatternCharge (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n)
    (mode : Finset (Word n)) (offset : Word n) : ℝ := by
  classical
  let targets := columnPattern vertices column mode offset
  let inputs := inputPattern transcript record vertices column mode offset
  exact if forwardWeight (realRecordRelation transcript) vertices mu d targets < 1 then
    ∑ row : Word n, oldRowCharge transcript vertices mu d targets inputs row
    else 0

namespace DriftChargeSpec

/-- Pointwise decomposition with the convexity coefficients. Taking θ=1 yields the
ordinary 2^(d-1) coefficient. The weighted variant uses the same potential. -/
def Pointwise : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (mu d : ℕ) (column : Word n) (mode : Finset (Word n)) (offset : Word n) (theta : ℝ),
    1 ≤ d → 0 < theta →
    patternIncrement transcript record vertices mu d column mode offset ≤
      reuseCharge transcript record vertices column mode offset +
        (1 + theta)^(d - 1) * oldPatternCharge transcript record vertices mu d column mode offset +
        (1 + theta⁻¹)^(d - 1) * forwardWeight (realRecordRelation transcript) vertices mu d
          (inputPattern transcript record vertices column mode offset)

/-- The actual change in translated potential covers the graph update before deletions. -/
def BoundedIncrement : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (mu d Pi : ℕ) (column : Word n) (mode : Finset (Word n)),
    (rightSupport (endpointPairs (realRecordRelation transcript) vertices record.output.2
      column)).card ≤ Pi →
      let inc := translatedIncrement transcript record vertices mu d column mode
      0 ≤ inc ∧ inc ≤ Pi ∧ inc =
        translatedPotential (realRecordRelation (transcript ++ [record]))
          vertices mu d column mode -
          translatedPotential (realRecordRelation transcript) vertices mu d column mode

end DriftChargeSpec

end JH.Graph
