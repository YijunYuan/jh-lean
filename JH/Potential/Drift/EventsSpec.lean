/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.PatternsSpec

/-!
# Shift events for a fixed pattern

Shift events that contribute to the drift of a fixed pattern.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ}

/-- The input mode determined by the old graph, output row and target pattern. -/
noncomputable def patternOutletSupport (transcript : Transcript n) (vertices : Set (State n))
    (outputRow column : Word n) (mode : Finset (Word n)) (offset : Word n) : Finset (Word n) :=
  restrictedLeftSupport (endpointPairs (realRecordRelation transcript) vertices outputRow column)
    (xorTranslate offset mode)

/-- The intrinsic coordinates held fixed when averaging over the offset in Lemma 4. -/
def SharesExposedCoordinates (recordFor : Word n → Record n) (inputColumn outputRow : Word n) :
    Prop :=
  ∀ shift, (recordFor shift).input.1 = inputColumn ∧ (recordFor shift).output.2 = outputRow ∧
    (recordFor shift).shift = shift

namespace DriftEventsSpec

/-- The sharper form of the old-ancestor row event bound used for both choices of the
coefficients in (A.2) and (A.3). -/
def AncestorRowProbability : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n))
    (inputColumn outputRow ancestorRow column : Word n) (mode : Finset (Word n)) (offset : Word n)
    (recordFor : Word n → Record n), SharesExposedCoordinates recordFor inputColumn outputRow →
      uniformShiftMass {shift |
        (rowAncestorsTo (realRecordRelation transcript) vertices ancestorRow
          (inputPattern transcript (recordFor shift) vertices column mode offset)).Nonempty} ≤
        (rightSupport (endpointPairs (realRecordRelation transcript) vertices
          ancestorRow inputColumn)).card *
          (patternOutletSupport transcript vertices outputRow column mode offset).card / (2 : ℝ)^n

/-- The reuse bound in the proof of Lemma 4, retaining the actual right support cardinal for the
return segment. -/
def ReuseProbability : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n))
    (inputColumn outputRow column : Word n) (mode : Finset (Word n)) (offset : Word n)
    (recordFor : Word n → Record n), SharesExposedCoordinates recordFor inputColumn outputRow →
      uniformShiftMass
        {shift | ReuseToPattern transcript (recordFor shift) vertices column mode offset}
        ≤ (rightSupport (endpointPairs (realRecordRelation transcript) vertices
          outputRow inputColumn)).card *
          (patternOutletSupport transcript vertices outputRow column mode offset).card / (2 : ℝ)^n

/-- An offset is chargeable only if the support into the target pattern is nonempty. -/
def EmptySupportNoGrowth : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (row column : Word n) (mode : Finset (Word n)) (offset : Word n),
    patternOutletSupport transcript vertices record.output.2 column mode offset = ∅ →
      rowAncestorsTo (realRecordRelation (transcript ++ [record])) vertices row
        (columnPattern vertices column mode offset) =
      rowAncestorsTo (realRecordRelation transcript) vertices row
        (columnPattern vertices column mode offset)

end DriftEventsSpec

end JH.Graph
