/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.ShiftTestSpec
public import JH.Graph.Evolution.RoundSpec

/-!
# Translated patterns and ancestor groups

Translated column patterns, ancestor groups, and their cardinalities.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

/-- Translate a set of words by XOR with the specified offset. -/
def xorTranslate (offset : Word n) (mode : Finset (Word n)) : Finset (Word n) :=
  mode.image fun delta ↦ offset ^^^ delta

/-- The restricted left support from the proof of Lemma 4. -/
def restrictedLeftSupport (pairs : Finset (Word n × Word n))
    (allowedRates : Finset (Word n)) : Finset (Word n) :=
  leftSupport (pairs.filter fun pair ↦ pair.2 ∈ allowedRates)

/-- The translated pattern in (16), intersected with the current residual vertices. -/
def columnPattern (vertices : Set (State n)) (column : Word n)
    (mode : Finset (Word n)) (offset : Word n) : Set (State n) :=
  {state | state ∈ vertices ∧ state.1 = column ∧ state.2 ∈ xorTranslate offset mode}

/-- Residual vertices in a specified row that can reach a member of the target set. -/
def rowAncestorsTo (edge : State n → State n → Prop) (vertices : Set (State n))
    (row : Word n) (targets : Set (State n)) : Set (State n) :=
  {state | state.2 = row ∧ ∃ target ∈ targets, ReachesWithin edge vertices state target}

/-- A walk to the selected pattern that traverses the newly added record at least twice.
The walk is in the graph after adding the record and before deleting vertices. -/
def ReuseToPattern (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (column : Word n) (mode : Finset (Word n)) (offset : Word n) : Prop :=
  ∃ source target : vertices, target.val ∈ columnPattern vertices column mode offset ∧
    ∃ walk : AddedWalk (residualRecordEdge transcript vertices)
      (residualNewEdge record vertices) source target, 1 < walk.newUses

/-- All new-record inputs with an output that can reach the pattern via old edges. -/
noncomputable def inputPattern (transcript : Transcript n) (record : Record n)
    (vertices : Set (State n)) (column : Word n) (mode : Finset (Word n)) (offset : Word n) :
    Set (State n) :=
  let support := restrictedLeftSupport
    (endpointPairs (realRecordRelation transcript) vertices record.output.2 column)
    (xorTranslate offset mode)
  columnPattern vertices record.input.1 support record.shift

/-- Offsets whose translated target pattern has nonempty restricted left support in (21). -/
def nonemptySupportOffsets (pairs : Finset (Word n × Word n))
    (mode : Finset (Word n)) : Finset (Word n) :=
  Finset.univ.filter fun offset ↦
    (restrictedLeftSupport pairs (xorTranslate offset mode)).Nonempty

namespace PatternsSpec

/-- Eligible new inputs for the translated target set are exactly the input pattern determined by
the old endpoint relation. -/
def InputIdentification : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (column : Word n) (mode : Finset (Word n)) (offset : Word n),
    newInputs (residualRecordEdge transcript vertices) (residualNewEdge record vertices)
      (Subtype.val ⁻¹' columnPattern vertices column mode offset) =
      Subtype.val ⁻¹' inputPattern transcript record vertices column mode offset

/-- The ancestor decomposition used in Lemma 4, with the full graph of the appended transcript
restricted to the old residual vertex set, as in the definition of the argument graph. -/
def TwoGroups : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (vertices : Set (State n))
    (row column : Word n) (mode : Finset (Word n)) (offset : Word n),
    ¬ ReuseToPattern transcript record vertices column mode offset →
    rowAncestorsTo (realRecordRelation (transcript ++ [record])) vertices row
        (columnPattern vertices column mode offset) =
      rowAncestorsTo (realRecordRelation transcript) vertices row
        (columnPattern vertices column mode offset) ∪
      rowAncestorsTo (realRecordRelation transcript) vertices row
        (inputPattern transcript record vertices column mode offset)

/-- The three support counts in the proof of Lemma 4, before inserting the bounds `Pi` and
`Theta`. -/
def TranslationCounts : Prop :=
  ∀ {n : ℕ} (pairs : Finset (Word n × Word n)) (mode : Finset (Word n)),
    (∀ offset, (restrictedLeftSupport pairs (xorTranslate offset mode)).card ≤
      (leftSupport pairs).card) ∧
    (nonemptySupportOffsets pairs mode).card ≤ mode.card * (rightSupport pairs).card ∧
    (∑ offset : Word n, (restrictedLeftSupport pairs (xorTranslate offset mode)).card) ≤
      mode.card * pairs.card

end PatternsSpec

end JH.Graph
