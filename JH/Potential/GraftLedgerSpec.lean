/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.WeightsSpec

/-!
# Payment for grafting by residual potential

The column and row payments for deleting vertices in Section 3.4.
-/

@[expose] public section

namespace JH.Graph

variable {n : ℕ} {initials : Finset (State n)}

/-- Real vertices on a line newly added to one side, indexed by their free coordinate. -/
noncomputable def graftedOnLine (old new : Set (Vertex initials))
    (line : Word n → State n) : Finset (Word n) := by
  classical
  exact Finset.univ.filter fun free ↦ Sum.inl (line free) ∈ new ∧ Sum.inl (line free) ∉ old

/-- The real vertices grafted forward in the given column, excluding inherited vertices. -/
noncomputable def forwardGraftCount (inherited finish : Boundary (Vertex initials))
    (column : Word n) : ℕ :=
  (graftedOnLine inherited.forward finish.forward (fun rate ↦ (column, rate))).card

/-- The real vertices grafted backward in the given row, excluding inherited vertices. -/
noncomputable def backwardGraftCount (inherited finish : Boundary (Vertex initials))
    (row : Word n) : ℕ :=
  (graftedOnLine inherited.backward finish.backward (fun column ↦ (column, row))).card

/-- Reverse the edges and exchange capacity with rate so that rows become columns. -/
def transposeStateEdge (edge : State n → State n → Prop) (source target : State n) : Prop :=
  edge target.swap source.swap

/-- Sum of the backward singleton weights in a row, using the transposed graph. -/
noncomputable def backwardPointRowPotential (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (row : Word n) : ℝ :=
  pointColumnPotential (transposeStateEdge edge) (Prod.swap ⁻¹' vertices) mu d row

/-- Backward potential for a translated pattern in a row, obtained by reversing edges and
swapping coordinates. -/
noncomputable def backwardTranslatedPotential (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (row : Word n) (mode : Finset (Word n)) : ℝ :=
  translatedPotential (transposeStateEdge edge) (Prod.swap ⁻¹' vertices) mu d row mode

namespace GraftLedgerSpec

/-- All actual forward and backward grafts in a continuing round are paid for by deleting
vertices after the argument graph has been formed. -/
def RoundPayment : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (mu d : ℕ)
    {initials : Finset (State n)} (before finish : Boundary (Vertex initials)),
    0 < mu → RoundStep transcript record mu before (.continued finish) →
      let updated := transcript ++ [record]
      let inherited := before.inherit (recordRelation updated initials)
      (∀ column, pointColumnPotential (realRecordRelation updated) finish.realResidual mu d column +
        forwardGraftCount inherited finish column ≤
          pointColumnPotential (argumentEdge transcript record before)
            before.realResidual mu d column) ∧
      (∀ row, backwardPointRowPotential (realRecordRelation updated) finish.realResidual mu d row +
        backwardGraftCount inherited finish row ≤
          backwardPointRowPotential (argumentEdge transcript record before)
            before.realResidual mu d row)

/-- From the argument graph to the final residual graph, every translated mode can only decrease. -/
def RoundModeDecrease : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (record : Record n) (mu d : ℕ)
    {initials : Finset (State n)} (before finish : Boundary (Vertex initials)),
    RoundStep transcript record mu before (.continued finish) →
      let updated := transcript ++ [record]
      (∀ column mode,
        translatedPotential (realRecordRelation updated) finish.realResidual mu d column mode ≤
        translatedPotential (argumentEdge transcript record before)
          before.realResidual mu d column mode) ∧
      (∀ row mode, backwardTranslatedPotential (realRecordRelation updated)
        finish.realResidual mu d row mode ≤
        backwardTranslatedPotential (argumentEdge transcript record before)
          before.realResidual mu d row mode)

end GraftLedgerSpec

end JH.Graph
