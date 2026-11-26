/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.StoppedGraphSpec
public import JH.Oracle.Coupling.SuccessTransferSpec
public import JH.Oracle.Independent.CoordinateTapeSpec

/-!
# Combining the first-stop probabilities

The four graph events under the actual independent-reply trial law.
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters

variable {params : Params} {q : ℕ}

/-- The eventual first graph stop by the end of the fresh-access budget. A halted program
adds no records in the remaining tape positions. -/
noncomputable def firstStopOnTapes (params : Params) (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
      (tapes : CoordinateTape params.n q × CoordinateTape params.n q) :
    Option FirstGraphStop :=
  let start : TapeState params.n := ⟨program, []⟩
  let final := start.runPrefix tapes.1 tapes.2 q le_rfl
  (GraphTracker.replay params psi initials targets final.records).stopReason

/-- Pairs of tapes for which the stopped replay records the specified first violation. -/
noncomputable def firstStopEvent (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (stop : FirstGraphStop) :
    Set (CoordinateTape params.n q × CoordinateTape params.n q) :=
  {tapes | firstStopOnTapes params psi initials targets program tapes = some stop}

/-- Probability of a specified first graph stop on the two independent uniform tapes. -/
noncomputable def firstStopProbability (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (stop : FirstGraphStop) : ℝ :=
  ((CoordinateTape.law params.n q).toOuterMeasure
    (firstStopEvent params q psi initials targets program stop)).toReal

/-- Bounds on the probabilities of the four first stopping events in (11). -/
structure FirstStopBounds (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (bound : ℝ) : Prop where
  /-- Bound for a first intersection during inheritance. -/
  intersect : firstStopProbability params q psi initials targets program .intersect ≤ bound
  /-- Bound for a first account reaching Bpot. -/
  potential : firstStopProbability params q psi initials targets program .overPotential ≤ bound
  /-- Bound for a first row-to-column packing larger than Bpath. -/
  connected : firstStopProbability params q psi initials targets program .overConnected ≤ bound
  /-- Bound for a first occupancy exceeding the line threshold. -/
  crowded : firstStopProbability params q psi initials targets program .overCrowded ≤ bound

namespace FirstStopSpec

/-- Each supported acceptance has already encountered a graph stop. All four events are
measured using the original bounded independent-reply program and both of its tapes. -/
def AcceptanceCovered : Prop :=
  ∀ {α : ℕ} (params : Params) (q : ℕ) (target : Word params.n) (initial : State params.n)
    (padding : Padding α params.n) (strategy : Strategy α params.n),
    let stop := firstStopProbability params q params.Psi {initial} {target}
      (TrialProgram.ofStrategy strategy initial padding)
    ((independentAcceptanceLaw q target initial padding strategy) true).toReal ≤
      stop .intersect + stop .overPotential + stop .overConnected + stop .overCrowded

end FirstStopSpec

end JH.Graph
