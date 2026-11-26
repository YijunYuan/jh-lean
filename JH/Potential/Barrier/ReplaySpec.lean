/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.Drift.StoppedChargeSpec
public import JH.Probability.FirstStopSpec
public import JH.Probability.Tape.TestsSpec

/-!
# Ledger charges along stopped graph replay

The adapted costs for a graph ledger and their deterministic barrier cover.
-/

@[expose] public section

namespace JH.Probability

open JH.Graph JH.Parameters
open scoped BigOperators

namespace BarrierReplay

variable {n q : ℕ}

/-- Run the trial on the intrinsic and shift projections of a paired tape. -/
def prefixState (program : TrialProgram n) (tape : Fin q → State n) (i : ℕ) (within : i ≤ q) :
    TapeState n :=
  (⟨program, []⟩ : TapeState n).runPrefix (fun j ↦ (tape j).1) (fun j ↦ (tape j).2) i within

/-- The frontier and transcript obtained from the prefix before the specified round. -/
def beforeRound (program : TrialProgram n) (i : Fin q)
    (prior : Fin i.val → State n) : TapeState n :=
  prefixState program prior i.val le_rfl

/-- Assess the new record against the old graph. A terminal program or a previously stopped
graph incurs zero cost. -/
noncomputable def ledgerCost (params : Params) (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (direction : Direction)
    (line : Word params.n) (mode : Finset (Word params.n)) :
    (i : Fin q) → (Fin i.val → State params.n) → State params.n → ℝ :=
  fun i prior word ↦
    let before := beforeRound program i prior
    match before.frontier with
    | .done _ => 0
    | .query request _ =>
        GraphTracker.charge params (GraphTracker.replay params psi initials targets before.records)
          (request.recordOfReply (request.replyCoords.symm word)) direction line mode

end BarrierReplay

namespace BarrierReplaySpec

open BarrierReplay

/-- A first potential crossing forces sufficient cumulative charge in some account. -/
def StopCovered : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    ∀ (tapes : CoordinateTape params.n q × CoordinateTape params.n q),
      firstStopOnTapes params psi initials targets program tapes = some .overPotential →
      ∃ (direction : Direction) (line : Word params.n) (mode : Finset (Word params.n)),
        mode.Nonempty ∧ mode.card ≤ params.Pi ∧
        let pairedTape : Fin q → State params.n := fun i ↦ (tapes.1 i, tapes.2 i)
        (params.Gamma : ℝ) / 2 ≤ ∑ i : Fin q,
          ledgerCost params psi initials targets program direction line mode i
            (TapeTests.prefixAt pairedTape i) (pairedTape i)

/-- Each active account charge lies between zero and Bver, as in (19). -/
def LocalRange : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ∀ direction line mode (i : Fin q) (prior : Fin i.val → State params.n) (word : State params.n),
      let cost := ledgerCost params psi initials targets program direction line mode i prior word
      0 ≤ cost ∧ cost ≤ (params.Pi : ℝ)

/-- Conditional on the prefix, an account charge has mean at most D/N for the unweighted D. -/
def LocalMean : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    0 < params.d → (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ∀ direction line (mode : Finset (Word params.n)), mode.card ≤ params.Pi →
    ∀ (i : Fin q) (prior : Fin i.val → State params.n) (intrinsic : Word params.n),
      wordMean (fun shift ↦ ledgerCost params psi initials targets program direction line mode
        i prior (intrinsic, shift)) ≤ (params.driftNumerator : ℝ) / (params.N : ℝ)

/-- The same conditional charge bound uses the weighted D of (A.3). -/
def WeightedLocalMean : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n) (theta : ℝ),
    0 < params.d → 0 < theta →
    (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ∀ direction line (mode : Finset (Word params.n)), mode.card ≤ params.Pi →
    ∀ (i : Fin q) (prior : Fin i.val → State params.n) (intrinsic : Word params.n),
      wordMean (fun shift ↦ ledgerCost params psi initials targets program direction line mode
        i prior (intrinsic, shift)) ≤ params.weightedDriftNumerator theta / (params.N : ℝ)

end BarrierReplaySpec

end JH.Probability
