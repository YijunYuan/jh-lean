/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.StoppedGraph
public import JH.Oracle.Independent.CoordinateTape
public import JH.Potential.Barrier.ReplaySpec
public import JH.Potential.Drift.StoppedCharge
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Ledger charges along stopped graph replay

Lemma 4 and the argument for (22) bound ledger growth by charges computed from the pre-round
history and the fresh reply. This replay pays for the decisive round and assigns zero cost once
the graph has stopped. Appendix A.3 supplies a weighted alternative for the mean. The initial
ledger bound and the prefix sum of charges witness a barrier stop.
-/

@[expose] public section

namespace JH

open JH.Graph JH.Parameters
open scoped BigOperators

/-- Extending the available tapes does not affect the state computed from a common prefix. -/
theorem TapeState.runPrefix_eq_of_prefix {n q r : ℕ} (initial : TapeState n)
    (intrinsic offsets : CoordinateTape n q) (otherIntrinsic otherOffsets : CoordinateTape n r)
    (i : ℕ) (within : i ≤ q) (otherWithin : i ≤ r)
    (agrees : ∀ j : Fin i,
      intrinsic ⟨j.val, j.isLt.trans_le within⟩ = otherIntrinsic ⟨j.val,
        j.isLt.trans_le otherWithin⟩ ∧
      offsets ⟨j.val, j.isLt.trans_le within⟩ = otherOffsets ⟨j.val, j.isLt.trans_le otherWithin⟩) :
    initial.runPrefix intrinsic offsets i within =
      initial.runPrefix otherIntrinsic otherOffsets i otherWithin := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have prior := ih (by omega) (by omega) (fun j ↦ agrees j.castSucc)
    obtain ⟨sameCoordinate, sameOffset⟩ := agrees (Fin.last i)
    rw [TapeState.runPrefix, TapeState.runPrefix, prior]
    exact congrArg₂ ((initial.runPrefix otherIntrinsic otherOffsets i (by omega)).step)
      sameCoordinate sameOffset

/-- Fixing the intrinsic coordinate fixes the input column and output row as the shift varies. -/
theorem Query.recordOfReply_sharesExposedCoordinates {n : ℕ} (request : Query n)
    (intrinsic : Word n) :
    ∃ inputColumn outputRow, SharesExposedCoordinates
      (fun shift ↦ request.recordOfReply (request.replyCoords.symm (intrinsic, shift)))
      inputColumn outputRow := by
  have shift_eq (shift : Word n) :
      (request.recordOfReply (request.replyCoords.symm (intrinsic, shift))).shift = shift :=
    congrArg Prod.snd
      ((request.recordOfReply_coords (request.replyCoords.symm (intrinsic, shift))).trans
        (request.replyCoords.apply_symm_apply (intrinsic, shift)))
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward => exact ⟨address.1, intrinsic, fun shift ↦ ⟨rfl, rfl, shift_eq shift⟩⟩
  | backward => exact ⟨intrinsic, address.2, fun shift ↦ ⟨rfl, rfl, shift_eq shift⟩⟩

namespace Probability.BarrierReplay

/-- The past used by a local charge agrees with replay up to the current tape position. -/
theorem beforeRound_eq_runPrefix {n q : ℕ} (program : TrialProgram n) (pairedTape : Fin q → State n)
    (i : Fin q) :
    beforeRound program i (TapeTests.prefixAt pairedTape i) =
      prefixState program pairedTape i.val (Nat.le_of_lt i.isLt) := by
  unfold beforeRound prefixState
  apply TapeState.runPrefix_eq_of_prefix
  intro j
  exact ⟨rfl, rfl⟩

/-- For any preceding prefix and fresh reply, the replayed charge lies in $[0,B_{\mathrm{ver}}]$. -/
theorem ledger_cost_range : BarrierReplaySpec.LocalRange := by
  intro params q psi initials targets program initialValid direction line mode i prior word
  cases reached : (beforeRound program i prior).frontier with
  | done terminal => simp [ledgerCost, reached]
  | query request resume =>
      cases recorded : GraphTracker.replay params psi initials targets
          (beforeRound program i prior).records with
      | stopped reason snapshot => simp [ledgerCost, reached, recorded, GraphTracker.charge]
      | active snapshot =>
          have valid := graph_active_parameters params psi initials targets initialValid
            (beforeRound program i prior).records snapshot recorded
          simpa only [ledgerCost, reached, recorded]
            using active_charge_range params psi snapshot valid
            (request.recordOfReply (request.replyCoords.symm word)) direction line mode

/-- Bound the shift average of the replayed charge after exposing the intrinsic coordinate. -/
theorem ledger_cost_mean : BarrierReplaySpec.LocalMean := by
  intro params q psi initials targets program positiveD initialValid direction line mode size
    i prior intrinsic
  have nonnegative : 0 ≤ (params.driftNumerator : ℝ) / (params.N : ℝ) := by positivity
  cases reached : (beforeRound program i prior).frontier with
  | done terminal => simpa [ledgerCost, reached, wordMean] using nonnegative
  | query request resume =>
      cases recorded : GraphTracker.replay params psi initials targets
          (beforeRound program i prior).records with
      | stopped reason snapshot =>
          simpa [ledgerCost, reached, recorded, GraphTracker.charge, wordMean] using nonnegative
      | active snapshot =>
          have valid := graph_active_parameters params psi initials targets initialValid
            (beforeRound program i prior).records snapshot recorded
          obtain ⟨inputColumn, outputRow, shares⟩ :=
            request.recordOfReply_sharesExposedCoordinates intrinsic
          simpa only [ledgerCost, reached, recorded] using active_charge_mean params psi snapshot
            inputColumn outputRow (fun shift ↦ request.recordOfReply
              (request.replyCoords.symm (intrinsic, shift)))
                positiveD valid shares direction line mode size

/-- Use the Appendix A.3 weighted charge bound with the same past and reply coordinates. -/
theorem ledger_cost_weighted_mean : BarrierReplaySpec.WeightedLocalMean := by
  intro params q psi initials targets program theta positiveD positiveTheta
    initialValid direction line mode
    size i prior intrinsic
  have nonnegative : 0 ≤ params.weightedDriftNumerator theta / (params.N : ℝ) := by
    unfold Params.weightedDriftNumerator Params.weightedCoefficient Analysis.weightedCost
    positivity
  cases reached : (beforeRound program i prior).frontier with
  | done terminal => simpa [ledgerCost, reached, wordMean] using nonnegative
  | query request resume =>
      cases recorded : GraphTracker.replay params psi initials targets
          (beforeRound program i prior).records with
      | stopped reason snapshot =>
          simpa [ledgerCost, reached, recorded, GraphTracker.charge, wordMean] using nonnegative
      | active snapshot =>
          have valid := graph_active_parameters params psi initials targets initialValid
            (beforeRound program i prior).records snapshot recorded
          obtain ⟨inputColumn, outputRow, shares⟩ :=
            request.recordOfReply_sharesExposedCoordinates intrinsic
          simpa only [ledgerCost, reached, recorded]
            using active_charge_weighted_mean params psi snapshot
            inputColumn outputRow (fun shift ↦ request.recordOfReply
              (request.replyCoords.symm (intrinsic, shift)))
                theta positiveD positiveTheta valid shares
            direction line mode size

private theorem advance_ledger_le (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (tracker : GraphTracker initials) (record : Record params.n)
    (positiveMu : 0 < params.mu) (positiveD : 0 < params.d)
    (notIntersected : (tracker.advance params psi record).stopReason ≠ some .intersect)
    (direction : Direction) (line : Word params.n) (mode : Finset (Word params.n)) :
    tracker.stopReason ≠ some .intersect ∧
      (tracker.advance params psi record).snapshot.ledger params.mu params.d direction line mode ≤
        tracker.snapshot.ledger params.mu params.d direction line mode +
          tracker.charge params record direction line mode := by
  -- A stopped tracker keeps its snapshot. A live nonintersection round pays for grafting.
  cases tracker with
  | stopped reason snapshot =>
      exact ⟨notIntersected, by simp [GraphTracker.advance, GraphTracker.charge]⟩
  | active snapshot =>
      obtain ⟨finish, classified, continued⟩ :=
        GraphTracker.advance_nonintersection snapshot record notIntersected
      refine ⟨by simp [GraphTracker.stopReason], ?_⟩
      rw [classified, GraphTracker.classified_snapshot]
      exact afterGrafting_ledger_le params snapshot record finish positiveMu positiveD continued
        direction line mode

/-- Replay the graph on the records written by the first `i` tape positions. -/
noncomputable def trackerAfterPrefix (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n) (i : ℕ) (within : i ≤ q) :
    GraphTracker initials :=
  GraphTracker.replay params psi initials targets (prefixState program tape i within).records

/-- A live round pays for its ledger increase, and a halted round preserves its ledger. -/
theorem prefix_ledger_step (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n) (i : Fin q)
    (positiveMu : 0 < params.mu) (positiveD : 0 < params.d)
    (notIntersected : (trackerAfterPrefix params psi initials targets program tape
      (i.val + 1) (Nat.succ_le_of_lt i.isLt)).stopReason ≠ some .intersect)
    (direction : Direction) (line : Word params.n) (mode : Finset (Word params.n)) :
    let old := trackerAfterPrefix params psi initials targets program tape i.val
        (Nat.le_of_lt i.isLt)
    let new := trackerAfterPrefix params psi initials targets program tape (i.val + 1)
      (Nat.succ_le_of_lt i.isLt)
    old.stopReason ≠ some .intersect ∧
      new.snapshot.ledger params.mu params.d direction line mode ≤
        old.snapshot.ledger params.mu params.d direction line mode +
          ledgerCost params psi initials targets program direction line mode i
            (TapeTests.prefixAt tape i) (tape i) := by
  let before := prefixState program tape i.val (Nat.le_of_lt i.isLt)
  let after := prefixState program tape (i.val + 1) (Nat.succ_le_of_lt i.isLt)
  let old := GraphTracker.replay params psi initials targets before.records
  let new := GraphTracker.replay params psi initials targets after.records
  -- Identify the charge computed from the prefix with the charge on the actual tracker.
  have cost_eq :
      ledgerCost params psi initials targets program direction line mode i
        (TapeTests.prefixAt tape i) (tape i) =
      match before.frontier with
      | .done _ => 0
      | .query request _ => GraphTracker.charge params old
          (request.recordOfReply (request.replyCoords.symm (tape i))) direction line mode := by
    rw [ledgerCost, beforeRound_eq_runPrefix]
    rfl
  change new.stopReason ≠ some .intersect at notIntersected
  change old.stopReason ≠ some .intersect ∧
    new.snapshot.ledger params.mu params.d direction line mode ≤
      old.snapshot.ledger params.mu params.d direction line mode +
        ledgerCost params psi initials targets program direction line mode i
          (TapeTests.prefixAt tape i) (tape i)
  cases reached : before.frontier with
  | done terminal =>
      have unchanged : after = before := by
        change before.step (tape i).1 (tape i).2 = before
        rw [TapeState.step, reached]
      have same : new = old := congrArg
        (fun state : TapeState params.n ↦
          GraphTracker.replay params psi initials targets state.records)
        unchanged
      rw [same, cost_eq, reached, add_zero]
      exact ⟨same ▸ notIntersected, le_rfl⟩
  | query request resume =>
      let record := request.recordOfReply (request.replyCoords.symm (tape i))
      have appends : after.records = before.records ++ [record] :=
        (TapeState.live_round (⟨program, []⟩ : TapeState params.n) (fun j ↦ (tape j).1)
          (fun j ↦ (tape j).2) i request resume reached).2.1
      have next : new = old.advance params psi record := by
        change GraphTracker.replay params psi initials targets after.records = _
        rw [appends]
        exact GraphTracker.replay_append params psi initials targets before.records [record]
      rw [next, cost_eq, reached]
      exact advance_ledger_le params psi old record positiveMu positiveD (next ▸ notIntersected)
        direction line mode

/-- Sum the ledger inequalities up to a given prefix for a history that avoids an
intersection stop. -/
theorem ledger_at_prefix_le_sum (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n)
    (positiveMu : 0 < params.mu) (positiveD : 0 < params.d)
    (direction : Direction) (line : Word params.n) (mode : Finset (Word params.n))
    (k : ℕ) (within : k ≤ q)
    (notIntersected : (trackerAfterPrefix params psi initials targets program tape
      k within).stopReason ≠ some .intersect) :
    (trackerAfterPrefix params psi initials targets program tape k within).snapshot.ledger
        params.mu params.d direction line mode ≤
      (GraphSnapshot.initial initials targets).ledger params.mu params.d direction line mode +
        ∑ j : Fin k, ledgerCost params psi initials targets program direction
          line mode (j.castLE within)
          (TapeTests.prefixAt tape (j.castLE within)) (tape (j.castLE within)) := by
  induction k with
  | zero =>
      simp [trackerAfterPrefix, prefixState, TapeState.runPrefix,
        GraphTracker.replay, GraphTracker.snapshot]
  | succ k ih =>
      let i : Fin q := ⟨k, Nat.lt_of_succ_le within⟩
      have growth := prefix_ledger_step params psi initials targets program
          tape i positiveMu positiveD
        notIntersected direction line mode
      have earlier := ih (Nat.le_of_succ_le within) growth.1
      rw [Fin.sum_univ_castSucc]
      refine growth.2.trans ?_
      rw [← add_assoc]
      exact add_le_add_left earlier
        (ledgerCost params psi initials targets program direction line mode i
          (TapeTests.prefixAt tape i) (tape i))

/-- The empty transcript gives the same initial potential bound in either direction. -/
theorem initial_ledger_bound (params : Params) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (positiveMu : 0 < params.mu) (positiveD : 0 < params.d)
    (direction : Direction)
    (line : Word params.n) (mode : Finset (Word params.n)) :
    (GraphSnapshot.initial initials targets).ledger params.mu params.d direction line mode ≤
      (params.N : ℝ) / (params.mu : ℝ) ^ params.d := by
  have initialPotential (vertices : Set (State params.n)) :
      translatedPotential (realRecordRelation ([] : Transcript params.n))
        vertices params.mu params.d line mode ≤
        (params.N : ℝ) / (params.mu : ℝ) ^ params.d := by
    simpa only [Params.N, Nat.cast_pow, Nat.cast_ofNat] using
      initial_translated_potential vertices params.mu params.d line mode positiveMu positiveD
  cases direction with
  | forward =>
      simpa [GraphSnapshot.ledger, GraphSnapshot.initial] using
        initialPotential (initialBoundary initials targets).realResidual
  | backward =>
      simpa [GraphSnapshot.ledger, GraphSnapshot.initial, backwardTranslatedPotential,
        transposeStateEdge_realRecordRelation] using
          initialPotential (Prod.swap ⁻¹' (initialBoundary initials targets).realResidual)

/-- The initial-potential certificate allocates at most half the barrier to initialization. -/
theorem initial_ledger_le_half (params : Params) (q : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (certificate : params.CommonCertificate q)
      (direction : Direction)
    (line : Word params.n) (mode : Finset (Word params.n)) :
    (GraphSnapshot.initial initials targets).ledger params.mu params.d direction line mode ≤
      (params.Gamma : ℝ) / 2 := by
  have positiveMu := lt_of_lt_of_le (by decide : 0 < 2) certificate.admissible.mu_ge_two
  have positiveD := lt_of_lt_of_le (by decide : 0 < 2) certificate.admissible.d_ge_two
  have ledger := initial_ledger_bound params initials targets positiveMu
      positiveD direction line mode
  have certificateBound := certificate.initial_potential
  rw [mul_div_assoc] at certificateBound
  linarith only [ledger, certificateBound]

private theorem replay_over_potential_not_below (params : Params) (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (records : Transcript params.n) (snapshot : GraphSnapshot initials)
    (stopped : GraphTracker.replay params psi initials targets records =
      .stopped .overPotential snapshot) :
    ¬ snapshot.BelowBarrier params := by
  obtain ⟨_, decisive, _, before, _, _, decision⟩ :=
    graph_earliest_record params psi initials targets records .overPotential snapshot stopped
  have notIntersected : (GraphTracker.advance params psi (.active before) decisive).stopReason ≠
      some .intersect := by simp [decision, GraphTracker.stopReason]
  obtain ⟨finish, classified, _⟩ :=
    GraphTracker.advance_nonintersection before decisive notIntersected
  rw [decision] at classified
  have same : snapshot = before.afterGrafting decisive finish := by
    have equation := congrArg GraphTracker.snapshot classified
    rw [GraphTracker.classified_snapshot] at equation
    exact equation
  subst snapshot
  exact (graph_threshold_priority params psi _).1.mp classified.symm

/-- A first potential stop identifies an account with cumulative charges at least
$B_{\mathrm{pot}}/2$. -/
theorem barrier_stop_covered : BarrierReplaySpec.StopCovered := by
  intro params q psi initials targets program certificate _ tapes stopped
  let tape : Fin q → State params.n := fun i ↦ (tapes.1 i, tapes.2 i)
  have stopReason :
      (trackerAfterPrefix params psi initials targets program tape q le_rfl).stopReason =
      some .overPotential := stopped
  cases replayed : trackerAfterPrefix params psi initials targets program tape q le_rfl with
  | active snapshot => simp [replayed, GraphTracker.stopReason] at stopReason
  | stopped reason snapshot =>
      have reason_eq : reason = .overPotential := by
        simpa [replayed, GraphTracker.stopReason] using stopReason
      subst reason
      have above := replay_over_potential_not_below params psi initials targets
        (prefixState program tape q le_rfl).records snapshot replayed
      unfold GraphSnapshot.BelowBarrier at above
      push Not at above
      obtain ⟨direction, line, mode, nonempty, size, reached⟩ := above
      have positiveMu := lt_of_lt_of_le (by decide : 0 < 2) certificate.admissible.mu_ge_two
      have positiveD := lt_of_lt_of_le (by decide : 0 < 2) certificate.admissible.d_ge_two
      have notIntersected :
          (trackerAfterPrefix params psi initials targets program tape q le_rfl).stopReason ≠
          some .intersect := by simp [replayed, GraphTracker.stopReason]
      -- Use the decisive snapshot to select the ledger, then bound its value by the charge sum.
      have accrued :=
        ledger_at_prefix_le_sum params psi initials targets program tape positiveMu positiveD
        direction line mode q le_rfl notIntersected
      rw [replayed] at accrued
      simp only [GraphTracker.snapshot, Fin.castLE_refl] at accrued
      have initial :=
        initial_ledger_le_half params q initials targets certificate direction line mode
      refine ⟨direction, line, mode, nonempty, size, ?_⟩
      change (params.Gamma : ℝ) / 2 ≤ ∑ i : Fin q,
        ledgerCost params psi initials targets program direction line mode i
          (TapeTests.prefixAt tape i) (tape i)
      linarith only [reached, accrued, initial]

end Probability.BarrierReplay

end JH
