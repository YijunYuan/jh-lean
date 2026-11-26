/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.CoordinateTapeSpec
public import JH.Oracle.Independent.Trial

/-!
# Presampling the independent-reply coordinates

Use independent uniform word tapes for the presampled coordinate $\boldsymbol{\xi}_i$ and
record offset $\boldsymbol{\sigma}$ of Section 3.3. Each live round consumes one position
after resolving cache hits. The prefix lemmas justify conditioning on the entire coordinate
tape and the offsets strictly before the tested round, as in Lemma 3.
-/

@[expose] public section

namespace JH

namespace CoordinateTape

/-- The first coordinate pair is independent of the two tails, with both words uniform. -/
theorem split_law : CoordinateTapeSpec.SplitLaw := by
  intro n q
  simp only [law, ReplyCoupling.independentPair_uniform, ReplyCoupling.uniformFinite_map_equiv]

end CoordinateTape

namespace Query

variable {n : ℕ}

theorem recordOfReply_direction (request : Query n) (answer : State n) :
    (request.recordOfReply answer).direction = request.direction := by
  rcases request with ⟨_ | _, address⟩ <;> rfl

theorem recordOfReply_coords (request : Query n) (answer : State n) :
    ((request.recordOfReply answer).intrinsicCoordinate, (request.recordOfReply answer).shift) =
      request.replyCoords answer := by
  rcases request with ⟨_ | _, address⟩ <;> rfl

end Query

namespace TapeState

open PartialPermutation (uniformFinite)

variable {n q : ℕ}

/-- The state after `i` tape positions depends only on positions with index below `i`. -/
theorem prefix_agreement : CoordinateTapeSpec.PrefixAgreement := by
  intro n q initial intrinsic offsets intrinsic' offsets' i within agrees
  induction i with
  | zero => rfl
  | succ i ih =>
    let index : Fin q := ⟨i, by omega⟩
    have prior := ih (by omega) fun j hj ↦ agrees j (Nat.lt_succ_of_lt hj)
    obtain ⟨coordinate, offset⟩ := agrees index (Nat.lt_succ_self i)
    rw [runPrefix, runPrefix, prior, coordinate, offset]

/-- A live step appends a record with the request direction and the pair from that tape index. -/
theorem live_round : CoordinateTapeSpec.LiveRound := by
  intro n q initial intrinsic offsets i request resume
  dsimp only
  intro reached
  rw [runPrefix, step, reached]
  let answer := request.replyCoords.symm (intrinsic i, offsets i)
  have coords := (request.recordOfReply_coords answer).trans
    (request.replyCoords.apply_symm_apply (intrinsic i, offsets i))
  exact ⟨rfl, rfl, request.recordOfReply_direction answer, congrArg Prod.fst coords,
    congrArg Prod.snd coords⟩

/-- Once the frontier is terminal, the program and transcript remain fixed through later rounds.
-/
theorem terminal_round : CoordinateTapeSpec.TerminalRound := by
  intro n q initial intrinsic offsets i j earlier within terminal
  dsimp only
  intro reached
  induction j with
  | zero =>
    have eq : i = 0 := Nat.eq_zero_of_le_zero earlier
    subst i
    rfl
  | succ j ih =>
    by_cases same : i = j + 1
    · subst i
      rfl
    · have stays := ih (by omega) (by omega) reached
      rw [runPrefix, stays, step, reached]

private theorem step_records (state : TapeState n) (coordinate offset : Word n) :
    (state.step coordinate offset).records.Extends state.records ∧
      (state.step coordinate offset).records.length ≤ state.records.length + 1 := by
  cases reached : state.frontier with
  | done terminal =>
    rw [step, reached]
    exact ⟨⟨[], List.append_nil _⟩, Nat.le_succ _⟩
  | query request resume =>
    rw [step, reached]
    exact ⟨⟨[_], rfl⟩, by simp [Transcript.appendReply]⟩

theorem records_prefix (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (i j : ℕ) (earlier : i ≤ j) (within : j ≤ q) :
    (initial.runPrefix intrinsic offsets j within).records.Extends
      (initial.runPrefix intrinsic offsets i (earlier.trans within)).records := by
  induction j with
  | zero =>
    have same : i = 0 := Nat.eq_zero_of_le_zero earlier
    subst i
    exact ⟨[], List.append_nil _⟩
  | succ j ih =>
    by_cases same : i = j + 1
    · subst i
      exact ⟨[], List.append_nil _⟩
    · let index : Fin q := ⟨j, by omega⟩
      exact List.IsPrefix.trans (ih (by omega) (by omega))
        (step_records (initial.runPrefix intrinsic offsets j (by omega))
          (intrinsic index) (offsets index)).1

theorem records_length_le_round (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (i : ℕ) (within : i ≤ q) :
    (initial.runPrefix intrinsic offsets i within).records.length ≤ initial.records.length + i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    let index : Fin q := ⟨i, by omega⟩
    have bound := (step_records (initial.runPrefix intrinsic offsets i (by omega))
      (intrinsic index) (offsets index)).2
    exact bound.trans (Nat.succ_le_succ (ih (by omega)))

/-- A live frontier at round `i` has appended exactly `i` records, since earlier termination
would have frozen the state. -/
theorem records_length_of_live (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (i : ℕ) (within : i ≤ q) {request : Query n} {resume : State n → TrialProgram n}
    (live : (initial.runPrefix intrinsic offsets i within).frontier = .query request resume) :
    (initial.runPrefix intrinsic offsets i within).records.length = initial.records.length + i := by
  induction i generalizing request resume with
  | zero => rfl
  | succ i ih =>
    let index : Fin q := ⟨i, by omega⟩
    let before := initial.runPrefix intrinsic offsets i (by omega)
    change (before.step (intrinsic index) (offsets index)).frontier = _ at live
    change (before.step (intrinsic index) (offsets index)).records.length = _
    cases reached : before.frontier with
    | done terminal =>
      have stays : before.step (intrinsic index) (offsets index) = before := by rw [step, reached]
      rw [stays, reached] at live
      cases live
    | query request' resume' =>
      have length_before : before.records.length = initial.records.length + i :=
          ih (by omega) reached
      rw [step, reached]
      simp only [Transcript.appendReply, List.length_append, List.length_singleton, length_before,
        Nat.add_assoc]

/-- A new record at any prefix comes from exactly its indexed earlier live round. -/
theorem recorded_round (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (j : ℕ) (within : j ≤ q)
    (label : Transcript.Label (initial.runPrefix intrinsic offsets j within).records)
    (newLabel : initial.records.length ≤ label.val) :
    ∃ (i : Fin q) (request : Query n) (resume : State n → TrialProgram n),
      i.val < j ∧ initial.records.length + i.val = label.val ∧
      (initial.runPrefix intrinsic offsets i.val (Nat.le_of_lt i.isLt)).frontier =
        .query request resume ∧
      (initial.runPrefix intrinsic offsets j within).records.get label =
        request.recordOfReply (request.replyCoords.symm (intrinsic i, offsets i)) := by
  let final := initial.runPrefix intrinsic offsets j within
  have finalBound : final.records.length ≤ initial.records.length + j :=
    initial.records_length_le_round intrinsic offsets j within
  have labelBound : label.val < final.records.length := label.isLt
  -- Strip the initial log length to identify the tape index of this appended record.
  let i : Fin q := ⟨label.val - initial.records.length, by omega⟩
  have earlier : i.val < j := by dsimp [i]; omega
  have index : initial.records.length + i.val = label.val := by dsimp [i]; omega
  let before := initial.runPrefix intrinsic offsets i.val (Nat.le_of_lt i.isLt)
  cases reached : before.frontier with
  | done terminal =>
    have frozen : final = before :=
      terminal_round initial intrinsic offsets i.val j
        (Nat.le_of_lt earlier) within terminal reached
    have beforeBound : before.records.length ≤ initial.records.length + i.val :=
      initial.records_length_le_round intrinsic offsets i.val (Nat.le_of_lt i.isLt)
    rw [frozen] at labelBound
    omega
  | query request resume =>
    refine ⟨i, request, resume, earlier, index, reached, ?_⟩
    let after := initial.runPrefix intrinsic offsets (i.val + 1) (Nat.succ_le_of_lt i.isLt)
    let record := request.recordOfReply (request.replyCoords.symm (intrinsic i, offsets i))
    have appends : after.records = before.records ++ [record] :=
      (live_round initial intrinsic offsets i request resume reached).2.1
    have beforeLength : before.records.length = initial.records.length + i.val :=
      initial.records_length_of_live intrinsic offsets i.val (Nat.le_of_lt i.isLt) reached
    have appendIndex : label.val = before.records.length := index.symm.trans beforeLength.symm
    have afterBound : label.val < after.records.length := by
      rw [appends, List.length_append, List.length_singleton, appendIndex]
      exact Nat.lt_succ_self _
    have extension : final.records.Extends after.records :=
      initial.records_prefix intrinsic offsets (i.val + 1) j (Nat.succ_le_of_lt earlier) within
    calc
      final.records.get label = after.records[label.val]'afterBound :=
        (List.IsPrefix.getElem extension afterBound).symm
      _ = (before.records ++ [record])[label.val]'(appends ▸ afterBound) :=
        List.getElem_of_eq appends afterBound
      _ = record := List.getElem_concat_length appendIndex _

theorem run_of_done (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    {terminal : Option (State n)} (reached : initial.frontier = .done terminal) :
    initial.run intrinsic offsets = some ⟨initial.records, terminal⟩ := by
  have frozen := terminal_round initial intrinsic offsets 0 q
      (Nat.zero_le q) le_rfl terminal reached
  simp only [run, frozen, runPrefix, result, reached]

private theorem runPrefix_tail (initial : TapeState n)
    (intrinsic offsets : CoordinateTape n (q + 1))
    (i : ℕ) (within : i ≤ q) :
    initial.runPrefix intrinsic offsets (i + 1) (Nat.succ_le_succ within) =
      (initial.step (intrinsic 0) (offsets 0)).runPrefix (Fin.tail intrinsic)
        (Fin.tail offsets) i within := by
  induction i with
  | zero => rfl
  | succ i ih =>
    let index : Fin q := ⟨i, by omega⟩
    change (initial.runPrefix intrinsic offsets (i + 1) (by omega)).step
        (intrinsic index.succ) (offsets index.succ) =
      ((initial.step (intrinsic 0) (offsets 0)).runPrefix (Fin.tail intrinsic) (Fin.tail offsets)
        i (by omega)).step (intrinsic index.succ) (offsets index.succ)
    rw [ih (by omega)]

theorem run_split (initial : TapeState n)
    (tapes : CoordinateTape n (q + 1) × CoordinateTape n (q + 1)) :
    initial.run tapes.1 tapes.2 =
      let parts := CoordinateTape.split n q tapes
      (initial.step parts.1.1 parts.1.2).run parts.2.1 parts.2.2 :=
  congrArg result (runPrefix_tail initial tapes.1 tapes.2 q le_rfl)

private theorem map_run_split (initial : TapeState n) (q : ℕ) :
    (CoordinateTape.law n (q + 1)).map (fun tapes ↦ initial.run tapes.1 tapes.2) =
      (ReplyCoupling.independentPair (uniformFinite (Word n))
        (uniformFinite (Word n))).bind fun first ↦
        (CoordinateTape.law n q).map fun tails ↦
          (initial.step first.1 first.2).run tails.1 tails.2 := by
  calc
    _ = ((CoordinateTape.law n (q + 1)).map (CoordinateTape.split n q)).map
        (fun parts ↦ (initial.step parts.1.1 parts.1.2).run parts.2.1 parts.2.2) := by
      rw [PMF.map_comp]
      exact congrArg (CoordinateTape.law n (q + 1)).map (funext (run_split initial))
    _ = _ := by
      rw [CoordinateTape.split_law n q]
      simp only [ReplyCoupling.independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

private theorem map_run_done (q : ℕ) (initial : TapeState n) {terminal : Option (State n)}
    (reached : initial.frontier = .done terminal) :
    (CoordinateTape.law n q).map (fun tapes ↦ initial.run tapes.1 tapes.2) =
      TrialProgram.independentCoordinatesBounded q initial.program initial.records := by
  rw [TrialProgram.independentCoordinatesBounded_eq q initial.program initial.records,
    TrialProgram.independentBounded_of_done q initial.program initial.records reached]
  have same : (fun tapes : CoordinateTape n q × CoordinateTape n q ↦ initial.run tapes.1 tapes.2) =
      Function.const _ (some (⟨initial.records, terminal⟩ : TrialResult n)) :=
    funext fun tapes ↦ initial.run_of_done tapes.1 tapes.2 reached
  rw [same, PMF.map_const]

/-- Presampling the tapes gives the same bounded law as sampling each fresh pair on demand. -/
theorem run_law : CoordinateTapeSpec.RunLaw := by
  intro n q initial
  induction q generalizing initial with
  | zero =>
    cases reached : initial.frontier with
    | done terminal => exact map_run_done 0 initial reached
    | query request resume =>
      rw [TrialProgram.independentCoordinatesBounded_eq 0 initial.program initial.records,
        TrialProgram.independentBounded_zero_of_query initial.program initial.records reached]
      change (CoordinateTape.law n 0).map (Function.const _ initial.result) = PMF.pure none
      rw [PMF.map_const, result, reached]
  | succ q ih =>
    cases reached : initial.frontier with
    | done terminal => exact map_run_done (q + 1) initial reached
    | query request resume =>
      -- The independent tails retain their law after the first pair fixes the next state.
      rw [map_run_split initial q,
        TrialProgram.independentCoordinatesBounded_succ_of_query q initial.program
          initial.records reached]
      apply congrArg (ReplyCoupling.independentPair (uniformFinite (Word n))
        (uniformFinite (Word n))).bind
      funext first
      rw [ih, step, reached]

end TapeState

end JH
