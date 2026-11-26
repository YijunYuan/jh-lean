/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Experiment
public import JH.Oracle.TrialProgramSpec

/-!
# Compile and replay a fixed-permutation trial

`TrialProgram.ofStrategy` compiles the strategy and the verification of its submission into one
query program. Replay identifies the permutations yielding a realized run with the permutations
agreeing with its transcript. This works for adaptive strategies because each logged answer
fixes the continuation at that query.
-/

@[expose] public section

namespace JH

namespace Transcript

variable {n : ℕ}

theorem consistent_of_extends {old new : Transcript n} {permutation : Permutation n}
    (extension : new.Extends old) (consistent : new.Consistent permutation) :
    old.Consistent permutation := by
  rw [consistent_iff_forall_record] at consistent ⊢
  intro record present
  exact consistent record (List.IsPrefix.subset extension present)

theorem cachedReply_eq_none_iff (old : Transcript n) (request : Query n) :
    old.cachedReply request = none ↔ old.any request.hasAddress = false := by
  simp only [cachedReply, Option.map_eq_none_iff, List.find?_eq_none, List.any_eq_false]

theorem cachedReply_eq_reply (old : Transcript n) (permutation : Permutation n) (request : Query n)
    (consistent : old.Consistent permutation) {answer : State n}
    (hit : old.cachedReply request = some answer) : answer = request.reply permutation := by
  obtain ⟨record, found, rfl⟩ := Option.map_eq_some_iff.mp hit
  exact cache_reply permutation request record
    ((consistent_iff_forall_record old permutation).mp consistent record
      (List.mem_of_find?_eq_some found)) (List.find?_some found)

/-- Agreement with the transcript after a query fixes the answer and reproduces its log update. -/
theorem logAccess_replay (old : Transcript n) (permutation other : Permutation n)
    (request : Query n) (consistent : old.Consistent permutation)
    (agrees : (old.logAccess permutation request).Consistent other) :
    request.reply other = request.reply permutation ∧
      old.logAccess other request = old.logAccess permutation request := by
  let logged := old.logAccess permutation request
  obtain ⟨record, present, matched⟩ := logAccess_has_match old permutation request
  have correct := (consistent_iff_forall_record logged permutation).mp
    (logAccess_consistent old permutation request consistent) record present
  have alsoCorrect := (consistent_iff_forall_record logged other).mp agrees record present
  have sameAnswer := (cache_reply other request record alsoCorrect matched).symm.trans
    (cache_reply permutation request record correct matched)
  refine ⟨sameAnswer, ?_⟩
  have sameRecord : request.record other = request.record permutation := by
    rcases request with ⟨direction, address⟩
    cases direction <;> simp only [Query.record, sameAnswer]
  unfold logAccess
  rw [sameRecord]

end Transcript

namespace TrialProgram

variable {α n : ℕ}

/-- A cache hit under a consistent permutation resumes the program with no new record. -/
theorem run_query_of_hit (permutation : Permutation n) (old : Transcript n) (request : Query n)
    (resume : State n → TrialProgram n) (consistent : old.Consistent permutation)
    {answer : State n} (hit : old.cachedReply request = some answer) :
    (TrialProgram.query request resume).run permutation old =
      (resume answer).run permutation old := by
  have known : old.any request.hasAddress = true := by
    obtain ⟨record, found, _⟩ := Option.map_eq_some_iff.mp hit
    exact List.any_eq_true.mpr ⟨record, List.mem_of_find?_eq_some found, List.find?_some found⟩
  rw [run, ← old.cachedReply_eq_reply permutation request consistent hit]
  simp only [Transcript.logAccess, known, ite_true]

/-- A cache miss appends the new pair before resuming the program on the true reply. -/
theorem run_query_of_miss (permutation : Permutation n) (old : Transcript n) (request : Query n)
    (resume : State n → TrialProgram n) (miss : old.cachedReply request = none) :
    (TrialProgram.query request resume).run permutation old =
      (resume (request.reply permutation)).run permutation (old ++
        [request.record permutation]) := by
  have fresh := (old.cachedReply_eq_none_iff request).mp miss
  simp only [run, Transcript.logAccess, fresh, Bool.false_eq_true, ite_false]

theorem verify_run (permutation : Permutation n) (initial : State n) (blocks : List (Word n))
    (old : Transcript n) :
    (verify initial blocks).run permutation old =
      let (terminal, records) := verifyBlocks permutation initial blocks old
      ⟨records, some terminal⟩ := by
  induction blocks generalizing initial old with
  | nil => rfl
  | cons block rest ih =>
    exact ih (compress permutation initial block)
      (old.logAccess permutation ⟨.forward, permInput initial block⟩)

private theorem ofStrategy_run_from (strategy : Strategy α n) (permutation : Permutation n)
    (initial : State n) (padding : Padding α n) (old : Transcript n) :
    (ofStrategy strategy initial padding).run permutation old =
      let (candidate, records) := strategy.run permutation old
      match candidate with
      | none => ⟨records, none⟩
      | some message =>
        let (terminal, final) := verifyBlocks permutation initial (padding.encode message) records
        ⟨final, some terminal⟩ := by
  induction strategy generalizing old with
  | halt candidate =>
    cases candidate with
    | none => rfl
    | some message => exact verify_run permutation initial (padding.encode message) old
  | query request _ ih =>
    exact ih (request.reply permutation) (old.logAccess permutation request)

/-- Compiling the strategy and its verification preserves the complete trial result. -/
theorem ofStrategy_run : TrialProgramSpec.FixedTrial := by
  intro α n strategy permutation initial padding
  exact ofStrategy_run_from strategy permutation initial padding []

theorem run_extends (program : TrialProgram n) (permutation : Permutation n) (old : Transcript n) :
    (program.run permutation old).records.Extends old := by
  induction program generalizing old with
  | done => exact ⟨[], List.append_nil _⟩
  | query request _ ih =>
    exact List.IsPrefix.trans (old.logAccess_extends permutation request)
      (ih (request.reply permutation) (old.logAccess permutation request))

theorem run_consistent (program : TrialProgram n) (permutation : Permutation n) (old : Transcript n)
    (consistent : old.Consistent permutation) :
    (program.run permutation old).records.Consistent permutation := by
  induction program generalizing old with
  | done => exact consistent
  | query request _ ih =>
    exact ih (request.reply permutation) (old.logAccess permutation request)
      (old.logAccess_consistent permutation request consistent)

/-- Any permutation consistent with the realized final records reproduces the entire run. -/
theorem run_replay (program : TrialProgram n) (permutation other : Permutation n)
    (old : Transcript n)
    (consistent : old.Consistent permutation)
    (agrees : (program.run permutation old).records.Consistent other) :
    program.run other old = program.run permutation old := by
  induction program generalizing old with
  | done => rfl
  | query request resume ih =>
    -- The final log contains this query's pair, so it fixes both the reply and the next log.
    have extension := (resume (request.reply permutation)).run_extends permutation
      (old.logAccess permutation request)
    obtain ⟨sameAnswer, sameLog⟩ := old.logAccess_replay permutation other request consistent
      (Transcript.consistent_of_extends extension agrees)
    rw [run, run, sameAnswer, sameLog]
    exact ih (request.reply permutation) (old.logAccess permutation request)
      (old.logAccess_consistent permutation request consistent) agrees

/-- The fiber of a realized run is precisely the set of completions of its transcript. -/
theorem run_consistent_replay_iff : TrialProgramSpec.ReplayCylinder := by
  intro n program permutation other old consistent
  constructor
  · rintro ⟨oldConsistent, equal⟩
    rw [← equal]
    exact program.run_consistent other old oldConsistent
  · intro agrees
    exact ⟨Transcript.consistent_of_extends (program.run_extends permutation old) agrees,
      program.run_replay permutation other old consistent agrees⟩

theorem run_eq_iff_consistent (program : TrialProgram n) (permutation other : Permutation n)
    (old : Transcript n) (consistent : old.Consistent permutation)
    (otherConsistent : old.Consistent other) :
    program.run other old = program.run permutation old ↔
      (program.run permutation old).records.Consistent other := by
  simpa only [otherConsistent, true_and] using
    run_consistent_replay_iff program permutation other old consistent

end TrialProgram

end JH
