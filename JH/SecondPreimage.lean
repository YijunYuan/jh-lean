/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Experiment
public import JH.Oracle.Lazy.Trial
public import JH.Oracle.TrialProgram
public import JH.SecondPreimageSpec

/-!
# The compiled second-preimage experiment

The query program evaluates the fixed original message $M$ and gives the adversary $M$,
its digest, and its transcript $T_M$, as in the second-preimage game in Section 2.2. It then
runs the selected strategy and accepts a distinct candidate with the same digest. The
compiled program can run with either permutation or independent responses.

`JH.TrialProgram.second_preimage_program` identifies the compiled experiment's records and
acceptance when replies come from a fixed permutation. The full program is coupled with budget
$Q + \ell(M)$ in `JH.second_preimage_transfer`, where $Q = q + L_\alpha$ covers the adversary
and candidate evaluation after disclosure.
-/

@[expose] public section

namespace JH

namespace TrialProgram

variable {α n : ℕ}

/-- Changing the program's final output preserves the record log for a fixed permutation. -/
theorem mapTerminal_run (f : Option (State n) → Option (State n)) (program : TrialProgram n)
    (permutation : Permutation n) (old : Transcript n) :
    (program.mapTerminal f).run permutation old =
      { program.run permutation old with
        terminal := f (program.run permutation old).terminal } := by
  induction program generalizing old with
  | done terminal => rfl
  | query request resume ih =>
      exact ih (request.reply permutation) (old.logAccess permutation request)

/-- Observing the original message under a fixed permutation produces the verification state and
transcript, with the states passed in chronological order. -/
theorem observe_original_run : SecondPreimageSpec.ObserveOriginal := by
  intro n permutation state blocks
  induction blocks generalizing state with
  | nil =>
      intro old previous next
      simp [observeOriginal, verifyBlocks]
  | cons block rest ih =>
      intro old previous next
      let request : Query n := ⟨.forward, permInput state block⟩
      let answer := request.reply permutation
      -- Only a cache miss appends a record in either run.
      have logged : (match old.cachedReply request with
          | none => old.appendReply request answer
          | some _ => old) = old.logAccess permutation request := by
        cases hit : old.cachedReply request with
        | none =>
            have fresh := (old.cachedReply_eq_none_iff request).mp hit
            simp only [Transcript.logAccess, fresh, Bool.false_eq_true, ite_false,
              Transcript.appendReply, answer, Query.record_eq_recordOfReply]
        | some reply =>
            have present : old.any request.hasAddress = true := by
              by_contra absent
              have no := (old.cachedReply_eq_none_iff request).mpr (Bool.of_not_eq_true absent)
              rw [hit] at no
              contradiction
            simp only [Transcript.logAccess, present, ite_true]
      change (observeOriginal (compress permutation state block) rest
          (match old.cachedReply request with
          | none => old.appendReply request answer
          | some _ => old) (state :: previous) next).run permutation
          (old.logAccess permutation request) = _
      rw [logged]
      simp only [verifyBlocks, List.scanl_cons]
      simpa only [List.reverse_cons, List.singleton_append, List.append_assoc] using
        ih (compress permutation state block) (old.logAccess permutation request)
          (state :: previous) next

/-- The distinct-candidate check filters the verified result by message inequality and the
target digest, preserving its records. -/
theorem verify_distinct_run (original : Message α) (target : Word n) (initial : State n)
    (padding : Padding α n) (strategy : Strategy α n) (permutation : Permutation n)
      (old : Transcript n) :
    let result := (ofStrategy strategy initial padding).run permutation old
    (verifyDistinct original target initial padding strategy).run permutation old =
      { result with terminal := if (strategy.run permutation old).1 ≠ some original ∧
        result.terminal.map Prod.fst = some target
        then result.terminal else none } := by
  induction strategy generalizing old with
  | halt candidate =>
      cases candidate with
      | none => simp [verifyDistinct, ofStrategy, run, Strategy.run]
      | some candidate =>
          rw [verifyDistinct, mapTerminal_run]
          simp only [ofStrategy, Strategy.run, ne_eq, Option.some.injEq]
  | query request resume ih =>
      exact ih (request.reply permutation) (old.logAccess permutation request)

/-- The compiled program logs the second-preimage experiment and accepts exactly when it
succeeds. -/
theorem second_preimage_program : SecondPreimageSpec.ProgramLaw := by
  intro α n select permutation initial padding original
  let originalRun := verifyBlocks permutation initial (padding.encode original) []
  let target := hash permutation initial padding original
  -- The terminal capacity of the original phase is the digest given to the strategy.
  have target_eq : originalRun.1.1 = target :=
    congrArg Prod.fst ((verify_blocks permutation initial (padding.encode original) []
      (by intro label; exact Fin.elim0 label)).1)
  have compiledRun : (ofSecondPreimage select initial padding original).run permutation [] =
      (verifyDistinct original target initial padding (select original target originalRun.2)).run
        permutation originalRun.2 := by
    unfold ofSecondPreimage
    rw [observe_original_run]
    change (verifyDistinct original originalRun.1.1 initial padding
      (select original originalRun.1.1 originalRun.2)).run permutation originalRun.2 = _
    rw [target_eq]
  dsimp only
  rw [compiledRun, verify_distinct_run]
  let strategy := select original target originalRun.2
  let result := (ofStrategy strategy initial padding).run permutation originalRun.2
  let good := (strategy.run permutation originalRun.2).1 ≠ some original ∧
    result.terminal.map Prod.fst = some target
  let : Decidable good := by dsimp only [good]; infer_instance
  change result.records = result.records ∧
    ((if good then result.terminal else none).isSome = true ↔ good)
  refine ⟨rfl, ?_⟩
  by_cases accepted : good
  · have verified := accepted.2
    cases ht : result.terminal with
    | none => simp [ht] at verified
    | some state => simp [accepted]
  · simp [accepted]

end TrialProgram

end JH
