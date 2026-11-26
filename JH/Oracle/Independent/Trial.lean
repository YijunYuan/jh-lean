/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.Reply
public import JH.Oracle.Independent.TrialSpec

/-!
# The bounded independent-reply trial

A fresh query draws a uniform state and appends its pair. A cache hit still uses the earliest
matching pair in the transcript. Splitting a uniform reply into the intrinsic coordinate
(output rate for forward queries, input capacity for backward queries) and the XOR offset gives
the equivalent law used in `CoordinateTape`.
-/

@[expose] public section

namespace JH.TrialProgram

open PartialPermutation (uniformFinite)

variable {n : ℕ}

private theorem runBoundedWith_succ_of_query (replyLaw : Query n → PMF (State n)) (fuel : ℕ)
    (program : TrialProgram n) (old : Transcript n) {request : Query n}
    {resume : State n → TrialProgram n} (reached : program.nextFresh old = .query request resume) :
    runBoundedWith replyLaw (fuel + 1) program old = (replyLaw request).bind fun answer ↦
      runBoundedWith replyLaw fuel (resume answer) (old.appendReply request answer) := by
  rw [runBoundedWith, reached]

theorem independentBounded_of_done (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    {terminal : Option (State n)} (reached : program.nextFresh old = .done terminal) :
    independentBounded fuel program old = PMF.pure (some ⟨old, terminal⟩) := by
  cases fuel <;> simp only [independentBounded, runBoundedWith, reached]

theorem independentBounded_zero_of_query (program : TrialProgram n) (old : Transcript n)
    {request : Query n} {resume : State n → TrialProgram n}
    (reached : program.nextFresh old = .query request resume) :
    independentBounded 0 program old = PMF.pure none := by
  rw [independentBounded, runBoundedWith, reached]

/-- At a fresh frontier, draw a uniform reply, log it, and spend one unit of fuel. -/
theorem independentBounded_succ_of_query (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    {request : Query n} {resume : State n → TrialProgram n}
    (reached : program.nextFresh old = .query request resume) :
    independentBounded (fuel + 1) program old =
      (uniformFinite (State n)).bind fun answer ↦
        independentBounded fuel (resume answer) (old.appendReply request answer) := by
  exact runBoundedWith_succ_of_query (fun _ ↦ uniformFinite (State n)) fuel program old reached

theorem independentCoordinatesBounded_succ_of_query (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n) {request : Query n} {resume : State n → TrialProgram n}
    (reached : program.nextFresh old = .query request resume) :
    independentCoordinatesBounded (fuel + 1) program old =
      (ReplyCoupling.independentPair (uniformFinite (Word n)) (uniformFinite (Word n))).bind
        fun coords ↦
          let answer := request.replyCoords.symm coords
          independentCoordinatesBounded fuel (resume answer) (old.appendReply request answer) := by
  simp only [independentCoordinatesBounded]
  rw [runBoundedWith_succ_of_query _ fuel program old reached, PMF.bind_map]
  rfl

/-- Two independently sampled words reconstruct the same uniform reply in either direction. -/
theorem independentCoordinatesBounded_eq : IndependentTrialSpec.CoordinateLaw := by
  intro n fuel program old
  unfold independentCoordinatesBounded independentBounded
  congr 1
  funext request
  exact Query.uniform_reply_from_coords request

private theorem support_of_done (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (result : TrialResult n) {terminal : Option (State n)}
    (reached : program.nextFresh old = .done terminal)
    (supported : some result ∈ (independentBounded fuel program old).support) :
    result.records.Extends old ∧ result.records.length ≤ old.length + fuel := by
  rw [independentBounded_of_done fuel program old reached] at supported
  have result_eq := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
  subst result
  exact ⟨⟨[], List.append_nil _⟩, Nat.le_add_right _ _⟩

/-- A completed outcome preserves the supplied log as a prefix and appends at most `fuel` pairs. -/
theorem independentBounded_support : IndependentTrialSpec.BudgetSupport := by
  intro n fuel program old result supported
  induction fuel generalizing program old with
  | zero =>
    cases reached : program.nextFresh old with
    | done terminal => exact support_of_done 0 program old result reached supported
    | query request resume =>
      rw [independentBounded_zero_of_query program old reached] at supported
      simp at supported
  | succ fuel ih =>
    cases reached : program.nextFresh old with
    | done terminal => exact support_of_done (fuel + 1) program old result reached supported
    | query request resume =>
      rw [independentBounded_succ_of_query fuel program old reached] at supported
      obtain ⟨answer, _, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨extension, budget⟩ :=
        ih (resume answer) (old.appendReply request answer) continued
      have added : (old.appendReply request answer).Extends old :=
        ⟨[request.recordOfReply answer], rfl⟩
      have length_added : (old.appendReply request answer).length = old.length + 1 := by
        simp [Transcript.appendReply]
      exact ⟨added.trans extension, by omega⟩

end JH.TrialProgram
