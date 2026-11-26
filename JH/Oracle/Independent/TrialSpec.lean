/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.ReplySpec
public import JH.Oracle.FreshFrontierSpec
public import JH.Oracle.Lazy.TrialSpec

/-!
# The bounded independent-reply trial

Trials with independent replies and a finite fresh-query budget.
-/

@[expose] public section

namespace JH

namespace TrialProgram

open PartialPermutation (uniformFinite)

variable {n : ℕ}

/-- Execute a bounded program using the supplied law at each fresh query. If the transcript
has repeated endpoints, cache hits use the first matching record in transcript order. -/
noncomputable def runBoundedWith (replyLaw : Query n → PMF (State n)) (fuel : ℕ)
    (program : TrialProgram n) (old : Transcript n) : PMF (Option (TrialResult n)) :=
  match program.nextFresh old with
  | .done terminal => PMF.pure (some ⟨old, terminal⟩)
  | .query request resume =>
      match fuel with
      | 0 => PMF.pure none
      | remaining + 1 =>
          (replyLaw request).bind fun answer ↦
            runBoundedWith replyLaw remaining (resume answer) (old.appendReply request answer)
termination_by structural fuel

/-- Draw a uniform state at every fresh query, retaining every proposed reply. -/
noncomputable def independentBounded (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n) : PMF (Option (TrialResult n)) :=
  runBoundedWith (fun _ ↦ uniformFinite (State n)) fuel program old

/-- Independently draw the random coordinate and the shift for each fresh query. -/
noncomputable def independentCoordinatesBounded (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n) : PMF (Option (TrialResult n)) :=
  runBoundedWith (fun request ↦
    (ReplyCoupling.independentPair (uniformFinite (Word n)) (uniformFinite (Word n))).map
      request.replyCoords.symm) fuel program old

end TrialProgram

namespace IndependentTrialSpec

/-- Sampling the two coordinates gives the same law for the entire bounded trial. -/
def CoordinateLaw : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n),
    TrialProgram.independentCoordinatesBounded fuel program old =
      TrialProgram.independentBounded fuel program old

/-- A completed independent trial retains all the initial records and adds at most one
per unit of fuel. The initial and final transcripts may contain repeated endpoints. -/
def BudgetSupport : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old : Transcript n) (result : TrialResult n),
    some result ∈ (TrialProgram.independentBounded fuel program old).support →
      result.records.Extends old ∧ result.records.length ≤ old.length + fuel

end IndependentTrialSpec

end JH
