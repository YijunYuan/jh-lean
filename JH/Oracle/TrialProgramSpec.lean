/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.ExperimentSpec

/-!
# Compile and replay a fixed-permutation trial

Compilation and replay of a fixed-permutation trial.
-/

@[expose] public section

namespace JH

namespace Transcript

/-- Look up an answer using either endpoint of the pairs already recorded. -/
def cachedReply {n : ℕ} (old : Transcript n) (request : Query n) : Option (State n) :=
  (old.find? request.hasAddress).map request.replyFrom

end Transcript

/-- A terminating query program whose verification accesses are represented by the same
constructor as the strategy's own accesses. -/
inductive TrialProgram (n : ℕ) where
  | done (terminal : Option (State n))
  | query (request : Query n) (resume : State n → TrialProgram n)

namespace TrialProgram

variable {α n : ℕ}

/-- Execute each query against a fixed full permutation and log each fresh access. -/
def run (permutation : Permutation n) : TrialProgram n → Transcript n → TrialResult n
  | .done terminal, old => ⟨old, terminal⟩
  | .query request resume, old =>
      (resume (request.reply permutation)).run permutation (old.logAccess permutation request)

/-- Turn verification of a list of blocks into forward queries. -/
def verify : State n → List (Word n) → TrialProgram n
  | state, [] => .done (some state)
  | state, block :: rest =>
      .query ⟨.forward, permInput state block⟩ (fun answer ↦
        verify (feedForward answer block) rest)

/-- Continue the strategy with verification from the specified initial state if it submits a
candidate. -/
def ofStrategy (strategy : Strategy α n) (initial : State n) (padding : Padding α n) :
    TrialProgram n :=
  match strategy with
  | .halt none => .done none
  | .halt (some message) => verify initial (padding.encode message)
  | .query request resume =>
      .query request (fun answer ↦ ofStrategy (resume answer) initial padding)

end TrialProgram

namespace TrialProgramSpec

/-- Compiling a fixed-target strategy preserves both its list of actual records and its
verification terminal state. -/
def FixedTrial : Prop :=
  ∀ {α n : ℕ} (strategy : Strategy α n) (permutation : Permutation n) (initial : State n)
    (padding : Padding α n),
    (TrialProgram.ofStrategy strategy initial padding).run permutation [] =
      fixedTargetTrial strategy permutation initial padding

/-- Among permutations consistent with the supplied records, the fiber of a realized result
consists exactly of the permutations consistent with all its records. -/
def ReplayCylinder : Prop :=
  ∀ {n : ℕ} (program : TrialProgram n) (permutation other : Permutation n) (old : Transcript n),
    old.Consistent permutation →
      (old.Consistent other ∧ program.run other old = program.run permutation old ↔
        (program.run permutation old).records.Consistent other)

end TrialProgramSpec

end JH
