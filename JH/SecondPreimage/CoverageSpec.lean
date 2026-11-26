/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.SecondPreimage.OriginalPhaseSpec
public import JH.SecondPreimage.TraceSpec

/-!
# Replay and path extraction after original-trace disclosure

Replay original and candidate compressions against the same independent-trial cache.
-/

@[expose] public section

namespace JH

namespace Transcript

/-- The first logged pair for an input determines all forward replies at that input. -/
def forwardReply {n : ℕ} (final : Transcript n) (input : State n) : State n :=
  (final.cachedReply ⟨.forward, input⟩).getD (0, 0)

end Transcript

namespace SecondPreimageCoverageSpec

open SecondPreimageTrace

/-- The original observation is the trace of the earliest-match reply function in any
extension. Collision-free capacities also determine its original log exactly. -/
def OriginalReplay : Prop :=
  ∀ {n : ℕ} (replyLaw : PMF (State n)) (initial : State n) (blocks : List (Word n))
    (observation : OriginalObservation n) (final : Transcript n),
    observation ∈ (OriginalPhase.sample replyLaw initial blocks [] []).support →
    ¬ OriginalPhase.HasCapacityCollision observation → final.Extends observation.records →
    let reply := final.forwardReply
    observation.states = states reply initial blocks ∧
      observation.records = originalRecords reply initial blocks ∧
      observation.terminal = runWith reply initial blocks

/-- A supported acceptance yields the distinct candidate, its run, and exact record
coverage under the earliest-match reply function of the same final log. -/
def AcceptedCandidate : Prop :=
  ∀ {α n : ℕ} (original : Message α) (target : Word n) (initial : State n) (padding : Padding α n)
    (strategy : Strategy α n) (fuel : ℕ) (old : Transcript n) (result : TrialResult n),
    some result ∈ (TrialProgram.independentBounded fuel
      (TrialProgram.verifyDistinct original target initial padding strategy) old).support →
    result.terminal.isSome = true →
    result.records.Extends old ∧ ∃ candidate : Message α, candidate ≠ original ∧
      let reply := result.records.forwardReply
      let terminal := runWith reply initial (padding.encode candidate)
      result.terminal = some terminal ∧ terminal.1 = target ∧
        Covers reply result.records initial (padding.encode candidate)

/-- After a collision-free original observation, each supported acceptance gives a
nonempty path in the graph of subsequent records, with the original auxiliary boundaries. -/
def AcceptedPath : Prop :=
  ∀ {α n : ℕ} (replyLaw : PMF (State n)) (initial : State n) (padding : Padding α n)
    (original : Message α) (observation : OriginalObservation n)
    (strategy : Strategy α n) (fuel : ℕ) (result : TrialResult n),
    observation ∈ (OriginalPhase.sample replyLaw initial (padding.encode original) [] []).support →
    ¬ OriginalPhase.HasCapacityCollision observation →
    some result ∈ (TrialProgram.independentBounded fuel
      (TrialProgram.verifyDistinct original observation.terminal.1 initial padding strategy)
      observation.records).support →
    result.terminal.isSome = true →
    let initials := observation.states.toFinset
    let later := result.records.drop observation.records.length
    ∃ (start : ↥initials) (target : State n), target.1 ∈ observation.states.map Prod.fst ∧
      ∃ path : Walk (Transcript.edge later initials) (.inr start) (.inl target), path.labels ≠ []

end SecondPreimageCoverageSpec

end JH
