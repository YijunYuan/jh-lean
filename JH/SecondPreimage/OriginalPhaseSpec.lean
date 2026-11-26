/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.TrialSpec
public import JH.SecondPreimageSpec

/-!
# Disclosure of the original trace and the capacity collision bound

Extract the original-message phase by disintegrating the bounded independent trial.
-/

@[expose] public section

namespace JH

/-- The terminal state, disclosed records, and state trajectory of the original message. -/
structure OriginalObservation (n : ℕ) where
  /-- Final state after the original message. -/
  terminal : State n
  /-- Disclosed permutation pairs from the original evaluation. -/
  records : Transcript n
  /-- Visited states in traversal order, including the initial state. -/
  states : List (State n)

namespace OriginalPhase

variable {n : ℕ}

/-- Finish the original message before running the adaptive continuation. Every fresh reply
uses the same law as the encompassing independent trial. -/
noncomputable def sample (replyLaw : PMF (State n)) :
    State n → List (Word n) → Transcript n → List (State n) → PMF (OriginalObservation n)
  | state, [], old, previous => PMF.pure ⟨state, old, (state :: previous).reverse⟩
  | state, block :: rest, old, previous =>
    let request : Query n := ⟨.forward, permInput state block⟩
    match old.cachedReply request with
    | some reply => sample replyLaw (feedForward reply block) rest old (state :: previous)
    | none => replyLaw.bind fun reply ↦
      sample replyLaw (feedForward reply block) rest (old.appendReply request reply)
        (state :: previous)

/-- The original trajectory repeats a capacity, the event bounded in (9). -/
def HasCapacityCollision (observation : OriginalObservation n) : Prop :=
  ¬ (observation.states.map Prod.fst).Nodup

end OriginalPhase

namespace OriginalPhaseSpec

/-- Split the experiment at disclosure, preserving the cache and subtracting the exact number
of new original-phase records from the combined budget. With distinct capacities, this leaves
$Q$ when the initial budget is $Q + \ell(M)$. -/
def ContinuationLaw : Prop :=
  ∀ {n : ℕ} (replyLaw : PMF (State n)) (fuel : ℕ) (state : State n) (blocks : List (Word n))
    (old : Transcript n) (previous : List (State n))
    (next : State n → Transcript n → List (State n) → TrialProgram n),
    blocks.length ≤ fuel →
    TrialProgram.runBoundedWith (fun _ ↦ replyLaw) fuel
      (TrialProgram.observeOriginal state blocks old previous next) old =
      (OriginalPhase.sample replyLaw state blocks old previous).bind fun observation ↦
        TrialProgram.runBoundedWith (fun _ ↦ replyLaw)
          (fuel + old.length - observation.records.length)
          (next observation.terminal observation.records observation.states) observation.records

/-- There are at most ℓ original-phase fresh accesses for ℓ blocks. -/
def Budget : Prop :=
  ∀ {n : ℕ} (replyLaw : PMF (State n)) (state : State n) (blocks : List (Word n))
    (old : Transcript n) (previous : List (State n)) (observation : OriginalObservation n),
    observation ∈ (OriginalPhase.sample replyLaw state blocks old previous).support →
    observation.records.Extends old ∧ observation.records.length ≤ old.length + blocks.length ∧
      observation.states.length = previous.length + blocks.length + 1

/-- Equation (9) for the actual original-message phase under independent replies. -/
def CollisionTail : Prop :=
  ∀ {n : ℕ} (state : State n) (blocks : List (Word n)),
    (PMF.toOuterMeasure (OriginalPhase.sample (PartialPermutation.uniformFinite (State n))
      state blocks [] []) {observation | OriginalPhase.HasCapacityCollision observation}).toReal ≤
      (blocks.length : ℝ) * ((blocks.length : ℝ) + 1) / (2 * (2 : ℝ) ^ n)

/-- On a collision-free original phase every block contributes one fresh record. -/
def CollisionFreeLength : Prop :=
  ∀ {n : ℕ} (replyLaw : PMF (State n)) (state : State n) (blocks : List (Word n))
    (observation : OriginalObservation n),
    observation ∈ (OriginalPhase.sample replyLaw state blocks [] []).support →
    ¬ OriginalPhase.HasCapacityCollision observation →
    observation.records.length = blocks.length

end OriginalPhaseSpec

end JH
