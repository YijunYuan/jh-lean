/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.ReplySpec
public import JH.Oracle.TrialProgramSpec
public import JH.PreimageSpec

/-!
# A target obtained by hashing a uniform message

Reduction for a target obtained by hashing a uniformly sampled message. The paper mentions this
additional result in the introduction.
-/

@[expose] public section

namespace JH

open scoped ENNReal

universe u v

variable {α n : ℕ} {Tape : Type u}

theorem message_nonempty_of_pos (positive : 0 < α) : Nonempty (Message α) :=
  ⟨⟨⟨0, positive⟩, 0⟩⟩

/-- The candidate message and its verification result in the fixed-original experiment. -/
structure SecondPreimageResult (α n : ℕ) where
  /-- The candidate submitted by the strategy, if any. -/
  candidate : Option (Message α)
  /-- The transcript and terminal state from checking that candidate. -/
  trial : TrialResult n

/-- A distinct candidate verifies to the digest of the original message. -/
def SecondPreimageResult.Success (result : SecondPreimageResult α n) (original : Message α)
    (target : Word n) : Prop :=
  result.candidate ≠ some original ∧ result.trial.Success target

/-- Give the adversary the fixed original message, its digest, and the permutation pairs used
to hash it. Start the adversary and candidate verification with those pairs cached. -/
def secondPreimageTrial (select : Message α → Word n → Transcript n → Strategy α n)
    (permutation : Permutation n) (initial : State n) (padding : Padding α n)
    (original : Message α) : SecondPreimageResult α n :=
  let old := (verifyBlocks permutation initial (padding.encode original) []).2
  let target := hash permutation initial padding original
  let strategy := select original target old
  ⟨(strategy.run permutation old).1,
    (TrialProgram.ofStrategy strategy initial padding).run permutation old⟩

namespace RandomTarget

/-- The independent draws that stay fixed when comparing choices of original message or target. -/
noncomputable def tapePermutationLaw (n : ℕ) (tapes : PMF Tape) : PMF (Tape × Permutation n) :=
  ReplyCoupling.independentPair tapes (uniformPMF (Permutation n))

/-- Probability mass of the outcomes satisfying a predicate. -/
noncomputable def eventMass {A : Type u} (law : PMF A) (event : A → Prop) : ℝ≥0∞ := by
  classical
  exact (law.map fun outcome ↦ decide (event outcome)) true

/-- Probability of an event evaluated on two independently sampled inputs. -/
noncomputable def choiceMass {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (event : A → B → Prop) : ℝ≥0∞ := by
  classical
  exact (draws.bind fun draw ↦ choices.map fun choice ↦ decide (event draw choice)) true

/-- The fixed tape and permutation lead to successful verification at the chosen digest. -/
def accepts (initial : State n) (padding : Padding α n)
    (adversary : Word n → Tape → Strategy α n) (draw : Tape × Permutation n)
    (target : Word n) : Prop :=
  (fixedTargetTrial (adversary target draw.1) draw.2 initial padding).Success target

end RandomTarget

/-- Success probability against a fixed original message. Its trajectory is disclosed after
the permutation draw. The tape is independent of the permutation. -/
noncomputable def fixedMessageSecondPreimageSuccessProbability (original : Message α)
    (initial : State n) (padding : Padding α n) (tapes : PMF Tape)
    (adversary : Message α → Word n → Transcript n → Tape → Strategy α n) : ℝ :=
  (RandomTarget.eventMass (RandomTarget.tapePermutationLaw n tapes) fun draw ↦
    (secondPreimageTrial (fun message target old ↦ adversary message target old draw.1)
      draw.2 initial padding original).Success original
        (hash draw.2 initial padding original)).toReal

/-- An independent uniform target is passed to the same adversary family. -/
noncomputable def uniformTargetSuccessProbability (initial : State n) (padding : Padding α n)
    (tapes : PMF Tape) (adversary : Word n → Tape → Strategy α n) : ℝ :=
  (RandomTarget.choiceMass (RandomTarget.tapePermutationLaw n tapes)
    (uniformPMF (Word n)) (RandomTarget.accepts initial padding adversary)).toReal

/-- The original is uniform independently of the tape and permutation. The adversary gets
its digest and uses the same real fixed-target trial for oracle access and verification. -/
noncomputable def randomTargetSuccessProbability (positive : 0 < α) (initial : State n)
    (padding : Padding α n) (tapes : PMF Tape)
    (adversary : Word n → Tape → Strategy α n) : ℝ :=
  letI : Nonempty (Message α) := message_nonempty_of_pos positive
  (RandomTarget.choiceMass (RandomTarget.tapePermutationLaw n tapes)
    (uniformPMF (Message α)) fun draw original ↦
      RandomTarget.accepts initial padding adversary draw
        (hash draw.2 initial padding original)).toReal

namespace RandomTargetSpec

/-- There are 2^(α+1) − 2 nonempty bit strings of length at most α. -/
def MessageCard : Prop :=
  ∀ α : ℕ, Fintype.card (Message α) = 2 ^ (α + 1) - 2

/-- An adversary using only the digest is unaffected by the additional information and
initial cache in the second-preimage trial. -/
def TargetOnlySPR : Prop :=
  ∀ {α n : ℕ} (initial : State n) (padding : Padding α n)
    (adversary : Word n → Strategy α n) (permutation : Permutation n) (original : Message α),
    let target := hash permutation initial padding original
    (secondPreimageTrial (fun _ digest _ ↦ adversary digest)
      permutation initial padding original).Success original target ↔
      ((adversary target).run permutation []).1 ≠ some original ∧
        (fixedTargetTrial (adversary target) permutation initial padding).Success target

/-- A uniform bound for every fixed digest also bounds success for an independently uniform
digest, as in Section 2.2. -/
def AveragingFixedTarget : Prop :=
  ∀ {α n : ℕ} {Tape : Type u} (initial : State n) (padding : Padding α n) (tapes : PMF Tape)
    (adversary : Word n → Tape → Strategy α n) (ε_pre : ℝ),
    (∀ target, fixedTargetSuccessProbability target initial padding
      (tapes.map (adversary target)) ≤ ε_pre) →
      uniformTargetSuccessProbability initial padding tapes adversary ≤ ε_pre

/-- The reduction needs the average independent-target bound and a uniform bound for the
second-preimage adversary derived by ignoring the original message and its trajectory. -/
def AveragedReduction : Prop :=
  ∀ {α n : ℕ} {Tape : Type u} (positive : 0 < α) (initial : State n) (padding : Padding α n)
    (tapes : PMF Tape) (adversary : Word n → Tape → Strategy α n) (ε_spr ε_pre : ℝ),
    (∀ original, fixedMessageSecondPreimageSuccessProbability original initial padding tapes
      (fun _ target _ tape ↦ adversary target tape) ≤ ε_spr) →
    uniformTargetSuccessProbability initial padding tapes adversary ≤ ε_pre →
      randomTargetSuccessProbability positive initial padding tapes adversary ≤
        ε_spr + ((2 : ℝ) ^ n / ((2 ^ (α + 1) - 2 : ℕ) : ℝ)) * ε_pre

/-- The uniform-message reduction with the two bounds taken uniformly over original messages and
fixed targets. -/
def Reduction : Prop :=
  ∀ {α n : ℕ} {Tape : Type u} (positive : 0 < α) (initial : State n) (padding : Padding α n)
    (tapes : PMF Tape) (adversary : Word n → Tape → Strategy α n) (ε_spr ε_pre : ℝ),
    (∀ original, fixedMessageSecondPreimageSuccessProbability original initial padding tapes
      (fun _ target _ tape ↦ adversary target tape) ≤ ε_spr) →
    (∀ target, fixedTargetSuccessProbability target initial padding
      (tapes.map (adversary target)) ≤ ε_pre) →
      randomTargetSuccessProbability positive initial padding tapes adversary ≤
        ε_spr + ((2 : ℝ) ^ n / ((2 ^ (α + 1) - 2 : ℕ) : ℝ)) * ε_pre

end RandomTargetSpec

end JH
