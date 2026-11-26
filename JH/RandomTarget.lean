/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.TrialProgram
public import JH.RandomTargetSpec
public import Mathlib.Algebra.BigOperators.Fin

/-!
# A target obtained by hashing a uniform message

In the uniform-message reduction the adversary sees the digest alone. Returning a different
message is a second-preimage event. For each fixed tape and permutation, the originals that are
returned successfully inject into the set of successful target digests, yielding the ratio of
the digest space size to the message space size.
-/

@[expose] public section

namespace JH

open scoped ENNReal BigOperators

universe u v w

variable {α n : ℕ} {Tape : Type u}

/-- There are `2 ^ (α + 1) - 2` binary messages of positive length at most `α`. -/
theorem message_card : RandomTargetSpec.MessageCard := by
  intro α
  change Fintype.card ((i : Fin α) × Word (i.val + 1)) = _
  rw [Fintype.card_sigma]
  simp_rw [word_card _, pow_succ]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k ↦ 2 ^ k)]
  have geometric := geom_sum_mul_add (1 : ℕ) α
  simp only [one_add_one_eq_two, mul_one] at geometric
  omega

/-- For a fixed permutation, every query takes the same continuation under either
initial cache. The cache determines which accesses enter the record log, and both runs
submit the same candidate. -/
theorem Strategy.run_candidate_eq (strategy : Strategy α n) (permutation : Permutation n)
    (left right : Transcript n) :
    (strategy.run permutation left).1 = (strategy.run permutation right).1 := by
  induction strategy generalizing left right with
  | halt => rfl
  | query request _ ih =>
    exact ih (request.reply permutation) (left.logAccess permutation request)
      (right.logAccess permutation request)

private theorem trialProgram_run_terminal_eq (program : TrialProgram n)
    (permutation : Permutation n)
    (left right : Transcript n) :
    (program.run permutation left).terminal = (program.run permutation right).terminal := by
  induction program generalizing left right with
  | done => rfl
  | query request _ ih =>
    exact ih (request.reply permutation) (left.logAccess permutation request)
      (right.logAccess permutation request)

/-- For a strategy selected only by the digest, target-only second-preimage success is
fixed-target success with a distinct returned message. -/
theorem secondPreimageTrial_target_only : RandomTargetSpec.TargetOnlySPR := by
  intro α n initial padding adversary permutation original
  dsimp only [secondPreimageTrial, SecondPreimageResult.Success]
  let old := (verifyBlocks permutation initial (padding.encode original) []).2
  let strategy := adversary (hash permutation initial padding original)
  -- The permutation supplies the same replies to both executions, so the strategy and verifier
  -- follow the same continuations. The fresh-record counts depend on the initial cache.
  have candidate := strategy.run_candidate_eq permutation old []
  have terminal := trialProgram_run_terminal_eq
    (TrialProgram.ofStrategy strategy initial padding) permutation old []
  rw [TrialProgram.ofStrategy_run strategy permutation initial padding] at terminal
  change ((strategy.run permutation old).1 ≠ some original ∧
      ((TrialProgram.ofStrategy strategy initial padding).run permutation old).Success _) ↔
    ((strategy.run permutation []).1 ≠ some original ∧
      (fixedTargetTrial strategy permutation initial padding).Success _)
  rw [TrialResult.Success, TrialResult.Success, candidate, terminal]

namespace RandomTarget

private theorem eventMass_ne_top {A : Type u} (law : PMF A) (event : A → Prop) :
    eventMass law event ≠ ⊤ :=
  PMF.apply_ne_top _ _

private theorem choiceMass_ne_top {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (event : A → B → Prop) : choiceMass draws choices event ≠ ⊤ :=
  PMF.apply_ne_top _ _

private theorem choiceMass_sum {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (event : A → B → Prop) :
    choiceMass draws choices event = ∑' draw, draws draw * eventMass choices (event draw) := by
  rw [choiceMass, PMF.bind_apply]
  rfl

private theorem choiceMass_swap {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (event : A → B → Prop) :
    choiceMass draws choices event = choiceMass choices draws fun choice draw ↦
      event draw choice := by
  unfold choiceMass PMF.map
  rw [PMF.bind_comm draws choices]
  rfl

private theorem choiceMass_toReal_le {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (event : A → B → Prop) (bound : ℝ)
    (each : ∀ choice, (eventMass draws fun draw ↦ event draw choice).toReal ≤ bound) :
    (choiceMass draws choices event).toReal ≤ bound := by
  obtain ⟨choice, _⟩ := choices.support_nonempty
  have nonnegative : 0 ≤ bound := le_trans ENNReal.toReal_nonneg (each choice)
  have mass_le (choice : B) : (eventMass draws fun draw ↦ event draw choice) ≤
      ENNReal.ofReal bound := by
    rw [← ENNReal.ofReal_toReal (eventMass_ne_top draws fun draw ↦ event draw choice)]
    exact ENNReal.ofReal_le_ofReal (each choice)
  have total : choiceMass draws choices event ≤ ENNReal.ofReal bound := by
    rw [choiceMass_swap, choiceMass_sum]
    calc
      _ ≤ ∑' choice, choices choice * ENNReal.ofReal bound :=
        tsum_le_tsum fun choice ↦ mul_le_mul_right (mass_le choice) (choices choice)
      _ = _ := by rw [ENNReal.tsum_mul_right, choices.tsum_coe, one_mul]
  simpa only [ENNReal.toReal_ofReal nonnegative]
    using ENNReal.toReal_mono ENNReal.ofReal_ne_top total

private theorem eventMass_split {A : Type u} (law : PMF A) (accept chosen : A → Prop) :
    eventMass law accept = (eventMass law fun a ↦ accept a ∧ chosen a) +
      (eventMass law fun a ↦ accept a ∧ ¬chosen a) := by
  simp only [eventMass, PMF.map_apply, ← tsum_add]
  apply tsum_congr
  intro a
  by_cases success : accept a <;> by_cases selected : chosen a <;> simp [success, selected]

private theorem choiceMass_split {A : Type u} {B : Type v} (draws : PMF A) (choices : PMF B)
    (accept chosen : A → B → Prop) :
    choiceMass draws choices accept =
      (choiceMass draws choices fun a b ↦ accept a b ∧ chosen a b) +
      (choiceMass draws choices fun a b ↦ accept a b ∧ ¬chosen a b) := by
  simp only [choiceMass_sum, ← tsum_add, ← mul_add]
  apply tsum_congr
  intro draw
  rw [← eventMass_split choices (accept draw) (chosen draw)]

private theorem uniform_event_mul_card {A : Type u} [Fintype A] [Nonempty A] (event : A → Prop) :
    eventMass (uniformPMF A) event * (Fintype.card A : ℝ≥0∞) = {a | event a}.ncard := by
  classical
  have preimage : (fun a ↦ decide (event a)) ⁻¹' {true} = {a | event a} := by ext a; simp
  rw [eventMass, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, preimage,
    toOuterMeasure_uniformPMF_apply, ENNReal.div_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (by simp), ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

private theorem choiceMass_scaled_le {A : Type u} {B : Type v} {C : Type w}
    (draws : PMF A) (left : PMF B) (right : PMF C) (acceptLeft : A → B → Prop)
    (acceptRight : A → C → Prop) (factorLeft factorRight : ℝ≥0∞)
    (pointwise : ∀ draw, eventMass left (acceptLeft draw) * factorLeft ≤
      eventMass right (acceptRight draw) * factorRight) :
    choiceMass draws left acceptLeft * factorLeft ≤
      choiceMass draws right acceptRight * factorRight := by
  simp only [choiceMass_sum, ← ENNReal.tsum_mul_right, mul_assoc]
  exact tsum_le_tsum fun draw ↦ mul_le_mul_right (pointwise draw) (draws draw)

theorem fixedTarget_eq_eventMass (initial : State n) (padding : Padding α n) (tapes : PMF Tape)
    (adversary : Word n → Tape → Strategy α n) (target : Word n) :
    fixedTargetSuccessProbability target initial padding (tapes.map (adversary target)) =
      (eventMass (tapePermutationLaw n tapes) fun draw ↦
        accepts initial padding adversary draw target).toReal := by
  simp only [fixedTargetSuccessProbability, eventMass, tapePermutationLaw,
    ReplyCoupling.independentPair, accepts, PMF.bind_map, PMF.map_bind,
      PMF.map_comp, Function.comp_def]
  rfl

/-- A bound uniform in the fixed target also bounds the average over an independent uniform
target. -/
theorem average_fixed_target : RandomTargetSpec.AveragingFixedTarget := by
  intro α n Tape initial padding tapes adversary bound each
  unfold uniformTargetSuccessProbability
  apply choiceMass_toReal_le
  intro target
  rw [← fixedTarget_eq_eventMass]
  exact each target

/-- The target-only strategy returns the specific original message whose digest it was given. -/
private def returnsOriginal (initial : State n) (padding : Padding α n)
    (adversary : Word n → Tape → Strategy α n) (draw : Tape × Permutation n)
    (original : Message α) : Prop :=
  ((adversary (hash draw.2 initial padding original) draw.1).run draw.2 []).1 = some original

private theorem same_return_count_le (initial : State n) (padding : Padding α n)
    (adversary : Word n → Tape → Strategy α n) (draw : Tape × Permutation n) :
    {original : Message α |
      accepts initial padding adversary draw (hash draw.2 initial padding original) ∧
        returnsOriginal initial padding adversary draw original}.ncard ≤
      {target | accepts initial padding adversary draw target}.ncard := by
  apply Set.ncard_le_ncard_of_injOn (hash draw.2 initial padding)
  · intro original accepted
    exact accepted.1
  · intro a ha b hb sameHash
    -- With the tape and permutation fixed, the digest determines a single returned message.
    have chosenA := ha.2
    have chosenB := hb.2
    unfold returnsOriginal at chosenA chosenB
    rw [sameHash] at chosenA
    exact Option.some.inj (chosenA.symm.trans chosenB)

/-- For targets obtained by hashing an independent uniform message, assume a second-preimage
bound `ε_spr` uniform in the original and a bound `ε_pre` averaged over independent uniform
targets. In both comparisons the strategy depends only on its random tape and the digest.
Success is at most
$\varepsilon_{\rm spr} + (N/D)\varepsilon_{\rm pre}$, with `N = 2 ^ n` and
`D = 2 ^ (α + 1) - 2`. -/
theorem randomTarget_reduction_of_average : RandomTargetSpec.AveragedReduction := by
  intro α n Tape positive initial padding tapes adversary ε_spr ε_pre secondBound averageBound
  let : Nonempty (Message α) := message_nonempty_of_pos positive
  let draws := tapePermutationLaw n tapes
  let messages := uniformPMF (Message α)
  let targets := uniformPMF (Word n)
  let success (draw : Tape × Permutation n) (original : Message α) :=
    accepts initial padding adversary draw (hash draw.2 initial padding original)
  let same := returnsOriginal initial padding adversary
  let originalSuccess := choiceMass draws messages fun draw original ↦
    success draw original ∧ same draw original
  let differentSuccess := choiceMass draws messages fun draw original ↦
    success draw original ∧ ¬same draw original
  let fixedSuccess := choiceMass draws targets (accepts initial padding adversary)
  -- First fix the original message. Returning a distinct message with the same digest is
  -- a second-preimage event for the strategy that uses only the digest.
  have different_le : differentSuccess.toReal ≤ ε_spr := by
    apply choiceMass_toReal_le
    intro original
    have event_eq :
        (fun draw ↦ success draw original ∧ ¬same draw original) =
          fun draw ↦ (secondPreimageTrial (fun _ target _ ↦ adversary target draw.1)
            draw.2 initial padding original).Success original
              (hash draw.2 initial padding original) := by
      funext draw
      exact propext (and_comm.trans
        (secondPreimageTrial_target_only initial padding (fun target ↦ adversary target draw.1)
          draw.2 original).symm)
    rw [event_eq]
    exact secondBound original
  -- Convert uniform event masses to counts for each fixed draw before averaging over draws.
  have count_le : originalSuccess * (Fintype.card (Message α) : ℝ≥0∞) ≤
      fixedSuccess * (Fintype.card (Word n) : ℝ≥0∞) := by
    apply choiceMass_scaled_le
    intro draw
    dsimp only [messages, targets]
    rw [uniform_event_mul_card, uniform_event_mul_card]
    dsimp only [success, same]
    exact_mod_cast same_return_count_le initial padding adversary draw
  have finite : fixedSuccess * (Fintype.card (Word n) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (choiceMass_ne_top _ _ _) (by simp)
  have scaled : originalSuccess.toReal * (Fintype.card (Message α) : ℝ) ≤
      fixedSuccess.toReal * (Fintype.card (Word n) : ℝ) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      using ENNReal.toReal_mono finite count_le
  have message_pos : (0 : ℝ) < Fintype.card (Message α) := by
    exact_mod_cast Fintype.card_pos
  have same_le : originalSuccess.toReal ≤
      ((Fintype.card (Word n) : ℝ) / (Fintype.card (Message α) : ℝ)) * ε_pre := by
    calc
      _ ≤ fixedSuccess.toReal * (Fintype.card (Word n) : ℝ) / (Fintype.card (Message α) : ℝ) :=
        (le_div_iff₀ message_pos).mpr scaled
      _ = ((Fintype.card (Word n) : ℝ) / (Fintype.card (Message α) : ℝ)) * fixedSuccess.toReal := by
        rw [div_mul_eq_mul_div, mul_comm fixedSuccess.toReal]
      _ ≤ _ := mul_le_mul_of_nonneg_left averageBound (by positivity)
  have split : choiceMass draws messages success = originalSuccess + differentSuccess :=
    choiceMass_split draws messages success same
  change (choiceMass draws messages success).toReal ≤ _
  rw [split, ENNReal.toReal_add (choiceMass_ne_top _ _ _) (choiceMass_ne_top _ _ _), add_comm]
  have total := add_le_add different_le same_le
  simpa only [message_card α, word_card n, Nat.cast_pow, Nat.cast_ofNat] using total

/-- For a target obtained by hashing a uniform message, a uniform second-preimage bound for each
original and a preimage bound for each fixed target give the random-message-target bound of
`JH.RandomTarget.randomTarget_reduction_of_average`. -/
theorem randomTarget_reduction : RandomTargetSpec.Reduction := by
  intro α n Tape positive initial padding tapes adversary ε_spr ε_pre secondBound fixedBound
  exact randomTarget_reduction_of_average positive initial padding tapes adversary ε_spr ε_pre
    secondBound (average_fixed_target initial padding tapes adversary ε_pre fixedBound)

end RandomTarget

end JH
