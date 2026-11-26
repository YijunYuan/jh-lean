/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelProofs
public import JH.Oracle.Coupling.FreshStepSpec
public import JH.Oracle.Coupling.Reply

/-!
# The separation hazard at a common fresh query

At a common extendible transcript, `Transcript.coupleFresh` pairs the permutation's posterior
reply with an independent uniform reply. A forward query forbids observed outputs and a
backward query forbids observed inputs. The number of such addresses is at most the transcript
length.
-/

@[expose] public section

namespace JH

open scoped ENNReal

theorem state_space_card (n : ℕ) : Nat.card (State n) = (2 ^ n) ^ 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, word_card n, pow_two]

namespace Transcript

variable {n : ℕ}

theorem observedInputs_card_le (old : Transcript n) : Nat.card old.observedInputs ≤ old.length := by
  simpa only [observedInputs, Set.range, Nat.card_fin] using
    Finite.card_range_le (fun i : old.Label ↦ (old.get i).input)

theorem observedOutputs_card_le (old : Transcript n) :
    Nat.card old.observedOutputs ≤ old.length := by
  simpa only [observedOutputs, Set.range, Nat.card_fin] using
    Finite.card_range_le (fun i : old.Label ↦ (old.get i).output)

end Transcript

/-- The one-step coupling has the posterior permutation reply and the uniform reply as marginals. -/
theorem fresh_step_marginals : FreshStepSpec.Marginals := by
  intro n old witness consistent request miss
  let known := old.partialPermutation witness consistent
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward =>
    let query : known.UnusedInput := ⟨address, old.forward_miss address miss⟩
    exact ⟨PartialPermutation.coupleForward_permutation_marginal known query,
      known.coupleForward_map_snd query⟩
  | backward =>
    let query : known.UnusedOutput := ⟨address, old.backward_miss address miss⟩
    exact ⟨PartialPermutation.coupleBackward_permutation_marginal known query,
      known.coupleBackward_map_snd query⟩

/-- Supported pairs agree exactly when the uniform proposal is an unused reply. -/
theorem fresh_step_support : FreshStepSpec.CoupledSupport := by
  intro n old witness consistent request miss replies supported
  let known := old.partialPermutation witness consistent
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward =>
    exact known.coupleForward_support ⟨address, old.forward_miss address miss⟩
      _ supported
  | backward =>
    exact known.coupleBackward_support ⟨address, old.backward_miss address miss⟩
      _ supported

/-- The conditional separation probability is at most the number of old records divided by the
`N²` possible replies, the per-access estimate in equation (8). -/
theorem fresh_step_hazard : FreshStepSpec.Hazard := by
  intro n old witness consistent request miss
  let known := old.partialPermutation witness consistent
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward =>
    let query : known.UnusedInput := ⟨address, old.forward_miss address miss⟩
    change (known.coupleForward query).toOuterMeasure _ ≤ _
    rw [known.coupleForward_disagreement, state_space_card]
    exact ENNReal.div_le_div_right (by exact_mod_cast old.observedOutputs_card_le) _
  | backward =>
    let query : known.UnusedOutput := ⟨address, old.backward_miss address miss⟩
    change (known.coupleBackward query).toOuterMeasure _ ≤ _
    rw [known.coupleBackward_disagreement, state_space_card]
    exact ENNReal.div_le_div_right (by exact_mod_cast old.observedInputs_card_le) _

end JH
