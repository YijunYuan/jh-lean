/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelProofs
public import JH.Oracle.ExperimentSpec

/-!
# Fixed-permutation trials

A transcript logs the first access to each pair of the fixed permutation. Verification extends
this same transcript and accounts for every compression of a submitted message. `trial_witness`
turns successful verification into a path from the virtual initial vertex to the target column.
-/

@[expose] public section

namespace JH

/-- A consistent cached pair gives the permutation answer in either query direction. -/
theorem cache_reply : ExperimentSpec.CacheReply := by
  intro n permutation ⟨direction, address⟩ record consistent hasAddress
  change permutation record.input = record.output at consistent
  cases direction with
  | forward =>
    exact consistent.symm.trans (congrArg permutation (of_decide_eq_true hasAddress))
  | backward =>
    exact (permutation.eq_symm_apply).mpr (consistent.trans (of_decide_eq_true hasAddress))

variable {n : ℕ}

private theorem query_record_consistent (permutation : Permutation n) (query : Query n) :
    (query.record permutation).Consistent permutation := by
  rcases query with ⟨_ | _, address⟩ <;> simp [Query.record, Query.reply, Record.Consistent]

private theorem record_matches_query (permutation : Permutation n) (query : Query n) :
    query.hasAddress (query.record permutation) = true := by
  rcases query with ⟨_ | _, address⟩ <;> simp [Query.record, Query.hasAddress]

namespace Transcript

theorem logAccess_extends (old : Transcript n) (permutation : Permutation n)
    (request : Query n) : (old.logAccess permutation request).Extends old := by
  unfold logAccess
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem logAccess_has_match (old : Transcript n) (permutation : Permutation n)
    (query : Query n) :
    ∃ record ∈ old.logAccess permutation query, query.hasAddress record = true := by
  by_cases cached : old.any query.hasAddress = true
  · simpa [logAccess, cached] using List.any_eq_true.mp cached
  · exact ⟨query.record permutation, by simp [logAccess, cached],
      record_matches_query permutation query⟩

theorem consistent_iff_forall_record (transcript : Transcript n) (permutation : Permutation n) :
    transcript.Consistent permutation ↔
      ∀ record ∈ transcript, record.Consistent permutation :=
  (List.forall_mem_iff_get (p := Record.Consistent permutation)).symm

theorem logAccess_consistent (old : Transcript n) (permutation : Permutation n)
    (request : Query n) (consistent : old.Consistent permutation) :
    (old.logAccess permutation request).Consistent permutation := by
  unfold logAccess
  split
  · exact consistent
  · rw [consistent_iff_forall_record, List.forall_mem_append]
    exact ⟨(consistent_iff_forall_record old permutation).mp consistent,
      by simpa using query_record_consistent permutation request⟩

end Transcript

private theorem strategy_consistent {α : ℕ} (strategy : Strategy α n)
    (permutation : Permutation n) (old : Transcript n) (consistent : old.Consistent permutation) :
    (strategy.run permutation old).2.Consistent permutation := by
  induction strategy generalizing old with
  | halt => exact consistent
  | query request _ ih =>
    exact ih (request.reply permutation) (old.logAccess permutation request)
      (old.logAccess_consistent permutation request consistent)

/-- Verification computes the ordinary block iteration and covers it with a consistent log. -/
theorem verify_blocks : ExperimentSpec.Verification := by
  intro n permutation initial blocks old consistent
  induction blocks generalizing initial old with
  | nil => exact ⟨rfl, ⟨[], List.append_nil _⟩, consistent, trivial⟩
  | cons block blocks ih =>
    let request : Query n := ⟨.forward, permInput initial block⟩
    let logged := old.logAccess permutation request
    let final := verifyBlocks permutation (compress permutation initial block) blocks logged
    have stepConsistent := old.logAccess_consistent permutation request consistent
    obtain ⟨terminal_eq, logPrefix, finalConsistent, coversRest⟩ :=
      ih (compress permutation initial block) logged stepConsistent
    change final.1 = _ ∧ final.2.Extends old ∧ final.2.Consistent permutation ∧
      final.2.Covers permutation initial (block :: blocks)
    refine ⟨terminal_eq, List.IsPrefix.trans (old.logAccess_extends permutation request) logPrefix,
      finalConsistent, ⟨?_, coversRest⟩⟩
    -- The block's matching pair may already be in the cache. Its label survives later appends.
    obtain ⟨record, present, matched⟩ := old.logAccess_has_match permutation request
    have finalPresent : record ∈ final.2 := List.IsPrefix.subset logPrefix present
    obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp finalPresent
    exact ⟨⟨i, hi⟩, (congrArg Record.input equal).trans (of_decide_eq_true matched)⟩

/-- The actual records of a successful fixed-target trial support a path to the target. -/
theorem trial_witness : ExperimentSpec.TrialWitness := by
  intro α n strategy permutation initial padding target
  dsimp only
  have initialConsistent : Transcript.Consistent permutation ([] : Transcript n) :=
    fun i ↦ Fin.elim0 i
  have consistent := strategy_consistent strategy permutation [] initialConsistent
  cases result : strategy.run permutation [] with
  | mk candidate records =>
    rw [result] at consistent
    cases candidate with
    | none => simp [fixedTargetTrial, result, TrialResult.Success, consistent]
    | some message =>
      unfold fixedTargetTrial
      rw [result]
      obtain ⟨terminal_eq, _, verifiedConsistent, covers⟩ :=
        verify_blocks permutation initial (padding.encode message) records consistent
      refine ⟨verifiedConsistent, ?_⟩
      intro success
      have capacity_eq :
          (verifyBlocks permutation initial (padding.encode message) records).1.1 = target :=
        Option.some.inj success
      have hash_eq : hash permutation initial padding message = target := by
        unfold hash
        rw [← terminal_eq]
        exact capacity_eq
      exact fixed_target_success_witness permutation _ verifiedConsistent initial padding message
        target covers hash_eq

end JH
