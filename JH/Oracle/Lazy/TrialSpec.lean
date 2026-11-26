/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.PermutationSpec
public import JH.Oracle.TrialProgramSpec
public import JH.Probability.DisintegrationSpec

/-!
# The law of adaptive lazy sampling

The recursive experiment with cached and fresh permutation queries.
-/

@[expose] public section

namespace JH

variable {n : ℕ}

/-- The law of the full permutation before any replies have been seen. -/
noncomputable def uniformPermutation (n : ℕ) : PMF (Permutation n) := by
  classical
  letI : Nonempty (Permutation n) := ⟨Equiv.refl _⟩
  exact PartialPermutation.uniformFinite _

theorem mem_support_uniformPermutation (permutation : Permutation n) :
    permutation ∈ (uniformPermutation n).support := by
  unfold uniformPermutation PartialPermutation.uniformFinite
  exact @mem_support_uniformPMF (Permutation n) (Fintype.ofFinite _) _ permutation

namespace Query

/-- Write the pair determined by the address and the received answer into a record. -/
def recordOfReply (request : Query n) (answer : State n) : Record n :=
  match request.direction with
  | .forward => ⟨request.address, answer, .forward⟩
  | .backward => ⟨answer, request.address, .backward⟩

theorem recordOfReply_consistent_iff (request : Query n) (answer : State n)
    (permutation : Permutation n) :
    (request.recordOfReply answer).Consistent permutation ↔ request.reply permutation = answer := by
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward => rfl
  | backward => exact eq_comm.trans permutation.symm_apply_eq.symm

end Query

namespace Transcript

/-- Append the pair revealed by a fresh query. -/
def appendReply (old : Transcript n) (request : Query n) (answer : State n) : Transcript n :=
  old ++ [request.recordOfReply answer]

private theorem consistent_iff_forall_mem (old : Transcript n) (permutation : Permutation n) :
    old.Consistent permutation ↔ ∀ record ∈ old, record.Consistent permutation := by
  constructor
  · intro consistent record present
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp present
    exact consistent ⟨i, hi⟩
  · intro agrees i
    exact agrees (old.get i) (List.getElem_mem i.isLt)

theorem consistent_appendReply_iff (old : Transcript n) (request : Query n) (answer : State n)
    (permutation : Permutation n) :
    (old.appendReply request answer).Consistent permutation ↔
      old.Consistent permutation ∧ request.reply permutation = answer := by
  simp only [appendReply, consistent_iff_forall_mem, List.forall_mem_append,
    List.forall_mem_singleton, Query.recordOfReply_consistent_iff]

/-- Condition the full permutation on agreeing with an extendible transcript. -/
noncomputable def posterior (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) :
    PMF (Permutation n) :=
  (uniformPermutation n).filter {π | old.Consistent π} (by
    obtain ⟨π, agrees⟩ := possible
    exact ⟨π, agrees, mem_support_uniformPermutation π⟩)

theorem mem_support_posterior_iff (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) (permutation : Permutation n) :
    permutation ∈ (old.posterior possible).support ↔ old.Consistent permutation := by
  simp only [posterior, PMF.mem_support_filter_iff, Set.mem_ofPred_eq,
    mem_support_uniformPermutation, and_true]

/-- A supported answer keeps the extended transcript extendible. -/
theorem appendReply_possible (old : Transcript n) (possible : ∃ π : Permutation n, old.Consistent π)
    (request : Query n) {answer : State n}
    (supported : answer ∈ ((old.posterior possible).map request.reply).support) :
    ∃ π : Permutation n, (old.appendReply request answer).Consistent π := by
  obtain ⟨π, present, correct⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact ⟨π, (old.consistent_appendReply_iff request answer π).mpr
    ⟨(old.mem_support_posterior_iff possible π).mp present, correct⟩⟩

theorem empty_possible (n : ℕ) : ∃ π : Permutation n, Transcript.Consistent π ([] : Transcript n) :=
  ⟨Equiv.refl _, fun i ↦ Fin.elim0 i⟩

/-- Forward queries use unused outputs, and backward queries use unused inputs. -/
def unusedReplies (old : Transcript n) (request : Query n) : Set (State n) :=
  match request.direction with
  | .forward => old.observedOutputsᶜ
  | .backward => old.observedInputsᶜ

end Transcript

namespace TrialProgram

/-- Run an adaptive trial by drawing each fresh answer under the current posterior. -/
noncomputable def lazyRun : TrialProgram n → (old : Transcript n) →
    (∃ π : Permutation n, old.Consistent π) → PMF (TrialResult n)
  | .done terminal, old, _ => PMF.pure ⟨old, terminal⟩
  | .query request resume, old, possible =>
      match old.cachedReply request with
      | some answer => (resume answer).lazyRun old possible
      | none =>
          ((old.posterior possible).map request.reply).bindOnSupport fun answer supported ↦
            (resume answer).lazyRun (old.appendReply request answer)
              (old.appendReply_possible possible request supported)

end TrialProgram

namespace LazyTrialSpec

/-- Conditioning on a fresh answer is equivalent to adding its record. -/
def PosteriorUpdate : Prop :=
  ∀ {n : ℕ} (old : Transcript n) (possible : ∃ π : Permutation n, old.Consistent π)
    (request : Query n) (answer : State n)
    (supported : answer ∈ ((old.posterior possible).map request.reply).support),
    ((old.posterior possible).filter (request.reply ⁻¹' {answer})
      (Probability.fiber_witness (old.posterior possible) request.reply supported)) =
      (old.appendReply request answer).posterior
        (old.appendReply_possible possible request supported)

/-- A fresh answer is uniform on the unused replies in its direction. -/
def FreshUniform : Prop :=
  ∀ {n : ℕ} (old : Transcript n) (possible : ∃ π : Permutation n, old.Consistent π)
    (request : Query n), old.cachedReply request = none →
    ∃ available : Nonempty (old.unusedReplies request),
      letI := available
      (old.posterior possible).map request.reply =
        (PartialPermutation.uniformFinite (old.unusedReplies request)).map Subtype.val

/-- The recursive query experiment agrees with drawing the conditioned full permutation first. -/
def RecursiveLaw : Prop :=
  ∀ {n : ℕ} (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π),
    program.lazyRun old possible = (old.posterior possible).map (fun π ↦ program.run π old)

/-- The lazy experiment starting from an empty transcript has the real fixed-target trial law. -/
def FixedTrialLaw : Prop :=
  ∀ {α n : ℕ} (strategy : Strategy α n) (initial : State n) (padding : Padding α n),
    (TrialProgram.ofStrategy strategy initial padding).lazyRun [] (Transcript.empty_possible n) =
      (uniformPermutation n).map (fun π ↦ fixedTargetTrial strategy π initial padding)

end LazyTrialSpec

end JH
