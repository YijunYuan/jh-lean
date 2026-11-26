/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.Permutation
public import JH.Oracle.Lazy.TrialSpec
public import JH.Oracle.TrialProgram
public import JH.Probability.Disintegration

/-!
# The law of adaptive lazy sampling

The posterior is uniform on permutations consistent with the observed records. A cache hit
continues with the same posterior. For a fresh query, adding the realized pair is exactly
conditioning on that answer. Induction on the query program then gives equality of laws for the
complete trial in Section 3.2.
-/

@[expose] public section

namespace JH

open scoped ENNReal

variable {n : ℕ}

private theorem filter_congr {α : Type*} (p : PMF α) {s t : Set α} (equal : s = t)
    (hs : ∃ x ∈ s, x ∈ p.support) (ht : ∃ x ∈ t, x ∈ p.support) :
    p.filter s hs = p.filter t ht := by
  subst t
  rfl

private theorem map_congr_on_support {α β : Type*} (p : PMF α) {f g : α → β}
    (agrees : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  simp only [PMF.map_apply]
  refine tsum_congr fun a ↦ ?_
  by_cases present : a ∈ p.support
  · rw [agrees a present]
  · have zero : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr present
    simp [zero]

namespace Query

theorem record_eq_recordOfReply (request : Query n) (permutation : Permutation n) :
    request.record permutation = request.recordOfReply (request.reply permutation) := by
  rcases request with ⟨direction, address⟩
  cases direction <;> rfl

end Query

namespace Transcript

/-- Conditioning on a supported answer gives the posterior of the transcript with that
answer appended. -/
theorem posterior_update : LazyTrialSpec.PosteriorUpdate := by
  intro n old possible request answer supported
  have intersection : {π : Permutation n | old.Consistent π} ∩ (request.reply ⁻¹' {answer}) =
      {π | (old.appendReply request answer).Consistent π} :=
    Set.ext fun π ↦ (old.consistent_appendReply_iff request answer π).symm
  unfold posterior
  exact (Probability.filter_filter (uniformPermutation n) _ _ _ _).trans
    (filter_congr _ intersection _ _)

theorem posterior_eq_conditionedUniform (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) (witness : Permutation n)
    (agrees : old.Consistent witness) :
    old.posterior possible = (old.partialPermutation witness agrees).conditionedUniform := by
  unfold posterior PartialPermutation.conditionedUniform uniformPermutation
  apply filter_congr
  exact Set.ext fun π ↦ (partialPermutation_extends_iff old witness agrees π).symm

/-- A cache miss has the uniform law on unused replies for the query direction. -/
theorem fresh_uniform : LazyTrialSpec.FreshUniform := by
  intro n old possible request miss
  obtain ⟨witness, agrees⟩ := possible
  let known := old.partialPermutation witness agrees
  have noMatch : ∀ record ∈ old, request.hasAddress record ≠ true :=
    List.any_eq_false.mp ((old.cachedReply_eq_none_iff request).mp miss)
  rw [old.posterior_eq_conditionedUniform ⟨witness, agrees⟩ witness agrees]
  rcases request with ⟨direction, address⟩
  cases direction with
  | forward =>
    let x : known.UnusedInput := ⟨address, by
      rintro ⟨i, hi⟩
      exact noMatch (old.get i) (List.getElem_mem i.isLt) (decide_eq_true hi)⟩
    let : Nonempty known.UnusedOutput := ⟨known.forward x known.complete⟩
    exact ⟨‹Nonempty known.UnusedOutput›, PartialPermutation.forward_uniform known x⟩
  | backward =>
    let y : known.UnusedOutput := ⟨address, by
      rintro ⟨i, hi⟩
      exact noMatch (old.get i) (List.getElem_mem i.isLt) (decide_eq_true hi)⟩
    let : Nonempty known.UnusedInput := ⟨known.backward y known.complete⟩
    exact ⟨‹Nonempty known.UnusedInput›, PartialPermutation.backward_uniform known y⟩

theorem posterior_empty (n : ℕ) : Transcript.posterior ([] : Transcript n) (empty_possible n) =
    uniformPermutation n := by
  have emptyEvent : {π : Permutation n | Transcript.Consistent π []} = Set.univ :=
    Set.eq_univ_of_forall fun _ i ↦ Fin.elim0 i
  apply PMF.ext
  intro π
  rw [posterior, PMF.filter_apply]
  simp only [emptyEvent, Set.indicator_univ, PMF.tsum_coe, inv_one, mul_one]

end Transcript

namespace TrialProgram

/-- Sampling each fresh reply from its posterior gives the law of drawing one compatible
permutation and running the entire program against it. -/
theorem lazyRun_eq_map : LazyTrialSpec.RecursiveLaw := by
  intro n program old possible
  induction program generalizing old with
  | done terminal =>
    let result : TrialResult n := ⟨old, terminal⟩
    change PMF.pure result = (old.posterior possible).map (fun _ ↦ result)
    exact (PMF.map_const (old.posterior possible) result).symm
  | query request resume ih =>
    cases cache : old.cachedReply request with
    | some answer =>
      simp only [lazyRun, cache, ih]
      -- Every permutation in the posterior gives the cached answer.
      apply map_congr_on_support
      intro π hπ
      exact (run_query_of_hit π old request resume
        ((old.mem_support_posterior_iff possible π).mp hπ)
        cache).symm
    | none =>
      simp only [lazyRun, cache]
      -- Split the full-permutation law by its answer, then use the updated posterior in each fiber.
      refine Eq.trans ?_
        (Probability.map_bindOnSupport_filter (old.posterior possible) request.reply _)
      apply congrArg ((old.posterior possible).map request.reply).bindOnSupport
      funext answer supported
      rw [ih answer, ← Transcript.posterior_update old possible request answer supported]
      apply map_congr_on_support
      intro π hπ
      have answered : request.reply π = answer := ((PMF.mem_support_filter_iff _).mp hπ).1
      have sameRecord : request.record π = request.recordOfReply answer :=
        (request.record_eq_recordOfReply π).trans (congrArg request.recordOfReply answered)
      rw [run_query_of_miss π old request resume cache, answered, sameRecord]
      rfl

/-- The lazy experiment starting from an empty transcript has the real fixed-target trial law.
-/
theorem lazyRun_fixedTarget : LazyTrialSpec.FixedTrialLaw := by
  intro α n strategy initial padding
  rw [lazyRun_eq_map (ofStrategy strategy initial padding) [] (Transcript.empty_possible n),
    Transcript.posterior_empty]
  exact congrArg (fun result ↦ (uniformPermutation n).map result)
    (funext fun π ↦ ofStrategy_run strategy π initial padding)

end TrialProgram

end JH
