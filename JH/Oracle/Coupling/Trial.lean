/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.TrialSpec
public import JH.Oracle.Independent.Trial
public import JH.Probability.Separation

/-!
# Coupling complete adaptive trials

While fresh replies agree, the trials share a program continuation and transcript. At the first
mismatch, each trial continues with its own reply and the remaining fuel. Projection recovers
the exact law of each experiment. Summing the hazards along common histories yields equation
(8).
-/

@[expose] public section

namespace JH

open scoped ENNReal BigOperators
open PartialPermutation (uniformFinite)

variable {n : ℕ}

private theorem bindOnSupport_congr {A B : Type*} {p q : PMF A} (same : p = q)
    {f : ∀ a ∈ p.support, PMF B} {g : ∀ a ∈ q.support, PMF B}
    (agrees : ∀ a hp hq, f a hp = g a hq) : p.bindOnSupport f = q.bindOnSupport g := by
  subst q
  apply congrArg p.bindOnSupport
  funext a supported
  exact agrees a supported supported

private theorem map_bindOnSupport {A B C : Type*} (p : PMF A)
    (f : ∀ a ∈ p.support, PMF B) (view : B → C) :
    (p.bindOnSupport f).map view = p.bindOnSupport fun a h ↦ (f a h).map view := by
  calc
    _ = (p.bindOnSupport f).bindOnSupport (fun b _ ↦ PMF.pure (view b)) :=
      (PMF.bindOnSupport_eq_bind (p.bindOnSupport f) (PMF.pure ∘ view)).symm
    _ = _ := by
      rw [PMF.bindOnSupport_bindOnSupport]
      simp only [PMF.bindOnSupport_eq_bind, PMF.map, Function.comp_def]

/-- Project a joint draw followed by supported continuations onto one reply law. -/
private theorem bindOnSupport_project {A B C D : Type*} (p : PMF A)
    (joint : ∀ a ∈ p.support, PMF B) (view : B → C) (project : A → D) (reply : PMF D)
    (replyLaw : p.map project = reply) (next : ∀ d ∈ reply.support, PMF C)
    (localLaw : ∀ a ha hp, (joint a ha).map view = next (project a) hp) :
    (p.bindOnSupport joint).map view = reply.bindOnSupport next := by
  rw [map_bindOnSupport]
  let propose : ∀ a ∈ p.support, PMF D := fun a _ ↦ PMF.pure (project a)
  have proposed : p.bindOnSupport propose = reply :=
    (PMF.bindOnSupport_eq_bind p (PMF.pure ∘ project)).trans replyLaw
  let lift : ∀ d ∈ (p.bindOnSupport propose).support, PMF C :=
    fun d h ↦ next d (proposed ▸ h)
  calc
    _ = (p.bindOnSupport propose).bindOnSupport lift := by
      rw [PMF.bindOnSupport_bindOnSupport]
      apply congrArg p.bindOnSupport
      funext a ha
      change (joint a ha).map view = (PMF.pure (project a)).bindOnSupport _
      rw [PMF.pure_bindOnSupport]
      exact localLaw a ha _
    _ = _ := bindOnSupport_congr proposed (fun _ _ _ ↦ rfl)

private theorem afterSeparation_map_permutation (p q : PMF (Option (TrialResult n))) :
    (CoupledResult.afterSeparation p q).map CoupledResult.permutation = p := by
  rw [CoupledResult.afterSeparation, PMF.map_comp]
  exact ReplyCoupling.independentPair_map_fst p q

private theorem afterSeparation_map_independent (p q : PMF (Option (TrialResult n))) :
    (CoupledResult.afterSeparation p q).map CoupledResult.independent = q := by
  rw [CoupledResult.afterSeparation, PMF.map_comp]
  exact ReplyCoupling.independentPair_map_snd p q

private theorem afterSeparation_support {p q : PMF (Option (TrialResult n))}
    {result : CoupledResult n} (supported : result ∈ (CoupledResult.afterSeparation p q).support) :
    result.separated = true := by
  obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rfl

private theorem of_agreed_support {outcome : Option (TrialResult n)} {result : CoupledResult n}
    (supported : result ∈ (PMF.pure (CoupledResult.agreed outcome)).support) :
    result.permutation = result.independent := by
  obtain rfl := (PMF.mem_support_pure_iff _ _).mp supported
  rfl

private theorem agreed_separation_mass (outcome : Option (TrialResult n)) :
    Separation.mass (PMF.pure (CoupledResult.agreed outcome)) CoupledResult.separated = 0 := by
  apply Separation.mass_eq_zero_of_good_on_support
  intro result supported
  obtain rfl := (PMF.mem_support_pure_iff _ _).mp supported
  rfl

private theorem mass_bindOnSupport_le {A B : Type*} (p : PMF A) (next : ∀ a ∈ p.support, PMF B)
    (separates : Set A) (bad : B → Bool) (allowance : ℝ≥0∞)
    (localBound : ∀ a h, a ∉ separates → Separation.mass (next a h) bad ≤ allowance) :
    Separation.mass (p.bindOnSupport next) bad ≤ p.toOuterMeasure separates + allowance := by
  rw [Separation.mass_eq_toOuterMeasure, PMF.toOuterMeasure_bindOnSupport_apply]
  calc
    _ ≤ ∑' a, (separates.indicator p a + p a * allowance) := by
      apply tsum_le_tsum
      intro a
      by_cases zero : p a = 0
      · simp [zero]
      · simp only [dite_eq_right zero, ← Separation.mass_eq_toOuterMeasure]
        by_cases different : a ∈ separates
        · rw [Set.indicator_of_mem different]
          calc
            _ ≤ p a * 1 := mul_le_mul_right (((next a zero).map bad).coe_le_one true) (p a)
            _ ≤ _ := by simp
        · rw [Set.indicator_of_notMem different, zero_add]
          exact mul_le_mul_right (localBound a zero different) (p a)
    _ = _ := by
      simp only [tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul,
        PMF.toOuterMeasure_apply]

private theorem sum_shift (length fuel : ℕ) (K : ℝ≥0∞) :
    (length : ℝ≥0∞) / K + (∑ i ∈ Finset.range fuel, ((length + 1 + i : ℕ) : ℝ≥0∞) / K) =
      ∑ i ∈ Finset.range (fuel + 1), ((length + i : ℕ) : ℝ≥0∞) / K := by
  rw [Finset.sum_range_succ', Nat.add_zero, add_comm ((length : ℝ≥0∞) / K)]
  apply congrArg (fun sum ↦ sum + (length : ℝ≥0∞) / K)
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_right_comm, Nat.add_assoc]

namespace TrialProgram

private theorem coupledBounded_of_done (fuel : ℕ) (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) {terminal : Option (State n)}
    (reached : program.nextFresh old = .done terminal) :
    coupledBounded fuel program old possible =
      PMF.pure (CoupledResult.agreed (some ⟨old, terminal⟩)) := by
  rw [coupledBounded]
  split <;> rename_i current
  · cases current.symm.trans reached
    rfl
  · cases current.symm.trans reached

private theorem coupledBounded_zero_of_query (program : TrialProgram n) (old : Transcript n)
    (possible : ∃ π : Permutation n, old.Consistent π) {request : Query n}
    {resume : State n → TrialProgram n} (reached : program.nextFresh old = .query request resume) :
    coupledBounded 0 program old possible = PMF.pure (CoupledResult.agreed none) := by
  rw [coupledBounded]
  split <;> rename_i current
  · cases current.symm.trans reached
  · rfl

private theorem coupledBounded_succ_of_query (fuel : ℕ) (program : TrialProgram n)
    (old : Transcript n) (possible : ∃ π : Permutation n, old.Consistent π) {request : Query n}
    {resume : State n → TrialProgram n} (reached : program.nextFresh old = .query request resume) :
    coupledBounded (fuel + 1) program old possible =
      let miss := nextFresh_miss program old request resume reached
      (old.coupledReplies possible request miss).bindOnSupport fun replies supported ↦
        let nextOld := old.appendReply request replies.1
        let nextPossible := old.coupledReply_possible possible request miss replies supported
        if replies.1 = replies.2 then
          coupledBounded fuel (resume replies.1) nextOld nextPossible
        else
          CoupledResult.afterSeparation
            (lazyBounded fuel (resume replies.1) nextOld nextPossible)
            (independentBounded fuel (resume replies.2) (old.appendReply request replies.2)) := by
  rw [coupledBounded]
  split <;> rename_i current
  · cases current.symm.trans reached
  · cases current.symm.trans reached
    rfl

/-- From a common transcript consistent with a permutation, the two projections recover
the bounded lazy-permutation law and the bounded independent-reply law. -/
theorem coupledBounded_marginals : CoupledTrialSpec.Marginals := by
  intro n fuel
  induction fuel with
  | zero =>
    intro program old possible
    dsimp only
    cases reached : program.nextFresh old with
    | done terminal =>
      simp [coupledBounded_of_done 0 program old possible reached, lazyBounded, reached,
        independentBounded_of_done 0 program old reached, PMF.pure_map, CoupledResult.agreed]
    | query request resume =>
      simp [coupledBounded_zero_of_query program old possible reached, lazyBounded, reached,
        independentBounded_zero_of_query program old reached, PMF.pure_map, CoupledResult.agreed]
  | succ fuel ih =>
    intro program old possible
    dsimp only
    cases reached : program.nextFresh old with
    | done terminal =>
      simp [coupledBounded_of_done (fuel + 1) program old possible reached, lazyBounded, reached,
        independentBounded_of_done (fuel + 1) program old reached, PMF.pure_map,
          CoupledResult.agreed]
    | query request resume =>
      let miss := nextFresh_miss program old request resume reached
      -- Equal replies give one continuation, whose projections follow by induction. On a
      -- mismatch, the product of the two continuation laws gives the required marginals.
      have fstLaw := old.coupledReplies_map_fst possible request miss
      have sndLaw : (old.coupledReplies possible request miss).map Prod.snd =
          uniformFinite (State n) :=
        (fresh_step_marginals old possible.choose possible.choose_spec request miss).2
      rw [coupledBounded_succ_of_query fuel program old possible reached]
      constructor
      · rw [lazyBounded, reached]
        refine bindOnSupport_project _ _ _ Prod.fst _ fstLaw _ ?_
        intro replies supported _
        dsimp only
        split
        · exact (ih _ _ _).1
        · exact afterSeparation_map_permutation _ _
      · rw [independentBounded_succ_of_query fuel program old reached,
          ← PMF.bindOnSupport_eq_bind (uniformFinite (State n))]
        refine bindOnSupport_project _ _ _ Prod.snd _ sndLaw _ ?_
        intro replies supported _
        dsimp only
        by_cases same : replies.1 = replies.2
        · rw [ite_eq_left same]
          exact (ih _ _ _).2.trans (by rw [same])
        · rw [ite_eq_right same]
          exact afterSeparation_map_independent _ _

/-- On the support of the coupling, an unset separation flag implies identical outcomes. -/
theorem coupledBounded_agreement : CoupledTrialSpec.Agreement := by
  intro n fuel
  induction fuel with
  | zero =>
    intro program old possible result supported _
    cases reached : program.nextFresh old with
    | done terminal =>
      rw [coupledBounded_of_done 0 program old possible reached] at supported
      exact of_agreed_support supported
    | query request resume =>
      rw [coupledBounded_zero_of_query program old possible reached] at supported
      exact of_agreed_support supported
  | succ fuel ih =>
    intro program old possible result supported agrees
    cases reached : program.nextFresh old with
    | done terminal =>
      rw [coupledBounded_of_done (fuel + 1) program old possible reached] at supported
      exact of_agreed_support supported
    | query request resume =>
      rw [coupledBounded_succ_of_query fuel program old possible reached] at supported
      obtain ⟨replies, _, outcome⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp supported
      dsimp only at outcome
      split at outcome
      · exact ih _ _ _ result outcome agrees
      · exact Bool.false_ne_true (agrees.symm.trans (afterSeparation_support outcome)) |>.elim

/-- Sum the hazards from a common transcript of length `old.length`. A shared fresh reply
adds one record before the next hazard is evaluated. -/
theorem coupledBounded_shifted_bound : CoupledTrialSpec.ShiftedBound := by
  intro n fuel
  let K : ℝ≥0∞ := (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞)
  induction fuel with
  | zero =>
    intro program old possible
    cases reached : program.nextFresh old with
    | done terminal =>
      rw [coupledBounded_of_done 0 program old possible reached, agreed_separation_mass]
      exact zero_le
    | query request resume =>
      rw [coupledBounded_zero_of_query program old possible reached, agreed_separation_mass]
      exact zero_le
  | succ fuel ih =>
    intro program old possible
    cases reached : program.nextFresh old with
    | done terminal =>
      rw [coupledBounded_of_done (fuel + 1) program old possible reached, agreed_separation_mass]
      exact zero_le
    | query request resume =>
      let miss := nextFresh_miss program old request resume reached
      let replies := old.coupledReplies possible request miss
      let later := ∑ i ∈ Finset.range fuel, ((old.length + 1 + i : ℕ) : ℝ≥0∞) / K
      rw [coupledBounded_succ_of_query fuel program old possible reached]
      -- Charge a mismatch at this step fully. Bound later mismatches on the agreeing branch.
      refine (mass_bindOnSupport_le replies _ {pair | pair.1 ≠ pair.2}
        CoupledResult.separated later ?_).trans ?_
      · intro pair supported notDifferent
        have equal : pair.1 = pair.2 := not_not.mp notDifferent
        dsimp only
        rw [ite_eq_left equal]
        have nextLength : (old.appendReply request pair.1).length = old.length + 1 := by
          simp [Transcript.appendReply]
        simpa only [later, K, nextLength] using
          ih (resume pair.1) (old.appendReply request pair.1)
            (old.coupledReply_possible possible request miss pair supported)
      · have current := fresh_step_hazard old possible.choose possible.choose_spec request miss
        exact (add_le_add current (le_refl later)).trans_eq (sum_shift old.length fuel K)

/-- Summing the per-query upper bounds from the empty transcript gives a separation probability
at most `q(q-1)/(2N²)`, as in (8). -/
theorem coupledBounded_separation_bound : CoupledTrialSpec.SeparationBound := by
  intro n fuel program
  rw [← Separation.sum_hazards]
  simpa only [List.length_nil, zero_add] using
    coupledBounded_shifted_bound fuel program [] (Transcript.empty_possible n)

end TrialProgram

end JH
