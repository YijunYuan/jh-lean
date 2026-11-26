/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelProofs
public import JH.Oracle.Coupling.Reply
public import JH.Oracle.TrialProgram
public import JH.Probability.Separation
public import JH.SecondPreimage.OriginalPhaseSpec

/-!
# Disclosure of the original trace and the capacity collision bound

Factor the bounded independent experiment at the end of original-message verification. The
continuation retains the disclosed transcript and pays for exactly the pairs newly written in
the original phase. Distinct capacities ensure each original block is fresh. This gives both
the exact collision-free cost and the hazard sum of equation (9) in Section 3.2.
-/

@[expose] public section

namespace JH.OriginalPhase

open JH
open JH.PartialPermutation (uniformFinite)
open scoped BigOperators ENNReal

variable {n : ℕ}

private theorem bounded_query_hit (replyLaw : PMF (State n)) (fuel : ℕ)
    (old : Transcript n) (request : Query n) (resume : State n → TrialProgram n)
    {hitReply : State n} (hit : old.cachedReply request = some hitReply) :
    TrialProgram.runBoundedWith (fun _ ↦ replyLaw) fuel (.query request resume) old =
      TrialProgram.runBoundedWith (fun _ ↦ replyLaw) fuel (resume hitReply) old := by
  rw [TrialProgram.runBoundedWith.eq_1 _ fuel (.query request resume) old,
    TrialProgram.runBoundedWith.eq_1 _ fuel (resume hitReply) old, TrialProgram.nextFresh, hit]

private theorem bounded_query_miss (replyLaw : PMF (State n)) (fuel : ℕ)
    (old : Transcript n) (request : Query n) (resume : State n → TrialProgram n)
    (miss : old.cachedReply request = none) :
    TrialProgram.runBoundedWith (fun _ ↦ replyLaw) (fuel + 1) (.query request resume) old =
      replyLaw.bind fun reply ↦
        TrialProgram.runBoundedWith (fun _ ↦ replyLaw) fuel (resume reply)
          (old.appendReply request reply) := by
  rw [TrialProgram.runBoundedWith.eq_1, TrialProgram.nextFresh, miss]

/-- Sample the original trace, then continue with its log and the remaining fresh budget. -/
theorem continuation_law : OriginalPhaseSpec.ContinuationLaw := by
  intro n replyLaw fuel state blocks
  induction blocks generalizing fuel state with
  | nil =>
      intro old previous next _
      simp [TrialProgram.observeOriginal, sample]
  | cons block rest ih =>
      intro old previous next enough
      let request : Query n := ⟨.forward, permInput state block⟩
      let resume (reply : State n) :=
        TrialProgram.observeOriginal (feedForward reply block) rest
          (match old.cachedReply request with
          | none => old.appendReply request reply
          | some _ => old) (state :: previous) next
      change TrialProgram.runBoundedWith (fun _ ↦ replyLaw) fuel (.query request resume) old = _
      cases known : old.cachedReply request with
      | some hit =>
          rw [bounded_query_hit replyLaw fuel old request resume known]
          have hb : rest.length ≤ fuel := by simp only [List.length_cons] at enough; omega
          simp only [resume, sample, show (⟨.forward, permInput state block⟩ : Query n) = request
            from rfl, known]
          exact ih fuel (feedForward hit block) old (state :: previous) next hb
      | none =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              have hb : rest.length ≤ fuel := by simpa using enough
              rw [bounded_query_miss replyLaw fuel old request resume known]
              simp only [sample, show ({ direction := .forward, address := permInput state block } :
                Query n) = request from rfl, known, PMF.bind_bind]
              apply congrArg replyLaw.bind
              funext reply
              simp only [resume, known]
              rw [ih fuel (feedForward reply block) (old.appendReply request reply)
                (state :: previous) next hb]
              -- The budget plus the log length is conserved when appending a fresh pair.
              have sameFuel : fuel +
                  (old.appendReply request reply).length = fuel + 1 + old.length := by
                simp only [Transcript.appendReply, List.length_append, List.length_singleton]
                omega
              simp only [sameFuel]

/-- The phase adds at most one record per block and records the start and every resulting state
after the previous states. -/
theorem sample_budget : OriginalPhaseSpec.Budget := by
  intro n replyLaw state blocks
  induction blocks generalizing state with
  | nil =>
      intro old previous observation present
      have exactResult : observation = ⟨state, old, (state :: previous).reverse⟩ := by
        simpa only [sample, PMF.support_pure, Set.mem_singleton_iff] using present
      subst observation
      exact ⟨List.prefix_refl _, by simp, by simp⟩
  | cons block rest ih =>
      intro old previous observation present
      let request : Query n := ⟨.forward, permInput state block⟩
      cases known : old.cachedReply request with
      | some hit =>
          have supported : observation ∈ (sample replyLaw (feedForward hit block) rest old
              (state :: previous)).support := by
            simpa only [sample, show ({ direction := .forward, address := permInput state block } :
              Query n) = request from rfl, known] using present
          obtain ⟨extension, hsize, hstates⟩ := ih (feedForward hit block) old (state :: previous)
            observation supported
          simp only [List.length_cons] at hstates ⊢
          exact ⟨extension, by omega, by omega⟩
      | none =>
          have supported : observation ∈ (replyLaw.bind fun reply ↦
              sample replyLaw (feedForward reply block) rest (old.appendReply request reply)
                (state :: previous)).support := by
            simpa only [sample, show ({ direction := .forward, address := permInput state block } :
              Query n) = request from rfl, known] using present
          obtain ⟨reply, _, hreply⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
          obtain ⟨extension, hsize, hstates⟩ := ih (feedForward reply block)
            (old.appendReply request reply) (state :: previous) observation hreply
          have prefixStep : (old.appendReply request reply).Extends old := List.prefix_append _ _
          have lengthStep : (old.appendReply request reply).length = old.length + 1 := by
            simp [Transcript.appendReply]
          simp only [List.length_cons, lengthStep] at hsize hstates ⊢
          exact ⟨prefixStep.trans extension, by omega, by omega⟩

/-- A new source capacity forces a cache miss when all old inputs use prior source capacities. -/
private theorem fresh_of_distinct (state : State n) (block : Word n) (old : Transcript n)
    (previous : List (State n)) (good : ((state :: previous).map Prod.fst).Nodup)
    (inputs : ∀ record ∈ old, record.input.1 ∈ previous.map Prod.fst) :
    old.cachedReply ⟨.forward, permInput state block⟩ = none := by
  apply (old.cachedReply_eq_none_iff _).2
  apply List.any_eq_false.2
  intro record present
  simp only [Query.hasAddress]
  intro same
  have member := inputs record present
  rw [congrArg Prod.fst (of_decide_eq_true same)] at member
  exact (List.nodup_cons.mp good).1 member

private theorem inputs_after_fresh (state : State n) (block : Word n) (old : Transcript n)
    (previous : List (State n)) (reply : State n)
    (inputs : ∀ record ∈ old, record.input.1 ∈ previous.map Prod.fst) :
    ∀ record ∈ old.appendReply ⟨.forward, permInput state block⟩ reply,
      record.input.1 ∈ (state :: previous).map Prod.fst := by
  intro record present
  rcases List.mem_append.mp present with prior | current
  · exact List.mem_cons_of_mem _ (inputs record prior)
  · have same := List.mem_singleton.mp current
    subst record
    exact List.mem_cons_self

private theorem sample_states_suffix (replyLaw : PMF (State n)) (state : State n)
    (blocks : List (Word n)) (old : Transcript n) (previous : List (State n))
    (observation : OriginalObservation n)
    (support : observation ∈ (sample replyLaw state blocks old previous).support) :
    ∃ newer, observation.states.reverse = newer ++ state :: previous := by
  induction blocks generalizing state old previous with
  | nil =>
      have same : observation = ⟨state, old, (state :: previous).reverse⟩ := by
        simpa only [sample, PMF.support_pure, Set.mem_singleton_iff] using support
      exact ⟨[], by simp [same]⟩
  | cons block rest ih =>
      let request : Query n := ⟨.forward, permInput state block⟩
      have extend (reply : State n) (records : Transcript n)
          (hit : observation ∈ (sample replyLaw (feedForward reply block) rest records
            (state :: previous)).support) :
          ∃ newer, observation.states.reverse = newer ++ state :: previous := by
        obtain ⟨newer, hs⟩ := ih (feedForward reply block) records (state :: previous) hit
        exact ⟨newer ++ [feedForward reply block], by simpa [List.append_assoc] using hs⟩
      cases hit : old.cachedReply request with
      | some reply =>
          exact extend reply old (by simpa only [sample, ← show request =
            (⟨.forward, permInput state block⟩ : Query n) from rfl, hit] using support)
      | none =>
          have h : observation ∈ (replyLaw.bind fun reply ↦
              sample replyLaw (feedForward reply block) rest (old.appendReply request reply)
                (state :: previous)).support := by
            simpa only [sample, ← show request = (⟨.forward, permInput state block⟩ : Query n)
              from rfl, hit] using support
          obtain ⟨reply, _, answer⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
          exact extend reply _ answer

/-- Starting from the empty transcript, a collision-free original run adds one pair per block. -/
theorem sample_collision_free_length : OriginalPhaseSpec.CollisionFreeLength := by
  intro n replyLaw initial blocks observation present free
  have general (state : State n) (blocks : List (Word n)) (old : Transcript n)
      (previous : List (State n))
      (inputs : ∀ record ∈ old, record.input.1 ∈ previous.map Prod.fst)
      (support : observation ∈ (sample replyLaw state blocks old previous).support) :
      observation.records.length = old.length + blocks.length := by
    induction blocks generalizing state old previous with
    | nil =>
        have same : observation = ⟨state, old, (state :: previous).reverse⟩ := by
          simpa only [sample, PMF.support_pure, Set.mem_singleton_iff] using support
        simp [same]
    | cons block rest ih =>
        let request : Query n := ⟨.forward, permInput state block⟩
        obtain ⟨newer, hs⟩ := sample_states_suffix replyLaw state (block :: rest) old previous
          observation support
        have allGood : (observation.states.reverse.map Prod.fst).Nodup := by
          simpa only [List.map_reverse, List.nodup_reverse] using
            (not_not.mp free : (observation.states.map Prod.fst).Nodup)
        have oldGood : ((state :: previous).map Prod.fst).Nodup := by
          rw [hs, List.map_append] at allGood
          exact (List.nodup_append.mp allGood).2.1
        have miss := fresh_of_distinct state block old previous oldGood inputs
        have h : observation ∈ (replyLaw.bind fun reply ↦
            sample replyLaw (feedForward reply block) rest (old.appendReply request reply)
              (state :: previous)).support := by
          simpa only [sample, miss] using support
        obtain ⟨reply, _, after⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
        have len := ih (feedForward reply block) (old.appendReply request reply)
          (state :: previous) (inputs_after_fresh state block old previous reply inputs) after
        simpa only [Transcript.appendReply, List.length_append, List.length_singleton,
          List.length_cons, List.length_nil, Nat.zero_add, Nat.add_right_comm,
            Nat.add_assoc] using len
  simpa using general initial blocks [] [] (by simp) present

/-- Feed-forward XOR with the fixed block preserves uniformity of the new capacity. -/
private theorem uniform_capacity (block : Word n) :
    (uniformFinite (State n)).map (fun reply ↦ (feedForward reply block).1) =
      uniformFinite (Word n) := by
  let e : State n ≃ State n :=
    { toFun := fun reply ↦ feedForward reply block
      invFun := fun reply ↦ feedForward reply block
      left_inv := fun reply ↦ Prod.ext (by simp [feedForward, BitVec.xor_assoc]) rfl
      right_inv := fun reply ↦ Prod.ext (by simp [feedForward, BitVec.xor_assoc]) rfl }
  change (uniformFinite (State n)).map (Prod.fst ∘ e) = _
  rw [← PMF.map_comp, ReplyCoupling.uniformFinite_map_equiv,
    ← ReplyCoupling.independentPair_uniform (α := Word n) (β := Word n)]
  exact ReplyCoupling.independentPair_map_fst _ _

private theorem new_collision_hazard (block : Word n) (visited : List (Word n)) :
    (uniformFinite (State n)).toOuterMeasure {reply | (feedForward reply block).1 ∈ visited} ≤
      (visited.length : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
  classical
  let bad : Set (Word n) := ↑visited.toFinset
  calc
    _ = ((uniformFinite (State n)).map (fun reply ↦ (feedForward reply block).1)).toOuterMeasure
        bad := by simp only [PMF.toOuterMeasure_map_apply, Set.preimage, bad, Finset.mem_coe,
          List.mem_toFinset]
    _ = (visited.toFinset.card : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
      rw [uniform_capacity, PartialPermutation.uniformFinite_event, Nat.card_coe_set_eq,
        Set.ncard_coe_finset, Nat.card_eq_fintype_card, word_card]
    _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast visited.toFinset_card_le) _

theorem collision_bind_le {A B : Type} (law : PMF A) (step : A → PMF B)
    (hit : Set A) (collision : Set B) (bound : ℝ≥0∞)
    (good : ∀ a ∈ law.support, a ∉ hit → (step a).toOuterMeasure collision ≤ bound) :
    (law.bind step).toOuterMeasure collision ≤ law.toOuterMeasure hit + bound := by
  classical
  have step_le (a : A) (supported : a ∈ law.support) :
      (step a).toOuterMeasure collision ≤ hit.indicator (fun _ ↦ 1) a + bound := by
    by_cases ha : a ∈ hit
    · rw [Set.indicator_of_mem ha]
      have one : (step a).toOuterMeasure Set.univ = 1 :=
        ((step a).toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
      exact ((step a).toOuterMeasure.mono (Set.subset_univ _)).trans (one ▸ le_self_add)
    · simpa only [Set.indicator_of_notMem ha, zero_add] using good a supported ha
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' a, law a * (hit.indicator (fun _ ↦ 1) a + bound) :=
      tsum_le_tsum fun a ↦ by
        by_cases supported : a ∈ law.support
        · exact mul_le_mul_right (step_le a supported) _
        · simp [(law.apply_eq_zero_iff a).mpr supported]
    _ = law.toOuterMeasure hit + bound := by
      rw [PMF.toOuterMeasure_apply]
      simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, law.tsum_coe, one_mul]
      congr 1
      apply tsum_congr
      intro a
      by_cases hitNow : a ∈ hit <;> simp [hitNow]

private theorem collision_remaining (state : State n) (blocks : List (Word n))
    (old : Transcript n) (previous : List (State n))
    (good : ((state :: previous).map Prod.fst).Nodup)
    (inputs : ∀ record ∈ old, record.input.1 ∈ previous.map Prod.fst) :
    (sample (uniformFinite (State n)) state blocks old previous).toOuterMeasure
      {outcome | HasCapacityCollision outcome} ≤
      ∑ i ∈ Finset.range blocks.length, ((previous.length + i + 1 : ℕ) : ℝ≥0∞) /
        ((2 ^ n : ℕ) : ℝ≥0∞) := by
  classical
  induction blocks generalizing state old previous with
  | nil =>
      have noCollision : (⟨state, old, (state :: previous).reverse⟩ : OriginalObservation n) ∉
          {outcome | HasCapacityCollision outcome} := by
        change ¬ ¬ ((state :: previous).reverse.map Prod.fst).Nodup
        rw [List.map_reverse, List.nodup_reverse]
        exact not_not.mpr good
      rw [sample, PMF.toOuterMeasure_pure_apply, ite_eq_right noCollision]
      exact zero_le
  | cons block rest ih =>
      let request : Query n := ⟨.forward, permInput state block⟩
      -- The next capacity can match any capacity in the current trace, including the source.
      let visited := (state :: previous).map Prod.fst
      let hit : Set (State n) := {reply | (feedForward reply block).1 ∈ visited}
      let allowance := ∑ i ∈ Finset.range rest.length,
        (((state :: previous).length + i + 1 : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞)
      have miss := fresh_of_distinct state block old previous good inputs
      simp only [sample, miss]
      refine (collision_bind_le _ _ hit _ allowance ?_).trans ?_
      · intro reply _ safe
        have stillGood : ((feedForward reply block :: state :: previous).map Prod.fst).Nodup :=
          List.nodup_cons.mpr ⟨safe, good⟩
        exact ih (feedForward reply block) (old.appendReply request reply) (state :: previous)
          stillGood (inputs_after_fresh state block old previous reply inputs)
      · refine (add_le_add (new_collision_hazard block visited) le_rfl).trans_eq ?_
        rw [List.length_cons, Finset.sum_range_succ']
        simp only [visited, List.length_map, List.length_cons, Nat.add_zero, allowance]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [show previous.length + 1 + i + 1 = previous.length + (i + 1) + 1 by omega]

/-- Equation (9) sums the first-collision hazards `j/N` for `j = 1, …, ℓ`. -/
theorem collision_tail : OriginalPhaseSpec.CollisionTail := by
  intro n state blocks
  have h := collision_remaining state blocks [] [] (by simp) (by simp)
  let N := (2 ^ n : ℕ)
  have sumEq : (∑ i ∈ Finset.range blocks.length, ((i + 1 : ℕ) : ℝ≥0∞) /
      (N : ℝ≥0∞)) = (((blocks.length + 1) * blocks.length : ℕ) : ℝ≥0∞) /
        (2 * (N : ℝ≥0∞)) := by
    have htriangle := Separation.sum_hazards (blocks.length + 1) (N : ℝ≥0∞)
    rw [Finset.sum_range_succ'] at htriangle
    simpa only [Nat.cast_zero, ENNReal.zero_div, add_zero, Nat.add_sub_cancel] using htriangle
  have hfinal := h.trans_eq (by simpa only [List.length_nil, Nat.zero_add] using sumEq)
  have finite : ((((blocks.length + 1) * blocks.length : ℕ) : ℝ≥0∞) /
      (2 * (N : ℝ≥0∞))) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by dsimp [N]; positivity)
  have hreal := ENNReal.toReal_mono finite hfinal
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hreal
  simpa only [N, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_comm ((blocks.length : ℝ) + 1)] using hreal

end JH.OriginalPhase
