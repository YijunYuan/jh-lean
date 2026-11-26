/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.SuccessTransferSpec
public import JH.Oracle.Coupling.Trial
public import JH.Oracle.Lazy.Bounded

/-!
# Transfer of acceptance and verification to independent replies

Acceptance of a bounded permutation trial is covered by independent acceptance and the
separation event of equation (8). For fixed-target strategies, the real budget identifies this
bounded law with the real trial. The final lemmas extract verification paths from independent
transcripts using the recorded pair for each block.
-/

@[expose] public section

namespace JH

open scoped ENNReal

theorem TrialResult.accepts_iff {n : ℕ} (target : Word n) (outcome : Option (TrialResult n)) :
    TrialResult.accepts target outcome = true ↔
      ∃ result, outcome = some result ∧ result.Success target := by
  cases outcome <;> simp [TrialResult.accepts]

/-- A Boolean acceptance test on the coupled outcomes can change only on separation. -/
theorem TrialProgram.bounded_acceptance_le : SuccessTransferSpec.BoundedAcceptance := by
  intro n q program accept
  let possible := Transcript.empty_possible n
  let joint := TrialProgram.coupledBounded q program [] possible
  let realEvent : Set (CoupledResult n) := {result | accept result.permutation = true}
  let independentEvent : Set (CoupledResult n) := {result | accept result.independent = true}
  let separated : Set (CoupledResult n) := {result | result.separated = true}
  have projections := TrialProgram.coupledBounded_marginals q program [] possible
  have realMass : Separation.mass (TrialProgram.lazyBounded q program [] possible) accept =
      joint.toOuterMeasure realEvent := by
    calc
      _ = (joint.map CoupledResult.permutation).toOuterMeasure
        {outcome | accept outcome = true} := by
        rw [show joint.map CoupledResult.permutation = _ from projections.1,
          Separation.mass_eq_toOuterMeasure]
      _ = _ := PMF.toOuterMeasure_map_apply _ _ _
  have independentMass : Separation.mass (TrialProgram.independentBounded q program []) accept =
      joint.toOuterMeasure independentEvent := by
    calc
      _ = (joint.map CoupledResult.independent).toOuterMeasure
        {outcome | accept outcome = true} := by
        rw [show joint.map CoupledResult.independent = _ from projections.2,
          Separation.mass_eq_toOuterMeasure]
      _ = _ := PMF.toOuterMeasure_map_apply _ _ _
  -- Agreement holds on supported joint outcomes, so restrict the event to that support.
  have comparison : realEvent ∩ joint.support ⊆ independentEvent ∪ separated := by
    rintro result ⟨success, supported⟩
    cases flag : result.separated with
    | false =>
      have agrees := TrialProgram.coupledBounded_agreement q program
          [] possible result supported flag
      left
      change accept result.independent = true
      rw [← agrees]
      exact success
    | true => exact Or.inr flag
  calc
    _ = joint.toOuterMeasure realEvent := realMass
    _ ≤ joint.toOuterMeasure (independentEvent ∪ separated) := joint.toOuterMeasure_mono comparison
    _ ≤ joint.toOuterMeasure independentEvent + joint.toOuterMeasure separated :=
      MeasureTheory.measure_union_le _ _
    _ ≤ _ := by
      rw [← independentMass, ← Separation.mass_eq_toOuterMeasure joint CoupledResult.separated]
      exact add_le_add le_rfl (TrialProgram.coupledBounded_separation_bound q program)

/-- The cumulative separation allowance for q fresh records in (8). -/
private noncomputable def separationAllowance (n q : ℕ) : ℝ≥0∞ :=
  ((q * (q - 1) : ℕ) : ℝ≥0∞) / (2 * (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞))

private theorem separationAllowance_ne_top (n q : ℕ) : separationAllowance n q ≠ ⊤ := by
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)

private theorem separationAllowance_toReal (n q : ℕ) :
    (separationAllowance n q).toReal = (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 : ℝ) ^ n) ^ 2) := by
  have numerator : ((q * (q - 1) : ℕ) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
    cases q with
    | zero => simp
    | succ q => rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_pos q), Nat.cast_one]
  simp only [separationAllowance, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast, Nat.cast_pow, Nat.cast_ofNat, numerator]

private theorem toReal_le_with_allowance {n q : ℕ} {p r : ℝ≥0∞} (finite : r ≠ ⊤)
    (bound : p ≤ r + separationAllowance n q) :
    p.toReal ≤ r.toReal + (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 : ℝ) ^ n) ^ 2) := by
  calc
    _ ≤ (r + separationAllowance n q).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finite, separationAllowance_ne_top n q⟩) bound
    _ ≤ r.toReal + (separationAllowance n q).toReal := ENNReal.toReal_add_le
    _ = _ := by rw [separationAllowance_toReal]

theorem TrialProgram.bounded_acceptance_le_real {n : ℕ} (q : ℕ) (program : TrialProgram n)
    (accept : Option (TrialResult n) → Bool) :
    (Separation.mass (TrialProgram.lazyBounded q program [] (Transcript.empty_possible n))
      accept).toReal ≤
        (Separation.mass (TrialProgram.independentBounded q program []) accept).toReal +
        (q : ℝ) * ((q : ℝ) - 1) / (2 * ((2 : ℝ) ^ n) ^ 2) := by
  exact toReal_le_with_allowance ((TrialProgram.independentBounded q program []).map accept
    |>.apply_ne_top true) (TrialProgram.bounded_acceptance_le q program accept)

private theorem strategy_acceptance_le {α n : ℕ} (q : ℕ) (target : Word n) (initial : State n)
    (padding : Padding α n) (strategy : Strategy α n)
    (budget : ∀ permutation,
      (fixedTargetTrial strategy permutation initial padding).WithinBudget q) :
    permutationAcceptanceLaw target initial padding strategy true ≤
      independentAcceptanceLaw q target initial padding strategy true +
        separationAllowance n q := by
  classical
  let program := TrialProgram.ofStrategy strategy initial padding
  have permutationLaw :
      (TrialProgram.lazyBounded q program [] (Transcript.empty_possible n)).map
        (TrialResult.accepts target) =
          permutationAcceptanceLaw target initial padding strategy := by
    change (TrialProgram.lazyBounded q (TrialProgram.ofStrategy strategy initial padding) []
      (Transcript.empty_possible n)).map _ = _
    rw [TrialProgram.lazyBounded_fixedTarget strategy initial padding q, PMF.map_comp]
    have sameUniform : uniformPermutation n = uniformPMF (Permutation n) :=
      PartialPermutation.uniformFinite_eq_uniformOfFintype _
    rw [sameUniform, permutationAcceptanceLaw]
    apply congrArg (uniformPMF (Permutation n)).map
    funext permutation
    change TrialResult.accepts target (if
      (fixedTargetTrial strategy permutation initial padding).records.length ≤ q then
      some (fixedTargetTrial strategy permutation initial padding) else none) =
      TrialResult.accepts target (some (fixedTargetTrial strategy permutation initial padding))
    -- With verification included in the budget, the bounded run returns the full result.
    have within : (fixedTargetTrial strategy permutation initial padding).records.length ≤ q :=
      budget permutation
    rw [ite_eq_left within]
  rw [← permutationLaw]
  exact TrialProgram.bounded_acceptance_le q program (TrialResult.accepts target)

/-- A fixed tape satisfying the budget incurs the separation term of equation (8). -/
theorem strategy_success_le_independent : SuccessTransferSpec.StrategyTransfer := by
  intro α n q target initial padding strategy budget
  exact toReal_le_with_allowance ((independentAcceptanceLaw q target initial padding
    strategy).apply_ne_top true)
    (strategy_acceptance_le q target initial padding strategy budget)

private theorem average_acceptance_le {Tape : Type*} (law : PMF Tape) (left right : Tape → PMF Bool)
    (allowance : ℝ≥0∞) (localBound : ∀ tape ∈ law.support,
      left tape true ≤ right tape true + allowance) :
    (law.bind left) true ≤ (law.bind right) true + allowance := by
  rw [PMF.bind_apply, PMF.bind_apply]
  calc
    _ ≤ ∑' tape, law tape * (right tape true + allowance) := by
      apply tsum_le_tsum
      intro tape
      by_cases supported : tape ∈ law.support
      · exact mul_le_mul_right (localBound tape supported) (law tape)
      · have zero := (law.apply_eq_zero_iff tape).mpr supported
        simp [zero]
    _ = _ := by
      simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, law.tsum_coe, one_mul]

/-- Average the fixed-strategy comparison over the original adversary tape law. The uniform
separation allowance is paid once. -/
theorem fixedTarget_success_le_independent : SuccessTransferSpec.Transfer := by
  intro α n q target initial padding strategies budget
  let real := permutationAcceptanceLaw target initial padding
  let independent := independentAcceptanceLaw q target initial padding
  have estimate := average_acceptance_le strategies real independent (separationAllowance n q)
    (fun strategy supported ↦ strategy_acceptance_le q target initial padding strategy
      (budget strategy supported))
  exact toReal_le_with_allowance ((strategies.bind independent).apply_ne_top true) estimate

/-- The comparison in the notation of the finite-parameter certificates. -/
theorem fixedTarget_success_le_independent_params : SuccessTransferSpec.ParameterTransfer := by
  intro α params q target initial padding strategies budget
  simpa only [Parameters.Params.separationTail, Parameters.Params.N,
    Nat.cast_pow, Nat.cast_ofNat] using
    fixedTarget_success_le_independent q target initial padding strategies budget

namespace TrialProgram

variable {n : ℕ}

private theorem independent_query_support (fuel : ℕ) (old : Transcript n) (request : Query n)
    (resume : State n → TrialProgram n) (result : TrialResult n)
    (supported : some result ∈ (independentBounded fuel (.query request resume) old).support) :
    ∃ (remaining : ℕ) (answer : State n) (nextOld : Transcript n) (record : Record n),
      some result ∈ (independentBounded remaining (resume answer) nextOld).support ∧
      record ∈ nextOld ∧ request.hasAddress record = true ∧ request.replyFrom record = answer := by
  cases cached : old.cachedReply request with
  | some answer =>
    have sameFrontier : (TrialProgram.query request resume).nextFresh old =
        (resume answer).nextFresh old := by
      rw [nextFresh, cached]
    have sameLaw : independentBounded fuel (.query request resume) old =
        independentBounded fuel (resume answer) old := by
      unfold independentBounded
      rw [runBoundedWith.eq_1 _ fuel (.query request resume) old,
        runBoundedWith.eq_1 _ fuel (resume answer) old, sameFrontier]
    rw [sameLaw] at supported
    unfold Transcript.cachedReply at cached
    cases found : old.find? request.hasAddress with
    | none => simp [found] at cached
    | some record =>
      simp only [found, Option.map_some, Option.some.injEq] at cached
      exact ⟨fuel, answer, old, record, supported, List.mem_of_find?_eq_some found,
        List.find?_some found, cached⟩
  | none =>
    have fresh : (TrialProgram.query request resume).nextFresh old = .query request resume := by
      rw [nextFresh, cached]
    cases fuel with
    | zero =>
      rw [independentBounded_zero_of_query (.query request resume) old fresh] at supported
      simp at supported
    | succ fuel =>
      rw [independentBounded_succ_of_query fuel (.query request resume) old fresh] at supported
      obtain ⟨answer, _, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      refine ⟨fuel, answer, old.appendReply request answer, request.recordOfReply answer,
        continued, by simp [Transcript.appendReply], ?_, ?_⟩
      · rcases request with ⟨direction, address⟩
        cases direction <;> simp [Query.hasAddress, Query.recordOfReply]
      · rcases request with ⟨direction, address⟩
        cases direction <;> rfl

private theorem edge_of_forward_reply (source : State n) (block : Word n) (answer : State n)
    (record : Record n)
    (addressMatch : (Query.mk .forward (permInput source block)).hasAddress record = true)
    (reply : (Query.mk .forward (permInput source block)).replyFrom record = answer) :
    record.edge source (feedForward answer block) := by
  have input : record.input = permInput source block := of_decide_eq_true addressMatch
  have output : record.output = answer := reply
  refine ⟨(congrArg Prod.fst input).symm, ?_⟩
  apply Prod.ext
  · change answer.1 ^^^ block = source.2 ^^^ (record.input.2 ^^^ record.output.1)
    rw [input, output]
    change answer.1 ^^^ block = source.2 ^^^ ((source.2 ^^^ block) ^^^ answer.1)
    rw [← BitVec.xor_assoc source.2 (source.2 ^^^ block) answer.1,
      ← BitVec.xor_assoc source.2 source.2 block, BitVec.xor_self, BitVec.zero_xor,
      BitVec.xor_comm answer.1 block]
  · change answer.2 = record.output.2
    exact congrArg Prod.snd output.symm

private theorem independent_verify_walk (blocks : List (Word n)) (state : State n) (fuel : ℕ)
    (old : Transcript n) (result : TrialResult n)
    (supported : some result ∈ (independentBounded fuel (verify state blocks) old).support) :
    ∃ (terminal : State n) (path : Walk result.records.realEdge state terminal),
      result.terminal = some terminal ∧ path.labels.length = blocks.length := by
  induction blocks generalizing fuel state old with
  | nil =>
    have reached : (verify state []).nextFresh old = .done (some state) := rfl
    rw [independentBounded_of_done fuel (verify state []) old reached] at supported
    have equal := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
    subst result
    exact ⟨state, .nil state, rfl, rfl⟩
  | cons block rest ih =>
    let request : Query n := ⟨.forward, permInput state block⟩
    let resume := fun answer ↦ verify (feedForward answer block) rest
    obtain ⟨remaining, answer, nextOld, record, continued, present, addressMatch, reply⟩ :=
      independent_query_support fuel old request resume result supported
    have extended :=
      (independentBounded_support remaining (resume answer) nextOld result continued).1
    -- A cached or fresh pair survives to the final log, where its index labels this edge.
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp (List.IsPrefix.subset extended present)
    let label : result.records.Label := ⟨i, hi⟩
    have edge : result.records.realEdge label state (feedForward answer block) := by
      change (result.records.get label).edge state (feedForward answer block)
      rw [show result.records.get label = record from same]
      exact edge_of_forward_reply state block answer record addressMatch reply
    obtain ⟨terminal, path, endState, length⟩ :=
      ih (feedForward answer block) remaining nextOld continued
    exact ⟨terminal, .cons label edge path,
      endState, by simp only [Walk.labels, List.length_cons, length]⟩

private theorem independent_success_walk {α : ℕ} (strategy : Strategy α n) (fuel : ℕ)
    (target : Word n) (initial : State n) (padding : Padding α n) (old : Transcript n)
    (result : TrialResult n)
    (supported : some result ∈
      (independentBounded fuel (ofStrategy strategy initial padding) old).support)
    (success : result.Success target) :
    ∃ rate : Word n,
      Nonempty (Walk (result.records.edge {initial}) (startCopy initial)
        (.inl (target, rate))) := by
  induction strategy generalizing fuel old with
  | halt candidate =>
    cases candidate with
    | none =>
      have reached : (ofStrategy (Strategy.halt none) initial padding).nextFresh
          old = .done none := rfl
      rw [independentBounded_of_done fuel _ old reached] at supported
      have equal := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
      subst result
      cases success
    | some message =>
      obtain ⟨terminal, path, endState, length⟩ :=
        independent_verify_walk (padding.encode message) initial fuel old result supported
      have capacity : terminal.1 = target := by
        rw [TrialResult.Success, endState] at success
        exact Option.some.inj success
      refine ⟨terminal.2, ?_⟩
      rcases terminal with ⟨column, rate⟩
      change column = target at capacity
      subst column
      -- Nonempty padding supplies a first edge to rebase at the virtual initial vertex.
      cases path with
      | nil => exact (padding.nonempty message (List.length_eq_zero_iff.mp length.symm)).elim
      | cons label edge rest =>
        rename_i middle
        have first : result.records.edge {initial} label (startCopy initial) (.inl middle) := edge
        exact ⟨.cons label first (rest.map Sum.inl (fun {_ _ _} step ↦ step))⟩
  | query request resume ih =>
    obtain ⟨remaining, answer, nextOld, _, continued, _, _, _⟩ :=
      independent_query_support fuel old request (fun reply ↦
        ofStrategy (resume reply) initial padding)
        result supported
    exact ih answer remaining nextOld continued

/-- Successful independent verification gives a nonempty walk from the virtual initial vertex
to the target column in its own transcript. -/
theorem independent_success_trace : SuccessTransferSpec.IndependentTrace := by
  intro α n q target initial padding strategy result supported success
  exact independent_success_walk strategy q target initial padding [] result supported success

end TrialProgram

end JH
