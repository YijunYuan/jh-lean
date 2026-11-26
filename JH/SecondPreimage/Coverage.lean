/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.Trial
public import JH.SecondPreimage.CoverageSpec
public import JH.SecondPreimage.Trace

/-!
# Replay and path extraction after original-trace disclosure

The earliest forward match in the final transcript defines one reply function for both traces.
A witnessed cache reply survives later appends, even when the independent experiment writes
repeated addresses. On a collision-free original observation, the first-departure and
first-return argument in Section 3.2 gives a path using only the records after disclosure.
-/

@[expose] public section

namespace JH.SecondPreimageCoverage

open SecondPreimageTrace

variable {n : ℕ}

private theorem find_hit (old : Transcript n) (request : Query n) (answer : State n)
    (hit : old.cachedReply request = some answer) :
    ∃ record, old.find? request.hasAddress = some record ∧ request.replyFrom record = answer :=
  Option.map_eq_some_iff.mp hit

private theorem cachedReply_extends {old final : Transcript n} (extension : final.Extends old)
    (request : Query n) {answer : State n} (hit : old.cachedReply request = some answer) :
    final.cachedReply request = some answer := by
  obtain ⟨record, found, same⟩ := find_hit old request answer hit
  simp only [Transcript.cachedReply, List.IsPrefix.find?_eq_some extension found,
    Option.map_some, same]

private theorem cachedReply_appended (old : Transcript n) (request : Query n) (answer : State n)
    (miss : old.cachedReply request = none) :
    (old.appendReply request answer).cachedReply request = some answer := by
  have absent : old.find? request.hasAddress = none := by
    simpa only [Transcript.cachedReply, Option.map_eq_none_iff] using miss
  have addressMatches : request.hasAddress (request.recordOfReply answer) = true := by
    rcases request with ⟨_ | _, address⟩ <;> simp [Query.hasAddress, Query.recordOfReply]
  have matchesAnswer : request.replyFrom (request.recordOfReply answer) = answer := by
    rcases request with ⟨_ | _, address⟩ <;> rfl
  simp only [Transcript.cachedReply, Transcript.appendReply, List.find?_append, absent,
    Option.none_or, List.find?_cons, addressMatches, Option.map_some, matchesAnswer]

private theorem forward_hit {old final : Transcript n} (extension : final.Extends old)
    (input : State n) (answer : State n) (hit : old.cachedReply ⟨.forward, input⟩ = some answer) :
    final.forwardReply input = answer ∧
      ∃ record ∈ final, record.input = input ∧ record.output = answer := by
  let request : Query n := ⟨.forward, input⟩
  have hitFinal := cachedReply_extends extension request hit
  obtain ⟨record, found, replied⟩ := find_hit final request answer hitFinal
  refine ⟨?_, record, List.mem_of_find?_eq_some found, ?_, replied⟩
  · simp only [Transcript.forwardReply, show final.cachedReply ⟨.forward, input⟩ =
      some answer from hitFinal,
      Option.getD_some]
  · exact of_decide_eq_true (List.find?_some (p := request.hasAddress) found)

/-- A lookup either reuses a recorded answer or appends the pair for a cache miss. -/
private inductive CacheStep (old : Transcript n) (request : Query n) :
    State n → Transcript n → Prop where
  | hit (answer : State n) (cached : old.cachedReply request = some answer) :
      CacheStep old request answer old
  | miss (answer : State n) (fresh : old.cachedReply request = none) :
      CacheStep old request answer (old.appendReply request answer)

private theorem CacheStep.extension {old updated : Transcript n}
    {request : Query n} {answer : State n}
    (step : CacheStep old request answer updated) : updated.Extends old := by
  cases step with
  | hit => exact List.prefix_refl _
  | miss => exact List.prefix_append _ _

private theorem CacheStep.reply_cached {old updated : Transcript n}
    {request : Query n} {answer : State n}
    (step : CacheStep old request answer updated) : updated.cachedReply request = some answer := by
  cases step with
  | hit known => exact known
  | miss fresh => exact cachedReply_appended old request _ fresh

private theorem sample_step (law : PMF (State n)) (source : State n) (block : Word n)
    (rest : List (Word n)) (old : Transcript n) (previous : List (State n))
    (observation : OriginalObservation n)
    (supported : observation ∈ (OriginalPhase.sample law source (block ::
      rest) old previous).support) :
    ∃ answer updated, CacheStep old ⟨.forward, permInput source block⟩ answer updated ∧
      observation ∈ (OriginalPhase.sample law (feedForward answer block) rest updated (source ::
        previous)).support := by
  cases cached : old.cachedReply ⟨.forward, permInput source block⟩ with
  | some answer =>
    exact ⟨answer, old, .hit answer cached, by simpa only [OriginalPhase.sample,
      cached] using supported⟩
  | none =>
    let request : Query n := ⟨.forward, permInput source block⟩
    have supportedBind : observation ∈ (law.bind fun answer ↦
        OriginalPhase.sample law (feedForward answer block) rest (old.appendReply request answer)
          (source :: previous)).support := by
      simpa only [OriginalPhase.sample, cached] using supported
    obtain ⟨answer, _, more⟩ := (PMF.mem_support_bind_iff _ _ _).mp supportedBind
    exact ⟨answer, old.appendReply request answer, .miss answer cached, more⟩

private theorem states_cons (reply : State n → State n) (source : State n) (block : Word n)
    (rest : List (Word n)) : states reply source (block :: rest) =
      source :: states reply (compressWith reply source block) rest := rfl

private theorem replay_sample (law : PMF (State n)) (source : State n) (blocks : List (Word n))
    (old : Transcript n) (previous : List (State n)) (observation : OriginalObservation n)
      (final : Transcript n)
    (supported : observation ∈ (OriginalPhase.sample law source blocks old previous).support)
    (extension : final.Extends observation.records) :
    observation.records.Extends old ∧
      observation.states = previous.reverse ++ states final.forwardReply source blocks ∧
      observation.terminal = runWith final.forwardReply source blocks ∧
      (¬ OriginalPhase.HasCapacityCollision observation →
        (∀ record ∈ old, record.input.1 ∈ previous.map Prod.fst) →
        observation.records = old ++ originalRecords final.forwardReply source blocks) := by
  induction blocks generalizing source old previous with
  | nil =>
    have same : observation = ⟨source, old, (source :: previous).reverse⟩ :=
      (PMF.mem_support_pure_iff _ _).mp supported
    subst observation
    refine ⟨List.prefix_refl _, ?_, rfl, fun _ _ ↦ (List.append_nil _).symm⟩
    simp only [List.reverse_cons, states, sources, List.nil_append, runWith, List.foldl_nil]
  | cons block rest ih =>
    obtain ⟨answer, updated, step, more⟩ :=
      sample_step law source block rest old previous observation supported
    obtain ⟨prefixLog, trace, terminal, log⟩ :=
      ih (feedForward answer block) updated (source :: previous) more
    -- This reply is cached after the step and remains the earliest forward reply in the final log.
    have answered :=
      (forward_hit (List.IsPrefix.trans prefixLog extension) (permInput source block) answer
      step.reply_cached).1
    have compression : compressWith final.forwardReply source block = feedForward answer block := by
      simp only [compressWith, answered]
    have fullTrace : observation.states =
        previous.reverse ++ states final.forwardReply source (block :: rest) := by
      rw [trace, List.reverse_cons, List.append_assoc, List.singleton_append,
        states_cons, compression]
    refine ⟨List.IsPrefix.trans step.extension prefixLog, fullTrace, ?_, ?_⟩
    · rw [runWith_cons, compression, terminal]
    · intro noCollision priorInputs
      cases step with
      -- An old matching input would repeat a prior source capacity.
      | hit cached =>
        obtain ⟨record, found, _⟩ := find_hit old ⟨.forward, permInput source block⟩ _ cached
        have matched := List.find?_some found
        have input : record.input = permInput source block := of_decide_eq_true matched
        have belongs : source.1 ∈ previous.reverse.map Prod.fst := by
          rw [List.map_reverse, List.mem_reverse]
          exact (congrArg (fun state : State n ↦ state.1) input) ▸
            priorInputs record (List.mem_of_find?_eq_some found)
        have distinct : (observation.states.map Prod.fst).Nodup := Classical.not_not.mp noCollision
        rw [fullTrace, List.map_append] at distinct
        have current : source.1 ∈ (states final.forwardReply source (block :: rest)).map Prod.fst :=
          List.mem_cons_self
        exact ((List.nodup_append.mp distinct).2.2 _ belongs _ current rfl).elim
      | miss fresh =>
        let request : Query n := ⟨.forward, permInput source block⟩
        have priorNext (record : Record n) (present : record ∈ old.appendReply request answer) :
            record.input.1 ∈ (source :: previous).map Prod.fst := by
          rcases List.mem_append.mp present with before | added
          · exact List.mem_cons_of_mem _ (priorInputs record before)
          · rw [List.mem_singleton.mp added]
            exact List.mem_cons_self
        simp only [log noCollision priorNext, Transcript.appendReply,
          originalRecords, List.append_assoc,
          List.singleton_append, Query.recordOfReply, compression, answered]

/-- Replay the collision-free original observation against any extension of its log. -/
theorem original_replay : SecondPreimageCoverageSpec.OriginalReplay := by
  intro n law initial blocks observation final supported noCollision extension
  obtain ⟨_, trace, terminal, logs⟩ :=
    replay_sample law initial blocks [] [] observation final supported extension
  have records := logs noCollision (fun _ present ↦ (List.not_mem_nil present).elim)
  exact ⟨trace, records, terminal⟩

private theorem bounded_query_step (fuel : ℕ) (old : Transcript n) (request : Query n)
    (resume : State n → TrialProgram n) (result : TrialResult n)
    (supported : some result ∈
      (TrialProgram.independentBounded fuel (.query request resume) old).support) :
    ∃ remaining answer updated, CacheStep old request answer updated ∧
      some result ∈ (TrialProgram.independentBounded remaining
        (resume answer) updated).support := by
  cases cached : old.cachedReply request with
  | some answer =>
    have same : TrialProgram.independentBounded fuel (.query request resume) old =
        TrialProgram.independentBounded fuel (resume answer) old := by
      unfold TrialProgram.independentBounded
      rw [TrialProgram.runBoundedWith.eq_1 _ fuel (.query request resume) old,
        TrialProgram.runBoundedWith.eq_1 _ fuel (resume answer) old, TrialProgram.nextFresh, cached]
    exact ⟨fuel, answer, old, .hit answer cached, same ▸ supported⟩
  | none =>
    have fresh : (TrialProgram.query request resume).nextFresh old = .query request resume := by
      simp only [TrialProgram.nextFresh, cached]
    cases fuel with
    | zero =>
      rw [TrialProgram.independentBounded_zero_of_query _ old fresh] at supported
      simp at supported
    | succ fuel =>
      rw [TrialProgram.independentBounded_succ_of_query fuel _ old fresh] at supported
      obtain ⟨answer, _, more⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      exact ⟨fuel, answer, old.appendReply request answer, .miss answer cached, more⟩

private theorem verify_support (changeTerminal : Option (State n) → Option (State n))
    (source : State n) (blocks : List (Word n)) (fuel : ℕ) (old : Transcript n)
      (result : TrialResult n)
    (supported : some result ∈ (TrialProgram.independentBounded fuel
      ((TrialProgram.verify source blocks).mapTerminal changeTerminal) old).support) :
    result.records.Extends old ∧
      result.terminal = changeTerminal (some (runWith result.records.forwardReply source blocks)) ∧
      Covers result.records.forwardReply result.records source blocks := by
  induction blocks generalizing source fuel old with
  | nil =>
    have atDone : ((TrialProgram.verify source []).mapTerminal changeTerminal).nextFresh old =
        .done (changeTerminal (some source)) := rfl
    rw [TrialProgram.independentBounded_of_done fuel _ old atDone] at supported
    have equal := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
    subst result
    exact ⟨List.prefix_refl _, rfl, trivial⟩
  | cons block rest ih =>
    let request : Query n := ⟨.forward, permInput source block⟩
    let resume (answer : State n) := (TrialProgram.verify (feedForward answer block)
        rest).mapTerminal changeTerminal
    obtain ⟨remaining, answer, updated, step, more⟩ :=
      bounded_query_step fuel old request resume result supported
    obtain ⟨extension, terminal, tailCovers⟩ := ih (feedForward answer block) remaining updated more
    obtain ⟨replied, record, present, input, output⟩ :=
      forward_hit extension (permInput source block) answer step.reply_cached
    have compression : compressWith result.records.forwardReply source block =
        feedForward answer block := by
      simp only [compressWith, replied]
    refine ⟨List.IsPrefix.trans step.extension extension, ?_, ?_⟩
    · rwa [runWith_cons, compression]
    · exact ⟨⟨record, present, input, output.trans replied.symm⟩, compression.symm ▸ tailCovers⟩

/-- A supported acceptance supplies a distinct candidate with the target capacity and record
coverage for every compression under the final cache. -/
theorem accepted_candidate : SecondPreimageCoverageSpec.AcceptedCandidate := by
  intro α n original target initial padding strategy fuel old result supported accepted
  induction strategy generalizing fuel old with
  | halt choice =>
    cases choice with
    | none =>
      have atDone : (TrialProgram.verifyDistinct original target initial padding
          (.halt none)).nextFresh old =
          .done none := rfl
      rw [TrialProgram.independentBounded_of_done fuel _ old atDone] at supported
      have equal := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)
      subst result
      cases accepted
    | some candidate =>
      let changeTerminal := fun terminal : Option (State n) ↦
        if candidate ≠ original ∧ terminal.map Prod.fst = some target then terminal else none
      obtain ⟨extension, terminal, covered⟩ :=
        verify_support changeTerminal initial (padding.encode candidate) fuel old result supported
      let finish := runWith result.records.forwardReply initial (padding.encode candidate)
      have accepts : candidate ≠ original ∧ finish.1 = target := by
        by_contra rejected
        have none : result.terminal = none := by
          simpa only [changeTerminal, finish, Option.map_some, Option.some.injEq,
            ite_eq_right rejected] using terminal
        rw [none] at accepted
        cases accepted
      refine ⟨extension, candidate, accepts.1, ?_, accepts.2, covered⟩
      simpa only [changeTerminal, finish, Option.map_some, Option.some.injEq,
        ite_eq_left accepts] using terminal
  | query request resume ih =>
    let next := fun answer ↦
        TrialProgram.verifyDistinct original target initial padding (resume answer)
    obtain ⟨remaining, answer, updated, step, more⟩ :=
      bounded_query_step fuel old request next result supported
    obtain ⟨extension, witness⟩ := ih answer remaining updated more
    exact ⟨List.IsPrefix.trans step.extension extension, witness⟩

/-- With a collision-free original trace, acceptance yields a nonempty path in the later graph
from an original state copy to a state in an original capacity column. -/
theorem accepted_path : SecondPreimageCoverageSpec.AcceptedPath := by
  intro α n law initial padding original observation strategy fuel result
    observed clean suffix accepted
  obtain ⟨extension, candidate, distinct, _, same, covered⟩ := accepted_candidate original
    observation.terminal.1 initial padding strategy fuel observation.records result suffix accepted
  obtain ⟨trace, logs, terminal⟩ := original_replay law initial (padding.encode original)
    observation result.records observed clean extension
  let reply := result.records.forwardReply
  let later := result.records.drop observation.records.length
  have concatenated : observation.records ++ later = result.records := by
    calc
      _ = result.records.take observation.records.length ++ later :=
        congrArg (· ++ later) (List.prefix_iff_eq_take.mp extension)
      _ = _ := List.take_append_drop _ _
  have covered' : Covers reply (originalRecords reply initial (padding.encode original) ++ later)
      initial (padding.encode candidate) := by
    rw [← logs, concatenated]
    exact covered
  have capacities : DistinctCapacities reply initial (padding.encode original) := by
    rw [DistinctCapacities, ← trace]
    exact Classical.not_not.mp clean
  have unequal : padding.encode original ≠ padding.encode candidate :=
    fun eq ↦ distinct (padding.injective eq).symm
  -- Both evaluations use the final cache. The path witness uses edges from the later records.
  have digest : (runWith reply initial (padding.encode candidate)).1 =
      (runWith reply initial (padding.encode original)).1 := same.trans (congrArg Prod.fst terminal)
  -- Injective padding gives distinct block sequences, as required for departure and return.
  obtain ⟨segment⟩ := departure_and_return reply initial (padding.encode original)
    (padding.encode candidate) later unequal capacities digest covered'
  have initials : observation.states.toFinset = initialStates reply initial
      (padding.encode original) :=
    congrArg List.toFinset trace
  dsimp only
  rw [initials, trace]
  exact ⟨segment.start, _, segment.target_column, segment.path, segment.nonempty⟩

end JH.SecondPreimageCoverage
