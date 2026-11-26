/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.IntersectionTailSpec
public import JH.Boundary.Mean
public import JH.Potential.Barrier.Replay
public import JH.Probability.Tape.AdaptiveMean

/-!
# The expected boundary population before a round

Section 3.4 controls the normalized forward and backward population using inheritance counts
and singleton-ledger graft charges. This version accepts the weighted graft coefficient of
Appendix A.3. Every charge uses its own pre-round activity test, which allows the costs to be
averaged over the full uniform tape.
-/

@[expose] public section

namespace JH.Probability.IntersectionTail

open JH.Graph JH.Parameters
open scoped BigOperators

variable {n : ℕ} {initials : Finset (State n)}

private theorem population_nonneg (sides : Boundary (Vertex initials)) : 0 ≤ population sides := by
  unfold population
  positivity

/-- Count newly added real vertices in fibers of their row or column coordinate. -/
private theorem ncard_added_le_lines (old new : Set (Vertex initials)) (coords : State n ≃ State n)
    (realAdded : ∀ v ∈ new \ old, ∃ state : State n, v = .inl state) :
    new.ncard ≤ old.ncard + ∑ line : Word n,
      ({free | Sum.inl (coords (line, free)) ∈ new \ old} : Set (Word n)).ncard := by
  let cells (line : Word n) : Set (Word n) := {free | Sum.inl (coords (line, free)) ∈ new \ old}
  let toGraph : (Σ line : Word n, cells line) → ↥(new \ old) :=
    fun p ↦ ⟨Sum.inl (coords (p.1, p.2.val)), p.2.property⟩
  have onto : Function.Surjective toGraph := by
    rintro ⟨vertex, member⟩
    obtain ⟨state, rfl⟩ := realAdded vertex member
    let pair := coords.symm state
    have returns : coords (pair.1, pair.2) = state := coords.apply_symm_apply state
    have inCell : pair.2 ∈ cells pair.1 := by
      change Sum.inl (coords (pair.1, pair.2)) ∈ new \ old
      rwa [returns]
    exact ⟨⟨pair.1, ⟨pair.2, inCell⟩⟩, Subtype.ext (congrArg Sum.inl returns)⟩
  have bound := Nat.card_le_card_of_surjective toGraph onto
  rw [Nat.card_sigma] at bound
  calc
    new.ncard ≤ (new \ old).ncard + old.ncard := Set.ncard_le_ncard_sdiff_add_ncard new old
    _ ≤ (∑ line : Word n, (cells line).ncard) + old.ncard := Nat.add_le_add_right bound _
    _ = _ := Nat.add_comm _ _

private theorem grafted_line_ncard (old new : Set (Vertex initials)) (line : Word n → State n) :
    ({free | Sum.inl (line free) ∈ new \ old} : Set (Word n)).ncard =
      (graftedOnLine old new line).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext free
  simp [graftedOnLine]

private theorem forward_added_real {before after : Boundary (Vertex initials)}
    (hasStarts : before.ContainsVirtualStarts) :
    ∀ v ∈ after.forward \ before.forward, ∃ state : State n, v = .inl state := by
  rintro (state | start) member
  · exact ⟨state, rfl⟩
  · exact (member.2 (hasStarts start)).elim

private theorem backward_added_real {before after : Boundary (Vertex initials)}
    (hasStarts : after.ContainsVirtualStarts) (disjoint : ¬ after.Intersects) :
    ∀ v ∈ after.backward \ before.backward, ∃ state : State n, v = .inl state := by
  rintro (state | start) member
  · exact ⟨state, rfl⟩
  · exact (disjoint ⟨.inr start, hasStarts start, member.1⟩).elim

/-- Number of coordinates inherited over all forward columns and backward rows in a round. -/
private noncomputable def inheritedTotal (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before : Boundary (Vertex initials)) : ℝ :=
  (∑ line : Word n,
    (BoundaryMean.inheritedCount transcript record threshold before .forward line : ℝ)) +
    ∑ line : Word n,
      (BoundaryMean.inheritedCount transcript record threshold before .backward line : ℝ)

/-- Number of vertices grafted on both sides between inheritance and the end of the round. -/
private noncomputable def graftTotal (inherited finish : Boundary (Vertex initials)) : ℝ :=
  (∑ line : Word n, (forwardGraftCount inherited finish line : ℝ)) +
    ∑ line : Word n, (backwardGraftCount inherited finish line : ℝ)

/-- Charge both stages of each continued boundary update by counting its new real vertices. -/
private theorem round_population_growth (transcript : Transcript n) (record : Record n)
    (threshold : ℕ) (before finish : Boundary (Vertex initials))
    (hasStarts : before.ContainsVirtualStarts)
    (continued : RoundStep transcript record threshold before (.continued finish)) :
    let inherited := before.inherit (recordRelation (transcript ++ [record]) initials)
    population finish ≤ population before + inheritedTotal transcript record threshold before +
      graftTotal inherited finish := by
  let updated := recordRelation (transcript ++ [record]) initials
  let inherited := before.inherit updated
  have grows := (Boundary.inheritance updated before).1
  have inheritedStarts : inherited.ContainsVirtualStarts := fun start ↦ grows.1 (hasStarts start)
  obtain ⟨_, finishStarts, _, _, finishDisjoint, _⟩ :=
    round_continuation transcript record threshold initials before finish hasStarts continued
  -- Count inheritance first and then grafting, separately for each direction.
  have inheritF : inherited.forward.ncard ≤ before.forward.ncard + ∑ column : Word n,
      (BoundaryEvents.forwardInheritedRates transcript record before column).ncard :=
    ncard_added_le_lines _ _ (Equiv.refl _) (forward_added_real hasStarts)
  have inheritB : inherited.backward.ncard ≤ before.backward.ncard + ∑ row : Word n,
      (BackwardBoundaryEvents.backwardInheritedCaps transcript record before row).ncard :=
    ncard_added_le_lines _ _ (Equiv.prodComm _ _) (backward_added_real inheritedStarts continued.1)
  have graftF : finish.forward.ncard ≤ inherited.forward.ncard + ∑ column : Word n,
      forwardGraftCount inherited finish column := by
    have bound := ncard_added_le_lines inherited.forward finish.forward (Equiv.refl _)
      (forward_added_real inheritedStarts)
    simpa only [Equiv.refl_apply, grafted_line_ncard, forwardGraftCount] using bound
  have graftB : finish.backward.ncard ≤ inherited.backward.ncard + ∑ row : Word n,
      backwardGraftCount inherited finish row := by
    have bound := ncard_added_le_lines inherited.backward finish.backward (Equiv.prodComm _ _)
      (backward_added_real finishStarts finishDisjoint)
    simpa only [Equiv.prodComm_apply, Prod.swap_prod_mk, grafted_line_ncard,
      backwardGraftCount] using bound
  have inheritFReal : (inherited.forward.ncard : ℝ) ≤
      (before.forward.ncard : ℝ) + ∑ column : Word n,
      (BoundaryMean.inheritedCount transcript record threshold before .forward column : ℝ) := by
    simp only [BoundaryMean.inheritedCount_of_continued continued]
    exact_mod_cast inheritF
  have inheritBReal : (inherited.backward.ncard : ℝ) ≤ (before.backward.ncard : ℝ) + ∑ row : Word n,
      (BoundaryMean.inheritedCount transcript record threshold before .backward row : ℝ) := by
    simp only [BoundaryMean.inheritedCount_of_continued continued]
    exact_mod_cast inheritB
  have graftFReal : (finish.forward.ncard : ℝ) ≤ (inherited.forward.ncard : ℝ) + ∑ column : Word n,
      (forwardGraftCount inherited finish column : ℝ) := by exact_mod_cast graftF
  have graftBReal : (finish.backward.ncard : ℝ) ≤ (inherited.backward.ncard : ℝ) + ∑ row : Word n,
      (backwardGraftCount inherited finish row : ℝ) := by exact_mod_cast graftB
  change population finish ≤ population before + inheritedTotal transcript record threshold before +
    graftTotal inherited finish
  unfold population inheritedTotal graftTotal
  linarith only [inheritFReal, inheritBReal, graftFReal, graftBReal]

/-- The accumulated graft count on the chosen side and line. -/
private noncomputable def graftsFor (snapshot : GraphSnapshot initials)
    (side : Direction) (line : Word n) : ℝ :=
  match side with
  | .forward => snapshot.forwardGrafts line
  | .backward => snapshot.backwardGrafts line

/-- Sum the graft counters over all lines in both directions. -/
private noncomputable def accruedGrafts (snapshot : GraphSnapshot initials) : ℝ :=
  (∑ line : Word n, graftsFor snapshot .forward line) + ∑ line : Word n,
    graftsFor snapshot .backward line

private theorem accruedGrafts_after (snapshot : GraphSnapshot initials) (record : Record n)
    (finish : Boundary (Vertex initials)) :
    accruedGrafts (snapshot.afterGrafting record finish) = accruedGrafts snapshot +
      graftTotal (snapshot.sides.inherit
        (recordRelation (snapshot.records ++ [record]) initials)) finish := by
  simp only [accruedGrafts, graftsFor, GraphSnapshot.afterGrafting, graftTotal, Nat.cast_add,
    Finset.sum_add_distrib]
  ring

/-- Sum of the forward and backward inheritance costs in the round. -/
private noncomputable def roundInheritance (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) : AdaptiveMean.Quantity (State params.n) q :=
  fun i prior word ↦ inheritanceCost params psi starts targets program .forward i prior word +
    inheritanceCost params psi starts targets program .backward i prior word

/-- Combine inheritance counts and singleton-ledger charges in both directions. -/
private noncomputable def roundCost (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) : AdaptiveMean.Quantity (State params.n) q :=
  fun i prior word ↦ roundInheritance params psi starts targets program i prior word +
    (graftCharge params psi starts targets program .forward i prior word +
      graftCharge params psi starts targets program .backward i prior word)

/-- Bound the population of an active prefix by its initial population and all added points. -/
private theorem population_prefix_le (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n) (k : ℕ) (within : k ≤ q)
    (snapshot : GraphSnapshot starts)
    (active : BarrierReplay.trackerAfterPrefix params psi starts targets
      program tape k within = .active snapshot) :
    population snapshot.sides ≤ population (initialBoundary starts targets) +
      (∑ j : Fin k, roundInheritance params psi starts targets program (j.castLE within)
        (TapeTests.prefixAt tape (j.castLE within)) (tape (j.castLE within))) +
          accruedGrafts snapshot := by
  induction k generalizing snapshot with
  | zero =>
    have same : GraphSnapshot.initial starts targets = snapshot := GraphTracker.active.inj active
    subst snapshot
    simp [GraphSnapshot.initial, accruedGrafts, graftsFor]
  | succ k ih =>
    let i : Fin q := ⟨k, Nat.lt_of_succ_le within⟩
    let old := BarrierReplay.prefixState program tape k (Nat.le_of_succ_le within)
    let new := BarrierReplay.prefixState program tape (k + 1) within
    let tracker := BarrierReplay.trackerAfterPrefix params psi starts targets program tape k
      (Nat.le_of_succ_le within)
    let later := BarrierReplay.trackerAfterPrefix params psi starts targets
        program tape (k + 1) within
    have agrees : BarrierReplay.beforeRound program i (TapeTests.prefixAt tape i) = old :=
      BarrierReplay.beforeRound_eq_runPrefix program tape i
    change later = .active snapshot at active
    rw [Fin.sum_univ_castSucc]
    change population snapshot.sides ≤ population (initialBoundary starts targets) +
      ((∑ j : Fin k, roundInheritance params psi starts targets program
        (j.castLE (Nat.le_of_succ_le within))
          (TapeTests.prefixAt tape (j.castLE (Nat.le_of_succ_le within)))
        (tape (j.castLE (Nat.le_of_succ_le within)))) +
        roundInheritance params psi starts targets program i (TapeTests.prefixAt tape i) (tape i)) +
      accruedGrafts snapshot
    cases reached : old.frontier with
    | done terminal =>
      have sameState : new = old := by
        change old.step (tape i).1 (tape i).2 = old
        rw [TapeState.step, reached]
      have sameTracker : later = tracker := congrArg
        (fun state : TapeState params.n ↦ GraphTracker.replay params psi starts targets
          state.records) sameState
      have prior := ih (Nat.le_of_succ_le within) snapshot (sameTracker.symm.trans active)
      have noInheritance : roundInheritance params psi starts targets program i
          (TapeTests.prefixAt tape i)
          (tape i) = 0 := by rw [roundInheritance, inheritanceCost, inheritanceCost, agrees,
            reached, add_zero]
      simpa only [noInheritance, add_zero] using prior
    | query request resume =>
      let record := request.recordOfReply (request.replyCoords.symm (tape i))
      have appended : new.records = old.records ++ [record] :=
        (TapeState.live_round (⟨program, []⟩ : TapeState params.n) (fun j ↦ (tape j).1)
          (fun j ↦ (tape j).2) i request resume reached).2.1
      have next : later = tracker.advance params psi record := by
        change GraphTracker.replay params psi starts targets new.records = _
        rw [appended]
        exact GraphTracker.replay_append params psi starts targets old.records [record]
      rw [next] at active
      cases priorTracker : tracker with
      | stopped reason previous => simp [priorTracker, GraphTracker.advance] at active
      | active previous =>
        rw [priorTracker] at active
        obtain ⟨finish, rfl, continued, _⟩ := GraphTracker.active_advance active
        have prior := ih (Nat.le_of_succ_le within) previous priorTracker
        have recorded : GraphTracker.replay params psi starts targets old.records = .active
            previous := priorTracker
        have valid := (graph_active_replay params psi starts targets old.records
            previous recorded).2
        have growth := round_population_growth previous.records record
            params.mu previous.sides finish
          valid.1 continued
        have paid := accruedGrafts_after previous record finish
        have current : roundInheritance params psi starts targets program i
            (TapeTests.prefixAt tape i)
            (tape i) = inheritedTotal previous.records record params.mu previous.sides := by
          simp only [roundInheritance, inheritanceCost, agrees, reached,
            recorded, inheritedTotal, record]
        rw [current, paid]
        change population finish ≤ _
        linarith only [growth, prior]

private theorem translated_nonneg (edge : State n → State n → Prop) (vertices : Set (State n))
    (mu d : ℕ) (line : Word n) (mode : Finset (Word n)) :
    0 ≤ translatedPotential edge vertices mu d line mode := by
  unfold translatedPotential
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ (forward_weight_range _ _ _ _ _).1) (by positivity)

private theorem graftsFor_le_ledger (params : Params) {starts : Finset (State params.n)}
    (snapshot : GraphSnapshot starts) (side : Direction) (line : Word params.n) :
    graftsFor snapshot side line ≤ snapshot.ledger params.mu params.d side line {0} := by
  cases side with
  | forward =>
    simp only [graftsFor, GraphSnapshot.ledger]
    exact le_add_of_nonneg_left (translated_nonneg _ _ _ _ _ _)
  | backward =>
    simp only [graftsFor, GraphSnapshot.ledger, backwardTranslatedPotential]
    exact le_add_of_nonneg_left (translated_nonneg _ _ _ _ _ _)

/-- Sum the singleton-ledger bounds to pay for all accrued grafts on one side. -/
private theorem grafts_prefix_le (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n) (k : ℕ) (within : k ≤ q)
    (snapshot : GraphSnapshot starts)
    (active : BarrierReplay.trackerAfterPrefix params psi starts targets
      program tape k within = .active snapshot)
    (positiveMu : 0 < params.mu) (positiveD : 0 < params.d) (side : Direction) :
    (∑ line : Word params.n, graftsFor snapshot side line) ≤
      (params.N : ℝ) * ((params.N : ℝ) / (params.mu : ℝ) ^ params.d) +
        ∑ j : Fin k, graftCharge params psi starts targets program side (j.castLE within)
          (TapeTests.prefixAt tape (j.castLE within)) (tape (j.castLE within)) := by
  have noIntersection : (BarrierReplay.trackerAfterPrefix params psi starts
      targets program tape k within).stopReason ≠
      some .intersect := by rw [active]; simp [GraphTracker.stopReason]
  -- The ledger bounds each line's graft counter because its potential is nonnegative.
  have each (line : Word params.n) : graftsFor snapshot side line ≤
      (params.N : ℝ) / (params.mu : ℝ) ^ params.d +
        ∑ j : Fin k, BarrierReplay.ledgerCost params psi starts targets program side line
          {0} (j.castLE within)
          (TapeTests.prefixAt tape (j.castLE within)) (tape (j.castLE within)) := by
    have ledger := BarrierReplay.ledger_at_prefix_le_sum params psi starts targets program tape
      positiveMu positiveD side line {0} k within noIntersection
    rw [active, GraphTracker.snapshot] at ledger
    exact (graftsFor_le_ledger params snapshot side line).trans
      (ledger.trans (add_le_add (BarrierReplay.initial_ledger_bound params starts targets
        positiveMu positiveD side line {0}) le_rfl))
  calc
    _ ≤ ∑ line : Word params.n, ((params.N : ℝ) / (params.mu : ℝ) ^ params.d +
        ∑ j : Fin k, BarrierReplay.ledgerCost params psi starts targets program side line
          {0} (j.castLE within)
          (TapeTests.prefixAt tape (j.castLE within)) (tape (j.castLE within))) :=
      Finset.sum_le_sum fun line _ ↦ each line
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, word_card, nsmul_eq_mul]
      unfold graftCharge
      rw [Finset.sum_comm]
      rfl

private theorem inheritance_nonneg (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (side : Direction) (i : Fin q) (prior : Fin i.val → State params.n) (word : State params.n) :
    0 ≤ inheritanceCost params psi starts targets program side i prior word := by
  unfold inheritanceCost
  dsimp only
  split
  · exact le_rfl
  split
  · exact le_rfl
  · exact Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

private theorem graft_charge_nonneg (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (side : Direction) (i : Fin q) (prior : Fin i.val → State params.n) (word : State params.n) :
    0 ≤ graftCharge params psi starts targets program side i prior word :=
  Finset.sum_nonneg fun line _ ↦
    (BarrierReplay.ledger_cost_range params q psi starts targets program
      initialValid side line {0} i prior word).1

private theorem round_cost_nonneg (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (i : Fin q) (prior : Fin i.val → State params.n) (word : State params.n) :
    0 ≤ roundCost params psi starts targets program i prior word :=
  add_nonneg (add_nonneg
    (inheritance_nonneg params psi starts targets program .forward i prior word)
    (inheritance_nonneg params psi starts targets program .backward i prior word))
    (add_nonneg (graft_charge_nonneg params psi starts targets program
      initialValid .forward i prior word)
      (graft_charge_nonneg params psi starts targets program initialValid .backward i prior word))

private theorem sum_prefix_le {q k : ℕ} (within : k ≤ q) (f : Fin q → ℝ)
    (nonnegative : ∀ j, 0 ≤ f j) : (∑ j : Fin k, f (j.castLE within)) ≤ ∑ j : Fin q, f j := by
  let e : Fin k ↪ Fin q :=
    ⟨Fin.castLE within, fun _ _ eq ↦ Fin.ext (congrArg (fun j : Fin q ↦ j.val) eq)⟩
  change (∑ j : Fin k, f (e j)) ≤ _
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ ↦ nonnegative j

/-- Dominate the activity-weighted population by initial terms and the full cost sum. -/
private theorem normalized_population_pointwise (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (positiveMu : 0 < params.mu) (positiveD : 0 < params.d) (initialBound : ℝ)
    (initialPop : population (initialBoundary starts targets) / (params.N : ℝ) ≤ initialBound)
    (tape : Fin q → State params.n) (k : ℕ) (within : k ≤ q) :
    activePopulation params
      (BarrierReplay.trackerAfterPrefix params psi starts targets program tape k within) ≤
      initialBound + 2 * (params.N : ℝ) / (params.mu : ℝ) ^ params.d +
        AdaptiveMean.total (roundCost params psi starts targets program) tape / (params.N : ℝ) := by
  let N : ℝ := (params.N : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr params.N_pos
  let cost (i : Fin q) :=
    roundCost params psi starts targets program i (TapeTests.prefixAt tape i) (tape i)
  have costsNonneg (i : Fin q) : 0 ≤ cost i :=
    round_cost_nonneg params psi starts targets program initialValid i
      (TapeTests.prefixAt tape i) (tape i)
  have initialNonneg : 0 ≤ initialBound := (div_nonneg (population_nonneg _) hN.le).trans initialPop
  cases tracked :
    BarrierReplay.trackerAfterPrefix params psi starts targets program tape k within with
  | stopped reason snapshot =>
    change 0 ≤ initialBound + 2 * N / (params.mu : ℝ) ^ params.d + (∑ i : Fin q, cost i) / N
    exact add_nonneg (add_nonneg initialNonneg (by positivity))
      (div_nonneg (Finset.sum_nonneg fun i _ ↦ costsNonneg i) hN.le)
  | active snapshot =>
    have base := population_prefix_le params psi starts targets program tape
        k within snapshot tracked
    have graftF := grafts_prefix_le params psi starts targets program tape k within snapshot tracked
      positiveMu positiveD .forward
    have graftB := grafts_prefix_le params psi starts targets program tape k within snapshot tracked
      positiveMu positiveD .backward
    have accumulated : population snapshot.sides ≤ population (initialBoundary starts targets) +
        2 * N * (N / (params.mu : ℝ) ^ params.d) + ∑ j : Fin k, cost (j.castLE within) := by
      simp only [accruedGrafts] at base
      simp only [cost, roundCost, Finset.sum_add_distrib]
      have scale : 2 * N * (N / (params.mu : ℝ) ^ params.d) =
          N * (N / (params.mu : ℝ) ^ params.d) + N * (N / (params.mu : ℝ) ^ params.d) := by ring
      rw [scale]
      linarith only [base, graftF, graftB]
    -- Nonnegative charges extend the bound to the whole horizon on the original tape law.
    have extended := accumulated.trans
      (add_le_add le_rfl (sum_prefix_le within cost costsNonneg))
    change population snapshot.sides / N ≤ initialBound + 2 * N / (params.mu : ℝ) ^ params.d +
      (∑ i : Fin q, cost i) / N
    calc
      _ ≤ (population (initialBoundary starts targets) + 2 * N * (N / (params.mu : ℝ) ^ params.d) +
          ∑ i : Fin q, cost i) / N := div_le_div_of_nonneg_right extended hN.le
      _ = population (initialBoundary starts targets) / N + 2 * N / (params.mu : ℝ) ^ params.d +
          (∑ i : Fin q, cost i) / N := by ring_nf; field_simp
      _ ≤ _ := add_le_add (add_le_add initialPop le_rfl) le_rfl

private theorem record_count_le {n q : ℕ} (program : TrialProgram n) (i : Fin q)
    (prior : Fin i.val → State n) :
      (BarrierReplay.beforeRound program i prior).records.length ≤ q := by
  have raw := TapeState.records_length_le_round (⟨program, []⟩ : TapeState n)
    (fun j ↦ (prior j).1) (fun j ↦ (prior j).2) i.val le_rfl
  have bound : (BarrierReplay.beforeRound program i prior).records.length ≤ i.val := by
    simpa only [BarrierReplay.beforeRound, BarrierReplay.prefixState,
      List.length_nil, Nat.zero_add] using raw
  exact bound.trans (Nat.le_of_lt i.isLt)

private theorem time_factor_le (params : Params) {k q : ℕ} (lengthBound : k ≤ q) :
    1 + (k : ℝ) * params.Theta / (params.N : ℝ) ≤ 1 + (q : ℝ) * params.Theta / (params.N : ℝ) :=
  add_le_add le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr lengthBound) (by positivity)) (by positivity))

/-- Average inherited vertices over the fresh offset using the total endpoint bound. -/
private theorem inheritance_mean (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (side : Direction) (i : Fin q) (prior : Fin i.val → State params.n)
      (intrinsic : Word params.n) :
    wordMean (fun shift ↦
      inheritanceCost params psi starts targets program side i prior (intrinsic, shift)) ≤
      (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) * ((psi : ℝ) + params.Pi) := by
  have nonneg : 0 ≤ (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
      ((psi : ℝ) + params.Pi) := by positivity
  cases reached : (BarrierReplay.beforeRound program i prior).frontier with
  | done terminal => simpa [inheritanceCost, reached, wordMean] using nonneg
  | query request resume =>
    cases recorded : GraphTracker.replay params psi starts targets
        (BarrierReplay.beforeRound program i prior).records with
    | stopped reason snapshot => simpa [inheritanceCost, reached, recorded, wordMean] using nonneg
    | active snapshot =>
      obtain ⟨sameRecords, validBoundary⟩ := graph_active_replay params psi starts targets
        (BarrierReplay.beforeRound program i prior).records snapshot recorded
      have valid := graph_active_parameters params psi starts targets initialValid
        (BarrierReplay.beforeRound program i prior).records snapshot recorded
      obtain ⟨column, row, shares⟩ := request.recordOfReply_sharesExposedCoordinates intrinsic
      let recordFor (shift : Word params.n) :=
        request.recordOfReply (request.replyCoords.symm (intrinsic, shift))
      have endpoint := GraphSnapshot.endpoint_bounds params psi snapshot valid
      have countBound : snapshot.records.length ≤ q := sameRecords ▸ record_count_le program i prior
      refine (le_trans ?_
        (mul_le_mul_of_nonneg_right (time_factor_le params countBound) (by positivity)))
      cases side with
      | forward =>
        have mean := BoundaryMean.forward_inheritance_mean snapshot.records params.mu snapshot.sides
          column row psi params.Pi params.Theta recordFor validBoundary.1 validBoundary.2.1 shares
          endpoint (valid.2.2.2.1 column)
        simpa only [inheritanceCost, reached, recorded, recordFor, Params.N, Nat.cast_pow,
          Nat.cast_ofNat] using mean
      | backward =>
        have mean := BoundaryMean.backward_inheritance_mean snapshot.records
            params.mu snapshot.sides
          column row psi params.Pi params.Theta recordFor validBoundary.1 validBoundary.2.1 shares
          endpoint (valid.2.2.2.2 row)
        simpa only [inheritanceCost, reached, recorded, recordFor, Params.N, Nat.cast_pow,
          Nat.cast_ofNat] using mean

/-- Average the total singleton graft charge for the fixed intrinsic coordinate. -/
private theorem graft_mean (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (theta : ℝ) (positiveD : 0 < params.d) (positiveTheta : 0 < theta)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (side : Direction) (i : Fin q) (prior : Fin i.val → State params.n)
      (intrinsic : Word params.n) :
    wordMean (fun shift ↦
      graftCharge params psi starts targets program side i prior (intrinsic, shift)) ≤
      (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
        (params.weightedCoefficient theta + (params.Pi : ℝ)) := by
  have costNonneg : 0 ≤ params.weightedCoefficient theta + (params.Pi : ℝ) := by
    unfold Params.weightedCoefficient Analysis.weightedCost
    positivity
  have nonneg : 0 ≤ (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
      (params.weightedCoefficient theta + (params.Pi : ℝ)) := by positivity
  cases reached : (BarrierReplay.beforeRound program i prior).frontier with
  | done terminal => simpa [graftCharge, BarrierReplay.ledgerCost, reached, wordMean] using nonneg
  | query request resume =>
    cases recorded : GraphTracker.replay params psi starts targets
        (BarrierReplay.beforeRound program i prior).records with
    | stopped reason snapshot =>
      simpa [graftCharge, BarrierReplay.ledgerCost, reached, recorded,
        GraphTracker.charge, wordMean] using nonneg
    | active snapshot =>
      have sameRecords := (graph_active_replay params psi starts targets
        (BarrierReplay.beforeRound program i prior).records snapshot recorded).1
      have valid := graph_active_parameters params psi starts targets initialValid
        (BarrierReplay.beforeRound program i prior).records snapshot recorded
      obtain ⟨column, row, shares⟩ := request.recordOfReply_sharesExposedCoordinates intrinsic
      let recordFor (shift : Word params.n) :=
        request.recordOfReply (request.replyCoords.symm (intrinsic, shift))
      have countBound : snapshot.records.length ≤ q := sameRecords ▸ record_count_le program i prior
      have mean := active_total_point_weighted_mean params psi snapshot column row recordFor theta
        positiveD positiveTheta valid shares side
      simpa only [graftCharge, BarrierReplay.ledgerCost, reached, recorded, recordFor] using
        mean.trans (mul_le_mul_of_nonneg_right (time_factor_le params countBound) costNonneg)

private theorem expect_word_eq_mean {n : ℕ} (f : Word n → ℝ) :
    (𝔼 word : Word n, f word) = wordMean f := by
  rw [Fintype.expect_eq_sum_div_card, wordMean, word_card, Nat.cast_pow, Nat.cast_ofNat]

private theorem round_cost_mean (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (theta : ℝ) (positiveD : 0 < params.d) (positiveTheta : 0 < theta)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi)
    (i : Fin q) (prior : Fin i.val → State params.n) :
    (𝔼 word : State params.n, roundCost params psi starts targets program i prior word) ≤
      2 * (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
        (params.weightedCoefficient theta + (psi : ℝ) + 2 * (params.Pi : ℝ)) := by
  -- Each offset mean has the same bound at every fixed intrinsic coordinate.
  rw [AdaptiveMean.expect_product]
  apply Finset.expect_le Finset.univ_nonempty
  intro intrinsic _
  rw [expect_word_eq_mean]
  simp only [roundCost, roundInheritance, wordMean_add]
  have f := inheritance_mean params psi starts targets program initialValid
      .forward i prior intrinsic
  have b := inheritance_mean params psi starts targets program initialValid
      .backward i prior intrinsic
  have gf := graft_mean params psi starts targets program theta positiveD positiveTheta initialValid
    .forward i prior intrinsic
  have gb := graft_mean params psi starts targets program theta positiveD positiveTheta initialValid
    .backward i prior intrinsic
  refine (add_le_add (add_le_add f b) (add_le_add gf gb)).trans_eq ?_
  ring

private theorem round_cost_total_mean (params : Params) {q : ℕ} (psi : ℕ)
    (starts : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (theta : ℝ) (positiveD : 0 < params.d) (positiveTheta : 0 < theta)
    (initialValid : (GraphSnapshot.initial starts targets).ValidParameters params psi) :
    (𝔼 tape : Fin q → State params.n,
      AdaptiveMean.total (roundCost params psi starts targets program) tape) ≤
      (q : ℝ) * (2 * (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
        (params.weightedCoefficient theta + (psi : ℝ) + 2 * (params.Pi : ℝ))) := by
  let allowance := 2 * (1 + (q : ℝ) * params.Theta / (params.N : ℝ)) *
    (params.weightedCoefficient theta + (psi : ℝ) + 2 * (params.Pi : ℝ))
  unfold AdaptiveMean.total
  -- Linearity reduces the total mean to separate estimates on each round's prefix law.
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ _ : Fin q, allowance := by
      apply Finset.sum_le_sum
      intro i _
      rw [AdaptiveMean.expect_adapted_round]
      apply Finset.expect_le Finset.univ_nonempty
      intro prior _
      exact round_cost_mean params psi starts targets program theta positiveD
        positiveTheta initialValid i prior
    _ = (q : ℝ) * allowance := by simp [nsmul_eq_mul]

/-- Bound the mean of the activity-weighted population for every pre-round prefix length. -/
theorem active_population_mean : IntersectionTailSpec.ActivePopulationMean := by
  intro params q psi starts targets program theta initialBound cert occupancy
    positiveTheta initialPop i
  have positiveMu : 0 < params.mu := by have := cert.admissible.mu_ge_two; omega
  have positiveD : 0 < params.d := by have := cert.admissible.d_ge_two; omega
  have initialValid := graph_initial_parameters params q psi starts targets cert occupancy
  have meanCost := round_cost_total_mean (q := q) params psi starts targets program theta
    positiveD positiveTheta initialValid
  -- The population depends solely on the prefix, so its mean can be taken over full tapes.
  have oldHistory :
      (𝔼 prior : Fin i.val → State params.n,
        populationBefore params psi starts targets program i prior) =
      𝔼 tape : Fin q → State params.n, activePopulation params
        (BarrierReplay.trackerAfterPrefix params psi starts targets program tape i.val
          (Nat.le_of_lt i.isLt)) := by
    have adapted := (AdaptiveMean.expect_adapted_round
      (fun j prior _ ↦ populationBefore params psi starts targets program j prior) i).symm
    simpa only [Fintype.expect_const, populationBefore, BarrierReplay.beforeRound_eq_runPrefix,
      BarrierReplay.trackerAfterPrefix] using adapted
  rw [oldHistory]
  calc
    _ ≤ 𝔼 tape : Fin q → State params.n,
        (initialBound + 2 * (params.N : ℝ) / (params.mu : ℝ) ^ params.d +
          AdaptiveMean.total (roundCost params psi starts targets program) tape / (params.N : ℝ)) :=
      Finset.expect_le_expect fun tape _ ↦
        normalized_population_pointwise params psi starts targets program
        initialValid positiveMu positiveD initialBound initialPop tape i.val (Nat.le_of_lt i.isLt)
    _ = initialBound + 2 * (params.N : ℝ) / (params.mu : ℝ) ^ params.d +
        (𝔼 tape : Fin q → State params.n,
          AdaptiveMean.total (roundCost params psi starts targets program) tape) /
            (params.N : ℝ) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.expect_div]
    _ ≤ _ := by
      unfold populationBound
      have bound := div_le_div_of_nonneg_right meanCost
          (Nat.cast_nonneg params.N : (0 : ℝ) ≤ params.N)
      convert add_le_add (le_refl (initialBound + 2 * (params.N : ℝ) / (params.mu : ℝ) ^ params.d))
        bound using 1
      ring

end JH.Probability.IntersectionTail
