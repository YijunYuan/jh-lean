/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.StoppedGraphSpec
public import JH.Parameters.Certificate
public import JH.Potential.GraftLedger

/-!
# Replay and the first stopping round

The replay consumes fresh-record positions in order and freezes the first stopping snapshot.
Intersection is tested after inheritance. A disjoint round finishes its grafts before the
potential, path-count and occupancy checks, in that order. The active snapshot records the
invariants used to bound the next round.
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters

variable {params : Params} {initials : Finset (State params.n)}

/-- Identify the first failed test among the three checks on a disjoint, grafted snapshot. -/
theorem graph_threshold_priority : StoppedGraphSpec.ThresholdPriority := by
  intro params psi initials snapshot
  classical
  by_cases hbarrier : snapshot.BelowBarrier params <;>
  by_cases hpaths : snapshot.PathsBounded params.pi <;>
  by_cases hoccupancy : snapshot.OccupancyBounded psi <;>
  simp [GraphTracker.classify, hbarrier, hpaths, hoccupancy]

theorem GraphTracker.selected_round_legal (snapshot : GraphSnapshot initials)
    (record : Record params.n) :
    RoundStep snapshot.records record params.mu snapshot.sides
      (selectRound params snapshot record) :=
  (round_exists snapshot.records record params.mu initials snapshot.sides).choose_spec

theorem GraphTracker.classified_snapshot (psi : ℕ) (snapshot : GraphSnapshot initials) :
    (classify params psi snapshot).snapshot = snapshot := by
  unfold classify
  split
  · rfl
  split
  · rfl
  split <;> rfl

private theorem classified_active_eq {psi : ℕ} {snapshot after : GraphSnapshot initials}
    (h : GraphTracker.classify params psi snapshot = .active after) : snapshot = after := by
  unfold GraphTracker.classify at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · exact GraphTracker.active.inj h

/-- An active result gives the legal grafted snapshot and certifies all three checks. -/
theorem GraphTracker.active_advance {psi : ℕ} {snapshot after : GraphSnapshot initials}
    {record : Record params.n}
    (h : advance params psi (.active snapshot) record = .active after) :
    ∃ finish, after = snapshot.afterGrafting record finish ∧
      RoundStep snapshot.records record params.mu snapshot.sides (.continued finish) ∧
      after.BelowBarrier params ∧ after.PathsBounded params.pi ∧ after.OccupancyBounded psi := by
  have legal := selected_round_legal snapshot record
  cases chosen : selectRound params snapshot record with
  | intersected => simp [advance, chosen] at h
  | continued finish =>
      rw [chosen] at legal
      have hc : classify params psi (snapshot.afterGrafting record finish) = .active after := by
        simpa only [advance, chosen] using h
      have heq := classified_active_eq hc
      refine ⟨finish, heq.symm, legal, ?_⟩
      rw [heq] at hc
      exact (graph_threshold_priority params psi after).2.2.2.mp hc

theorem GraphSnapshot.initial_valid (initials : Finset (State params.n))
    (targets : Set (Word params.n)) : (initial initials targets).ValidBoundary targets := by
  obtain ⟨starts, separate, closed⟩ := initial_boundary_invariants initials targets
  exact ⟨starts, closed, separate, fun state inTargets ↦ ⟨state, rfl, inTargets⟩⟩

theorem GraphSnapshot.valid_after_grafting {targetColumns : Set (Word params.n)}
    {snapshot : GraphSnapshot initials} {record : Record params.n}
      {finish : Boundary (Vertex initials)}
    (valid : snapshot.ValidBoundary targetColumns)
    (legal : RoundStep snapshot.records record params.mu snapshot.sides (.continued finish)) :
    (snapshot.afterGrafting record finish).ValidBoundary targetColumns := by
  obtain ⟨grows, virtual, _, closed, separate, _⟩ :=
    round_continuation snapshot.records record params.mu initials snapshot.sides
      finish valid.1 legal
  exact ⟨virtual, closed, separate, fun state inTargets ↦ grows.2 (valid.2.2.2 state inTargets)⟩

theorem GraphTracker.replay_append (params : Params) (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (before after : Transcript params.n) :
    replay params psi initials targets (before ++ after) =
      after.foldl (advance params psi) (replay params psi initials targets before) := by
  simp only [replay, List.foldl_append]

private theorem fold_advance_stopped (psi : ℕ) (reason : FirstGraphStop)
    (snapshot : GraphSnapshot initials) (records : Transcript params.n) :
    records.foldl (GraphTracker.advance params psi) (.stopped reason snapshot) =
      .stopped reason snapshot := by
  induction records with
  | nil => rfl
  | cons record tail ih => simpa only [List.foldl_cons, GraphTracker.advance] using ih

theorem GraphTracker.replay_stopped_append (psi : ℕ) (targets : Set (Word params.n))
    (old rest : Transcript params.n) (reason : FirstGraphStop) (snapshot : GraphSnapshot initials)
    (stopped : replay params psi initials targets old = .stopped reason snapshot) :
    replay params psi initials targets (old ++ rest) = .stopped reason snapshot := by
  rw [replay_append, stopped, fold_advance_stopped]

/-- An active replay has incorporated the entire supplied prefix and retains the
closed, disjoint boundaries containing the virtual starts and target vertices. -/
theorem graph_active_replay : StoppedGraphSpec.ActiveReplay := by
  intro params psi initials targets records
  induction records using List.reverseRecOn with
  | nil =>
      intro snapshot result
      have eq : GraphSnapshot.initial initials targets = snapshot := GraphTracker.active.inj result
      subst snapshot
      exact ⟨rfl, GraphSnapshot.initial_valid (params := params) initials targets⟩
  | append_singleton records record ih =>
      intro snapshot result
      rw [GraphTracker.replay_append] at result
      cases hBefore : GraphTracker.replay params psi initials targets records with
      | stopped reason old =>
          rw [hBefore] at result
          contradiction
      | active old =>
          rw [hBefore] at result
          have hs : GraphTracker.advance params psi (.active old) record =
              .active snapshot := result
          obtain ⟨finish, same, legal, _⟩ := GraphTracker.active_advance hs
          obtain ⟨hrecords, hvalid⟩ := ih old hBefore
          subst snapshot
          exact ⟨congrArg (· ++ [record]) hrecords,
            GraphSnapshot.valid_after_grafting hvalid legal⟩

/-- Every active snapshot satisfies the parameter bounds, starting from a valid
initial snapshot. -/
theorem graph_active_parameters : StoppedGraphSpec.ActiveParameters := by
  intro params psi initials targets initialValid records
  induction records using List.reverseRecOn with
  | nil =>
      intro snapshot result
      have eq : GraphSnapshot.initial initials targets = snapshot := GraphTracker.active.inj result
      exact eq ▸ initialValid
  | append_singleton records record _ =>
      intro snapshot result
      rw [GraphTracker.replay_append] at result
      cases hBefore : GraphTracker.replay params psi initials targets records with
      | stopped reason old =>
          rw [hBefore] at result
          contradiction
      | active old =>
          rw [hBefore] at result
          have hs : GraphTracker.advance params psi (.active old) record =
              .active snapshot := result
          obtain ⟨finish, same, legal, barrier, paths, occupancy⟩ := GraphTracker.active_advance hs
          have oldValid := (graph_active_replay params psi initials targets records old hBefore).2
          -- Exhausting the eligible grafts gives the strict residual threshold. The three
          -- other bounds come from the active classification.
          have threshold := (round_continuation old.records record params.mu initials old.sides
            finish oldValid.1 legal).2.2.2.2.2
          subst snapshot
          exact ⟨threshold, barrier, paths, occupancy⟩

private theorem empty_within_graft_threshold {n : ℕ} {initials : Finset (State n)}
    (sides : Boundary (Vertex initials)) (mu : ℕ) (hmu : 2 ≤ mu) :
    sides.WithinGraftThreshold [] mu := by
  intro root _
  constructor
  · intro row
    have onlyRoot : rowAncestors (realRecordRelation ([] : Transcript n)) sides.realResidual
        row root ⊆ {root} := by
      intro a ha
      exact Set.mem_singleton_iff.mpr (no_record_reaches_same ha.2)
    exact lt_of_le_of_lt ((Set.ncard_mono onlyRoot).trans (Set.ncard_singleton _).le) (by omega)
  · intro column
    have onlyRoot : columnDescendants (realRecordRelation ([] : Transcript n))
        sides.realResidual column root ⊆ {root} := by
      intro a ha
      exact Set.mem_singleton_iff.mpr (no_record_reaches_same ha.2).symm
    exact lt_of_le_of_lt ((Set.ncard_mono onlyRoot).trans (Set.ncard_singleton _).le) (by omega)

private theorem empty_paths_bounded {n : ℕ} (vertices : Set (State n)) (pi : ℕ)
    (hpi : 1 ≤ pi) : PathsWithinThreshold (realRecordRelation ([] : Transcript n)) vertices pi := by
  intro row column packing
  obtain ⟨paths, each, disjoint⟩ := packing
  have eachHas (i : Fin (pi + 1)) : ∃ v ∈ paths i, v.val = (column, row) := by
    have path := each i
    cases hlist : paths i with
    | nil => simpa [hlist] using path.starts
    | cons a tail =>
        cases tail with
        | nil =>
            obtain ⟨start, hs, sameStart⟩ := path.starts
            obtain ⟨finish, hf, sameFinish⟩ := path.ends
            simp only [hlist, List.head?_cons, Option.some.injEq] at sameStart
            simp only [hlist, List.getLast?_singleton, Option.some.injEq] at sameFinish
            subst start
            subst finish
            exact ⟨a, List.mem_cons_self, Prod.ext hf hs⟩
        | cons b rest =>
            have linked : (a :: b :: rest).IsChain
                (residualRelation (realRecordRelation ([] : Transcript n)) vertices) :=
              hlist ▸ path.chain
            obtain ⟨label, _⟩ := (List.isChain_cons_cons.mp linked).1
            exact Fin.elim0 label
  -- Without any records, every path in a fixed endpoint class is the same singleton.
  -- The first two paths of the alleged packing must therefore share that vertex.
  let i : Fin (pi + 1) := ⟨0, by omega⟩
  let j : Fin (pi + 1) := ⟨1, by omega⟩
  have different : i ≠ j := fun same ↦ Nat.zero_ne_one (congrArg Fin.val same)
  obtain ⟨a, ha, haState⟩ := eachHas i
  obtain ⟨b, hb, hbState⟩ := eachHas j
  have equal : a = b := Subtype.ext (haState.trans hbState.symm)
  exact disjoint different a ha (equal.symm ▸ hb)

/-- On the empty record graph, the certificate and initial occupancy suffice for all
four parameter bounds. -/
theorem graph_initial_parameters : StoppedGraphSpec.InitialParameters := by
  intro params q psi initials targets cert occupancy
  let snapshot := GraphSnapshot.initial initials targets
  have hmu : 0 < params.mu := by have hm := cert.admissible.mu_ge_two; omega
  have hd : 0 < params.d := by have hm := cert.admissible.d_ge_two; omega
  have hGamma : 0 < (params.Gamma : ℝ) := by
    exact_mod_cast params.Gamma_pos cert.admissible cert.nu_choice
  have initialPotential := cert.initial_potential
  have below (vertices : Set (State params.n)) (line : Word params.n)
      (mode : Finset (Word params.n)) :
      translatedPotential (realRecordRelation ([] : Transcript params.n)) vertices
        params.mu params.d line mode < params.Gamma := by
    have base := initial_translated_potential vertices params.mu params.d line mode hmu hd
    simp only [Params.N, Nat.cast_pow, Nat.cast_ofNat] at initialPotential
    rw [mul_div_assoc] at initialPotential
    linarith
  refine ⟨empty_within_graft_threshold snapshot.sides params.mu cert.admissible.mu_ge_two,
    ?_, empty_paths_bounded snapshot.sides.realResidual params.pi cert.admissible.pi_pos, occupancy⟩
  intro direction line mode _ _
  cases direction with
  | forward =>
      simpa [snapshot, GraphSnapshot.ledger, GraphSnapshot.initial] using
        below snapshot.sides.realResidual line mode
  | backward =>
      simpa [snapshot, GraphSnapshot.ledger, GraphSnapshot.initial, backwardTranslatedPotential,
        transposeStateEdge_realRecordRelation] using
        below (Prod.swap ⁻¹' snapshot.sides.realResidual) line mode

/-- One initial state and one target column have occupancy at most one on every line. -/
theorem graph_fixed_initial_occupancy : StoppedGraphSpec.FixedInitialOccupancy := by
  intro n initial target psi hpsi
  let sides := initialBoundary {initial} {target}
  constructor
  · intro column
    have onlyRate : sides.forwardRates column ⊆ {initial.2} := by
      rintro rate ⟨vertex, ⟨source, rfl⟩, _, hs⟩
      have same : (source : State n) = initial := Finset.mem_singleton.mp source.property
      exact Set.mem_singleton_iff.mpr (hs.symm.trans (congrArg Prod.snd same))
    exact ((Set.ncard_mono onlyRate).trans (Set.ncard_singleton _).le).trans hpsi
  · intro row
    have onlyTarget : sides.backwardCaps row ⊆ {target} := by
      rintro capacity ⟨state, same, member⟩
      have eq : (capacity, row) = state := Sum.inl.inj same
      exact Set.mem_singleton_iff.mpr ((congrArg Prod.fst eq).trans
        (Set.mem_singleton_iff.mp member))
    exact ((Set.ncard_mono onlyTarget).trans (Set.ncard_singleton _).le).trans hpsi

theorem GraphTracker.advance_residual_subset (psi : ℕ) (tracker : GraphTracker initials)
    (record : Record params.n) :
    (advance params psi tracker record).snapshot.sides.realResidual ⊆
      tracker.snapshot.sides.realResidual := by
  cases tracker with
  | stopped reason snapshot => exact subset_rfl
  | active snapshot =>
      let updated := snapshot.records ++ [record]
      let edge := recordRelation updated initials
      have old := Boundary.inheritance edge snapshot.sides
      have legal := selected_round_legal snapshot record
      cases choice : selectRound params snapshot record with
      | intersected =>
          simp only [advance, choice, GraphTracker.snapshot]
          exact fun _ member ↦ old.1.residual_subset member
      | continued finish =>
          rw [choice] at legal
          obtain ⟨separate, sequence, _⟩ := legal
          have growth := (sequence.invariants old.2.1 separate).1
          simp only [advance, choice, classified_snapshot]
          exact fun _ member ↦ old.1.residual_subset (growth.residual_subset member)

/-- Extending the record prefix can only shrink the real residual graph's vertex set. -/
theorem graph_residual_monotone : StoppedGraphSpec.ResidualMonotone := by
  intro params psi initials targets earlier later
  rw [GraphTracker.replay_append]
  generalize GraphTracker.replay params psi initials targets earlier = tracker
  induction later generalizing tracker with
  | nil => exact subset_rfl
  | cons record rest ih =>
      exact (ih (tracker := tracker.advance params psi record)).trans
        (GraphTracker.advance_residual_subset psi tracker record)

/-- Recover the active prefix, decisive record and trailing records from a stopped replay. -/
theorem graph_earliest_record : StoppedGraphSpec.EarliestRecord := by
  intro params psi initials targets records
  induction records using List.reverseRecOn with
  | nil =>
      intro reason snapshot impossible
      contradiction
  | append_singleton records record ih =>
      intro reason snapshot result
      rw [GraphTracker.replay_append] at result
      cases hBefore : GraphTracker.replay params psi initials targets records with
      | active before =>
          rw [hBefore] at result
          exact ⟨records, record, [], before, by simp, hBefore, result⟩
      -- A stopped prefix keeps its original decisive record when the transcript grows.
      | stopped first old =>
          rw [hBefore] at result
          obtain ⟨rfl, rfl⟩ := GraphTracker.stopped.inj result
          obtain ⟨earlier, decisive, later, before, split, previous, stopped⟩ :=
            ih first old hBefore
          exact ⟨earlier, decisive, later ++ [record], before,
            by rw [split, List.append_assoc], previous, stopped⟩

theorem GraphTracker.advance_nonintersection {psi : ℕ} (snapshot : GraphSnapshot initials)
    (record : Record params.n)
    (notIntersected : (advance params psi (.active snapshot) record).stopReason ≠ some .intersect) :
    ∃ finish, advance params psi (.active snapshot) record =
      classify params psi (snapshot.afterGrafting record finish) ∧
      RoundStep snapshot.records record params.mu snapshot.sides (.continued finish) := by
  have legal := selected_round_legal snapshot record
  cases chosen : selectRound params snapshot record with
  | intersected => simp [advance, chosen, stopReason] at notIntersected
  | continued finish =>
      exact ⟨finish, by simp only [advance, chosen], chosen ▸ legal⟩

theorem GraphTracker.advance_over_connected {psi : ℕ} {before after : GraphSnapshot initials}
    {record : Record params.n}
    (h : advance params psi (.active before) record = .stopped .overConnected after) :
    after.records = before.records ++ [record] ∧ ¬ after.PathsBounded params.pi := by
  have different : (advance params psi (.active before) record).stopReason ≠ some .intersect := by
    rw [h]
    simp [stopReason]
  obtain ⟨finish, classified, _⟩ := advance_nonintersection before record different
  rw [h] at classified
  have identified : after = before.afterGrafting record finish := by
    have projected := congrArg GraphTracker.snapshot classified
    change after = (classify params psi (before.afterGrafting record finish)).snapshot at projected
    simpa only [classified_snapshot] using projected
  subst after
  exact ⟨rfl, ((graph_threshold_priority params psi _).2.1.mp classified.symm).2⟩

private theorem reaches_stays_forward {V : Type*} {edge : V → V → Prop} {sides : Boundary V}
    (closed : sides.Closed edge) {start finish : V} (sourceMem : start ∈ sides.forward)
    (path : Reaches edge start finish) : finish ∈ sides.forward := by
  induction path with
  | refl => exact sourceMem
  | tail _ step ih => exact closed.1 ih step

/-- A path from a virtual start to a target column forces the replay to stop.
Forward closure would otherwise put the target on both disjoint boundaries. -/
theorem graph_success_stops : StoppedGraphSpec.SuccessStops := by
  intro params psi initials targets records witness
  cases hReplay : GraphTracker.replay params psi initials targets records with
  | stopped reason snapshot => exact ⟨reason, snapshot, rfl⟩
  | active snapshot =>
      obtain ⟨hrecords, starts, closed, separate, ends⟩ :=
        graph_active_replay params psi initials targets records snapshot hReplay
      obtain ⟨start, target, targetIn, path⟩ := witness
      rw [hrecords] at closed
      have forward := reaches_stays_forward closed (starts start) path
      exact False.elim (separate ⟨.inl target, forward, ends target targetIn⟩)

end JH.Graph
