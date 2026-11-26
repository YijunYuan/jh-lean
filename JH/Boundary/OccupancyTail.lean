/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.BackwardEvents
public import JH.Boundary.ForwardEvents
public import JH.Boundary.OccupancyTailSpec
public import JH.Connectivity.FlowTailBounds
public import JH.Potential.Barrier.Replay
public import JH.Probability.Tape.AdaptiveMean
public import JH.Probability.Tape.Tests

/-!
# The first occupancy-stop tail

Section 3.4 charges occupancy on a single line to its initial points, accrued grafts, and
rounds with nonempty inheritance. If occupancy causes the first stop, the barrier still bounds
the graft count, so at least `nu` inheritance tests pass. Counting the choices of line,
direction, and tested rounds gives the tail.
-/

@[expose] public section

namespace JH.Probability.OccupancyTail

open JH.Graph JH.Parameters
open PartialPermutation (uniformFinite)
open scoped ENNReal BigOperators

/-- Count the choices of direction, line, and $B_{\mathrm{inh}}$ distinct rounds. -/
theorem encoding_card : OccupancyTailSpec.EncodingCard := by
  intro n q nu
  simp [Code, Selected, Fintype.card_finset_len, word_card n, Nat.mul_assoc]

private theorem uniform_shift_le {n : ℕ} {event : Set (Word n)} {bound : ℝ}
    (estimate : uniformShiftMass event ≤ bound) :
    (uniformFinite (Word n)).toOuterMeasure event ≤ ENNReal.ofReal bound := by
  rw [PartialPermutation.uniformFinite_eq_uniformOfFintype,
    ← ENNReal.ofReal_toReal (FlowTail.mass_ne_top (uniformPMF (Word n)) event)]
  exact ENNReal.ofReal_le_ofReal estimate

/-- Bound nonempty inheritance by fixing the old history and averaging the fresh offset. -/
theorem conditional_test : OccupancyTailSpec.ConditionalTest := by
  intro params q psi initials targets program initialValid direction line intrinsic i prior
  let before := BarrierReplay.beforeRound program i (fun j ↦
      (TapeTests.prefixAt intrinsic i j, prior j))
  change (uniformFinite (Word params.n)).toOuterMeasure
    {offset | inheritsAt params psi initials targets before direction line (intrinsic i, offset)} ≤
      ENNReal.ofReal (stepBound params psi)
  cases reached : before.frontier with
  | done terminal => simp [inheritsAt, reached]
  | query request resume =>
      cases recorded : GraphTracker.replay params psi initials targets before.records with
      | stopped reason snapshot => simp [inheritsAt, reached, recorded]
      | active snapshot =>
          have valid := graph_active_parameters params psi initials targets initialValid
            before.records snapshot recorded
          have boundary :=
            (graph_active_replay params psi initials targets before.records snapshot recorded).2
          have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
          -- The exposed coordinates determine which endpoint supports bound the candidate offsets.
          obtain ⟨inputColumn, outputRow, shares⟩ :=
            request.recordOfReply_sharesExposedCoordinates (intrinsic i)
          let recordFor (offset : Word params.n) :=
            request.recordOfReply (request.replyCoords.symm (intrinsic i, offset))
          have forward := BoundaryEvents.forward_inheritance_probability snapshot.records params.mu
            snapshot.sides inputColumn outputRow line psi params.Pi recordFor
              boundary.1 boundary.2.1
            shares (valid.2.2.2.1 inputColumn)
              (bounds outputRow inputColumn).2.1 (bounds outputRow line).1
          have backward :=
            BackwardBoundaryEvents.backward_inheritance_probability snapshot.records params.mu
            snapshot.sides inputColumn outputRow line psi params.Pi recordFor
              boundary.1 boundary.2.1
            shares (valid.2.2.2.2 outputRow) (bounds outputRow inputColumn).1
              (bounds line inputColumn).2.1
          cases direction with
          | forward =>
              simpa only [inheritsAt, reached, recorded, inheritedOnLine] using uniform_shift_le
                (bound := stepBound params psi)
                (by simpa only [stepBound, Params.N, Nat.cast_pow, Nat.cast_ofNat] using forward)
          | backward =>
              simpa only [inheritsAt, reached, recorded, inheritedOnLine] using uniform_shift_le
                (bound := stepBound params psi)
                (by simpa only [stepBound, Params.N, Nat.cast_pow, Nat.cast_ofNat] using backward)

/-- For each intrinsic tape, apply the adapted product bound to the selected offsets. -/
private theorem code_event_probability (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
    (initialValid : (GraphSnapshot.initial initials targets).ValidParameters params psi)
    (code : Code params.n q params.nu) :
    ((CoordinateTape.law params.n q).toOuterMeasure
      (codeEvent params psi initials targets program code)).toReal ≤
      (stepBound params psi) ^ params.nu := by
  let rate := ENNReal.ofReal (stepBound params psi)
  have bound : (CoordinateTape.law params.n q).toOuterMeasure
      (codeEvent params psi initials targets program code) ≤ rate ^ params.nu := by
    rw [CoordinateTape.law, ReplyCoupling.independentPair, PMF.toOuterMeasure_bind_apply]
    simp_rw [PMF.toOuterMeasure_map_apply]
    calc
      _ ≤ ∑' intrinsic : CoordinateTape params.n q,
          uniformFinite (CoordinateTape params.n q) intrinsic * (rate ^ params.nu) := by
        apply tsum_le_tsum
        intro intrinsic
        apply mul_le_mul_right
        have localBound := TapeTests.adapted_product_bound
          (test params psi initials targets program
            (directionOf code.1) code.2.1 intrinsic) code.2.2.val rate
          (fun i _ prior ↦ conditional_test params q psi initials targets program initialValid
            (directionOf code.1) code.2.1 intrinsic i prior)
        exact localBound.trans_eq (congrArg (rate ^ ·) code.2.2.property)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have nonnegative : 0 ≤ stepBound params psi := by unfold stepBound; positivity
  simpa only [rate, ENNReal.toReal_pow, ENNReal.toReal_ofReal nonnegative] using
    ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) bound

/-- Count rates on a forward column or capacities on a backward row. -/
private noncomputable def lineOccupancy {n : ℕ} {initials : Finset (State n)}
    (snapshot : GraphSnapshot initials) (direction : Direction) (line : Word n) : ℕ :=
  match direction with
  | .forward => (snapshot.sides.forwardRates line).ncard
  | .backward => (snapshot.sides.backwardCaps line).ncard

/-- The number of vertices grafted into the chosen side and line at a snapshot. -/
private def grafts {n : ℕ} {initials : Finset (State n)}
    (snapshot : GraphSnapshot initials) (direction : Direction) (line : Word n) : ℕ :=
  match direction with
  | .forward => snapshot.forwardGrafts line
  | .backward => snapshot.backwardGrafts line

private theorem ncard_le_of_three_sets {A : Type*} [Finite A] {seen old inherited grafted : Set A}
    (covered : seen ⊆ old ∪ inherited ∪ grafted) :
    seen.ncard ≤ old.ncard + inherited.ncard + grafted.ncard :=
  (Set.ncard_mono covered).trans
    ((Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _))

/-- Every occupied point is old, inherited this round, or paid by the new graft count. -/
private theorem after_grafting_occupancy (params : Params) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) (record : Record params.n)
      (finish : Boundary (Vertex initials))
    (starts : snapshot.sides.ContainsVirtualStarts) (direction : Direction) (line : Word params.n) :
    let after := snapshot.afterGrafting record finish
    lineOccupancy after direction line + grafts snapshot direction line ≤
      lineOccupancy snapshot direction line + grafts after direction line +
        (inheritedOnLine snapshot.records record snapshot.sides direction line).ncard := by
  let inherited := snapshot.sides.inherit (recordRelation (snapshot.records ++ [record]) initials)
  cases direction with
  | forward =>
      let fresh := graftedOnLine inherited.forward finish.forward (fun rate ↦ (line, rate))
      have covered : finish.forwardRates line ⊆ snapshot.sides.forwardRates line ∪
          BoundaryEvents.forwardInheritedRates snapshot.records record snapshot.sides line ∪
          (fresh : Set (Word params.n)) := by
        rintro rate ⟨vertex, onFinish, sameColumn, sameRate⟩
        cases vertex with
        | inr initial =>
            exact Or.inl (Or.inl ⟨.inr initial, starts initial, sameColumn, sameRate⟩)
        | inl state =>
            have located : state = (line, rate) := Prod.ext sameColumn sameRate
            subst state
            by_cases old : Sum.inl (line, rate) ∈ snapshot.sides.forward
            · exact Or.inl (Or.inl ⟨.inl (line, rate), old, rfl, rfl⟩)
            by_cases inheritedHere : Sum.inl (line, rate) ∈ inherited.forward
            · exact Or.inl (Or.inr ⟨inheritedHere, old⟩)
            · exact Or.inr (mem_graftedOnLine.mpr ⟨onFinish, inheritedHere⟩)
      have size := ncard_le_of_three_sets covered
      rw [Set.ncard_coe_finset] at size
      change (finish.forwardRates line).ncard + snapshot.forwardGrafts line ≤
        (snapshot.sides.forwardRates line).ncard + (snapshot.forwardGrafts line + fresh.card) +
          (BoundaryEvents.forwardInheritedRates snapshot.records record snapshot.sides line).ncard
      omega
  | backward =>
      let fresh := graftedOnLine inherited.backward finish.backward
          (fun capacity ↦ (capacity, line))
      have covered : finish.backwardCaps line ⊆ snapshot.sides.backwardCaps line ∪
          BackwardBoundaryEvents.backwardInheritedCaps snapshot.records record snapshot.sides line ∪
          (fresh : Set (Word params.n)) := by
        intro capacity onFinish
        by_cases old : Sum.inl (capacity, line) ∈ snapshot.sides.backward
        · exact Or.inl (Or.inl old)
        by_cases inheritedHere : Sum.inl (capacity, line) ∈ inherited.backward
        · exact Or.inl (Or.inr ⟨inheritedHere, old⟩)
        · exact Or.inr (mem_graftedOnLine.mpr ⟨onFinish, inheritedHere⟩)
      have size := ncard_le_of_three_sets covered
      rw [Set.ncard_coe_finset] at size
      change (finish.backwardCaps line).ncard + snapshot.backwardGrafts line ≤
        (snapshot.sides.backwardCaps line).ncard + (snapshot.backwardGrafts line + fresh.card) +
          (BackwardBoundaryEvents.backwardInheritedCaps snapshot.records
            record snapshot.sides line).ncard
      omega

/-- Pair each intrinsic coordinate with the offset drawn at the same round. -/
private def pairTapes {n q : ℕ} (tapes : CoordinateTape n q × CoordinateTape n q) :
    Fin q → State n :=
  fun index ↦ (tapes.1 index, tapes.2 index)

/-- The inheritance test for the specified line on the given pair of tapes. -/
private noncomputable def occurs (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
      (tapes : CoordinateTape params.n q × CoordinateTape params.n q)
    (direction : Direction) (line : Word params.n) (i : Fin q) : Prop :=
  test params psi initials targets program direction line tapes.1 i
    (TapeTests.prefixAt tapes.2 i) (tapes.2 i)

private theorem occurs_eq (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
      (tapes : CoordinateTape params.n q × CoordinateTape params.n q)
    (direction : Direction) (line : Word params.n) (i : Fin q) :
    occurs params psi initials targets program tapes direction line i ↔
      inheritsAt params psi initials targets
        (BarrierReplay.prefixState program (pairTapes tapes) i.val (Nat.le_of_lt i.isLt))
        direction line (pairTapes tapes i) := by
  change inheritsAt params psi initials targets
      (BarrierReplay.beforeRound program i (TapeTests.prefixAt (pairTapes tapes) i)) direction line
        (pairTapes tapes i) ↔ _
  rw [BarrierReplay.beforeRound_eq_runPrefix]

/-- One when the event holds and zero otherwise. -/
private noncomputable def indicator (event : Prop) : ℕ := by
  classical
  exact if event then 1 else 0

private theorem initial_valid_of_base (params : Params) (q psi b : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (certificate : params.CommonCertificate q)
    (base : (GraphSnapshot.initial initials targets).OccupancyBounded b)
    (arithmetic : b + params.Gamma + (params.nu - 1) * params.Pi ≤ psi) :
    (GraphSnapshot.initial initials targets).ValidParameters params psi := by
  have base_le : b ≤ psi := by omega
  exact graph_initial_parameters params q psi initials targets certificate
    ⟨fun column ↦ (base.1 column).trans base_le, fun row ↦ (base.2 row).trans base_le⟩

/-- A nonempty inheritance contributes at most $B_{\mathrm{ver}}$ points on the chosen line. -/
private theorem prefix_occupancy_step (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
      (tapes : CoordinateTape params.n q × CoordinateTape params.n q)
    (initialValid : (GraphSnapshot.initial initials targets).ValidParameters params psi)
    (direction : Direction) (line : Word params.n) (i : Fin q)
    (notIntersected :
      (BarrierReplay.trackerAfterPrefix params psi initials targets program (pairTapes tapes)
      (i.val + 1) (Nat.succ_le_of_lt i.isLt)).stopReason ≠ some .intersect) :
    let old := BarrierReplay.trackerAfterPrefix params psi initials targets
        program (pairTapes tapes)
      i.val (Nat.le_of_lt i.isLt)
    let new := BarrierReplay.trackerAfterPrefix params psi initials targets
        program (pairTapes tapes)
      (i.val + 1) (Nat.succ_le_of_lt i.isLt)
    old.stopReason ≠ some .intersect ∧
      lineOccupancy new.snapshot direction line + grafts old.snapshot direction line ≤
        lineOccupancy old.snapshot direction line + grafts new.snapshot direction line +
          params.Pi * indicator
            (occurs params psi initials targets program tapes direction line i) := by
  let before := BarrierReplay.prefixState program (pairTapes tapes) i.val (Nat.le_of_lt i.isLt)
  let after := BarrierReplay.prefixState program (pairTapes tapes) (i.val +
      1) (Nat.succ_le_of_lt i.isLt)
  let old := GraphTracker.replay params psi initials targets before.records
  let new := GraphTracker.replay params psi initials targets after.records
  change new.stopReason ≠ some .intersect at notIntersected
  change old.stopReason ≠ some .intersect ∧
    lineOccupancy new.snapshot direction line + grafts old.snapshot direction line ≤
      lineOccupancy old.snapshot direction line + grafts new.snapshot direction line +
        params.Pi * indicator (occurs params psi initials targets program tapes direction line i)
  cases reached : before.frontier with
  | done terminal =>
      have same : after = before := by
        change before.step (tapes.1 i) (tapes.2 i) = before
        rw [TapeState.step, reached]
      have sameGraph : new = old := congrArg
        (fun state : TapeState params.n ↦
          GraphTracker.replay params psi initials targets state.records) same
      rw [sameGraph]
      exact ⟨sameGraph ▸ notIntersected, Nat.le_add_right _ _⟩
  | query request resume =>
      let record := request.recordOfReply (request.replyCoords.symm (pairTapes tapes i))
      have appends : after.records = before.records ++ [record] :=
        (TapeState.live_round (⟨program, []⟩ : TapeState params.n)
          tapes.1 tapes.2 i request resume reached).2.1
      have moved : new = old.advance params psi record := by
        change GraphTracker.replay params psi initials targets after.records = _
        rw [appends]
        exact GraphTracker.replay_append params psi initials targets before.records [record]
      have allowed := moved ▸ notIntersected
      rw [moved]
      cases tracked : old with
      | stopped reason snapshot =>
          exact ⟨by simpa [tracked, GraphTracker.advance] using allowed, Nat.le_add_right _ _⟩
      | active snapshot =>
          have active : GraphTracker.replay params psi initials targets before.records =
              .active snapshot := tracked
          have noIntersection :
              (GraphTracker.advance params psi (.active snapshot) record).stopReason ≠
              some .intersect := by simpa [tracked] using allowed
          obtain ⟨finish, classified, legal⟩ :=
            GraphTracker.advance_nonintersection snapshot record noIntersection
          have boundary :=
            (graph_active_replay params psi initials targets before.records snapshot active).2
          have valid := graph_active_parameters params psi initials targets initialValid
              before.records snapshot active
          have bounds := GraphSnapshot.endpoint_bounds params psi snapshot valid
          have inherited_le :
              (inheritedOnLine snapshot.records record snapshot.sides direction line).ncard ≤
              params.Pi := by
            cases direction with
            | forward =>
              exact (BoundaryEvents.forward_inherited_count snapshot.records record params.mu
                snapshot.sides finish line boundary.1 boundary.2.1 legal).trans
                (bounds record.output.2 line).2.1
            | backward =>
              exact (BackwardBoundaryEvents.backward_inherited_count snapshot.records record
                params.mu snapshot.sides finish line boundary.1 boundary.2.1 legal).trans
                (bounds line record.input.1).1
          have event : occurs params psi initials targets program tapes direction line i ↔
              (inheritedOnLine snapshot.records record snapshot.sides direction line).Nonempty := by
            rw [occurs_eq]
            change inheritsAt params psi initials targets before direction line
              (pairTapes tapes i) ↔ _
            simp only [inheritsAt, reached, active]
            constructor
            · rintro ⟨_, _, nonempty⟩
              exact nonempty
            · exact fun nonempty ↦ ⟨finish, legal, nonempty⟩
          -- Use the indicator only when the inherited set is nonempty.
          have inherited_paid :
              (inheritedOnLine snapshot.records record snapshot.sides direction line).ncard ≤
              params.Pi * indicator
                (occurs params psi initials targets program tapes direction line i) := by
            by_cases nonempty :
              (inheritedOnLine snapshot.records record snapshot.sides direction line).Nonempty
            · simpa only [indicator, ite_eq_left (event.mpr nonempty),
                Nat.mul_one] using inherited_le
            · rw [Set.not_nonempty_iff_eq_empty.mp nonempty, Set.ncard_empty]
              exact Nat.zero_le _
          rw [classified, GraphTracker.classified_snapshot]
          exact ⟨by simp [GraphTracker.stopReason],
            (after_grafting_occupancy params snapshot record finish boundary.1 direction line).trans
              (Nat.add_le_add_left inherited_paid _)⟩

/-- Sum the round inequalities so that the intermediate graft counts cancel. -/
private theorem occupancy_at_prefix (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n)
      (tapes : CoordinateTape params.n q × CoordinateTape params.n q)
    (initialValid : (GraphSnapshot.initial initials targets).ValidParameters params psi)
    (direction : Direction) (line : Word params.n) (k : ℕ) (within : k ≤ q)
    (notIntersected :
      (BarrierReplay.trackerAfterPrefix params psi initials targets program (pairTapes tapes)
      k within).stopReason ≠ some .intersect) :
    let snapshot :=
      (BarrierReplay.trackerAfterPrefix params psi initials targets program (pairTapes tapes)
      k within).snapshot
    lineOccupancy snapshot direction line ≤
      lineOccupancy (GraphSnapshot.initial initials targets) direction line +
        params.Pi * (∑ j : Fin k,
          indicator (occurs params psi initials targets program tapes direction line
          (j.castLE within))) + grafts snapshot direction line := by
  induction k with
  | zero =>
      simp [BarrierReplay.trackerAfterPrefix, BarrierReplay.prefixState, TapeState.runPrefix,
        GraphTracker.replay, GraphTracker.snapshot]
  | succ k ih =>
      let i : Fin q := ⟨k, Nat.lt_of_succ_le within⟩
      have growth := prefix_occupancy_step params psi initials targets program tapes initialValid
        direction line i notIntersected
      have earlier := ih (Nat.le_of_succ_le within) growth.1
      dsimp only
      rw [Fin.sum_univ_castSucc, Nat.mul_add]
      have step := growth.2
      let old := (BarrierReplay.trackerAfterPrefix params psi initials targets program
        (pairTapes tapes) k (Nat.le_of_succ_le within)).snapshot
      let new := (BarrierReplay.trackerAfterPrefix params psi initials targets program
        (pairTapes tapes) (k + 1) within).snapshot
      let base := lineOccupancy (GraphSnapshot.initial initials targets) direction line
      let previous := params.Pi * ∑ j : Fin k,
        indicator (occurs params psi initials targets program tapes direction line
          (j.castLE (Nat.le_of_succ_le within)))
      let current := params.Pi *
          indicator (occurs params psi initials targets program tapes direction line i)
      change lineOccupancy new direction line ≤ base + (previous + current) +
        grafts new direction line
      change lineOccupancy old direction line ≤ base + previous +
        grafts old direction line at earlier
      change lineOccupancy new direction line + grafts old direction line ≤
        lineOccupancy old direction line + grafts new direction line + current at step
      omega

private theorem replay_over_crowded (params : Params) (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (records : Transcript params.n) (snapshot : GraphSnapshot initials)
    (stopped : GraphTracker.replay params psi initials targets records =
      .stopped .overCrowded snapshot) :
    snapshot.BelowBarrier params ∧ ¬ snapshot.OccupancyBounded psi := by
  obtain ⟨_, record, _, before, _, _, decisive⟩ :=
    graph_earliest_record params psi initials targets records .overCrowded snapshot stopped
  have notIntersected : (GraphTracker.advance params psi (.active before) record).stopReason ≠
      some .intersect := by simp [decisive, GraphTracker.stopReason]
  obtain ⟨finish, classified, _⟩ :=
    GraphTracker.advance_nonintersection before record notIntersected
  rw [decisive] at classified
  have same : snapshot = before.afterGrafting record finish := by
    have eq := congrArg GraphTracker.snapshot classified
    rw [GraphTracker.classified_snapshot] at eq
    exact eq
  subst snapshot
  -- Threshold priority gives both the barrier bound and occupancy overflow in this snapshot.
  obtain ⟨below, _, crowded⟩ := (graph_threshold_priority params psi _).2.2.1.mp classified.symm
  exact ⟨below, crowded⟩

private theorem translatedPotential_nonneg {n : ℕ} (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (line : Word n) (mode : Finset (Word n)) :
    0 ≤ translatedPotential edge vertices mu d line mode := by
  unfold translatedPotential
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦
    (forward_weight_range _ _ _ _ _).1) (Nat.cast_nonneg _)

private theorem grafts_lt_gamma (params : Params) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) (below : snapshot.BelowBarrier params)
    (piPositive : 0 < params.Pi) (direction : Direction) (line : Word params.n) :
    grafts snapshot direction line < params.Gamma := by
  have modeSize : ({0} : Finset (Word params.n)).card ≤ params.Pi := by
    rw [Finset.card_singleton]
    exact piPositive
  have ledger := below direction line {0} (by simp) modeSize
  -- The singleton ledger contains the graft count plus a nonnegative potential.
  have graftLe : (grafts snapshot direction line : ℝ) ≤
      snapshot.ledger params.mu params.d direction line {0} := by
    cases direction with
    | forward =>
        simpa [grafts, GraphSnapshot.ledger] using le_add_of_nonneg_left
          (a := (snapshot.forwardGrafts line : ℝ))
          (translatedPotential_nonneg (realRecordRelation snapshot.records)
            snapshot.sides.realResidual params.mu params.d line {0})
    | backward =>
        simpa [grafts, GraphSnapshot.ledger, backwardTranslatedPotential]
          using le_add_of_nonneg_left
          (a := (snapshot.backwardGrafts line : ℝ))
          (translatedPotential_nonneg (transposeStateEdge (realRecordRelation snapshot.records))
            (Prod.swap ⁻¹' snapshot.sides.realResidual) params.mu params.d line {0})
  exact Nat.cast_lt.mp (graftLe.trans_lt ledger)

/-- An occupancy stop yields an encoding with $B_{\mathrm{inh}}$ successful inheritance tests. -/
theorem witness_covered : OccupancyTailSpec.WitnessCovered := by
  intro params q psi b initials targets program certificate base arithmetic tapes event
  classical
  let tape := pairTapes tapes
  let final := BarrierReplay.trackerAfterPrefix params psi initials targets program tape q le_rfl
  have firstStop : final.stopReason = some .overCrowded := event
  cases replayed : final with
  | active snapshot => simp [replayed, GraphTracker.stopReason] at firstStop
  | stopped reason snapshot =>
      have reason_eq : reason =
          .overCrowded := by simpa [replayed, GraphTracker.stopReason] using firstStop
      subst reason
      obtain ⟨below, crowded⟩ := replay_over_crowded params psi initials targets
        (BarrierReplay.prefixState program tape q le_rfl).records snapshot replayed
      have overLine : ∃ direction line, psi < lineOccupancy snapshot direction line := by
        by_contra absent
        have under (direction : Direction) (line : Word params.n) :
            lineOccupancy snapshot direction line ≤ psi :=
          le_of_not_gt fun overflow ↦ absent ⟨direction, line, overflow⟩
        exact crowded ⟨under .forward, under .backward⟩
      obtain ⟨direction, line, tooMany⟩ := overLine
      have graftBound := grafts_lt_gamma params snapshot below
          (params.Pi_pos certificate.admissible)
        direction line
      have initialBound :
          lineOccupancy (GraphSnapshot.initial initials targets) direction line ≤ b := by
        cases direction with
        | forward => exact base.1 line
        | backward => exact base.2 line
      have noIntersection : final.stopReason ≠ some .intersect := by simp [replayed,
          GraphTracker.stopReason]
      have initialValid :=
        initial_valid_of_base params q psi b initials targets certificate base arithmetic
      have decomposition :=
        occupancy_at_prefix params psi initials targets program tapes initialValid
        direction line q le_rfl noIntersection
      let witness := occurs params psi initials targets program tapes direction line
      let passed := Finset.univ.filter witness
      change lineOccupancy final.snapshot direction line ≤
        lineOccupancy (GraphSnapshot.initial initials targets) direction line +
          params.Pi * (∑ i : Fin q, indicator (witness i)) +
            grafts final.snapshot direction line at decomposition
      rw [replayed] at decomposition
      simp only [GraphTracker.snapshot] at decomposition
      have count : (∑ i : Fin q, indicator (witness i)) = passed.card := by
        unfold indicator passed
        rw [← Finset.sum_filter]
        simp
      rw [count] at decomposition
      -- Fewer than `nu` passing rounds would keep occupancy within the threshold.
      have enough : params.nu ≤ passed.card := by
        by_contra insufficient
        have few : passed.card ≤ params.nu - 1 := by omega
        have fewPaid : params.Pi * passed.card ≤ (params.nu - 1) * params.Pi := by
          rw [Nat.mul_comm (params.nu - 1)]
          exact Nat.mul_le_mul_left _ few
        omega
      obtain ⟨chosen, contained, exactSize⟩ := Finset.exists_subset_card_eq enough
      let backwards := match direction with
        | .forward => false
        | .backward => true
      have direction_eq : directionOf backwards = direction := by cases direction <;> rfl
      apply Set.mem_iUnion.mpr
      refine ⟨(backwards, line, ⟨chosen, exactSize⟩), ?_⟩
      intro i selected
      have accepted := (Finset.mem_filter.mp (contained selected)).2
      change test params psi initials targets program (directionOf backwards) line tapes.1
        i (TapeTests.prefixAt tapes.2 i) (tapes.2 i)
      rw [direction_eq]
      exact accepted

/-- Apply the encoded union bound to a first occupancy stop. -/
theorem first_stop_bound : OccupancyTailSpec.FirstStopBound := by
  intro params q psi b initials targets program certificate base arithmetic
  let law := CoordinateTape.law params.n q
  let event := fun code : Code params.n q params.nu ↦
      codeEvent params psi initials targets program code
  have initialValid :=
    initial_valid_of_base params q psi b initials targets certificate base arithmetic
  have nonnegative : 0 ≤ stepBound params psi := by unfold stepBound; positivity
  have unionBound :=
    AdaptiveMean.probability_iUnion_le_card_mul law event ((stepBound params psi) ^ params.nu)
    (pow_nonneg nonnegative _)
      (code_event_probability params q psi initials targets program initialValid)
  have covers : firstStopEvent params q psi initials targets program
      .overCrowded ⊆ ⋃ code, event code :=
    witness_covered params q psi b initials targets program certificate base arithmetic
  change (law.toOuterMeasure (firstStopEvent params q psi initials targets
    program .overCrowded)).toReal ≤ _
  refine (ENNReal.toReal_mono (FlowTail.mass_ne_top law _)
    (law.toOuterMeasure.mono covers)).trans ?_
  simpa only [encoding_card params.n q params.nu, Params.occupancyTail, stepBound, Params.N,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using unionBound

end JH.Probability.OccupancyTail
