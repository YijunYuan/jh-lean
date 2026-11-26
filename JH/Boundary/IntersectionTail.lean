/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.IntersectionPopulation
public import JH.Boundary.IntersectionTailSpec
public import JH.Boundary.Mean
public import JH.Potential.Barrier.Replay
public import JH.Probability.Tape.AdaptiveMean

/-!
# The first intersection tail

Section 3.4 averages the one-round intersection test over the intrinsic coordinate and the
offset. Averaging over the exposed row or column replaces its occupancy by a normalized
boundary population. Summing the active-round estimates with the population bound yields the
weighted intersection term of Appendix A.3.
-/

@[expose] public section

namespace JH.Probability.IntersectionTail

open JH.Graph JH.Parameters
open JH.PartialPermutation (uniformFinite)
open scoped BigOperators ENNReal

private theorem expect_word_eq_mean {n : ℕ} (f : Word n → ℝ) :
    (𝔼 word : Word n, f word) = wordMean f := by
  rw [Fintype.expect_eq_sum_div_card, wordMean, word_card, Nat.cast_pow, Nat.cast_ofNat]

private theorem before_round_length_le {n q : ℕ} (program : TrialProgram n)
    (i : Fin q) (prior : Fin i.val → State n) :
    (BarrierReplay.beforeRound program i prior).records.length ≤ q := by
  have bound := TapeState.records_length_le_round (⟨program, []⟩ : TapeState n)
    (fun j ↦ (prior j).1) (fun j ↦ (prior j).2) i.val le_rfl
  exact (by simpa only [BarrierReplay.beforeRound, BarrierReplay.prefixState,
    List.length_nil, Nat.zero_add] using bound :
    (BarrierReplay.beforeRound program i prior).records.length ≤ i.val).trans (Nat.le_of_lt i.isLt)

private theorem population_before_nonneg (params : Params) {q psi : ℕ}
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (i : Fin q) (prior : Fin i.val → State params.n) :
    0 ≤ populationBefore params psi initials targets program i prior := by
  unfold populationBefore
  cases GraphTracker.replay params psi initials targets
    (BarrierReplay.beforeRound program i prior).records with
  | active snapshot => simp only [activePopulation, population]; positivity
  | stopped reason snapshot => exact le_rfl

private theorem round_shift {n : ℕ} (request : Query n) (intrinsic shift : Word n) :
    (request.recordOfReply (request.replyCoords.symm (intrinsic, shift))).shift = shift :=
  congrArg Prod.snd
    ((request.recordOfReply_coords (request.replyCoords.symm (intrinsic, shift))).trans
    (request.replyCoords.apply_symm_apply (intrinsic, shift)))

/-- For an active history, first expose the intrinsic coordinate and then average the shift. -/
private theorem intersection_mean_eq_nested (params : Params) {q psi : ℕ}
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (i : Fin q) (prior : Fin i.val → State params.n)
    (snapshot : GraphSnapshot initials) (request : Query params.n)
    (resume : State params.n → TrialProgram params.n)
    (reached : (BarrierReplay.beforeRound program i prior).frontier = .query request resume)
    (recorded : GraphTracker.replay params psi initials targets
      (BarrierReplay.beforeRound program i prior).records = .active snapshot) :
    (𝔼 word : State params.n,
      intersectionIndicator params psi initials targets program i prior word) =
      wordMean (fun intrinsic ↦ uniformShiftMass {shift |
        RoundStep snapshot.records
          (request.recordOfReply (request.replyCoords.symm (intrinsic, shift)))
          params.mu snapshot.sides .intersected}) := by
  classical
  rw [AdaptiveMean.expect_product]
  simp only [expect_word_eq_mean, intersectionIndicator, intersectsAt, reached, recorded]
  apply congrArg wordMean
  funext intrinsic
  let event : Set (Word params.n) := {shift |
    RoundStep snapshot.records (request.recordOfReply (request.replyCoords.symm (intrinsic, shift)))
      params.mu snapshot.sides .intersected}
  exact (wordMean_indicator event 1).trans (mul_one _)

/-- Bound the conditional intersection probability using the pre-round population. -/
theorem local_intersection_mean : IntersectionTailSpec.LocalIntersectionMean := by
  intro params q psi initials targets program cert occupancy i prior
  classical
  have initialValid := graph_initial_parameters params q psi initials targets cert occupancy
  have popNonneg := population_before_nonneg (psi := psi) params initials targets program i prior
  have nonnegative : 0 ≤ (psi : ℝ) / (params.N : ℝ) *
      (1 + (q : ℝ) * (params.Theta : ℝ) / (params.N : ℝ) +
      populationBefore params psi initials targets program i prior) := by positivity
  cases reached : (BarrierReplay.beforeRound program i prior).frontier with
  | done terminal => simpa [intersectionIndicator, intersectsAt, reached] using nonnegative
  | query request resume =>
    cases recorded : GraphTracker.replay params psi initials targets
        (BarrierReplay.beforeRound program i prior).records with
    | stopped reason snapshot =>
      simpa [intersectionIndicator, intersectsAt, reached, recorded] using nonnegative
    | active snapshot =>
      obtain ⟨sameRecords, geometry⟩ := graph_active_replay params psi initials targets
        (BarrierReplay.beforeRound program i prior).records snapshot recorded
      have valid := graph_active_parameters params psi initials targets initialValid
        (BarrierReplay.beforeRound program i prior).records snapshot recorded
      have endpointBound := GraphSnapshot.endpoint_bounds params psi snapshot valid
      have lengthBound : snapshot.records.length ≤ q :=
        sameRecords ▸ before_round_length_le program i prior
      let N : ℝ := (params.N : ℝ)
      have hN : 0 < N := Nat.cast_pos.mpr params.N_pos
      have pastBound : (snapshot.records.length : ℝ) * params.Theta / N ≤
          (q : ℝ) * params.Theta / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr lengthBound) (by positivity)) hN.le
      have compare (count : ℕ) (bounded : (count : ℝ) ≤ population snapshot.sides) :
          (psi : ℝ) / N * (1 + (snapshot.records.length : ℝ) * params.Theta / N + (count : ℝ) / N) ≤
          (psi : ℝ) / N * (1 + (q : ℝ) * params.Theta / N +
            populationBefore params psi initials targets program i prior) := by
        rw [populationBefore, recorded, activePopulation]
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hN.le)
        have populationBound := div_le_div_of_nonneg_right bounded hN.le
        linarith only [pastBound, populationBound]
      -- Use the forward output row or backward input column to average opposite-side occupancy.
      rw [intersection_mean_eq_nested params initials targets program i prior snapshot
        request resume reached recorded]
      rcases request with ⟨direction, address⟩
      cases direction with
      | forward =>
        let request : Query params.n := ⟨.forward, address⟩
        have fixed (row : Word params.n) : SharesExposedCoordinates
            (fun shift ↦ request.recordOfReply (request.replyCoords.symm (row,
              shift))) address.1 row :=
          fun shift ↦ ⟨rfl, rfl, round_shift request row shift⟩
        have average :=
          BoundaryMean.forward_intersection_mean snapshot.records params.mu snapshot.sides
          address.1 psi params.Theta (fun row shift ↦ request.recordOfReply
            (request.replyCoords.symm (row, shift)))
          geometry.1 geometry.2.1 geometry.2.2.1 fixed (fun row column ↦
            (endpointBound row column).2.2)
          (valid.2.2.2.1 address.1)
        have sideBound : (snapshot.sides.backward.ncard : ℝ) ≤ population snapshot.sides := by
          unfold population
          exact le_add_of_nonneg_left (Nat.cast_nonneg _)
        have next := compare _ sideBound
        simp only [N, Params.N, Nat.cast_pow, Nat.cast_ofNat] at next
        simpa only [Params.N, Nat.cast_pow, Nat.cast_ofNat] using average.trans next
      | backward =>
        let request : Query params.n := ⟨.backward, address⟩
        have fixed (column : Word params.n) : SharesExposedCoordinates
            (fun shift ↦ request.recordOfReply (request.replyCoords.symm (column,
              shift))) column address.2 :=
          fun shift ↦ ⟨rfl, rfl, round_shift request column shift⟩
        have average :=
          BoundaryMean.backward_intersection_mean snapshot.records params.mu snapshot.sides
          address.2 psi params.Theta
          (fun column shift ↦ request.recordOfReply (request.replyCoords.symm (column, shift)))
          geometry.1 geometry.2.1 geometry.2.2.1 fixed (fun row column ↦
            (endpointBound row column).2.2)
          (valid.2.2.2.2 address.2)
        have sideBound : (snapshot.sides.forward.ncard : ℝ) ≤ population snapshot.sides := by
          unfold population
          exact le_add_of_nonneg_right (Nat.cast_nonneg _)
        have next := compare _ sideBound
        simp only [N, Params.N, Nat.cast_pow, Nat.cast_ofNat] at next
        simpa only [Params.N, Nat.cast_pow, Nat.cast_ofNat] using average.trans next

private theorem prefixes_eq_of_length {A : Type*} {a b c : List A}
    (aPrefix : a <+: c) (bPrefix : b <+: c) (same : a.length = b.length) : a = b := by
  obtain ⟨tailA, fromA⟩ := aPrefix
  obtain ⟨tailB, fromB⟩ := bPrefix
  have takeA : c.take a.length = a := by
    rw [← fromA, List.take_append_of_le_length le_rfl, List.take_length]
  have takeB : c.take b.length = b := by
    rw [← fromB, List.take_append_of_le_length le_rfl, List.take_length]
  rw [← takeA, same, takeB]

private theorem classify_not_intersection (params : Params) {psi : ℕ}
    {initials : Finset (State params.n)} (snapshot : GraphSnapshot initials) :
    (GraphTracker.classify params psi snapshot).stopReason ≠ some .intersect := by
  unfold GraphTracker.classify
  split
  · simp [GraphTracker.stopReason]
  split
  · simp [GraphTracker.stopReason]
  split <;> simp [GraphTracker.stopReason]

private theorem intersection_round_of_stop (params : Params) {psi : ℕ}
    {initials : Finset (State params.n)} {before after : GraphSnapshot initials}
    {record : Record params.n}
    (stopped : GraphTracker.advance params psi (.active before) record =
      .stopped .intersect after) :
    RoundStep before.records record params.mu before.sides .intersected := by
  have legal := GraphTracker.selected_round_legal before record
  cases chosen : GraphTracker.selectRound params before record with
  | intersected => exact chosen ▸ legal
  | continued finish =>
    have classified : GraphTracker.classify params psi (before.afterGrafting record finish) =
        .stopped .intersect after := by simpa only [GraphTracker.advance, chosen] using stopped
    have impossible :=
      classify_not_intersection (psi := psi) params (before.afterGrafting record finish)
    rw [classified] at impossible
    exact (impossible rfl).elim

/-- Locate the decisive record of an intersection stop at its live tape round. -/
theorem intersection_stop_has_round (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (tape : Fin q → State params.n)
    (stopped : firstStopOnTapes params psi initials targets program
      ((fun j ↦ (tape j).1), (fun j ↦ (tape j).2)) = some .intersect) :
    ∃ i : Fin q, intersectsAt params psi initials targets program i
      (TapeTests.prefixAt tape i) (tape i) := by
  let start : TapeState params.n := ⟨program, []⟩
  let first : CoordinateTape params.n q := fun j ↦ (tape j).1
  let second : CoordinateTape params.n q := fun j ↦ (tape j).2
  let final := start.runPrefix first second q le_rfl
  change (GraphTracker.replay params psi initials targets final.records).stopReason =
    some .intersect at stopped
  cases replayed : GraphTracker.replay params psi initials targets final.records with
  | active snapshot => simp [replayed, GraphTracker.stopReason] at stopped
  | stopped reason after =>
    have actual : reason = .intersect := by simpa [replayed, GraphTracker.stopReason] using stopped
    subst reason
    obtain ⟨old, record, rest, before, split, prior, stoppedRound⟩ :=
      graph_earliest_record params psi initials targets final.records .intersect after replayed
    have validIndex : old.length < final.records.length := by
      rw [split, List.length_append, List.length_append, List.length_singleton]
      omega
    let label : final.records.Label := ⟨old.length, validIndex⟩
    obtain ⟨i, request, resume, _, index, live, sampled⟩ :=
      start.recorded_round first second q le_rfl label (by simp [start])
    let prefixState := start.runPrefix first second i.val (Nat.le_of_lt i.isLt)
    have prefixLength : prefixState.records.length = old.length :=
      (start.records_length_of_live first second i.val (Nat.le_of_lt i.isLt) live).trans index
    -- The replay prefix and the records before the decisive step have the same length.
    have prefixAgreement : prefixState.records = old := by
      apply prefixes_eq_of_length (c := final.records)
      · exact start.records_prefix first second i.val q (Nat.le_of_lt i.isLt) le_rfl
      · exact ⟨record ::
          rest, by simpa only [List.append_assoc, List.singleton_append] using split.symm⟩
      · exact prefixLength
    have atLabel : final.records.get label = record :=
      List.getElem_of_append
        (by simpa only [List.append_assoc, List.singleton_append] using split) rfl
    have chosenRecord : request.recordOfReply (request.replyCoords.symm (tape i)) = record :=
      sampled.symm.trans atLabel
    have cut := intersection_round_of_stop params stoppedRound
    refine ⟨i, ?_⟩
    have snapshotEq :
        BarrierReplay.beforeRound program i (TapeTests.prefixAt tape i) = prefixState :=
      BarrierReplay.beforeRound_eq_runPrefix program tape i
    have prefixLive : prefixState.frontier = .query request resume := live
    simp only [intersectsAt, snapshotEq, prefixLive, prefixAgreement, prior, chosenRecord]
    exact cut

private theorem indicator_nonnegative (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (i : Fin q) (prior : Fin i.val → State params.n)
      (word : State params.n) :
    0 ≤ intersectionIndicator params psi initials targets program i prior word := by
  unfold intersectionIndicator
  split <;> positivity

/-- The sum of the active-round indicators dominates the first-intersection indicator. -/
private theorem probability_le_expected_total (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n)) (program :
      TrialProgram params.n) :
    firstStopProbability params q psi initials targets program .intersect ≤
      𝔼 tape : Fin q → State params.n,
        AdaptiveMean.total (intersectionIndicator params psi initials targets program) tape := by
  let tapeLaw := uniformFinite (Fin q → State params.n)
  let split (tape : Fin q → State params.n) :
      CoordinateTape params.n q × CoordinateTape params.n q :=
    (fun i ↦ (tape i).1, fun i ↦ (tape i).2)
  let event := split ⁻¹' firstStopEvent params q psi initials targets program .intersect
  have sameLaw : tapeLaw.map split = CoordinateTape.law params.n q := AdaptiveMean.uniform_pair_tape
  unfold firstStopProbability
  rw [← sameLaw, PMF.toOuterMeasure_map_apply]
  change (tapeLaw.toOuterMeasure event).toReal ≤ _
  rw [AdaptiveMean.uniform_mass_eq_expect]
  apply Finset.expect_le_expect
  intro tape _
  have nonnegative (i : Fin q) :
      0 ≤ intersectionIndicator params psi initials targets program i
        (TapeTests.prefixAt tape i) (tape i) :=
    indicator_nonnegative params psi initials targets program i (TapeTests.prefixAt tape i) (tape i)
  by_cases stopped : tape ∈ event
  · obtain ⟨i, hit⟩ := intersection_stop_has_round params psi initials targets program tape stopped
    rw [Set.indicator_of_mem stopped]
    have value : intersectionIndicator params psi initials targets program i (TapeTests.prefixAt
        tape i) (tape i) = 1 := by
      unfold intersectionIndicator
      rw [ite_eq_left hit]
    rw [← value]
    exact Finset.single_le_sum (fun j _ ↦ nonnegative j) (Finset.mem_univ i)
  · rw [Set.indicator_of_notMem stopped]
    exact Finset.sum_nonneg (fun i _ ↦ nonnegative i)

/-- Average the local bound over old prefixes and insert the expected population estimate. -/
private theorem expected_round_intersection_le (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
      (program : TrialProgram params.n)
    (theta initialBound : ℝ) (cert : params.CommonCertificate q)
    (occupancy : (GraphSnapshot.initial initials targets).OccupancyBounded psi)
    (positiveTheta : 0 < theta)
    (initialPop : population (initialBoundary initials targets) / (params.N : ℝ) ≤ initialBound)
    (i : Fin q) :
    (𝔼 tape : Fin q → State params.n,
      intersectionIndicator params psi initials targets program i
        (TapeTests.prefixAt tape i) (tape i)) ≤
      (psi : ℝ) / (params.N : ℝ) * (1 + (q : ℝ) * params.Theta / (params.N : ℝ) +
        populationBound params q psi theta initialBound) := by
  let rate := (psi : ℝ) / (params.N : ℝ)
  let base := 1 + (q : ℝ) * params.Theta / (params.N : ℝ)
  let pop (prior : Fin i.val → State params.n) :=
    populationBefore params psi initials targets program i prior
  -- Average over the preceding history, with the activity test already in the integrand.
  rw [AdaptiveMean.expect_adapted_round]
  calc
    _ ≤ 𝔼 prior : Fin i.val → State params.n, rate * (base + pop prior) :=
      Finset.expect_le_expect fun prior _ ↦
        local_intersection_mean params q psi initials targets program
        cert occupancy i prior
    _ = rate * (base + (𝔼 prior : Fin i.val → State params.n, pop prior)) := by
      rw [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const]
    _ ≤ _ := by
      have bound := active_population_mean params q psi initials targets
          program theta initialBound cert
        occupancy positiveTheta initialPop i
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl bound) (by dsimp [rate]; positivity)

/-- Use `q / N <= 1 / U` and the endpoint budget to simplify the summed hazard. -/
private theorem sum_le_certificate_tail (params : Params) (q psi : ℕ) (theta initialBound : ℝ)
    (cert : params.CommonCertificate q) (positiveTheta : 0 < theta)
      (initialNonneg : 0 ≤ initialBound) :
    (q : ℝ) * ((psi : ℝ) / (params.N : ℝ) * (1 + (q : ℝ) * params.Theta / (params.N : ℝ) +
      populationBound params q psi theta initialBound)) ≤
      params.intersectionTail psi (initialBound + 2) (params.weightedCoefficient theta) := by
  let N : ℝ := (params.N : ℝ)
  let U : ℝ := (params.U : ℝ)
  let base := 1 + (q : ℝ) * params.Theta / N
  let coefficient := params.weightedCoefficient theta + (psi : ℝ) + 2 * (params.Pi : ℝ)
  let envelope := initialBound + 2 + 2 * N / (params.mu : ℝ) ^ params.d + 4 / U * coefficient
  have hN : 0 < N := Nat.cast_pos.mpr params.N_pos
  have hU : 0 < U := Nat.cast_pos.mpr params.U_pos
  have qScaled : (q : ℝ) / N ≤ 1 / U := by
    calc
      _ ≤ (N / U) / N := div_le_div_of_nonneg_right cert.budget hN.le
      _ = _ := by field_simp
  -- The two budget inequalities bound the time-dependent endpoint factor by two.
  have thetaScaled : (q : ℝ) * params.Theta / N ≤ 1 := by
    calc
      _ = ((q : ℝ) / N) * params.Theta := by ring
      _ ≤ (1 / U) * params.Theta := mul_le_mul_of_nonneg_right qScaled (Nat.cast_nonneg _)
      _ ≤ (1 / U) * U :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr cert.endpoint_budget) (by positivity)
      _ = _ := by field_simp
  have baseBound : base ≤ 2 := by dsimp [base]; linarith only [thetaScaled]
  have baseNonneg : 0 ≤ base := by dsimp [base]; positivity
  have coeffNonneg : 0 ≤ coefficient := by
    dsimp [coefficient, Params.weightedCoefficient, Analysis.weightedCost]
    positivity
  have factorBound : (2 * (q : ℝ) / N) * base ≤ 4 / U := by
    calc
      _ = ((q : ℝ) / N) * (2 * base) := by ring
      _ ≤ (1 / U) * (2 * base) := mul_le_mul_of_nonneg_right qScaled (by positivity)
      _ ≤ (1 / U) * (2 * 2) := by gcongr
      _ = _ := by ring
  have populationEnvelope : populationBound params q psi theta initialBound ≤
      initialBound + 2 * N / (params.mu : ℝ) ^ params.d + 4 / U * coefficient := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right factorBound coeffNonneg)
  have hazardEnvelope : base + populationBound params q psi theta initialBound ≤ envelope := by
    dsimp [envelope]
    linarith only [baseBound, populationEnvelope]
  have envelopeNonneg : 0 ≤ envelope := by dsimp [envelope]; positivity
  have rateBound : (q : ℝ) * ((psi : ℝ) / N) ≤ (psi : ℝ) / U := by
    calc
      _ = (psi : ℝ) * ((q : ℝ) / N) := by ring
      _ ≤ (psi : ℝ) * (1 / U) := mul_le_mul_of_nonneg_left qScaled (Nat.cast_nonneg _)
      _ = _ := by ring
  change (q : ℝ) * ((psi : ℝ) / N * (base + populationBound params q psi theta initialBound)) ≤
    (psi : ℝ) / U * envelope
  calc
    _ = ((q : ℝ) * ((psi : ℝ) / N)) *
      (base + populationBound params q psi theta initialBound) := by ring
    _ ≤ ((q : ℝ) * ((psi : ℝ) / N)) * envelope :=
      mul_le_mul_of_nonneg_left hazardEnvelope (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right rateBound envelopeNonneg

/-- The first intersection probability is bounded by the certificate's intersection tail. -/
theorem first_stop_bound : IntersectionTailSpec.Tail := by
  intro params q psi initials targets program theta initialBound cert occupancy
    positiveTheta initialPop
  let roundBound := (psi : ℝ) / (params.N : ℝ) * (1 + (q : ℝ) * params.Theta / (params.N : ℝ) +
    populationBound params q psi theta initialBound)
  have nonnegativeInitial : 0 ≤ initialBound := by
    refine le_trans ?_ initialPop
    unfold population
    positivity
  refine (probability_le_expected_total params q psi initials targets program).trans ?_
  unfold AdaptiveMean.total
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ _ : Fin q, roundBound := Finset.sum_le_sum fun i _ ↦
      expected_round_intersection_le params q psi initials targets program theta initialBound
        cert occupancy positiveTheta initialPop i
    _ = (q : ℝ) * roundBound := by simp [nsmul_eq_mul]
    _ ≤ _ := sum_le_certificate_tail params q psi theta initialBound cert
      positiveTheta nonnegativeInitial

end JH.Probability.IntersectionTail
