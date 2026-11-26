/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.StoppedGraph
public import JH.Oracle.Coupling.SuccessTransfer
public import JH.Oracle.Independent.CoordinateTape
public import JH.Parameters.Uniform
public import JH.Probability.FirstStopSpec

/-!
# Combining the first-stop probabilities

Section 3.2 covers accepted independent-reply trials using the four possible graph stops. The
strategy mixture preserves that bound, and transfer to the permutation experiment adds the
separation term. The resulting union estimate serves both the equal-weight certificate and the
weighted certificate of Appendix A.3.
-/

@[expose] public section

namespace JH

open scoped ENNReal
open Parameters
open Graph

private theorem event_mass_ne_top {A : Type*} (law : PMF A) (event : Set A) :
    law.toOuterMeasure event ≠ ⊤ := by
  simpa only [PMF.toOuterMeasure_apply] using law.tsum_coe_indicator_ne_top event

private theorem real_event_union_le {A : Type*} (law : PMF A) (first second : Set A) :
    (law.toOuterMeasure (first ∪ second)).toReal ≤
      (law.toOuterMeasure first).toReal + (law.toOuterMeasure second).toReal := by
  exact (ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨event_mass_ne_top law first, event_mass_ne_top law second⟩)
    (MeasureTheory.measure_union_le _ _)).trans ENNReal.toReal_add_le

/-- If every supported accepting trial has a recorded walk from a virtual start to a target
column, its acceptance probability is at most the sum of the four first-stop probabilities. -/
theorem Graph.independent_acceptance_covered_of_paths (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (accept : Option (TrialResult params.n) → Bool)
    (witnessed : ∀ outcome ∈ (program.independentBounded q []).support, accept outcome = true →
      ∃ result, outcome = some result ∧
        ∃ start : {s : State params.n // s ∈ initials}, ∃ terminal : State params.n,
          terminal.1 ∈ targets ∧
          Reaches (recordRelation result.records initials) (.inr start) (.inl terminal)) :
    let stop := firstStopProbability params q psi initials targets program
    (Separation.mass (program.independentBounded q []) accept).toReal ≤
      stop .intersect + stop .overPotential + stop .overConnected + stop .overCrowded := by
  dsimp only
  let initialState : TapeState params.n := ⟨program, []⟩
  let law := CoordinateTape.law params.n q
  let result := fun tapes : CoordinateTape params.n q × CoordinateTape params.n q ↦
    initialState.run tapes.1 tapes.2
  let success := fun tapes ↦ accept (result tapes)
  let event := fun e ↦ firstStopEvent params q psi initials targets program e
  -- Replay on coordinate tapes has the same result law as the independent trial.
  have trialLaw : law.map result = program.independentBounded q [] := by
    rw [show law.map result = TrialProgram.independentCoordinatesBounded q program [] from
      TapeState.run_law q initialState]
    exact TrialProgram.independentCoordinatesBounded_eq q program []
  have hSuccess : Separation.mass (program.independentBounded q []) accept =
      law.toOuterMeasure {tapes | success tapes = true} := by
    rw [← trialLaw, Separation.mass_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply]
    rfl
  have inclusion : {tapes | success tapes = true} ∩ law.support ⊆
      (event .intersect ∪ event .overPotential ∪ event .overConnected ∪ event .overCrowded) := by
    rintro tapes ⟨accepted, supported⟩
    have inTrial : result tapes ∈ (program.independentBounded q []).support := by
      rw [← trialLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tapes, supported, rfl⟩
    obtain ⟨outcome, hResult, found⟩ := witnessed (result tapes) inTrial accepted
    let final := initialState.runPrefix tapes.1 tapes.2 q le_rfl
    have sameRecords : final.records = outcome.records := by
      change final.result = some outcome at hResult
      unfold TapeState.result at hResult
      split at hResult
      · exact congrArg TrialResult.records (Option.some.inj hResult)
      · contradiction
    -- The path witness uses the final transcript and rules out an active final graph.
    -- Replay preserves the first stop even if the trial logs more records afterward.
    obtain ⟨reason, snapshot, stopped⟩ :=
      graph_success_stops params psi initials targets outcome.records found
    have picked : tapes ∈ event reason := by
      change (GraphTracker.replay params psi initials targets
        final.records).stopReason = some reason
      rw [sameRecords, stopped]
      rfl
    cases reason with
    | intersect => exact Or.inl (Or.inl (Or.inl picked))
    | overPotential => exact Or.inl (Or.inl (Or.inr picked))
    | overConnected => exact Or.inl (Or.inr picked)
    | overCrowded => exact Or.inr picked
  rw [hSuccess]
  refine (ENNReal.toReal_mono (event_mass_ne_top law _)
    (law.toOuterMeasure_mono inclusion)).trans ?_
  exact (real_event_union_le law _ _).trans
    (add_le_add (real_event_union_le law _ _) le_rfl |>.trans
      (add_le_add (add_le_add (real_event_union_le law _ _) le_rfl) le_rfl))

/-- Use the preimage success trace to supply the recorded path for acceptance coverage. -/
theorem Graph.independent_acceptance_covered : FirstStopSpec.AcceptanceCovered := by
  intro α params q target initial padding strategy
  refine independent_acceptance_covered_of_paths params q params.Psi {initial} {target}
    (TrialProgram.ofStrategy strategy initial padding) (TrialResult.accepts target) ?_
  intro outcome supported accepted
  obtain ⟨result, rfl, success⟩ := (TrialResult.accepts_iff target outcome).mp accepted
  obtain ⟨rate, path⟩ := TrialProgram.independent_success_trace q target initial padding strategy
    result supported success
  exact ⟨result, rfl, ⟨initial, Finset.mem_singleton_self initial⟩, (target, rate), rfl,
    (walk_iff_reaches _ _ _).mp path⟩

/-- A common acceptance bound for strategies in the support survives averaging. -/
theorem average_acceptance_real_le {A : Type*} (law : PMF A) (accept : A → PMF Bool)
    {bound : ℝ} (nonneg : 0 ≤ bound)
    (localBound : ∀ choice ∈ law.support, (accept choice true).toReal ≤ bound) :
    ((law.bind accept) true).toReal ≤ bound := by
  have bounded (choice : A) (supported : choice ∈ law.support) :
      accept choice true ≤ ENNReal.ofReal bound := by
    rw [← ENNReal.ofReal_toReal ((accept choice).apply_ne_top true)]
    exact ENNReal.ofReal_le_ofReal (localBound choice supported)
  have total : (law.bind accept) true ≤ ENNReal.ofReal bound := by
    rw [PMF.bind_apply]
    calc
      _ ≤ ∑' choice, law choice * ENNReal.ofReal bound :=
        tsum_le_tsum fun choice ↦ by
          by_cases supported : choice ∈ law.support
          · exact mul_le_mul_right (bounded choice supported) (law choice)
          · have empty := (law.apply_eq_zero_iff choice).mpr supported
            simp only [empty, zero_mul, le_rfl]
      _ = _ := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top total).trans_eq (ENNReal.toReal_ofReal nonneg)

/-- Combine the four graph stops and the coupling under five copies of the tail budget. -/
theorem fixedTarget_bound_of_first_stops {α : ℕ} (params : Params) (q : ℕ)
    (target : Word params.n) (initial : State params.n) (padding : Padding α params.n)
    (strategies : PMF (Strategy α params.n))
      (budget : FixedTargetBudget q initial padding strategies)
    (separation : params.separationTail q ≤ params.tailBudget)
    (stops : ∀ program, FirstStopBounds params q params.Psi {initial} {target} program
      params.tailBudget) :
    fixedTargetSuccessProbability target initial padding strategies ≤ 5 * params.tailBudget ∧
      5 * params.tailBudget < ((2 : ℝ) ^ params.lambda)⁻¹ := by
  have tailPositive : 0 < params.tailBudget := by unfold Params.tailBudget; positivity
  have hi : independentFixedTargetSuccessProbability q target initial padding strategies ≤
      4 * params.tailBudget := by
    apply average_acceptance_real_le strategies _ (by linarith)
    intro strategy _
    have cover := independent_acceptance_covered params q target initial padding strategy
    have bounds := stops (TrialProgram.ofStrategy strategy initial padding)
    dsimp only at cover
    exact cover.trans (by linarith [bounds.intersect, bounds.potential,
      bounds.connected, bounds.crowded])
  -- The permutation comparison pays the fifth term once, after averaging over strategies.
  have joined := fixedTarget_success_le_independent_params params q target
      initial padding strategies
    budget
  constructor
  · linarith
  · unfold Params.tailBudget
    have hpos : 0 < ((2 : ℝ) ^ params.lambda)⁻¹ := by positivity
    rw [pow_add, mul_inv]
    norm_num
    linarith

/-- Derive the finite fixed-target theorem from the equal-weight first-stop bounds. -/
theorem preimage_finite_from_first_stops
    (stops : ∀ (params : Params) (q : ℕ), params.PreCertificate q →
      ∀ (target : Word params.n) (initial : State params.n) (program : TrialProgram params.n),
        FirstStopBounds params q params.Psi {initial} {target} program params.tailBudget) :
    PreimageSpec.FiniteBound := by
  intro params q α cert target initial padding strategies budget
  exact fixedTarget_bound_of_first_stops params q target initial padding strategies budget
    cert.separation_tail_le (stops params q cert target initial)

/-- Use the same union calculation with the weighted first-stop bounds. -/
theorem weighted_preimage_finite_from_first_stops
    (stops : ∀ (params : Params) (q : ℕ) (theta : ℝ), params.WeightedPreCertificate q theta →
      ∀ (target : Word params.n) (initial : State params.n) (program : TrialProgram params.n),
        FirstStopBounds params q params.Psi {initial} {target} program params.tailBudget) :
    PreimageSpec.WeightedFiniteBound := by
  intro params q α theta cert target initial padding strategies budget
  exact fixedTarget_bound_of_first_stops params q target initial padding strategies budget
    cert.separation_tail_le (stops params q theta cert target initial)

/-- Instantiate the finite bound with the uniform certificate from Appendix A.2. -/
theorem explicit_sqrt_from_finite (finite : PreimageSpec.FiniteBound) :
    PreimageSpec.ExplicitSqrtBound := by
  intro n q α hn hq target initial padding strategies budget
  obtain ⟨upper, strict⟩ := finite (explicitParams n) q α (explicit_certificate n q hn hq)
    target initial padding strategies budget
  exact upper.trans_lt strict

end JH
