/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Preimage
public import JH.SecondPreimage.Coupling
public import JH.SecondPreimage.Coverage
public import JH.SecondPreimage.OriginalPhase
public import JH.SecondPreimage.PreloadedCache

/-!
# The finite second-preimage bound

For Theorem 2(2), compare the complete original-and-candidate program under a uniform
permutation and under independent replies, with budget `q + ℓ`. In the independent experiment,
a collision-free original trace has exactly `ℓ` records and leaves `q` fresh accesses.

Only later records build the stopped graph. The original trace supplies its virtual starts and
target columns. The six contributions are separation, an original capacity collision, and the
four graph stops.
-/

@[expose] public section

namespace JH

universe u

open JH.Graph JH.Parameters JH.Probability
open JH.PartialPermutation (uniformFinite)
open scoped BigOperators ENNReal

private theorem spr_graph_bounds (params : Params) (q L : ℕ) (cert : params.SPRCertificate q L)
    (states : List (State params.n)) (size : states.length ≤ L + 1)
    (program : TrialProgram params.n) :
    FirstStopBounds params q (params.sprPsi L) states.toFinset {c | c ∈ states.map Prod.fst}
      program params.tailBudget := by
  classical
  let initials := states.toFinset
  let targets : Set (Word params.n) := {c | c ∈ states.map Prod.fst}
  let snapshot := GraphSnapshot.initial initials targets
  have initialCount : initials.card ≤ L + 1 := (List.toFinset_card_le (l := states)).trans size
  have targetCount : targets.ncard ≤ L + 1 := by
    have equal : targets = ↑(states.map Prod.fst).toFinset := by
      ext c
      simp [targets]
    rw [equal, Set.ncard_coe_finset]
    exact (List.toFinset_card_le (l := states.map Prod.fst)).trans (by simpa using size)
  -- The original states supply at most `L + 1` virtual starts and at most `L + 1` full target
  -- columns.
  have initialBase : snapshot.OccupancyBounded (L + 1) := by
    obtain ⟨hf, _⟩ := BoundaryMean.occupancy_totals snapshot.sides
    have hFront := (Graph.initial_boundary_sizes initials targets).1
    constructor
    · intro column
      calc
        _ ≤ ∑ line : Word params.n, (snapshot.sides.forwardRates line).ncard :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ column)
        _ ≤ snapshot.sides.forward.ncard := hf
        _ = initials.card := hFront
        _ ≤ L + 1 := initialCount
    · intro row
      have equal : snapshot.sides.backwardCaps row = targets := by
        ext capacity
        constructor
        · rintro ⟨s, eq, hs⟩
          have hc : capacity = s.1 := congrArg (fun s : State params.n ↦ s.1) (Sum.inl.inj eq)
          exact hc.symm ▸ hs
        · intro ht
          exact ⟨(capacity, row), rfl, ht⟩
      rw [equal]
      exact targetCount
  -- Each target column contributes N states, and the length bound gives at most N virtual
  -- starts. Dividing by N gives at most L + 2.
  have population :
      IntersectionTail.population (initialBoundary initials targets) /
        (params.N : ℝ) ≤ (L : ℝ) + 2 := by
    obtain ⟨front, back⟩ := Graph.initial_boundary_sizes initials targets
    have hN : 0 < (params.N : ℝ) := Nat.cast_pos.mpr params.N_pos
    have hf : (initials.card : ℝ) ≤ (params.N : ℝ) :=
      Nat.cast_le.mpr (initialCount.trans cert.length_space)
    have hb : (targets.ncard : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast targetCount
    rw [IntersectionTail.population, front, back, Params.N, Nat.cast_mul]
    change ((initials.card : ℝ) + (targets.ncard : ℝ) * (params.N : ℝ)) / (params.N : ℝ) ≤ _
    apply (div_le_iff₀ hN).2
    calc
      _ ≤ (params.N : ℝ) + ((L : ℝ) + 1) * (params.N : ℝ) :=
        add_le_add hf (mul_le_mul_of_nonneg_right hb hN.le)
      _ = _ := by ring
  have positivePi : 1 ≤ params.Pi := params.Pi_pos cert.admissible
  have positiveNu : 1 ≤ params.nu := cert.nu_choice.nu_pos
  have product : (params.nu - 1) * params.Pi + params.Pi = params.Gamma := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel positiveNu, Params.Gamma, Nat.mul_comm]
  have base : L + 1 + params.Gamma + (params.nu - 1) * params.Pi ≤ params.sprPsi L := by
    unfold Params.sprPsi
    omega
  have occupancy : snapshot.OccupancyBounded (params.sprPsi L) :=
    ⟨fun line ↦ (initialBase.1 line).trans (by omega), fun line ↦
      (initialBase.2 line).trans (by omega)⟩
  -- The same endpoint estimate as in the fixed-target graph adds two to the population term.
  have intersection := IntersectionTail.first_stop_bound params q (params.sprPsi L) initials targets
    program 1 ((L : ℝ) + 2) cert.toCommonCertificate occupancy (by norm_num) population
  rw [show (L : ℝ) + 2 + 2 = (L : ℝ) + 4 by ring, Params.weightedCoefficient_one] at intersection
  refine
    { intersect := intersection.trans cert.intersection.tail_le
      potential := (barrier_equal_tail params q (params.sprPsi L) initials targets program
        cert.toCommonCertificate occupancy cert.cumulative_drift_le).trans
          cert.nu_choice.barrier_tail_le
      connected := (FlowTail.first_stop_bound params q (params.sprPsi L) initials targets program
        cert.toCommonCertificate occupancy).trans cert.flow_tail_le
      crowded := (OccupancyTail.first_stop_bound params q (params.sprPsi L) (L + 1) initials targets
        program cert.toCommonCertificate initialBase base).trans cert.occupancy_tail_le }

private theorem accepted_second_preimage_after_observation {α : ℕ} (params : Params) (q L : ℕ)
    (cert : params.SPRCertificate q L)
    (initial : State params.n) (padding : Padding α params.n) (original : Message α)
    (observation : OriginalObservation params.n)
    (strategy : Strategy α params.n) (hLength : (padding.encode original).length ≤ L)
    (supported : observation ∈ (OriginalPhase.sample (uniformFinite (State params.n)) initial
      (padding.encode original) [] []).support)
    (collisionFree : ¬ OriginalPhase.HasCapacityCollision observation) :
    (Separation.mass (TrialProgram.independentBounded q
      (TrialProgram.verifyDistinct original observation.terminal.1 initial padding strategy)
      observation.records) compiledSecondPreimageAccepts).toReal ≤ 4 * params.tailBudget := by
  classical
  let suffix := TrialProgram.verifyDistinct original observation.terminal.1 initial padding strategy
  -- Serve the disclosed records as cached replies while keeping them out of the new graph.
  let isolated := TrialProgram.preloadCache observation.records suffix
  let restore (outcome : Option (TrialResult params.n)) :=
    outcome.map fun result ↦ {result with records := observation.records ++ result.records}
  have sameLaw : suffix.independentBounded q observation.records =
      (isolated.independentBounded q []).map restore := by
    simpa only [List.append_nil] using
      TrialProgram.independentBounded_preloadCache q suffix observation.records []
  have acceptLaw : Separation.mass (suffix.independentBounded q observation.records)
      compiledSecondPreimageAccepts =
        Separation.mass (isolated.independentBounded q []) compiledSecondPreimageAccepts := by
    unfold Separation.mass
    rw [sameLaw, PMF.map_comp]
    have sameAccept : compiledSecondPreimageAccepts ∘ restore = compiledSecondPreimageAccepts := by
      funext outcome
      cases outcome <;> rfl
    rw [sameAccept]
  have graphCover := independent_acceptance_covered_of_paths params q (params.sprPsi L)
    observation.states.toFinset {c | c ∈ observation.states.map Prod.fst} isolated
      compiledSecondPreimageAccepts
  have cover := graphCover (by
    intro outcome present accepted
    cases outcome with
    | none => contradiction
    | some result =>
        let restored : TrialResult params.n := {result with records :=
            observation.records ++ result.records}
        have inTrial : some restored ∈ (suffix.independentBounded q
            observation.records).support := by
          rw [sameLaw]
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, present, rfl⟩
        -- The first differing block uses a later record. The common digest ensures a return to
        -- an original capacity column, with only later records on the walk to its first return.
        obtain ⟨start, target, targetMember, path, _⟩ :=
          SecondPreimageCoverage.accepted_path (uniformFinite (State params.n)) initial padding
            original observation strategy q restored supported collisionFree inTrial accepted
        -- Restoring the original prefix is needed for verification coverage. Dropping it recovers
        -- the graph's records.
        have trace : restored.records.drop observation.records.length = result.records := by
          simp [restored]
        rw [trace] at path
        exact ⟨result, rfl, start, target, targetMember, (walk_iff_reaches _ _ _).mp ⟨path⟩⟩)
  have observedSize := (OriginalPhase.sample_budget (uniformFinite (State params.n)) initial
    (padding.encode original) [] [] observation supported).2.2
  have size : observation.states.length ≤ L + 1 := by simp at observedSize; omega
  have bounds := spr_graph_bounds params q L cert observation.states size isolated
  change (Separation.mass (suffix.independentBounded q observation.records)
    compiledSecondPreimageAccepts).toReal ≤ _
  rw [acceptLaw]
  exact cover.trans
    (by linarith [bounds.intersect, bounds.potential, bounds.connected, bounds.crowded])

private theorem bounded_independent_second_preimage {α : ℕ} (params : Params) (q L : ℕ)
    (cert : params.SPRCertificate q L)
    (initial : State params.n) (padding : Padding α params.n) (original : Message α)
    (select : Message α → Word params.n → Transcript params.n → Strategy α params.n)
    (hLength : (padding.encode original).length ≤ L) :
    (Separation.mass (TrialProgram.independentBounded (q + (padding.encode original).length)
      (TrialProgram.ofSecondPreimage select initial padding original) [])
        compiledSecondPreimageAccepts).toReal ≤ 5 * params.tailBudget := by
  let blocks := padding.encode original
  let offer := uniformFinite (State params.n)
  let sampling := OriginalPhase.sample offer initial blocks [] []
  let suffix (observation : OriginalObservation params.n) :=
    TrialProgram.verifyDistinct original observation.terminal.1 initial padding
      (select original observation.terminal.1 observation.records)
  let continueWith (observation : OriginalObservation params.n) :=
    (suffix observation).independentBounded (q + blocks.length - observation.records.length)
      observation.records
  let collision : Set (OriginalObservation params.n) := {o | OriginalPhase.HasCapacityCollision o}
  let success : Set (Option (TrialResult params.n)) :=
    {outcome | compiledSecondPreimageAccepts outcome = true}
  have law : (TrialProgram.ofSecondPreimage select initial padding original).independentBounded
      (q + blocks.length) [] = sampling.bind continueWith := by
    simpa only [sampling, continueWith, suffix, blocks, offer, TrialProgram.independentBounded,
      TrialProgram.ofSecondPreimage, List.length_nil, Nat.add_zero] using
        OriginalPhase.continuation_law offer (q + blocks.length) initial blocks [] []
          (fun terminal records _ ↦ TrialProgram.verifyDistinct original terminal.1 initial padding
            (select original terminal.1 records)) (Nat.le_add_left _ _)
  have hbounded (observation : OriginalObservation params.n) (supported :
      observation ∈ sampling.support)
      (clean : observation ∉ collision) :
      (continueWith observation).toOuterMeasure success ≤ ENNReal.ofReal
        (4 * params.tailBudget) := by
    -- Distinct capacities force a fresh access at each original block, so subtracting the
    -- original log leaves exactly `q`.
    have exactBudget := OriginalPhase.sample_collision_free_length offer initial blocks observation
      supported clean
    rw [← ENNReal.ofReal_toReal (FlowTail.mass_ne_top _ success)]
    apply ENNReal.ofReal_le_ofReal
    change (PMF.toOuterMeasure ((suffix observation).independentBounded
      (q + blocks.length - observation.records.length) observation.records) success).toReal ≤ _
    rw [exactBudget, Nat.add_sub_cancel_right, ← Separation.mass_eq_toOuterMeasure]
    exact accepted_second_preimage_after_observation params q L cert initial padding original
      observation (select original observation.terminal.1 observation.records)
        hLength supported clean
  -- Charge the full mass of collisions and apply the four-stop bound to each supported clean
  -- observation.
  have charge := OriginalPhase.collision_bind_le sampling continueWith collision success
    (ENNReal.ofReal (4 * params.tailBudget)) hbounded
  have collisionTail := OriginalPhase.collision_tail initial blocks
  have cb : (sampling.toOuterMeasure collision).toReal ≤ params.tailBudget := by
    apply collisionTail.trans
    simpa only [Params.collisionTail, Params.N, Nat.cast_pow, Nat.cast_ofNat, blocks] using
      cert.collision_tail_le hLength
  have nonneg : 0 ≤ 4 * params.tailBudget := by unfold Params.tailBudget; positivity
  rw [law, Separation.mass_eq_toOuterMeasure]
  calc
    _ ≤ (sampling.toOuterMeasure collision + ENNReal.ofReal (4 * params.tailBudget)).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨FlowTail.mass_ne_top _ collision, ENNReal.ofReal_ne_top⟩) charge
    _ ≤ (sampling.toOuterMeasure collision).toReal + 4 * params.tailBudget := by
      have realAdd :
          (sampling.toOuterMeasure collision + ENNReal.ofReal (4 * params.tailBudget)).toReal ≤
            (sampling.toOuterMeasure collision).toReal + (ENNReal.ofReal
              (4 * params.tailBudget)).toReal :=
        ENNReal.toReal_add_le
      rwa [ENNReal.toReal_ofReal nonneg] at realAdd
    _ ≤ _ := by linarith

/-- **Fixed-message second-preimage bound** (Theorem 2(2)). Fix the original message before drawing
the independent adversarial tape and uniform permutation. The adversary receives the original
message, its digest, and the permutation pairs used to evaluate it.

The original has at most `L` padded blocks. Both sides use the common threshold
$C=2B_{\mathrm{pot}}+2L$ from (24). Here `q` denotes the paper's post-disclosure budget
$Q=q+L_\alpha$. The coupling includes the original evaluation, with allowance $Q+\ell(M)$.
`FixedSecondPreimageBudget` counts at most `q` fresh accesses after disclosure, including
candidate verification, for every supported tape and every permutation. The success probability
averaged over both draws is at most `6 * params.tailBudget`, strictly below $2^{-\lambda}$. -/
theorem second_preimage_finite : SecondPreimageSpec.FiniteBound.{u} := by
  intro Tape params q L α cert initial padding original tapes adversary hLength budget
  let acceptLaw := fun tape ↦ secondPreimageAcceptanceLaw
    (fun message target old ↦ adversary message target old tape) initial padding original
  have law : fixedMessageSecondPreimageSuccessProbability original initial padding tapes adversary =
      ((tapes.bind acceptLaw) true).toReal := by
    simp only [fixedMessageSecondPreimageSuccessProbability, RandomTarget.eventMass,
      RandomTarget.tapePermutationLaw, ReplyCoupling.independentPair, PMF.map_bind, PMF.map_comp,
      Function.comp_def, acceptLaw, secondPreimageAcceptanceLaw]
  -- The comparison is pointwise in the supported adversarial tape. Average after applying the
  -- six-term bound.
  have perTape (tape : Tape) (supported : tape ∈ tapes.support) :
      (acceptLaw tape true).toReal ≤ 6 * params.tailBudget := by
    let select := fun message target old ↦ adversary message target old tape
    have compared := second_preimage_transfer params q select initial padding original
        (budget tape supported)
    have bound := bounded_independent_second_preimage params q L cert initial
        padding original select hLength
    have separation := cert.separation_tail_le hLength
    dsimp only at compared
    change (secondPreimageAcceptanceLaw select initial padding original true).toReal ≤ _
    linarith
  constructor
  · rw [law]
    exact average_acceptance_real_le tapes acceptLaw
      (by unfold Params.tailBudget; positivity) perTape
  · unfold Params.tailBudget
    have hpos : 0 < ((2 : ℝ) ^ params.lambda)⁻¹ := by positivity
    rw [pow_add, mul_inv]
    norm_num
    linarith

end JH
