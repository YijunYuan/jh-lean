/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.IntersectionTail
public import JH.Boundary.OccupancyTail
public import JH.Connectivity.FlowTail
public import JH.ModelProofs
public import JH.Potential.Barrier.Tail
public import JH.Probability.FirstStop

/-!
# Fixed-target preimage bounds

The equal-weight and weighted certificates share the same four first-stop bounds on the
independent-reply graph. `JH.preimage_finite` combines those bounds with the coupling to a
uniform permutation. `JH.preimage_explicit_sqrt` instantiates its parameters using the uniform
construction in Appendix A.2.
-/

@[expose] public section

namespace JH

open JH.Parameters JH.Graph JH.Probability

/-- The initial forward boundary contains one virtual vertex per start. Each target capacity
contributes a full backward column of `2 ^ n` real states. -/
theorem Graph.initial_boundary_sizes {n : ℕ} (initials : Finset (State n))
    (targetColumns : Set (Word n)) :
    (initialBoundary initials targetColumns).forward.ncard = initials.card ∧
      (initialBoundary initials targetColumns).backward.ncard = targetColumns.ncard * 2 ^ n := by
  constructor
  · change (Set.range (Sum.inr : {s : State n // s ∈ initials} → Vertex initials)).ncard = _
    rw [Set.ncard_range_of_injective Sum.inr_injective]
    simp [Nat.card_eq_fintype_card]
  · let toVertex (p : targetColumns × Word n) : Vertex initials := .inl (p.1.val, p.2)
    have injective : Function.Injective toVertex := by
      rintro ⟨capacity, rate⟩ ⟨otherCap, otherRate⟩ same
      have sameState : (capacity.val, rate) = (otherCap.val, otherRate) := Sum.inl.inj same
      exact Prod.ext (Subtype.ext (congrArg (fun s : State n ↦ s.1) sameState))
        (congrArg (fun s : State n ↦ s.2) sameState)
    have boundary : (initialBoundary initials targetColumns).backward = Set.range toVertex := by
      ext vertex
      constructor
      · rintro ⟨state, rfl, target⟩
        exact ⟨(⟨state.1, target⟩, state.2), rfl⟩
      · rintro ⟨⟨capacity, rate⟩, rfl⟩
        exact ⟨(capacity.val, rate), rfl, capacity.property⟩
    rw [boundary, Set.ncard_range_of_injective injective, Nat.card_prod, Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card, word_card]

private theorem fixed_initial_population (params : Params) (initial : State params.n)
    (target : Word params.n) :
    IntersectionTail.population (initialBoundary {initial} {target}) / (params.N : ℝ) ≤ 2 := by
  obtain ⟨front, back⟩ := Graph.initial_boundary_sizes ({initial} : Finset (State params.n))
    ({target} : Set (Word params.n))
  rw [IntersectionTail.population, front, back, Finset.card_singleton, Set.ncard_singleton, one_mul]
  have atLeastOne : (1 : ℝ) ≤ (params.N : ℝ) := by exact_mod_cast params.N_pos
  apply (div_le_iff₀ (Nat.cast_pos.mpr params.N_pos : 0 < (params.N : ℝ))).2
  rw [Nat.cast_one]
  change (1 : ℝ) + (params.N : ℝ) ≤ 2 * (params.N : ℝ)
  linarith

theorem Parameters.Params.weightedCoefficient_one (params : Params) :
    params.weightedCoefficient 1 = params.graftCoefficient := by
  simp only [Params.weightedCoefficient, Params.graftCoefficient, Analysis.weightedCost, inv_one]
  norm_num
  ring

private theorem fixed_graph_bounds (params : Params) (q : ℕ) (theta : ℝ)
    (cert : params.CommonCertificate q) (htheta : 0 < theta) (initial : State params.n)
    (target : Word params.n) (program : TrialProgram params.n)
    (barrier : firstStopProbability params q params.Psi {initial} {target} program .overPotential ≤
      params.barrierTail)
    (occupancyTail : params.occupancyTail q params.Psi ≤ params.tailBudget)
    (intersection : params.IntersectionCondition params.Psi 4 (params.weightedCoefficient theta)) :
    FirstStopBounds params q params.Psi {initial} {target} program params.tailBudget := by
  have pPi : 1 ≤ params.Pi := params.Pi_pos cert.admissible
  have pNu : 1 ≤ params.nu := cert.nu_choice.nu_pos
  have product : (params.nu - 1) * params.Pi + params.Pi = params.Gamma := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel pNu, Params.Gamma, Nat.mul_comm]
  have base : 1 + params.Gamma + (params.nu - 1) * params.Pi ≤ params.Psi := by
    unfold Params.Psi
    omega
  have initOccupancy := graph_fixed_initial_occupancy initial target params.Psi (by omega)
  -- One virtual start and one full target column give normalized initial population at most two.
  -- The certificate bounds `q * Theta / N` by one.
  -- The constant and endpoint terms therefore add at most two.
  have intersected := IntersectionTail.first_stop_bound params q params.Psi {initial} {target}
    program theta 2 cert initOccupancy htheta (fixed_initial_population params initial target)
  rw [show (2 : ℝ) + 2 = 4 by norm_num] at intersected
  -- Apply the certificate to each first-stop probability before taking their union.
  refine
    { intersect := intersected.trans intersection.tail_le
      potential := barrier.trans cert.nu_choice.barrier_tail_le
      connected := (FlowTail.first_stop_bound params q params.Psi {initial} {target} program
        cert initOccupancy).trans cert.flow_tail_le
      crowded := (OccupancyTail.first_stop_bound params q params.Psi 1 {initial} {target}
        program cert (graph_fixed_initial_occupancy initial target 1 le_rfl)
          base).trans occupancyTail }

/-- **Fixed-target preimage bound** (Theorem 2(1)). Fix the target before independently drawing a
strategy and a uniform permutation. The success probability is at most `5 * params.tailBudget`,
which is strictly below $2^{-\lambda}$.

`Params.PreCertificate` supplies the finite inequalities. The argument `q` denotes the
paper's total budget $Q=q+L_\alpha$. `FixedTargetBudget`
requires the strategy and candidate verification together to use at most `q` fresh accesses for
each supported strategy and each permutation. See `JH.fixedTarget_bound_of_first_stops` for the
four graph terms and the separation term. Inequality (A.5) bounds the latter by one
tail budget. -/
theorem preimage_finite : PreimageSpec.FiniteBound := by
  apply preimage_finite_from_first_stops
  intro params q cert target initial program
  have hPsi : 1 ≤ params.Psi := by
    have positive := params.Gamma_pos cert.admissible cert.nu_choice
    unfold Params.Psi
    omega
  have occupancy := graph_fixed_initial_occupancy initial target params.Psi hPsi
  refine fixed_graph_bounds params q 1 cert.toCommonCertificate (by norm_num) initial target program
    (barrier_equal_tail params q params.Psi {initial} {target} program cert.toCommonCertificate
      occupancy cert.cumulative_drift_le) cert.occupancy_tail_le ?_
  -- The equal-weight grafting coefficient is the weighted coefficient at `theta = 1`.
  simpa only [Params.weightedCoefficient_one] using cert.intersection

/-- The weighted finite bound of Appendix A.3. A `Params.WeightedPreCertificate` provides a
positive weight for the graph estimates. The fixed-target experiment and its fresh-access
budget are as in `JH.preimage_finite`, with the same five-term success bound. -/
theorem preimage_weighted_finite : PreimageSpec.WeightedFiniteBound := by
  apply weighted_preimage_finite_from_first_stops
  intro params q theta cert target initial program
  have hPsi : 1 ≤ params.Psi := by
    have positive := params.Gamma_pos cert.admissible cert.nu_choice
    unfold Params.Psi
    omega
  have occupancy := graph_fixed_initial_occupancy initial target params.Psi hPsi
  exact fixed_graph_bounds params q theta cert.toCommonCertificate cert.theta_pos initial target
    program (barrier_weighted_tail params q params.Psi {initial} {target} program theta
      cert.theta_pos cert.toCommonCertificate occupancy cert.cumulative_drift_le)
    cert.occupancy_tail_le cert.intersection

/-- Specializing (39) at χ = ⌈√(n/2)⌉ gives the rounded loss `JH.PreimageSpec.uniformLoss`. For
n ≥ 4 the total fresh-access budget then gives advantage strictly below 2^(−⌊√(2n)⌋). -/
theorem preimage_explicit_sqrt : PreimageSpec.ExplicitSqrtBound :=
  explicit_sqrt_from_finite preimage_finite

end JH
