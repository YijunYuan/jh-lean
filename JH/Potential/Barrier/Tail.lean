/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.Barrier.Modes
public import JH.Potential.Barrier.Replay
public import JH.Potential.Barrier.TailSpec
public import JH.Probability.Tape.AdaptiveMean

/-!
# The first potential-stop tail

Summing the single-account crossing estimate over the two directions, all N lines, and the
admissible patterns gives (22). The resulting exponential factor is at most 2^(−Binh/8). The
weighted version uses the drift numerator (A.3).
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters JH.Probability
open JH.PartialPermutation (uniformFinite)
open scoped BigOperators ENNReal

/-- A common bound on the per-ledger conditional means gives the full barrier tail. -/
private theorem barrier_tail_from_mean (params : Params) (q psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (mean : ℝ)
    (cert : params.CommonCertificate q)
    (occupancy : (GraphSnapshot.initial initials targets).OccupancyBounded psi)
    (hmean : (q : ℝ) * mean ≤ (params.Gamma : ℝ) / 4)
    (fixedMean : ∀ (key : LedgerKey params) (i : Fin q) (prior : Fin i.val → State params.n)
      (intrinsic : Word params.n),
      wordMean (fun shift ↦ BarrierReplay.ledgerCost params psi initials targets program
        key.1 key.2.1 key.2.2.val i prior (intrinsic, shift)) ≤ mean) :
    firstStopProbability params q psi initials targets program .overPotential ≤
      params.barrierTail := by
  let tapeLaw := uniformFinite (Fin q → State params.n)
  let split (tape : Fin q → State params.n) :
      CoordinateTape params.n q × CoordinateTape params.n q :=
    (fun i ↦ (tape i).1, fun i ↦ (tape i).2)
  let cost (key : LedgerKey params) : AdaptiveMean.Quantity (State params.n) q :=
    BarrierReplay.ledgerCost params psi initials targets program key.1 key.2.1 key.2.2.val
  let crosses (key : LedgerKey params) : Set (Fin q → State params.n) :=
    {tape | (params.Gamma : ℝ) / 2 ≤ AdaptiveMean.total (cost key) tape}
  let delta := (2 : ℝ) ^ (-(params.nu : ℝ) / 8)
  have sameLaw : tapeLaw.map split = CoordinateTape.law params.n q :=
    AdaptiveMean.uniform_pair_tape
  have hPi := params.Pi_pos cert.admissible
  have valid := graph_initial_parameters params q psi initials targets cert occupancy
  have each (key : LedgerKey params) : (tapeLaw.toOuterMeasure (crosses key)).toReal ≤ delta := by
    refine (AdaptiveMean.finite_barrier (cost key) (params.Pi : ℝ) (params.Gamma : ℝ) mean
      (by exact_mod_cast hPi) ?_ ?_ hmean).trans (ledger_tail_exponent params hPi)
    · intro i prior word
      exact BarrierReplay.ledger_cost_range params q psi initials targets program valid
        key.1 key.2.1 key.2.2.val i prior word
    · intro i prior
      -- The shift bound holds for each intrinsic coordinate, so averaging over that coordinate
      -- keeps the same bound on the mean of a fresh reply.
      rw [AdaptiveMean.expect_product]
      apply Finset.expect_le Finset.univ_nonempty
      intro intrinsic _
      rw [Fintype.expect_eq_sum_div_card, word_card, Nat.cast_pow, Nat.cast_ofNat]
      exact fixedMean key i prior intrinsic
  -- The first stop provides a direction, line, and mode whose charge sum crossed the threshold.
  have covered : split ⁻¹' firstStopEvent params q psi initials targets program .overPotential ⊆
      ⋃ key, crosses key := by
    intro tape stopped
    obtain ⟨direction, line, mode, nonempty, small, witness⟩ :=
      BarrierReplay.barrier_stop_covered params q psi initials targets program cert occupancy
        (split tape) stopped
    exact Set.mem_iUnion.mpr ⟨(direction, line, ⟨mode, nonempty, small⟩), witness⟩
  have unionFinite : tapeLaw.toOuterMeasure (⋃ key, crosses key) ≠ ⊤ := by
    simpa only [PMF.toOuterMeasure_apply] using tapeLaw.tsum_coe_indicator_ne_top _
  have hcount := ledger_count params
  rw [Nat.card_eq_fintype_card] at hcount
  unfold firstStopProbability
  rw [← sameLaw, PMF.toOuterMeasure_map_apply]
  calc
    _ ≤ (tapeLaw.toOuterMeasure (⋃ key, crosses key)).toReal :=
      ENNReal.toReal_mono unionFinite (tapeLaw.toOuterMeasure.mono covered)
    _ ≤ (Fintype.card (LedgerKey params) : ℝ) * delta :=
      AdaptiveMean.probability_iUnion_le_card_mul tapeLaw crosses delta
        (by dsimp [delta]; positivity) each
    _ ≤ ((2 * params.N * (params.N + 1) ^ params.Pi : ℕ) : ℝ) * delta :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by dsimp [delta]; positivity)
    _ = params.barrierTail := by simp [delta, Params.barrierTail]

/-- Use the equal-weight drift numerator for the Section 3.4 barrier tail. -/
theorem barrier_equal_tail : BarrierTailSpec.EqualTail := by
  intro params q psi initials targets program cert occupancy mean
  apply barrier_tail_from_mean params q psi initials targets program
    ((params.driftNumerator : ℝ) / (params.N : ℝ)) cert occupancy mean
  have hd : 0 < params.d := by have := cert.admissible.d_ge_two; omega
  have valid := graph_initial_parameters params q psi initials targets cert occupancy
  intro key i prior intrinsic
  exact BarrierReplay.ledger_cost_mean params q psi initials targets program hd valid
    key.1 key.2.1 key.2.2.val key.2.2.property.2 i prior intrinsic

/-- Use the weighted drift numerator for the Appendix A.3 barrier tail. -/
theorem barrier_weighted_tail : BarrierTailSpec.WeightedTail := by
  intro params q psi initials targets program theta htheta cert occupancy mean
  apply barrier_tail_from_mean params q psi initials targets program
    (params.weightedDriftNumerator theta / (params.N : ℝ)) cert occupancy mean
  have hd : 0 < params.d := by have := cert.admissible.d_ge_two; omega
  have valid := graph_initial_parameters params q psi initials targets cert occupancy
  intro key i prior intrinsic
  exact BarrierReplay.ledger_cost_weighted_mean params q psi initials targets
    program theta hd htheta valid
    key.1 key.2.1 key.2.2.val key.2.2.property.2 i prior intrinsic

end JH.Graph
