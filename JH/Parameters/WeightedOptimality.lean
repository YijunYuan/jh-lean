/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Parameters.Certificate
public import JH.Parameters.WeightedOptimality.Lower
public import JH.Parameters.WeightedOptimality.Upper
public import JH.Parameters.WeightedOptimalitySpec
public import JH.Preimage
public import Mathlib.Tactic.Linarith

/-!
# Optimal certificate loss and the resulting query bound

Feasibility here fixes `lambda = 1` and uses `q = 0` to test the parameter inequalities. For
all sufficiently large `n`, the least feasible loss exists. The upper and lower estimates on it
give the weighted part of (A.12).

To bound queries in the actual experiment, transfer a feasible certificate to the proposed
query budget and apply `JH.preimage_weighted_finite` at success probability one half.
-/

@[expose] public section

namespace JH.Parameters.WeightedOptimality

open Filter

/-- When there is a feasible certificate, the least weighted loss is feasible. -/
theorem least_feasible_of_exists {n : ℕ} (feasible : ∃ s, WeightedFeasible n s) :
    WeightedFeasible n (leastWeightedLoss n) := by
  classical
  rw [leastWeightedLoss, dite_eq_left feasible]
  exact Nat.find_spec feasible

theorem least_le_of_feasible {n s : ℕ} (feasible : WeightedFeasible n s) :
    leastWeightedLoss n ≤ s := by
  classical
  have existsFeasible : ∃ t, WeightedFeasible n t := ⟨s, feasible⟩
  rw [leastWeightedLoss, dite_eq_left existsFeasible]
  exact Nat.find_min' existsFeasible feasible

theorem eventual_feasibility_of_upper (upper : WeightedUpperSpec.OptimalUpper) :
    WeightedOptimalitySpec.EventualFeasibility := by
  obtain ⟨_, _, construct⟩ := upper
  filter_upwards [construct] with n candidate
  obtain ⟨params, theta, length, advantage, certificate, _⟩ := candidate
  exact least_feasible_of_exists ⟨params.s, params, theta, length, advantage, rfl, certificate⟩

/-- Combine a uniform lower bound and an eventual construction to obtain an error bounded by a
constant around the main loss term. -/
theorem loss_asymptotic_of_bounds (lower : WeightedLowerSpec.UniformLower)
    (upper : WeightedUpperSpec.OptimalUpper) : WeightedOptimalitySpec.LossAsymptotic := by
  obtain ⟨Klo, _, necessary⟩ := lower
  obtain ⟨Khi, _, construct⟩ := upper
  unfold WeightedOptimalitySpec.LossAsymptotic
  apply Asymptotics.IsBigO.of_bound (max Klo Khi)
  filter_upwards [construct] with n candidate
  obtain ⟨params, theta, length, advantage, certificate, upperLe⟩ := candidate
  have trialFeasible : WeightedFeasible n params.s :=
    ⟨params, theta, length, advantage, rfl, certificate⟩
  have leastUpper : (leastWeightedLoss n : ℝ) ≤ weightedLossMain n + Khi :=
    (Nat.cast_le.mpr (least_le_of_feasible trialFeasible)).trans upperLe
  -- Apply the necessary bound to the certificate attaining the least loss. The constructed
  -- certificate already supplies an upper bound.
  obtain ⟨minimum, weight, minLength, minAdvantage, minLoss, minCertificate⟩ :=
    least_feasible_of_exists ⟨params.s, trialFeasible⟩
  have leastLower : weightedLossMain n - Klo ≤ (leastWeightedLoss n : ℝ) := by
    simpa only [weightedLossMain, minLength, minLoss] using
      necessary minimum 0 weight minAdvantage minCertificate
  rw [Real.norm_eq_abs, norm_one, mul_one]
  apply abs_le.mpr
  constructor
  · linarith only [leastLower, le_max_left Klo Khi]
  · linarith only [leastUpper, le_max_right Klo Khi]

/-- The weighted finite theorem forces a strategy of success probability at least one half to
exceed the feasible certificate's budget. -/
theorem fixed_target_query_bound_of_finite (finite : PreimageSpec.WeightedFiniteBound)
    (transfer : WeightedUpperSpec.BudgetTransfer) :
      WeightedOptimalitySpec.FixedTargetQueryBound := by
  intro n s q α target initial padding strategies feasible actualBudget successful
  obtain ⟨params, theta, length, advantage, loss, certificate⟩ := feasible
  subst n
  subst s
  -- If the actual budget met the certificate's query condition, the finite theorem would give
  -- success strictly below one half.
  have exceeds : ¬ params.QueryBudget q := by
    intro within
    obtain ⟨successLe, tailLt⟩ :=
      finite params q α theta (transfer params theta q certificate within)
      target initial padding strategies actualBudget
    have tailHalf : 5 * params.tailBudget < (1 / 2 : ℝ) := by
      simpa only [advantage, pow_one, one_div] using tailLt
    exact (not_lt_of_ge successful) (successLe.trans_lt tailHalf)
  have positiveN : 0 < (params.N : ℝ) := Nat.cast_pos.mpr params.N_pos
  have positiveU : 0 < (params.U : ℝ) := Nat.cast_pos.mpr params.U_pos
  have larger : (params.N : ℝ) / (params.U : ℝ) < (q : ℝ) := lt_of_not_ge exceeds
  have ratioPos := div_pos positiveN positiveU
  have logRatio : Real.logb 2 ((params.N : ℝ) / (params.U : ℝ)) =
      (params.n : ℝ) - (params.s : ℝ) := by
    rw [Real.logb_div positiveN.ne' positiveU.ne']
    simp [Params.N, Params.U, Real.logb_pow]
  have lifted := Real.logb_lt_logb (by norm_num : 1 < (2 : ℝ)) ratioPos larger
  rw [logRatio] at lifted
  exact ⟨Nat.cast_pos.mp (ratioPos.trans larger), lifted⟩

/-- A feasible loss gives a strict logarithmic lower bound for every real trial attaining
success probability at least one half. -/
theorem fixed_target_query_bound : WeightedOptimalitySpec.FixedTargetQueryBound :=
  fixed_target_query_bound_of_finite JH.preimage_weighted_finite WeightedUpper.budget_transfer

/-- Smaller feasible losses increase the range of budgets ruled out by the finite theorem.
An eventual upper bound on the least feasible loss therefore yields a query lower bound. -/
theorem query_lower_bound_of_upper (upper : WeightedUpperSpec.OptimalUpper)
    (finite : WeightedOptimalitySpec.FixedTargetQueryBound) :
      WeightedOptimalitySpec.QueryLowerBound := by
  obtain ⟨K, Knonnegative, construct⟩ := upper
  refine ⟨K, Knonnegative, ?_⟩
  filter_upwards [construct] with n candidate
  obtain ⟨params, theta, length, advantage, certificate, upperLe⟩ := candidate
  have trialFeasible : WeightedFeasible n params.s :=
    ⟨params, theta, length, advantage, rfl, certificate⟩
  have leastUpper : (leastWeightedLoss n : ℝ) ≤ weightedLossMain n + K :=
    (Nat.cast_le.mpr (least_le_of_feasible trialFeasible)).trans upperLe
  have leastFeasible := least_feasible_of_exists ⟨params.s, trialFeasible⟩
  intro q α target initial padding strategies actualBudget successful
  obtain ⟨positive, query⟩ := finite n (leastWeightedLoss n) q α target initial padding strategies
    leastFeasible actualBudget successful
  exact ⟨positive, by linarith only [leastUpper, query]⟩

/-- For every sufficiently large width the least feasible weighted loss is attained. -/
theorem eventual_feasibility : WeightedOptimalitySpec.EventualFeasibility :=
  eventual_feasibility_of_upper WeightedUpper.optimal_upper

/-- The weighted part of (A.12). With `lambda = 1`, the least feasible weighted loss is
$C_* \sqrt{n} + \log_2 n + O(1)$ as $n$ tends to infinity. Feasibility is
`JH.Parameters.WeightedFeasible`, and the constant is `JH.Analysis.WeightedConstant.Cstar`. -/
theorem loss_asymptotic : WeightedOptimalitySpec.LossAsymptotic :=
  loss_asymptotic_of_bounds WeightedLower.uniform_lower WeightedUpper.optimal_upper

/-- For all sufficiently large word lengths, fixed-target success of at least one half
requires a positive total fresh-access budget `q`. Its base-two logarithm is at least
`n - weightedLossMain n - K` for some constant `K` independent of the strategy and target. -/
theorem query_lower_bound : WeightedOptimalitySpec.QueryLowerBound :=
  query_lower_bound_of_upper WeightedUpper.optimal_upper fixed_target_query_bound

end JH.Parameters.WeightedOptimality
