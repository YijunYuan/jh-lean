/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.WeightedConstantSpec
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The constant in the weighted certificate loss

Equation (A.14) minimizes `2 * y / sqrt (R y)` over `R y > 0`, where `g y = log₂ (1 + 2 ^
(-y))` and `R y = y - g y / 2`. The derivative of the squared objective gives a unique
minimizer in `(0, 1)`.

The certificate lower bound uses `minmax_lower_bound`. The upper construction uses `flow_slack`
to pay the path-witness constraint after rounding.
-/

@[expose] public section

namespace JH.Analysis.WeightedConstant

/-- The magnitude of the derivative of `g`. -/
private noncomputable def reciprocal (y : ℝ) : ℝ :=
  (1 + (2 : ℝ) ^ y)⁻¹

private theorem reciprocal_pos (y : ℝ) : 0 < reciprocal y := by
  unfold reciprocal
  positivity

private theorem reciprocal_lt_one (y : ℝ) : reciprocal y < 1 := by
  have power : 0 < (2 : ℝ) ^ y := Real.rpow_pos_of_pos (by norm_num) _
  exact inv_lt_one_of_one_lt₀ (lt_add_of_pos_right _ power)

private theorem reciprocal_antitone : Antitone reciprocal := by
  intro a b le
  unfold reciprocal
  apply inv_anti₀ (by positivity)
  exact add_le_add_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) le) 1

theorem g_pos (y : ℝ) : 0 < g y := by
  apply Real.logb_pos (by norm_num : 1 < (2 : ℝ))
  exact lt_add_of_pos_right _ (Real.rpow_pos_of_pos (by norm_num) _)

theorem g_derivative (y : ℝ) : HasDerivAt g (-(1 + (2 : ℝ) ^ y)⁻¹) y := by
  have power := (hasDerivAt_id y).neg.const_rpow (a := (2 : ℝ)) (by norm_num)
  have argument : 0 < (1 : ℝ) + (2 : ℝ) ^ (-y) := by positivity
  have raw := ((power.const_add (1 : ℝ)).log argument.ne').div_const (Real.log 2)
  refine raw.congr_deriv ?_
  change Real.log 2 * (-1 : ℝ) * (2 : ℝ) ^ (-y) / (1 + (2 : ℝ) ^ (-y)) / Real.log 2 =
    -(1 + (2 : ℝ) ^ y)⁻¹
  have logNe : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have powerPos : 0 < (2 : ℝ) ^ y := by positivity
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have plusPos : 0 < (1 : ℝ) + (2 : ℝ) ^ y := by positivity
  have inversePlusPos : 0 < (1 : ℝ) + ((2 : ℝ) ^ y)⁻¹ := by positivity
  field_simp [logNe, powerPos.ne', plusPos.ne', inversePlusPos.ne']
  ring

theorem R_derivative (y : ℝ) : HasDerivAt R (1 + (1 + (2 : ℝ) ^ y)⁻¹ / 2) y := by
  refine ((hasDerivAt_id y).sub ((g_derivative y).div_const 2)).congr_deriv ?_
  ring

theorem g_strictAnti : StrictAnti g :=
  strictAnti_of_hasDerivAt_neg g_derivative fun y ↦ neg_lt_zero.mpr (reciprocal_pos y)

theorem R_strictMono : StrictMono R :=
  strictMono_of_hasDerivAt_pos R_derivative fun _ ↦ by positivity

private theorem ascending_loss_strictMono : StrictMono (fun y : ℝ ↦ y + g y / 2) := by
  refine strictMono_of_hasDerivAt_pos
    (fun y ↦ (hasDerivAt_id y).add ((g_derivative y).div_const 2)) ?_
  intro y
  have bound : (1 + (2 : ℝ) ^ y)⁻¹ < 1 := reciprocal_lt_one y
  linarith only [bound]

theorem R_continuous : Continuous R :=
  continuous_iff_continuousAt.mpr fun y ↦ (R_derivative y).continuousAt

private theorem g_continuous : Continuous g :=
  continuous_iff_continuousAt.mpr fun y ↦ (g_derivative y).continuousAt

@[simp] theorem g_zero : g 0 = 1 := by
  simp [g, one_add_one_eq_two]

@[simp] theorem R_zero : R 0 = -(1 / 2) := by simp [R]

theorem R_lt_self (y : ℝ) : R y < y := by
  unfold R
  linarith only [g_pos y]

private theorem y_pos_of_domain {y : ℝ} (positive : 0 < R y) : 0 < y :=
  positive.trans (R_lt_self y)

/-- The two loss terms balance at the unique solution of `R y = r` for each nonnegative ratio
`r`. -/
theorem balance : WeightedConstantSpec.Balance := by
  intro r nonnegative
  have ordered : 0 ≤ r + 1 := by linarith
  have start : R 0 ≤ r := by rw [R_zero]; linarith
  have gBound : g (r + 1) ≤ 1 := (g_strictAnti.antitone ordered).trans_eq g_zero
  have finish : r ≤ R (r + 1) := by unfold R; linarith
  obtain ⟨y, _, balanced⟩ := intermediate_value_Icc ordered R_continuous.continuousOn
    (show r ∈ Set.Icc (R 0) (R (r + 1)) from ⟨start, finish⟩)
  exact ⟨y, balanced, fun z eq ↦ R_strictMono.injective (eq.trans balanced.symm)⟩

/-- The bounds at one follow from the exact comparisons `2 < (3/2)^2` and `(3/2)^3 < 4`. -/
theorem g_one_bounds : (1 / 2 : ℝ) < g 1 ∧ g 1 < (2 / 3 : ℝ) := by
  have gOne : g 1 = Real.logb 2 (3 / 2) := by
    unfold g
    rw [Real.rpow_neg_one]
    norm_num
  have low : Real.logb 2 2 < Real.logb 2 ((3 / 2 : ℝ) ^ (2 : ℕ)) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have high : Real.logb 2 ((3 / 2 : ℝ) ^ (3 : ℕ)) < Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))] at low
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))] at high
  rw [gOne]
  norm_num at low high
  constructor <;> linarith only [low, high]

/-- The factor that determines the sign of the derivative of the squared objective on the
domain. -/
private noncomputable def critical (y : ℝ) : ℝ :=
  y * (1 - reciprocal y / 2) - g y

private theorem critical_formula (y : ℝ) :
    critical y = 2 * R y - y * (1 + reciprocal y / 2) := by
  unfold critical R
  ring

private theorem critical_continuous : Continuous critical := by
  have power : Continuous (fun y : ℝ ↦ (2 : ℝ) ^ y) :=
    Real.continuous_const_rpow (by norm_num)
  have denominator : Continuous (fun y : ℝ ↦ (1 : ℝ) + (2 : ℝ) ^ y) := continuous_const.add power
  have invContinuous : Continuous reciprocal := denominator.inv₀ (fun _ ↦ by positivity)
  exact (continuous_id.mul (continuous_const.sub (invContinuous.div_const 2))).sub g_continuous

private theorem critical_strictMonoOn : StrictMonoOn critical (Set.Ici 0) := by
  intro a ha b _ order
  have weight : 1 - reciprocal a / 2 ≤ 1 - reciprocal b / 2 := by
    have ordered := reciprocal_antitone order.le
    linarith only [ordered]
  have positive : 0 < 1 - reciprocal b / 2 := by linarith only [reciprocal_lt_one b]
  have increase : a * (1 - reciprocal a / 2) < b * (1 - reciprocal b / 2) :=
    (mul_le_mul_of_nonneg_left weight ha).trans_lt (mul_lt_mul_of_pos_right order positive)
  unfold critical
  linarith only [increase, g_strictAnti order]

private theorem critical_exists : ∃ y ∈ Set.Ioo (0 : ℝ) 1, critical y = 0 ∧ 0 < R y := by
  have negative : critical 0 < 0 := by norm_num [critical]
  have positive : 0 < critical 1 := by
    unfold critical reciprocal
    rw [Real.rpow_one]
    linarith only [g_one_bounds.2]
  obtain ⟨y, inside, root⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    critical_continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (critical 0) (critical 1) from ⟨negative.le, positive.le⟩)
  have yPos : 0 < y := lt_of_le_of_ne inside.1 fun same ↦
    negative.ne (by simpa only [← same] using root)
  have yLt : y < 1 := lt_of_le_of_ne inside.2 fun same ↦
    positive.ne' (by simpa only [same] using root)
  refine ⟨y, ⟨yPos, yLt⟩, root, ?_⟩
  -- At the critical point the identity `2 * R y = y * (1 + reciprocal y / 2)` puts the root
  -- inside the positive-denominator domain.
  have product : 0 < y * (1 + reciprocal y / 2) := by
    have := reciprocal_pos y
    positivity
  rw [critical_formula] at root
  linarith only [product, root]

/-- One quarter of the squared objective on `R y > 0`. -/
private noncomputable def objectiveSq (y : ℝ) : ℝ := y ^ 2 / R y

private theorem objective_square (y : ℝ) (positive : 0 < R y) :
    (objective y) ^ 2 = 4 * objectiveSq y := by
  unfold objective objectiveSq
  rw [div_pow, mul_pow, Real.sq_sqrt positive.le]
  ring

private theorem objective_pos {y : ℝ} (positive : 0 < R y) : 0 < objective y :=
  div_pos (mul_pos (by norm_num) (y_pos_of_domain positive)) (Real.sqrt_pos.mpr positive)

private theorem objective_lt_of_sq_lt {a b : ℝ} (aPos : 0 < R a) (bPos : 0 < R b)
    (smaller : objectiveSq a < objectiveSq b) : objective a < objective b := by
  apply (sq_lt_sq₀ (objective_pos aPos).le (objective_pos bPos).le).mp
  rw [objective_square a aPos, objective_square b bPos]
  exact mul_lt_mul_of_pos_left smaller (by norm_num)

private theorem objectiveSq_derivative (y : ℝ) (positive : 0 < R y) :
    HasDerivAt objectiveSq (y * critical y / (R y) ^ 2) y := by
  refine (((hasDerivAt_id y).fun_pow 2).div (R_derivative y) positive.ne').congr_deriv ?_
  norm_num [critical_formula, reciprocal]
  ring

/-- A zero of the derivative numerator in the domain gives a strict global minimizer. -/
private theorem objective_lt_at_critical {star y : ℝ} (starPos : 0 < R star)
    (root : critical star = 0)
    (yPos : 0 < R y) (different : y ≠ star) : objective star < objective y := by
  -- Both objectives are positive. The sign of the derivative of `objectiveSq` follows the sign of
  -- `critical` on the whole interval to the root.
  apply objective_lt_of_sq_lt starPos yPos
  rcases lt_or_gt_of_ne different with left | right
  · have domainOf (z : ℝ) (inside : z ∈ Set.Icc y star) : 0 < R z :=
      yPos.trans_le (R_strictMono.monotone inside.1)
    have negative (z : ℝ) (inside : z ∈ interior (Set.Icc y star)) : deriv objectiveSq z < 0 := by
      have positive := domainOf z (interior_subset inside)
      rw [interior_Icc] at inside
      have sign := critical_strictMonoOn (y_pos_of_domain positive).le
          (y_pos_of_domain starPos).le inside.2
      rw [root] at sign
      rw [(objectiveSq_derivative z positive).deriv]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (y_pos_of_domain positive) sign)
        (sq_pos_of_pos positive)
    have decreasing := strictAntiOn_of_deriv_neg (convex_Icc y star)
      (fun z inside ↦ (objectiveSq_derivative z (domainOf z
        inside)).continuousAt.continuousWithinAt)
      negative
    exact decreasing ⟨le_rfl, left.le⟩ ⟨left.le, le_rfl⟩ left
  · have domainOf (z : ℝ) (inside : z ∈ Set.Icc star y) : 0 < R z :=
      starPos.trans_le (R_strictMono.monotone inside.1)
    have positive (z : ℝ) (inside : z ∈ interior (Set.Icc star y)) : 0 < deriv objectiveSq z := by
      have domainPos := domainOf z (interior_subset inside)
      rw [interior_Icc] at inside
      have sign := critical_strictMonoOn (y_pos_of_domain starPos).le
          (y_pos_of_domain domainPos).le inside.1
      rw [root] at sign
      rw [(objectiveSq_derivative z domainPos).deriv]
      exact div_pos (mul_pos (y_pos_of_domain domainPos) sign) (sq_pos_of_pos domainPos)
    have increasing := strictMonoOn_of_deriv_pos (convex_Icc star y)
      (fun z inside ↦ (objectiveSq_derivative z (domainOf z
        inside)).continuousAt.continuousWithinAt)
      positive
    exact increasing ⟨le_rfl, right.le⟩ ⟨right.le, le_rfl⟩ right

/-- The objective in (A.14) has a unique minimizer on the domain `R y > 0`. -/
theorem unique_minimizer : WeightedConstantSpec.UniqueMinimizer := by
  obtain ⟨star, _, root, positive⟩ := critical_exists
  refine ⟨star, ⟨positive, ?_⟩, ?_⟩
  · intro y present
    by_cases same : y = star
    · rw [same]
    · exact (objective_lt_at_critical positive root present same).le
  · intro y minimizes
    by_contra different
    exact (not_lt_of_ge (minimizes.2 star positive))
      (objective_lt_at_critical positive root minimizes.1 different)

/-- The infimum `Cstar` is the value of the objective at its minimizer. -/
theorem attainment : WeightedConstantSpec.Attainment := by
  obtain ⟨y, minimizes, _⟩ := unique_minimizer
  have least : IsLeast (objective '' domain) (objective y) := by
    refine ⟨⟨y, minimizes.1, rfl⟩, ?_⟩
    rintro _ ⟨z, defined, rfl⟩
    exact minimizes.2 z defined
  exact ⟨y, minimizes, least.csInf_eq.symm⟩

theorem Cstar_pos : 0 < Cstar := by
  obtain ⟨y, minimizes, equal⟩ := attainment
  exact equal ▸ objective_pos minimizes.1

theorem Cstar_le_objective (y : ℝ) (positive : 0 < R y) : Cstar ≤ objective y := by
  obtain ⟨star, minimizes, equal⟩ := attainment
  exact equal ▸ minimizes.2 y positive

private theorem minimizer_facts {y : ℝ} (minimizes : Minimizer y) :
    y ∈ Set.Ioo (0 : ℝ) 1 ∧ critical y = 0 := by
  obtain ⟨star, inside, root, positive⟩ := critical_exists
  have same : y = star := by
    by_contra different
    exact (not_lt_of_ge (minimizes.2 star positive))
      (objective_lt_at_critical positive root minimizes.1 different)
  rw [same]
  exact ⟨inside, root⟩

theorem minimizer_lt_one {y : ℝ} (minimizes : Minimizer y) : y < 1 :=
  (minimizer_facts minimizes).1.2

/-- At the minimizing argument the derivative equation is `2 * R y = y * deriv R y`. -/
theorem critical_point : WeightedConstantSpec.CriticalPoint := by
  intro y minimizes
  have root := (minimizer_facts minimizes).2
  rw [critical_formula] at root
  rw [(R_derivative y).deriv]
  change 2 * R y = y * (1 + reciprocal y / 2)
  linarith only [root]

/-- The minimizer supplies a strict margin above the coefficient `1 / 2` needed by the flow
bound. -/
theorem flow_slack : WeightedConstantSpec.FlowSlack := by
  intro y minimizes
  have belowOne := minimizer_lt_one minimizes
  have gLarge : (1 / 2 : ℝ) < g y := g_one_bounds.1.trans (g_strictAnti belowOne)
  have upperR : R y < 1 := (R_lt_self y).trans belowOne
  have lowerR : 0 < R y := minimizes.1
  have upperSqrt : Real.sqrt (R y) < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt lowerR.le upperR
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr lowerR)).mpr
  linarith only [gLarge, upperSqrt]

/-- For a positive ratio `r`, the maximum of the two weighted losses is at least `Cstar * sqrt
r` at every `y`. -/
theorem minmax_lower_bound : WeightedConstantSpec.MinMaxLowerBound := by
  intro r y positive
  obtain ⟨point, balanced, _⟩ := balance r positive.le
  have pointPos : 0 < R point := by
    rw [balanced]
    exact positive
  have minimum := Cstar_le_objective point pointPos
  rw [objective, balanced] at minimum
  have minimumProduct := (le_div_iff₀ (Real.sqrt_pos.mpr positive)).mp minimum
  unfold R at balanced
  apply minimumProduct.trans
  -- Left of the balance point use the decreasing loss `2 * r + g y`. Right of it use the
  -- increasing loss `r + y + g y / 2`.
  by_cases left : y ≤ point
  · apply le_trans _ (le_max_left _ _)
    linarith only [balanced, g_strictAnti.antitone left]
  · apply le_trans _ (le_max_right _ _)
    have other := ascending_loss_strictMono.monotone (le_of_not_ge left)
    linarith only [balanced, other]

end JH.Analysis.WeightedConstant
