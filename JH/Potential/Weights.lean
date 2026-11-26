/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelProofs
public import JH.Potential.Patterns
public import JH.Potential.WeightsSpec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity

/-!
# Point and translated potentials

Forward weight is a capped sum of powered row-ancestor counts. The zero singleton mode recovers
the point potential, and the empty record graph gives the initial translated bound. A forward
graft carries a row with enough ancestors through its root, so each removed successor pays one
unit of point potential.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

theorem normalized_row_nonneg (edge : State n → State n → Prop) (vertices : Set (State n))
    (mu d : ℕ) (targets : Set (State n)) (row : Word n) :
    0 ≤ normalizedRowWeight edge vertices mu d targets row := by
  unfold normalizedRowWeight
  positivity

/-- The normalized weight is nonnegative and capped at one. -/
theorem forward_weight_range (edge : State n → State n → Prop) (vertices : Set (State n))
    (mu d : ℕ) (targets : Set (State n)) :
    0 ≤ forwardWeight edge vertices mu d targets ∧ forwardWeight edge vertices mu d targets ≤ 1 :=
  ⟨le_min (by norm_num) (Finset.sum_nonneg fun row _ ↦
    normalized_row_nonneg edge vertices mu d targets row), min_le_left _ _⟩

theorem reachesWithin_mono {edge smallEdge : State n → State n → Prop}
    {vertices small : Set (State n)} {a b : State n}
    (subVertices : small ⊆ vertices)
    (subEdges : ∀ source target, smallEdge source target → edge source target)
    (reaches : ReachesWithin smallEdge small a b) : ReachesWithin edge vertices a b :=
  ⟨subVertices reaches.1, subVertices reaches.2.1,
    Relation.ReflTransGen.mono (r := inducedEdge smallEdge small)
      (fun _ _ h ↦ ⟨subVertices h.1, subVertices h.2.1, subEdges _ _ h.2.2⟩) a b reaches.2.2⟩

theorem row_ancestors_to_mono {edge smallEdge : State n → State n → Prop}
    {vertices small targets smallTargets : Set (State n)} {row : Word n}
    (subVertices : small ⊆ vertices) (subTargets : smallTargets ⊆ targets)
    (subEdges : ∀ source target, smallEdge source target → edge source target) :
    rowAncestorsTo smallEdge small row smallTargets ⊆ rowAncestorsTo edge vertices row targets := by
  rintro source ⟨fromRow, target, ht, reach⟩
  exact ⟨fromRow, target, subTargets ht, reachesWithin_mono subVertices subEdges reach⟩

/-- Reachability increases under enlarging the vertices, edges or target set, so
the capped ancestor weight can only increase. -/
theorem forward_weight_mono {edge smallEdge : State n → State n → Prop}
    {vertices small targets smallTargets : Set (State n)} {mu d : ℕ}
    (subVertices : small ⊆ vertices) (subTargets : smallTargets ⊆ targets)
    (subEdges : ∀ source target, smallEdge source target → edge source target) :
    forwardWeight smallEdge small mu d smallTargets ≤ forwardWeight edge vertices mu d targets := by
  apply min_le_min le_rfl
  apply Finset.sum_le_sum
  intro row _
  unfold normalizedRowWeight
  have count : (rowAncestorsTo smallEdge small row smallTargets).ncard ≤
      (rowAncestorsTo edge vertices row targets).ncard :=
    Set.ncard_mono (row_ancestors_to_mono subVertices subTargets subEdges)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr count) _

theorem rowAncestorsTo_singleton (edge : State n → State n → Prop)
    (vertices : Set (State n)) (row : Word n) (state : State n) :
    rowAncestorsTo edge vertices row {state} = rowAncestors edge vertices row state := by
  ext source
  simp [rowAncestorsTo, rowAncestors]

theorem forward_weight_empty {edge : State n → State n → Prop} {vertices : Set (State n)}
    {mu d : ℕ} (degree : 0 < d) : forwardWeight edge vertices mu d ∅ = 0 := by
  have emptyRow (row : Word n) : rowAncestorsTo edge vertices row ∅ = ∅ := by
    ext source
    simp [rowAncestorsTo]
  simp [forwardWeight, normalizedRowWeight, emptyRow, Nat.ne_of_gt degree]

private theorem mem_columnRates {vertices : Set (State n)} {column rate : Word n} :
    rate ∈ columnRates vertices column ↔ (column, rate) ∈ vertices := by
  classical
  simp [columnRates]

private theorem singleton_column_pattern {vertices : Set (State n)} {column rate : Word n}
    (present : (column, rate) ∈ vertices) :
    columnPattern vertices column {0} rate = {(column, rate)} := by
  ext state
  constructor
  · rintro ⟨_, hcol, hrate⟩
    exact Set.mem_singleton_iff.mpr (Prod.ext hcol (by
      simpa [xorTranslate, BitVec.xor_zero] using hrate))
  · intro member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨present, rfl, by simp [xorTranslate, BitVec.xor_zero]⟩

private theorem absent_singleton_column_pattern {vertices : Set (State n)} {column rate : Word n}
    (absent : (column, rate) ∉ vertices) :
    columnPattern vertices column {0} rate = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro state
  rintro ⟨present, hcol, hrate⟩
  have equal : state = (column, rate) :=
    Prod.ext hcol (by simpa [xorTranslate, BitVec.xor_zero] using hrate)
  exact absent (equal ▸ present)

/-- Translating the singleton zero mode picks out one point in the column at a time.
The resulting translated potential equals the point potential. -/
theorem singleton_mode_is_point_column : PotentialSpec.SingletonMode := by
  intro n edge vertices mu d column degree
  classical
  unfold translatedPotential pointColumnPotential columnRates
  rw [Finset.card_singleton, Nat.cast_one, div_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rate _
  by_cases present : (column, rate) ∈ vertices
  · rw [ite_eq_left present, singleton_column_pattern present]
  · rw [ite_eq_right present, absent_singleton_column_pattern present, forward_weight_empty degree]

theorem no_record_reaches_same {vertices : Set (State n)} {a b : State n}
    (reach : ReachesWithin (realRecordRelation ([] : Transcript n)) vertices a b) : a = b := by
  induction reach.2.2 with
  | refl => rfl
  | tail _ edge _ =>
    obtain ⟨label, _⟩ := edge.2.2
    exact Fin.elim0 label

theorem card_xorTranslate (offset : Word n) (mode : Finset (Word n)) :
    (xorTranslate offset mode).card = mode.card := by
  apply Finset.card_image_of_injective
  intro x y equal
  have result := congrArg (fun t ↦ offset ^^^ t) equal
  simpa only [xor_left_cancel] using result

private theorem initial_pattern_weight (vertices : Set (State n)) (mu d : ℕ)
    (column offset : Word n) (mode : Finset (Word n)) (degree : 0 < d) :
    forwardWeight (realRecordRelation ([] : Transcript n)) vertices mu d
      (columnPattern vertices column mode offset) ≤ (mode.card : ℝ) / (mu : ℝ) ^ d := by
  classical
  let edge := realRecordRelation ([] : Transcript n)
  let targets := columnPattern vertices column mode offset
  let translated := xorTranslate offset mode
  -- With zero edges, a row can contribute only its own point in the target column.
  have perRow (row : Word n) :
      normalizedRowWeight edge vertices mu d targets row ≤
        if row ∈ translated then 1 / (mu : ℝ) ^ d else 0 := by
    by_cases allowed : row ∈ translated
    · have onlyPoint : rowAncestorsTo edge vertices row targets ⊆ {(column, row)} := by
        rintro point ⟨pointRow, target, ⟨_, targetColumn, _⟩, reaches⟩
        have same := no_record_reaches_same reaches
        subst target
        exact Set.mem_singleton_iff.mpr (Prod.ext targetColumn pointRow)
      have count : (rowAncestorsTo edge vertices row targets).ncard ≤ 1 :=
        (Set.ncard_mono onlyPoint).trans (Set.ncard_singleton _).le
      rw [ite_eq_left allowed, normalizedRowWeight]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa using pow_le_pow_left₀ (by positivity : 0 ≤
        ((rowAncestorsTo edge vertices row targets).ncard : ℝ)) (Nat.cast_le.mpr count) d
    · have empty : rowAncestorsTo edge vertices row targets = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro point ⟨pointRow, target, ⟨_, _, inMode⟩, reaches⟩
        have same := no_record_reaches_same reaches
        subst target
        exact allowed (pointRow ▸ inMode)
      simp [allowed, normalizedRowWeight, empty, Nat.ne_of_gt degree]
  have filter_eq : Finset.univ.filter (fun r ↦ r ∈ translated) = translated := by
    ext r
    simp
  calc
    _ ≤ ∑ row : Word n, normalizedRowWeight edge vertices mu d targets row := min_le_right _ _
    _ ≤ ∑ row : Word n, if row ∈ translated then (1 : ℝ) / (mu : ℝ) ^ d else 0 :=
      Finset.sum_le_sum fun row _ ↦ perRow row
    _ = _ := by
      rw [← Finset.sum_filter, filter_eq]
      simp [translated, card_xorTranslate, nsmul_eq_mul, div_eq_mul_inv]

/-- On the empty record graph the translated potential is at most `2 ^ n / mu ^ d`
for positive threshold and exponent, including when the mode is empty. -/
theorem initial_translated_potential : PotentialSpec.InitialPotential := by
  intro n vertices mu d column mode positiveMu positiveD
  classical
  by_cases empty : mode.card = 0
  · simp only [translatedPotential, empty, Nat.cast_zero, div_zero]
    positivity
  have modeNonzero : (mode.card : ℝ) ≠ 0 := by exact_mod_cast empty
  have muNonzero : (mu : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr positiveMu)
  calc
    _ ≤ (∑ _ : Word n, (mode.card : ℝ) / (mu : ℝ) ^ d) / (mode.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun offset _ ↦
        initial_pattern_weight vertices mu d column offset mode positiveD) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [word_card n, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- A row with at least `mu` residual ancestors of the root makes every residual
successor of that root have forward point weight one. -/
theorem graft_point_weight : PotentialSpec.GraftPointWeight := by
  intro n edge vertices mu d root target row positiveMu enough reach
  have ancestors :
      rowAncestors edge vertices row root ⊆ rowAncestorsTo edge vertices row {target} :=
    fun source ⟨fromRow, oldPath⟩ ↦
      ⟨fromRow, target, rfl, ⟨oldPath.1, reach.2.1, oldPath.2.2.trans reach.2.2⟩⟩
  have count := enough.trans (Set.ncard_mono ancestors)
  have unit : 1 ≤ normalizedRowWeight edge vertices mu d {target} row := by
    unfold normalizedRowWeight
    have pos : 0 < (mu : ℝ) ^ d := pow_pos (Nat.cast_pos.mpr positiveMu) _
    apply (le_div_iff₀ pos).2
    simpa only [one_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ (mu : ℝ))
      (Nat.cast_le.mpr count) d
  apply min_eq_left
  exact unit.trans (Finset.single_le_sum (fun rate _ ↦
    normalized_row_nonneg edge vertices mu d {target} rate) (Finset.mem_univ row))

/-- Deleting vertices of unit point weight decreases the point potential by at least
their number in the column. -/
theorem deletion_pays_column : PotentialSpec.DeletionPayment := by
  intro n edge before after mu d column paidRates subVertices paid
  classical
  let kept := columnRates after column
  let original := columnRates before column
  let oldWeight (rate : Word n) := forwardWeight edge before mu d {(column, rate)}
  have disjoint : Disjoint kept paidRates := by
    apply Finset.disjoint_left.mpr
    intro rate still paidHere
    exact (paid rate paidHere).2.1 (mem_columnRates.mp still)
  have contained : kept ∪ paidRates ⊆ original := by
    intro rate member
    apply mem_columnRates.mpr
    rcases Finset.mem_union.mp member with still | paidHere
    · exact subVertices (mem_columnRates.mp still)
    · exact (paid rate paidHere).1
  -- The kept points have smaller ancestor sets. The paid points are disjoint from them
  -- and each had weight one before deletion.
  have remaining : pointColumnPotential edge after mu d column ≤ ∑ rate ∈ kept, oldWeight rate :=
    Finset.sum_le_sum fun rate _ ↦ forward_weight_mono subVertices (fun _ h ↦ h) (fun _ _ h ↦ h)
  have counted : (∑ rate ∈ paidRates, oldWeight rate) = (paidRates.card : ℝ) := by
    calc
      _ = ∑ _ ∈ paidRates, (1 : ℝ) := Finset.sum_congr rfl fun rate hr ↦ (paid rate hr).2.2
      _ = _ := by simp
  calc
    _ ≤ (∑ rate ∈ kept, oldWeight rate) + (∑ rate ∈ paidRates, oldWeight rate) :=
      add_le_add remaining (le_of_eq counted.symm)
    _ = ∑ rate ∈ kept ∪ paidRates, oldWeight rate := (Finset.sum_union disjoint).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg contained fun rate _ _ ↦
      (forward_weight_range edge before mu d {(column, rate)}).1

end JH.Graph
