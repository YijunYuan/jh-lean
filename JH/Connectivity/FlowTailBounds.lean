/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.Endpoints
public import JH.Connectivity.FlowTailSpec
public import JH.Connectivity.ShiftTest
public import JH.Graph.Evolution.StoppedGraph
public import JH.Oracle.Independent.CoordinateTape
public import JH.Probability.Tape.Tests
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Counting and testing encoded flow witnesses

Lemma 3 counts encodings by the original row and column, the selected record indices, and the
two boundary origins at each reverse rank. After the intrinsic tape is fixed, each selected
test has a uniform bound over the fresh offset for every preceding offset prefix. The product
bound proceeds in time order.
-/

@[expose] public section

namespace JH.Graph.FlowTail

open Parameters Probability
open PartialPermutation (uniformFinite)
open scoped ENNReal BigOperators

variable {q h : ℕ}

/-- Read a chosen set of record indices in decreasing time order. -/
theorem roundAt_strictAnti (selected : Selected q h) : StrictAnti (roundAt selected) := by
  intro a b order
  exact (selected.val.orderEmbOfFin selected.property).strictMono (Fin.rev_lt_rev.mpr order)

theorem roundAt_mem (selected : Selected q h) (rank : Fin h) :
    roundAt selected rank ∈ selected.val :=
  selected.val.orderEmbOfFin_mem selected.property rank.rev

theorem exists_roundAt (selected : Selected q h) {i : Fin q} (present : i ∈ selected.val) :
    ∃ rank : Fin h, roundAt selected rank = i := by
  have inRange : i ∈ Set.range (selected.val.orderEmbOfFin selected.property) := by
    rw [Finset.range_orderEmbOfFin]
    exact present
  obtain ⟨j, rfl⟩ := inRange
  exact ⟨j.rev, by simp only [roundAt, Fin.rev_rev]⟩

/-- The sorted set of indices recovers the original decreasing sequence. -/
theorem roundAt_of_strictAnti {f : Fin h → Fin q} (ordered : StrictAnti f) :
    ∃ selected : Selected q h, roundAt selected = f := by
  let embedding : Fin h ↪ Fin q := ⟨f, ordered.injective⟩
  let selected : Selected q h := ⟨Finset.univ.map embedding, by simp⟩
  let increasing (j : Fin h) := f j.rev
  have sorted : StrictMono increasing := fun _ _ less ↦ ordered (Fin.rev_lt_rev.mpr less)
  have within (j : Fin h) : increasing j ∈ selected.val :=
    Finset.mem_map.mpr ⟨j.rev, Finset.mem_univ _, rfl⟩
  have eq := Finset.orderEmbOfFin_unique selected.property within sorted
  refine ⟨selected, funext fun j ↦ ?_⟩
  simpa only [roundAt, increasing, Fin.rev_rev] using (congrFun eq j.rev).symm

/-- Count all encodings, including the pairs of boundary origins at every rank. -/
theorem encoding_card : FlowTailSpec.EncodingCard := by
  intro n q h
  have rounds : Fintype.card (Selected q h) = q.choose h := by
    simp [Selected, Fintype.card_finset_len]
  -- At zero-based rank `j`, each of the two origins has `j + 1` choices.
  have origins : Fintype.card (Origins h) = h.factorial ^ 2 := by
    simp only [Origins, Fintype.card_pi, Fintype.card_prod, Fintype.card_fin,
      Finset.prod_mul_distrib]
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) h,
      Finset.prod_range_add_one_eq_factorial, pow_two]
  simp only [Code, Fintype.card_prod, word_card n, rounds, origins, pow_two, Nat.mul_assoc]

theorem mass_ne_top {α : Type*} (law : PMF α) (event : Set α) : law.toOuterMeasure event ≠ ⊤ := by
  simpa only [PMF.toOuterMeasure_apply] using law.tsum_coe_indicator_ne_top event

private theorem reply_record_coords {n : ℕ} (request : Query n) (coordinate offset : Word n) :
    let record := request.recordOfReply (request.replyCoords.symm (coordinate, offset))
    let fixed := request.recordOfReply (request.replyCoords.symm (coordinate, (0 : Word n)))
    record.input.1 = fixed.input.1 ∧ record.output.2 = fixed.output.2 ∧ record.shift = offset := by
  let answer := request.replyCoords.symm (coordinate, offset)
  have pair := (request.recordOfReply_coords answer).trans
    (request.replyCoords.apply_symm_apply (coordinate, offset))
  refine ⟨?_, ?_, congrArg Prod.snd pair⟩ <;>
    rcases request with ⟨direction, address⟩ <;> cases direction <;> rfl

/-- Starting from a valid graph snapshot, fix an encoding, an intrinsic tape and any preceding
offset prefix. The one-round test passes with probability at most $2B_{\mathrm{ver}}^2/N$ under
a fresh uniform offset. -/
theorem conditional_test : FlowTailSpec.ConditionalTest := by
  intro params q psi initials targets program valid code intrinsic i prior
  cases reached : (beforeRound program intrinsic i prior).frontier with
  | done terminal =>
    simp [TapeTests.approving, test, reached]
  | query request resume =>
    cases history : GraphTracker.replay params psi initials targets
        (beforeRound program intrinsic i prior).records with
    | stopped reason snapshot =>
      simp [TapeTests.approving, test, reached, history]
    | active snapshot =>
      by_cases chosen : ∃ rank : Fin params.h, roundAt code.2.1 rank = i
      · obtain ⟨rank, atRound⟩ := chosen
        let recordFor (offset : Word params.n) :=
          request.recordOfReply (request.replyCoords.symm (intrinsic i, offset))
        let row := boundaryValue code.2.1 intrinsic code.1.1 rank (code.2.2 rank).1
        let column := boundaryValue code.2.1 intrinsic code.1.2 rank (code.2.2 rank).2
        let event := {offset | HasNewPath snapshot.records (recordFor offset)
            snapshot.sides.realResidual
          row column}
        have implies : TapeTests.approving
            (test psi initials targets program code intrinsic) i prior ⊆
            event := by
          intro offset passes
          change test psi initials targets program code intrinsic i prior offset at passes
          simp only [test, reached, history] at passes
          obtain ⟨other, sameRound, hasPath⟩ := passes
          have same : other = rank := (roundAt_strictAnti code.2.1).injective
              (sameRound.trans atRound.symm)
          cases same
          exact hasPath
        have active := graph_active_parameters params psi initials targets valid
          (beforeRound program intrinsic i prior).records snapshot history
        -- Only the active prefix graph enters the endpoint supports for this test.
        have supports := endpoint_support_bounds (realRecordRelation snapshot.records)
          snapshot.sides.realResidual params.mu params.pi active.1 active.2.2.1
        -- The request and intrinsic coordinate fix the input column and output row.
        -- Varying the fresh offset changes the shift used by the endpoint test.
        have realBound : uniformShiftMass event ≤ stepBound params := by
          simpa only [stepBound, Params.N, Nat.cast_pow, Nat.cast_ofNat] using
            uniform_new_path_probability snapshot.records snapshot.sides.realResidual params.Pi
              (fun r c ↦ ⟨(supports r c).1, (supports r c).2.1⟩)
              (recordFor 0).input.1 (recordFor 0).output.2 row column recordFor
              (reply_record_coords request (intrinsic i))
        apply (MeasureTheory.measure_mono (μ := (uniformFinite (Word params.n)).toOuterMeasure)
          implies).trans
        rw [PartialPermutation.uniformFinite_eq_uniformOfFintype,
          ← ENNReal.ofReal_toReal (mass_ne_top (uniformPMF (Word params.n)) event)]
        exact ENNReal.ofReal_le_ofReal realBound
      · have empty : TapeTests.approving
          (test psi initials targets program code intrinsic) i prior = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun offset passes ↦ by
            change test psi initials targets program code intrinsic i prior offset at passes
            simp only [test, reached, history] at passes
            obtain ⟨rank, atRound, _⟩ := passes
            exact chosen ⟨rank, atRound⟩
        rw [empty, MeasureTheory.measure_empty]
        exact zero_le

private theorem average_section_bound {A B : Type*} (first : PMF A) (second : PMF B)
    (event : Set (A × B)) (bound : ℝ≥0∞)
    (each : ∀ x, second.toOuterMeasure ((fun y ↦ (x, y)) ⁻¹' event) ≤ bound) :
    (ReplyCoupling.independentPair first second).toOuterMeasure event ≤ bound := by
  rw [ReplyCoupling.independentPair, PMF.toOuterMeasure_bind_apply]
  simp_rw [PMF.toOuterMeasure_map_apply]
  calc
    _ ≤ ∑' x, first x * bound := tsum_le_tsum fun x ↦ mul_le_mul_right (each x) _
    _ = _ := by rw [ENNReal.tsum_mul_right, first.tsum_coe, one_mul]

/-- Multiply the conditional pass bounds and take the union over the encodings. -/
theorem encoded_union : FlowTailSpec.EncodedUnion := by
  intro params q psi initials targets program valid
  let law := CoordinateTape.law params.n q
  let event := fun code : Code params.n q params.h ↦ codeEvent psi initials targets program code
  let bound : ℝ≥0∞ := ENNReal.ofReal (stepBound params) ^ params.h
  have each (code : Code params.n q params.h) : law.toOuterMeasure (event code) ≤ bound := by
    -- The two tapes are independent, so fixing the whole intrinsic tape leaves the offset
    -- tape uniform. Apply the per-prefix test bounds in chronological order and average.
    apply average_section_bound
    intro intrinsic
    have cap := TapeTests.adapted_product_bound (test psi initials targets program code intrinsic)
      code.2.1.val (ENNReal.ofReal (stepBound params))
      (fun i _ prior ↦
        conditional_test params q psi initials targets program valid code intrinsic i prior)
    exact cap.trans_eq (congrArg ((ENNReal.ofReal (stepBound params)) ^ ·) code.2.1.property)
  have total : law.toOuterMeasure (⋃ code, event code) ≤
      (Fintype.card (Code params.n q params.h) : ℝ≥0∞) * bound := by
    calc
      _ ≤ ∑' code, law.toOuterMeasure (event code) := MeasureTheory.measure_iUnion_le event
      _ ≤ ∑' _ : Code params.n q params.h, bound := tsum_le_tsum each
      _ = _ := by simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have finite : (Fintype.card (Code params.n q params.h) : ℝ≥0∞) * bound ≠ ⊤ := by
    apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have stepNonneg : 0 ≤ stepBound params := by unfold stepBound; positivity
  simpa only [law, event, bound, ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal stepNonneg, encoding_card params.n q params.h,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    unionBound, Params.N] using ENNReal.toReal_mono finite total

/-- Use the binomial coefficient and query budget to obtain the tail bound (14). -/
theorem union_bound_le_flowTail (params : Params) (q : ℕ) (budget : params.QueryBudget q) :
    unionBound params q ≤ params.flowTail := by
  let N := (params.N : ℝ)
  let U := (params.U : ℝ)
  let r := 2 * (params.Pi : ℝ) ^ 2
  let f := (params.h.factorial : ℝ)
  have Npos : 0 < N := Nat.cast_pos.mpr params.N_pos
  have Upos : 0 < U := Nat.cast_pos.mpr params.U_pos
  have fpos : 0 < f := Nat.cast_pos.mpr (Nat.factorial_pos params.h)
  have rNonneg : 0 ≤ r := by positivity
  have ratio : 0 ≤ r / N := div_nonneg rNonneg Npos.le
  -- The binomial bound cancels one factorial. The budget absorbs `q / N` into `1 / U`.
  have choose : (q.choose params.h : ℝ) ≤ (q : ℝ) ^ params.h / f :=
    Nat.choose_le_pow_div params.h q
  have scaled : (q : ℝ) * (r / N) ≤ r / U := by
    calc
      _ ≤ (N / U) * (r / N) := mul_le_mul_of_nonneg_right budget ratio
      _ = r / U := by field_simp [Npos.ne', Upos.ne']
  change N ^ 2 * (q.choose params.h : ℝ) * f ^ 2 * (r / N) ^ params.h ≤
    N ^ 2 * f * (r / U) ^ params.h
  calc
    _ ≤ N ^ 2 * ((q : ℝ) ^ params.h / f) * f ^ 2 * (r / N) ^ params.h :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left choose (sq_nonneg _)) (sq_nonneg _)) (pow_nonneg ratio _)
    _ = N ^ 2 * f * ((q : ℝ) * (r / N)) ^ params.h := by
      rw [mul_pow]
      field_simp [fpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by positivity) ratio) scaled _)
      (mul_nonneg (sq_nonneg _) fpos.le)

end JH.Graph.FlowTail
