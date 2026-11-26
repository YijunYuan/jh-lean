/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.FlowWitnessCuts
public import JH.Graph.AddedPath
public import JH.Parameters.Certificate

/-!
# Row-to-column path packing witnesses

Lemma 3 extracts decreasing record labels by cutting each path at the latest selected label it
uses. Each original path leaves a distinct zero-edge vertex. Counting the rows and columns
available to those vertices gives the counting inequality in the proof of Lemma 3 and a lower
bound on the number of selected records. A selected path can be tested at that record's earlier
prefix.
-/

@[expose] public section

namespace JH.Graph

variable {n count : ℕ} {transcript : Transcript n} {vertices : Set (State n)}
  {row column : Word n}

private theorem path_from_chain {V L : Type*} {edge : L → V → V → Prop}
    (list : List V) {a b : V} (head : list.head? = some a) (last : list.getLast? = some b)
    (chain : list.IsChain (fun x y ↦ ∃ label, edge label x y)) :
    ∃ walk : Walk edge a b, walk.vertices = list := by
  induction list using List.twoStepInduction generalizing a b with
  | nil => simp at head
  | singleton vertex =>
    have first : vertex = a := Option.some.inj head
    have final : vertex = b := Option.some.inj last
    subst a
    subst b
    exact ⟨.nil vertex, rfl⟩
  | cons_cons source middle rest _ ih =>
    have first : source = a := Option.some.inj head
    subst a
    obtain ⟨⟨label, step⟩, linked⟩ := List.isChain_cons_cons.mp chain
    obtain ⟨tail, equal⟩ := ih middle (a := middle) (b := b) rfl
      (by simpa only [List.getLast?_cons_cons] using last) linked
    exact ⟨.cons label step tail, by simp only [Walk.vertices, equal]⟩

private theorem source_in_rows (path : FlowPath transcript vertices)
    {previous : List transcript.Label}
    (valid : path.HasBoundaries row column previous) :
    path.source.val.2 ∈ flowRows transcript row previous := by
  rw [valid.row_eq]
  cases origin : path.rowFrom with
  | none => simp [flowRow, flowRows]
  | some label =>
    obtain ⟨present, direction⟩ := valid.row_from label origin
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨present, decide_eq_true direction⟩)))

private theorem target_in_columns (path : FlowPath transcript vertices)
    {previous : List transcript.Label} (valid : path.HasBoundaries row column previous) :
    path.target.val.1 ∈ flowColumns transcript column previous := by
  rw [valid.column_eq]
  cases origin : path.columnFrom with
  | none => simp [flowColumn, flowColumns]
  | some label =>
    obtain ⟨present, direction⟩ := valid.column_from label origin
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨present, decide_eq_true direction⟩)))

/-- Sweep the record indices down, skipping indices no remaining path uses. A zero-edge
path has no labels left and stays at its recorded vertex. -/
private theorem sweep (bound : ℕ) (within : bound ≤ transcript.length)
    (previous : List transcript.Label) (paths : Fin count → FlowPath transcript vertices)
    (valid : ∀ i, (paths i).HasBoundaries row column previous)
    (below : ∀ i label, label ∈ (paths i).walk.labels → label.val < bound) :
    ∃ (tests : List (FlowTest transcript vertices)) (points : Fin count → vertices),
      tests.Pairwise (fun earlier later ↦ later.label < earlier.label) ∧
      (∀ test ∈ tests, test.label.val < bound) ∧ ValidFlowTests row column previous tests ∧
      (∀ i, points i ∈ (paths i).walk.vertices) ∧
      (∀ i, (points i).val.2 ∈ flowRows transcript row (previous ++ tests.map FlowTest.label) ∧
        (points i).val.1 ∈ flowColumns transcript column
          (previous ++ tests.map FlowTest.label)) := by
  classical
  induction bound generalizing previous paths with
  | zero =>
    have empty (i : Fin count) : (paths i).walk.labels = [] := by
      cases labels : (paths i).walk.labels with
      | nil => rfl
      | cons label rest =>
        exact False.elim (Nat.not_lt_zero _ (below i label (by simp [labels])))
    refine ⟨[], fun i ↦ (paths i).source, List.Pairwise.nil, by simp, trivial,
      fun i ↦ (paths i).walk.source_mem_vertices, ?_⟩
    intro i
    simp only [List.map_nil, List.append_nil]
    refine ⟨source_in_rows (paths i) (valid i), ?_⟩
    rw [(paths i).walk.source_eq_target_of_labels_nil (empty i)]
    exact target_in_columns (paths i) (valid i)
  | succ bound ih =>
    let selected : transcript.Label := ⟨bound, by omega⟩
    have lower {label : transcript.Label} (lt : label.val < bound + 1)
        (unequal : label ≠ selected) : label.val < bound := by
      have ne : label.val ≠ bound := fun eq ↦ unequal (Fin.ext eq)
      omega
    by_cases used : ∃ i, selected ∈ (paths i).walk.labels
    · obtain ⟨i, present⟩ := used
      -- All remaining paths that use this label are cut so it disappears everywhere.
      -- Their new endpoint coordinates can cite this label in subsequent witness tests.
      have trims (j : Fin count) : ∃ shortened : FlowPath transcript vertices,
          shortened.walk.vertices ⊆ (paths j).walk.vertices ∧
          shortened.walk.labels ⊆ (paths j).walk.labels ∧ selected ∉ shortened.walk.labels ∧
          shortened.HasBoundaries row column (previous ++ [selected]) := by
        by_cases occurs : selected ∈ (paths j).walk.labels
        · exact (paths j).truncate selected occurs (valid j)
        · exact ⟨paths j, fun _ h ↦ h, fun _ h ↦ h, occurs,
            (valid j).mono (fun _ mem ↦ List.mem_append_left _ mem)⟩
      choose shortened subVertices subLabels absent validShort using trims
      have belowShort (j : Fin count) (label : transcript.Label) (mem : label ∈
          (shortened j).walk.labels) :
          label.val < bound :=
        lower (below j label (subLabels j mem)) fun eq ↦ absent j (eq ▸ mem)
      obtain ⟨tests, points, decreasing, later, good, kept, grid⟩ :=
        ih (by omega) (previous ++ [selected]) shortened validShort belowShort
      refine ⟨⟨selected, paths i⟩ :: tests, points, ?_, ?_, ?_, fun j ↦ subVertices j (kept j), ?_⟩
      · exact List.pairwise_cons.mpr ⟨later, decreasing⟩
      · intro test mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact Nat.lt_succ_self bound
        · exact Nat.lt_succ_of_lt (later test mem)
      · refine ⟨⟨valid i, present, ?_⟩, good⟩
        exact fun label mem ↦ Nat.le_of_lt_succ (below i label mem)
      · simpa only [List.append_assoc, List.singleton_append, List.map_cons] using grid
    · have belowNext (i : Fin count) (label : transcript.Label) (mem : label ∈
        (paths i).walk.labels) :
          label.val < bound :=
        lower (below i label mem) fun eq ↦ used ⟨i, eq ▸ mem⟩
      obtain ⟨tests, points, decreasing, later, good, kept, grid⟩ :=
        ih (by omega) previous paths valid belowNext
      exact ⟨tests, points, decreasing, fun test mem ↦
        Nat.lt_succ_of_lt (later test mem), good, kept, grid⟩

private theorem grid_card_bound (labels : List transcript.Label) (points : Fin count → vertices)
    (distinct : Function.Injective points)
    (inGrid : ∀ i, (points i).val.2 ∈ flowRows transcript row labels ∧
      (points i).val.1 ∈ flowColumns transcript column labels) :
    count ≤ ((flowLabels transcript .forward labels).length + 1) *
      ((flowLabels transcript .backward labels).length + 1) := by
  let rows := flowRows transcript row labels
  let columns := flowColumns transcript column labels
  let point (i : Fin count) : ↥(rows ×ˢ columns) :=
    ⟨(points i).val.swap, Finset.mem_product.mpr (inGrid i)⟩
  have injection : Function.Injective point := by
    intro i j equal
    apply distinct
    exact Subtype.ext (congrArg (fun p : ↥(rows ×ˢ columns) ↦ p.val.swap) equal)
  have card : count ≤ rows.card * columns.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe, Finset.card_product] using
      Fintype.card_le_of_injective point injection
  have rowsBound : rows.card ≤ (flowLabels transcript .forward labels).length + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      (Finset.card_image_le.trans (List.toFinset_card_le _)) 1)
  have columnsBound : columns.card ≤ (flowLabels transcript .backward labels).length + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      (Finset.card_image_le.trans (List.toFinset_card_le _)) 1)
  exact card.trans (Nat.mul_le_mul rowsBound columnsBound)

/-- Turn a vertex-disjoint packing into a decreasing list of record tests and an
injective placement of the remaining vertices in the grid of generated boundaries. -/
theorem extract_flow_witness : FlowWitnessSpec.Extract := by
  classical
  intro n transcript vertices row column count packed
  obtain ⟨lists, simple, disjoint⟩ := packed
  have labelled (i : Fin count) : ∃ path : FlowPath transcript vertices,
      path.HasBoundaries row column [] ∧ path.walk.vertices = lists i := by
    obtain ⟨a, inRow, head⟩ := (simple i).starts
    obtain ⟨b, inColumn, last⟩ := (simple i).ends
    have chain : (lists i).IsChain (fun x y ↦
        ∃ label, residualRecordEdge transcript vertices label x y) :=
      (simple i).chain
    obtain ⟨walk, equal⟩ := path_from_chain (lists i) head last chain
    exact ⟨⟨a, b, walk, none, none⟩, ⟨inRow, inColumn, by simp, by simp⟩, equal⟩
  choose paths valid lists_eq using labelled
  obtain ⟨tests, points, decreasing, _, good, kept, grid⟩ :=
    sweep transcript.length le_rfl [] paths valid (fun _ label _ ↦ label.isLt)
  -- Each surviving vertex lies on its original path, so packing disjointness still applies.
  have distinct : Function.Injective points := by
    intro i j equal
    by_contra different
    have hi := kept i
    have hj := kept j
    rw [lists_eq i] at hi
    rw [lists_eq j, ← equal] at hj
    exact disjoint different (points i) hi hj
  simp only [List.nil_append] at grid
  exact ⟨⟨tests, decreasing, good, points, distinct, grid,
    grid_card_bound (tests.map FlowTest.label) points distinct grid⟩⟩

theorem flowLabels_lengths_sum (transcript : Transcript n) (labels : List transcript.Label) :
    (flowLabels transcript .forward labels).length +
      (flowLabels transcript .backward labels).length = labels.length := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    simp only [flowLabels, List.filter_cons, List.length_cons, List.get_eq_getElem] at ih ⊢
    cases transcript[label.val].direction <;> simp <;> omega

/-- The counting inequality in Lemma 3 forces at least `p.h` selected labels at the flow
threshold. -/
theorem flow_witness_record_count : FlowWitnessSpec.RecordCount := by
  intro p transcript vertices row column witness
  let labels := witness.tests.map FlowTest.label
  let forward := (flowLabels transcript .forward labels).length
  let backward := (flowLabels transcript .backward labels).length
  have sum : forward + backward = witness.tests.length := calc
    _ = labels.length := flowLabels_lengths_sum transcript labels
    _ = _ := by simp [labels]
  have lower : p.pi + 1 ≤ (forward + 1) * (backward + 1) := witness.grid_bound
  -- Bound the product by the square of half the sum via the nonnegative squared difference.
  have realLower : (p.pi : ℝ) + 1 ≤ ((forward : ℝ) + 1) * ((backward : ℝ) + 1) := by
    exact_mod_cast lower
  have realSum : (forward : ℝ) + (backward : ℝ) = (witness.tests.length : ℝ) := by
    exact_mod_cast sum
  apply p.h_le_of_flow_grid (realLower.trans ?_)
  rw [← realSum]
  nlinarith only [sq_nonneg ((forward : ℝ) - (backward : ℝ))]

private theorem walk_with_selected_label {earlier : Set (State n)} (enlarge : vertices ⊆ earlier)
    (selected : transcript.Label) {a b : vertices}
      (walk : Walk (residualRecordEdge transcript vertices) a b)
    (latest : ∀ label ∈ walk.labels, label ≤ selected) :
    ∃ path : AddedWalk (residualRecordEdge (transcript.take selected.val) earlier)
      (residualNewEdge (transcript.get selected) earlier)
      ⟨a.val, enlarge a.property⟩ ⟨b.val, enlarge b.property⟩,
      (selected ∈ walk.labels → 0 < path.newUses) := by
  induction walk with
  | nil vertex => exact ⟨.nil _, by simp [Walk.labels]⟩
  | @cons a middle b label step tail ih =>
    obtain ⟨rest, positive⟩ := ih (fun i mem ↦ latest i (List.mem_cons_of_mem _ mem))
    by_cases same : label = selected
    · subst label
      have newStep : residualNewEdge (transcript.get selected) earlier
          ⟨a.val, enlarge a.property⟩ ⟨middle.val, enlarge middle.property⟩ := step
      exact ⟨.cons .new newStep rest, fun _ ↦ by simp⟩
    · have older : label < selected := lt_of_le_of_ne
        (latest label List.mem_cons_self) same
      let prefixLabel : Transcript.Label (transcript.take selected.val) := ⟨label.val,
        by
          simpa only [List.length_take_of_le (Nat.le_of_lt selected.isLt)] using
            Fin.lt_def.mp older⟩
      have record_eq : (transcript.take selected.val).get prefixLabel = transcript.get label := by
        simp [prefixLabel]
      have oldStep : residualRecordEdge (transcript.take selected.val) earlier prefixLabel
          ⟨a.val, enlarge a.property⟩ ⟨middle.val, enlarge middle.property⟩ := by
        simpa only [residualRecordEdge, Transcript.realEdge, record_eq] using step
      refine ⟨.cons (.old prefixLabel) oldStep rest, fun used ↦ ?_⟩
      rw [AddedWalk.newUses_old]
      exact positive ((List.mem_cons.mp used).resolve_left (Ne.symm same))

/-- At the selected label's original round, the witness uses that record and only older
ones. Residual monotonicity allows the test on the earlier, larger vertex set. -/
theorem flow_test_on_prefix : FlowWitnessSpec.PrefixTest := by
  intro n transcript vertices earlier row column previous test enlarge good
  obtain ⟨walk, uses⟩ := walk_with_selected_label enlarge test.label test.path.walk good.latest
  exact ⟨⟨test.path.source.val, enlarge test.path.source.property⟩,
    ⟨test.path.target.val, enlarge test.path.target.property⟩,
    good.boundaries.row_eq, good.boundaries.column_eq, walk, uses good.uses⟩

end JH.Graph
