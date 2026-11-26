/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.EndpointsSpec
public import JH.Graph.Menger
public import JH.ModelProofs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Endpoint supports of the residual graph

For a fixed source row and target column, `endpointPairs` records the two free coordinates of
reachable endpoints. A Menger separator of the residual subtype gives the support bounds of
Lemma 1. Charging to record labels allows the sum over all columns in (13), and reversing paths
and swapping coordinates gives the row sum in the same equation.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

theorem mem_endpointPairs {edge : State n → State n → Prop} {vertices : Set (State n)}
    {row column : Word n} {pair : Word n × Word n} :
    pair ∈ endpointPairs edge vertices row column ↔
      ReachesWithin edge vertices (pair.1, row) (column, pair.2) := by
  classical
  simp [endpointPairs]

/-- Pass between ambient states with residual membership and paths in the residual subtype.
Reflexive paths are allowed at precisely the residual vertices. -/
theorem reachesWithin_iff_residual {edge : State n → State n → Prop}
    {vertices : Set (State n)} {a b : vertices} :
    ReachesWithin edge vertices a.val b.val ↔ Reaches (residualRelation edge vertices) a b := by
  constructor
  · rintro ⟨_, _, path⟩
    suffices liftPath : ∀ {target : State n},
        Reaches (inducedEdge edge vertices) a.val target →
        ∀ htarget : target ∈ vertices,
          Reaches (residualRelation edge vertices) a ⟨target, htarget⟩ by
      exact liftPath path b.property
    intro target hpath
    induction hpath with
    | refl => intro _; exact .refl
    | tail _ last ih =>
        intro _
        exact (ih last.1).tail last.2.2
  · intro path
    exact ⟨a.property, b.property,
      path.lift Subtype.val (fun x y step ↦ ⟨x.property, y.property, step⟩)⟩

private theorem reaches_through_vertex {A : Type*} {edge : A → A → Prop} {source target pivot : A}
    {path : List A} (isPath : IsPath edge {source} {target} path) (onPath : pivot ∈ path) :
    Reaches edge source pivot ∧ Reaches edge pivot target := by
  obtain ⟨before, _, startPath⟩ := isPath.prefix_of_mem onPath
  obtain ⟨after, _, suffix⟩ := isPath.reverse.prefix_of_mem (by simpa using onPath)
  exact ⟨reaches_iff_exists_isPath.mpr ⟨before, startPath⟩,
    (reaches_iff_exists_isPath.mpr ⟨after, suffix⟩).swap⟩

/-- Every reachable endpoint pair has one of the separator vertices on a path. -/
theorem endpoint_pair_through_separator {edge : State n → State n → Prop}
    {vertices : Set (State n)} {row column : Word n} {separator : Finset vertices}
    (separates : IsSeparator (residualRelation edge vertices)
      (rowVertices vertices row) (columnVertices vertices column) separator)
    {pair : Word n × Word n} (present : pair ∈ endpointPairs edge vertices row column) :
    ∃ pivot ∈ separator,
      (pair.1, row) ∈ rowAncestors edge vertices row pivot.val ∧
        (column, pair.2) ∈ columnDescendants edge vertices column pivot.val := by
  have within := mem_endpointPairs.mp present
  let source : vertices := ⟨(pair.1, row), within.1⟩
  let target : vertices := ⟨(column, pair.2), within.2.1⟩
  have reaches : Reaches (residualRelation edge vertices) source target :=
    reachesWithin_iff_residual.mp within
  obtain ⟨path, isPath⟩ := reaches_iff_exists_isPath.mp reaches
  have fromRow : ({source} : Set vertices) ⊆ rowVertices vertices row := by
    intro vertex hv
    rw [Set.mem_singleton_iff.mp hv]
    rfl
  have toColumn : ({target} : Set vertices) ⊆ columnVertices vertices column := by
    intro vertex hv
    rw [Set.mem_singleton_iff.mp hv]
    rfl
  obtain ⟨pivot, inSeparator, onPath⟩ :=
    separates path (isPath.mono (fun _ _ h ↦ h) fromRow toColumn)
  obtain ⟨left, right⟩ := reaches_through_vertex isPath onPath
  exact ⟨pivot, inSeparator, ⟨rfl, reachesWithin_iff_residual.mpr left⟩,
    ⟨rfl, reachesWithin_iff_residual.mpr right⟩⟩

/-- With bounded disjoint-path count and strict graft thresholds, bound both projections and the
full set of endpoint pairs as in Lemma 1. -/
theorem endpoint_support_bounds : EndpointsSpec.SupportBounds := by
  intro n edge vertices mu pi graft paths row column
  classical
  obtain ⟨separator, separates, separatorBound⟩ :=
    (directed_vertex_menger vertices (residualRelation edge vertices)
      (rowVertices vertices row) (columnVertices vertices column) pi).mp (paths row column)
  -- Each separator vertex gives a rectangle of possible endpoint pairs, with factors
  -- controlled by its row ancestors and column descendants.
  let left (vertex : vertices) : Finset (Word n) :=
    (Set.toFinite (rowAncestors edge vertices row vertex.val)).toFinset.image Prod.fst
  let right (vertex : vertices) : Finset (Word n) :=
    (Set.toFinite (columnDescendants edge vertices column vertex.val)).toFinset.image Prod.snd
  have leftBound (vertex : vertices) : (left vertex).card ≤ mu - 1 := by
    have h := (graft vertex.val vertex.property).1 row
    apply Finset.card_image_le.trans
    rw [← Set.ncard_eq_toFinset_card]
    omega
  have rightBound (vertex : vertices) : (right vertex).card ≤ mu - 1 := by
    have h := (graft vertex.val vertex.property).2 column
    apply Finset.card_image_le.trans
    rw [← Set.ncard_eq_toFinset_card]
    omega
  have factor (pair : Word n × Word n)
      (present : pair ∈ endpointPairs edge vertices row column) :
      ∃ pivot ∈ separator, pair.1 ∈ left pivot ∧ pair.2 ∈ right pivot := by
    obtain ⟨pivot, hp, hl, hr⟩ := endpoint_pair_through_separator separates present
    exact ⟨pivot, hp, Finset.mem_image.mpr ⟨(pair.1, row), (Set.Finite.mem_toFinset _).2 hl, rfl⟩,
      Finset.mem_image.mpr ⟨(column, pair.2), (Set.Finite.mem_toFinset _).2 hr, rfl⟩⟩
  have leftSubset : leftSupport (endpointPairs edge vertices row column) ⊆
      separator.biUnion left := by
    intro capacity hcap
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hcap
    obtain ⟨pivot, hp, ha, _⟩ := factor pair hpair
    exact Finset.mem_biUnion.mpr ⟨pivot, hp, ha⟩
  have rightSubset : rightSupport (endpointPairs edge vertices row column) ⊆
      separator.biUnion right := by
    intro rate hrate
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp hrate
    obtain ⟨pivot, hp, _, hb⟩ := factor pair hpair
    exact Finset.mem_biUnion.mpr ⟨pivot, hp, hb⟩
  have pairSubset : endpointPairs edge vertices row column ⊆
      separator.biUnion (fun pivot ↦ left pivot ×ˢ right pivot) := by
    intro pair hpair
    obtain ⟨pivot, hp, ha, hb⟩ := factor pair hpair
    exact Finset.mem_biUnion.mpr ⟨pivot, hp, Finset.mem_product.mpr ⟨ha, hb⟩⟩
  refine ⟨(Finset.card_le_card leftSubset).trans ?_, (Finset.card_le_card rightSubset).trans ?_,
    (Finset.card_le_card pairSubset).trans ?_⟩
  · exact (Finset.card_biUnion_le_card_mul _ _ _ fun x _ ↦ leftBound x).trans
      (Nat.mul_le_mul_right _ separatorBound)
  · exact (Finset.card_biUnion_le_card_mul _ _ _ fun x _ ↦ rightBound x).trans
      (Nat.mul_le_mul_right _ separatorBound)
  · apply (Finset.card_biUnion_le_card_mul separator _ ((mu - 1) ^ 2) ?_).trans
      (Nat.mul_le_mul_right _ separatorBound)
    intro pivot _
    rw [Finset.card_product, pow_two]
    exact Nat.mul_le_mul (leftBound pivot) (rightBound pivot)

/-- A fixed row's endpoint pairs can be charged to its zero-edge walks or to the label
of the last step and the endpoints of the preceding walk. -/
theorem endpoint_row_total (transcript : Transcript n) (vertices : Set (State n))
    (theta : ℕ) (row : Word n)
    (bounded : ∀ column,
      (endpointPairs (realRecordRelation transcript) vertices row column).card ≤ theta) :
    (∑ column : Word n,
      (endpointPairs (realRecordRelation transcript) vertices row column).card) ≤
      2 ^ n + transcript.length * theta := by
  classical
  let allEndpoints := (Finset.univ : Finset (Word n)).sigma
    (endpointPairs (realRecordRelation transcript) vertices row)
  let trivialEndpoint (u : Word n) : Σ _ : Word n, Word n × Word n :=
    ⟨u, (u, row)⟩
  let addLast (label : transcript.Label) (pair : Word n × Word n) :
      Σ _ : Word n, Word n × Word n :=
    let record := transcript.get label
    ⟨pair.2 ^^^ record.shift, (pair.1, record.output.2)⟩
  let byLabel (label : transcript.Label) :=
    (endpointPairs (realRecordRelation transcript) vertices row (transcript.get label).input.1)
      |>.image (addLast label)
  let zeroEdges := Finset.univ.image trivialEndpoint
  let lastEdges := (Finset.univ : Finset transcript.Label).biUnion byLabel
  have subset : allEndpoints ⊆ zeroEdges ∪ lastEdges := by
    rintro ⟨column, u, v⟩ present
    have endpoint := mem_endpointPairs.mp (Finset.mem_sigma.mp present).2
    obtain ⟨sourceResidual, _, path⟩ := endpoint
    rcases path.cases_tail with trivial | ⟨middle, earlier, lastStep⟩
    · have hcol : column = u := congrArg Prod.fst trivial
      have hrate : v = row := congrArg Prod.snd trivial
      subst column
      subst v
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    · obtain ⟨middleResidual, _, label, capacity_eq, target_eq⟩ := lastStep
      have prior : (u, middle.2) ∈ endpointPairs (realRecordRelation transcript) vertices row
          (transcript.get label).input.1 := by
        apply mem_endpointPairs.mpr
        rw [← capacity_eq]
        exact ⟨sourceResidual, middleResidual, earlier⟩
      have hcol : column = middle.2 ^^^ (transcript.get label).shift :=
        congrArg Prod.fst target_eq
      have hrate : v = (transcript.get label).output.2 := congrArg Prod.snd target_eq
      subst column
      subst v
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨label, Finset.mem_univ _, Finset.mem_image.mpr ⟨(u, middle.2), prior, rfl⟩⟩)
  -- A zero-edge path contributes at most one pair per state of the source row.
  -- A nonempty path contributes via its last label and a pair for that label's input column.
  have zeroCount : zeroEdges.card ≤ 2 ^ n :=
    (Finset.card_image_le (s := (Finset.univ : Finset (Word n)))).trans_eq
      (Finset.card_univ.trans (word_card n))
  have lastCount : lastEdges.card ≤ transcript.length * theta := by
    have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset transcript.Label) byLabel theta
      (fun label _ ↦ Finset.card_image_le.trans (bounded (transcript.get label).input.1))
    simpa using h
  calc
    _ = allEndpoints.card := (Finset.card_sigma _ _).symm
    _ ≤ (zeroEdges ∪ lastEdges).card := Finset.card_le_card subset
    _ ≤ zeroEdges.card + lastEdges.card := Finset.card_union_le _ _
    _ ≤ 2 ^ n + transcript.length * theta := Nat.add_le_add zeroCount lastCount

@[simp] theorem transpose_record_twice (record : Record n) :
    transposeRecord (transposeRecord record) = record := by
  cases record with
  | mk input output direction => cases direction <;> rfl

private theorem record_relation_iff_record_mem {transcript : Transcript n} {a b : State n} :
    realRecordRelation transcript a b ↔ ∃ record ∈ transcript, record.edge a b :=
  (List.exists_mem_iff_get (p := fun r : Record n ↦ r.edge a b)).symm

/-- Appending one record adds exactly its edges to the real-state relation. -/
theorem realRecordRelation_append (transcript : Transcript n) (record : Record n) (a b : State n) :
    realRecordRelation (transcript ++ [record]) a b ↔
      realRecordRelation transcript a b ∨ record.edge a b := by
  simp [record_relation_iff_record_mem, or_and_right, exists_or]

private theorem transpose_record_edge {record : Record n} {a b : State n}
    (edge : record.edge a b) : (transposeRecord record).edge b.swap a.swap := by
  rcases edge with ⟨capacity_eq, rfl⟩
  refine ⟨rfl, Prod.ext ?_ capacity_eq⟩
  change a.2 = (a.2 ^^^ (record.input.2 ^^^ record.output.1)) ^^^
    (record.output.1 ^^^ record.input.2)
  rw [BitVec.xor_comm record.output.1 record.input.2, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

private theorem transpose_reachesWithin {transcript : Transcript n} {vertices : Set (State n)}
    {a b : State n} (path : ReachesWithin (realRecordRelation transcript) vertices a b) :
    ReachesWithin (realRecordRelation (transcript.map transposeRecord))
      (Prod.swap ⁻¹' vertices) b.swap a.swap := by
  have swapped_mem {state : State n} (present : state ∈ vertices) :
      state.swap ∈ Prod.swap ⁻¹' vertices := by
    simpa only [Set.mem_preimage, Prod.swap_swap] using present
  refine ⟨swapped_mem path.2.1, swapped_mem path.1, ?_⟩
  apply path.2.2.swap.lift Prod.swap
  intro source target step
  refine ⟨swapped_mem step.2.1, swapped_mem step.1, ?_⟩
  obtain ⟨record, present, edge⟩ := record_relation_iff_record_mem.mp step.2.2
  exact record_relation_iff_record_mem.mpr ⟨transposeRecord record,
    List.mem_map.mpr ⟨record, present, rfl⟩, transpose_record_edge edge⟩

theorem transpose_reachesWithin_iff {transcript : Transcript n} {vertices : Set (State n)}
    {a b : State n} :
    ReachesWithin (realRecordRelation (transcript.map transposeRecord))
      (Prod.swap ⁻¹' vertices) b.swap a.swap ↔
      ReachesWithin (realRecordRelation transcript) vertices a b := by
  constructor
  · intro h
    simpa [List.map_map, Function.comp_def, Set.preimage_preimage] using transpose_reachesWithin h
  · exact transpose_reachesWithin

/-- Reversing all record edges and swapping the state coordinates exchanges the endpoint
row and column and swaps the free coordinates in each pair. -/
theorem transposed_endpoint_pairs (transcript : Transcript n) (vertices : Set (State n))
    (row column : Word n) :
    (endpointPairs (realRecordRelation transcript) vertices row column).image Prod.swap =
      endpointPairs (realRecordRelation (transcript.map transposeRecord))
        (Prod.swap ⁻¹' vertices) column row := by
  ext pair
  constructor
  · intro present
    obtain ⟨original, originalMem, rfl⟩ := Finset.mem_image.mp present
    exact mem_endpointPairs.mpr (transpose_reachesWithin (mem_endpointPairs.mp originalMem))
  · intro present
    refine Finset.mem_image.mpr ⟨pair.swap, mem_endpointPairs.mpr ?_, Prod.swap_swap pair⟩
    exact transpose_reachesWithin_iff.mp (mem_endpointPairs.mp present)

/-- The two sums in (13), using only the per-cell bound from Lemma 1. -/
theorem endpoint_total_bounds : EndpointsSpec.TotalBounds := by
  intro n transcript vertices theta cellBound
  refine ⟨fun row ↦ endpoint_row_total transcript vertices theta row (cellBound row), ?_⟩
  intro column
  have cards (row column : Word n) :
      (endpointPairs (realRecordRelation (transcript.map transposeRecord))
        (Prod.swap ⁻¹' vertices) column row).card =
      (endpointPairs (realRecordRelation transcript) vertices row column).card := by
    rw [← transposed_endpoint_pairs transcript vertices row column,
      Finset.card_image_of_injective _ Prod.swap_injective]
  have reversed := endpoint_row_total (transcript.map transposeRecord)
    (Prod.swap ⁻¹' vertices) theta column (fun row ↦ (cards row column).trans_le
      (cellBound row column))
  simpa only [cards, List.length_map] using reversed

end JH.Graph
