/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.Round
public import JH.Potential.GraftLedgerSpec
public import JH.Potential.Weights

/-!
# Payment for grafting by residual potential

A newly grafted vertex pays one unit out of the point potential on its line. The differences in
boundary membership for successive grafts are disjoint, so these payments add. For other
translated modes, it suffices that deleting vertices decreases potential. Backward payment uses
reversed edges and swapped state coordinates.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ} {initials : Finset (State n)}

@[simp] theorem mem_graftedOnLine {old new : Set (Vertex initials)}
    {line : Word n → State n} {free : Word n} :
    free ∈ graftedOnLine old new line ↔ Sum.inl (line free) ∈ new ∧ Sum.inl (line free) ∉ old := by
  simp [graftedOnLine]

@[simp] theorem graftedOnLine_self (side : Set (Vertex initials)) (line : Word n → State n) :
    graftedOnLine side side line = ∅ := by
  ext free
  simp

private theorem graftedOnLine_card_add {old middle new : Set (Vertex initials)}
    (first : old ⊆ middle) (second : middle ⊆ new) (line : Word n → State n) :
    (graftedOnLine old new line).card =
      (graftedOnLine old middle line).card + (graftedOnLine middle new line).card := by
  classical
  -- Assign each newly admitted point to the first transfer that added it.
  have classify : graftedOnLine old new line =
      graftedOnLine old middle line ∪ graftedOnLine middle new line := by
    ext free
    simp only [Finset.mem_union, mem_graftedOnLine]
    constructor
    · rintro ⟨inNew, notOld⟩
      by_cases inMiddle : Sum.inl (line free) ∈ middle
      · exact Or.inl ⟨inMiddle, notOld⟩
      · exact Or.inr ⟨inNew, inMiddle⟩
    · rintro (⟨inMiddle, notOld⟩ | ⟨inNew, notMiddle⟩)
      · exact ⟨second inMiddle, notOld⟩
      · exact ⟨inNew, fun inOld ↦ notMiddle (first inOld)⟩
  have disjoint : Disjoint (graftedOnLine old middle line) (graftedOnLine middle new line) := by
    refine Finset.disjoint_left.mpr fun free left right ↦ ?_
    exact (mem_graftedOnLine.mp right).2 (mem_graftedOnLine.mp left).1
  rw [classify, Finset.card_union_of_disjoint disjoint]

private theorem grows_graft {V : Type*} (sides : Boundary V) (edge : V → V → Prop)
    (direction : Direction) (root : V) : sides.GrowsTo (sides.graft edge direction root) := by
  cases direction with
  | forward => exact ⟨fun _ h ↦ Or.inl h, fun _ h ↦ h⟩
  | backward => exact ⟨fun _ h ↦ h, fun _ h ↦ Or.inl h⟩

theorem GraftSequence.grows {V : Type*} {edge : V → V → Prop}
    {eligible : Boundary V → Direction → V → Prop} {start finish : Boundary V}
    (steps : GraftSequence edge eligible start finish) : start.GrowsTo finish := by
  induction steps with
  | nil sides => exact sides.grows_refl
  | @cons before _ direction root _ _ ih => exact (grows_graft before edge direction root).trans ih

private theorem realResidual_mono {before after : Boundary (Vertex initials)}
    (grows : before.GrowsTo after) : after.realResidual ⊆ before.realResidual :=
  fun _ h ↦ grows.residual_subset h

private theorem real_path_of_real_source (transcript : Transcript n)
    (sides : Boundary (Vertex initials)) {source : State n} {vertex : Vertex initials}
    (path : Reaches (inducedEdge (recordRelation transcript initials) sides.residual)
      (.inl source) vertex) :
    ∃ target : State n, vertex = .inl target ∧
      Reaches (inducedEdge (realRecordRelation transcript) sides.realResidual) source target := by
  induction path with
  | refl => exact ⟨source, rfl, .refl⟩
  | @tail before after _ step ih =>
    obtain ⟨middle, rfl, toMiddle⟩ := ih
    cases after with
    | inl target => exact ⟨target, rfl, toMiddle.tail ⟨step.1, step.2.1, step.2.2⟩⟩
    | inr initial =>
      obtain ⟨_, impossible⟩ := step.2.2
      exact False.elim impossible

private theorem real_reachesWithin {transcript : Transcript n}
    {sides : Boundary (Vertex initials)} {a b : State n}
    (path : ReachesWithin (recordRelation transcript initials) sides.residual (.inl a) (.inl b)) :
    ReachesWithin (realRecordRelation transcript) sides.realResidual a b := by
  obtain ⟨target, equal, toTarget⟩ := real_path_of_real_source transcript sides path.2.2
  cases equal
  exact ⟨path.1, path.2.1, toTarget⟩

private theorem reachesWithin_transpose {edge : State n → State n → Prop}
    {vertices : Set (State n)} {a b : State n} (path : ReachesWithin edge vertices a b) :
    ReachesWithin (transposeStateEdge edge) (Prod.swap ⁻¹' vertices) b.swap a.swap := by
  have swapped_mem {state : State n} (present : state ∈ vertices) :
      state.swap ∈ Prod.swap ⁻¹' vertices := by
    simpa only [Set.mem_preimage, Prod.swap_swap] using present
  refine ⟨swapped_mem path.2.1, swapped_mem path.1, ?_⟩
  apply path.2.2.swap.lift Prod.swap
  intro source target step
  exact ⟨swapped_mem step.2.1, swapped_mem step.1, by
    simpa only [transposeStateEdge, Prod.swap_swap] using step.2.2⟩

private theorem descendants_le_transposed_ancestors (edge : State n → State n → Prop)
    (vertices : Set (State n)) (column : Word n) (root : State n) :
    (columnDescendants edge vertices column root).ncard ≤
      (rowAncestors (transposeStateEdge edge) (Prod.swap ⁻¹' vertices) column root.swap).ncard := by
  refine Set.ncard_le_ncard_of_injOn Prod.swap ?_ Prod.swap_injective.injOn
  rintro target ⟨inColumn, path⟩
  exact ⟨inColumn, reachesWithin_transpose path⟩

private theorem pointColumnPotential_vertices_mono {edge : State n → State n → Prop}
    {small large : Set (State n)} {mu d : ℕ} {column : Word n} (subset : small ⊆ large) :
    pointColumnPotential edge small mu d column ≤ pointColumnPotential edge large mu d column := by
  simpa using deletion_pays_column edge large small mu d column ∅ subset
    (fun rate absent ↦ (Finset.notMem_empty rate absent).elim)

private theorem translatedPotential_vertices_mono {edge : State n → State n → Prop}
    {small large : Set (State n)} {mu d : ℕ} {column : Word n} {mode : Finset (Word n)}
    (subset : small ⊆ large) :
    translatedPotential edge small mu d column mode ≤
      translatedPotential edge large mu d column mode := by
  unfold translatedPotential
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro offset _
  apply forward_weight_mono subset _ (fun _ _ h ↦ h)
  rintro state ⟨present, rest⟩
  exact ⟨subset present, rest⟩

private theorem reachesWithin_induced_iff {edge : State n → State n → Prop}
    {vertices : Set (State n)} {a b : State n} :
    ReachesWithin (inducedEdge edge vertices) vertices a b ↔ ReachesWithin edge vertices a b := by
  constructor
  · exact reachesWithin_mono (fun _ h ↦ h) (fun _ _ step ↦ step.2.2)
  · rintro ⟨start, finish, path⟩
    exact ⟨start, finish, Relation.ReflTransGen.mono (r := inducedEdge edge vertices)
      (fun _ _ step ↦ ⟨step.1, step.2.1, step⟩) a b path⟩

private theorem forwardWeight_induced (edge : State n → State n → Prop) (vertices : Set (State n))
    (mu d : ℕ) (targets : Set (State n)) :
    forwardWeight (inducedEdge edge vertices) vertices mu d targets =
      forwardWeight edge vertices mu d targets := by
  have ancestors (row : Word n) :
      rowAncestorsTo (inducedEdge edge vertices) vertices row targets =
        rowAncestorsTo edge vertices row targets := by
    ext state
    simp only [rowAncestorsTo, Set.mem_ofPred_eq, reachesWithin_induced_iff]
  simp only [forwardWeight, normalizedRowWeight, ancestors]

theorem pointColumnPotential_induced (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n) :
    pointColumnPotential (inducedEdge edge vertices) vertices mu d column =
      pointColumnPotential edge vertices mu d column := by
  simp only [pointColumnPotential, forwardWeight_induced]

theorem translatedPotential_induced (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n) (mode : Finset (Word n)) :
    translatedPotential (inducedEdge edge vertices) vertices mu d column mode =
      translatedPotential edge vertices mu d column mode := by
  simp only [translatedPotential, forwardWeight_induced]

theorem transpose_inducedEdge (edge : State n → State n → Prop) (vertices : Set (State n)) :
    transposeStateEdge (inducedEdge edge vertices) =
      inducedEdge (transposeStateEdge edge) (Prod.swap ⁻¹' vertices) := by
  funext source target
  apply propext
  change (target.swap ∈ vertices ∧ source.swap ∈ vertices ∧ edge target.swap source.swap) ↔
    (source.swap ∈ vertices ∧ target.swap ∈ vertices ∧ edge target.swap source.swap)
  exact and_left_comm

theorem backwardPointRowPotential_induced (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (row : Word n) :
    backwardPointRowPotential (inducedEdge edge vertices) vertices mu d row =
      backwardPointRowPotential edge vertices mu d row := by
  unfold backwardPointRowPotential
  rw [transpose_inducedEdge, pointColumnPotential_induced]

theorem backwardTranslatedPotential_induced (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (row : Word n) (mode : Finset (Word n)) :
    backwardTranslatedPotential (inducedEdge edge vertices) vertices mu d row mode =
      backwardTranslatedPotential edge vertices mu d row mode := by
  unfold backwardTranslatedPotential
  rw [transpose_inducedEdge, translatedPotential_induced]

private theorem transpose_record_step {record : Record n} {source target : State n}
    (step : record.edge source target) : (transposeRecord record).edge target.swap source.swap := by
  rcases step with ⟨sameColumn, rfl⟩
  refine ⟨rfl, Prod.ext ?_ sameColumn⟩
  change source.2 = (source.2 ^^^ (record.input.2 ^^^ record.output.1)) ^^^
    (record.output.1 ^^^ record.input.2)
  rw [BitVec.xor_comm record.output.1 record.input.2, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

/-- Reverse every edge and exchange the state coordinates by transposing each
record at the same position in the transcript. -/
theorem transposeStateEdge_realRecordRelation (transcript : Transcript n) :
    transposeStateEdge (realRecordRelation transcript) =
      realRecordRelation (transcript.map transposeRecord) := by
  funext source target
  apply propext
  constructor
  · rintro ⟨label, step⟩
    let mapped : Transcript.Label (transcript.map transposeRecord) :=
      ⟨label.val, by
        rw [List.length_map]
        exact label.isLt⟩
    refine ⟨mapped, ?_⟩
    have reversed := transpose_record_step
      (show (transcript.get label).edge target.swap source.swap from step)
    simpa only [Transcript.realEdge, List.get_eq_getElem, List.getElem_map, mapped, Prod.swap_swap]
      using reversed
  · rintro ⟨label, step⟩
    let original : transcript.Label := ⟨label.val, by simpa using label.isLt⟩
    have mappedStep : (transposeRecord (transcript.get original)).edge source target := by
      simpa only [Transcript.realEdge, List.get_eq_getElem, List.getElem_map, original] using step
    exact ⟨original, by simpa only [Transcript.realEdge, transpose_record_twice]
      using transpose_record_step mappedStep⟩

theorem backward_singleton_mode_is_point_row (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (row : Word n) (degree : 0 < d) :
    backwardTranslatedPotential edge vertices mu d row {0} =
      backwardPointRowPotential edge vertices mu d row :=
  singleton_mode_is_point_column _ _ _ _ _ degree

private theorem forward_graft_payment (transcript : Transcript n) (mu d : ℕ)
    (before : Boundary (Vertex initials)) (direction : Direction) (root : Vertex initials)
    (positiveMu : 0 < mu) (ready : recordGraftEligible transcript mu before direction root)
    (column : Word n) :
    let edge := recordRelation transcript initials
    let after := before.graft edge direction root
    pointColumnPotential (realRecordRelation transcript) after.realResidual mu d column +
        forwardGraftCount before after column ≤
      pointColumnPotential (realRecordRelation transcript) before.realResidual mu d column := by
  dsimp only
  have subset := realResidual_mono
      (grows_graft before (recordRelation transcript initials) direction root)
  cases direction with
  | backward =>
    have noPayment : forwardGraftCount before
        (before.graft (recordRelation transcript initials) .backward root) column = 0 := by
      simp [forwardGraftCount, Boundary.graft]
    rw [noPayment, Nat.cast_zero, add_zero]
    exact pointColumnPotential_vertices_mono subset
  | forward =>
    cases root with
    | inr initial => exact False.elim ready
    | inl root =>
      obtain ⟨_, row, enough⟩ := ready
      unfold forwardGraftCount
      refine deletion_pays_column _ _ _ _ _ _ _ subset fun rate paid ↦ ?_
      have newly := mem_graftedOnLine.mp paid
      have path : ReachesWithin (recordRelation transcript initials) before.residual
          (.inl root) (.inl (column, rate)) := Or.resolve_left newly.1 newly.2
      have realPath := real_reachesWithin path
      refine ⟨realPath.2.1, fun present ↦ present (Or.inl newly.1), ?_⟩
      exact graft_point_weight (realRecordRelation transcript) before.realResidual mu d
        root (column, rate) row positiveMu enough realPath

private theorem backward_graft_payment (transcript : Transcript n) (mu d : ℕ)
    (before : Boundary (Vertex initials)) (direction : Direction) (root : Vertex initials)
    (positiveMu : 0 < mu) (ready : recordGraftEligible transcript mu before direction root)
    (row : Word n) :
    let edge := recordRelation transcript initials
    let after := before.graft edge direction root
    backwardPointRowPotential (realRecordRelation transcript) after.realResidual mu d row +
        backwardGraftCount before after row ≤
      backwardPointRowPotential (realRecordRelation transcript) before.realResidual mu d row := by
  dsimp only
  have subset := Set.preimage_mono (f := Prod.swap)
    (realResidual_mono (grows_graft before (recordRelation transcript initials) direction root))
  cases direction with
  | forward =>
    have noPayment : backwardGraftCount before
        (before.graft (recordRelation transcript initials) .forward root) row = 0 := by
      simp [backwardGraftCount, Boundary.graft]
    rw [noPayment, Nat.cast_zero, add_zero]
    exact pointColumnPotential_vertices_mono subset
  | backward =>
    cases root with
    | inr initial => exact False.elim ready
    | inl root =>
      obtain ⟨_, column, enough⟩ := ready
      unfold backwardPointRowPotential backwardGraftCount
      refine deletion_pays_column _ _ _ _ _ _ _ subset fun capacity paid ↦ ?_
      have newly := mem_graftedOnLine.mp paid
      have path : ReachesWithin (recordRelation transcript initials) before.residual
          (.inl (capacity, row)) (.inl root) := Or.resolve_left newly.1 newly.2
      have realPath := real_reachesWithin path
      refine ⟨realPath.1, fun present ↦ present (Or.inr newly.1), ?_⟩
      -- An eligible backward root has enough descendants in one column. These become
      -- row ancestors for the forward payment argument after transposition.
      have enoughTransposed := enough.trans
        (descendants_le_transposed_ancestors (realRecordRelation transcript)
          before.realResidual column root)
      exact graft_point_weight (transposeStateEdge (realRecordRelation transcript))
        (Prod.swap ⁻¹' before.realResidual) mu d root.swap (row, capacity) column
        positiveMu enoughTransposed (reachesWithin_transpose realPath)

private theorem graftSequence_payment (transcript : Transcript n) (mu d : ℕ)
    (positiveMu : 0 < mu) {start finish : Boundary (Vertex initials)}
    (steps : GraftSequence (recordRelation transcript initials)
      (recordGraftEligible transcript mu) start finish) :
    (∀ column, pointColumnPotential (realRecordRelation transcript)
      finish.realResidual mu d column +
      forwardGraftCount start finish column ≤
        pointColumnPotential (realRecordRelation transcript) start.realResidual mu d column) ∧
    (∀ row, backwardPointRowPotential (realRecordRelation transcript) finish.realResidual mu d row +
      backwardGraftCount start finish row ≤
        backwardPointRowPotential (realRecordRelation transcript) start.realResidual mu d row) := by
  induction steps with
  | nil sides => constructor <;> intro line <;> simp [forwardGraftCount, backwardGraftCount]
  | @cons before finish direction root ready rest ih =>
    let after := before.graft (recordRelation transcript initials) direction root
    have first := grows_graft before (recordRelation transcript initials) direction root
    have second := rest.grows
    constructor
    · intro column
      have split : forwardGraftCount before finish column =
          forwardGraftCount before after column + forwardGraftCount after finish column :=
        graftedOnLine_card_add first.1 second.1 (fun rate ↦ (column, rate))
      rw [split, Nat.cast_add]
      simpa only [add_assoc, add_left_comm, add_comm] using (add_le_add_left (ih.1 column)
        (forwardGraftCount before after column : ℝ)).trans
          (forward_graft_payment transcript mu d before direction root positiveMu ready column)
    · intro row
      have split : backwardGraftCount before finish row =
          backwardGraftCount before after row + backwardGraftCount after finish row :=
        graftedOnLine_card_add first.2 second.2 (fun column ↦ (column, row))
      rw [split, Nat.cast_add]
      simpa only [add_assoc, add_left_comm, add_comm] using (add_le_add_left (ih.2 row)
        (backwardGraftCount before after row : ℝ)).trans
          (backward_graft_payment transcript mu d before direction root positiveMu ready row)

/-- For a disjoint round, the final point potential plus the new graft count is
bounded by the potential in the add-only graph before any deletion. -/
theorem round_graft_payment : GraftLedgerSpec.RoundPayment := by
  intro n transcript record mu d initials before finish positiveMu continued
  dsimp only
  let updated := transcript ++ [record]
  let edge := recordRelation updated initials
  let inherited := before.inherit edge
  obtain ⟨_, steps, _⟩ := continued
  -- The graft count starts after inheritance. Compare its starting potential with
  -- the larger add-only graph to absorb deletions made by inheritance.
  have subset : inherited.realResidual ⊆ before.realResidual :=
    realResidual_mono (Boundary.inheritance edge before).1
  obtain ⟨forwardPaid, backwardPaid⟩ := graftSequence_payment updated mu d positiveMu steps
  constructor
  · intro column
    apply (forwardPaid column).trans
    rw [argumentEdge, pointColumnPotential_induced]
    exact pointColumnPotential_vertices_mono subset
  · intro row
    apply (backwardPaid row).trans
    rw [argumentEdge, backwardPointRowPotential_induced]
    exact pointColumnPotential_vertices_mono (Set.preimage_mono subset)

/-- Inheritance and grafting only delete residual vertices of the add-only graph.
For each translated mode, the corresponding potential can only decrease. -/
theorem round_mode_decrease_after_deletion : GraftLedgerSpec.RoundModeDecrease := by
  intro n transcript record mu d initials before finish continued
  dsimp only
  let updated := transcript ++ [record]
  let edge := recordRelation updated initials
  obtain ⟨_, steps, _⟩ := continued
  have subset : finish.realResidual ⊆ before.realResidual :=
    realResidual_mono ((Boundary.inheritance edge before).1.trans steps.grows)
  constructor
  · intro column mode
    rw [argumentEdge, translatedPotential_induced]
    exact translatedPotential_vertices_mono subset
  · intro row mode
    rw [argumentEdge, backwardTranslatedPotential_induced]
    exact translatedPotential_vertices_mono (Set.preimage_mono subset)

end JH.Graph
