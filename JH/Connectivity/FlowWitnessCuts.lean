/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.FlowWitnessSpec

/-!
# Truncating walks at a record label

The cut depends on the access direction. A forward record changes the source row to its output
rate, and a backward record changes the target column to its input capacity. The remaining path
lies inside the original one and has no further occurrence of the selected label. This permits
the descending sweep in `extract_flow_witness`.
-/

@[expose] public section

namespace JH

universe u v

namespace Walk

variable {Vertex : Type u} {Label : Type v} {edge : Label → Vertex → Vertex → Prop}
  {source middle target : Vertex}

theorem source_mem_vertices (walk : Walk edge source target) : source ∈ walk.vertices := by
  cases walk <;> simp [vertices]

theorem source_eq_target_of_labels_nil (walk : Walk edge source target) (empty : walk.labels = []) :
    source = target := by
  cases walk with
  | nil => rfl
  | cons => simp [labels] at empty

theorem labels_append (before : Walk edge source middle) (after : Walk edge middle target) :
    (before.append after).labels = before.labels ++ after.labels := by
  induction before with
  | nil => rfl
  | cons label step rest ih => simp only [append, labels, List.cons_append, ih]

theorem vertices_subset_append_left (before : Walk edge source middle)
    (after : Walk edge middle target) : before.vertices ⊆ (before.append after).vertices := by
  induction before with
  | nil => simpa [vertices, append] using after.source_mem_vertices
  | cons label step rest ih =>
    intro v mem
    simp only [append, vertices, List.mem_cons] at mem ⊢
    exact mem.imp_right fun tailMem ↦ ih after tailMem

theorem vertices_subset_append_right (before : Walk edge source middle)
    (after : Walk edge middle target) : after.vertices ⊆ (before.append after).vertices := by
  induction before with
  | nil => exact fun _ mem ↦ mem
  | cons label step rest ih =>
    intro v mem
    exact List.mem_cons_of_mem _ (ih after mem)

/-- Cut at the first occurrence of the selected label, leaving a label-free prefix
with respect to that choice. -/
theorem first_occurrence : Graph.FlowWitnessSpec.FirstOccurrence.{u, v} := by
  intro Vertex Label edge source target walk choice
  induction walk with
  | nil vertex => simp [labels]
  | @cons source middle target label step rest ih =>
    intro present
    by_cases same : choice = label
    · subst label
      exact ⟨source, middle, .nil source, step, rest, rfl, List.not_mem_nil⟩
    · have inRest : choice ∈ rest.labels := (List.mem_cons.mp present).resolve_left same
      obtain ⟨x, y, before, chosen, after, split, absent⟩ := ih inRest
      refine ⟨x, y, .cons label step before, chosen, after,
        congrArg (Walk.cons label step) split, ?_⟩
      simpa only [labels, List.mem_cons, not_or] using And.intro same absent

/-- Cut at the last occurrence of the selected label, leaving a suffix that avoids it. -/
theorem last_occurrence : Graph.FlowWitnessSpec.LastOccurrence.{u, v} := by
  intro Vertex Label edge source target walk choice
  induction walk with
  | nil vertex => simp [labels]
  | @cons source middle target label step rest ih =>
    intro present
    by_cases inRest : choice ∈ rest.labels
    · obtain ⟨x, y, before, chosen, after, split, absent⟩ := ih inRest
      exact ⟨x, y, .cons label step before, chosen, after,
        congrArg (Walk.cons label step) split, absent⟩
    · have same : choice = label := (List.mem_cons.mp present).resolve_right inRest
      subst label
      exact ⟨source, middle, .nil source, step, rest, rfl, inRest⟩

end Walk

namespace Graph.FlowPath

variable {n : ℕ} {transcript : Transcript n} {vertices : Set (State n)}
  {path : FlowPath transcript vertices} {row column : Word n}
    {previous next : List transcript.Label}

theorem HasBoundaries.mono (valid : path.HasBoundaries row column previous)
    (enlarge : previous ⊆ next) : path.HasBoundaries row column next :=
  ⟨valid.row_eq, valid.column_eq,
    fun label origin ↦ (valid.row_from label origin).imp_left (fun h ↦ enlarge h),
    fun label origin ↦ (valid.column_from label origin).imp_left (fun h ↦ enlarge h)⟩

/-- A forward cut keeps the suffix after the last use. A backward cut keeps the prefix
before the first use. The retained vertices and labels come from the original path. -/
theorem truncate (path : FlowPath transcript vertices) (selected : transcript.Label)
    (used : selected ∈ path.walk.labels) (valid : path.HasBoundaries row column previous) :
    ∃ shortened : FlowPath transcript vertices,
      shortened.walk.vertices ⊆ path.walk.vertices ∧
      shortened.walk.labels ⊆ path.walk.labels ∧ selected ∉ shortened.walk.labels ∧
      shortened.HasBoundaries row column (previous ++ [selected]) := by
  cases direction : (transcript.get selected).direction with
  | forward =>
    obtain ⟨x, y, before, step, after, split, absent⟩ :=
      Walk.last_occurrence path.walk selected used
    refine ⟨⟨y, path.target, after, some selected, path.columnFrom⟩, ?_, ?_, absent, ?_⟩
    · change after.vertices ⊆ path.walk.vertices
      rw [split]
      intro v mem
      exact before.vertices_subset_append_right (.cons selected step after)
        (List.mem_cons_of_mem _ mem)
    · change after.labels ⊆ path.walk.labels
      rw [split, Walk.labels_append]
      intro label mem
      exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)
    · refine ⟨?_, valid.column_eq, ?_, ?_⟩
      · have rate := congrArg (fun state : State n ↦ state.2) step.2
        exact rate
      · intro label eq
        obtain rfl := Option.some.inj eq
        exact ⟨by simp, direction⟩
      · intro label eq
        obtain ⟨mem, dir⟩ := valid.column_from label eq
        exact ⟨List.mem_append_left _ mem, dir⟩
  | backward =>
    obtain ⟨x, y, before, step, after, split, absent⟩ :=
      Walk.first_occurrence path.walk selected used
    refine ⟨⟨path.source, x, before, path.rowFrom, some selected⟩, ?_, ?_, absent, ?_⟩
    · change before.vertices ⊆ path.walk.vertices
      rw [split]
      exact before.vertices_subset_append_left (.cons selected step after)
    · change before.labels ⊆ path.walk.labels
      rw [split, Walk.labels_append]
      exact fun _ mem ↦ List.mem_append_left _ mem
    · refine ⟨valid.row_eq, step.1, ?_, ?_⟩
      · intro label eq
        obtain ⟨mem, dir⟩ := valid.row_from label eq
        exact ⟨List.mem_append_left _ mem, dir⟩
      · intro label eq
        obtain rfl := Option.some.inj eq
        exact ⟨by simp, direction⟩

end Graph.FlowPath

end JH
