/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.AddedPathSpec
public import JH.Graph.Evolution

/-!
# Walks using the current record

Walks retain record labels, so two uses of the same new record are detected even when some
edges also have an older label. Cutting at the final new occurrence, or the final two,
identifies the stretches of old reachability needed by the shift tests and by the ancestor-set
decomposition.
-/

@[expose] public section

namespace JH.Graph

universe u v

variable {Vertex : Type u} {OldLabel : Type v}
variable {oldEdge : OldLabel → Vertex → Vertex → Prop} {newEdge : Vertex → Vertex → Prop}

namespace AddedWalk

@[simp] theorem newUses_nil (vertex : Vertex) :
    newUses (.nil vertex : AddedWalk oldEdge newEdge vertex vertex) = 0 := rfl

@[simp] theorem newUses_old {source middle target : Vertex} {label : OldLabel}
    (step : oldEdge label source middle) (rest : AddedWalk oldEdge newEdge middle target) :
    newUses (.cons (.old label) step rest) = rest.newUses := by
  simp [newUses, Walk.labels, AddedLabel.isNew]

@[simp] theorem newUses_new {source middle target : Vertex} (step : newEdge source middle)
    (rest : AddedWalk oldEdge newEdge middle target) :
    newUses (.cons .new step rest) = rest.newUses + 1 := by
  simp [newUses, Walk.labels, List.countP_cons, AddedLabel.isNew]

@[simp] theorem newUses_append {source middle target : Vertex}
    (before : AddedWalk oldEdge newEdge source middle)
      (after : AddedWalk oldEdge newEdge middle target) :
    (before.append after).newUses = before.newUses + after.newUses := by
  induction before with
  | nil vertex => simp [append]
  | cons label step rest ih =>
      cases label with
      | old label => simpa [append] using ih after
      | new =>
          simp only [append, newUses_new, ih]
          omega

theorem append_assoc {a b c d : Vertex} (first : AddedWalk oldEdge newEdge a b)
    (second : AddedWalk oldEdge newEdge b c) (third : AddedWalk oldEdge newEdge c d) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => rfl
  | cons label step rest ih => exact congrArg (Walk.cons label step) (ih second)

/-- A zero count gives an old path with the same endpoints. -/
theorem old_reaches {source target : Vertex} (walk : AddedWalk oldEdge newEdge source target)
    (zero : walk.newUses = 0) : Reaches (oldRelation oldEdge) source target := by
  induction walk with
  | nil => exact .refl
  | cons label step _ ih =>
      cases label with
      | old label =>
          exact (ih (by simpa only [newUses_old] using zero)).head ⟨label, step⟩
      | new => simp at zero

theorem exists_of_old_reaches (newEdge : Vertex → Vertex → Prop) {source target : Vertex}
    (path : Reaches (oldRelation oldEdge) source target) :
    ∃ walk : AddedWalk oldEdge newEdge source target, walk.newUses = 0 := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _, rfl⟩
  | head step _ ih =>
      obtain ⟨label, step⟩ := step
      obtain ⟨rest, zero⟩ := ih
      exact ⟨.cons (.old label) step rest, by simpa only [newUses_old] using zero⟩

end AddedWalk

theorem added_walk_iff_reaches (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (source target : Vertex) :
    Nonempty (AddedWalk oldEdge newEdge source target) ↔
      Reaches (addedRelation oldEdge newEdge) source target := by
  rw [walk_iff_reaches (addedEdge oldEdge newEdge) source target]
  have relation_eq : (fun a b ↦ ∃ label, addedEdge oldEdge newEdge label a b) =
      addedRelation oldEdge newEdge := by
    funext a b
    apply propext
    constructor
    · rintro ⟨label, step⟩
      cases label with
      | old label => exact Or.inl ⟨label, step⟩
      | new => exact Or.inr step
    · rintro (⟨label, step⟩ | step)
      · exact ⟨.old label, step⟩
      · exact ⟨.new, step⟩
  rw [relation_eq]

/-- The suffix following the final new occurrence has zero new occurrences. -/
theorem last_new_split : AddedPathSpec.LastNewSplit.{u, v} := by
  intro Vertex OldLabel oldEdge newEdge source target walk
  induction walk with
  | nil vertex => simp
  | @cons source middle target label step rest ih =>
      intro positive
      by_cases restOld : AddedWalk.newUses rest = 0
      · cases label with
        | old label => simp [restOld] at positive
        | new => exact ⟨source, middle, .nil source, step, rest, rfl, restOld⟩
      · obtain ⟨x, y, before, lastStep, after, split, afterOld⟩ := ih (Nat.pos_of_ne_zero restOld)
        exact ⟨x, y, .cons label step before, lastStep, after,
          congrArg (Walk.cons label step) split, afterOld⟩

/-- The segment between the final two new occurrences and the final suffix both use old edges.
-/
theorem last_two_new_split : AddedPathSpec.LastTwoNewSplit.{u, v} := by
  intro Vertex OldLabel oldEdge newEdge source target walk repeated
  obtain ⟨x, y, before, step, after, split, afterOld⟩ := last_new_split walk (by omega)
  have count : walk.newUses = before.newUses + 1 := by
    rw [split]
    simp [afterOld]
  obtain ⟨a, b, earlier, previousStep, between, splitBefore, betweenOld⟩ :=
    last_new_split before (by omega)
  refine ⟨a, b, x, y, earlier, previousStep, between, step, after, ?_, betweenOld, afterOld⟩
  rw [split, splitBefore, AddedWalk.append_assoc]
  rfl

/-- Recover the old suffix after the final new step. The old stretch before this step
starts at the source if the new label occurs once and at the preceding new output otherwise. -/
theorem last_new_segments : AddedPathSpec.LastNewSegments.{u, v} := by
  intro Vertex OldLabel oldEdge newEdge source target walk positive
  by_cases once : walk.newUses = 1
  · obtain ⟨x, y, before, step, after, split, afterOld⟩ := last_new_split walk positive
    have count : walk.newUses = before.newUses + 1 := by
      rw [split]
      simp [afterOld]
    exact ⟨x, y, step, after.old_reaches afterOld, Or.inl ⟨once, before.old_reaches (by omega)⟩⟩
  · have repeated : 1 < walk.newUses := by omega
    obtain ⟨a, b, x, y, _, earlier, between, step, after, _, betweenOld, afterOld⟩ :=
      last_two_new_split walk repeated
    exact ⟨x, y, step, after.old_reaches afterOld,
      Or.inr ⟨repeated, a, b, earlier, between.old_reaches betweenOld⟩⟩

/-- For walks with at most one new step, split the ancestors into old ancestors of
the original targets and old ancestors of the eligible new inputs. -/
theorem at_most_one_new_ancestors : AddedPathSpec.AtMostOneAncestors.{u, v} := by
  intro Vertex OldLabel oldEdge newEdge targets
  ext source
  constructor
  · rintro ⟨target, inTargets, walk, limit⟩
    by_cases zero : walk.newUses = 0
    · exact Or.inl ⟨target, inTargets, walk.old_reaches zero⟩
    obtain ⟨x, y, step, after, onceOrRepeated⟩ := last_new_segments walk (Nat.pos_of_ne_zero zero)
    rcases onceOrRepeated with ⟨_, before⟩ | ⟨repeated, _⟩
    · exact Or.inr ⟨x, ⟨y, step, target, inTargets, after⟩, before⟩
    · omega
  · rintro (⟨target, inTargets, path⟩ | ⟨x, ⟨y, step, target, inTargets, after⟩, before⟩)
    · obtain ⟨walk, zero⟩ := AddedWalk.exists_of_old_reaches newEdge path
      exact ⟨target, inTargets, walk, by simp [zero]⟩
    · obtain ⟨start, startOld⟩ := AddedWalk.exists_of_old_reaches newEdge before
      obtain ⟨finish, finishOld⟩ := AddedWalk.exists_of_old_reaches newEdge after
      exact ⟨target, inTargets,
        start.append (.cons .new step finish), by simp [startOld, finishOld]⟩

/-- For these targets, a bound on new-label occurrences in every walk lifts the
at-most-one ancestor identity to ordinary reachability in the enlarged graph. -/
theorem no_reuse_ancestors : AddedPathSpec.NoReuseAncestors.{u, v} := by
  intro Vertex OldLabel oldEdge newEdge targets noReuse
  trans atMostOneNewAncestors oldEdge newEdge targets
  · ext source
    constructor
    · rintro ⟨target, inTargets, path⟩
      obtain ⟨walk⟩ := (added_walk_iff_reaches oldEdge newEdge source target).mpr path
      exact ⟨target, inTargets, walk, noReuse inTargets walk⟩
    · rintro ⟨target, inTargets, walk, _⟩
      exact ⟨target, inTargets, (added_walk_iff_reaches oldEdge newEdge source target).mp ⟨walk⟩⟩
  · exact at_most_one_new_ancestors oldEdge newEdge targets

end JH.Graph
