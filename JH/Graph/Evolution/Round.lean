/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.RecordEvolution
public import JH.Graph.Evolution.RoundSpec

/-!
# A record-graph round

Appending a record preserves the positions of all old labels. The round tests for intersection
after inheritance and only runs the graft sequence in the disjoint case. The resulting boundary
and the add-only graph on the old residual set serve different steps of the proof.
-/

@[expose] public section

namespace JH.Graph

/-- Every label after appending a record is its new position or a lifted old label. -/
theorem appended_record_indices : RoundSpec.RecordIndices := by
  intro n transcript record
  refine ⟨?_, ?_, ?_⟩
  · intro label
    exact List.getElem_append_left label.isLt
  · change (transcript ++ [record])[transcript.length] = record
    rw [List.getElem_append_right (le_refl transcript.length)]
    simp
  · intro label
    by_cases earlier : label.val < transcript.length
    · exact Or.inr ⟨⟨label.val, earlier⟩, Fin.ext rfl⟩
    · left
      apply Fin.ext
      change label.val = transcript.length
      have limit := label.isLt
      simp only [List.length_append, List.length_singleton] at limit
      omega

/-- An intersecting inheritance ends the round. Otherwise a finite sequence of
eligible grafts yields a legal continuation. -/
theorem round_exists : RoundSpec.Existence := by
  intro n transcript record threshold initials before
  let updated := transcript ++ [record]
  let edge := recordRelation updated initials
  let inherited := before.inherit edge
  have closed : inherited.Closed edge := (Boundary.inheritance edge before).2.1
  by_cases intersects : inherited.Intersects
  · exact ⟨.intersected, intersects⟩
  obtain ⟨finish, steps, _, _, _, done⟩ :=
    Boundary.graft_termination edge (recordGraftEligible updated threshold)
      (fun _ _ _ ↦ record_eligible_residual) inherited closed intersects
  exact ⟨.continued finish, intersects, steps, done⟩

/-- A continuing round preserves the virtual starts and boundary invariants and leaves
strictly subthreshold ancestor and descendant counts on its residual graph. -/
theorem round_continuation : RoundSpec.Continuation := by
  intro n transcript record threshold initials before finish hasStarts continued
  let updated := transcript ++ [record]
  let edge := recordRelation updated initials
  obtain ⟨separate, steps, finished⟩ := continued
  obtain ⟨inheritedGrows, inheritedClosed, _⟩ := Boundary.inheritance edge before
  obtain ⟨graftGrows, finishClosed, finishSeparate⟩ := steps.invariants inheritedClosed separate
  have grows := inheritedGrows.trans graftGrows
  exact ⟨grows, fun i ↦ grows.1 (hasStarts i), fun _ h ↦ grows.residual_subset h,
    finishClosed, finishSeparate, within_threshold_of_no_graft finished⟩

end JH.Graph
