/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution
public import JH.Graph.Evolution.RecordEvolutionSpec

/-!
# Graft thresholds in the record graph

The initial forward boundary consists of virtual starts and the backward boundary consists of
real vertices in the target columns. The generic graft termination argument gives the strict
row-ancestor and column-descendant bounds of equation (7) on the remaining real vertices.
-/

@[expose] public section

namespace JH.Graph

/-- An eligible root lies in the real residual graph. -/
theorem record_eligible_residual {n threshold : ℕ} {transcript : Transcript n}
    {initials : Finset (State n)} {sides : Boundary (Vertex initials)} {direction : Direction}
    {root : Vertex initials}
      (eligible : recordGraftEligible transcript threshold sides direction root) :
    root ∈ sides.residual := by
  cases root with
  | inl _ => exact eligible.1
  | inr _ => exact False.elim eligible

/-- A residual row-ancestor or column-descendant count at least the threshold would
make its root eligible to graft in the corresponding direction. -/
theorem within_threshold_of_no_graft {n threshold : ℕ} {transcript : Transcript n}
    {initials : Finset (State n)} {sides : Boundary (Vertex initials)}
    (finished : ∀ direction root, ¬ recordGraftEligible transcript threshold sides direction root) :
    sides.WithinGraftThreshold transcript threshold := by
  intro root residual
  -- Here equality with the threshold already triggers eligibility.
  constructor
  · intro row
    exact lt_of_not_ge fun atLeast ↦ finished .forward (.inl root) ⟨residual, row, atLeast⟩
  · intro column
    exact lt_of_not_ge fun atLeast ↦ finished .backward (.inl root) ⟨residual, column, atLeast⟩

/-- In the empty transcript the initial sides are closed and disjoint and contain all virtual
starts on the forward side. -/
theorem initial_boundary_invariants : RecordEvolutionSpec.InitialBoundary := by
  intro n initials targetColumns
  refine ⟨fun i ↦ ⟨i, rfl⟩, ?_, ⟨?_, ?_⟩⟩
  · rintro ⟨_, ⟨i, rfl⟩, ⟨state, equal, _⟩⟩
    cases equal
  · rintro _ _ _ ⟨label, _⟩
    exact Fin.elim0 label
  · rintro _ _ _ ⟨label, _⟩
    exact Fin.elim0 label

/-- Finish all eligible grafts and obtain both strict residual bounds of equation (7). -/
theorem record_graft_thresholds : RecordEvolutionSpec.GraftThresholds := by
  intro n transcript initials threshold start hasStarts closed separate
  obtain ⟨finish, steps, grows, finishClosed, finishSeparate, finished⟩ :=
    Boundary.graft_termination (recordRelation transcript initials)
      (recordGraftEligible transcript threshold) (fun _ _ _ ↦ record_eligible_residual)
      start closed separate
  exact ⟨finish, steps, grows, fun i ↦ grows.1 (hasStarts i), finishClosed, finishSeparate,
    within_threshold_of_no_graft finished⟩

end JH.Graph
