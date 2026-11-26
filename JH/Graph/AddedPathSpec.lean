/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.EvolutionSpec

/-!
# Walks using the current record

Decomposition of walks according to their uses of the new record.
-/

@[expose] public section

namespace JH.Graph

universe u v

variable {Vertex : Type u} {OldLabel : Type v}

/-- A step keeps its old record label, or is marked as an occurrence of the new record. -/
inductive AddedLabel (OldLabel : Type v) where
  | old (label : OldLabel)
  | new

/-- Tests whether an edge carries the label of the record just added. -/
def AddedLabel.isNew : AddedLabel OldLabel → Bool
  | .old _ => false
  | .new => true

/-- The labelled edge relation after adjoining one record, distinguishing its edges from every
old label. -/
@[implicit_reducible] def addedEdge (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) : AddedLabel OldLabel → Vertex → Vertex → Prop
  | .old label => oldEdge label
  | .new => newEdge

/-- Two vertices are adjacent by an edge with an old label. -/
def oldRelation (oldEdge : OldLabel → Vertex → Vertex → Prop) (a b : Vertex) : Prop :=
  ∃ label, oldEdge label a b

/-- Adjacency after adjoining the edges of the new record. -/
def addedRelation (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (a b : Vertex) : Prop :=
  oldRelation oldEdge a b ∨ newEdge a b

/-- Instantiate `Vertex` with the residual subtype to keep every step on the old residual set. -/
abbrev AddedWalk (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) := Walk (addedEdge oldEdge newEdge)

namespace AddedWalk

variable {oldEdge : OldLabel → Vertex → Vertex → Prop} {newEdge : Vertex → Vertex → Prop}

/-- Count occurrences, including repeated uses of the same new edge. -/
def newUses {source target : Vertex} (walk : AddedWalk oldEdge newEdge source target) : ℕ :=
  walk.labels.countP AddedLabel.isNew

/-- Concatenate two labelled walks at their common endpoint. -/
def append {target : Vertex} : {source middle : Vertex} →
    AddedWalk oldEdge newEdge source middle → AddedWalk oldEdge newEdge middle target →
    AddedWalk oldEdge newEdge source target
  | _, _, .nil _, after => after
  | _, _, .cons label step rest, after => .cons label step (append rest after)

end AddedWalk

/-- Sources that can reach at least one vertex of the target set. -/
def ancestorsOf (edge : Vertex → Vertex → Prop) (targets : Set Vertex) : Set Vertex :=
  {source | ∃ target ∈ targets, Reaches edge source target}

/-- Inputs of new edges whose outputs can reach a target using old edges. -/
def newInputs (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (targets : Set Vertex) : Set Vertex :=
  {x | ∃ y, newEdge x y ∧ y ∈ ancestorsOf (oldRelation oldEdge) targets}

/-- Sources with a walk to the target set that uses the new label at most once. -/
def atMostOneNewAncestors (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (targets : Set Vertex) : Set Vertex :=
  {source | ∃ target ∈ targets, ∃ walk : AddedWalk oldEdge newEdge source target, walk.newUses ≤ 1}

namespace AddedPathSpec

/-- The suffix following the final new occurrence has zero new occurrences. -/
def LastNewSplit : Prop :=
  ∀ {Vertex : Type u} {OldLabel : Type v} {oldEdge : OldLabel → Vertex → Vertex → Prop}
    {newEdge : Vertex → Vertex → Prop} {source target : Vertex}
    (walk : AddedWalk oldEdge newEdge source target), 0 < walk.newUses →
      ∃ (x y : Vertex) (before : AddedWalk oldEdge newEdge source x)
        (step : newEdge x y) (after : AddedWalk oldEdge newEdge y target),
        walk = before.append (.cons .new step after) ∧ after.newUses = 0

/-- The segment between the final two new occurrences and the final suffix both use old edges. -/
def LastTwoNewSplit : Prop :=
  ∀ {Vertex : Type u} {OldLabel : Type v} {oldEdge : OldLabel → Vertex → Vertex → Prop}
    {newEdge : Vertex → Vertex → Prop} {source target : Vertex}
    (walk : AddedWalk oldEdge newEdge source target), 1 < walk.newUses →
      ∃ (a b x y : Vertex) (before : AddedWalk oldEdge newEdge source a)
        (previousStep : newEdge a b) (between : AddedWalk oldEdge newEdge b x)
        (lastStep : newEdge x y) (after : AddedWalk oldEdge newEdge y target),
        walk = before.append
          (.cons .new previousStep (between.append (.cons .new lastStep after))) ∧
          between.newUses = 0 ∧ after.newUses = 0

/-- Old reachability at the relevant endpoints, as used by the support bounds in Lemmas 2 and 4. -/
def LastNewSegments : Prop :=
  ∀ {Vertex : Type u} {OldLabel : Type v} {oldEdge : OldLabel → Vertex → Vertex → Prop}
    {newEdge : Vertex → Vertex → Prop} {source target : Vertex}
    (walk : AddedWalk oldEdge newEdge source target), 0 < walk.newUses →
      ∃ x y, newEdge x y ∧ Reaches (oldRelation oldEdge) y target ∧
        ((walk.newUses = 1 ∧ Reaches (oldRelation oldEdge) source x) ∨
          (1 < walk.newUses ∧ ∃ a b, newEdge a b ∧ Reaches (oldRelation oldEdge) b x))

/-- The old ancestors of the targets and the old ancestors of the new inputs form two groups. -/
def AtMostOneAncestors : Prop :=
  ∀ {Vertex : Type u} {OldLabel : Type v} (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (targets : Set Vertex),
    atMostOneNewAncestors oldEdge newEdge targets =
      ancestorsOf (oldRelation oldEdge) targets ∪
        ancestorsOf (oldRelation oldEdge) (newInputs oldEdge newEdge targets)

/-- The decomposition into two ancestor sets before restriction to an ancestor row. -/
def NoReuseAncestors : Prop :=
  ∀ {Vertex : Type u} {OldLabel : Type v} (oldEdge : OldLabel → Vertex → Vertex → Prop)
    (newEdge : Vertex → Vertex → Prop) (targets : Set Vertex),
    (∀ {source target : Vertex}, target ∈ targets →
      ∀ walk : AddedWalk oldEdge newEdge source target, walk.newUses ≤ 1) →
    ancestorsOf (addedRelation oldEdge newEdge) targets =
      ancestorsOf (oldRelation oldEdge) targets ∪
        ancestorsOf (oldRelation oldEdge) (newInputs oldEdge newEdge targets)

end AddedPathSpec

end JH.Graph
