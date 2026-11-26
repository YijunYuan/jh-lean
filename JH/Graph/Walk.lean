/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import Mathlib.Logic.Relation

/-!
# Labelled walks

Labelled walks and their traversal order.
-/

@[expose] public section

namespace JH

universe u v w

/-- A finite directed walk stores each step's label, including multiple occurrences of a label. -/
inductive Walk {Vertex : Type u} {Label : Type v} (edge : Label → Vertex → Vertex → Prop) :
    Vertex → Vertex → Type (max u v) where
  | nil (vertex : Vertex) : Walk edge vertex vertex
  | cons {source middle target : Vertex} (label : Label) (step : edge label source middle)
      (rest : Walk edge middle target) : Walk edge source target

namespace Walk

variable {Vertex : Type u} {Label : Type v} {edge : Label → Vertex → Vertex → Prop}

/-- Labels are listed in traversal order. -/
def labels : {source target : Vertex} → Walk edge source target → List Label
  | _, _, .nil _ => []
  | _, _, .cons label _ rest => label :: rest.labels

/-- The vertex list includes both endpoints. A zero-edge walk has one vertex. -/
def vertices : {source target : Vertex} → Walk edge source target → List Vertex
  | _, _, .nil vertex => [vertex]
  | source, _, .cons _ _ rest => source :: rest.vertices

/-- Map the vertices of a walk while preserving its sequence of record labels. -/
def map {Other : Type w} {otherEdge : Label → Other → Other → Prop} (f : Vertex → Other)
    (mapEdge : ∀ ⦃label a b⦄, edge label a b → otherEdge label (f a) (f b)) :
    {source target : Vertex} → Walk edge source target → Walk otherEdge (f source) (f target)
  | _, _, .nil vertex => .nil (f vertex)
  | _, _, .cons label step rest => .cons label (mapEdge step) (rest.map f mapEdge)

end Walk

end JH
