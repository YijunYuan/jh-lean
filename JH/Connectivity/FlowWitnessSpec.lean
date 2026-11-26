/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.ShiftTestSpec
public import JH.Parameters.CertificateSpec

/-!
# Row-to-column path packing witnesses

Backward selection of record labels from vertex-disjoint residual paths.
-/

@[expose] public section

namespace JH.Walk

universe u v

variable {Vertex : Type u} {Label : Type v} {edge : Label → Vertex → Vertex → Prop}

/-- Concatenate two labelled walks at their common vertex. -/
def append {target : Vertex} : {source middle : Vertex} →
    Walk edge source middle → Walk edge middle target → Walk edge source target
  | _, _, .nil _, after => after
  | _, _, .cons label step rest, after => .cons label step (rest.append after)

end JH.Walk

namespace JH.Graph

universe u v

variable {n : ℕ}

/-- The boundary is either the original row or the output rate of a selected record. -/
def flowRow (transcript : Transcript n) (original : Word n) : Option transcript.Label → Word n
  | none => original
  | some label => (transcript.get label).output.2

/-- The boundary is either the original column or the input capacity of a selected record. -/
def flowColumn (transcript : Transcript n) (original : Word n) : Option transcript.Label → Word n
  | none => original
  | some label => (transcript.get label).input.1

/-- A residual path and the origins of its two boundary coordinates. -/
structure FlowPath (transcript : Transcript n) (vertices : Set (State n)) where
  /-- The residual source vertex. -/
  source : vertices
  /-- The residual target vertex. -/
  target : vertices
  /-- A labelled walk between the two vertices. -/
  walk : Walk (residualRecordEdge transcript vertices) source target
  /-- The selected record that supplied the row, if any. -/
  rowFrom : Option transcript.Label
  /-- The selected record that supplied the column, if any. -/
  columnFrom : Option transcript.Label

/-- The path's row and column come from the original endpoints or from previously selected
records. -/
structure FlowPath.HasBoundaries {transcript : Transcript n} {vertices : Set (State n)}
    (path : FlowPath transcript vertices) (row column : Word n) (previous : List transcript.Label) :
    Prop where
  /-- The source rate agrees with the encoded row. -/
  row_eq : path.source.val.2 = flowRow transcript row path.rowFrom
  /-- The target capacity agrees with the encoded column. -/
  column_eq : path.target.val.1 = flowColumn transcript column path.columnFrom
  /-- A record supplying the row is a previously selected forward query. -/
  row_from : ∀ label, path.rowFrom = some label →
    label ∈ previous ∧ (transcript.get label).direction = .forward
  /-- A record supplying the column is a previously selected inverse query. -/
  column_from : ∀ label, path.columnFrom = some label →
    label ∈ previous ∧ (transcript.get label).direction = .backward

/-- The selected record and a path which used it at that selection. -/
structure FlowTest (transcript : Transcript n) (vertices : Set (State n)) where
  /-- The label selected in this test. -/
  label : transcript.Label
  /-- The residual path at the time of selection. -/
  path : FlowPath transcript vertices

/-- The test has the prescribed boundary origins and its walk uses the selected label under the
reverse sweep. -/
structure FlowTest.Valid {transcript : Transcript n} {vertices : Set (State n)}
    (test : FlowTest transcript vertices) (row column : Word n) (previous : List transcript.Label) :
    Prop where
  /-- The path has the required row and column origins. -/
  boundaries : test.path.HasBoundaries row column previous
  /-- The selected label occurs on the walk. -/
  uses : test.label ∈ test.path.walk.labels
  /-- Labels on the walk are at most the selected label. -/
  latest : ∀ label ∈ test.path.walk.labels, label ≤ test.label

/-- Each test may refer only to the two original boundaries and records already selected. -/
def ValidFlowTests {transcript : Transcript n} {vertices : Set (State n)} (row column : Word n)
    (previous : List transcript.Label) : List (FlowTest transcript vertices) → Prop
  | [] => True
  | test :: rest => test.Valid row column previous ∧
      ValidFlowTests row column (previous ++ [test.label]) rest

/-- The selected record labels with the given query direction, in list order. -/
def flowLabels (transcript : Transcript n) (direction : Direction)
    (labels : List transcript.Label) : List transcript.Label :=
  labels.filter fun label ↦ decide ((transcript.get label).direction = direction)

/-- The initial row and the output rows of the selected forward records in Lemma 3. -/
def flowRows (transcript : Transcript n) (row : Word n) (labels : List transcript.Label) :
    Finset (Word n) :=
  insert row ((flowLabels transcript .forward labels).toFinset.image
    fun label ↦ (transcript.get label).output.2)

/-- The initial column and the input columns of the selected inverse records in Lemma 3. -/
def flowColumns (transcript : Transcript n) (column : Word n) (labels : List transcript.Label) :
    Finset (Word n) :=
  insert column ((flowLabels transcript .backward labels).toFinset.image
    fun label ↦ (transcript.get label).input.1)

/-- One zero-edge vertex survives from each original path in the grid of generated boundaries. -/
structure FlowWitness (transcript : Transcript n) (vertices : Set (State n))
    (row column : Word n) (count : ℕ) where
  /-- The selected records and their path tests in reverse order. -/
  tests : List (FlowTest transcript vertices)
  /-- Selected record indices strictly decrease. -/
  decreasing : tests.Pairwise (fun earlier later ↦ later.label < earlier.label)
  /-- Each test is valid relative to the earlier selections in the list. -/
  valid : ValidFlowTests row column [] tests
  /-- The remaining zero-edge vertices, one per original path. -/
  points : Fin count → vertices
  /-- Distinct original paths leave distinct vertices. -/
  points_injective : Function.Injective points
  /-- Each remaining vertex lies in the grid of available rows and columns. -/
  points_in_grid : ∀ i,
    (points i).val.2 ∈ flowRows transcript row (tests.map FlowTest.label) ∧
    (points i).val.1 ∈ flowColumns transcript column (tests.map FlowTest.label)
  /-- The product of the two grid dimensions bounds the number of paths. -/
  grid_bound : count ≤
    ((flowLabels transcript .forward (tests.map FlowTest.label)).length + 1) *
    ((flowLabels transcript .backward (tests.map FlowTest.label)).length + 1)

namespace FlowWitnessSpec

/-- The prefix preceding the first selected occurrence avoids its label. -/
def FirstOccurrence : Prop :=
  ∀ {Vertex : Type u} {Label : Type v} {edge : Label → Vertex → Vertex → Prop}
    {source target : Vertex} (walk : Walk edge source target) (label : Label),
    label ∈ walk.labels →
    ∃ (x y : Vertex) (before : Walk edge source x) (step : edge label x y)
      (after : Walk edge y target),
      walk = before.append (.cons label step after) ∧ label ∉ before.labels

/-- The suffix following the last selected occurrence avoids its label. -/
def LastOccurrence : Prop :=
  ∀ {Vertex : Type u} {Label : Type v} {edge : Label → Vertex → Vertex → Prop}
    {source target : Vertex} (walk : Walk edge source target) (label : Label),
    label ∈ walk.labels →
    ∃ (x y : Vertex) (before : Walk edge source x) (step : edge label x y)
      (after : Walk edge y target),
      walk = before.append (.cons label step after) ∧ label ∉ after.labels

/-- A disjoint family from one residual row to one residual column yields a flow witness. -/
def Extract : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices : Set (State n))
    (row column : Word n) (count : ℕ),
    HasDisjointPaths (residualRelation (realRecordRelation transcript) vertices)
      (rowVertices vertices row) (columnVertices vertices column) count →
    Nonempty (FlowWitness transcript vertices row column count)

/-- The grid inequality forces at least `h` distinct selected labels at the flow threshold. -/
def RecordCount : Prop :=
  ∀ (p : Parameters.Params) (transcript : Transcript p.n) (vertices : Set (State p.n))
    (row column : Word p.n) (witness : FlowWitness transcript vertices row column (p.pi + 1)),
    p.h ≤ witness.tests.length

/-- The tested path uses the chosen record and its predecessors, on any earlier residual set
that contains the final residual vertices. -/
def PrefixTest : Prop :=
  ∀ {n : ℕ} (transcript : Transcript n) (vertices earlier : Set (State n))
    (row column : Word n) (previous : List transcript.Label) (test : FlowTest transcript vertices),
    vertices ⊆ earlier → test.Valid row column previous →
    HasNewPath (transcript.take test.label.val) (transcript.get test.label) earlier
      (flowRow transcript row test.path.rowFrom) (flowColumn transcript column test.path.columnFrom)

end FlowWitnessSpec

end JH.Graph
