/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Connectivity.FlowWitnessSpec
public import JH.Probability.FirstStopSpec
public import JH.Probability.Tape.TestsSpec
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset

/-!
# From a path-count stop to a flow witness

The finite witness union for the first connected stop in Lemma 3.
-/

@[expose] public section

namespace JH.Graph

open Parameters
open scoped ENNReal

namespace FlowTail

/-- A choice of h record positions from the q rounds of Lemma 3. -/
abbrev Selected (q h : ℕ) := {rounds : Finset (Fin q) // rounds.card = h}

/-- The encoding of the two boundary origins at each reverse rank of the selected records. -/
abbrev Origins (h : ℕ) := (j : Fin h) → Fin (j.val + 1) × Fin (j.val + 1)

/-- The original row and column, a set of selected rounds, and two origins per rank. -/
abbrev Code (n q h : ℕ) := (Word n × Word n) × (Selected q h × Origins h)

/-- The selected rounds are visited in decreasing order. -/
def roundAt {q h : ℕ} (selected : Selected q h) (rank : Fin h) : Fin q :=
  selected.val.orderEmbOfFin selected.property rank.rev

/-- Zero denotes the original coordinate. A positive origin denotes an earlier rank in
the backward selection, so its value can be read from the presampled intrinsic tape. -/
def boundaryValue {n q h : ℕ} (selected : Selected q h) (intrinsic : CoordinateTape n q)
    (original : Word n) (rank : Fin h) (origin : Fin (rank.val + 1)) : Word n :=
  if origin.val = 0 then original
  else intrinsic (roundAt selected
    ⟨origin.val - 1, by have := rank.isLt; have := origin.isLt; omega⟩)

/-- Replay the given coordinate prefix up to the specified round. -/
def beforeRound {n q : ℕ} (program : TrialProgram n) (intrinsic : CoordinateTape n q)
    (i : Fin q) (prior : Fin i.val → Word n) : TapeState n :=
  (⟨program, []⟩ : TapeState n).runPrefix
    (Probability.TapeTests.prefixAt intrinsic i) prior i.val le_rfl

/-- The fixed witness encoding and intrinsic tape determine the row and column of the test.
The preceding offsets determine the adaptive query and residual graph with that tape fixed.
The current offset determines whether the fresh record supplies a new path.
A halted trial or an already stopped graph cannot pass. -/
noncomputable def test {params : Params} {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (code : Code params.n q params.h)
    (intrinsic : CoordinateTape params.n q) : Probability.TapeTests.Test (Word params.n) q :=
  fun i prior offset ↦
    let before := beforeRound program intrinsic i prior
    match before.frontier, GraphTracker.replay params psi initials targets before.records with
    | .query request _, .active snapshot =>
      ∃ rank : Fin params.h, roundAt code.2.1 rank = i ∧
        HasNewPath snapshot.records
          (request.recordOfReply (request.replyCoords.symm (intrinsic i, offset)))
          snapshot.sides.realResidual
          (boundaryValue code.2.1 intrinsic code.1.1 rank (code.2.2 rank).1)
          (boundaryValue code.2.1 intrinsic code.1.2 rank (code.2.2 rank).2)
    | _, _ => False

/-- Pairs of tapes passing all selected tests of a given disjoint-path encoding. -/
noncomputable def codeEvent {params : Params} {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (code : Code params.n q params.h) :
    Set (CoordinateTape params.n q × CoordinateTape params.n q) :=
  {tapes | tapes.2 ∈ Probability.TapeTests.passes
    (test psi initials targets program code tapes.1) code.2.1.val}

/-- The single-record offset probability bound in Lemma 2. -/
noncomputable def stepBound (params : Params) : ℝ := 2 * (params.Pi : ℝ) ^ 2 / (params.N : ℝ)

/-- The union estimate over encodings of disjoint paths in Lemma 3. -/
noncomputable def unionBound (params : Params) (q : ℕ) : ℝ :=
  (params.N : ℝ) ^ 2 * (q.choose params.h : ℝ) * (params.h.factorial : ℝ) ^ 2 *
    (stepBound params) ^ params.h

end FlowTail

namespace FlowTailSpec

open FlowTail

/-- Original cells, sets of specified rounds, and the two origin choices at each rank. -/
def EncodingCard : Prop :=
  ∀ n q h : ℕ, Fintype.card (Code n q h) = (2 ^ n) ^ 2 * q.choose h * h.factorial ^ 2

/-- Each specified offset test has bounded mass given any old shift prefix. -/
def ConditionalTest : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ∀ (code : Code params.n q params.h) (intrinsic : CoordinateTape params.n q)
      (i : Fin q) (prior : Fin i.val → Word params.n),
      (PartialPermutation.uniformFinite (Word params.n)).toOuterMeasure
        (Probability.TapeTests.approving
          (test psi initials targets program code intrinsic) i prior) ≤
      ENNReal.ofReal (stepBound params)

/-- Union of the encoded witnesses, averaged over the intrinsic tape. -/
def EncodedUnion : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ((CoordinateTape.law params.n q).toOuterMeasure
      (⋃ code : Code params.n q params.h, codeEvent psi initials targets program code)).toReal ≤
      unionBound params q

/-- The actual first path-count stop is covered by the encoded witness events. -/
def WitnessCovered : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    firstStopEvent params q psi initials targets program .overConnected ⊆
      ⋃ code : Code params.n q params.h, codeEvent psi initials targets program code

/-- Equation (14) for the first connected stop under the actual bounded trial law. -/
def FirstStopBound : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    firstStopProbability params q psi initials targets program .overConnected ≤ params.flowTail

end FlowTailSpec

end JH.Graph
