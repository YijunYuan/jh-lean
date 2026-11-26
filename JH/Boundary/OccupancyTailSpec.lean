/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.BackwardEventsSpec
public import JH.Potential.Barrier.ReplaySpec
public import Mathlib.Data.Fintype.Powerset

/-!
# The first occupancy-stop tail

The first occupancy stop and its inherited-line witnesses from Section 3.4.
-/

@[expose] public section

namespace JH.Probability

open JH.Graph JH.Parameters
open scoped ENNReal

namespace OccupancyTail

/-- A set of exactly Binh distinct round indices for an occupancy witness. -/
abbrev Selected (q nu : ℕ) := {rounds : Finset (Fin q) // rounds.card = nu}

/-- An occupancy witness consisting of a direction, a line, and Binh selected rounds. -/
abbrev Code (n q nu : ℕ) := Bool × Word n × Selected q nu

/-- Decode the direction bit of an occupancy witness. -/
def directionOf : Bool → Direction
  | false => .forward
  | true => .backward

/-- The newly inherited coordinates on the chosen forward column or backward row. -/
def inheritedOnLine {n : ℕ} {initials : Finset (State n)}
    (records : Transcript n) (record : Record n) (before : Boundary (Vertex initials))
    (direction : Direction) (line : Word n) : Set (Word n) :=
  match direction with
  | .forward => BoundaryEvents.forwardInheritedRates records record before line
  | .backward => BackwardBoundaryEvents.backwardInheritedCaps records record before line

/-- Test whether this fresh record makes a nonempty inheritance transfer while the old
graph is active and the current record permits a continuing graph round. -/
noncomputable def inheritsAt (params : Params) (psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (before : TapeState params.n) (direction : Direction)
    (line : Word params.n) (word : State params.n) : Prop :=
  match before.frontier, GraphTracker.replay params psi initials targets before.records with
  | .query request _, .active snapshot =>
      let record := request.recordOfReply (request.replyCoords.symm word)
      ∃ finish, RoundStep snapshot.records record params.mu snapshot.sides (.continued finish) ∧
        (inheritedOnLine snapshot.records record snapshot.sides direction line).Nonempty
  | _, _ => False

/-- For a fixed intrinsic tape, a test uses only the previous shifts and the new shift. -/
noncomputable def test (params : Params) {q : ℕ} (psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n) (direction : Direction)
    (line : Word params.n) (intrinsic : CoordinateTape params.n q) :
    TapeTests.Test (Word params.n) q :=
  fun i prior shift ↦
    let before := BarrierReplay.beforeRound program i (fun j ↦
        (TapeTests.prefixAt intrinsic i j, prior j))
    inheritsAt params psi initials targets before direction line (intrinsic i, shift)

/-- Pairs of tapes that pass all inheritance tests in the occupancy witness. -/
noncomputable def codeEvent (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (code : Code params.n q params.nu) :
    Set (CoordinateTape params.n q × CoordinateTape params.n q) :=
  {tapes | tapes.2 ∈ TapeTests.passes
    (test params psi initials targets program (directionOf code.1) code.2.1 tapes.1) code.2.2.val}

/-- The one-line, one-round inheritance bound Bver (C + Bver)/N used in (23). -/
noncomputable def stepBound (params : Params) (psi : ℕ) : ℝ :=
  (params.Pi : ℝ) * ((psi : ℝ) + (params.Pi : ℝ)) / (params.N : ℝ)

end OccupancyTail

namespace OccupancyTailSpec

open OccupancyTail PartialPermutation

/-- There are two directions, N lines, and binomially many choices of Binh rounds. -/
def EncodingCard : Prop :=
  ∀ n q nu : ℕ, Fintype.card (Code n q nu) = 2 * 2 ^ n * q.choose nu

/-- Given the previous offsets and the intrinsic tape, each inheritance test has probability at
most the one-round bound. -/
def ConditionalTest : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    (GraphSnapshot.initial initials targets).ValidParameters params psi →
    ∀ (direction : Direction) (line : Word params.n) (intrinsic : CoordinateTape params.n q)
      (i : Fin q) (prior : Fin i.val → Word params.n),
      (uniformFinite (Word params.n)).toOuterMeasure
        (TapeTests.approving
          (test params psi initials targets program direction line intrinsic) i prior) ≤
      ENNReal.ofReal (stepBound params psi)

/-- A first occupancy crossing produces a line and Binh distinct rounds with nonempty
inheritance. -/
def WitnessCovered : Prop :=
  ∀ (params : Params) (q psi b : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded b →
    b + params.Gamma + (params.nu - 1) * params.Pi ≤ psi →
      firstStopEvent params q psi initials targets program .overCrowded ⊆
        ⋃ code : Code params.n q params.nu, codeEvent params psi initials targets program code

/-- The first occupancy crossing is bounded by (23) summed over directions and lines. -/
def FirstStopBound : Prop :=
  ∀ (params : Params) (q psi b : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded b →
    b + params.Gamma + (params.nu - 1) * params.Pi ≤ psi →
      firstStopProbability params q psi initials targets program .overCrowded ≤
        params.occupancyTail q psi

end OccupancyTailSpec

end JH.Probability
