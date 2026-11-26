/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.TrialSpec
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Presampling the independent-reply coordinates

The independent experiment driven by two presampled tapes.
-/

@[expose] public section

namespace JH

/-- One n-bit word per fresh-query position, sampled in advance. -/
abbrev CoordinateTape (n q : ℕ) := Fin q → Word n

namespace CoordinateTape

open PartialPermutation (uniformFinite)

/-- Draw the whole intrinsic-coordinate tape and the whole offset tape independently. -/
noncomputable def law (n q : ℕ) : PMF (CoordinateTape n q × CoordinateTape n q) :=
  ReplyCoupling.independentPair (uniformFinite _) (uniformFinite _)

/-- Split the first pair of coordinates from the two remaining tapes. -/
def split (n q : ℕ) : (CoordinateTape n (q + 1) × CoordinateTape n (q + 1)) ≃
    ((Word n × Word n) × (CoordinateTape n q × CoordinateTape n q)) where
  toFun tapes := ((tapes.1 0, tapes.2 0), (Fin.tail tapes.1, Fin.tail tapes.2))
  invFun parts := (Fin.cons parts.1.1 parts.2.1, Fin.cons parts.1.2 parts.2.2)
  left_inv tapes := Prod.ext (Fin.cons_self_tail tapes.1) (Fin.cons_self_tail tapes.2)
  right_inv parts := by rcases parts with ⟨⟨a, b⟩, x, d⟩; simp only [Fin.cons_zero, Fin.tail_cons]

end CoordinateTape

namespace Record

/-- A forward record contributes its output rate, and a backward record its input capacity. -/
def intrinsicCoordinate {n : ℕ} (record : Record n) : Word n :=
  match record.direction with
  | .forward => record.output.2
  | .backward => record.input.1

end Record

/-- The remaining program and the records already written before the next round. -/
structure TapeState (n : ℕ) where
  /-- The remaining adaptive computation. -/
  program : TrialProgram n
  /-- The records already disclosed. -/
  records : Transcript n

namespace TapeState

variable {n q : ℕ}

/-- Resolve cache hits before inspecting the next coordinate and offset. -/
def frontier (state : TapeState n) : FreshFrontier n := state.program.nextFresh state.records

/-- A terminal frontier remains unchanged during every unused round. -/
def step (state : TapeState n) (coordinate offset : Word n) : TapeState n :=
  match state.frontier with
  | .done _ => state
  | .query request resume =>
    let answer := request.replyCoords.symm (coordinate, offset)
    ⟨resume answer, state.records.appendReply request answer⟩

/-- Consume precisely the first `i` tape positions. -/
def runPrefix (initial : TapeState n) (intrinsic offsets : CoordinateTape n q) :
    (i : ℕ) → i ≤ q → TapeState n
  | 0, _ => initial
  | i + 1, within =>
    (runPrefix initial intrinsic offsets i (by omega)).step
      (intrinsic ⟨i, by omega⟩) (offsets ⟨i, by omega⟩)

/-- The terminal trial result when the frontier has finished, or no result while a query is
pending. -/
def result (state : TapeState n) : Option (TrialResult n) :=
  match state.frontier with
  | .done terminal => some ⟨state.records, terminal⟩
  | .query _ _ => none

/-- A query left after the last tape position exhausts the budget. -/
def run (initial : TapeState n) (intrinsic offsets : CoordinateTape n q) : Option (TrialResult n) :=
  (initial.runPrefix intrinsic offsets q le_rfl).result

end TapeState

namespace CoordinateTapeSpec

open PartialPermutation (uniformFinite)

/-- The first pair consists of two independent uniform words, independent of both tails. -/
def SplitLaw : Prop :=
  ∀ n q, (CoordinateTape.law n (q + 1)).map (CoordinateTape.split n q) =
    ReplyCoupling.independentPair
      (ReplyCoupling.independentPair (uniformFinite (Word n)) (uniformFinite (Word n)))
      (CoordinateTape.law n q)

/-- Presampling the tapes gives the law of sampling the coordinates as queries are reached. -/
def RunLaw : Prop :=
  ∀ {n : ℕ} (q : ℕ) (initial : TapeState n),
    (CoordinateTape.law n q).map (fun tapes ↦ initial.run tapes.1 tapes.2) =
      TrialProgram.independentCoordinatesBounded q initial.program initial.records

/-- The state before round `i` depends only on tape positions strictly before `i`. -/
def PrefixAgreement : Prop :=
  ∀ {n q : ℕ} (initial : TapeState n) (intrinsic offsets intrinsic' offsets' : CoordinateTape n q)
    (i : ℕ) (within : i ≤ q),
    (∀ j : Fin q, j.val < i → intrinsic j = intrinsic' j ∧ offsets j = offsets' j) →
    initial.runPrefix intrinsic offsets i within = initial.runPrefix intrinsic' offsets' i within

/-- A live round follows the program continuation and appends one record carrying its tape pair. -/
def LiveRound : Prop :=
  ∀ {n q : ℕ} (initial : TapeState n) (intrinsic offsets : CoordinateTape n q) (i : Fin q)
    (request : Query n) (resume : State n → TrialProgram n),
    let before := initial.runPrefix intrinsic offsets i.val (Nat.le_of_lt i.isLt)
    before.frontier = .query request resume →
    let after := initial.runPrefix intrinsic offsets (i.val + 1) (Nat.succ_le_of_lt i.isLt)
    let answer := request.replyCoords.symm (intrinsic i, offsets i)
    let record := request.recordOfReply answer
    after.program = resume answer ∧ after.records = before.records ++ [record] ∧
      record.direction = request.direction ∧ record.intrinsicCoordinate = intrinsic i ∧
      record.shift = offsets i

/-- Once the frontier is terminal, the program and transcript remain fixed through later rounds. -/
def TerminalRound : Prop :=
  ∀ {n q : ℕ} (initial : TapeState n) (intrinsic offsets : CoordinateTape n q)
    (i j : ℕ) (earlier : i ≤ j) (within : j ≤ q) (terminal : Option (State n)),
    let before := initial.runPrefix intrinsic offsets i (earlier.trans within)
    before.frontier = .done terminal → initial.runPrefix intrinsic offsets j within = before

end CoordinateTapeSpec

end JH
