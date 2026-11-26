/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Model

/-!
# Compression edges and covered walks

A transcript consistent with a permutation identifies the labelled edges in (6) with uses of
the compression function (3). Virtual starts give the version for nonempty block lists.
-/

@[expose] public section

namespace JH.ModelSpec

/-- The state-coordinate space has exactly N = 2^n elements. -/
def WordCard : Prop := ∀ n : ℕ, Fintype.card (Word n) = 2 ^ n

/-- Equation (6) represents exactly the compressions using this consistent record. The
compression block realizing an edge for this label is unique. -/
def RecordEdge : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (record : Record n),
    record.Consistent permutation → ∀ (source target : State n),
      record.edge source target ↔
        ∃! block : Word n, permInput source block = record.input ∧
          compress permutation source block = target

/-- The enumerated edges agree with the edge predicate. Each record gives N real edges. -/
def RecordEdges : Prop :=
  ∀ {n : ℕ} (record : Record n),
    (∀ (source target : State n), (source, target) ∈ record.edges ↔ record.edge source target) ∧
      record.edges.card = 2 ^ n

/-- Zero-edge walks are included for real vertices. -/
def RealWalk : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (transcript : Transcript n),
    transcript.Consistent permutation → ∀ (source target : State n),
      Nonempty (Walk transcript.realEdge source target) ↔
        ∃ blocks : List (Word n), transcript.Covers permutation source blocks ∧
          run permutation source blocks = target

/-- Virtual start copies characterize nonempty runs, also for several initial states. -/
def VirtualWalk : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (transcript : Transcript n),
    transcript.Consistent permutation →
      ∀ (initials : Finset (State n)) (initial : { state : State n // state ∈ initials })
        (target : State n),
        Nonempty (Walk (transcript.edge initials) (.inr initial) (.inl target)) ↔
          ∃ blocks : List (Word n), blocks ≠ [] ∧
            transcript.Covers permutation initial.val blocks ∧
            run permutation initial.val blocks = target

/-- After verification, a successful legal fixed-target output gives a graph witness. -/
def FixedTargetSuccessWitness : Prop :=
  ∀ {α n : ℕ} (permutation : Permutation n) (transcript : Transcript n),
    transcript.Consistent permutation →
      ∀ (initial : State n) (padding : Padding α n) (message : Message α) (target : Word n),
        transcript.Covers permutation initial (padding.encode message) →
          hash permutation initial padding message = target →
            ∃ rate : Word n, Nonempty
              (Walk (transcript.edge {initial}) (startCopy initial) (.inl (target, rate)))

end JH.ModelSpec
