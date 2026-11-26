/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.ExperimentSpec

/-!
# First departure and return in a second-preimage trace

The first departure from and first return to an original compression trace in Section 3.2.
-/

@[expose] public section

namespace JH.SecondPreimageTrace

variable {n : ℕ}

/-- Compression with a fixed forward reply function. -/
def compressWith (reply : State n → State n) (source : State n) (block : Word n) : State n :=
  feedForward (reply (permInput source block)) block

/-- Iterate compression on a list of blocks using the supplied reply function. -/
def runWith (reply : State n → State n) (initial : State n) (blocks : List (Word n)) : State n :=
  blocks.foldl (compressWith reply) initial

/-- The states immediately before each block. -/
def sources (reply : State n → State n) : State n → List (Word n) → List (State n)
  | _, [] => []
  | source, block :: rest => source :: sources reply (compressWith reply source block) rest

/-- All states of the original trace, including the final state. -/
def states (reply : State n → State n) (initial : State n)
    (blocks : List (Word n)) : List (State n) :=
  sources reply initial blocks ++ [runWith reply initial blocks]

/-- All capacities along the trajectory, including the initial capacity, are distinct. -/
def DistinctCapacities (reply : State n → State n) (initial : State n)
    (blocks : List (Word n)) : Prop :=
  ((states reply initial blocks).map Prod.fst).Nodup

/-- The ordered forward records of the original trace. -/
def originalRecords (reply : State n → State n) : State n → List (Word n) → Transcript n
  | _, [] => []
  | source, block :: rest =>
    ⟨permInput source block, reply (permInput source block), .forward⟩ ::
      originalRecords reply (compressWith reply source block) rest

/-- The set I of states visited by the original trajectory in (10). -/
def initialStates (reply : State n → State n) (initial : State n) (original : List (Word n)) :
    Finset (State n) := (states reply initial original).toFinset

/-- The set Z of capacities visited by that trajectory, used as target columns in (10). -/
def capacityColumns (reply : State n → State n) (initial : State n) (original : List (Word n)) :
    Set (Word n) := {capacity | capacity ∈ (states reply initial original).map Prod.fst}

/-- The candidate uses the input and reply of a recorded pair at every compression. -/
def Covers (reply : State n → State n) (records : Transcript n) :
    State n → List (Word n) → Prop
  | _, [] => True
  | source, block :: rest =>
    (∃ record ∈ records, record.input = permInput source block ∧
      record.output = reply (permInput source block)) ∧
    Covers reply records (compressWith reply source block) rest

/-- The first differing block and the segment through the first subsequent original column. -/
structure ReturnSegment (reply : State n → State n) (initial : State n)
    (original candidate : List (Word n)) (later : Transcript n) where
  /-- Shared block prefix up to departure. -/
  common : List (Word n)
  /-- Original blocks following the common prefix. -/
  originalTail : List (Word n)
  /-- First candidate block after the common prefix. -/
  firstBlock : Word n
  /-- Remaining candidate blocks after departure. -/
  candidateTail : List (Word n)
  /-- Prefix of the remaining blocks through the first return. -/
  throughReturn : List (Word n)
  /-- The common prefix and original tail reconstruct the original. -/
  original_split : original = common ++ originalTail
  /-- The common prefix, departing block, and candidate tail reconstruct the candidate. -/
  candidate_split : candidate = common ++ (firstBlock :: candidateTail)
  /-- The original ends or has a different block at the departure. -/
  next_differs : originalTail.head? ≠ some firstBlock
  /-- The return segment uses a prefix of the remaining candidate blocks. -/
  return_prefix : throughReturn <+: candidateTail
  /-- Original state from which the candidate departs. -/
  start : ↥(initialStates reply initial original)
  /-- The shared prefix reaches the departure state. -/
  start_eq : start.val = runWith reply initial common
  /-- A walk from the virtual departure state using later records. -/
  path : Walk (later.edge (initialStates reply initial original)) (.inr start)
    (.inl (runWith reply start.val (firstBlock :: throughReturn)))
  /-- The walk contains at least one record label. -/
  nonempty : path.labels ≠ []
  /-- The endpoint capacity belongs to Z in (10). -/
  target_column : (runWith reply start.val (firstBlock :: throughReturn)).1 ∈
    capacityColumns reply initial original
  /-- Internal capacities avoid Z until the first return. -/
  internal_columns : ∀ vertex ∈ (path.vertices.drop 1).dropLast,
    vertex.state.1 ∉ capacityColumns reply initial original

end JH.SecondPreimageTrace

namespace JH.SecondPreimageTraceSpec

open SecondPreimageTrace

/-- A covered candidate of the same terminal capacity gives a subsequent-record witness. -/
def DepartureAndReturn : Prop :=
  ∀ {n : ℕ} (reply : State n → State n) (initial : State n)
    (original candidate : List (Word n)) (later : Transcript n),
    original ≠ candidate → DistinctCapacities reply initial original →
    (runWith reply initial candidate).1 = (runWith reply initial original).1 →
    Covers reply (originalRecords reply initial original ++ later) initial candidate →
    Nonempty (ReturnSegment reply initial original candidate later)

/-- A collision-free original run logs the exact ordered list of its forward accesses. -/
def VerifiedOriginal : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (initial : State n) (original : List (Word n)),
    DistinctCapacities permutation initial original →
    (verifyBlocks permutation initial original []).2 = originalRecords permutation initial original

/-- Actual verification supplies the per-compression input and reply witnesses. -/
def VerifiedCoverage : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (initial : State n) (blocks : List (Word n))
    (old : Transcript n), old.Consistent permutation →
    Covers permutation (verifyBlocks permutation initial blocks old).2 initial blocks

/-- For distinct messages with the same digest, retain only the records after the original run. -/
def VerifiedMessages : Prop :=
  ∀ {α n : ℕ} (permutation : Permutation n) (initial : State n) (padding : Padding α n)
    (original candidate : Message α) (accesses : Transcript n),
    original ≠ candidate → DistinctCapacities permutation initial (padding.encode original) →
    hash permutation initial padding candidate = hash permutation initial padding original →
    let originalLog := (verifyBlocks permutation initial (padding.encode original) []).2
    Transcript.Consistent permutation (originalLog ++ accesses) →
    let final := (verifyBlocks permutation initial (padding.encode candidate)
        (originalLog ++ accesses)).2
    Nonempty (ReturnSegment permutation initial (padding.encode original) (padding.encode candidate)
      (final.drop originalLog.length))

end JH.SecondPreimageTraceSpec
