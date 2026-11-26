/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Walk
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Sigma

/-!
# The JH compression function and record graph

A state is a capacity-rate pair of n-bit words. Compression (3) and the record edges (6) let a
single permutation query represent an edge for each source rate. Virtual copies of the starting
states distinguish nonempty encoded messages from zero-edge walks.
-/

@[expose] public section

namespace JH

/-- An n-bit word in the paper's half-state space V. -/
abbrev Word (n : ℕ) := BitVec n

/-- The first coordinate is capacity and the second coordinate is rate. -/
abbrev State (n : ℕ) := Word n × Word n

/-- A permutation of the full 2n-bit state space. -/
abbrev Permutation (n : ℕ) := Equiv.Perm (State n)

/-- Enumerate the n-bit words by their unsigned values from zero to 2^n − 1. -/
instance wordFintype (n : ℕ) : Fintype (Word n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (BitVec.equivFin (m := n)).toEquiv.symm

/-- Messages of bit length 1 through α, encoded with length index one less than the bit length. -/
abbrev Message (α : ℕ) := (k : Fin α) × Word (k.val + 1)

/-- An injective encoding into nonempty lists of n-bit blocks. The experiment accounts for the
cost of processing the encoded list. -/
structure Padding (α n : ℕ) where
  /-- The padded blocks submitted to the compression function. -/
  encode : Message α → List (Word n)
  /-- Distinct messages have distinct block encodings. -/
  injective : Function.Injective encode
  /-- Every padded message uses at least one block. -/
  nonempty : ∀ message, encode message ≠ []

/-- XOR the message block into the rate before the permutation call in (3). -/
def permInput {n : ℕ} (state : State n) (block : Word n) : State n :=
  (state.1, state.2 ^^^ block)

/-- XOR the message block into the capacity of the permutation output in (3). -/
def feedForward {n : ℕ} (response : State n) (block : Word n) : State n :=
  (response.1 ^^^ block, response.2)

/-- Compression in equation (3). -/
def compress {n : ℕ} (permutation : Permutation n) (state : State n) (block : Word n) :
    State n :=
  feedForward (permutation (permInput state block)) block

/-- Iterate JH compression in block order from the initial state. -/
def run {n : ℕ} (permutation : Permutation n) (initial : State n) (blocks : List (Word n)) :
    State n :=
  blocks.foldl (compress permutation) initial

/-- The capacity of the final state after evaluating the padded message. -/
def hash {α n : ℕ} (permutation : Permutation n) (initial : State n)
    (padding : Padding α n) (message : Message α) : Word n :=
  (run permutation initial (padding.encode message)).1

/-- A forward or inverse permutation query. -/
inductive Direction where
  | forward
  | backward
  deriving DecidableEq

/-- Either query direction yields an input/output record for the same permutation. -/
structure Record (n : ℕ) where
  /-- The permutation input x. -/
  input : State n
  /-- The corresponding output y. -/
  output : State n
  /-- The direction of the access disclosing this pair. -/
  direction : Direction
  deriving DecidableEq

namespace Record

variable {n : ℕ}

/-- The record agrees with the given permutation. -/
def Consistent (permutation : Permutation n) (record : Record n) : Prop :=
  permutation record.input = record.output

/-- The offset σ of a record in (6), its input rate XOR its output capacity. -/
def shift (record : Record n) : Word n :=
  record.input.2 ^^^ record.output.1

/-- Equation (6), for one specified record. -/
def edge (record : Record n) (source target : State n) : Prop :=
  source.1 = record.input.1 ∧ target = (source.2 ^^^ record.shift, record.output.2)

/-- The directed edge in (6) indexed by a source rate. -/
def edgeAtRate (record : Record n) : Word n ↪ (State n × State n) where
  toFun rate := ((record.input.1, rate), (rate ^^^ record.shift, record.output.2))
  inj' := fun _ _ h ↦ congrArg (fun pair ↦ pair.1.2) h

/-- The N graph edges contributed by one record. -/
def edges (record : Record n) : Finset (State n × State n) :=
  Finset.univ.map record.edgeAtRate

end Record

/-- The list of disclosed permutation records, in access order. -/
abbrev Transcript (n : ℕ) := List (Record n)

/-- Real states together with the virtual copies $I^*$ of the selected starting states $I$.
For fixed-target preimages, $I$ is the singleton containing the public initial value. -/
abbrev Vertex {n : ℕ} (initials : Finset (State n)) :=
  State n ⊕ { state : State n // state ∈ initials }

/-- The real state represented by an ordinary vertex or a virtual copy. -/
def Vertex.state {n : ℕ} {initials : Finset (State n)} : Vertex initials → State n
  | .inl state => state
  | .inr initial => initial.val

/-- The virtual copy of the single start in the fixed-target preimage game. -/
def startCopy {n : ℕ} (initial : State n) : Vertex ({initial} : Finset (State n)) :=
  .inr ⟨initial, Finset.mem_singleton_self initial⟩

namespace Transcript

variable {n : ℕ}

/-- The position of a record in the transcript. -/
abbrev Label (transcript : Transcript n) := Fin transcript.length

/-- Every record in the transcript agrees with the given permutation. -/
def Consistent (permutation : Permutation n) (transcript : Transcript n) : Prop :=
  ∀ label : transcript.Label, (transcript.get label).Consistent permutation

/-- The edge relation (6) on real states contributed by the specified label. -/
def realEdge (transcript : Transcript n) (label : transcript.Label) :
    State n → State n → Prop :=
  (transcript.get label).edge

/-- Copies of real outgoing edges at each virtual source. Every edge has a real target. -/
def edge (transcript : Transcript n) (initials : Finset (State n))
    (label : transcript.Label) (source target : Vertex initials) : Prop :=
  match target with
  | .inl targetState => transcript.realEdge label source.state targetState
  | .inr _ => False

/-- Every permutation input used in the run occurs in the transcript. -/
def Covers (transcript : Transcript n) (permutation : Permutation n) :
    State n → List (Word n) → Prop
  | _, [] => True
  | state, block :: rest =>
      (∃ label : transcript.Label, (transcript.get label).input = permInput state block) ∧
        transcript.Covers permutation (compress permutation state block) rest

end Transcript

end JH
