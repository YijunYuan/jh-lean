/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelSpec

/-!
# Fixed-permutation trials

Oracle queries, verification, and fixed-target trials.
-/

@[expose] public section

namespace JH

/-- A forward or inverse request at a 2n-bit address. -/
structure Query (n : ℕ) where
  /-- Which direction of the permutation to query. -/
  direction : Direction
  /-- The state supplied to the oracle. -/
  address : State n

namespace Query

variable {n : ℕ}

/-- The answer to the query under the specified permutation. -/
def reply (permutation : Permutation n) (query : Query n) : State n :=
  match query.direction with
  | .forward => permutation query.address
  | .backward => permutation.symm query.address

/-- The disclosed input-output pair, together with the direction of the request. -/
def record (permutation : Permutation n) (query : Query n) : Record n :=
  match query.direction with
  | .forward => ⟨query.address, query.reply permutation, .forward⟩
  | .backward => ⟨query.reply permutation, query.address, .backward⟩

/-- Tests whether this record supplies the address requested in the given direction. -/
def hasAddress (query : Query n) (record : Record n) : Bool :=
  match query.direction with
  | .forward => decide (record.input = query.address)
  | .backward => decide (record.output = query.address)

/-- Read the answer from the output or input of a record according to the query direction. -/
def replyFrom (query : Query n) (record : Record n) : State n :=
  match query.direction with
  | .forward => record.output
  | .backward => record.input

end Query

namespace Transcript

/-- A new transcript extends the old ordering and preserves all its labels. -/
def Extends {n : ℕ} (new old : Transcript n) : Prop :=
  old <+: new

/-- Append the permutation pair if the queried address is missing from its side of the log.
A forward query checks input addresses and an inverse query checks output addresses. -/
def logAccess {n : ℕ} (old : Transcript n) (permutation : Permutation n) (query : Query n) :
    Transcript n :=
  if old.any query.hasAddress then old else old ++ [query.record permutation]

end Transcript

/-- A deterministic terminating adaptive computation, after fixing its independent random tape.
The continuation can use a repeated answer, just as it can a fresh answer. -/
inductive Strategy (α n : ℕ) where
  | halt (candidate : Option (Message α))
  | query (request : Query n) (resume : State n → Strategy α n)

/-- Execute a deterministic adaptive strategy and record its fresh accesses. -/
def Strategy.run {α n : ℕ} (permutation : Permutation n) :
    Strategy α n → Transcript n → Option (Message α) × Transcript n
  | .halt candidate, transcript => (candidate, transcript)
  | .query request resume, transcript =>
      (resume (request.reply permutation)).run permutation
        (transcript.logAccess permutation request)

/-- Evaluate the submitted blocks and log every previously unrecorded verification access. -/
def verifyBlocks {n : ℕ} (permutation : Permutation n) :
    State n → List (Word n) → Transcript n → State n × Transcript n
  | state, [], transcript => (state, transcript)
  | state, block :: rest, transcript =>
      verifyBlocks permutation (compress permutation state block) rest
        (transcript.logAccess permutation ⟨.forward, permInput state block⟩)

/-- The final transcript and the optional state obtained by verifying the candidate. -/
structure TrialResult (n : ℕ) where
  /-- All records disclosed through candidate verification. -/
  records : Transcript n
  /-- The final verified state, if a candidate was submitted. -/
  terminal : Option (State n)

/-- The real experiment with a fixed permutation and fixed adversary tape.
The strategy has already been given the fixed target. -/
def fixedTargetTrial {α n : ℕ} (strategy : Strategy α n) (permutation : Permutation n)
    (initial : State n) (padding : Padding α n) : TrialResult n :=
  let (candidate, records) := strategy.run permutation []
  match candidate with
  | none => ⟨records, none⟩
  | some message =>
      let (terminal, records) := verifyBlocks permutation initial (padding.encode message) records
      ⟨records, some terminal⟩

/-- The verified candidate has the fixed target as its final capacity. -/
def TrialResult.Success {n : ℕ} (result : TrialResult n) (target : Word n) : Prop :=
  result.terminal.map Prod.fst = some target

/-- The complete transcript, including candidate verification, contains at most the given number
of records. -/
def TrialResult.WithinBudget {n : ℕ} (result : TrialResult n) (q : ℕ) : Prop :=
  result.records.length ≤ q

namespace ExperimentSpec

/-- Looking up a matching record consistent with the permutation returns the actual oracle reply.
-/
def CacheReply : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (query : Query n) (record : Record n),
    record.Consistent permutation → query.hasAddress record = true →
      query.replyFrom record = query.reply permutation

/-- Verification computes the iterated compression and extends the consistent transcript to cover
all submitted blocks. -/
def Verification : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (initial : State n) (blocks : List (Word n))
    (old : Transcript n), old.Consistent permutation →
      let result := verifyBlocks permutation initial blocks old
      result.1 = JH.run permutation initial blocks ∧ result.2.Extends old ∧
        result.2.Consistent permutation ∧ result.2.Covers permutation initial blocks

/-- A successful real trial produces the path using the actual logged strategy and verification
accesses. A caller gives the result of the trial rather than a postulated covered run. -/
def TrialWitness : Prop :=
  ∀ {α n : ℕ} (strategy : Strategy α n) (permutation : Permutation n) (initial : State n)
    (padding : Padding α n) (target : Word n),
    let result := fixedTargetTrial strategy permutation initial padding
    result.records.Consistent permutation ∧
      (result.Success target →
        ∃ rate : Word n, Nonempty
          (Walk (result.records.edge {initial}) (startCopy initial) (.inl (target, rate))))

end ExperimentSpec

end JH
