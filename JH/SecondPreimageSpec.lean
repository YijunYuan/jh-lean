/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Lazy.TrialSpec
public import JH.RandomTargetSpec

/-!
# The compiled second-preimage experiment

The experiment in Section 2.2 discloses the original message, its digest, and its evaluation
transcript. `FiniteBound` states the common-threshold estimate of Theorem 2(2) for a fixed
original.
-/

@[expose] public section

namespace JH

universe u

namespace TrialProgram

variable {α n : ℕ}

/-- Change the terminal result while keeping all queries, including failed verification. -/
def mapTerminal (changeTerminal : Option (State n) → Option (State n)) :
    TrialProgram n → TrialProgram n
  | .done terminal => .done (changeTerminal terminal)
  | .query request resume => .query request fun reply ↦ mapTerminal changeTerminal (resume reply)

/-- Evaluate the original message and pass its terminal, cache, and complete state sequence
to the continuation. The cache records a pair only on a fresh access. -/
def observeOriginal : State n → List (Word n) → Transcript n → List (State n) →
    (State n → Transcript n → List (State n) → TrialProgram n) → TrialProgram n
  | state, [], old, previous, next =>
    next state old (state :: previous).reverse
  | state, block :: rest, old, previous, next =>
    let request : Query n := ⟨.forward, permInput state block⟩
    .query request fun reply ↦
      let records := match old.cachedReply request with
        | none => old.appendReply request reply
        | some _ => old
      observeOriginal (feedForward reply block) rest records (state :: previous) next

/-- Run the same candidate verification and accept precisely a distinct candidate
with the original digest. -/
def verifyDistinct (original : Message α) (target : Word n) (initial : State n)
    (padding : Padding α n) : Strategy α n → TrialProgram n
  | .halt none => .done none
  | .halt (some candidate) => (verify initial (padding.encode candidate)).mapTerminal
      (fun terminal ↦ if candidate ≠ original ∧ terminal.map Prod.fst = some target
        then terminal else none)
  | .query request resume => .query request fun reply ↦
      verifyDistinct original target initial padding (resume reply)

/-- Compile evaluation and disclosure of the original, the adaptive strategy, and verification of
its distinct candidate into one program. -/
def ofSecondPreimage (select : Message α → Word n → Transcript n → Strategy α n)
    (initial : State n) (padding : Padding α n) (original : Message α) : TrialProgram n :=
  observeOriginal initial (padding.encode original) [] [] fun terminal records _ ↦
    verifyDistinct original terminal.1 initial padding (select original terminal.1 records)

end TrialProgram

/-- For every supported tape and permutation, the strategy and verification together
add at most `q` fresh records after disclosure. The disclosed transcript is already
cached. This budget is $Q=q+L_\alpha$ in the manuscript. -/
def FixedSecondPreimageBudget {α n : ℕ} {Tape : Type u} (q : ℕ) (original : Message α)
    (initial : State n) (padding : Padding α n) (tapes : PMF Tape)
    (adversary : Message α → Word n → Transcript n → Tape → Strategy α n) : Prop :=
  ∀ tape ∈ tapes.support, ∀ permutation,
    let old := (verifyBlocks permutation initial (padding.encode original) []).2
    let result := secondPreimageTrial (fun message target records ↦
      adversary message target records tape) permutation initial padding original
    result.trial.records.length ≤ old.length + q

namespace SecondPreimageSpec

/-- The real program retains the observed original states and query records exactly. -/
def ObserveOriginal : Prop :=
  ∀ {n : ℕ} (permutation : Permutation n) (state : State n) (blocks : List (Word n))
    (old : Transcript n) (previous : List (State n))
    (next : State n → Transcript n → List (State n) → TrialProgram n),
    let observed := verifyBlocks permutation state blocks old
    (TrialProgram.observeOriginal state blocks old previous next).run permutation old =
      (next observed.1 observed.2 (previous.reverse ++
        blocks.scanl (compress permutation) state)).run permutation observed.2

/-- Compiling the full trial preserves its actual record log and acceptance. -/
def ProgramLaw : Prop :=
  ∀ {α n : ℕ} (select : Message α → Word n → Transcript n → Strategy α n)
    (permutation : Permutation n) (initial : State n) (padding : Padding α n)
      (original : Message α),
    let real := secondPreimageTrial select permutation initial padding original
    let compiled :=
      (TrialProgram.ofSecondPreimage select initial padding original).run permutation []
    compiled.records = real.trial.records ∧
      (compiled.terminal.isSome = true ↔
        real.Success original (hash permutation initial padding original))

/-- Theorem 2(2). For each original fixed before sampling the permutation, the common threshold
C = 2 Bpot + 2L gives success probability at most 6 · 2^(−λ−3). -/
def FiniteBound : Prop :=
  ∀ {Tape : Type u} (params : Parameters.Params) (q L α : ℕ), params.SPRCertificate q L →
    ∀ (initial : State params.n) (padding : Padding α params.n) (original : Message α)
      (tapes : PMF Tape) (adversary : Message α → Word params.n → Transcript params.n →
        Tape → Strategy α params.n),
      (padding.encode original).length ≤ L →
      FixedSecondPreimageBudget q original initial padding tapes adversary →
        fixedMessageSecondPreimageSuccessProbability original initial padding tapes adversary ≤
          6 * params.tailBudget ∧ 6 * params.tailBudget < ((2 : ℝ) ^ params.lambda)⁻¹

end SecondPreimageSpec

end JH
