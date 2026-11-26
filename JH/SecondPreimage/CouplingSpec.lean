/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.SuccessTransferSpec
public import JH.SecondPreimageSpec

/-!
# Transfer second-preimage acceptance with the combined budget

Transfer the second-preimage trial to independent replies, including the original accesses.
-/

@[expose] public section

namespace JH

variable {α n : ℕ}

/-- Tests whether the compiled second-preimage verifier returned a terminal state. -/
def compiledSecondPreimageAccepts (outcome : Option (TrialResult n)) : Bool :=
  outcome.any fun result ↦ result.terminal.isSome

/-- The Boolean acceptance law of the fixed-original strategy under a uniform permutation. -/
noncomputable def secondPreimageAcceptanceLaw
    (select : Message α → Word n → Transcript n → Strategy α n)
    (initial : State n) (padding : Padding α n) (original : Message α) : PMF Bool := by
  classical
  exact (uniformPMF (Permutation n)).map fun permutation ↦
    decide ((secondPreimageTrial select permutation initial padding original).Success
      original (hash permutation initial padding original))

namespace SecondPreimageCouplingSpec

/-- The argument `q` is the paper's post-disclosure budget $Q = q + L_\alpha$,
including candidate evaluation. The full trial is coupled with budget $Q + \ell(M)$. -/
def Transfer : Prop :=
  ∀ {α : ℕ} (params : Parameters.Params) (q : ℕ)
    (select : Message α → Word params.n → Transcript params.n → Strategy α params.n)
    (initial : State params.n) (padding : Padding α params.n) (original : Message α),
    (∀ permutation,
      (secondPreimageTrial select permutation initial padding original).trial.records.length ≤
        (verifyBlocks permutation initial (padding.encode original) []).2.length + q) →
    let fuel := q + (padding.encode original).length
    ((secondPreimageAcceptanceLaw select initial padding original) true).toReal ≤
      (Separation.mass (TrialProgram.independentBounded fuel
        (TrialProgram.ofSecondPreimage select initial padding original) [])
          compiledSecondPreimageAccepts).toReal + params.separationTail fuel

end SecondPreimageCouplingSpec

end JH
