/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.SuccessTransfer
public import JH.Oracle.Lazy.Bounded
public import JH.SecondPreimage
public import JH.SecondPreimage.CouplingSpec

/-!
# Transfer second-preimage acceptance with the combined budget

The original-message computation, the adversary after disclosure, and candidate verification
form one query program. If the original encoding has `ℓ` blocks, its initial phase costs at
most `ℓ` fresh accesses. The coupling starts before disclosure with fuel `q + ℓ`, where `q` is
the post-disclosure budget used by the graph argument in Section 3.2.
-/

@[expose] public section

namespace JH

variable {α n : ℕ}

/-- Every verification block appends at most one pair to the initial log. -/
theorem verifyBlocks_length_le (permutation : Permutation n) (initial : State n)
    (blocks : List (Word n)) (old : Transcript n) :
    (verifyBlocks permutation initial blocks old).2.length ≤ old.length + blocks.length := by
  induction blocks generalizing initial old with
  | nil => simp [verifyBlocks]
  | cons block rest ih =>
      let request : Query n := ⟨.forward, permInput initial block⟩
      let after := old.logAccess permutation request
      have step : after.length ≤ old.length + 1 := by
        dsimp only [after, Transcript.logAccess]
        split <;> simp
      simp only [verifyBlocks, List.length_cons]
      exact (ih (compress permutation initial block) after).trans (by omega)

/-- Real second-preimage acceptance is at most the independent trial's acceptance plus
the separation allowance $\binom{Q+\ell(M)}{2}/N^2$ in the paper's
`eq:advantage-decomposition`. -/
theorem second_preimage_transfer : SecondPreimageCouplingSpec.Transfer := by
  intro α params q select initial padding original budget
  classical
  let fuel := q + (padding.encode original).length
  let program := TrialProgram.ofSecondPreimage select initial padding original
  have realLaw :
      (TrialProgram.lazyBounded fuel program [] (Transcript.empty_possible params.n)).map
        compiledSecondPreimageAccepts =
          secondPreimageAcceptanceLaw select initial padding original := by
    have uniform : uniformPermutation params.n = uniformPMF (Permutation params.n) :=
      PartialPermutation.uniformFinite_eq_uniformOfFintype _
    rw [TrialProgram.lazyBounded_eq_map, Transcript.posterior_empty, PMF.map_comp,
      uniform, secondPreimageAcceptanceLaw]
    apply congrArg (uniformPMF (Permutation params.n)).map
    funext permutation
    have originalLength := verifyBlocks_length_le permutation initial (padding.encode original) []
    simp only [List.length_nil, zero_add] at originalLength
    have budgetUsed := budget permutation
    have programLaw :=
      TrialProgram.second_preimage_program select permutation initial padding original
    -- The original-phase bound and the post-disclosure promise cover the same compiled run.
    have total : (program.run permutation []).records.length ≤
        ([ ] : Transcript params.n).length + fuel := by
      have records_eq : (program.run permutation []).records =
          (secondPreimageTrial select permutation initial padding
            original).trial.records := programLaw.1
      rw [records_eq]
      dsimp [fuel]
      omega
    have runLaw := TrialProgram.runFreshBounded_eq_by_budget permutation fuel program []
      (by intro label; exact Fin.elim0 label)
    change compiledSecondPreimageAccepts
      (TrialProgram.runFreshBounded permutation fuel program []) =
      decide ((secondPreimageTrial select permutation initial padding original).Success
        original (hash permutation initial padding original))
    rw [runLaw, ite_eq_left total]
    apply Bool.eq_iff_iff.mpr
    simpa only [compiledSecondPreimageAccepts, Option.any_some,
      decide_eq_true_eq] using programLaw.2
  -- Compare the complete trials once both stages fit in the combined budget.
  have coupled := TrialProgram.bounded_acceptance_le_real fuel program compiledSecondPreimageAccepts
  unfold Separation.mass at coupled
  rw [realLaw] at coupled
  simpa only [Parameters.Params.separationTail, Parameters.Params.N, Nat.cast_pow, Nat.cast_ofNat,
    fuel, program, Separation.mass] using coupled

end JH
