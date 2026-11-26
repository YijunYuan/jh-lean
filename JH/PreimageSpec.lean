/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.ExperimentSpec
public import JH.Parameters.CertificateSpec
public import JH.Probability.UniformPMF
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Fixed-target preimage bounds

For a fixed digest and a strategy law independent of the permutation, `FiniteBound` and
`WeightedFiniteBound` give the $5\cdot 2^{-\lambda-3}$ upper bound in (A.5).
`ExplicitSqrtBound` specializes (39). In all three statements, `q` denotes the paper's
total budget $Q=q+L_\alpha$.
-/

@[expose] public section

namespace JH

noncomputable section

/-- The adversary's tape selects a deterministic strategy independently of the uniform
permutation. The target is fixed before either draw. -/
def fixedTargetSuccessProbability {α n : ℕ} (target : Word n) (initial : State n)
    (padding : Padding α n) (strategies : PMF (Strategy α n)) : ℝ := by
  classical
  exact ((strategies.bind fun strategy ↦
    (uniformPMF (Permutation n)).map fun permutation ↦
      decide ((fixedTargetTrial strategy permutation initial padding).Success target)) true).toReal

/-- For every supported strategy and every permutation, the trial logs at most `q`
fresh records, counting both the adversary and verification. -/
def FixedTargetBudget {α n : ℕ} (q : ℕ) (initial : State n) (padding : Padding α n)
    (strategies : PMF (Strategy α n)) : Prop :=
  ∀ strategy ∈ strategies.support, ∀ permutation,
    (fixedTargetTrial strategy permutation initial padding).WithinBudget q

namespace PreimageSpec

open JH.Parameters

/-- Theorem 2(1) in the $5\cdot 2^{-\lambda-3}$ form of (A.5).
Each of the four graph probabilities and the coupling bound fits in one tail budget.
The same bound holds for every admissible strategy law at a fixed digest. -/
def FiniteBound : Prop :=
  ∀ (params : Params) (q α : ℕ), params.PreCertificate q →
    ∀ (target : Word params.n) (initial : State params.n)
      (padding : Padding α params.n) (strategies : PMF (Strategy α params.n)),
      FixedTargetBudget q initial padding strategies →
        fixedTargetSuccessProbability target initial padding strategies ≤ 5 * params.tailBudget ∧
          5 * params.tailBudget < ((2 : ℝ) ^ params.lambda)⁻¹

/-- With the weighted coefficients (A.3), the certificate (A.4) gives the fixed-target success
bound (A.5). -/
def WeightedFiniteBound : Prop :=
  ∀ (params : Params) (q α : ℕ) (theta : ℝ), params.WeightedPreCertificate q theta →
    ∀ (target : Word params.n) (initial : State params.n)
      (padding : Padding α params.n) (strategies : PMF (Strategy α params.n)),
      FixedTargetBudget q initial padding strategies →
        fixedTargetSuccessProbability target initial padding strategies ≤ 5 * params.tailBudget ∧
          5 * params.tailBudget < ((2 : ℝ) ^ params.lambda)⁻¹

/-- The rounded loss εₙ after the square-root substitution below (39). -/
def uniformLoss (n : ℕ) : ℕ :=
  2 * ⌈Real.sqrt ((n : ℝ) / 2)⌉₊ + ⌈Real.sqrt (2 * (n : ℝ))⌉₊ +
    5 * ⌈Real.log (n : ℝ) / Real.log 2⌉₊ + 12

/-- The specialization of (39) to χ = ⌈√(n/2)⌉ and λ = ⌊√(2n)⌋ for n ≥ 4. -/
def ExplicitSqrtBound : Prop :=
  ∀ (n q α : ℕ), 4 ≤ n → q * 2 ^ uniformLoss n ≤ 2 ^ n →
    ∀ (target : Word n) (initial : State n)
      (padding : Padding α n) (strategies : PMF (Strategy α n)),
      FixedTargetBudget q initial padding strategies →
        fixedTargetSuccessProbability target initial padding strategies <
          ((2 : ℝ) ^ ⌊Real.sqrt (2 * (n : ℝ))⌋₊)⁻¹

end PreimageSpec

end

end JH
