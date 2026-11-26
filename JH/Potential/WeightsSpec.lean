/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.PatternsSpec

/-!
# Point and translated potentials

Point and translated potentials of the residual graph.
-/

@[expose] public section

namespace JH.Graph

open scoped BigOperators

variable {n : ℕ}

/-- The contribution of one row to (15) before truncation, its ancestor count to the power d
divided by μ^d. -/
noncomputable def normalizedRowWeight (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (targets : Set (State n)) (row : Word n) : ℝ :=
  ((rowAncestorsTo edge vertices row targets).ncard : ℝ) ^ d / (mu : ℝ) ^ d

/-- The truncated forward weight in (15). -/
noncomputable def forwardWeight (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (targets : Set (State n)) : ℝ :=
  min 1 (∑ row : Word n, normalizedRowWeight edge vertices mu d targets row)

/-- The forward translated potential in (16). The empty mode has value zero. -/
noncomputable def translatedPotential (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n) (mode : Finset (Word n)) : ℝ :=
  (∑ offset : Word n, forwardWeight edge vertices mu d
    (columnPattern vertices column mode offset)) / mode.card

/-- Rates of the residual vertices in the specified capacity column. -/
noncomputable def columnRates (vertices : Set (State n)) (column : Word n) : Finset (Word n) := by
  classical
  exact Finset.univ.filter fun rate ↦ (column, rate) ∈ vertices

/-- The sum of the single-state weights over the current residual column, as in the singleton
case of (16). -/
noncomputable def pointColumnPotential (edge : State n → State n → Prop)
    (vertices : Set (State n)) (mu d : ℕ) (column : Word n) : ℝ :=
  ∑ rate ∈ columnRates vertices column, forwardWeight edge vertices mu d {(column, rate)}

namespace PotentialSpec

/-- The zero singleton pattern in (16) gives the sum of the point weights in the column. -/
def SingletonMode : Prop :=
  ∀ {n : ℕ} (edge : State n → State n → Prop) (vertices : Set (State n)) (mu d : ℕ)
    (column : Word n), 0 < d →
    translatedPotential edge vertices mu d column {0} =
      pointColumnPotential edge vertices mu d column

/-- With no records, each translated potential is at most the initial bound p₀ = N/μ^d. -/
def InitialPotential : Prop :=
  ∀ {n : ℕ} (vertices : Set (State n)) (mu d : ℕ) (column : Word n) (mode : Finset (Word n)),
    0 < mu → 0 < d →
      translatedPotential (realRecordRelation ([] : Transcript n)) vertices mu d column mode ≤
        (2 : ℝ) ^ n / (mu : ℝ) ^ d

/-- Each residual successor of a forward-eligible root has singleton weight one. -/
def GraftPointWeight : Prop :=
  ∀ {n : ℕ} (edge : State n → State n → Prop) (vertices : Set (State n))
    (mu d : ℕ) (root target : State n) (row : Word n),
    0 < mu → mu ≤ (rowAncestors edge vertices row root).ncard →
      ReachesWithin edge vertices root target →
      forwardWeight edge vertices mu d {target} = 1

/-- A deletion pays one unit from the column potential for every removed unit-weight point. -/
def DeletionPayment : Prop :=
  ∀ {n : ℕ} (edge : State n → State n → Prop) (before after : Set (State n))
    (mu d : ℕ) (column : Word n) (paidRates : Finset (Word n)),
    after ⊆ before →
    (∀ rate ∈ paidRates, (column, rate) ∈ before ∧ (column, rate) ∉ after ∧
      forwardWeight edge before mu d {(column, rate)} = 1) →
    pointColumnPotential edge after mu d column + paidRates.card ≤
      pointColumnPotential edge before mu d column

end PotentialSpec

end JH.Graph
