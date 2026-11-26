/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.Evolution.StoppedGraphSpec
public import JH.Potential.Drift.MeanSpec

/-!
# Charges on the stopped graph replay

The deletion and conditional charge bounds for active graph histories.
-/

@[expose] public section

namespace JH.Graph.StoppedChargeSpec

open JH.Parameters
open scoped BigOperators

/-- After a continuing graph round, the increase of every ledger is covered by the
charge computed before deleting any vertices. -/
def LedgerGrowth : Prop :=
  ∀ (params : Params) {initials : Finset (State params.n)} (snapshot : GraphSnapshot initials)
    (record : Record params.n) (finish : Boundary (Vertex initials)),
    0 < params.mu → 0 < params.d →
    RoundStep snapshot.records record params.mu snapshot.sides (.continued finish) →
    ∀ direction line mode,
      (snapshot.afterGrafting record finish).ledger params.mu params.d direction line mode ≤
        snapshot.ledger params.mu params.d direction line mode +
          GraphTracker.charge params (.active snapshot) record direction line mode

/-- The bound holds at each active state for either direction and every mode. -/
def ActiveChargeRange : Prop :=
  ∀ (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials), snapshot.ValidParameters params psi →
    ∀ record direction line mode,
      let charge := GraphTracker.charge params (.active snapshot) record direction line mode
      0 ≤ charge ∧ charge ≤ (params.Pi : ℝ)

/-- The ordinary conditional mean from (19), given the old active state and the exposed
coordinates of the current record. -/
def ActiveChargeMean : Prop :=
  ∀ (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) (inputColumn outputRow : Word params.n)
    (recordFor : Word params.n → Record params.n),
    0 < params.d → snapshot.ValidParameters params psi →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    ∀ direction line (mode : Finset (Word params.n)), mode.card ≤ params.Pi →
      wordMean (fun shift ↦ GraphTracker.charge params (.active snapshot) (recordFor shift)
        direction line mode) ≤ (params.driftNumerator : ℝ) / (params.N : ℝ)

/-- The weighted conditional mean uses the same ledgers and charges as the ordinary bound. -/
def ActiveChargeWeightedMean : Prop :=
  ∀ (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) (inputColumn outputRow : Word params.n)
    (recordFor : Word params.n → Record params.n) (theta : ℝ),
    0 < params.d → 0 < theta → snapshot.ValidParameters params psi →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    ∀ direction line (mode : Finset (Word params.n)), mode.card ≤ params.Pi →
      wordMean (fun shift ↦ GraphTracker.charge params (.active snapshot) (recordFor shift)
        direction line mode) ≤ params.weightedDriftNumerator theta / (params.N : ℝ)

/-- Sum the charge over the singleton ledgers in one direction, as needed to count grafts. -/
def ActiveTotalPointWeightedMean : Prop :=
  ∀ (params : Params) (psi : ℕ) {initials : Finset (State params.n)}
    (snapshot : GraphSnapshot initials) (inputColumn outputRow : Word params.n)
    (recordFor : Word params.n → Record params.n) (theta : ℝ),
    0 < params.d → 0 < theta → snapshot.ValidParameters params psi →
    SharesExposedCoordinates recordFor inputColumn outputRow →
    ∀ direction,
      wordMean (fun shift ↦ ∑ line : Word params.n,
        GraphTracker.charge params (.active snapshot) (recordFor shift) direction line {0}) ≤
        (1 + (snapshot.records.length : ℝ) * (params.Theta : ℝ) / (params.N : ℝ)) *
          (params.weightedCoefficient theta + (params.Pi : ℝ))

end JH.Graph.StoppedChargeSpec
