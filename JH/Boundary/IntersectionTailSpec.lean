/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Boundary.MeanSpec
public import JH.Potential.Barrier.ReplaySpec
public import JH.Probability.Tape.AdaptiveMeanSpec

/-!
# The first intersection tail

Population and first-intersection estimates for the stopped adaptive trial in Section 3.4.
-/

@[expose] public section

namespace JH.Probability

open JH.Graph JH.Parameters
open scoped BigOperators

namespace IntersectionTail

/-- Total number of vertices on the two sides, before normalization. -/
noncomputable def population {n : ℕ} {initials : Finset (State n)}
    (sides : Boundary (Vertex initials)) : ℝ :=
  (sides.forward.ncard : ℝ) + (sides.backward.ncard : ℝ)

/-- Scale the population by `N` and keep only histories still active before a round. -/
noncomputable def activePopulation (params : Params) {initials : Finset (State params.n)}
    (tracker : GraphTracker initials) : ℝ :=
  match tracker with
  | .active snapshot => population snapshot.sides / (params.N : ℝ)
  | .stopped _ _ => 0

/-- Sum of the two boundary sizes divided by N before this round, and zero if the graph has
stopped. -/
noncomputable def populationBefore (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (i : Fin q) (prior : Fin i.val → State params.n) : ℝ :=
  activePopulation params
    (GraphTracker.replay params psi initials targets
      (BarrierReplay.beforeRound program i prior).records)

/-- A past round contributes its real inheritance if it began active and had a fresh access. -/
noncomputable def inheritanceCost (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (side : Direction) :
      AdaptiveMean.Quantity (State params.n) q :=
  fun i prior word ↦
    let before := BarrierReplay.beforeRound program i prior
    match before.frontier with
    | .done _ => 0
    | .query request _ =>
      match GraphTracker.replay params psi initials targets before.records with
      | .stopped _ _ => 0
      | .active snapshot =>
        let record := request.recordOfReply (request.replyCoords.symm word)
        ∑ line : Word params.n,
          (BoundaryMean.inheritedCount snapshot.records record params.mu
            snapshot.sides side line : ℝ)

/-- Sum the singleton ledger charges, which pay for grafts in one direction. -/
noncomputable def graftCharge (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) (side : Direction) :
      AdaptiveMean.Quantity (State params.n) q :=
  fun i prior word ↦ ∑ line : Word params.n,
    BarrierReplay.ledgerCost params psi initials targets program side line {0} i prior word

/-- A first intersection can occur only on an active history and a fresh access. -/
def intersectsAt (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) : TapeTests.Test (State params.n) q :=
  fun i prior word ↦
    let before := BarrierReplay.beforeRound program i prior
    match before.frontier with
    | .done _ => False
    | .query request _ =>
      match GraphTracker.replay params psi initials targets before.records with
      | .stopped _ _ => False
      | .active snapshot =>
        RoundStep snapshot.records (request.recordOfReply (request.replyCoords.symm word))
          params.mu snapshot.sides .intersected

/-- Indicator of an active round that first intersects during inheritance. -/
noncomputable def intersectionIndicator (params : Params) {q : ℕ} (psi : ℕ)
    (initials : Finset (State params.n)) (targets : Set (Word params.n))
    (program : TrialProgram params.n) : AdaptiveMean.Quantity (State params.n) q := by
  classical
  exact fun i prior word ↦
    if intersectsAt params psi initials targets program i prior word then 1 else 0

/-- The active-population bound before using $QB_{\mathrm{pair}}/N\le 1$ and $Q/N\le 1/U$. -/
noncomputable def populationBound (params : Params) (q psi : ℕ) (theta initialBound : ℝ) : ℝ :=
  initialBound + 2 * (params.N : ℝ) / (params.mu : ℝ) ^ params.d +
    (2 * (q : ℝ) / (params.N : ℝ)) * (1 + (q : ℝ) * (params.Theta : ℝ) / (params.N : ℝ)) *
      (params.weightedCoefficient theta + (psi : ℝ) + 2 * (params.Pi : ℝ))

end IntersectionTail

namespace IntersectionTailSpec

open IntersectionTail

/-- Condition on the past only. Average over both coordinates of the next fresh reply. -/
def LocalIntersectionMean : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    ∀ (i : Fin q) (prior : Fin i.val → State params.n),
      (𝔼 word : State params.n,
        intersectionIndicator params psi initials targets program i prior word) ≤
        (psi : ℝ) / (params.N : ℝ) * (1 + (q : ℝ) * (params.Theta : ℝ) / (params.N : ℝ) +
          populationBefore params psi initials targets program i prior)

/-- Every round begins with the same upper bound on the mean active population. -/
def ActivePopulationMean : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n) (theta initialBound : ℝ),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    0 < theta → population (initialBoundary initials targets) / (params.N : ℝ) ≤ initialBound →
    ∀ i : Fin q,
      (𝔼 prior : Fin i.val → State params.n,
        populationBefore params psi initials targets program i prior) ≤
        populationBound params q psi theta initialBound

/-- Equation (29), with the initial-size and weighted-drift parameters of Section 3.4 and
Appendix A.3. -/
def Tail : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n) (theta initialBound : ℝ),
    params.CommonCertificate q → (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    0 < theta → population (initialBoundary initials targets) / (params.N : ℝ) ≤ initialBound →
    firstStopProbability params q psi initials targets program .intersect ≤
      params.intersectionTail psi (initialBound + 2) (params.weightedCoefficient theta)

end IntersectionTailSpec

end JH.Probability
