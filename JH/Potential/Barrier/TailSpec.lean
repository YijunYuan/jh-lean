/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Potential.Barrier.ReplaySpec

/-!
# The first potential-stop tail

Probability bounds for the first potential stop.
-/

@[expose] public section

namespace JH.Graph.BarrierTailSpec

open JH.Parameters

/-- The first potential crossing satisfies the consequence of (22) with exponential factor
2^(−Binh/8). The initial occupancy hypothesis applies to either security experiment. -/
def EqualTail : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n),
    params.CommonCertificate q →
    (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    (q : ℝ) * ((params.driftNumerator : ℝ) / (params.N : ℝ)) ≤ (params.Gamma : ℝ) / 4 →
    firstStopProbability params q psi initials targets program .overPotential ≤ params.barrierTail

/-- The same event and tail expression with the weighted charge mean from (A.3). -/
def WeightedTail : Prop :=
  ∀ (params : Params) (q psi : ℕ) (initials : Finset (State params.n))
    (targets : Set (Word params.n)) (program : TrialProgram params.n) (theta : ℝ),
    0 < theta → params.CommonCertificate q →
    (GraphSnapshot.initial initials targets).OccupancyBounded psi →
    (q : ℝ) * (params.weightedDriftNumerator theta / (params.N : ℝ)) ≤ (params.Gamma : ℝ) / 4 →
    firstStopProbability params q psi initials targets program .overPotential ≤ params.barrierTail

end JH.Graph.BarrierTailSpec
