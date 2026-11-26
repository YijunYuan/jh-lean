/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Probability.FirstStopSpec

/-!
# Counting ledgers for the barrier union

Finite ledger modes and the cardinality bound for the barrier event.
-/

@[expose] public section

namespace JH.Graph

open JH.Parameters

/-- An account in (18), indexed by direction, line, and nonempty pattern of size at most Bver. -/
abbrev LedgerKey (params : Params) :=
  Direction × Word params.n × {mode : Finset (Word params.n) //
    mode.Nonempty ∧ mode.card ≤ params.Pi}

namespace BarrierModesSpec

/-- The factor in the union bound in (22). -/
def LedgerCount : Prop :=
  ∀ params : Params, Nat.card (LedgerKey params) ≤ 2 * params.N * (params.N + 1) ^ params.Pi

/-- The exponential single-account bound is at most $2^{-B_{\mathrm{inh}}/8}$. -/
def TailExponent : Prop :=
  ∀ params : Params, 0 < params.Pi →
    Real.exp (-((Real.log 2 / 2 - 1 / 4) * ((params.Gamma : ℝ) / params.Pi))) ≤
      (2 : ℝ) ^ (-(params.nu : ℝ) / 8)

end BarrierModesSpec

end JH.Graph
