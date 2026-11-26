/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.PrivateAncestors
public import JH.Parameters.WeightedOptimality
public import JH.Parameters.WeightedOptimality.Limits
public import JH.Preimage
public import JH.RandomTarget
public import JH.SecondPreimageBound

/-!
# JH preimage and second-preimage bounds

This library formalizes results from
*Near-n-Bit Preimage and Second-Preimage Security of the JH Mode*.
`JH.preimage_finite` proves the fixed-target bound of Theorem 2(1) in the
$5\cdot 2^{-\lambda-3}$ form of (A.5), with one tail budget for the coupling.
`JH.second_preimage_finite` proves Theorem 2(2) for a fixed original message with
the same occupancy threshold on both sides of the graph. The joint bound of Theorem 3 uses
different thresholds.

`JH.preimage_explicit_sqrt` specializes (39) to the rounded square-root parameters.
`JH.preimage_weighted_finite` gives (A.5) for positive weights, and
`JH.Parameters.WeightedOptimality.loss_asymptotic` proves the weighted part of (A.12).

Each theorem's type names its quantified statement, for example `JH.PreimageSpec.FiniteBound`.
In the finite bounds, `q` is the paper's $Q=q+L_\alpha$, which includes candidate verification.
The reading guides map the manuscript notation to Lean. `JH.Audit` checks the theorem types
and reports their axiom dependencies.
-/
