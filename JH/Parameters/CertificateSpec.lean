/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Analysis.ConvexSpec
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite security certificates

Section 3.5 and Appendix A.1 give the finite certificate conditions. Here `pi`, `Pi`, and
`Theta` denote $B_{\mathrm{path}}$, $B_{\mathrm{ver}}$, and $B_{\mathrm{pair}}$.
The inheritance and potential thresholds $B_{\mathrm{inh}}$ and $B_{\mathrm{pot}}$
are `nu` and `Gamma`. The two occupancy choices in (24) are `Psi` ($C_0$) and `sprPsi L`
($C$) for a fixed original of padded length at most `L`.
-/

@[expose] public section

namespace JH.Parameters

/-- Integer parameters of the finite security certificate in Section 3.5 and (A.1). -/
structure Params where
  /-- Digest and half-state width in bits. -/
  n : ℕ
  /-- Exponent λ in the target advantage bound. -/
  lambda : ℕ
  /-- Graft threshold μ in (7). -/
  mu : ℕ
  /-- Degree of the potential weight in (15). -/
  d : ℕ
  /-- Disjoint-path threshold Bpath in (12). -/
  pi : ℕ
  /-- Integer loss s in the budget exponent. -/
  s : ℕ
  /-- Inheritance threshold Binh in (30). -/
  nu : ℕ

namespace Params

/-- The half-state space size N = 2^n. -/
def N (p : Params) : ℕ := 2 ^ p.n

/-- The divisor U = 2^s in the total fresh-access budget Q ≤ N/U. -/
def U (p : Params) : ℕ := 2 ^ p.s

/-- The bound Bver = Bpath (μ − 1) on each endpoint support in Lemma 1. -/
def Pi (p : Params) : ℕ := p.pi * (p.mu - 1)

/-- The bound Bpair = Bpath (μ − 1)² on the endpoint relation in Lemma 1. -/
def Theta (p : Params) : ℕ := p.pi * (p.mu - 1) ^ 2

/-- The potential threshold Bpot = Bver Binh in (24). -/
def Gamma (p : Params) : ℕ := p.Pi * p.nu

/-- The fixed-target occupancy threshold C₀ = 2 Bpot from (A.1). -/
def Psi (p : Params) : ℕ := 2 * p.Gamma

/-- The common second-preimage occupancy threshold C = 2 Bpot + 2L in (24). -/
def sprPsi (p : Params) (L : ℕ) : ℕ := 2 * p.Gamma + 2 * L

noncomputable section

/-- Number of records selected in the path witness of Lemma 3, h = ⌈2√(Bpath + 1)⌉ − 2. -/
def h (p : Params) : ℕ := ⌈2 * Real.sqrt ((p.pi : ℝ) + 1)⌉₊ - 2

/-- Basic lower bounds on the integer certificate parameters in (A.1). -/
structure Admissible (p : Params) : Prop where
  /-- The half-state has positive width. -/
  n_pos : 1 ≤ p.n
  /-- The target advantage exponent is positive. -/
  lambda_pos : 1 ≤ p.lambda
  /-- The graft threshold is at least two. -/
  mu_ge_two : 2 ≤ p.mu
  /-- The potential degree is at least two. -/
  d_ge_two : 2 ≤ p.d
  /-- At least one disjoint path is allowed. -/
  pi_pos : 1 ≤ p.pi

/-- The total fresh-access budget $Q\le N/U$ in Section 3.5. Here `q` denotes
$Q=q+L_\alpha$ from the paper. -/
def QueryBudget (p : Params) (q : ℕ) : Prop := (q : ℝ) ≤ (p.N : ℝ) / (p.U : ℝ)

/-- The inheritance threshold Binh is at least 8 ((n + 1) Bver + n + λ + 4), as required by
(30). -/
def NuChoice (p : Params) : Prop :=
  8 * ((p.n + 1) * p.Pi + p.n + p.lambda + 4) ≤ p.nu

/-- The unweighted one-record drift numerator D in (20) and (A.2). -/
def driftNumerator (p : Params) : ℕ :=
  2 ^ (p.d - 1) * p.Gamma * (p.Pi ^ 2 + p.Theta) + p.Pi * p.Theta

/-- The unweighted graft coefficient J in (A.2). -/
def graftCoefficient (p : Params) : ℝ :=
  2 ^ (p.d - 1) * ((p.Pi : ℝ) + (p.Gamma : ℝ))

/-- The graft coefficient J at weight θ in (A.3). -/
def weightedCoefficient (p : Params) (theta : ℝ) : ℝ :=
  JH.Analysis.weightedCost (p.Pi : ℝ) (p.Gamma : ℝ) p.d theta

/-- The numerator of the weighted one-step drift in equation (A.3). -/
def weightedDriftNumerator (p : Params) (theta : ℝ) : ℝ :=
  (p.Theta : ℝ) * (p.weightedCoefficient theta + (p.Pi : ℝ))

/-- The factor multiplying $C/U$ in (29). The argument `psi` is $C$, `initial` is
$L+4$, and `coefficient` is $J$. The term inside the budget correction is
$T(C)=J+C+2B_{\mathrm{ver}}$. -/
def intersectionFactor (p : Params) (psi : ℕ) (initial coefficient : ℝ) : ℝ :=
  initial + 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d +
    (4 / (p.U : ℝ)) * (coefficient + (psi : ℝ) + 2 * (p.Pi : ℝ))

/-- The intersection estimate (29) fits the single-event budget of (34). -/
def IntersectionCondition (p : Params) (psi : ℕ) (initial coefficient : ℝ) : Prop :=
  (2 : ℝ) ^ (p.lambda + 3) * (psi : ℝ) * p.intersectionFactor psi initial coefficient ≤
    (p.U : ℝ)

/-- The common assumptions from both parts of Theorem 2, including the conditions (30), (31),
and (33). -/
structure CommonCertificate (p : Params) (q : ℕ) : Prop where
  /-- The integer parameters satisfy their domain constraints. -/
  admissible : p.Admissible
  /-- The complete post-initialization budget satisfies Q ≤ N/U. -/
  budget : p.QueryBudget q
  /-- Binh satisfies (30). -/
  nu_choice : p.NuChoice
  /-- The initial potential is at most half the account threshold by (31). -/
  initial_potential : 2 * (p.N : ℝ) / (p.mu : ℝ) ^ p.d ≤ (p.Gamma : ℝ)
  /-- The endpoint-pair bound fits in U by (31). -/
  endpoint_budget : p.Theta ≤ p.U
  /-- The disjoint-path tail fits the event budget by (33). -/
  flow : 2 ^ (2 * p.n + p.lambda + 3) * p.h.factorial * (2 * p.Pi ^ 2) ^ p.h ≤ p.U ^ p.h

/-- The fixed-target certificate of Theorem 2(1), also given in (A.4). -/
structure PreCertificate (p : Params) (q : ℕ) : Prop extends p.CommonCertificate q where
  /-- The separation budget in Theorem 2(1). -/
  separation : p.lambda + 2 ≤ 2 * p.s
  /-- The unweighted drift inequality (32). -/
  drift : 4 * p.driftNumerator ≤ p.Gamma * p.U
  /-- The fixed-target crowding inequality in Theorem 2(1). -/
  occupancy : 6 * p.Pi * (p.Psi + p.Pi) ≤ p.nu * p.U
  /-- The fixed-target instance of (34). -/
  intersection : p.IntersectionCondition p.Psi 4 p.graftCoefficient

/-- The common-threshold certificate of Theorem 2(2) for an original of at most `L` padded
blocks. Both sides use C = 2 Bpot + 2 L from (24). -/
structure SPRCertificate (p : Params) (q L : ℕ) : Prop extends p.CommonCertificate q where
  /-- The separation budget in Theorem 2(2). -/
  separation : p.lambda + 4 ≤ 2 * p.s
  /-- The original has room for L + 1 distinct capacities. -/
  length_space : L + 1 ≤ p.N
  /-- The original phase's length allowance fits the budget scale N/U. -/
  length_budget : L * p.U ≤ p.N
  /-- The unweighted drift inequality (32). -/
  drift : 4 * p.driftNumerator ≤ p.Gamma * p.U
  /-- The common-threshold crowding inequality of Theorem 2(2). -/
  occupancy : 12 * p.Pi * p.sprPsi L ≤ p.nu * p.U
  /-- The capacity collision term (9) fits the event budget. -/
  collision : 2 ^ (p.lambda + 2) * L * (L + 1) ≤ p.N
  /-- The instance of (34) with the common threshold and L original blocks allowed. -/
  intersection : p.IntersectionCondition (p.sprPsi L) ((L : ℝ) + 4) p.graftCoefficient

/-- The fixed-target inequalities (A.4) with the weighted graft coefficient J and drift
numerator D from (A.3). -/
structure WeightedPreCertificate (p : Params) (q : ℕ) (theta : ℝ) : Prop
    extends p.CommonCertificate q where
  /-- The weight θ is strictly positive. -/
  theta_pos : 0 < theta
  /-- The separation budget in (A.4). -/
  separation : p.lambda + 2 ≤ 2 * p.s
  /-- The drift inequality in (A.4) with D from (A.3). -/
  drift : 4 * p.weightedDriftNumerator theta ≤ (p.Gamma : ℝ) * (p.U : ℝ)
  /-- The crowding inequality at the fixed-target threshold C₀. -/
  occupancy : 6 * p.Pi * (p.Psi + p.Pi) ≤ p.nu * p.U
  /-- The intersection condition in (A.4) with the weighted J. -/
  intersection : p.IntersectionCondition p.Psi 4 (p.weightedCoefficient theta)

/-- The common target 2^(-λ-3) for each numerical tail. -/
def tailBudget (p : Params) : ℝ := ((2 : ℝ) ^ (p.lambda + 3))⁻¹

/-- The coupling separation expression of equation (8). -/
def separationTail (p : Params) (q : ℕ) : ℝ :=
  (q : ℝ) * ((q : ℝ) - 1) / (2 * (p.N : ℝ) ^ 2)

/-- The bound (22) after weakening its exponential factor to 2^(−Binh/8). -/
def barrierTail (p : Params) : ℝ :=
  2 * (p.N : ℝ) * ((p.N : ℝ) + 1) ^ p.Pi * (2 : ℝ) ^ (-(p.nu : ℝ) / 8)

/-- The union of (23) over both directions and all N lines at the common threshold. -/
def occupancyTail (p : Params) (q psi : ℕ) : ℝ :=
  2 * (p.N : ℝ) * ((q.choose p.nu : ℝ) *
    ((p.Pi : ℝ) * ((psi : ℝ) + (p.Pi : ℝ)) / (p.N : ℝ)) ^ p.nu)

/-- The disjoint-path expression of equation (14). -/
def flowTail (p : Params) : ℝ :=
  (p.N : ℝ) ^ 2 * (p.h.factorial : ℝ) * (2 * (p.Pi : ℝ) ^ 2 / (p.U : ℝ)) ^ p.h

/-- The intersection expression of equation (29), also used with the stated replacements. -/
def intersectionTail (p : Params) (psi : ℕ) (initial coefficient : ℝ) : ℝ :=
  ((psi : ℝ) / (p.U : ℝ)) * p.intersectionFactor psi initial coefficient

/-- The original-capacity collision expression of equation (9). -/
def collisionTail (p : Params) (ell : ℕ) : ℝ :=
  (ell : ℝ) * ((ell : ℝ) + 1) / (2 * (p.N : ℝ))

end

end Params

end JH.Parameters
