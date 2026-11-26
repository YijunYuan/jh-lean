# Lean formalization of the JH security bounds

This is the Lean companion to *Near-$n$-Bit Preimage and Second-Preimage
Security of the JH Mode*. The library covers the adaptive oracle comparison,
the graph and probability estimates behind Theorem 2, the rounded explicit
preimage bound, the random-message target reduction, and the asymptotic
optimum of the weighted fixed-target preimage certificate at advantage one
half. The code is distributed under Apache-2.0. [License](LICENSE)

## Build and verify

Install Elan and Git. This revision pins Lean **4.36.0** and mathlib
**v4.36.0** at commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
The Lake manifest records the full dependency lock. Run these commands
from the repository root. [Elan installation](https://lean-lang.org/install/)

```sh
lean --version
lake exe cache get
lake --wfail build
lake lean JH/Audit.lean
```

The PowerShell verifier also checks the frozen file hashes and allows only
`propext`, `Classical.choice`, and `Quot.sound` in the audit reports.

```sh
pwsh -File ./verify.ps1
```

For an offline check, pass `-CacheRoot` with the path to a Lake packages
directory containing compiled imports at the pinned revisions.
[Dependency lock](lake-manifest.json) · [Verifier](verify.ps1)

## Read the proofs

```lean
import JH

#check JH.preimage_finite
#check JH.second_preimage_finite
#check JH.preimage_explicit_sqrt
#check JH.Parameters.WeightedOptimality.loss_asymptotic
```

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1, directed vertex Menger | `JH.Graph.directed_vertex_menger`. [Proof](JH/Graph/Menger.lean) |
| Lemmas 1 and 2, residual endpoints and a path through the fresh record | `JH.Graph.endpoint_support_bounds` and `JH.Graph.uniform_new_path_probability`. [Endpoints](JH/Connectivity/Endpoints.lean) · [Shift test](JH/Connectivity/ShiftTest.lean) |
| Lemma 3, too many disjoint residual paths | `JH.Graph.FlowTail.conditional_test` and `JH.Graph.FlowTail.first_stop_bound`. [Conditional estimate](JH/Connectivity/FlowTailBounds.lean) · [Stopping bound](JH/Connectivity/FlowTail.lean) |
| Theorem 2(1), fixed-target preimage bound | `JH.preimage_finite`. [Statement](JH/PreimageSpec.lean) · [Proof](JH/Preimage.lean) |
| Theorem 2(2), fixed-message second-preimage bound with the common threshold | `JH.second_preimage_finite`. [Statement](JH/SecondPreimageSpec.lean) · [Proof](JH/SecondPreimageBound.lean) |
| Equation (39) and the square-root choice that follows it | `JH.Parameters.uniform_parameter_feasibility` constructs the general certificate. `JH.preimage_explicit_sqrt` gives the bound at the rounded square-root parameters. [Construction](JH/Parameters/Uniform.lean) · [Bound](JH/Preimage.lean) |
| Appendix A.3–A.4, weighted fixed-target preimages | `JH.preimage_weighted_finite`, `JH.Analysis.theta_optimal`, and `JH.Parameters.WeightedOptimality.loss_asymptotic`. [Finite bound](JH/Preimage.lean) · [Optimal weight](JH/Analysis/Convex.lean) · [Loss](JH/Parameters/WeightedOptimality.lean) |
| Section 1.2, target obtained by hashing a uniform message | `JH.RandomTarget.randomTarget_reduction`. [Proof](JH/RandomTarget.lean) |

In the finite statements, Lean's `q` is the paper's total budget
$Q=q+L_\alpha$. It counts adversary queries and candidate verification. For
second preimages this budget starts after disclosure. The complete coupling
allows $Q+\ell(M)$ accesses, including evaluation of the original message.
The fixed-target theorem gives the $5\cdot 2^{-\lambda-3}$ bound in (A.5),
charging one of its five shares for the separation term $\binom{Q}{2}/N^2$.
The common-threshold second-preimage theorem gives $6\cdot 2^{-\lambda-3}$.
Both upper bounds are uniform over admissible strategy or tape laws.
[First-stop combination](JH/Probability/FirstStop.lean) · [Second-preimage coupling](JH/SecondPreimage/Coupling.lean)

The manuscript and the library use `JH.Graph.directed_vertex_menger` for
the directed Menger theorem. [Menger theorem](JH/Graph/Menger.lean)

| Paper | Lean parameter |
| --- | --- |
| $B_{\mathrm{path}}$, $B_{\mathrm{ver}}$, $B_{\mathrm{pair}}$ | `Params.pi`, `Params.Pi`, `Params.Theta` |
| $B_{\mathrm{inh}}$, $B_{\mathrm{pot}}$ | `Params.nu`, `Params.Gamma` |
| $C_0=2B_{\mathrm{pot}}$ | `Params.Psi` |
| $C=2B_{\mathrm{pot}}+2L$ | `Params.sprPsi L` |

The joint target-column estimate of Theorem 3 and the explicit
second-preimage parameter choice of (40) are proved in the manuscript.
The paper's separate exact-arithmetic checker evaluates its numerical
certificates. The formalization guide traces the modules in paper order
and gives the detailed parameter correspondence. [Formalization guide (Chinese)](FORMALIZATION.md)

Module summaries, docstrings, and comments on key proof steps follow the
mathlib guidance for documenting mathematical content and making proofs
easier to review. [Documentation style](https://mathlib.org/contribute/doc.html) ·
[Pull request review guide](https://mathlib.org/contribute/pr-review.html)
