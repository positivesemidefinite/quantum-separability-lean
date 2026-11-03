# Quantum separability in Lean

Lean 4 sources for the algorithmic results associated with the manuscript
*Quantum Separability in Polynomial Time* by Giulio Malavolta.

The main Lean theorems derive their conclusions from four explicit external
contracts, described below. The existence of those contracts is not proved
in this repository.

The project is a mathematical formalization of randomized procedures and
runtime bounds in an exact real-RAM model. Many definitions are
`noncomputable`; this repository does not supply a numerical solver or a
finite-precision implementation.

## Main theorem statements

Both statements take the explicit parameter
`assumptions : QuantumSep.AllowedAssumptions`.

- **Product optimization:**
  [`QuantumSep.randomizedUnitProductOptimization_main`](QuantumSep/PhysicalOptimization.lean).
  For positive dimension and additive accuracy, and a Hermitian bipartite
  matrix of Frobenius norm at most one, the stated procedure always returns
  two unit vectors. Its product expectation is within the requested additive
  error of every competing unit product pair with probability at least
  `2/3`. The stated runtime bound is polynomial in the local dimension for
  each fixed accuracy.
- **Separable weak membership:**
  [`QuantumSep.randomizedSeparableWeakMembership_main`](QuantumSep/WeakMembershipMain.lean).
  For positive dimension and gap, and a Hermitian input in the Frobenius unit
  ball, the statement constructs a probability law and measurable Boolean
  decision. It accepts separable inputs with probability at least `2/3` and
  accepts inputs at distance strictly greater than the gap from every
  separable state with probability zero. Its stated runtime bound is
  polynomial in the local dimension for each fixed gap.

These statements concern the equal-local-dimension bipartite setting encoded
by `Fin d`. They do not certify every claim in the manuscript.

## External assumptions

[`AllowedAssumptions`](QuantumSep/PaperInterfaces.lean) has four fields:

1. efficient exact Haar-random unitary sampling;
2. a dense Max-4-CSP approximation scheme;
3. degree-two Gaussian hypercontractivity;
4. an exact real-RAM arithmetic model.

The algorithmic contracts are specified in
[`AlgorithmicInterfaces.lean`](QuantumSep/AlgorithmicInterfaces.lean), and
the Gaussian contract and combined assumptions in
[`PaperInterfaces.lean`](QuantumSep/PaperInterfaces.lean).
The CSP contract requires a nonempty alphabet. The reduction proves this
condition for its disk-net alphabets before invoking the solver.

## Verify locally

Install Lean using the [official installation guide](https://lean-lang.org/install/).
Open the whole repository folder, containing `lakefile.toml`, in your editor.
From a terminal in that folder, run:

```bash
lake exe cache get
lake build
lake env lean checks/AlphabetRegression.lean
lake env lean checks/MainAxioms.lean
```

The first command downloads precompiled Mathlib dependencies; the second
checks the project. The remaining commands check the solver's alphabet
boundary and print the two main theorems' axiom dependencies.
Explicit theorem hypotheses, including `AllowedAssumptions`, do not appear
in that axiom list.

The version files are part of the certificate:

| Component | Pinned version |
| --- | --- |
| Lean | `v4.32.1` in `lean-toolchain` |
| Mathlib | `v4.32.1` in `lakefile.toml` |
| Mathlib commit | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| Transitive dependencies | Exact revisions in `lake-manifest.json` |

Keep these files together. Updating dependencies changes the verification
environment. See [Verification notes](docs/VERIFICATION.md) for the recorded
checks and their limits.

## Source guide

| Subject | Starting points |
| --- | --- |
| All project imports | [`QuantumSep.lean`](QuantumSep.lean) |
| Public optimization and membership statements | [`PhysicalOptimization.lean`](QuantumSep/PhysicalOptimization.lean), [`WeakMembershipMain.lean`](QuantumSep/WeakMembershipMain.lean) |
| Assumptions and procedure model | [`PaperInterfaces.lean`](QuantumSep/PaperInterfaces.lean), [`AlgorithmicInterfaces.lean`](QuantumSep/AlgorithmicInterfaces.lean) |
| Matrix objective and separable-state geometry | [`MatrixPrelim.lean`](QuantumSep/MatrixPrelim.lean), [`MatrixObjective.lean`](QuantumSep/MatrixObjective.lean), [`SeparableGeometry.lean`](QuantumSep/SeparableGeometry.lean) |
| Gaussian and Haar analysis | `QuantumSep/Gaussian*.lean`, `QuantumSep/Haar*.lean` |
| Discretization and CSP reduction | [`Discretization.lean`](QuantumSep/Discretization.lean), [`MatrixCSPReduction.lean`](QuantumSep/MatrixCSPReduction.lean) |
| Optimizer and runtime composition | [`ProductOptimizationAlgorithm.lean`](QuantumSep/ProductOptimizationAlgorithm.lean), [`MainTheorem.lean`](QuantumSep/MainTheorem.lean), [`RuntimeAnalysis.lean`](QuantumSep/RuntimeAnalysis.lean) |
| Adaptive weak membership | [`AdaptiveOptimization.lean`](QuantumSep/AdaptiveOptimization.lean), [`AdaptiveWeakMembership.lean`](QuantumSep/AdaptiveWeakMembership.lean), [`WeakMembershipRuntime.lean`](QuantumSep/WeakMembershipRuntime.lean) |

## Automatic checks on GitHub

The included [workflow](.github/workflows/lean.yml) builds the project, checks
the alphabet boundary, and prints the theorem axiom dependencies on pushes
and pull requests. It can
also be started manually from the repository's **Actions** tab. It uses the
official [Lean action](https://github.com/leanprover/lean-action).

A green check records successful compilation and regression checks. The
four external contracts remain hypotheses of the main theorem statements.

## License

No license has been selected for the project sources. The repository owner
can add a `LICENSE` file when choosing the terms of reuse. Lean, Mathlib, and
the other dependencies retain their own licenses and are downloaded
separately.
