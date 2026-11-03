# Verification notes

Prepared on 3 November 2026.

## Source changes

The publication folder contains the complete 55-module certificate, the
three original version/build configuration files, and separate verification
files in `checks/`. The original project and this publication copy include
the same nonempty-alphabet repair.

The repair adds `[Nonempty Alphabet]` to the dense Max-4-CSP solver contract
and its associated fields and procedure. The concrete reduction proves that
each disk-net alphabet is nonempty: the disk contains zero when its radius
is nonnegative, so its covering net has a point. Solver calls use this proof.
The final optimization and weak-membership conclusions are unchanged.

This excludes a previously invalid instantiation with one variable and an
empty alphabet, which would require a function `Unit → Empty`.

## Environment

- Lean: `4.32.1`, commit `f054605aea4b840552cca2e725580bffd1e1b704`.
- Mathlib: `v4.32.1`, commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- All nine local dependency revisions matched `lake-manifest.json` before
  verification.

## Recorded checks

All checks passed with the pinned Lean version on 3 November 2026:

| Check | Result |
| --- | --- |
| Full `lake build` | Passed; 8,710 build jobs, zero errors |
| Rebuild after the repair | All six changed modules and their dependents rebuilt; 31 project modules compiled |
| `lake env lean checks/AlphabetRegression.lean` | Passed all five boundary checks |
| `lake env lean checks/MainAxioms.lean` | Both main theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound` |
| Source correspondence | All 60 source/configuration/check files matched the tested project byte for byte |

The full build reports 82 existing style/linter warnings. The deliberate
rejection tests report four unused-variable warnings, since rejected terms
do not become part of the resulting proofs. There are no proof errors.
No `sorry` or new axiom declaration was added by the repair.

The two main theorem reports are:

```text
QuantumSep.randomizedUnitProductOptimization_main:
  [propext, Classical.choice, Quot.sound]
QuantumSep.randomizedSeparableWeakMembership_main:
  [propext, Classical.choice, Quot.sound]
```

## Interpretation

The alphabet regression check confirms that the solver and its procedure
reject an empty alphabet. It also confirms that an empty set of variables
is still permitted when the alphabet is nonempty.

The repair removes the demonstrated empty-alphabet contradiction. It does
not prove the existence of the four external contracts. They remain explicit
theorem hypotheses and therefore do not appear in `#print axioms` reports.
The formalization uses noncomputable mathematical procedures and an exact
real-RAM runtime model, rather than a finite-precision executable solver.

Verification used an isolated local copy with the existing pinned dependency
artifacts and caches for unchanged project modules. Artifacts for the six
modified modules were removed before the full build, and Lake rebuilt their
dependents. The verified build cache was then copied back to the original
project. A fresh checkout on GitHub is a separate check and has not yet run;
the included workflow will make that check available after upload.

## Packaging checks

All 55 certificate modules are reachable from the root `QuantumSep.lean`
import. The publication folder contains no `.lake` directory, compiled Lean
objects, dependency checkout, local symbolic link, editor cache, macOS
metadata, or manuscript draft. Dependencies are restored from the committed
manifest.
