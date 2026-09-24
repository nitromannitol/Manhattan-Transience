# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the two main
theorems of the formalization of *The randomly oriented Manhattan lattice in 2D
is transient* (Bou-Rabee and Peres): Theorem 1.1 and Theorem 1.2.  Each
comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `Transience/` | Theorem 1.1, `thm:main` | `ManhattanAudit.transience` | `Manhattan.transience` |
| `AnnealedGreenBound/` | Theorem 1.2, `thm:annealed` | `ManhattanAudit.annealed_green_bound` | `Manhattan.annealed_green_bound` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in both
challenges: the sites and directed lines of `ℤ²`, the fair-coin environment
law, the quenched one-step and `n`-step kernels, the discrete Green series, the
rate-two Poisson weights, and the quenched and annealed continuous-time
kernels.

## What Is Checked

Neither theorem has a hypothesis: no result from the literature is assumed, so
the challenges carry none.

- **`Transience`** (Theorem 1.1): for almost every environment under the
  product fair-coin law, `discreteGreen ω x < ∞` at every site `x`, where
  `discreteGreen ω x = ∑' n, p^ω_n(x, x)` in `ℝ≥0∞`.
- **`AnnealedGreenBound`** (Theorem 1.2): there is `C < ∞` with
  `∫⁻ t in Ici 0, ofReal (exp (-λ t)) * annealedContinuousKernel t 0 0 ≤ C` for
  every `λ ∈ (0, 1]`, and `∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞`.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorems, in the namespace `ManhattanAudit`.

| Challenge declaration | Repository source |
| --- | --- |
| `Axis`, `Site`, `LineIndex`, `Orientation`, `Orientation.sign`, `Environment`, `transverseCoordinate`, `lineAt`, `basisStep`, `directedNeighbor`, `fairCoinPMF`, `fairCoin`, `environmentLaw` | `Manhattan/Model/Basic.lean` |
| `followPath`, `oneStepKernel`, `nStepKernel` | `Manhattan/Model/Kernel.lean` |
| `discreteGreen` | `Manhattan/Model/MainTheorem.lean` |
| `rateTwoPoissonWeight`, `continuousKernel`, `annealedContinuousKernel` | `Manhattan/Model/Subordination.lean` |

The statement of `AnnealedGreenBound` is the body of the repository definition
`Manhattan.AnnealedGreenBound` (`Manhattan/Model/Subordination.lean`) with
every repository name replaced by its vocabulary copy.

## Solutions

Each `Solution.lean` imports the repository together with
`Audit/Support/Vocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `Manhattan/MainTheorems.lean` through the bridges in
`Audit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`Audit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`Audit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and
mentions no constant of the repository namespace `Manhattan`, and prints the
axioms of each solution theorem.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/Transience/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in both challenges and in `Audit/Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build Audit.StatementRegression
```

which prints, for each of the two theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  Both solutions build, and the statement regression and the axiom
prints pass locally.  `leanprover/comparator` itself was run on both pairs on
2026-09-24 at commit `34b9cb3`, and both passed with the Lean kernel and with
the independent nanoda kernel; see [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md)
for the full results and reproduction steps.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
the same check on request.
