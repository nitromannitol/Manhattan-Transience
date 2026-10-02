# ManhattanAudit Comparator Surface

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
challenges (and in each pair's `SolutionBasic.lean`): the sites and directed lines of `ℤ²`, the fair-coin environment
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

Each pair has four files: `Challenge.lean`, `SolutionBasic.lean`, `Solution.lean` and
`comparator.json`.  `SolutionBasic.lean` imports only Mathlib and is a verbatim,
mechanical copy of the vocabulary block of the pair's `Challenge.lean`.  `Solution.lean`
imports the repository together with its own `SolutionBasic.lean` and its own bridge
(`Support/TransienceBridge.lean`, `Support/AnnealedGreenBoundBridge.lean`), and proves the
byte-identical statement from the corresponding theorem of `Manhattan/MainTheorems.lean`
(see [`DESIGN.md`](DESIGN.md)).

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash ManhattanAudit/check_standalone.sh ManhattanAudit/Transience/Challenge.lean
bash ManhattanAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that, in each pair, the vocabulary
block of `Challenge.lean` and of `SolutionBasic.lean` is byte-identical.  The solutions
build with

```bash
lake build ManhattanAudit
```

and, with `leanprover/comparator`, from the repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ManhattanAudit/Transience/comparator.json
```

expecting `Your solution is okay!`.

**Status.**  Both solutions build.  `leanprover/comparator` accepts both pairs, with the
Lean kernel and with the independent nanoda kernel; see
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and reproduction
steps.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
the same check on request.
