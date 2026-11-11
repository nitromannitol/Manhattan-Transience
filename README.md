# The randomly oriented Manhattan lattice in 2D is transient

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Yuval Peres,
> *The randomly oriented Manhattan lattice in 2D is transient*,
> [arXiv:2609.07621](https://arxiv.org/abs/2609.07621).

The pinned manuscript, its bibliography and the unmodified arXiv source are included under
[`paper/`](paper/). The 2 main theorems of the paper are proved, in the form in which its
introduction states them, **for the randomly oriented Manhattan lattice of the paper**, with no
hypothesis and no result from the literature assumed.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
the shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`), a library of lattice probability and potential theory.

[![CI](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml)

## What is proved

Independently orient each horizontal and vertical line of `ℤ²` by a fair coin. A walker
chooses one of the two lines through its current position with equal probability and takes one
step in the direction of that line. Theorem 1.1 of the paper says that for almost every
environment the walk is transient: the quenched Green series `∑_{n ≥ 0} p^ω_n(x, x)` is finite
at every site `x`. Theorem 1.2 is the annealed estimate it is deduced from: for the
continuous-time walk with total jump rate two, the Laplace transforms
`∫_0^∞ e^{-λt} p̄_t(0,0) dt` of the annealed return probability are bounded uniformly in
`λ ∈ (0, 1]`, and hence `∫_0^∞ p̄_t(0,0) dt < ∞`. The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The 2 main results, formalized as stated in the introduction of the paper, are collected in
[`Manhattan/MainTheorems.lean`](Manhattan/MainTheorems.lean). Each is proved by direct
application of its certified counterpart in `Manhattan/Frozen/Main/`, and neither has a
hypothesis.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `thm:main`) | `Manhattan.transience` | the quenched Green series is finite at every site, for almost every environment |
| Theorem 1.2 (label `thm:annealed`) | `Manhattan.annealed_green_bound` | the Laplace transforms of the annealed return probability are bounded uniformly in `λ ∈ (0, 1]` |

**Theorem 1.1 (transience, `thm:main`).** For almost every environment `ω`,
`∑_{n ≥ 0} p^ω_n(x, x) < ∞` for every `x ∈ ℤ²`; that is, the walk is transient in almost every
environment.

In Lean, `Manhattan.transience` states that for almost every environment under
`Manhattan.environmentLaw`, the product fair-coin law, every site `x : Manhattan.Site` has
`Manhattan.discreteGreen ω x < ∞`, where `discreteGreen ω x = ∑' n, p^ω_n(x, x)` in `ℝ≥0∞`.
Its statement is byte-faithful to `Manhattan.Frozen.Main.theorem_1_1`.

**Theorem 1.2 (annealed Green function bound, `thm:annealed`).**

1. *Uniform bound.* There is `C < ∞` with `∫_0^∞ e^{-λt} p̄_t(0,0) dt ≤ C` for all
   `λ ∈ (0, 1]`.
2. *Finiteness.* Hence `∫_0^∞ p̄_t(0,0) dt < ∞`.

In Lean, `Manhattan.annealed_green_bound` states that there is `C < ∞` in `ℝ≥0∞` with
`∫⁻ t in Ici 0, ofReal (exp (-λ t)) * annealedContinuousKernel t 0 0 ≤ C` for every
`λ ∈ (0, 1]`, and `∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞`. The certified
statement `Manhattan.Frozen.Main.theorem_1_2` is the proposition
`Manhattan.AnnealedGreenBound`, and the statement displayed in `MainTheorems.lean` is the body
of that definition.

Besides the two main theorems, the repository formalizes the statements of the pinned
manuscript that the proof passes through: the generator and Green decomposition in
Fourier–Walsh coordinates (Proposition 2.1), the variational upper bound (formula (15)), the
fixed-frequency estimate (Proposition 2.2), the degree-one and degree-three estimates
(Lemma 4.1 and Proposition 4.2), and the Fourier–Walsh calculations of Section 5 at the
concrete competitor. Theorem 1.1 is also proved a second time, along the shorter argument of
the arXiv version (`Manhattan/V4/`).

## Corrections to the published version

The formalization follows `paper/manuscript.tex`, a corrected text of the paper. It is a
different text from [arXiv:2609.07621v1](https://arxiv.org/abs/2609.07621v1), with a different
proof of the frequency bound, and it carries five corrections.
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) compares the two texts result by
result and lists every change against the arXiv version.

## Standing assumptions and scope

1. **Every theorem is about the one model of the paper.** The model has no parameter. An
   environment `ω` orients each horizontal and vertical line of `ℤ²` by a fair coin; the
   environment law `Manhattan.environmentLaw` is Mathlib's `Measure.infinitePi` of fair coins,
   and the sites are `Manhattan.Site`. Theorem 1.1 holds for almost every environment under
   this law, and Theorem 1.2 for the annealed continuous-time kernel
   `Manhattan.annealedContinuousKernel`. Neither theorem has a hypothesis.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The two main theorems use no axiom beyond `propext`,
   `Classical.choice` and `Quot.sound`. The main theorems rely on no unproved result:
   everything they use, including the facts the paper cites from the literature, is available
   in mathlib or Lattice-Probability or is proved in this repository;
   [`ASSUMPTIONS.md`](ASSUMPTIONS.md) records that no registered statement is assumed.
3. **What is not formalized.** The open questions of the last section of the paper, the
   figures, and the survey of related work in the introduction.
4. **Modelling conventions.**
   - An environment gives one orientation to each line, indexed by its axis and its
     transverse coordinate, rather than the paper's redundant `ω(z, i)` with the condition
     that `ω(z, i)` does not depend on `z_i`.
   - The quenched `n`-step kernel is the path count `2⁻ⁿ · #{axis words of length n from z to z'}`,
     which is the probability under the quenched walk law.
   - The continuous-time kernel is defined by rate-two Poisson subordination of the discrete
     kernel, not as the transition function of a continuous-time Markov process; the generator
     identity with equation (2) is proved (`Manhattan/Model/Kernel.lean`).
   - Finiteness of a nonnegative series or integral is stated as its `ℝ≥0∞` value being
     `< ∞`.
   - Homogeneous Walsh spaces use finite sets of line indices. The degree-three correction,
     whose ordered coefficient can contain coincident rows, is built on an ordered carrier and
     projected, with the projection error bounded.
5. **Numerical constants.** The arXiv version states Theorem 1.2 and Proposition 6.1 with the
   constant `2048` and Lemma 5.1 with the constant `16`; the formal statements have an
   unspecified constant, as `paper/manuscript.tex` does, the formal proofs reach them along a
   lossier route, and the constant of Lemma 5.1 is discharged below `670` by
   `Manhattan.V4.v4ConstantSplit_lt`.
6. **Statements without a formal counterpart.** Every numbered statement registered in the
   manifest is machine-checked, but the numerals of the arXiv version are not. The pinned
   manuscript states what the Lean statements state;
   [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) records every difference
   between it and the arXiv version, whose unmodified source is
   [`paper/arxiv/`](paper/arxiv/). [`VERIFICATION.md`](VERIFICATION.md) compares the Lean
   statements with the arXiv version, statement by statement, marked EXACT, EQUIVALENT or
   WEAKER, and [`CORRESPONDENCE.md`](CORRESPONDENCE.md) is the paper-to-Lean map, node by node.

## Registered statements

The manifest [`ledger/manifest.yaml`](ledger/manifest.yaml) registers 76 statements, all in the
state `PROVED`. The pinned source is [`paper/manuscript.tex`](paper/manuscript.tex), whose
SHA-256 is recorded in [`paper/SOURCE_PIN.txt`](paper/SOURCE_PIN.txt) and in the manifest. A
registered statement's text between the lines `-- FROZEN-STATEMENT-BEGIN` and
`-- FROZEN-STATEMENT-END` is pinned by the SHA-256 of those bytes in the manifest, together
with the line range of the paper it transcribes; the proof after the end marker is not pinned.
In the manifest, a registered statement is `PROVED` when its axiom closure is exactly the three
standard axioms.

The principal registered statements, with their manifest identifiers and the lines of the
pinned source they transcribe:

| Manifest ID | Paper result | Pinned source |
|---|---|---|
| `thm-main` | Theorem 1.1, almost-sure summability of quenched returns | `manuscript.tex:192` |
| `thm-annealed` | Theorem 1.2, annealed Green-function bound | `manuscript.tex:207` |
| `prop-generator-v2` | Proposition 2.1, pointwise frequency generator and Green decomposition | `manuscript.tex:555-607` |
| `var-ineq` | Formula (15), upper-bound direction only | `manuscript.tex:626-638` |
| `prop-frequency` | Proposition 2.2, fixed-frequency estimate | `manuscript.tex:644` |
| `lem-onecoin-v3` | Lemma 4.1, degree-one integral estimates and finiteness certificates | `manuscript.tex:907` |
| `prop-key` | Proposition 4.2, degree-three correction estimate | `manuscript.tex:1007` |
| `eq-hsym-concrete` | (Hsym), equation (20), the degree-`n` multiplier | `manuscript.tex:743-751` |
| `lem-raise-concrete-raising` | Lemma 5.1, raising side, equation (45) | `manuscript.tex:1179-1191` |
| `lem-raise-concrete-adjoint` | Lemma 5.1, adjoint side | `manuscript.tex:1179-1191` |
| `lem-four-concrete-raising-energy` | Lemma 5.2, operator half, equation (47) | `manuscript.tex:1200-1207` |
| `lem-four-concrete-competitor` | Lemma 5.2 at the concrete competitor | `manuscript.tex:1200-1207` |
| `lem-distinct-concrete-frequency` | Lemma 5.3, raw frequency side only | `manuscript.tex:1212-1221` |
| `lem-correction-calculation-concrete` | Lemma 5.4, the raw mixed residual | `manuscript.tex:1305-1400` |
| `eq-e-summand-one` … `-four` | the four summands of the objective (22) | `manuscript.tex:765-772` |
| `eq-construction-sector-energy` | `E_p(f_p,k_p) ≤ C √L`, third display of (25) | `manuscript.tex:785-790` |

## Guarantees

- **No `sorry`.** The sources of the library contain no `sorry`, `admit` or `axiom` token
  outside comments. Each Mathlib-only comparator challenge under
  [`ManhattanAudit/`](ManhattanAudit/) contains one intentional statement-level `sorry`,
  which the corresponding solution file proves.
- **Standard axioms only.** The comparator accepts, with only `propext`, `Classical.choice`
  and `Quot.sound` permitted, a solution for each of the 2 main theorems that is proved from
  `Manhattan.transience` and `Manhattan.annealed_green_bound` through a bridge, so neither
  theorem rests on any other axiom.
  [`Manhattan/Meta/AxiomsAudit.lean`](Manhattan/Meta/AxiomsAudit.lean) prints the axioms of
  every proved node, and [`Manhattan/Certificate.lean`](Manhattan/Certificate.lean) restates
  the main results in self-contained form and prints the axioms each rests on. The
  axiom-audit and certificate steps of the [`build.yml`](.github/workflows/build.yml)
  workflow fail on `sorryAx` or on any other axiom, and `python3 tools/check_manifest.py`
  checks that no `axiom`, `admit` or `sorryAx` token occurs in the production tree.
- **Independent check of the statements.** Both main theorems are restated using only mathlib,
  with no project definition, in
  [`ManhattanAudit/Transience/Challenge.lean`](ManhattanAudit/Transience/Challenge.lean) and
  [`ManhattanAudit/AnnealedGreenBound/Challenge.lean`](ManhattanAudit/AnnealedGreenBound/Challenge.lean).
  Each challenge rebuilds the model from mathlib primitives (the sites and directed lines of
  `ℤ²`, the fair-coin environment law, the quenched one-step and `n`-step kernels, the discrete
  Green series, and the rate-two Poisson subordination that defines the continuous-time
  kernel). The solution file proves each restatement from the library through its own bridge
  in `ManhattanAudit/Support/`, over a verbatim copy of the challenge vocabulary in its own
  `SolutionBasic.lean`, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
  is proved, with only the three standard axioms, through independent implementations of the
  Lean kernel. See [`ManhattanAudit/README.md`](ManhattanAudit/README.md) and
  [`ManhattanAudit/COMPARATOR_RUNS.md`](ManhattanAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability at commit
  `bbe0b90a7cf0517db0578139aaab7f152edbc45e`, pinned in [`lakefile.lean`](lakefile.lean) and
  recorded, with mathlib's own dependencies, in [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `ef90fcdfb102b3f47407eb906b69bb44bd11feaa63609bc3dbf3272be3e0020a` of
  `paper/manuscript.tex`.

## Size

The library contains 229 Lean files with 56,782 physical lines, on top of mathlib and
Lattice-Probability. The count covers `Manhattan.lean` and `Manhattan/`. The comparator
sources (8 files, 1,124 lines) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
./bootstrap.sh       # first time: install the toolchain, lake exe cache get, lake build
lake build           # afterwards
```

`bootstrap.sh` runs `lake exe cache get` for the prebuilt mathlib, which requires the committed
[`lake-manifest.json`](lake-manifest.json) with its exact dependency revisions; do not run
`lake update`. Never run `lake clean`: it discards the mathlib build artifacts. Lattice-Probability
has no prebuilt cache, so the first build compiles it as well as the library. The results that
do not depend on the Manhattan model (the semigroup of a bounded generator and its Laplace
resolvent, the dissipative-skew pair and its coercive resolvents, Pólya's theorem in two
dimensions, the Nash inequality on `ℤ²` and the rate-two Poisson clock) come from
Lattice-Probability. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

`import Manhattan` loads the whole development, and `import Manhattan.MainTheorems` loads the
main theorems and what they use.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `bbe0b90a7cf0517db0578139aaab7f152edbc45e`.

To reproduce the axiom reports and build the certificate and the comparator libraries:

```bash
lake build Manhattan.Meta.AxiomsAudit   # print the axioms of the main theorems and every proved node
lake build Manhattan.Certificate        # the self-contained certificate of what is proved
lake build ManhattanAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3.8 or newer and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | each frozen statement's bytes match its recorded SHA-256, every file under `Manhattan/Frozen/` belongs to exactly one node, each node's recorded dependency-closure hash matches, and no `axiom`, `admit` or `sorryAx` token, and no unregistered `sorry`, occurs in the production tree |
| `python3 tools/check_warnings.py` | the build of `Manhattan` emits no warning other than the `sorry` warnings the manifest authorizes (it authorizes none) |
| `python3 tools/assumptions.py --check` | `ASSUMPTIONS.md` is current with the manifest |
| `lake env lean tools/lint_fast.lean` | the fast Mathlib environment linters pass on the whole library |
| `lake env lean tools/lint_simpnf.lean` | the `simpNF` linter passes (slow) |

## Running the comparators

Each comparator pair has a configuration `ManhattanAudit/<Pair>/comparator.json`, for `<Pair>`
one of `Transience` and `AnnealedGreenBound`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the independent nanoda kernel. The comparator
checks that the solution proves the challenge statement, compares their dependency closures,
and replays the proof with the Lean and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`ManhattanAudit/COMPARATOR_RUNS.md`](ManhattanAudit/COMPARATOR_RUNS.md)), and from the
repository root run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ManhattanAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the two pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library and checks the
manifest, the warnings, the linters, the certificate and the axiom reports; **Comparator
audit** checks both challenge/solution pairs. CI runs on pushes to `main` that change code or
build configuration, and Comparator audit only on request. Both workflows can be started
manually from the [Actions page](https://github.com/nitromannitol/Manhattan-Transience/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Manhattan.lean            the root module, importing the whole library
Manhattan/
  MainTheorems.lean       the main theorems, stated in full
  Certificate.lean        self-contained restatements of what is proved, with their axioms
  Frozen/                 the certified statement surface, one frozen statement per file:
                          Main/, Operator/, Estimates/, Glue/
  Model/                  sites, lines, the fair-coin environment, the kernels,
                          Poisson subordination
  Walsh/                  the Fourier–Walsh basis on environments and its grading
  Operator/               the generator in Fourier coordinates and the frequency
                          resolvent bound
  Library.lean            the operator objects re-exported from Lattice-Probability
  Estimates/              the degree-one and degree-three estimates
  Competitor/             the competitor and the obstruction to the raw frequency version
  Glue/                   the concrete competitor, the four summands, the assembly
                          of the main theorems
  V4/                     the second proof of Theorem 1.1, along the arXiv version
  Paper/                  further statements of the arXiv version
  Meta/                   AxiomsAudit.lean (the axiom report, compiled by `lake build`,
                          not imported by the root), Cone.lean
ManhattanAudit/           the mathlib-only restatements and their solutions
ASSUMPTIONS.md            the results assumed (none; generated)
CORRESPONDENCE.md         paper to Lean, node by node
VERIFICATION.md           statement-by-statement comparison with the arXiv version
ledger/manifest.yaml      one row per registered statement: hash, paper lines, state
paper/                    the pinned manuscript, its checksum, the unmodified arXiv
                          source (arxiv/) and CHANGES_FROM_ARXIV.md
tools/                    the checkers listed under Building
.github/workflows/        build.yml and comparator.yml
bootstrap.sh              first-time setup
formalization.yaml        models, tooling, cost and review disclosure
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes,
[arXiv:2609.07621](https://arxiv.org/abs/2609.07621), is joint work of Ahmed
Bou-Rabee and Yuval Peres.  To cite the formalization, use
[`CITATION.cff`](CITATION.cff).  This formalization is built on
[Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability); the
comparator audit in [`ManhattanAudit/`](ManhattanAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper sources in `paper/` are included for
reference and are not covered by the Apache license.
