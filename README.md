# The randomly oriented Manhattan lattice in 2D is transient

[![CI](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee and Yuval Peres,
> *The randomly oriented Manhattan lattice in 2D is transient*,
> [arXiv:2609.07621](https://arxiv.org/abs/2609.07621).

The paper proves that the random walk on the randomly oriented Manhattan lattice of `ℤ²` is
transient for almost every choice of the orientations. It also proves that the expected time the
walk spends at its starting point, averaged over the orientations, is finite. Both main
theorems are proved in Lean, with no hypothesis beyond the model of the paper. Nothing is assumed:
the results of other works that the proofs use are in mathlib, in the library Lattice-Probability,
or proved here. The library has no `sorry` and uses only the standard axioms.

## The paper

Orient each horizontal and each vertical line of `ℤ²` by an independent fair coin. These
orientations form the *environment* `ω`. A walker at `z`
chooses one of the two lines through `z` with probability 1/2 each, and takes one step in the
direction of that line. Redner introduced this walk as a model of transport in a random velocity
field. Transience was conjectured by Guillotin-Plantard, and the paper proves it.

One coin orients a whole line, so the environment has correlations of infinite range. The randomness
matters: for the alternating orientations the walk is recurrent.

Write `p^ω_n(z, z')` for the probability that the walk in the environment `ω` goes from `z` to `z'`
in `n` steps.

**Theorem 1.1.** For almost every environment `ω`, `Σ_{n ≥ 0} p^ω_n(x, x) < ∞` for every `x ∈ ℤ²`.
That is, the walk is transient in almost every environment.

The proof goes through continuous time. The continuous-time walk jumps along each of its two
outgoing edges at rate 1, so its transition probabilities are
`p^ω_t(z, z') = Σ_{n ≥ 0} e^{−2t} (2t)ⁿ p^ω_n(z, z')/n!`. Let `p̄_t(0, 0)` be the average of
`p^ω_t(0, 0)` over the environment.

**Theorem 1.2.** There is `C < ∞` with `∫_0^∞ e^{−λt} p̄_t(0, 0) dt ≤ C` for all `λ ∈ (0, 1]`, and
hence the annealed Green function `∫_0^∞ p̄_t(0, 0) dt` is finite.

The proof writes the Laplace transform of `p̄_t(0, 0)` through a variational formula, in Fourier
coordinates in space and Fourier–Walsh coordinates in the environment, and evaluates it at one
explicit function.

## The main theorems in Lean

The main theorems are stated in full in [`Manhattan/MainTheorems.lean`](Manhattan/MainTheorems.lean).
Neither has a hypothesis.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `Manhattan.transience` |
| Theorem 1.2 | `Manhattan.annealed_green_bound` |

```lean
theorem Manhattan.transience :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞

theorem Manhattan.annealed_green_bound :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
        ∫⁻ t in Ici 0,
          ENNReal.ofReal (Real.exp (-lambda * t)) *
            Manhattan.annealedContinuousKernel t 0 0 ≤ C) ∧
      ∫⁻ t in Ici 0, Manhattan.annealedContinuousKernel t 0 0 < ∞
```

How to read the statements:

- `Manhattan.Site` is `ℤ × ℤ`. An environment gives one orientation to each line, indexed by its
  axis and its transverse coordinate. The law `Manhattan.environmentLaw` is mathlib's
  `Measure.infinitePi` of fair coins.
- `Manhattan.discreteGreen ω x` is `Σ' n, p^ω_n(x, x)` in `ℝ≥0∞`. The kernel `p^ω_n(z, z')` is
  `2⁻ⁿ` times the number of axis words of length `n` that lead from `z` to `z'`, which is the
  probability under the quenched walk.
- `Manhattan.annealedContinuousKernel` is the average over the environment of the continuous-time
  kernel. That kernel is defined by the rate-two Poisson formula above, and its generator identity
  with equation (2) of the paper is proved.
- Finiteness of a nonnegative series or integral is stated as its value in `ℝ≥0∞` being `< ∞`.

They restate `Manhattan.Frozen.Main.theorem_1_1` and `Manhattan.Frozen.Main.theorem_1_2` of the
table below; the second is displayed with its defining proposition unfolded.

## All numbered results

The numbering is that of [`paper/manuscript.tex`](paper/manuscript.tex). Each row gives one Lean
declaration that proves the result; the names are in the namespace `Manhattan.Frozen`.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `Main.theorem_1_1` | Transience in almost every environment. |
| Theorem 1.2 | `Main.theorem_1_2` | The annealed Laplace transforms are bounded uniformly in `λ ∈ (0, 1]`. |
| Proposition 2.1 | `Operator.proposition_generator_v2` | The generator at frequency `p` is `S_p + A_p`, and the Laplace transform of `p̄_t(0, 0)` is the integral of `r_λ(p)` over the torus. |
| Formula (15), upper bound | `Operator.resolventQuadratic_le` | Every test function `g` bounds `r_λ(p)` from above. |
| Proposition 2.2 | `Estimates.proposition_frequency` | The frequency bound, with the gain `L_λ(p)^{3/2}`. |
| Lemma 3.1, (D2a) | `Paper.lowering_twoRow` | The two-row component of `D̃₂*k`. |
| Lemma 3.1, (D2b) | `Paper.lowering_mixed` | The mixed component of `D̃₂*k`. |
| Lemma 3.1, (D1), first formula | `Paper.lowering_degreeOne` | `D₀*f = −i sin(p₁) ∫ f dm`. |
| Lemma 3.1, (D1), second formula | `Paper.raising_twoRow` | The two-row component of `D̃₁f`. |
| Lemma 3.1, (D1), third formula | `Paper.raising_mixed` | The mixed component of `D̃₁f`. |
| Lemma 4.1 | `Estimates.lemma_one_coin_v3` | The estimates (a) to (d) for the degree-one coefficient `f_p`. |
| Proposition 4.2 | `Estimates.proposition_key` | A degree-three coefficient `k` with the bound (key), `≤ C √L`. |
| Lemma 5.1, (raise) | `Paper.orderedFourier_rawRaise` | The formula for the raising operator `D̃_n`, at every degree. |
| Lemma 5.1, factorization | `Paper.symCoeff_walshRaise` | `D_n = Π_{n+1} D̃_n Π_n`, at every degree. |
| Lemma 5.1, commutation | `Paper.offDiagonalProjection_comp_orderedMultiplier` | `Π_n` commutes with every continuous multiplier that is a function of `P`. |
| Lemma 5.2 | `Paper.lemma_four` | The bound (four) for every `k ∈ ℋ₃`, with `κ = 97`. |
| Lemma 5.3 | `Paper.lemma_distinct` | The error of the projection onto distinct row indices. |
| Lemma 5.4 | `Paper.lemma_correction_calculation` | The correction calculation for the competitor of Section 4. |

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps each of the 95 pinned statements (see
[Checking the proofs](#checking-the-proofs)) to the lines of the paper it states, with its hypotheses.

The arXiv text, [arXiv:2609.07621v1](https://arxiv.org/abs/2609.07621v1), has the same main
theorems, but a different proof of the frequency bound and a different numbering. Its unmodified
source is in [`paper/arxiv/`](paper/arxiv/). Its explicit constants are proved:

| arXiv:2609.07621v1 | Lean declaration |
| --- | --- |
| Theorem 1.2 with the constant `2048` | `Manhattan.Frozen.Paper.annealed_laplace_le_2048` |
| `∫_0^∞ p̄_t(0, 0) dt ≤ 2048`, the equation (green-explicit) | `Manhattan.Frozen.Paper.annealed_green_le_2048` |
| Proposition 6.1 with the constant `2048` | `Manhattan.Frozen.Paper.frequencyBound_2048` |
| Lemma 5.1 with the constant `16` | `Manhattan.Frozen.Paper.move1_objective_sixteen` |

The bound of Lemma 5.1 with `16` is proved for the profiles `φ = t/q` on `Γ_δ` that the proof of
Proposition 6.1 uses, not for every even `φ ∈ L²` that vanishes off `Γ_δ`. The arXiv argument is
also formalized in [`Manhattan/V4/`](Manhattan/V4/), which proves Theorem 1.1 a second time
(`Manhattan.V4.theorem_1_1_v4`). [`Manhattan/Paper/`](Manhattan/Paper/) proves Proposition 6.2 of the
arXiv version. It also proves the claim of its Problem 7.3: a random shift of the alternating
environment gives a stationary ergodic law under which the walk is recurrent.
[`VERIFICATION.md`](VERIFICATION.md) compares each numbered statement of the arXiv version with its
Lean statement.

## Corrections

The Lean statements follow [`paper/manuscript.tex`](paper/manuscript.tex), the text of the paper
numbered above. [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) compares it with the
arXiv text result by result, and lists the five corrections that it carries:

1. The continuous-time transition probabilities were used without a formula that identifies them;
   the formula by Poisson subordination is added.
2. The completeness of the Fourier–Walsh basis uses martingale convergence along an enumeration of
   the lines, so that the finite sets of signs exhaust all lines.
3. The coefficients of an element of `ℋ_n` are summed over ordered tuples of line indices, which
   gives the factor `n!` of the isometry (17).
4. The rank-one minimization (34) needs `∫_J dm/M < ∞` and a class of functions for the infimum;
   both are stated.
5. The proof that `Π_n` commutes with the multipliers that are functions of `P` treated each of
   them as a combination of translations, which holds only for trigonometric polynomials. The
   statement is restricted to continuous multipliers, which are the ones used, and proved by
   uniform approximation.

In `paper/manuscript.tex`, Theorem 1.2 has an unspecified constant where the arXiv text has `2048`.

## Scope

- **One model.** The model has no parameter, and every theorem is about it.
- **Formula (15).** The manuscript states that `r_λ(p)` equals an infimum, citing Theorem 4.1 of
  Komorowski, Landim and Olla. The proofs use only the upper bound, which is proved; the equality is
  not formalized.
- **Hypotheses of the lemmas.** Some lemmas are stated in the cases the proofs use. For example,
  (D2b) is stated for `k` symmetric in its two row frequencies. Lemma 5.4 assumes the hypotheses of
  Proposition 4.2, `b_p ≠ 0`, and an integrability condition that is proved when `p₁ ≠ 0`.
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) records the hypotheses of each statement.
- **Not formalized.** The open questions of the last section of `paper/manuscript.tex`, the
  figures, and the survey of related work in the introduction.

## Checking the proofs

- **No `sorry`.** The library contains no `sorry`, `admit` or `axiom`. Each comparator challenge
  under [`ManhattanAudit/`](ManhattanAudit/) has one intentional `sorry` at the statement, which the
  matching solution proves.
- **Standard axioms only.** [`Manhattan/Meta/AxiomsAudit.lean`](Manhattan/Meta/AxiomsAudit.lean)
  prints the axioms of the main theorems, of every pinned statement except two superseded forms,
  and of intermediate results: 135 reports, a count the CI workflow checks.
  [`Manhattan/Certificate.lean`](Manhattan/Certificate.lean) restates the main results in
  self-contained form and prints their axioms. Both steps fail on
  `sorryAx` or on any axiom other than `propext`, `Classical.choice` and `Quot.sound`.
- **Independent check of the statements.** Each main theorem is restated in a `Challenge.lean` that
  imports mathlib alone. It rebuilds the model from mathlib's primitives: the sites and lines, the
  environment law, the kernels, the Green series and the Poisson subordination. The matching
  `Solution.lean` proves it from the library through a bridge.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the standard axioms are used, and replays the proof with the Lean and NanoDa
  kernels. See [`ManhattanAudit/README.md`](ManhattanAudit/README.md) and
  [`ManhattanAudit/COMPARATOR_RUNS.md`](ManhattanAudit/COMPARATOR_RUNS.md).
- **Pinned statements.** The numbered results and the other claims of the paper that the proofs
  use are stated in `Manhattan/Frozen/`, one per file: 95 statements, all proved.
  [`ledger/manifest.yaml`](ledger/manifest.yaml) records for each the SHA-256 of its Lean text and
  the lines of the paper it states, and CI checks the hashes. The SHA-256 of `paper/manuscript.tex`
  is in [`paper/SOURCE_PIN.txt`](paper/SOURCE_PIN.txt).
- **Continuous integration.** The **CI** workflow builds the library and checks the manifest, the
  warnings, the linters, the certificate and the axiom reports. The **Comparator audit** workflow
  checks both comparator pairs. Both run on request, from the
  [Actions page](https://github.com/nitromannitol/Manhattan-Transience/actions).

The library, `Manhattan.lean` and `Manhattan/`, contains 258 Lean files with 62,767 lines. The
comparator sources are 8 files with 1,124 lines. The library is built on mathlib and on
Lattice-Probability, which supplies the results that do not depend on the model, among them Pólya's
theorem in two dimensions, the Nash inequality on `ℤ²` and the semigroup of a bounded generator.

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
has no prebuilt cache, so the first build compiles it as well as the library. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

`import Manhattan` loads every module except six: two superseded statements, two `Glue/` modules
and two files of `Paper/Constant/`. `lake build` compiles these too, through the library glob.
`import Manhattan.MainTheorems` loads the main theorems and what they use.

The toolchain is Lean `v4.32.0`. The dependencies are public repositories, pinned in
[`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `bbe0b90a7cf0517db0578139aaab7f152edbc45e`.

To reproduce the axiom reports and build the certificate and the comparator libraries:

```bash
lake build Manhattan.Meta.AxiomsAudit   # the 135 axiom reports
lake build Manhattan.Certificate        # the self-contained restatements of the main results
lake build ManhattanAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3.8 or newer and PyYAML (`pip install pyyaml`).

| command | what it checks |
|---|---|
| `python3 tools/check_manifest.py` | each pinned statement and its dependency closure match their recorded SHA-256, every file under `Manhattan/Frozen/` has one entry in the manifest, and no `axiom`, `admit` or `sorry` occurs in the library |
| `python3 tools/check_warnings.py` | the build of `Manhattan` emits no warning |
| `python3 tools/assumptions.py --check` | [`ASSUMPTIONS.md`](ASSUMPTIONS.md), which records that nothing is assumed, agrees with the manifest |
| `lake env lean tools/lint_fast.lean` | the fast mathlib environment linters pass on the whole library |
| `lake env lean tools/lint_simpnf.lean` | the `simpNF` linter passes (slow) |

## Running the comparators

Each comparator pair has a configuration `ManhattanAudit/<Pair>/comparator.json`, for `<Pair>`
one of `Transience` and `AnnealedGreenBound`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the independent NanoDa kernel.

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
runs the two pairs one after the other in a single job on GitHub-hosted runners. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Manhattan.lean            the root module, importing all but six modules (see Building)
Manhattan/
  MainTheorems.lean       the main theorems, stated in full
  Certificate.lean        self-contained restatements of what is proved, with their axioms
  Frozen/                 the pinned statements, one per file: Main/, Operator/,
                          Estimates/, Glue/, Paper/
  Model/                  sites, lines, the fair-coin environment, the kernels,
                          Poisson subordination
  Walsh/                  the Fourier–Walsh basis on environments and its grading
  Operator/               the generator in Fourier coordinates and the frequency
                          resolvent bound
  Library.lean            the operator objects re-exported from Lattice-Probability
  Estimates/              the degree-one and degree-three estimates
  Glue/                   the concrete competitor, the four summands, the assembly
                          of the main theorems
  V4/                     the second proof of Theorem 1.1, along the arXiv version
  Paper/                  the lemmas of Sections 3 and 5 in the paper's normalization,
                          and further statements of the arXiv version
  Meta/                   AxiomsAudit.lean (the axiom reports), Cone.lean (the
                          declarations a proof uses)
ManhattanAudit/           the mathlib-only restatements and their solutions
CORRESPONDENCE.md         paper to Lean, statement by statement
VERIFICATION.md           statement-by-statement comparison with the arXiv version
ledger/manifest.yaml      one row per pinned statement: hash, paper lines, state
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
DeepSeek, under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The
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
