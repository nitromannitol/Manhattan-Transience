# The randomly oriented Manhattan lattice in 2D is transient

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Yuval Peres,
> [*The randomly oriented Manhattan lattice in 2D is transient*](https://arxiv.org/abs/2609.07621),
> arXiv:2609.07621.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and the shared library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`).

Both main theorems of the paper are proved, and no result from the literature is
assumed.

[![CI](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Manhattan-Transience/actions/workflows/comparator.yml)

## What is proved

Independently orient each horizontal and vertical line of `ℤ²` by a fair coin.
A walker chooses one of the two lines through its current position with equal
probability and takes one step in the direction of that line.  Theorem 1.1 of
the paper says that for almost every environment the walk is transient: the
quenched Green series `∑_{n ≥ 0} p^ω_n(x, x)` is finite at every site `x`.
Theorem 1.2 is the annealed estimate it is deduced from: for the
continuous-time walk with total jump rate two, the Laplace transforms
`∫_0^∞ e^{-λt} p̄_t(0,0) dt` of the annealed return probability are bounded
uniformly in `λ ∈ (0, 1]`, and hence `∫_0^∞ p̄_t(0,0) dt < ∞`.  Both are proved,
and stated in full in
[`Manhattan/MainTheorems.lean`](Manhattan/MainTheorems.lean):

- **`Manhattan.transience`** (Theorem 1.1, `thm:main`): for almost every
  environment under the product fair-coin law `environmentLaw`, every site `x`
  has `discreteGreen ω x < ∞`, where `discreteGreen ω x = ∑' n, p^ω_n(x, x)` in
  `ℝ≥0∞`.  Its statement is byte-faithful to
  `Manhattan.Frozen.Main.theorem_1_1`.
- **`Manhattan.annealed_green_bound`** (Theorem 1.2, `thm:annealed`): there is
  `C < ∞` such that
  `∫⁻ t in Ici 0, ofReal (exp (-λ t)) * annealedContinuousKernel t 0 0 ≤ C`
  for every `λ ∈ (0, 1]`, and
  `∫⁻ t in Ici 0, annealedContinuousKernel t 0 0 < ∞`.  The certified
  statement `Manhattan.Frozen.Main.theorem_1_2` is the proposition
  `Manhattan.AnnealedGreenBound`, and the statement displayed in
  `MainTheorems.lean` is the body of that definition.

Each is proved by direct application of its certified counterpart in
`Manhattan/Frozen/Main/`, and neither has a hypothesis.

Besides the two main theorems, the repository formalizes the statements of the
pinned manuscript that the proof passes through: the generator and Green
decomposition in Fourier–Walsh coordinates (Proposition 2.1), the variational
upper bound (formula (15)), the fixed-frequency estimate (Proposition 2.2), the
degree-one and degree-three estimates (Lemma 4.1 and Proposition 4.2), and the
Fourier–Walsh calculations of Section 5 at the concrete competitor.  Theorem 1.1
is also proved a second time, along the shorter argument of the arXiv version
(`Manhattan/V4/`).  Not formalized: the open questions of the last section, the
figures, and the survey of related work in the introduction.

**What is assumed.**  Nothing.  No theorem of this repository carries a result
from the literature as a hypothesis, and
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) records that no registered statement is
assumed.  The status is **76 registered statements, all `PROVED`**, each with
exactly the three standard axioms.  The paper-to-Lean map, node by node, is
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

**The pinned source and the registered statements.**  The pinned source is
[`paper/manuscript.tex`](paper/manuscript.tex), whose SHA-256 is recorded in
[`paper/SOURCE_PIN.txt`](paper/SOURCE_PIN.txt) and
[`ledger/manifest.yaml`](ledger/manifest.yaml).  A registered statement's text
between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is
pinned by the SHA-256 of those bytes in the manifest, together with the line
range of the paper it transcribes; the proof after the end marker is not pinned.
In the manifest, a registered statement is `PROVED` when its axiom closure is
exactly the three standard axioms.  The pinned manuscript states what the Lean
statements state;
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) records every
difference between it and the arXiv version, whose unmodified source is
[`paper/arxiv/`](paper/arxiv/).
[`VERIFICATION.md`](VERIFICATION.md) compares the Lean statements with the arXiv
version, statement by statement, marked EXACT, EQUIVALENT or WEAKER.

Modelling decisions:

- An environment gives one orientation to each line, indexed by its axis and
  its transverse coordinate, rather than the paper's redundant `ω(z, i)` with
  the condition that `ω(z, i)` does not depend on `z_i`.  The law
  `environmentLaw` is Mathlib's `Measure.infinitePi` of fair coins.
- The quenched `n`-step kernel is the path count
  `2⁻ⁿ · #{axis words of length n from z to z'}`, which is the probability
  under the quenched walk law.
- The continuous-time kernel is defined by rate-two Poisson subordination of
  the discrete kernel, not as the transition function of a continuous-time
  Markov process; the generator identity with equation (2) is proved
  (`Manhattan/Model/Kernel.lean`).
- Finiteness of a nonnegative series or integral is stated as its `ℝ≥0∞` value
  being `< ∞`.
- Homogeneous Walsh spaces use finite sets of line indices.  The degree-three
  correction, whose ordered coefficient can contain coincident rows, is built
  on an ordered carrier and projected, with the projection error bounded.

Every numbered statement registered in the manifest is machine-checked, but the
numerals of the arXiv version are not.  The arXiv version states Theorem 1.2
and Proposition 6.1 with the constant `2048` and Lemma 5.1 with the constant
`16`; the formal statements have an unspecified constant, as
`paper/manuscript.tex` does, the formal proofs reach them along a lossier
route, and the constant of Lemma 5.1 is discharged below `670` by
`Manhattan.V4.v4ConstantSplit_lt`.

The principal registered statements, with their manifest identifiers and the
lines of the pinned source they transcribe:

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

- **No `sorry`** in the library.  Each Mathlib-only comparator challenge under
  `ManhattanAudit/` contains one intentional statement-level `sorry`, which the
  corresponding solution file proves.
- **No custom axiom.**  The main theorems depend only on mathlib's three standard
  axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`Manhattan/Meta/AxiomsAudit.lean`](Manhattan/Meta/AxiomsAudit.lean) prints the
  axioms of every proved node, and
  [`Manhattan/Certificate.lean`](Manhattan/Certificate.lean) restates the main
  results in self-contained form and prints the axioms each rests on.  The
  axiom-audit and certificate steps of the
  [`build.yml`](.github/workflows/build.yml) workflow fail on `sorryAx` or on
  any other axiom, and `python3 tools/check_manifest.py` checks that no `axiom`,
  `admit` or `sorryAx` token occurs in the production tree.
- **Independent check of the statements.**  Both main theorems are restated
  using only Mathlib, with no project definition, in
  [`ManhattanAudit/Transience/Challenge.lean`](ManhattanAudit/Transience/Challenge.lean) and
  [`ManhattanAudit/AnnealedGreenBound/Challenge.lean`](ManhattanAudit/AnnealedGreenBound/Challenge.lean).
  Each challenge rebuilds the model from Mathlib primitives (the sites and
  directed lines of `ℤ²`, the fair-coin environment law, the quenched one-step
  and `n`-step kernels, the discrete Green series, and the rate-two Poisson
  subordination that defines the continuous-time kernel) and contains one
  intentional statement-level `sorry`, which the corresponding `Solution.lean`
  fills from the library through its own bridge in `ManhattanAudit/Support/`, over a
  verbatim copy of the challenge vocabulary in its own `SolutionBasic.lean`.  The
  configurations `ManhattanAudit/*/comparator.json` are for
  [`leanprover/comparator`](https://github.com/leanprover/comparator), which
  confirms that the challenge and the solution have identical elaborated types
  and that the proof reduces to the three standard axioms; both pairs pass, with
  the Lean kernel and with the independent nanoda kernel, as recorded in
  [`ManhattanAudit/COMPARATOR_RUNS.md`](ManhattanAudit/COMPARATOR_RUNS.md).  The workflow
  [`comparator.yml`](.github/workflows/comparator.yml) runs the comparator on
  request.  See [`ManhattanAudit/README.md`](ManhattanAudit/README.md).
- **Pinned toolchain.**  Lean `v4.35.0-rc2` ([`lean-toolchain`](lean-toolchain)),
  mathlib at revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` and
  `Lattice-Probability` at commit `bbe0b90`, pinned in
  [`lakefile.lean`](lakefile.lean) and recorded, with mathlib's own
  dependencies, in [`lake-manifest.json`](lake-manifest.json).

## Size

About 57,000 lines of Lean in 229 modules, of which about 44,000 lines are code
once comments and blank lines are removed, on top of mathlib and the
Lattice-Probability library.  The count covers `Manhattan.lean` and
`Manhattan/`, and excludes the `ManhattanAudit/` comparator surface.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake.  The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.35.0-rc2`), so `elan`
installs the right Lean version automatically, and the dependencies are pinned
to commits in [`lakefile.lean`](lakefile.lean) and
[`lake-manifest.json`](lake-manifest.json).
The results that do not depend on the Manhattan model (the semigroup of a
bounded generator and its Laplace resolvent, the dissipative-skew pair and its
coercive resolvents, Pólya's theorem in two dimensions, the Nash inequality on
`ℤ²` and the rate-two Poisson clock) come from the shared library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

```bash
# from the repository root, the first time
./bootstrap.sh       # install the toolchain, lake exe cache get, lake build
# afterwards
lake build           # compile the project
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact dependency
revisions; do not run `lake update`.  Never run `lake clean`: it discards the
Mathlib build artifacts.  Further building notes are in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

```bash
lake build Manhattan.Meta.AxiomsAudit   # print the axioms of the main theorems and every proved node
lake build Manhattan.Certificate        # the self-contained certificate of what is proved
lake build ManhattanAudit               # the comparator challenges and solutions
```

To use the library, `import Manhattan` pulls in the whole development; the main
results are in `import Manhattan.MainTheorems`.

The checkers in `tools/` need Python 3.8 or newer and PyYAML
(`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | each frozen statement's bytes match its recorded SHA-256, every file under `Manhattan/Frozen/` belongs to exactly one node, each node's recorded dependency-closure hash matches, and no `axiom`, `admit` or `sorryAx` token, and no unregistered `sorry`, occurs in the production tree |
| `python3 tools/check_warnings.py` | the build of `Manhattan` emits no warning other than the `sorry` warnings the manifest authorizes (it authorizes none) |
| `python3 tools/assumptions.py --check` | `ASSUMPTIONS.md` is current with the manifest |
| `lake env lean tools/lint_fast.lean` | the fast Mathlib environment linters pass on the whole library |
| `lake env lean tools/lint_simpnf.lean` | the `simpNF` linter passes (slow) |

## Repository layout

```
Manhattan/
  MainTheorems.lean   the main theorems, stated in full
  Certificate.lean    self-contained restatements of what is proved, with their axioms
  Frozen/             the certified statement surface, one frozen statement per file:
                      Main/, Operator/, Estimates/, Glue/
  Model/              sites, lines, the fair-coin environment, the kernels,
                      Poisson subordination
  Walsh/              the Fourier–Walsh basis on environments and its grading
  Operator/           the generator in Fourier coordinates and the frequency
                      resolvent bound
  Library.lean        the operator objects re-exported from Lattice-Probability
  Estimates/          the degree-one and degree-three estimates
  Competitor/         the competitor and the obstruction to the raw frequency version
  Glue/               the concrete competitor, the four summands, the assembly
                      of the main theorems
  V4/                 the second proof of Theorem 1.1, along the arXiv version
  Paper/              further statements of the arXiv version
  Meta/               AxiomsAudit.lean, Cone.lean
Manhattan.lean        the root module (imports the whole library)
ManhattanAudit/       Mathlib-only comparator challenges and solutions
ASSUMPTIONS.md        the results assumed (none; generated)
CORRESPONDENCE.md     paper ↔ Lean, node by node
VERIFICATION.md       statement-by-statement comparison with the arXiv version
CONTRIBUTING.md       building notes and the elaboration policy for new files
ledger/manifest.yaml  one row per registered statement: hash, paper lines, state
paper/                the pinned manuscript, its checksum, the unmodified arXiv
                      source (arxiv/) and CHANGES_FROM_ARXIV.md
tools/                the checkers listed under Building
.github/workflows/    build.yml and comparator.yml, run on request
bootstrap.sh          first-time setup
formalization.yaml    models, tooling, cost and review disclosure
CITATION.cff          citation metadata
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors, citation, acknowledgements

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

## Palomar preflight

The manually dispatched [Palomar full preflight](.github/workflows/palomar-preflight.yml)
calls Palomar's complete verifier at a pinned revision. Select the repository-relative
Comparator configuration to check. It records the dispatched commit and runs with
`mode: full` and `execution_profile: palomar-standard-v1`. Resolve the current Lean
minimum, source-module, Challenge-closure, licensing and metadata requirements before
dispatch. A passing preflight is advisory; it is separate from submission, editorial
review and a public registry record.

The module compatibility revision preserves the mathematical definitions and frozen
statements. Its pinned Lattice-Probability source adds public module interfaces and
updates existing walk-proof calls to the current Mathlib API. Full Palomar
verification checks the selected Challenge/Solution pair at the dispatched commit.
