# The randomly oriented Manhattan lattice in Lean

This repository formalizes Ahmed Bou-Rabee and Yuval Peres' manuscript
*The randomly oriented Manhattan lattice in 2D is transient*. The pinned source
is [`paper/manuscript.tex`](paper/manuscript.tex), whose SHA-256 is recorded in
[`paper/SOURCE_PIN.txt`](paper/SOURCE_PIN.txt) and
[`ledger/manifest.yaml`](ledger/manifest.yaml).

The target is a statement-faithful, kernel-checked Lean 4 development of the
paper's almost-sure transience theorem. The formalization uses Lean 4 v4.26.0
and Mathlib v4.26.0 only. In particular, the continuous-time kernel is built by
rate-two Poisson subordination of the discrete transition probabilities; no
separate continuous-time Markov-process dependency is used.

Homogeneous Walsh spaces use finite sets of line indices. For the
degree-three correction, the manuscript's ordered raw coefficient can contain
coincident rows, so the formalization constructs it on an ordered carrier,
projects it to the Finset-indexed space, and proves the projection-error bound
and Finset-specific lowering normalizations. Finset indexing does not
erase the projection or Lemma 5.3 obligations.

## Start here

Two files answer the two questions a reader has.

* [`Manhattan/Certificate.lean`](Manhattan/Certificate.lean) — **what is
  proved.**  It restates the main results in self-contained form and prints
  the axioms each rests on.  Building it checks every claim it makes:

      lake build Manhattan.Certificate

  Every line of its audit must report exactly
  `[propext, Classical.choice, Quot.sound]`.

* [`VERIFICATION.md`](VERIFICATION.md) — **whether the Lean says what the paper
  says.**  Statement by statement, marked EXACT, EQUIVALENT or WEAKER, with the
  definition chain spelled out where the correspondence is not immediate.

One caveat belongs up front, because it is the place where a reader could
over-read this development.  Every numbered statement is machine-checked, but
the paper's *numerals are not*.  Lemma 4.2 and Proposition 5.1 both assert a
universal constant and record the values `16` and `2048` in their proofs; the
formalized proofs reach the same statements along a lossier route, discharging
the first with `Manhattan.V4.v4ConstantSplit_lt`, below `670`.  The difference
is confined to proofs, and `VERIFICATION.md` says exactly where it lives.

## Status

The repository contains no `sorry` anywhere. `Manhattan.Frozen.Main.theorem_1_1`
(Theorem 1.1) and `Manhattan.Frozen.Main.theorem_1_2` (Theorem 1.2) are proved
and depend on exactly `[propext, Classical.choice, Quot.sound]`, as does
`Manhattan.Frozen.Estimates.proposition_frequency` (Proposition 2.2).

The manifest has 76 records, every one in state `PROVED` and none registered as
a draft. Three proved predecessors are retired from the live import cone; their
successors are the torus-restricted fixed-frequency consequence, Lemma 4.1 v3
with explicit integral-finiteness certificates, and the pointwise-fiber
Proposition 2.1 v2. Twelve of the records are the concrete-lemma anchors frozen
on 2026-09-04: Lemma 5.1 on both sides, (Hsym), Lemma 5.2 twice, Lemma 5.3 on
the raw frequency side, Lemma 5.4, the four summands of the objective (22), and
the paper's estimate `E_p(f_p,k_p) ≤ C √L`.

A theorem is not advertised as proved merely because a working support lemma or
abstract implication exists. Under the project's two-key rule the twelve
concrete anchors and the cone of the main theorems each need an independent
second key;
until a second verdict is recorded, [`CORRESPONDENCE.md`](CORRESPONDENCE.md)
lists those rows as `sealed` rather than `proved`.

## Imports and toolchain

The project is pinned to Lean 4 v4.26.0 and Mathlib v4.26.0. It has no
dependency beyond Mathlib: Lean modules import `Mathlib` or narrower Mathlib
modules and project modules beneath the `Manhattan` namespace. Reuse candidates were surveyed and none were adopted; the development depends
on Mathlib alone.

## Paper anchors

| Manifest ID | Paper result | Pinned source |
|---|---|---|
| `thm-main` | Theorem 1.1, almost-sure summability of quenched returns | `manuscript.tex:192` |
| `thm-annealed` | Theorem 1.2, annealed Green-function bound | `manuscript.tex:207` |
| `prop-generator-v2` | Proposition 2.1, pointwise frequency generator and Green decomposition | `manuscript.tex:555-607` |
| `var-ineq` | Formula (11), upper-bound direction only | `manuscript.tex:626-638` |
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

## Verification discipline

- The paper is the specification. Statement-level interpretations and
  corrections are recorded in [`ledger/ERRATA.md`](ledger/ERRATA.md).
- Every public definition or theorem has one row in
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) and one node in
  [`ledger/manifest.yaml`](ledger/manifest.yaml).
- Each frozen declaration lives alone between
  `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`; the manifest pins
  the exact bytes and, once emitted, the explicit local dependency closure.
- There are no custom axioms. Definitions never contain `sorry`. A `sorry` is
  permitted only as the single proof body of a manifest-registered theorem in
  state `DRAFT_SORRY`.
- A theorem reaches `PROVED` only after its exact frozen statement, provider,
  axiom surface, and independent audit have been checked. The main theorems
- Builds are warning-clean except for the exact manifest-registered draft
  warning multiset.

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build Manhattan.Model
lake build Manhattan.Operator
lake build Manhattan.Estimates
lake build Manhattan.Frozen
lake build Manhattan.Glue
lake build Manhattan.Meta.AxiomsAudit
python3 tools/check_manifest.py
python3 tools/check_warnings.py
```

Never run `lake clean`: cached Mathlib artifacts are intentionally preserved.
The manifest checker requires Python 3.8 or newer and PyYAML.


## Layout

```text
Manhattan/             Lean sources
paper/                 pinned manuscript and source checksum
ledger/                manifest and errata
tools/                 manifest and warning gates
CORRESPONDENCE.md      complete paper-to-Lean public-statement map
ROADMAP.md             dependency-ordered formalization phases
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) before changing statements or proofs.
