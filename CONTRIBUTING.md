# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
./bootstrap.sh       # first time: install the toolchain, get the mathlib cache, build
lake build           # afterwards
```

The toolchain is pinned in `lean-toolchain`. The production build is required to emit no Lean
or linter warnings (`python3 tools/check_warnings.py`). The two mathlib-only files
`ManhattanAudit/*/Challenge.lean` are the only files with a `sorry`: each contains one
documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`. `lake build Manhattan` builds the library and
`lake build ManhattanAudit` the comparator libraries.

## The main results and the axiom audit

The main results `Manhattan.transience` and `Manhattan.annealed_green_bound` are in
`Manhattan/MainTheorems.lean`. To print their axiom reports:

```bash
lake build Manhattan.Meta.AxiomsAudit   # the main theorems and every proved node not superseded
lake build Manhattan.Certificate        # the self-contained certificate
```

`Manhattan/Meta/AxiomsAudit.lean` is not imported by the library root, because a
`#print axioms` command runs again whenever its module is rebuilt. Each report must list
exactly `propext`, `Classical.choice` and `Quot.sound`; the axiom-audit and certificate steps
of `build.yml` fail on `sorryAx` and on any other axiom, and `python3 tools/check_manifest.py`
rejects an `axiom`, `admit` or `sorryAx` token in the production tree.

## Conventions for Lean files

- No `sorry`, `admit` or new `axiom` in the library; `python3 tools/check_manifest.py` rejects
  them.
- **Frozen statements.** The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Manhattan/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`. A new or changed statement needs a manifest node with its source
  lines in `paper/manuscript.tex`, a row in `CORRESPONDENCE.md`, and the author's approval;
  then `python3 tools/check_manifest.py --emit` refreshes the dependency-closure hashes, and
  `python3 tools/check_manifest.py` must pass. Proofs after the end marker may be changed
  freely.
- **The paper is the specification.** `paper/manuscript.tex` states what the frozen statements
  state. A mistake found in it is corrected in that file, citing `manuscript.tex:<line>`, and
  recorded in `paper/CHANGES_FROM_ARXIV.md`; it is never absorbed silently.
- **Library lemmas.** Results that do not depend on the Manhattan model (the semigroup of a
  bounded generator, the dissipative-skew pair and its resolvents, Pólya's theorem, the Nash
  inequality on `ℤ²` and the Poisson clock) come from the shared library Lattice-Probability;
  new model-independent lemmas belong there. The dependencies under `.lake/packages/` are
  read-only.
- **Never run `lake clean` or `lake update`.** `lake clean` wipes the mathlib oleans and
  forces a multi-hour rebuild from source, and `lake update` moves mathlib off its pin. To
  force a project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Manhattan` (and the corresponding `.lake/build/ir/Manhattan`) and
  re-run `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not modification time, so `touch`
  does nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the
  module.

### Elaboration policy for new files

These rules keep elaboration time predictable in a development of this size.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. Never call `nlinarith` on a goal that contains `Real.rpow`,
  `Real.exp` or `Real.log` terms. When a nonlinear fact is needed, hoist it into
  a small `private` lemma over abstract real variables, so that `rpow`, `exp` and
  `log` terms never enter a numeric tactic.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`).
- Keep Lean files under 1500 lines.

## Comparators

Each pair under `ManhattanAudit/<Pair>/` has a `Challenge.lean` that imports mathlib only, a
`Solution.lean`, a `SolutionBasic.lean` and a `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. Do not add a declaration to a challenge that
the statement does not need, and do not change a challenge without checking it against the
paper's statement. `ManhattanAudit/check_standalone.sh` elaborates one file standalone with the
project's options. The command that runs a pair is in
[`ManhattanAudit/README.md`](ManhattanAudit/README.md) and
[`ManhattanAudit/COMPARATOR_RUNS.md`](ManhattanAudit/COMPARATOR_RUNS.md). A missing pair, a
missing tool or a failed kernel check is a failure.

## Continuous integration

- `build.yml` (**CI**) checks the frozen-statement manifest, builds `Manhattan` and enforces the
  registered warning multiset, runs the environment linters, and checks the certificate and
  the axiom reports. It runs on pushes to `main` that change code or build configuration
  (documentation, `paper/`, `formalization.yaml` and `CITATION.cff` are ignored), and on
  request.
- `comparator.yml` (**Comparator audit**) builds `ManhattanAudit` and runs the comparator on both
  pairs. It runs on request only.
