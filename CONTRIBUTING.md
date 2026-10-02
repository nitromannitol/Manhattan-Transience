# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
./bootstrap.sh       # first time: install the toolchain, get the Mathlib cache, build
lake build           # afterwards
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The two Mathlib-only files
`Audit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean` or `lake update`.**  `lake clean` wipes the Mathlib
  oleans and forces a multi-hour rebuild from source, and `lake update` moves
  Mathlib off its pin.  To force a project-only rebuild, remove the project
  build artifacts under `.lake/build/lib/lean/Manhattan` (and the
  corresponding `.lake/build/ir/Manhattan`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Manhattan/Frozen/` is pinned by the SHA-256
  recorded in `ledger/manifest.yaml`.  A new or changed statement needs a
  manifest node with its source lines in `paper/manuscript.tex`, a row in
  `CORRESPONDENCE.md`, and the author's approval; then
  `python3 tools/check_manifest.py --emit` refreshes the dependency-closure
  hashes, and `python3 tools/check_manifest.py` must pass.  Proofs after the
  end marker may be changed freely.

- **Library lemmas.**  Results that do not depend on the Manhattan model (the
  semigroup of a bounded generator, the dissipative-skew pair and its
  resolvents, Pólya's theorem, the Nash inequality on `ℤ²` and the Poisson
  clock) come from the shared library Lattice-Probability; new
  model-independent lemmas belong there.

- **The paper is the specification.**  `paper/manuscript.tex` states what the
  frozen statements state.  A mistake found in it is corrected in that file,
  citing `manuscript.tex:<line>`, and recorded in
  `paper/CHANGES_FROM_ARXIV.md`; it is never absorbed silently.

- **The main results** are in `Manhattan/MainTheorems.lean`; the axiom audit is
  `lake build Manhattan.Meta.AxiomsAudit`, and the comparator surface is
  `lake build Audit`.

## Elaboration policy for new files

These rules keep elaboration time predictable in a development of this size.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`.  Never call `nlinarith` on a goal that contains `Real.rpow`,
  `Real.exp` or `Real.log` terms.  When a nonlinear fact is needed, hoist it into
  a small `private` lemma over abstract real variables, so that `rpow`, `exp` and
  `log` terms never enter a numeric tactic.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`).
- Keep Lean files under 1500 lines.
- Never run `lake clean`: it wipes the Mathlib oleans and forces a multi-hour
  rebuild from source.
