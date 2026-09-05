# Contributing

This project treats the pinned manuscript as a specification and separates
statement approval from proof development. Preserve that separation in every
change.

## Before editing

1. Read [`paper/manuscript.tex`](paper/manuscript.tex),
   the relevant entries in
   [`ledger/ERRATA.md`](ledger/ERRATA.md).
2. Check [`CORRESPONDENCE.md`](CORRESPONDENCE.md) and
   [`ledger/manifest.yaml`](ledger/manifest.yaml) for an existing owner.
   strengthen, weaken, normalize, or repair the manuscript.

## Statement-first workflow

Every meaning-carrying public definition and every public theorem must have:

- one frozen file under `Manhattan/Frozen/` containing exactly one declaration
  between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END`;
- one manifest node with an exact source location such as
  `manuscript.tex:192` and the applicable ruling identifiers;
- one row in `CORRESPONDENCE.md`;
- an author-approved statement version before proof work is sealed.

After approval, hash the bytes between the marker lines for `frozen_sha256`.
Run `python3 tools/check_manifest.py --emit` to add or refresh the explicit
local dependency-closure hashes, review the diff, then run the checker without
`--emit`.

The supported states are:

- theorem: `DRAFT_SORRY`, `PROVED`, or `SEALED`;
- definition: `FROZEN` only.

`DRAFT_SORRY` authorizes exactly one placeholder, after the end marker, as the
theorem proof body. No other state authorizes one. Definitions and all support
code must be sorry-free. No `axiom`, `admit`, or explicit `sorryAx` is allowed
in the production tree.

## Proof and audit gates

Keep reusable support outside frozen files. Once a provider proof builds:

1. verify the exact frozen target and its source location;
2. run the manifest and warning gates;
3. inspect `#print axioms` for only `propext`, `Classical.choice`, and
   `Quot.sound` as applicable;
4. obtain an independent hostile statement/proof audit;
5. for headline statements, pass a Mathlib-only comparator challenge under
6. record the audit and change the manifest state only after all gates pass.

Comparator `Challenge.lean` and `SolutionBasic.lean` vocabulary must be
byte-identical and import only Mathlib. `Solution.lean` may import the project
and connect the independent vocabulary to the sealed theorem.

## Build hygiene

Use the pinned toolchain and build the narrowest module first:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build Manhattan.<Module>
python3 tools/check_manifest.py
python3 tools/check_warnings.py
```

Lean options are strict: `autoImplicit` is off and unused-variable linters are
on. Do not suppress a warning to land code. Do not run `lake clean`.

why, module interfaces, Mathlib gaps, and manuscript issues. Put manuscript
issues in `ledger/ERRATA.md` with `manuscript.tex:<line>` citations.
