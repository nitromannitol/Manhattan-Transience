/-
The fast environment linters over the whole library: `docBlame`,
`unusedArguments`, `dupNamespace`, `defLemma`, dangerous instances and the
rest.  Cheap enough to run on every push.  `simpNF` is registered slow and is
run separately by `tools/lint_simpnf.lean`.

    lake env lean tools/lint_fast.lean
-/
import Manhattan

#lint* in Manhattan
