/-
The `simpNF` linter over the whole library.  It re-runs `simp` on every simp
lemma, so it takes hours and runs on the nightly schedule rather than on every
push.

    lake env lean tools/lint_simpnf.lean
-/
import Manhattan

#lint only simpNF in Manhattan
