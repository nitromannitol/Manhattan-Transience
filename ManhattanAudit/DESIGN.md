# Comparator design memo: vocabulary, bridges, deltas

This memo records how the two comparator pairs are built, for whoever checks
or extends them.  Each pair `<Thm>` (`Transience`, `AnnealedGreenBound`) has a
directory `ManhattanAudit/<Thm>/` with the same four files, and one bridge in
`ManhattanAudit/Support/`:

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object the theorem mentions, states the theorem, and ends in a
  single `sorry`.  This file is the object of trust: a reader checks what it says,
  not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`).  It imports
  only `Mathlib`, so the vocabulary elaborates in the solution exactly as in the
  challenge.
- `Solution.lean` imports the library together with its own `SolutionBasic` and its
  own bridge, restates the challenge theorem byte-for-byte, and proves it from the
  library's theorem.
- `comparator.json` names the challenge module, the solution module, the theorem and
  the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and enables the
  nanoda replay.
- `Support/TransienceBridge.lean` and `Support/AnnealedGreenBoundBridge.lean` hold the
  transports (sections 1 to 3).  Each imports only its own pair's `SolutionBasic`, and
  only that pair's `Solution.lean` imports it.  The two bridges share the
  identification of the environment spaces (section 2) and differ in the theorem-level
  transport: the `Transience` bridge ends with `Bridge.transience`, the
  `AnnealedGreenBound` bridge with `annealedContinuousKernel_eq`.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`ManhattanAudit/<Thm>/SolutionBasic.lean`, as in their
per-challenge `SolutionBasic.lean`), and `Solution.lean` imports the repository, that
module, and its bridge, and states the theorem with the challenge's bytes.

The two challenges carry one vocabulary block, byte-identical in each and in each
pair's `SolutionBasic.lean` (`bash ManhattanAudit/check_standalone.sh --vocabulary`
compares each `Challenge.lean` with its `SolutionBasic.lean`).  The block contains
definitions that the Theorem 1.1 challenge does not use (the Poisson weights and the
continuous-time kernels) and one that neither statement uses (`oneStepKernel`,
equation (1)); they do not enter the dependency closure of a theorem that does not
mention them.

## 1. Definitionally shared vocabulary

`Site` and `LineIndex` are abbreviations of Mathlib types, and
`rateTwoPoissonWeight` is the same Mathlib expression as the repository's, so
`rateTwoPoissonWeight_eq` (in the `AnnealedGreenBound` bridge) is `rfl`.  The time integrals, `Set.Ici`,
`ENNReal.ofReal`, `Real.exp` and the codomains `ℝ≥0` and `ℝ≥0∞` are Mathlib's
on both sides.

## 2. Inductive copies

The vocabulary declares its own `Axis` and `Orientation`, which are new
inductive types.  The bridges match them constructor by constructor
(`axisEquiv`, `orientationEquiv`) and build from these a measurable equivalence
`environmentMeasurableEquiv` of the environment spaces, reindexing the product
by the line equivalence and mapping each coordinate by the orientation
equivalence.  They prove, rather than assume, that the objects built on them
agree:

- `measurePreserving_environmentMeasurableEquiv`: the equivalence carries the
  vocabulary's product fair-coin law to the repository's;
- `directedNeighbor_equiv`, `followPath_equiv` (induction on the word),
  `nStepKernel_equiv` (reindexing the finite sum over words): the directed
  edges, paths and `n`-step kernels agree along the equivalence;
- `discreteGreen_eq` (in the `Transience` bridge), `continuousKernel_eq` (in the
  `AnnealedGreenBound` bridge): consequences for the Green series and the subordinated
  kernel;
- `annealedContinuousKernel_eq`: the annealed kernels are equal, by the change
  of variables `MeasurePreserving.lintegral_comp_emb` along the equivalence.

## 3. Theorem-level bridges

`Bridge.transience` pulls `Manhattan.transience` back along the
measure-preserving equivalence (`QuasiMeasurePreserving.tendsto_ae`) and
rewrites with `discreteGreen_eq`.  The Theorem 1.2 solution rewrites
`Manhattan.annealed_green_bound` with `annealedContinuousKernel_eq` and closes
the goal with `exact`.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `Manhattan/MainTheorems.lean` with
every repository name replaced by its vocabulary copy.  Relative to the frozen
statement `Manhattan.Frozen.Main.theorem_1_2`, whose type is the definition
`Manhattan.AnnealedGreenBound`, the Theorem 1.2 challenge displays the body of
that definition.

How the repository reads the paper is recorded in `VERIFICATION.md`,
`CORRESPONDENCE.md` and `paper/CHANGES_FROM_ARXIV.md`.  Four readings enter these
statements:

1. The paper records an environment as the redundant function
   `ω : ℤ² × {1,2} → {-1,1}`, with the condition that `ω(z,i)` does not depend
   on `z_i` (`manuscript.tex:167-174`).  The vocabulary, like the repository,
   indexes an environment by the lines themselves, `(axis, transverse
   coordinate)`, so the product of fair coins is literal and equation (1)
   (`manuscript.tex:176-180`) holds without an invariance condition.
2. The paper introduces `p^ω_n` as a probability under the quenched walk law
   (`manuscript.tex:186-190`).  The vocabulary gives the equivalent finite path
   count: every length-`n` word in the two axes has weight `2⁻ⁿ`.
3. The paper's continuous-time walk jumps from `z` to `z + ω(z,i) e_i` at rate
   `1` for each `i` (`manuscript.tex:200-205`).  The vocabulary defines its
   transition function by rate-two Poisson subordination of the discrete
   kernel, `∑' n, P(N_t = n) p^ω_n(z, z')`, which is that walk's transition
   function because its jump chain is the discrete walk; no continuous-time
   Markov-process theory enters.
4. Finiteness of a nonnegative series or integral is stated as its `ℝ≥0∞`
   value being `< ∞`, and the half-line `[0, ∞)` of the time integrals is
   `Set.Ici 0`.

The comparator does not check these readings: it checks that the library
proves exactly the displayed statement, over definitions that can be read
without the library.

## 5. What the comparator does not certify

- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the repository's definitions, so the comparator shows that nothing in the
  statements depends on the library beyond what the vocabulary displays; a
  reader still has to check the vocabulary against the paper, in particular
  reading 3 above.

## 6. Notes on the checks

- **Instance environments.**  The solutions import both the repository
  and the vocabulary, and both declare `MeasurableSpace` instances on their own
  `Axis` and `Orientation`.  These are instances on different types; the comparator
  elaborates the challenge and the solution statement and requires the two to
  coincide constant by constant, so a solution statement that picked up a repository
  constant or instance is rejected.
- **Comparator.**  `leanprover/comparator` checks each solution statement against its
  challenge and the dependency closure of the solution theorem against Mathlib, and
  accepts both pairs, with the Lean kernel and with the independent nanoda kernel (see
  `ManhattanAudit/COMPARATOR_RUNS.md`).  Because each pair has its own vocabulary, no
  file imports several solutions at once, and the comparator is the only statement-identity
  check.
