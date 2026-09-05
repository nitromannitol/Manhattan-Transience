# Formalization roadmap

The phases are dependency-ordered. A phase may develop sorry-free support
before its public surface is frozen, but no downstream result is reported as
proved through an unsealed anchor.

## Phase 1 — Model

Define line indices, environments and their fair product law, translations,
the discrete transition kernel, iterates, quenched/annealed return
probabilities, and rate-two Poisson subordination. Prove the generator identity
from the subordinate definition rather than introducing continuous-time
Markov-process theory.

## Phase 2 — Walsh basis and grading

Index Walsh monomials by finite sets of line indices. Prove orthonormality,
completeness in complex `L²`, the cardinality grading, and the add/remove action
of multiplication by a line sign. This is the homogeneous Hilbert-space
carrier replacing the paper's underspecified symmetric tuple quotient. It does
not remove the degree-three diagonal issue: construct the raw correction on
ordered, possibly coincident row indices, project it to the Finset carrier, and
prove the projection-error estimate and Finset-specific lowering
normalizations.

## Phase 3 — Fourier in position and Proposition 2.1

Use Mathlib's Fourier basis on the two-torus to transform the joint
environment/position operator. Prove the symmetric/skew decomposition, norm
and adjoint claims, Green-function decomposition, and frequency resolvent.

Anchor: `prop-generator` — Proposition 2.1 (`manuscript.tex:576`).

## Phase 4 — Variational inequality

For coercive `H ± A`, construct the inverses by real Lax--Milgram on the
underlying real Hilbert space, recover complex linearity, and complete the
square at the specified optimizer. Only the upper-bound direction used by the
paper is in scope.

Anchor: `var-ineq` — the `≤` direction of formula (11)
(`manuscript.tex:626-638`).

## Phase 5 — Competitor and estimates

Formalize the degree-one and degree-three competitor in finite-set Walsh
coordinates, the one-dimensional torus estimates, the ordered raw correction,
its projection and Lemma 5.3 error bound, the corrected cancellation
calculation, and the integrable fixed-frequency estimate.

Anchors:

- `lem-onecoin` — Lemma 4.1 (`manuscript.tex:907`);
- `prop-key` — Proposition 4.2 (`manuscript.tex:1007`);
- `prop-frequency` — Proposition 2.2 (`manuscript.tex:644`).

## Phase 6 — Assembly

Integrate the frequency estimate, pass to the unweighted annealed Green
function, use Tonelli and the Poisson occupation identity, and transfer the
origin statement to every lattice point by countability and translation
invariance.

Anchors:

- `thm-annealed` — Theorem 1.2 (`manuscript.tex:207`);
- `thm-main` — Theorem 1.1 (`manuscript.tex:192`).
