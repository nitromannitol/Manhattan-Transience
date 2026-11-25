# Statement verification: does the Lean say what the paper says?

Checked against `paper/arxiv/main.tex`, the unmodified source of
arXiv:2609.07621v1 (SHA-256 `08089661c62ee867…`).  Numbers and labels below are
those of that text.  The manifest follows `paper/manuscript.tex`, a different
text of the same paper; `paper/CHANGES_FROM_ARXIV.md` compares the two.

A formalization is only worth what its statements say. This file records, for
every numbered statement of the paper, whether the Lean statement is the same
statement, an equivalent one in different coordinates, or something weaker.
Three verdicts are used:

* **EXACT** — the Lean statement is the paper's, symbol for symbol, once
  definitions are unfolded.
* **EQUIVALENT** — the same mathematical content in a different normalization
  or at a lower level, with the translation proved or explicitly documented.
* **WEAKER** — the Lean statement does not carry something the paper asserts.

## Theorem 1.1 (`thm:main`) — EXACT

Paper: for `P`-almost every `ω`, `∑_{n≥0} p_n^ω(x,x) < ∞` for every `x ∈ Z²`.

Lean: `∀ᵐ ω ∂environmentLaw, ∀ x : Site, discreteGreen ω x < ∞`.

Unfolding the definitions gives the paper's statement and not merely something
like it:

| paper | Lean |
| --- | --- |
| `Z²` | `Site := ℤ × ℤ` |
| one fair coin per line, independent | `environmentLaw := Measure.infinitePi (fun _ : LineIndex => fairCoin)` |
| `ω(z,i)` does not depend on `z_i` | `lineAt z i = (i, transverseCoordinate z i)`, and `transverseCoordinate` returns `z.2` for the horizontal axis and `z.1` for the vertical |
| step rule `z + ω(z,i)e_i` of `eq:rule` | `directedNeighbor ω z i = z + (ω (lineAt z i)).sign • basisStep i` |
| `p_n^ω(x,x)` | `nStepKernel ω n x x = 2⁻ⁿ · #{axis words of length n returning to x}` |
| `∑_{n≥0}` | `discreteGreen ω x = ∑' n, nStepKernel ω n x x` |

Proved twice, by independent routes: `Frozen.Main.theorem_1_1` and
`V4.theorem_1_1_v4`.

## Theorem 1.2 (`thm:annealed`) — EXACT (with the numeral)

Both conjuncts are present, with the same range `λ ∈ (0,1]`, and the closing
"and hence" is a conjunct rather than a remark.  The frozen statement asserts a
constant `C < ∞`, which is what `paper/manuscript.tex` states.  The arXiv
numeral is proved separately: `Manhattan.Paper.annealed_laplace_le_2048` is
`∫₀^∞ e^{-λt} p̄_t(0,0) dt ≤ 2048` for every `λ ∈ (0,1]`, and
`Manhattan.Paper.annealed_green_le_2048` is `eq:green-explicit`,
`∫₀^∞ p̄_t(0,0) dt ≤ 2048` (`Manhattan/Paper/AnnealedConstant.lean`).

## Proposition 2.1 (`prop:generator`) — EXACT

Split across frozen nodes, each matching the printed formula:

| paper | Lean |
| --- | --- |
| `eq:Sp` | `fiberS_eq_formula`, character for character |
| `eq:Ap` | `fiberA_eq_formula`, character for character |
| `S_p` self-adjoint, nonpositive | `fiberS_self_adjoint`, `fiberS_nonpositive` |
| `A_p* = -A_p` | `fiberA_skewAdjoint` |
| `‖S_p‖ ≤ 4`, `‖A_p‖ ≤ 2` | `fiberS_norm_le`, `fiberA_norm_le`, same numerals |
| `eq:green`, `eq:frequency-resolvent` | the last conjunct of `proposition_generator_v2` |

## Lemma 2.2 (`lem:variational-bound`) — EXACT

`LatticeProb.Analysis.DissipativeSkewPair.variational_bound`, restated as
`Manhattan.Certificate.variational_bound`, is the two-sided statement
`0 ≤ r ≤ ‖g‖₊² + ‖V - A g‖₋²`, with no hypothesis on `g`, as in the paper.
Its halves are `resolventQuadratic_nonneg` and `resolventQuadratic_le`.

## Proposition 6.1 (`prop:frequency`) — EXACT (with the numeral)

`V4FrequencyBound C` is `r_λ(p) ≤ C · v4Majorant λ p` for `λ ∈ (0,1]` and `p`
on the torus, with

    v4Majorant λ p = 1 / (λ + a(p)² · (1 + log₊(1/(√λ + a(p))))^{3/2}),
    maxFrequency p = max |p₀| |p₁| = a(p).

The exponent `3/2` is real division, confirmed by the accompanying lemma
`x ^ (3/2 : ℝ) = x * √x`. The majorant is the paper's.  The statement with the
paper's numeral, `V4FrequencyBound 2048`, is `Manhattan.Paper.frequencyBound_2048`
(`Manhattan/Paper/FrequencyBound.lean`).

## Proposition 6.2 (`prop:time`) — EXACT, both equations

`eq:heat-kernel` is `Paper.ck_le_two_div : ck ω t x y ≤ 2/(t+2)`, quantified
over every environment and both sites, as the paper states.

`eq:time-derivative` is stated in the paper for the **annealed** `f(t) =
p̄_t(0,0)`, and `Paper.abs_deriv_annealedReal_le` states it in that form:
`|deriv annealedReal t| ≤ 2/(√t (1 + t/4))`, together with the `8t^{-3/2}`
form. It follows from the quenched bound: differentiation under the integral is
legitimate because the quenched bound is uniform in `ω` and `environmentLaw` is
a probability measure.

## Lemma 3.1 (`lem:raise`) — EXACT for the formula and the factorization; the commutation clause for continuous multipliers

The paper states the averaged formula
`(D̃_n f)_{j₁…j_{n+1}} = (i/(n+1)) ∑_a sin(P_{j_a}) f_{…ĵ_a…}`, the
factorization `D_n = Π_{n+1} D̃_n Π_n`, and that `Π_n` commutes with every
bounded multiplier that is a function of `P`. The first two are Lean
statements at every degree `n`, in the symmetric coefficients of the paper.
The commutation is proved for every continuous multiplier that is a function of
`P`, which is the statement of `paper/manuscript.tex` (line 1190); the
multipliers the argument uses are continuous
(`paper/CHANGES_FROM_ARXIV.md`, 1.3).

| paper | Lean |
| --- | --- |
| symmetric coefficient `f` of `F`, `(n!)⁻¹⟨W_S, F⟩` at each ordering of `S` | `Manhattan.Paper.symCoeff`, `symCoeff_apply` |
| `D̃_n`: shift, append the origin line, distribute over the `n+1` slots | `Manhattan.Paper.rawRaise` |
| `eq:raise` | `Manhattan.Paper.orderedFourier_rawRaise` |
| `D_n = Π_{n+1} D̃_n Π_n` | `Manhattan.Paper.symCoeff_walshRaise` |
| `Π_n` commutes with continuous multipliers of `P` | `Manhattan.Paper.offDiagonalProjection_comp_orderedMultiplier` |

`Π_n` is `Manhattan.Glue.offDiagonalProjection n`, a multiplier `m(P)` is
given by a continuous function `m` on the two-torus `ℝ²/(2πℤ)²`, and the
commutation is proved as in the paper, by uniform approximation of `m` by
trigonometric polynomials. The concrete Walsh matrix elements
(`lemma_raise_concrete_raising`, `lemma_raise_concrete_adjoint`) remain the
registered nodes.

## Lemma 3.2 (`lem:formulas`) — EXACT

All five formulas are Lean statements in the paper's normalization (the
coefficients of types `11`, `12` and `112` multiplied by `√2`, `2` and `√18`),
for the raw operators `D̃` and `D̃*` of `lem:raise`, at every square-integrable
coefficient.  They are derived from `eq:raise` at every degree
(`Manhattan.Paper.orderedFourier_rawRaise`) and from its adjoint
(`Manhattan.Paper.orderedFourier_rawLower`); `D̃*` is the adjoint of `D̃` for
the inner products of `eq:iso` (`Manhattan.Paper.factorial_mul_inner_rawRaise`),
and the integral over the frequency of one line is
`Manhattan.Paper.slotIntegral`, identified with the integral by
`coeFn_slotIntegral`.

| paper | Lean (`Manhattan/Paper/LowDegreeFormulas.lean`) |
| --- | --- |
| `eq:D2a`, `-i sin(α) ∫ k dm(β)` | `Manhattan.Paper.lowering_twoRow` |
| `eq:D2b`, `-i√2 sin(β) ∫ k dm(r')` | `Manhattan.Paper.lowering_mixed` |
| `eq:D1`, `D₀* f = -i sin(p₁) ∫ f dm` | `Manhattan.Paper.lowering_degreeOne` |
| `eq:D1`, `(D̃₁f)₁₁ = (i/√2) sin(p₁)[f(r) + f(r')]` | `Manhattan.Paper.raising_twoRow` |
| `eq:D1`, `(D̃₁f)₁₂ = i sin(r) f(r)` | `Manhattan.Paper.raising_mixed` |

A coefficient of type `112` is the function `k(r, r', β)` of the two row
frequencies and the column frequency; `Manhattan.Paper.type112Freq` places it,
with the factor `1/√18`, in the three axis patterns of the symmetric
coefficient.  `eq:D2b` uses the symmetry of `k` in its two row frequencies.

The development that proves the main theorems uses the earlier raw symbols
`rawD2StarTwoRow` and `rawD2StarMixed`, which carry the Finset normalization:
`rawD2StarMixed` has no `√2`, which is placed in the kernel instead
(`Manhattan/V4/MixedBridge.lean:40`).

## Lemma 4.1 (`lem:parity`) and Lemma 5.1 (`lem:effective-energy`)

The construction is formalized (`rawMultiplierEnergy_le_evenMajorantEnergy`,
`operatorEstimate`, `effectiveWeight`), and `effectiveWeight r = |r|/√(log(1/|r|))`
is the paper's `q(r)` exactly.

`lem:effective-energy` asserts

    r_λ(p) ≤ (1 - s ∫ φ)²/H₀ + 16 ∫ q(r) φ(r)² dm(r).

**WEAKER in scope.** The constant `16` is proved for the one-parameter family
`φ = t/q` on `Γ_δ`, which is the case `prop:frequency` uses, not for every real
even `φ ∈ L²` vanishing off `Γ_δ`.

`Manhattan.Paper.move1_objective_sixteen` bounds the objective of
`lem:variational-bound` at a test function `g` by
`(1 - s ∫ φ)²/H₀ + 16 ∫ q φ²` for these profiles
(`Manhattan/Paper/EffectiveEnergy.lean`); the step from the objective to
`r_λ(p)` is `resolventQuadratic_le`.  `Manhattan.Paper.move2Supply_sixteen`
is `eq:optimized` in the form `prop:frequency` uses:
`r_λ(p) ≤ 1/(H₀ + s² Z_δ/16)` on `√λ + a(p) ≤ 1/256` for some `s` with
`s² ≥ (2/π)² a(p)²` (the proof takes `s = sin p₁` after exchanging rows and
columns).  The route is the paper's: `eq:majorant` with constant one
and `M = 4(δ + |r| + |r'| + |β|)` (`Manhattan.Paper.sectorForms_rawWalsh_le`),
the exact splitting of the objective into its sectors
(`Manhattan.Paper.objective_eq_sectors`), the completed square of
`eq:scalar-energy` (`Manhattan.Paper.parityCost_eq`), and `eq:beta` with the
constant `(π^{5/2}+π)/2 < 11`.  Two intermediate steps are bounded slightly
differently, with the same conclusion: the weight
`λ + θ(P) + 6|sin(P₁/2)| + 6|sin(P₂/2)|` in place of the paper's bracket
(both are below `M`), and the two-row bound `4 s² J(μ)` of
`Manhattan.V4.hMinusEnergy_twoRow_le` in place of the paper's `2 s² J(μ)`
(the degree-one cost is then `15/4 ∫ q φ²`, below the paper's `5`).
The earlier route, with `16` replaced by `Manhattan.V4.v4ConstantSplit < 670`,
remains in `Manhattan/V4/`.

## The explicit constants

The paper states two numerals: `2048` in Theorem 1.2 and Proposition 6.1,
and `16` in Lemma 5.1.  Both are proved in `Manhattan/Paper/` and registered as
frozen nodes in `Manhattan/Frozen/Paper/` (the statements pinned to
`paper/manuscript.tex` quantify the constant existentially, as that text does):

| statement | numeral | Lean |
| --- | --- | --- |
| `lem:effective-energy` | `16` | `Manhattan.Paper.move1_objective_sixteen` (profiles `φ = t/q` on `Γ_δ`) |
| `eq:optimized` | `16` | `Manhattan.Paper.move2Supply_sixteen` (on `√λ + a(p) ≤ 1/256`, for some `s` with `s² ≥ (2/π)² a(p)²`) |
| `prop:frequency` | `2048` | `Manhattan.Paper.frequencyBound_2048` |
| `thm:annealed` | `2048` | `Manhattan.Paper.annealed_laplace_le_2048` |
| `eq:green-explicit` | `2048` | `Manhattan.Paper.annealed_green_le_2048` |

The paper's `16` is `5 + 11`.  The proof reaches `15/4 + (π^{5/2}+π)/2`: the
degree-one and two-row costs give `3/4 + 3`, and the column integral `eq:beta`
at `M = 4(δ + |r| + |r'| + |β|)` gives `(π^{5/2}+π)/2 < 11` with coefficient
one.  Coefficient one needs the three exact steps of the paper:
`eq:majorant` with constant one (`Manhattan.Paper.sectorForms_rawWalsh_le`:
three slot terms when a row is added and two when a column is added, and the
ordered row pairs carry half the energy of a symmetric kernel), the exact
splitting of the objective (`Manhattan.Paper.objective_eq_sectors`), and the
completed square (`Manhattan.Paper.parityCost_eq`).  `prop:frequency` follows
with `10π² · 16 < 1580` on the improvement region and `83` on its complement,
and `thm:annealed` with `1/π² + 2^{7/2}·2048/(π²√(1 + log 4)) + log(4π) < 2048`
(`Manhattan.Paper.greenConstant_le_2048`).

### The Version 4 constants

`Manhattan/V4/` proves the same inequalities with larger constants:
`v4ConstantSplit < 670` for Lemma 5.1 and `2.75 · 10⁸` for the Green integral
(`Manhattan.Paper.Constant.annealed_green_le_numeral`).  The differences are:

| step | paper | `Manhattan/V4/` | why |
| --- | --- | --- | --- |
| degree-one and two-row | `5` | `60 = 2·6 + 4·12` | `objective_le_v4Move1` splits the residual by Cauchy–Schwarz, with multipliers `2` and `4` |
| column term | `1 · 11` | `8 · 76.2` | the operator step is a majorant comparison (`A = 291/κ`), not the paper's exact minimization |

Both `eq:beta` evaluations are proved. `Manhattan/V4/BetaSplit.lean` splits
the fundamental domain at `|β| = √ρ`, integrates the inner reciprocal quadratic
over the line (`∫_ℝ dβ/(A+Bβ²) = π/√(AB)`, `Manhattan/V4/BetaIntegral.lean`)
and evaluates both tails, giving `π/(2√(2c)) + π/2`. At the paper's own
`c = 1/(2π³)` this is exactly `(π^{5/2}+π)/2`.

`Manhattan/V4/SharpConstant.lean` closes the multiplier side:
`symbolWeight_le_multiplier_one` (`κ = 40 → 1`),
`multiplier_one_le_evenMajorant_three` (`κ = 120 → 3`, beating the paper's own
`4` in `eq:M`) and `hThreeForm_rawWalsh_le_sharp`. They are proved by observing
that the multiplier is *linear in its constant*, so an identity or a
contraction established at one constant transfers to any other
(`multiplier_eq_smul`, `integral_multiplier_eq_smul`,
`rawMultiplierEnergy_eq_smul`).

Move 1 is stated over an abstract shared constant `κ`, operator coefficient
`A` and column constant `C_β` (`OperatorCoefficient`, `BetaColumnBound`), with
Move 1 coefficient `4A + 4`. Because the operator estimate reads as
`A = 291/κ` and `C_β` grows like `√κ`, the product `(4A+4)·C_β` is least at
`κ = 291`, where `A = 1`; that is the instance `SplitConstant.lean` runs.

Which of the two binds is worth stating. `operatorEstimate_sharp` carries
`A·κ = 97·3 = 291`, where `97 = 1 + 8·12` comes from
`hThreeForm_rawWalsh_le_sharp` and `sectorDFourForm_rawWalsh_le`. Because the
Move 1 coefficient is `4A + 4` and `C_β` grows like `√κ`, running at `A = 1`
gives `60 + 8·C_β(κ)` with `κ = A·κ`. Even a perfect operator step, `A·κ = 1`,
would leave `60 + 8·5.94 ≈ 108`: the `2`/`4` Cauchy–Schwarz multipliers of
`objective_le_v4Move1` are the binding constraint, not the operator estimate.
`Manhattan/Paper/EffectiveEnergy.lean` uses the paper's exact minimization of
the degree-three form instead of that splitting and of the majorant comparison.
