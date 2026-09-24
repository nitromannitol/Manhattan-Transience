# Statement verification: does the Lean say what the paper says?

Checked against `paper/arxiv/main.tex`, the unmodified source of
arXiv:2609.07621v1 (SHA-256 `08089661c62ee867…`).  Numbers and labels below are
those of that text.  The manifest follows the earlier text
`paper/manuscript.tex`; `paper/CHANGES_FROM_ARXIV.md` compares the two.

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

## Theorem 1.2 (`thm:annealed`) — WEAKER

Both conjuncts are present, with the same range `λ ∈ (0,1]`, and the closing
"and hence" is a conjunct rather than a remark.  The arXiv statement bounds the
Laplace transform by `2048`; the Lean statement asserts a constant `C < ∞`,
which is what `paper/manuscript.tex` states.  The numeral is not certified;
see the explicit constants below.

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

## Proposition 6.1 (`prop:frequency`) — WEAKER

`V4FrequencyBound C` is `r_λ(p) ≤ C · v4Majorant λ p` for `λ ∈ (0,1]` and `p`
on the torus, with

    v4Majorant λ p = 1 / (λ + a(p)² · (1 + log₊(1/(√λ + a(p))))^{3/2}),
    maxFrequency p = max |p₀| |p₁| = a(p).

The exponent `3/2` is real division, confirmed by the accompanying lemma
`x ^ (3/2 : ℝ) = x * √x`. The majorant is the paper's.  The paper's constant is
the numeral `2048`; the Lean constant `C` is existential.  See the explicit
constants below.

## Proposition 6.2 (`prop:time`) — EXACT, both equations

`eq:heat-kernel` is `Paper.ck_le_two_div : ck ω t x y ≤ 2/(t+2)`, quantified
over every environment and both sites, as the paper states.

`eq:time-derivative` is stated in the paper for the **annealed** `f(t) =
p̄_t(0,0)`. Only the quenched form was formalized, so
`Paper.abs_deriv_annealedReal_le` was added:
`|deriv annealedReal t| ≤ 2/(√t (1 + t/4))`, together with the `8t^{-3/2}`
form. Differentiation under the integral is legitimate because the quenched
bound is uniform in `ω` and `environmentLaw` is a probability measure.

## Lemma 3.1 (`lem:raise`) — EQUIVALENT

The paper states the averaged formula
`(D̃_n f)_{j₁…j_{n+1}} = (i/(n+1)) ∑_a sin(P_{j_a}) f_{…ĵ_a…}`.
Lean proves the concrete Walsh matrix elements
(`lemma_raise_concrete_raising`, `lemma_raise_concrete_adjoint`), from which
the printed formula follows by `(e^{ip} - e^{-ip})/2 = i sin p`, together with
the slot sum itself at the degree the development uses
(`Paper.Formulas.raise_slot_sum`, `n = 3`). The content is the same; the
printed averaged form at general `n` is not itself a Lean statement.

## Lemma 3.2 (`lem:formulas`) — EXACT for two of three, EQUIVALENT for the third

* `eq:D1`, first formula: `dStarZero_degreeOneRealFrequency` is
  `-(i sin p₀) ∫ f`, matching `(D₀*f)(p) = -i sin(p₁) ∫ f dm` including the
  sign.
* `eq:D2a`: `rawD2StarTwoRow` is `-i sin(α) ∫ k dm(β)`, matching.
* `eq:D2b`: the paper carries `-i√2 sin(β) ∫ k dm(r')`; Lean's
  `rawD2StarMixed` carries **no** `√2`. This is a deliberate normalization
  difference, documented at `Manhattan/V4/MixedBridge.lean:40`: the `(√2)⁻¹`
  is placed in the kernel instead, so the mixed symbol is `(√2)⁻¹ σ v`. Both
  factors are pinned by strict inequalities in `MixedBridgeWitnesses.lean`, so
  neither can be silently doubled or halved. Consistent, but not verbatim.

## Lemma 4.1 (`lem:parity`) and Lemma 5.1 (`lem:effective-energy`)

The construction is formalized (`rawMultiplierEnergy_le_evenMajorantEnergy`,
`operatorEstimate`, `effectiveWeight`), and `effectiveWeight r = |r|/√(log(1/|r|))`
is the paper's `q(r)` exactly.

**WEAKER in the constant only.** `lem:effective-energy` asserts

    r_λ(p) ≤ (1 - s ∫ φ)²/H₀ + 16 ∫ q(r) φ(r)² dm(r).

Lean proves the same inequality with `16` replaced by
`Manhattan.V4.v4ConstantSplit`, certified below `670` by `v4ConstantSplit_lt`.
That constant is universal and independent of `λ`, `p` and `φ`, so the Lean
statement is the paper's with a larger numeral.

## The explicit constants

The paper states two numerals: `2048` in Theorem 1.2 and Proposition 6.1,
and `16` in Lemma 5.1.  No Lean statement claims either value.

* The Lean statements of `lem:effective-energy` and `prop:frequency` quantify
  their constant existentially. Lean discharges the first with
  `v4ConstantSplit < 670` (`Manhattan/V4/SplitConstant.lean`), down from
  `20,028` and from the `74,869` of the first assembly, and the second with
  `max(max(1, 8π³ · v4ConstantSplit), outerRegionConstant(1/4))`.
* For Theorem 1.2 the formalized chain gives
  `∫₀^∞ p̄_t(0,0) dt ≤ 2.75 · 10⁸`
  (`Manhattan.Paper.Constant.annealed_green_le_numeral`).
* The formalized proofs reach the paper's inequalities along a lossier route,
  so they produce larger values.

### Where the remaining gap is

The paper's `16` is `5 + 11`: the degree-one cost contributes `5`, and the
column integral `eq:beta` contributes `11 = (π^{5/2}+π)/2` with coefficient
one. Lean's `670` is `60 + 8·76.2`, and the two differences are exactly:

| step | paper | Lean | why |
| --- | --- | --- | --- |
| degree-one and two-row | `5` | `60 = 2·6 + 4·12` | `objective_le_v4Move1` splits the residual by Cauchy–Schwarz, with multipliers `2` and `4` |
| column term | `1 · 11` | `8 · 76.2` | the operator step is a majorant comparison (`A = 291/κ`), not the paper's exact minimization |

Both `eq:beta` evaluations are now proved. `Manhattan/V4/BetaSplit.lean` splits
the fundamental domain at `|β| = √ρ`, integrates the inner reciprocal quadratic
over the line (`∫_ℝ dβ/(A+Bβ²) = π/√(AB)`, `Manhattan/V4/BetaIntegral.lean`)
and evaluates both tails, giving `π/(2√(2c)) + π/2` in place of the earlier
`π² + 1/c`. At the paper's own `c = 1/(2π³)` this is exactly `(π^{5/2}+π)/2`.

`Manhattan/V4/SharpConstant.lean` closes the multiplier side:
`symbolWeight_le_multiplier_one` (`κ = 40 → 1`),
`multiplier_one_le_evenMajorant_three` (`κ = 120 → 3`, beating the paper's own
`4` in `eq:M`) and `hThreeForm_rawWalsh_le_sharp`. They are proved by observing
that the multiplier is *linear in its constant*, so an identity or a
contraction established at one constant transfers to any other
(`multiplier_eq_smul`, `integral_multiplier_eq_smul`,
`rawMultiplierEnergy_eq_smul`); no frozen statement had to move.

Move 1 is now stated over an abstract shared constant `κ`, operator coefficient
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
Closing the rest means replacing that splitting, and the majorant comparison,
by the paper's exact minimization of the degree-three form. Neither affects any
statement, only the value of the constant.
