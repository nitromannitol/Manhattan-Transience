# Statement verification: does the Lean say what the paper says?

Checked 2026-09-05 against `paper/manuscript-current.tex`
(SHA-256 `15884222065585ca…`, the text after the mean-zero correction).

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

## Theorem 1.2 (`thm:annealed`) — EXACT

Both conjuncts are present, with the same range `λ ∈ (0,1]`, and the closing
"and hence" is a conjunct rather than a remark. The constant is existential in
the paper too, so nothing numeric is claimed by the statement.

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

`Manhattan.Operator.DissipativeSkewPair.variational_bound` is the two-sided
statement `0 ≤ r ≤ ‖g‖₊² + ‖V - A g‖₋²`, with no hypothesis on `g`.

This one needed work on both sides. The paper assumed `⟨1,g⟩ = 0`; the Lean
inequality never did, so the hypothesis was dropped from the paper and its
proof replaced by the unrestricted argument. In the other direction the Lean
had only the upper bound, so `resolventQuadratic_nonneg` was added to supply
the `0 ≤` half the paper asserts. The two now say the same thing.

## Proposition 5.1 (`prop:frequency`) — EXACT

`V4FrequencyBound C` is `r_λ(p) ≤ C · v4Majorant λ p` for `λ ∈ (0,1]` and `p`
on the torus, with

    v4Majorant λ p = 1 / (λ + a(p)² · (1 + log₊(1/(√λ + a(p))))^{3/2}),
    maxFrequency p = max |p₀| |p₁| = a(p).

The exponent `3/2` is real division, confirmed by the accompanying lemma
`x ^ (3/2 : ℝ) = x * √x`. The paper's constant is existential ("there is a
universal `C`"), so the statement matches; see the caveat below about the
explicit value `2048`, which appears in the proof rather than the statement.

## Proposition 6.1 (`prop:time`) — EXACT, both equations

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
the printed formula follows by `(e^{ip} - e^{-ip})/2 = i sin p`. The content is
the same; the printed averaged form is not itself a Lean statement.

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

## Lemma 4.1 (`lem:parity`) and Lemma 4.2 (`lem:effective-energy`)

The construction is formalized (`rawMultiplierEnergy_le_evenMajorantEnergy`,
`operatorEstimate`, `effectiveWeight`), and `effectiveWeight r = |r|/√(log(1/|r|))`
is the paper's `q(r)` exactly.

**WEAKER in one respect.** The paper's `lem:effective-energy` states the
constant **16**:

    r_λ(p) ≤ (1 - s ∫ φ)²/H₀ + 16 ∫ q(r) φ(r)² dm(r).

No Lean statement carries `16`. The formalized inequality has a symbolic
constant. So the shape of the lemma is certified and its explicit constant is
not.

## The explicit constants are not certified

This is the one place where the reader should not over-read the formalization.

* `lem:effective-energy` prints `16`; Lean proves the same inequality with a
  symbolic constant.
* The proof of `prop:frequency` says "We verify that `C = 2048` suffices".
  The *statement* is existential and is certified. The value `2048` is not.
  Lean in fact proves the opposite direction about its own chain:
  `Paper.Constant.green_constant_gt_paper` shows the constant the formalized
  route produces exceeds `2048 · 10⁵`, and `annealed_green_le_numeral` certifies
  only `∫ p̄_t(0,0) dt ≤ 2.75 · 10⁸`.

Nothing here contradicts the paper. The formalization simply tracks constants
far more loosely than a human derivation does, and it does not attempt the
sharp bookkeeping that yields `16` and `2048`. Anyone citing this development
should say that the qualitative theorems are machine-checked and that the
explicit numerical constants are not.
