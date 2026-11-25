import Manhattan.Paper.EffectiveEnergy

/-! Lemma 5.1 of the arXiv version (`lem:effective-energy`, `paper/arxiv/main.tex:951-1033`)
with the constant `16`, for the profiles `φ = t/q` on `Γ_δ` that the proof of
`prop:frequency` uses (not for every real even `φ ∈ L²` vanishing off `Γ_δ`): there is a
test function `g` at which the objective of `lem:variational-bound` is at most
`(1 - s ∫ φ)²/H₀ + 16 ∫ q φ²`, with `s = sin p₁`, `φ = t/q` on `Γ_δ` for a real `t`
and `H₀ = λ + θ(p)`.  Hypotheses: `δ > 0`, `λ + 4|p₂| ≤ 4δ`, `√δ ≤ r₀ ≤ 1/4` and
`λ + d(p₁) ≤ δ²`. -/

open scoped lp
open MeasureTheory Set UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.V4.Frequency Manhattan.Paper
open LatticeProb.Analysis
open Manhattan.V4 Manhattan.Operator

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.move1_objective_sixteen {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta r0 : ℝ}
    (hdelta : 0 < delta) (hlamdelta : q.lambda + 4 * |p 1| ≤ 4 * delta)
    (hr014 : r0 ≤ 1 / 4) (hsqle : Real.sqrt delta ≤ r0)
    (hmud : q.lambda + Estimates.dispersion (p 0) ≤ delta ^ 2) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0) * (t * profileMass r0 delta)) ^ 2
              / (q.lambda + Operator.theta p)
            + 16 * (t ^ 2 * profileMass r0 delta)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.move1_objective_sixteen hlam p hdelta hlamdelta hr014 hsqle hmud t
