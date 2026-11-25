import Manhattan.Paper.EffectiveEnergy

/-! Equation `eq:optimized` of the arXiv version (`paper/arxiv/main.tex:1052-1067`) with the
constant `16`, in the form `prop:frequency` uses: for `0 < r₀ ≤ 1/4`, on
`√λ + a(p) ≤ r₀⁴`, `r_λ(p) ≤ 1/(H₀ + s² Z_δ/16)` for some `s` with `s² ≥ (2/π)² a(p)²`.
Here `λ ∈ (0,1]`, `p ∈ 𝕋²`, `H₀ = λ + θ(p)`, `δ = √λ + a(p)` and `Z_δ = Zdelta r₀ δ` is taken
over `√δ ≤ |r| ≤ r₀`.  The printed `eq:optimized` has `s = sin p₁` under `|p₂| ≤ |p₁|`; this
statement only asserts that some such `s` exists (it covers both orderings of `|p₁|` and
`|p₂|`). -/

open scoped lp
open MeasureTheory Set UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.V4.Frequency Manhattan.Paper
open LatticeProb.Analysis
open Manhattan.V4 Manhattan.Operator

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.move2Supply_sixteen {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 16
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.move2Supply_sixteen hr0 hr014
