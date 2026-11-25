import Manhattan.Paper.EffectiveEnergy

/-! Equation `eq:optimized` of the arXiv version (`paper/arxiv/main.tex:1052-1067`) with the
constant `16`, in the form `prop:frequency` uses: for `0 < r₀ ≤ 1/4`, on
`√λ + a(p) ≤ r₀⁴`, `r_λ(p) ≤ 1/(H₀ + s² Z_δ/16)` for some `s` with `s² ≥ (2/π)² a(p)²`. -/

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
