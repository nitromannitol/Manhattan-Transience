import Manhattan.Paper.ParityTransport

/-! Equation `eq:majorant` of the arXiv version (`paper/arxiv/main.tex:813-854`) with
constant one and `M = 4(δ + |r| + |r'| + |β|)`, for bounded measurable kernels `k`
(`TorusBoundedThree`) symmetric in their two row frequencies, in place of every
symmetric `K ∈ L²(𝕋³)`, under `λ + 4|p₂| ≤ 4δ`.  The bound reads `½ ∫ M |k|²`
because the paper's `K` is `k/√2`. -/

open scoped lp
open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.sectorForms_rawWalsh_le {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta : ℝ} (hdelta : q.lambda + 4 * |p 1| ≤ 4 * delta)
    {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (hsym : ∀ r r' beta, k r r' beta = k r' r beta) :
    sectorHThreeForm q.lambda p (V4.rawWalsh p hk) + sectorDFourForm hlambda p (V4.rawWalsh p hk)
      ≤ 1 / 2 * V4.evenMajorantEnergy 4 delta k
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.sectorForms_rawWalsh_le hlambda p hdelta hk hsym
