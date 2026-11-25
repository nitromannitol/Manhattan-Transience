import Manhattan.Paper.AnnealedConstant

/-! Equation `eq:green-explicit` of the arXiv version (`paper/arxiv/main.tex:1115-1121`)
with the printed constant `2048`: `∫₀^∞ p̄_t(0,0) dt ≤ 2048`.  The proof reaches about
`1578`. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Manhattan Manhattan.V4.Frequency Manhattan.Estimates Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.annealed_green_le_2048 :
    (∫⁻ t in Ici (0:ℝ), Manhattan.annealedContinuousKernel t 0 0) ≤ ENNReal.ofReal 2048
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.annealed_green_le_2048
