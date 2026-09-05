import Manhattan.Glue.SummandThree

/-! Frozen Lemma 5.4 anchor: the squared mixed `H⁻¹` norm of the raw residual
is `C √L` (`lem:correction-calculation`, `manuscript.tex:1305`; the four steps
are at `manuscript.tex:1305-1400`). -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Estimates

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_correction_calculation_concrete {q : Parameters}
    (hq : q.Admissible) {C a p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (hfive : PropositionFiveTwoIntegralBound 40 C q a) :
    mixedRawResidualHMinusSq q a p₂ ≤
      (2 + 2 * errorKernelConstant q) * C * Real.sqrt (q.scaleLog a)
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.mixedRawResidualHMinusSq_le_sqrtScale hq ha hp₂ hfive
