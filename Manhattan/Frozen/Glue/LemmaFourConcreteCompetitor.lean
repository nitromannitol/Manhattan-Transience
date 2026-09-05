import Manhattan.Glue.SummandFourAssembly

/-! Frozen Lemma 5.2 anchor, competitor half: the degree-four sector form of
the concrete correction is bounded by its raw cubic multiplier energy
(`lem:four`, `manuscript.tex:1200-1207`). -/

open MeasureTheory UnitAddTorus Set
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_four_concrete_competitor {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) :
    sectorDFourForm hlambda p
        (Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
          |p 0| (p 0) (p 1))
      ≤ 8 * rawCubicMultiplierEnergy q |p 0| (p 1)
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.sectorDFourForm_shiftedCorrectionWalsh_le hlambda p
