import Manhattan.Glue.CorrectionLowering

/-! Frozen Lemma 5.3 anchor for the competitor, on the RAW / FREQUENCY side
(`lem:distinct`, `manuscript.tex:1212-1221`).

SCOPE, recorded with the node: `projectionErrorHMinusSq` is a frequency-side
scalar.  Nothing in the tree proves it equal to the operator-level
`‖Π₂ D̃₂* k̃ - D₂* k‖²_{H⁻¹}` of an actual Walsh vector; that bridge is still open.  This node must therefore NOT be read as
an operator-level rendering of Lemma 5.3.  The qualitative clause is
independently covered at the Walsh level by
`Manhattan.Glue.type112DStarTwoRow_correction`. -/

open MeasureTheory Set
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_distinct_concrete_frequency {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    (rawProjectionDifference 1 1 (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) 0
        (rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))))).twoRow = 0 ∧
      projectionErrorHMinusSq q
          (rawDiagonalPart (p 1)
            (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) ≤
        rawMultiplierEnergy 40 q (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.lemma_distinct_correction hlambda a p
