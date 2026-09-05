import Manhattan.Glue.RaisingEnergy

/-! Frozen Lemma 5.2 anchor, operator half: the degree-four raising energy
bound for a general degree-three coefficient (`lem:four`,
`manuscript.tex:1200-1207`; `eq:four` = (47), `manuscript.tex:1203`). -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.lemma_four_concrete_raising_energy
    {q : Estimates.Parameters} (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (i : Fin 2)
    (g : DegreeCoefficient 3) :
    (∑' σ : Fin 4 → Axis, ∫ t, (symbolWeight 4 q.lambda p σ t)⁻¹ *
        ‖((lineIndexFourier 4 (degreeRaiseDir p i g)) σ :
          UnitAddTorus (Fin 4) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 4))
      ≤ 2 * ∑' σ : Fin 3 → Axis, ∫ t,
          Estimates.multiplier 40 q (totalFrequency 3 p σ t) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure 3)
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le (by norm_num : (12:ℝ) ≤ 40) hlam p i g
