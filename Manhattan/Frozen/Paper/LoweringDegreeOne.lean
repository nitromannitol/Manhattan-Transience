import Manhattan.Paper.LowDegreeFormulas

/-! Lemma 3.1 (`lem:formulas`, `manuscript.tex:827-841`), first formula of `eq:D1`:
for a degree-one coefficient carrying only a row sign (its column sector is zero),
`D₀* f = -i sin(p₁) ∫ f dm`. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lowering_degreeOne (p : Fin 2 → ℝ) (c : OrderedCoefficient 1)
    (hc : (orderedFourier 1 c) columnPattern = 0) :
    ((orderedFourier 0 (rawLower 0 p c)) ![] : UnitAddTorus (Fin 0) → ℂ)
      =ᵐ[LineTorusMeasure 0] fun θ =>
        -Complex.I * (Real.sin (p 0) : ℂ) *
          ∫ t, ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.insertNth 0 t θ)
            ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lowering_degreeOne p c hc
