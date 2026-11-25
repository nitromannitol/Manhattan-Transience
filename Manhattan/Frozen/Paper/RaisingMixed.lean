import Manhattan.Paper.LowDegreeFormulas

/-! Lemma 3.1 (`lem:formulas`, `manuscript.tex:827-841`), third formula of `eq:D1`:
for a degree-one coefficient carrying only a row sign, `(D̃₁ f)₁₂ = i sin(r) f(r)`
in the normalization of Section 3.4, almost everywhere. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.raising_mixed (p : Fin 2 → ℝ) (c : OrderedCoefficient 1)
    (hc : (orderedFourier 1 c) columnPattern = 0) :
    ((2 : ℂ) • (orderedFourier 2 (rawRaise 1 p c)) mixedPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      Complex.I * (Real.sin (totalFrequency 2 p mixedPattern θ 1) : ℂ) *
        ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 1 θ)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.raising_mixed p c hc
