import Manhattan.Paper.LowDegreeFormulas

/-! Lemma 3.1 (`lem:formulas`, `manuscript.tex:827-841`), second formula of `eq:D1`:
`(D̃₁ f)₁₁ = (i/√2) sin(p₁) [f(r) + f(r')]` in the normalization of Section 3.4, almost
everywhere; no hypothesis on the column sector of `f` is needed here. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.raising_twoRow (p : Fin 2 → ℝ) (c : OrderedCoefficient 1) :
    (((Real.sqrt 2 : ℝ) : ℂ) • (orderedFourier 2 (rawRaise 1 p c)) twoRowPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      Complex.I / (Real.sqrt 2 : ℂ) * (Real.sin (p 0) : ℂ) *
        (((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 0 θ) +
          ((orderedFourier 1 c) rowPattern : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth 1 θ))
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.raising_twoRow p c
