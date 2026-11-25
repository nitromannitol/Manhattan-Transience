import Manhattan.Paper.LemmaRaise

/-! Lemma 5.1 (`lem:raise`, `manuscript.tex:1179-1191`), equation `eq:raise`, at every
degree `n`: in the sector of axis pattern `σ`, the line-frequency coefficient of
`D̃_n c` is `(i/(n+1)) Σ_a sin(P_{σ_a}) ĉ_{σ without a}`, almost everywhere, with `P`
the total frequency after raising. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.orderedFourier_rawRaise (n : ℕ) (p : Fin 2 → ℝ) (c : OrderedCoefficient n)
    (σ : Fin (n + 1) → Axis) :
    ((orderedFourier (n + 1) (rawRaise n p c)) σ : UnitAddTorus (Fin (n + 1)) → ℂ)
      =ᵐ[LineTorusMeasure (n + 1)] fun θ =>
        Complex.I / ((n + 1 : ℕ) : ℂ) * ∑ r : Fin (n + 1),
          (Real.sin (totalFrequency (n + 1) p σ θ (axisIndex (σ r))) : ℂ) *
            ((orderedFourier n c) (Fin.removeNth r σ) : UnitAddTorus (Fin n) → ℂ)
              (Fin.removeNth r θ)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.orderedFourier_rawRaise n p c σ
