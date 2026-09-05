import Manhattan.Glue.ConcreteMultiplier

/-! Frozen (Hsym) anchor: after equation (20) the degree-`n` block `H_n` is
multiplication by `lambda + theta P` (`eq:Hsym` = (20), `manuscript.tex:749`;
`eq:P` = (19), `manuscript.tex:745`). -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Glue.hsym_concrete (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (f : LineFreqL2 n) (σ : Fin n → Axis) :
    ((freqH n lam p f) σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => ((symbolWeight n lam p σ t : ℝ) : ℂ) * (f σ) t
-- FROZEN-STATEMENT-END
:= Manhattan.Glue.coeFn_freqH n lam p f σ
