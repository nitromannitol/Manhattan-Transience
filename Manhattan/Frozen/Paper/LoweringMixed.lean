import Manhattan.Paper.LowDegreeFormulas

/-! Lemma 3.1 (`lem:formulas`, `manuscript.tex:827-841`), equation `eq:D2b`: for a
coefficient function `k` of type `112` symmetric in its two row frequencies
(`torusPerm 3 (Equiv.swap 0 1) k = k`), in the normalization of Section 3.4 (the
mixed sector multiplied by `2`), the mixed component of `D̃₂* k` is
`-i √2 sin(β) ∫ k(r, r', β) dm(r')`, almost everywhere. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lowering_mixed (p : Fin 2 → ℝ) (k : Lp ℂ 2 (LineTorusMeasure 3))
    (hk : torusPerm 3 (Equiv.swap 0 1) k = k) :
    ((2 : ℂ) • rawLowerFreq 2 p (type112Freq k) mixedPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      -Complex.I * (Real.sqrt 2 : ℂ) * (Real.sin (totalFrequency 2 p mixedPattern θ 0) : ℂ) *
        ∫ t, (k : UnitAddTorus (Fin 3) → ℂ) (Fin.insertNth 1 t θ)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lowering_mixed p k hk
