import Manhattan.Paper.LowDegreeFormulas

/-! Lemma 3.1 (`lem:formulas`, `manuscript.tex:827-841`), equation `eq:D2a`: in the
normalization of Section 3.4 (a coefficient function `k` of type `112` placed in
the three axis patterns with the factor `1/√18` by `Manhattan.Paper.type112Freq`,
the two-row sector multiplied by `√2`), the two-row component of `D̃₂* k` is
`-i sin(α) ∫ k(r, r', β) dm(β)`, as an almost-everywhere identity of line-frequency
functions; `α` is the second coordinate of the total frequency. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.lowering_twoRow (p : Fin 2 → ℝ) (k : Lp ℂ 2 (LineTorusMeasure 3)) :
    (((Real.sqrt 2 : ℝ) : ℂ) • rawLowerFreq 2 p (type112Freq k) twoRowPattern :
        UnitAddTorus (Fin 2) → ℂ) =ᵐ[LineTorusMeasure 2] fun θ =>
      -Complex.I * (Real.sin (totalFrequency 2 p twoRowPattern θ 1) : ℂ) *
        ∫ t, (k : UnitAddTorus (Fin 3) → ℂ) (Fin.insertNth 2 t θ)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.lowering_twoRow p k
