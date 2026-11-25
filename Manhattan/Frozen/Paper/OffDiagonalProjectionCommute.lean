import Manhattan.Paper.LemmaRaiseMultiplier

/-! Lemma 5.1 (`lem:raise`, `manuscript.tex:1189-1190`): `Π_n` commutes with every
multiplier by a continuous function of the total frequency `P` (the paper also
states it for bounded Borel functions; the continuous case is what the proofs use). -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.offDiagonalProjection_comp_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ)
    (m : C(UnitAddTorus (Fin 2), ℂ)) :
    offDiagonalProjection n ∘L orderedMultiplier n p m =
      orderedMultiplier n p m ∘L offDiagonalProjection n
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.offDiagonalProjection_comp_orderedMultiplier n p m
