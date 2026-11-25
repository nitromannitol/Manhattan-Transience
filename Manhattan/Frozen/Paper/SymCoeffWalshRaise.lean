import Manhattan.Paper.LemmaRaise

/-! Lemma 5.1 (`lem:raise`, `manuscript.tex:1188-1189`): `D_n = Π_{n+1} D̃_n Π_n` at every
degree, in the symmetric coefficients of Section 3.1. -/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue Manhattan.Paper

-- FROZEN-STATEMENT-BEGIN
theorem Manhattan.Frozen.Paper.symCoeff_walshRaise (n : ℕ) (p : Fin 2 → ℝ) (F : WalshL2) :
    symCoeff (n + 1) (walshRaise p F) =
      offDiagonalProjection (n + 1)
        (rawRaise n p (offDiagonalProjection n (symCoeff n F)))
-- FROZEN-STATEMENT-END
:= Manhattan.Paper.symCoeff_walshRaise n p F
