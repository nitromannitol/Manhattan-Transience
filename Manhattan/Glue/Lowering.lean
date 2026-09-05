import Manhattan.Glue.Correction
import Manhattan.Walsh.LowDegreeSectors

/-!
# Exact lowering components of the corrected type-112 vector

These declarations specialize the complete Finset lowering maps to the
explicit projected correction `k_p`. Both components are extracted from the
actual concrete skew fiber. The displayed coefficient formulas are the
factorial-free versions of (D2a) and (D2b).

Paper: `manuscript.tex:827-840` and `manuscript.tex:1238-1255`.
.
-/

namespace Manhattan.Glue

noncomputable section

open ComplexConjugate

/-- The exact two-row component of `D₂* k_p`. -/
noncomputable def correctedD2StarTwoRow {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    ℓ²(Type11Index, ℂ) :=
  type112DStarTwoRow p
    (correctionType112Coefficients (kappa := 40) (by norm_num) hlambda a (p 1))

/-- The exact mixed component of `D₂* k_p`. -/
noncomputable def correctedD2StarMixed {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    ℓ²(Type12Index, ℂ) :=
  type112DStarMixed p
    (correctionType112Coefficients (kappa := 40) (by norm_num) hlambda a (p 1))

/-- The complete degree-two lowering vector of the corrected type-`112`
element. -/
noncomputable def correctedD2Star {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) : WalshL2 :=
  type112DStar p
    (correctionType112Coefficients (kappa := 40) (by norm_num) hlambda a (p 1))

/-- (D2a), with every normalization supplied by the Finset isometries. -/
theorem correctedD2StarTwoRow_apply_finset {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ)
    (T : Type11Index) :
    correctedD2StarTwoRow hlambda a p T =
      (fiberASpatialCoefficient p T.1).sum fun S z =>
        conj z * type112CoefficientAt
          (correctionType112Coefficients (kappa := 40) (by norm_num)
            hlambda a (p 1)) S := by
  exact type112DStarTwoRow_apply_finset p _ T

/-- (D2b), with coefficient one in the Finset isometry. The tuple-space
`sqrt 2` from the manuscript is exactly absent, while
`correctionCoefficient` carries `i * sin beta` rather than
`i * sin beta / sqrt 2`. -/
theorem correctedD2StarMixed_apply_finset {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ)
    (T : Type12Index) :
    correctedD2StarMixed hlambda a p T =
      (fiberASpatialCoefficient p T.1).sum fun S z =>
        conj z * type112CoefficientAt
          (correctionType112Coefficients (kappa := 40) (by norm_num)
            hlambda a (p 1)) S := by
  exact type112DStarMixed_apply_finset p _ T

/-- The packaged corrected lowering is exactly the orthogonal sum of the two
computed coefficient sectors. -/
theorem correctedD2Star_eq_components {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    correctedD2Star hlambda a p =
      type11WalshSynthesis (correctedD2StarTwoRow hlambda a p) +
        type12WalshSynthesis (correctedD2StarMixed hlambda a p) := rfl

end

end Manhattan.Glue
