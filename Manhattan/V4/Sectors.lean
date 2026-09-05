import Manhattan.V4.MixedBridge
import Manhattan.V4.CompetitorEnergy
import Manhattan.Glue.SummandThreeTwoRow

/-!
# Version 4, Move 1: the sector splitting (residue B-3)

 (B-3) records that the repository has only
the parallelogram bounds `Manhattan.Glue.hEnergy_add_le` and
`Manhattan.Glue.hMinusEnergy_add_le`, and no exact additivity over orthogonal
Walsh sectors. For the two higher sectors that is harmless: a factor two there
only doubles the constant `C` of Move 1. For the **degree-zero** sector it is
not harmless: `Manhattan.V4.Frequency.V4Move2Supply` asks for the closed form
`1/(λ + θ(p) + s² Z_δ/C)` with the coefficient **one** on `λ + θ(p)`, and a
factor `A > 1` there cannot be absorbed into `C`.

This file therefore proves exact additivity across the degree-zero sector. The
constant Walsh vector is an eigenvector of `H` (`Manhattan.concreteH_empty`), so
`H⁻¹` preserves both the line it spans (`Manhattan.concreteHInverse_empty`) and
its orthogonal complement, and the two cross terms in
`‖c·1 + v‖²₋₁` vanish for real `c`. The higher sectors then pay the
parallelogram factor two, once for the degree-two/degree-four split and once for
the two-row/mixed split inside the degree-two sector.

The main statement is `resolventQuadratic_le_v4Move1`.
-/

noncomputable section
open MeasureTheory ComplexConjugate InnerProductSpace RCLike
open scoped ComplexConjugate InnerProduct

namespace Manhattan.V4


open Manhattan.Operator Manhattan.Glue

/-- `H` is symmetric for the full complex inner product. -/
theorem inner_H_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : DissipativeSkewPair E) (lambda : ℝ) (x y : E) :
    inner ℂ (P.H lambda x) y = inner ℂ x (P.H lambda y) := by
  rw [← (P.H lambda).adjoint_inner_right x y,
    show (P.H lambda)† = P.H lambda from P.H_selfAdjoint lambda]

/-- `H⁻¹` preserves the orthogonal complement of the constant Walsh vector. -/
theorem inner_empty_hInverse_eq_zero {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    {v : WalshL2} (hv : inner ℂ (Manhattan.walshL2 ∅) v = 0) :
    inner ℂ (Manhattan.walshL2 ∅)
        (((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEquiv hlambda).symm v)
      = 0 := by
  set P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p with hP
  set z := (P.hEquiv hlambda).symm v with hz
  have hHz : P.H lambda z = v := P.H_apply_inverse hlambda v
  have hkey : inner ℂ (P.H lambda (Manhattan.walshL2 ∅)) z = 0 := by
    rw [inner_H_symm P lambda, hHz, hv]
  rw [Manhattan.concreteH_empty] at hkey
  rw [inner_smul_left] at hkey
  have hden : (lambda + Operator.theta p) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hlambda (Manhattan.operatorTheta_nonneg p)).ne'
  have hconj : (starRingEnd ℂ) ((lambda + Operator.theta p : ℝ) : ℂ)
      = ((lambda + Operator.theta p : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hconj] at hkey
  have hne : ((lambda + Operator.theta p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  exact (mul_eq_zero.mp hkey).resolve_left hne

/-- **Exact additivity across the degree-zero sector.** The constant Walsh
vector is an eigenvector of `H`, so `H⁻¹` preserves both the line it spans and
its orthogonal complement, and the dual energy of a real multiple of the
constant plus an orthogonal vector is the sum of the two dual energies. No
parallelogram factor is lost here. -/
theorem hMinusEnergy_empty_add {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (c : ℝ) {v : WalshL2} (hv : inner ℂ (Manhattan.walshL2 ∅) v = 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (((c : ℝ) : ℂ) • Manhattan.walshL2 ∅ + v)
      = c ^ 2 / (lambda + Operator.theta p)
        + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda v := by
  have hzero := inner_empty_hInverse_eq_zero hlambda p hv
  have hinvempty := Manhattan.concreteHInverse_empty hlambda p
  have h1 : inner ℂ (Manhattan.walshL2 ∅) (Manhattan.walshL2 ∅) = (1 : ℂ) := by
    rw [Manhattan.inner_walshL2, if_pos rfl]
  have h2 : inner ℂ v (Manhattan.walshL2 ∅) = 0 := by
    rw [← InnerProductSpace.conj_inner_symm, hv, map_zero]
  rw [DissipativeSkewPair.hMinusEnergy, DissipativeSkewPair.hMinusEnergy, map_add,
    map_smul, hinvempty]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    h1, h2, hzero, Complex.conj_ofReal, mul_zero, add_zero, zero_add, mul_one]
  rw [map_add]
  congr 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [show re ((c * ((lambda + Operator.theta p)⁻¹ * c) : ℝ) : ℂ)
      = c * ((lambda + Operator.theta p)⁻¹ * c) from rfl, div_eq_mul_inv, sq]
  ring


/-- **The Version 4 three-sector decomposition.** Unlike
`Manhattan.Glue.unnormalizedResidual_eq_sector_sum`, no degree-zero
cancellation is assumed: the uncancelled constant coefficient is kept as the
first summand. This is what lets Move 1 carry the coefficient `1` on
`(1-s∫φ)²/h₀`. -/
theorem unnormalizedResidual_eq_three_sectors (p : Fin 2 → ℝ) (b : ℝ) {c : ℂ}
    {f k : WalshL2} (hf : f ∈ Manhattan.walshDegree 1) (hk : k ∈ Manhattan.walshDegree 3)
    (hc : inner ℂ (Manhattan.walshL2 ∅) (unnormalizedResidual p b f k) = c) :
    unnormalizedResidual p b f k
      = c • Manhattan.walshL2 ∅
        + (walshSectorComponent (fun S => S.card = 2) (unnormalizedResidual p b f k)
          + walshSectorComponent (fun S => S.card = 4)
              (unnormalizedResidual p b f k)) := by
  classical
  refine walshL2_ext ?_
  intro U
  rw [inner_add_right, inner_add_right, inner_smul_right, Manhattan.inner_walshL2,
    inner_walshL2_walshSectorComponent, inner_walshL2_walshSectorComponent]
  by_cases hempty : U = ∅
  · subst hempty
    rw [if_pos rfl, if_neg (by simp), if_neg (by simp), hc]
    ring
  rw [if_neg hempty, mul_zero, zero_add]
  by_cases h2 : U.card = 2
  · rw [if_pos h2, if_neg (by omega), add_zero]
  by_cases h4 : U.card = 4
  · rw [if_neg h2, if_pos h4, zero_add]
  rw [if_neg h2, if_neg h4, add_zero]
  have hcard : U.card ≠ 0 := fun h => hempty (Finset.card_eq_zero.mp h)
  rw [unnormalizedResidual, inner_sub_right, inner_smul_right,
    Manhattan.inner_walshL2, if_neg hempty, map_add, inner_add_right,
    inner_walshL2_concreteFiberA_eq_zero hf p (by omega) (by omega),
    inner_walshL2_concreteFiberA_eq_zero hk p (by omega) (by omega)]
  simp


/-- The degree-two and degree-four sectors carry no constant Walsh
coefficient. -/
theorem inner_empty_sector_sum (x : WalshL2) :
    inner ℂ (Manhattan.walshL2 ∅)
        (walshSectorComponent (fun S => S.card = 2) x
          + walshSectorComponent (fun S => S.card = 4) x) = 0 := by
  classical
  rw [inner_add_right, inner_walshL2_walshSectorComponent,
    inner_walshL2_walshSectorComponent, if_neg (by simp), if_neg (by simp), add_zero]

/-- **The Version 4 residual dual energy, split.** The degree-zero summand
keeps the coefficient `1`; only the two higher sectors pay the parallelogram
factor `2`. -/
theorem hMinusEnergy_residual_le {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (b : ℝ) {c : ℝ} {f k : WalshL2}
    (hf : f ∈ Manhattan.walshDegree 1) (hk : k ∈ Manhattan.walshDegree 3)
    (hc : inner ℂ (Manhattan.walshL2 ∅) (unnormalizedResidual p b f k)
      = ((c : ℝ) : ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (unnormalizedResidual p b f k)
      ≤ c ^ 2 / (lambda + Operator.theta p)
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshSectorComponent (fun S => S.card = 2)
              (Manhattan.concreteFiberA p (f + k)))
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshSectorComponent (fun S => S.card = 4)
              (Manhattan.concreteFiberA p k)) := by
  have hsplit := unnormalizedResidual_eq_three_sectors p b hf hk hc
  rw [hsplit, hMinusEnergy_empty_add hlambda p c
    (inner_empty_sector_sum (unnormalizedResidual p b f k))]
  have hpar := hMinusEnergy_add_le
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda
    (walshSectorComponent (fun S => S.card = 2) (unnormalizedResidual p b f k))
    (walshSectorComponent (fun S => S.card = 4) (unnormalizedResidual p b f k))
  rw [hMinusEnergy_sector_two_residual hlambda p b f k,
    hMinusEnergy_sector_four_residual hlambda p b hf] at hpar
  linarith

/-- **Move 1, the sector form.** The Cauchy-Schwarz bound of Version 4, Step 1,
split into the four sectors that actually occur. The degree-zero residual keeps
the coefficient `1`. -/
theorem resolventQuadratic_le_v4Sectors {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {c : ℝ} {f k : WalshL2}
    (hf : f ∈ Manhattan.walshDegree 1) (hk : k ∈ Manhattan.walshDegree 3)
    (hc : inner ℂ (Manhattan.walshL2 ∅) (unnormalizedResidual p 1 f k)
      = ((c : ℝ) : ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ c ^ 2 / (lambda + Operator.theta p)
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda f
        + 2 * ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda k
            + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
              hlambda (walshSectorComponent (fun S => S.card = 4)
                (Manhattan.concreteFiberA p k)))
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshSectorComponent (fun S => S.card = 2)
              (Manhattan.concreteFiberA p (f + k))) := by
  have hres : unnormalizedResidual p 1 f k
      = Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p (f + k) := by
    rw [unnormalizedResidual, Complex.ofReal_one, one_smul]
  have hcs := (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    p).resolventQuadratic_le hlambda (Manhattan.walshL2 ∅) (f + k)
  have hA : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).A
      = Manhattan.concreteFiberA p := rfl
  rw [hA, ← hres] at hcs
  have hpar := hEnergy_add_le
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda.le f k
  have hsec := hMinusEnergy_residual_le hlambda p 1 hf hk hc
  linarith


/-! ## The two-row / mixed split inside the degree-two sector -/

/-- **The degree-two sector of `A_p(f+k)` splits into its two-row and mixed
halves.** This is `Manhattan.Glue.hMinusEnergy_sectorTwo_le` read at
`A_p(f+k)` itself rather than at the residual, which is what the Version 4
three-sector decomposition produces. -/
theorem hMinusEnergy_sectorTwo_split {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (c : Manhattan.RowLineCoefficient)
    (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (walshSectorComponent (fun S => S.card = 2)
          (Manhattan.concreteFiberA p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
              + Manhattan.type112WalshSynthesis kc)))
      ≤ 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))))
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type12WalshSynthesis
              (Manhattan.type12WalshAnalysis (walshRaise p
                  (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
                - Manhattan.type112DStarMixed p kc)) := by
  rw [walshSectorComponent_two_concreteFiberA_eq p c kc hk]
  exact hMinusEnergy_add_le _ hlambda _ _

/-! ## Move 1 in sector form -/

/-- **Move 1 of Version 4, in the four sectors that occur.** The competitor is
the degree-one row vector `D₁`-source `axisDegreeOneSynthesis horizontal c`
together with the degree-three vector `type112WalshSynthesis kc`; the hypothesis
`hk` is `(D₂*k)₁₁ = 0`, and `hc` is the uncancelled degree-zero
coefficient. The degree-zero summand carries the coefficient one; the
degree-three cost appears in exactly the combination
`Glue.sectorHThreeForm + Glue.sectorDFourForm` that
`Manhattan.V4.operatorEstimate` bounds. -/
theorem resolventQuadratic_le_v4Move1 {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {cc : ℝ} (c : Manhattan.RowLineCoefficient)
    (kc : ℓ²(Manhattan.Type112Index, ℂ))
    (hk : Manhattan.type112DStarTwoRow p kc = 0)
    (hc : inner ℂ (Manhattan.walshL2 ∅)
        (unnormalizedResidual p 1
          (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
          (Manhattan.type112WalshSynthesis kc)) = ((cc : ℝ) : ℂ)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ cc ^ 2 / (lambda + Operator.theta p)
        + 2 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
            lambda (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)
        + 2 * (sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
            + sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc))
        + 4 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
              (walshRaise p
                (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))))
        + 4 * (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.type12WalshSynthesis
              (Manhattan.type12WalshAnalysis (walshRaise p
                  (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c))
                - Manhattan.type112DStarMixed p kc)) := by
  have hf : Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c
      ∈ Manhattan.walshDegree 1 := axisDegreeOneSynthesis_mem_walshDegree _ c
  have hkk : Manhattan.type112WalshSynthesis kc ∈ Manhattan.walshDegree 3 :=
    Manhattan.type112WalshSynthesis_mem_degree kc
  have hmain := resolventQuadratic_le_v4Sectors hlambda p hf hkk hc
  have hsplit := hMinusEnergy_sectorTwo_split hlambda p c kc hk
  have hH : sectorHThreeForm lambda p (Manhattan.type112WalshSynthesis kc)
      = (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.type112WalshSynthesis kc) := rfl
  have hD : sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis kc)
      = (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 4)
          (Manhattan.concreteFiberA p (Manhattan.type112WalshSynthesis kc))) := rfl
  rw [hH, hD]
  linarith

end Manhattan.V4
