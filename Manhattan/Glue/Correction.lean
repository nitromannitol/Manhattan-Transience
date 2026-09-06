import Manhattan.Glue.Competitor
import Manhattan.Walsh.Correction
import Manhattan.Estimates.LemmaFourTwoSuccessor
import Manhattan.Estimates.PropositionFiveTwo

/-!
# Concrete corrected low-degree data

This module packages the scalar functions of Sections 4--5 as honest
degree-one and type-`(1,1,2)` vectors in the concrete Walsh fiber.  The
constant component is computed against the actual `concreteFiberA`; no
coefficient-level cancellation is assumed.

Paper: `manuscript.tex:762-790`, `manuscript.tex:907-958`, and
`manuscript.tex:1024-1063`.
-/

noncomputable section

open MeasureTheory Set
open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Quadratic homogeneity of the positive energy. -/
theorem hEnergy_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Operator.DissipativeSkewPair E) (lambda : ℝ) (a : ℂ) (x : E) :
    P.hEnergy lambda (a • x) = ‖a‖ ^ 2 * P.hEnergy lambda x := by
  unfold Operator.DissipativeSkewPair.hEnergy
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul]
  rw [← ofReal_pow, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

/-- Quadratic homogeneity of the dual energy. -/
theorem hMinusEnergy_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Operator.DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (a : ℂ) (x : E) :
    P.hMinusEnergy hlambda (a • x) =
      ‖a‖ ^ 2 * P.hMinusEnergy hlambda x := by
  unfold Operator.DissipativeSkewPair.hMinusEnergy
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul]
  rw [← ofReal_pow, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

/-- The dual energy is nonnegative: it is the positive energy of the
`H`-preimage. -/
theorem hMinusEnergy_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Operator.DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (u : E) :
    0 ≤ P.hMinusEnergy hlambda u := by
  have hpre := P.hEnergy_nonneg hlambda.le ((P.hEquiv hlambda).symm u)
  rw [P.H_apply_inverse hlambda u] at hpre
  exact hpre

/-- The manuscript's multiplier `sgn(sin p₁)` of `manuscript.tex:1138-1141`
is either zero or unimodular, so it never increases a quadratic energy. -/
theorem norm_ofReal_sign_sq_le_one (x : ℝ) :
    ‖((Real.sign x : ℝ) : ℂ)‖ ^ 2 ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]

/-- Multiplying by `sgn(sin p₁)` does not increase the positive energy. -/
theorem hEnergy_ofReal_sign_smul_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Operator.DissipativeSkewPair E) {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (x : ℝ) (v : E) :
    P.hEnergy lambda (((Real.sign x : ℝ) : ℂ) • v) ≤ P.hEnergy lambda v := by
  rw [hEnergy_smul]
  have h1 := norm_ofReal_sign_sq_le_one x
  have h2 : 0 ≤ P.hEnergy lambda v := P.hEnergy_nonneg hlambda v
  nlinarith

/-- Exact scaling identity behind (24)--(25). -/
theorem normalizedObjective_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : Operator.DissipativeSkewPair E) (V x : E) {lambda b : ℝ}
    (hlambda : 0 < lambda) (hb : 0 < b) :
    P.hEnergy lambda (((b : ℂ)⁻¹) • x) +
        P.hMinusEnergy hlambda (V - P.A (((b : ℂ)⁻¹) • x)) =
      b⁻¹ ^ 2 *
        (P.hEnergy lambda x +
          P.hMinusEnergy hlambda ((b : ℂ) • V - P.A x)) := by
  have hbComplex : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hresidual : V - P.A (((b : ℂ)⁻¹) • x) =
      ((b : ℂ)⁻¹) • ((b : ℂ) • V - P.A x) := by
    rw [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hbComplex,
      one_smul]
  rw [hEnergy_smul, hresidual, hMinusEnergy_smul]
  have hnorm : ‖(b : ℂ)⁻¹‖ ^ 2 = b⁻¹ ^ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  rw [hnorm]
  ring

/-- Specialization of the scaling identity to the concrete synthesized
low-degree competitor. -/
theorem lowDegreeCompetitor_objective_eq_unnormalized
    (d : LowDegreeCompetitorData) (p : Fin 2 → ℝ) {lambda : ℝ}
    (hlambda : 0 < lambda) (hnormalization : 0 < d.normalization) :
    (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
          lambda d.competitor +
        (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (walshL2 ∅ - concreteFiberA p d.competitor) =
      d.normalization⁻¹ ^ 2 *
        ((concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
            (degreeOneFrequencySynthesis Axis.horizontal d.rowFrequency +
              type112WalshSynthesis d.mixedCoefficient) +
          (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda
              ((d.normalization : ℂ) • walshL2 ∅ -
                concreteFiberA p
                  (degreeOneFrequencySynthesis Axis.horizontal d.rowFrequency +
                    type112WalshSynthesis d.mixedCoefficient))) := by
  exact normalizedObjective_eq
    (concreteFiberEnvironment.dissipativeSkewPair p) (walshL2 ∅)
      (degreeOneFrequencySynthesis Axis.horizontal d.rowFrequency +
        type112WalshSynthesis d.mixedCoefficient) hlambda hnormalization

/-- Fixed scale-separation constant used in the construction. -/
def correctedCompetitorK : ℝ := 20

/-- Fixed mesoscopic cutoff parameter. -/
noncomputable def correctedCompetitorRho : ℝ := Real.pi / 20

/-- The resulting small frequency cutoff `r₀=ρ/(100K)`. -/
noncomputable def correctedCompetitorCutoff : ℝ :=
  correctedCompetitorRho / (100 * correctedCompetitorK)

theorem correctedCompetitorCutoff_eq :
    correctedCompetitorCutoff = Real.pi / 40000 := by
  unfold correctedCompetitorCutoff correctedCompetitorRho correctedCompetitorK
  ring

theorem correctedCompetitorCutoff_pos : 0 < correctedCompetitorCutoff := by
  rw [correctedCompetitorCutoff_eq]
  positivity

theorem correctedCompetitorCutoff_lt_one : correctedCompetitorCutoff < 1 := by
  rw [correctedCompetitorCutoff_eq]
  have hpi := Real.pi_le_four
  nlinarith [Real.pi_pos]

/-- Measurability of the explicit degree-one coefficient. -/
theorem degreeOneCoefficient_measurable (q : Estimates.Parameters) (p₁ : ℝ) :
    Measurable (Estimates.degreeOneCoefficient q p₁) := by
  unfold Estimates.degreeOneCoefficient
  apply Measurable.ite measurableSet_Icc
  · fun_prop
  · exact measurable_const

/-- The finite degree-one energy certificate implies that the explicit
coefficient is genuinely square-integrable. -/
theorem degreeOneCoefficient_memLp_of_integralCertificate
    {q : Estimates.Parameters} {p₁ p₂ : ℝ} (hlambda : 0 < q.lambda)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q p₁ p₂) :
    MemLp (Estimates.degreeOneCoefficient q p₁) 2
      (volume.restrict Estimates.torus) := by
  have hfmeas := degreeOneCoefficient_measurable q p₁
  apply (memLp_two_iff_integrable_sq_norm
    hfmeas.aestronglyMeasurable).2
  have hsource := hcert.degreeOneEnergy_integrable.const_mul q.lambda⁻¹
  apply Integrable.mono' hsource
    (hfmeas.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with r
  let w := q.lambda + Estimates.dispersion p₁ + Estimates.dispersion r
  have hw : q.lambda ≤ w := by
    dsimp [w]
    linarith [Estimates.dispersion_nonneg p₁,
      Estimates.dispersion_nonneg r]
  have hinvNonneg : 0 ≤ q.lambda⁻¹ := inv_nonneg.mpr hlambda.le
  have hfactor : 1 ≤ q.lambda⁻¹ * w := by
    calc
      1 = q.lambda⁻¹ * q.lambda := by
        exact (inv_mul_cancel₀ hlambda.ne').symm
      _ ≤ q.lambda⁻¹ * w :=
        mul_le_mul_of_nonneg_left hw hinvNonneg
  have hsq : ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 ≤
      q.lambda⁻¹ *
        (w * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2) := by
    calc
      _ = 1 * ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 := by ring
      _ ≤ (q.lambda⁻¹ * w) *
          ‖Estimates.degreeOneCoefficient q p₁ r‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
      _ = _ := by ring
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖Estimates.degreeOneCoefficient q p₁ r‖)]
  simpa only [Estimates.degreeOneEnergyIntegrand, w] using hsq

/-! ### The degree-one half of the `(shift)` phase

The manuscript's degree-one coefficient is a function of the *shifted* row
frequency `r=p₂+s` of `manuscript.tex:791-800`, where `s` is the Walsh line
frequency.  On line coefficients that substitution is multiplication by
`e^{imp₂}`, i.e. translation of the frequency torus by `p₂`; the declarations
below install it.  Translation is measure preserving, so no coefficient
modulus and no `L²` norm moves.
-/

/-- The multiplicative character is multiplicative in its argument. -/
@[nolint unusedArguments]
theorem fourier_add_arg {T : ℝ} [Fact (0 < T)] (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul]

/-- Translation of the paper's frequency torus, as a linear isometry of `L²`.
On line coefficients this is multiplication by the (shift) phase `e^{ims}`. -/
noncomputable def rowTorusShift (s : ℝ) :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) →ₗᵢ[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + ((s : ℝ) : AddCircle torusPeriod))
    (measurePreserving_add_right _ _)

theorem coeFn_rowTorusShift (s : ℝ)
    (F : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))) :
    (rowTorusShift s F : AddCircle torusPeriod → ℂ)
      =ᵐ[(AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))]
      fun x => F (x + ((s : ℝ) : AddCircle torusPeriod)) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_add_right _ _)

/-- The zero Fourier coordinate, hence the whole constant component of the
competitor, is untouched by the (shift) phase. -/
theorem fourierBasis_repr_rowTorusShift_zero (s : ℝ)
    (F : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))) :
    fourierBasis.repr (rowTorusShift s F) 0 = fourierBasis.repr F 0 := by
  have hzero : ∀ G : Lp ℂ 2
      (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)),
      fourierBasis.repr G 0 =
        ∫ x, (G : AddCircle torusPeriod → ℂ) x ∂AddCircle.haarAddCircle := by
    intro G
    rw [fourierBasis_repr]
    simp [fourierCoeff]
  rw [hzero, hzero, integral_congr_ae (coeFn_rowTorusShift s F)]
  exact integral_add_right_eq_self (fun x => (F : AddCircle torusPeriod → ℂ) x) _

/-- **The competitor's degree-one frequency function `f_p`.**  The paper's
coefficient, read at the shifted row frequency `r=p₂+s` of (shift). -/
noncomputable def correctedRowFrequency {q : Estimates.Parameters}
    {p₁ p₂ : ℝ} (hlambda : 0 < q.lambda)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q p₁ p₂) :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) :=
  rowTorusShift p₂ (realTorusL2 (Estimates.degreeOneCoefficient q p₁) (by
    simpa only [Estimates.torus] using
      degreeOneCoefficient_memLp_of_integralCertificate hlambda hcert))

/-- The explicit `f_p,k_p,b_p` data in the branch where the scalar
certificates apply.

`mixedCoefficient` carries the manuscript's multiplier `sgn(sin p₁)`
(`manuscript.tex:1138-1141`).  `Real.sign 0 = 0`, so that
factor would empty the whole degree-three part at `sin (p 0) = 0`; the guard
`Manhattan.Estimates.sin_ne_zero_of_degreeOneNormalization_ne_zero` shows the
hypothesis `hnormalization` already excludes that point, and
`correctedLowDegreeData_mixedCoefficient_eq_zero_iff` below is the consequence
for this definition. -/
noncomputable def correctedLowDegreeData {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    LowDegreeCompetitorData where
  rowFrequency := correctedRowFrequency hlambda hcert
  mixedCoefficient := (Real.sign (Real.sin (p 0)) : ℂ) •
    shiftedCorrectionType112Coefficients
      (kappa := 40) (by norm_num) hlambda |p 0| (p 0) (p 1)
  normalization := Estimates.degreeOneNormalization q (p 0)
  normalization_ne := hnormalization

/-- The degree-one part of the packaged data is exactly the (shift)-translate
of the synthesis of the paper's coefficient. -/
theorem correctedLowDegreeData_row_eq {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    (correctedLowDegreeData hlambda p hcert hnormalization).rowFrequency =
      rowTorusShift (p 1)
        (realTorusL2 (Estimates.degreeOneCoefficient q (p 0)) (by
          simpa only [Estimates.torus] using
            degreeOneCoefficient_memLp_of_integralCertificate hlambda hcert)) := rfl

/-- The type-`(1,1,2)` coefficient of the packaged data is the manuscript's
`k_p`: the projected correction built from `correctionCoefficient`, multiplied
by `sgn(sin p₁)` as in `manuscript.tex:1138-1141`. -/
theorem correctedLowDegreeData_mixedCoefficient_eq {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient =
      (Real.sign (Real.sin (p 0)) : ℂ) •
        shiftedCorrectionType112Coefficients (kappa := 40) (by norm_num) hlambda
          |p 0| (p 0) (p 1) := rfl

/-- **The sign guard, at the competitor.**  The `sgn(sin p₁)` multiplier
prescribed by `manuscript.tex:1138-1141` cannot empty the degree-three part:
under `hnormalization` the factor `Real.sign (Real.sin (p 0))` is a nonzero
real, so the packaged `mixedCoefficient` vanishes exactly when the underlying
shifted correction does.  Without `hnormalization` this fails, because
`Real.sign 0 = 0`. -/
theorem correctedLowDegreeData_mixedCoefficient_eq_zero_iff {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient = 0 ↔
      shiftedCorrectionType112Coefficients (kappa := 40) (by norm_num) hlambda
        |p 0| (p 0) (p 1) = 0 := by
  rw [correctedLowDegreeData_mixedCoefficient_eq, smul_eq_zero]
  simp [Estimates.ofReal_sign_sin_ne_zero_of_degreeOneNormalization_ne_zero
    hnormalization]

/-- The degree-three part of the packaged data is the projected correction
constructed from `correctionCoefficient`, carrying the manuscript's
`sgn(sin p₁)` multiplier. -/
theorem correctedLowDegreeData_mixed_eq {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0) :
    type112WalshSynthesis
        (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient =
      (Real.sign (Real.sin (p 0)) : ℂ) •
        shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
          |p 0| (p 0) (p 1) := by
  rw [correctedLowDegreeData_mixedCoefficient_eq, map_smul]
  rfl

/-- The scalar identity `D₀* f_p=-b_p` gives exact constant cancellation
for the actual synthesized `f_p+k_p` competitor. -/
theorem correctedLowDegreeData_cancelsAt {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0)
    (hdegreeZero :
      Estimates.degreeZeroAdjoint (p 0)
          (Estimates.degreeOneCoefficient q (p 0)) =
        -(Estimates.degreeOneNormalization q (p 0) : ℂ)) :
    (correctedLowDegreeData hlambda p hcert hnormalization).CancelsAt p := by
  let hf : MemLp (Estimates.degreeOneCoefficient q (p 0)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa only [Estimates.torus] using
      degreeOneCoefficient_memLp_of_integralCertificate hlambda hcert
  have hzero : fourierBasis.repr
      (rowTorusShift (p 1)
        (realTorusL2 (Estimates.degreeOneCoefficient q (p 0)) hf)) 0 =
      (2 * Real.pi)⁻¹ *
        ∫ r in Ioc (-Real.pi) Real.pi, Estimates.degreeOneCoefficient q (p 0) r := by
    rw [fourierBasis_repr_rowTorusShift_zero, fourierBasis_repr_realTorusL2_zero]
  have hrow : inner ℂ (walshL2 ∅)
      (concreteFiberA p
        (degreeOneFrequencySynthesis Axis.horizontal
          (rowTorusShift (p 1)
            (realTorusL2 (Estimates.degreeOneCoefficient q (p 0)) hf)))) =
      (Estimates.degreeOneNormalization q (p 0) : ℂ) := by
    change inner ℂ (walshL2 ∅)
      (concreteFiberA p
        (axisDegreeOneSynthesis Axis.horizontal
          (fourierBasis.repr
            (rowTorusShift (p 1)
              (realTorusL2 (Estimates.degreeOneCoefficient q (p 0)) hf))))) = _
    rw [inner_empty_concreteFiberA_axisDegreeOne, hzero]
    have hidentify :
        Complex.I * (Real.sin (p 0) : ℂ) *
            ((2 * Real.pi)⁻¹ *
              ∫ r in Ioc (-Real.pi) Real.pi,
                Estimates.degreeOneCoefficient q (p 0) r) =
          -Estimates.degreeZeroAdjoint (p 0)
            (Estimates.degreeOneCoefficient q (p 0)) := by
      simp only [Estimates.degreeZeroAdjoint, Estimates.torusIntegral,
        Estimates.torus]
      rw [Complex.real_smul]
      ring
    rw [hidentify, hdegreeZero, neg_neg]
  have hmixed : inner ℂ (walshL2 ∅)
      (concreteFiberA p
        (type112WalshSynthesis
          (correctedLowDegreeData hlambda p hcert hnormalization).mixedCoefficient)) = 0 :=
    inner_empty_concreteFiberA_type112 p _
  rw [LowDegreeCompetitorData.CancelsAt,
    LowDegreeCompetitorData.competitor,
    correctedLowDegreeData_row_eq hlambda p hcert hnormalization]
  rw [map_smul, map_add, inner_sub_right, inner_walshL2,
    inner_smul_right, inner_add_right, hrow, hmixed]
  have hbComplex :
      (Estimates.degreeOneNormalization q (p 0) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnormalization
  rw [add_zero]
  change (if ∅ = ∅ then 1 else 0) -
    (Estimates.degreeOneNormalization q (p 0) : ℂ)⁻¹ *
      (Estimates.degreeOneNormalization q (p 0) : ℂ) = 0
  rw [if_pos rfl, inv_mul_cancel₀ hbComplex]
  simp

/-- In the horizontal high-logarithmic regime, Lemma 4.1 v3 supplies a
nonzero normalization and the explicit synthesized data cancels the
constant component exactly. -/
theorem correctedLowDegreeData_exists_horizontal
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambdaOne : lambda ≤ 1)
    (p : Fin 2 → ℝ) (hp₀ : p 0 ∈ Estimates.torus)
    (hp₁ : p 1 ∈ Estimates.torus) (horder : |p 1| ≤ |p 0|)
    (hpositive : 0 < |p 0|)
    (hlog :
      (Estimates.Parameters.logThreshold
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩) <
        Estimates.Parameters.scaleLog
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ |p 0|) :
    let q : Estimates.Parameters :=
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
    ∃ hcert : Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1),
      ∃ hnormalization : Estimates.degreeOneNormalization q (p 0) ≠ 0,
        (correctedLowDegreeData hlambda p hcert hnormalization).CancelsAt p := by
  obtain ⟨c, _, hc, _, hmain⟩ :=
    Estimates.lemmaFourTwoSuccessorV3Claim_proved
      correctedCompetitorK correctedCompetitorRho
      (by simp [correctedCompetitorK])
      (by simp [correctedCompetitorRho]; positivity)
      (by simp [correctedCompetitorRho])
  let q : Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  have hs := hmain lambda hlambda hlambdaOne (p 0) (p 1)
    hp₀ hp₁ horder hpositive hlog
  have hthresholdPos : 0 < q.logThreshold := by
    simp only [q, Estimates.Parameters.logThreshold, correctedCompetitorK]
    have : 0 < Real.log 20 := Real.log_pos (by norm_num)
    linarith
  have hscalePos : 0 < q.scaleLog |p 0| := hthresholdPos.trans hlog
  have hnormalizationPos : 0 < Estimates.degreeOneNormalization q (p 0) :=
    (mul_pos (mul_pos hc hpositive) hscalePos).trans_le hs.2.2.1
  refine ⟨hs.1, hnormalizationPos.ne', ?_⟩
  exact correctedLowDegreeData_cancelsAt hlambda p hs.1
    hnormalizationPos.ne' hs.2.1

end Manhattan.Glue
