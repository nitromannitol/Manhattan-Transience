import Manhattan.Glue.SummandsTorus
import Manhattan.Glue.Correction

/-!
# The first summand of (22): the degree-one energy `⟨f,H₁f⟩`

This file computes the concrete degree-one row energy
`⟨f,H₁f⟩` of the actual operator `concreteFiberS` as the explicit weighted
frequency integral of (Hsym) in degree one, and bounds it by the scalar
`degreeOneEnergy` of Lemma 4.1 v3.

The competitor of `Glue/Correction.lean` carries the paper's coefficient in
the *shifted* variable `r=p₂+s` of `eq:shift` (`manuscript.tex:791-800`)
while the Walsh vector it synthesizes carries it in the *unshifted* line
frequency `s`.  The two weights `λ+d(p₁)+d(p₂+s)` and `λ+d(p₁)+d(s)`
therefore differ; `dispersion_add_le` and `dispersion_le_of_abs_le` show
they are comparable with the universal factor three, which is all the
estimate (23) needs.

Paper: `manuscript.tex:743-758` ((Hsym)), `manuscript.tex:869-958`
(Lemma 4.1), `manuscript.tex:762-790` ((22)-(23)).
-/

noncomputable section

open MeasureTheory Set
open ComplexConjugate InnerProductSpace RCLike
open scoped InnerProduct

namespace Manhattan.Glue

/-! ### The row sector of degree one -/

/-- The complete degree-one synthesis is the sum of its coefficients. -/
theorem hasSum_axisDegreeOneSynthesis (i : Manhattan.Axis)
    (c : Manhattan.RowLineCoefficient) :
    HasSum (fun k : ℤ => c k • Manhattan.walshL2 {(i, k)})
      (Manhattan.axisDegreeOneSynthesis i c) := by
  have horth := (Manhattan.orthonormal_walshL2.comp
    (fun m : ℤ => ({(i, m)} : Finset Manhattan.LineIndex)) (by
      intro m n h
      simpa using h))
  simpa only [Manhattan.axisDegreeOneSynthesis,
    LinearIsometry.toSpanSingleton_apply] using
    horth.orthogonalFamily.hasSum_linearIsometry c

/-- A lattice translation moves a horizontal line by its second coordinate. -/
theorem translateWalshIndex_rowSingleton (x : Manhattan.Operator.Lattice) (k : ℤ) :
    Manhattan.translateWalshIndex x {(Manhattan.Axis.horizontal, k)} =
      {(Manhattan.Axis.horizontal, k + x 1)} := by
  rw [Manhattan.translateWalshIndex, Finset.map_singleton]
  rfl

theorem environmentShift_rowSingleton (x : Manhattan.Operator.Lattice) (k : ℤ) :
    Manhattan.environmentShift x
        (Manhattan.walshL2 {(Manhattan.Axis.horizontal, k)}) =
      Manhattan.walshL2 {(Manhattan.Axis.horizontal, k + x 1)} := by
  rw [Manhattan.environmentShift_walshL2_public, translateWalshIndex_rowSingleton]

/-- Translations parallel to the rows fix the row sector. -/
theorem environmentShift_row_fixed {x : Manhattan.Operator.Lattice} (hx : x 1 = 0)
    (c : Manhattan.RowLineCoefficient) :
    Manhattan.environmentShift x
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c) =
      Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c := by
  have hs := hasSum_axisDegreeOneSynthesis Manhattan.Axis.horizontal c
  have h1 := hs.mapL (Manhattan.environmentShift x)
  have h2 : ∀ k : ℤ,
      Manhattan.environmentShift x
          (c k • Manhattan.walshL2 {(Manhattan.Axis.horizontal, k)}) =
        c k • Manhattan.walshL2 {(Manhattan.Axis.horizontal, k)} := by
    intro k
    rw [map_smul, environmentShift_rowSingleton, hx, add_zero]
  have h3 : HasSum (fun k : ℤ =>
      c k • Manhattan.walshL2 ({(Manhattan.Axis.horizontal, k)} : Finset Manhattan.LineIndex))
      (Manhattan.environmentShift x
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c)) := by
    simpa only [h2] using h1
  exact h3.unique hs

/-- The row sector's transverse shift is, in Fourier coordinates,
multiplication by `fourier (-1)`. -/
theorem inner_row_environmentShift (F : Lp ℂ 2 haarTorus) :
    inner ℂ (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal F)
        (Manhattan.environmentShift (Manhattan.Operator.axisVector 1)
          (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal F)) =
      inner ℂ (fourierMul (-1) F) F := by
  set c : Manhattan.RowLineCoefficient := fourierBasis.repr F with hc
  set y : Manhattan.WalshL2 :=
    Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal c with hy
  have haxis : (Manhattan.Operator.axisVector 1) 1 = 1 := by
    simp [Manhattan.Operator.axisVector]
  have hs := hasSum_axisDegreeOneSynthesis Manhattan.Axis.horizontal c
  have h1 := hs.mapL (Manhattan.environmentShift (Manhattan.Operator.axisVector 1))
  have h2 : ∀ k : ℤ,
      Manhattan.environmentShift (Manhattan.Operator.axisVector 1)
          (c k • Manhattan.walshL2 {(Manhattan.Axis.horizontal, k)}) =
        c k • Manhattan.walshL2 {(Manhattan.Axis.horizontal, k + 1)} := by
    intro k
    rw [map_smul, environmentShift_rowSingleton, haxis]
  have h3 : HasSum (fun k : ℤ =>
      c k • Manhattan.walshL2
        ({(Manhattan.Axis.horizontal, k + 1)} : Finset Manhattan.LineIndex))
      (Manhattan.environmentShift (Manhattan.Operator.axisVector 1) y) := by
    simpa only [h2] using h1
  have h4 := h3.mapL (innerSL ℂ y)
  have h5 : ∀ k : ℤ,
      (innerSL ℂ y) (c k • Manhattan.walshL2
        ({(Manhattan.Axis.horizontal, k + 1)} : Finset Manhattan.LineIndex)) =
        c k * conj (c (k + 1)) := by
    intro k
    rw [innerSL_apply_apply, inner_smul_right, ← Manhattan.inner_axisDegreeOneSynthesis
      Manhattan.Axis.horizontal (k + 1) c, ← inner_conj_symm]
  have h6 : HasSum (fun k : ℤ => c k * conj (c (k + 1)))
      (inner ℂ y (Manhattan.environmentShift (Manhattan.Operator.axisVector 1) y)) := by
    simpa only [h5] using h4
  -- the torus side
  have hrepr : ∀ k : ℤ, fourierBasis.repr (fourierMul (-1) F) k = c (k + 1) := by
    intro k
    have hk : k - (-1) = k + 1 := by ring
    rw [repr_fourierMul, hk]
  have h7 : inner ℂ (fourierMul (-1) F) F =
      ∑' k : ℤ, c k * conj (c (k + 1)) := by
    rw [← fourierBasis.repr.inner_map_map (fourierMul (-1) F) F, lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [RCLike.inner_apply, hrepr k]
  rw [h6.tsum_eq] at h7
  exact h7.symm

/-! ### (Hsym) in degree one -/

/-- `RCLike.re` and `Complex.re` agree on `ℂ`; the quadratic forms of
`Manhattan/Operator/Variational.lean` use the former and the explicit
exponential lemmas of Mathlib use the latter. -/
theorem re_eq_complexRe (u : ℂ) : re u = u.re := rfl

/-- The degree-one row symbol `λ+d(p₁)+d(p₂+·)`, written intrinsically on
the frequency torus. -/
noncomputable def rowSymbol (lambda : ℝ) (p : Fin 2 → ℝ)
    (x : AddCircle Manhattan.torusPeriod) : ℝ :=
  lambda + Manhattan.Estimates.dispersion (p 0) + 1 -
    re (Complex.exp (-Complex.I * (p 1 : ℂ)) * fourier (-1) x)

theorem rowSymbol_coe (lambda : ℝ) (p : Fin 2 → ℝ) (r : ℝ) :
    rowSymbol lambda p (r : AddCircle Manhattan.torusPeriod) =
      lambda + Manhattan.Estimates.dispersion (p 0) +
        Manhattan.Estimates.dispersion (p 1 + r) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hT : ((Manhattan.torusPeriod : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [Manhattan.torusPeriod]
    push_cast
    ring
  have hexp : (fourier (-1) (r : AddCircle Manhattan.torusPeriod) : ℂ) =
      Complex.exp (-(Complex.I * (r : ℂ))) := by
    rw [fourier_coe_apply, hT]
    congr 1
    field_simp
    ring
  have harg : -Complex.I * (p 1 : ℂ) + -(Complex.I * (r : ℂ)) =
      ((-(p 1 + r) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [rowSymbol, hexp, ← Complex.exp_add, harg, re_eq_complexRe,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp only [Manhattan.Estimates.dispersion]
  ring

/-- **(Hsym) in degree one for the actual fiber.**  The `H₁` energy of the
row-sector Walsh vector synthesized from a torus frequency function `F` is
the integral of `|F|²` against the total-frequency weight
`λ+d(p₁)+d(p₂+s)`. -/
theorem hEnergy_degreeOneRow (lambda : ℝ) (p : Fin 2 → ℝ) (F : Lp ℂ 2 haarTorus) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal F) =
      ∫ x, rowSymbol lambda p x * ‖F x‖ ^ 2 ∂haarTorus := by
  classical
  set y : Manhattan.WalshL2 :=
    Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal F with hydef
  set E1 : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
    Manhattan.environmentShift (Manhattan.Operator.axisVector 1) with hE1
  set E1' : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
    Manhattan.environmentShift (-Manhattan.Operator.axisVector 1) with hE1'
  set D : Lp ℂ 2 haarTorus := fourierMul (-1) F with hD
  set J : ℂ := ∫ x, fourier (-1) x * ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ)
      ∂haarTorus with hJ
  set z : ℂ := Complex.exp (-Complex.I * (p 1 : ℂ)) with hz
  -- the row sector is fixed by translations parallel to the rows
  have hzero : (Manhattan.Operator.axisVector 0) 1 = 0 := by
    simp [Manhattan.Operator.axisVector]
  have hzero' : (-Manhattan.Operator.axisVector 0) 1 = 0 := by
    simp [hzero]
  have hfix : Manhattan.environmentShift (Manhattan.Operator.axisVector 0) y = y :=
    environmentShift_row_fixed hzero _
  have hfix' : Manhattan.environmentShift (-Manhattan.Operator.axisVector 0) y = y :=
    environmentShift_row_fixed hzero' _
  -- the symmetric part on the row sector
  have hSy : Manhattan.concreteFiberS p y =
      (2 : ℂ)⁻¹ •
        ((Complex.exp (Complex.I * (p 0 : ℂ)) • y +
            Complex.exp (-Complex.I * (p 0 : ℂ)) • y - (2 : ℂ) • y) +
          (Complex.exp (Complex.I * (p 1 : ℂ)) • E1 y +
            Complex.exp (-Complex.I * (p 1 : ℂ)) • E1' y - (2 : ℂ) • y)) := by
    rw [Manhattan.concreteFiberS_formula]
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, Fin.sum_univ_two]
    rw [hfix, hfix']
  have hnorm : ‖y‖ = ‖F‖ := Manhattan.norm_degreeOneFrequencySynthesis _ _
  have hA : (inner ℂ y y : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_cast
  set w : ℂ := inner ℂ y (E1 y) with hw
  have hEadj : E1' = ContinuousLinearMap.adjoint E1 := by
    rw [hE1, hE1', Manhattan.environmentShift_adjoint]
  have hwleft : (inner ℂ (E1 y) y : ℂ) = conj w := by
    rw [hw, ← inner_conj_symm]
  have hwleft' : (inner ℂ (E1' y) y : ℂ) = w := by
    rw [hEadj, ContinuousLinearMap.adjoint_inner_left, hw]
  have hconj0 : conj (Complex.exp (Complex.I * (p 0 : ℂ))) =
      Complex.exp (-Complex.I * (p 0 : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hconj0' : conj (Complex.exp (-Complex.I * (p 0 : ℂ))) =
      Complex.exp (Complex.I * (p 0 : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hconj1 : conj (Complex.exp (Complex.I * (p 1 : ℂ))) =
      Complex.exp (-Complex.I * (p 1 : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hconj1' : conj (Complex.exp (-Complex.I * (p 1 : ℂ))) =
      Complex.exp (Complex.I * (p 1 : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hcos : Complex.exp (-Complex.I * (p 0 : ℂ)) +
      Complex.exp (Complex.I * (p 0 : ℂ)) = ((2 * Real.cos (p 0) : ℝ) : ℂ) := by
    have h := Complex.two_cos ((p 0 : ℝ) : ℂ)
    have e1 : ((p 0 : ℝ) : ℂ) * Complex.I = Complex.I * ((p 0 : ℝ) : ℂ) := by ring
    have e2 : -((p 0 : ℝ) : ℂ) * Complex.I = -Complex.I * ((p 0 : ℝ) : ℂ) := by ring
    rw [e1, e2] at h
    rw [add_comm]
    push_cast
    exact h.symm
  have hinner : (inner ℂ (Manhattan.concreteFiberS p y) y : ℂ) =
      (2 : ℂ)⁻¹ *
        ((Complex.exp (-Complex.I * (p 0 : ℂ)) + Complex.exp (Complex.I * (p 0 : ℂ))
              - 2 - 2) * ((‖F‖ ^ 2 : ℝ) : ℂ) +
          (Complex.exp (-Complex.I * (p 1 : ℂ)) * conj w +
            Complex.exp (Complex.I * (p 1 : ℂ)) * w)) := by
    rw [hSy]
    simp only [inner_add_left, inner_sub_left, inner_smul_left, hwleft, hwleft', hA,
      hconj0, hconj0', hconj1, hconj1', map_ofNat, map_inv₀]
    ring
  have hre : re (inner ℂ (Manhattan.concreteFiberS p y) y) =
      (Real.cos (p 0) - 2) * ‖F‖ ^ 2 +
        re (Complex.exp (Complex.I * (p 1 : ℂ)) * w) := by
    have hconjterm : Complex.exp (-Complex.I * (p 1 : ℂ)) * conj w
        = conj (Complex.exp (Complex.I * (p 1 : ℂ)) * w) := by
      rw [map_mul, hconj1]
    have hsum : conj (Complex.exp (Complex.I * (p 1 : ℂ)) * w) +
        Complex.exp (Complex.I * (p 1 : ℂ)) * w =
        2 * ((re (Complex.exp (Complex.I * (p 1 : ℂ)) * w) : ℝ) : ℂ) := by
      rw [add_comm]
      exact RCLike.add_conj _
    rw [hinner, hconjterm, hcos, hsum]
    have hcollapse : (2 : ℂ)⁻¹ *
        ((((2 * Real.cos (p 0) : ℝ) : ℂ) - 2 - 2) * ((‖F‖ ^ 2 : ℝ) : ℂ) +
          2 * ((re (Complex.exp (Complex.I * (p 1 : ℂ)) * w) : ℝ) : ℂ)) =
        (((Real.cos (p 0) - 2) * ‖F‖ ^ 2 +
          re (Complex.exp (Complex.I * (p 1 : ℂ)) * w) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcollapse]
    exact Complex.ofReal_re _
  -- identification of the shift form with the torus integral
  have hwval : w = conj J := by
    rw [hw]
    rw [show (inner ℂ y (E1 y) : ℂ) = inner ℂ (fourierMul (-1) F) F from
      inner_row_environmentShift F]
    rw [← inner_conj_symm, inner_fourierMul_self]
  have hcombine : re (Complex.exp (Complex.I * (p 1 : ℂ)) * w) = re (z * J) := by
    rw [hwval, hz]
    have hswap : Complex.exp (Complex.I * (p 1 : ℂ)) * conj J =
        conj (Complex.exp (-Complex.I * (p 1 : ℂ)) * J) := by
      rw [map_mul, hconj1']
    rw [hswap, RCLike.conj_re]
  -- the energy in terms of the torus data
  have hEn : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda y =
      lambda * ‖F‖ ^ 2 - ((Real.cos (p 0) - 2) * ‖F‖ ^ 2 + re (z * J)) := by
    rw [Manhattan.Operator.DissipativeSkewPair.hEnergy,
      Manhattan.Operator.DissipativeSkewPair.re_inner_H_apply, hnorm]
    rw [show ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).S y) =
      Manhattan.concreteFiberS p y from rfl, hre, hcombine]
  -- the right-hand side
  have hgint : Integrable
      (fun x => ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2) haarTorus :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have hnorm2 : ∫ x, ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 ∂haarTorus
      = ‖F‖ ^ 2 := by
    have h1 : (inner ℂ F F : ℂ) =
        ∫ x, ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ) ∂haarTorus := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [RCLike.inner_apply, RCLike.mul_conj]
      norm_cast
    have h2 : (inner ℂ F F : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h2, integral_complex_ofReal] at h1
    exact_mod_cast h1.symm
  have hJint : Integrable (fun x => fourier (-1) x *
      ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ)) haarTorus := by
    have hgintC : Integrable (fun x : AddCircle Manhattan.torusPeriod =>
        ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ)) haarTorus :=
      hgint.ofReal
    refine hgintC.mono ?_ ?_
    · exact ((map_continuous (fourier (-1))).aestronglyMeasurable).mul
        (Complex.measurable_ofReal.comp_aemeasurable
          ((Lp.aestronglyMeasurable F).norm.aemeasurable.pow_const 2)).aestronglyMeasurable
    · filter_upwards with x
      have hone : ‖fourier (-1) x‖ = 1 := Circle.norm_coe _
      rw [norm_mul, hone, one_mul]
  have hzJint : Integrable (fun x => z * (fourier (-1) x *
      ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ))) haarTorus :=
    hJint.const_mul z
  have hpt : ∀ x : AddCircle Manhattan.torusPeriod,
      rowSymbol lambda p x * ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 =
        (lambda + Manhattan.Estimates.dispersion (p 0) + 1) *
            ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 -
          re (z * (fourier (-1) x *
            ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ))) := by
    intro x
    have hsplit : re (z * (fourier (-1) x *
        ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ))) =
        re (z * fourier (-1) x) *
          ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 := by
      rw [re_eq_complexRe, re_eq_complexRe, ← mul_assoc,
        mul_comm (z * fourier (-1) x), Complex.re_ofReal_mul, mul_comm]
    rw [rowSymbol, ← hz, hsplit]
    ring
  have hRHS : ∫ x, rowSymbol lambda p x *
        ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 ∂haarTorus =
      (lambda + Manhattan.Estimates.dispersion (p 0) + 1) * ‖F‖ ^ 2 - re (z * J) := by
    rw [show (fun x : AddCircle Manhattan.torusPeriod =>
        rowSymbol lambda p x * ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2) =
      (fun x : AddCircle Manhattan.torusPeriod =>
        (lambda + Manhattan.Estimates.dispersion (p 0) + 1) *
            ‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 -
          re (z * (fourier (-1) x *
            ((‖(F : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 : ℝ) : ℂ))))
      from funext hpt]
    rw [integral_sub (hgint.const_mul _) hzJint.re, integral_const_mul, hnorm2,
      integral_re hzJint, integral_const_mul, ← hJ]
  rw [hEn, hRHS]
  simp only [Manhattan.Estimates.dispersion]
  ring

/-- The same identity for the real-frequency competitor of Section 4:
the `H₁` energy is the paper's normalized torus integral of `|f|²` against
`λ+d(p₁)+d(p₂+r)`. -/
theorem hEnergy_degreeOneRealRow (lambda : ℝ) (p : Fin 2 → ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.degreeOneRealFrequencySynthesis Manhattan.Axis.horizontal f hf) =
      Manhattan.Estimates.torusIntegral (fun r : ℝ =>
        (lambda + Manhattan.Estimates.dispersion (p 0) +
          Manhattan.Estimates.dispersion (p 1 + r)) * ‖f r‖ ^ 2) := by
  rw [Manhattan.degreeOneRealFrequencySynthesis, hEnergy_degreeOneRow]
  have hae : (fun x : AddCircle Manhattan.torusPeriod =>
        rowSymbol lambda p x *
          ‖(Manhattan.realTorusL2 f hf : AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2)
      =ᵐ[haarTorus] fun x : AddCircle Manhattan.torusPeriod =>
        rowSymbol lambda p x *
          ‖AddCircle.liftIoc Manhattan.torusPeriod (-Real.pi) f x‖ ^ 2 := by
    filter_upwards [Manhattan.coeFn_realTorusL2 f hf] with x hx
    rw [hx]
  rw [integral_congr_ae hae, integral_haarTorus_eq_torusIntegral]
  simp only [Manhattan.Estimates.torusIntegral, Manhattan.Estimates.torus]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hend : -Real.pi + Manhattan.torusPeriod = Real.pi := by
    rw [Manhattan.torusPeriod]; ring
  have hmem : r ∈ Ioc (-Real.pi) (-Real.pi + Manhattan.torusPeriod) := by
    rw [hend]; exact hr
  rw [AddCircle.liftIoc_coe_apply hmem, rowSymbol_coe]

/-! ### The `(shift)` translate of the row competitor -/

/-- The character `fourier (-1)` at a real frequency. -/
theorem fourier_neg_one_coe (r : ℝ) :
    (fourier (-1) ((r : ℝ) : AddCircle Manhattan.torusPeriod) : ℂ) =
      Complex.exp (-(Complex.I * (r : ℂ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hT : ((Manhattan.torusPeriod : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [Manhattan.torusPeriod]
    push_cast
    ring
  rw [fourier_coe_apply, hT]
  congr 1
  field_simp
  ring

/-- **The (shift) phase makes the degree-one weight exact.**  The row symbol at
the true momentum `p`, read at the line frequency `s`, is the symbol at the
momentum `(p₁,0)` read at the shifted frequency `r=p₂+s`. -/
theorem rowSymbol_add_shift (lambda : ℝ) (p : Fin 2 → ℝ)
    (x : AddCircle Manhattan.torusPeriod) :
    rowSymbol lambda ![p 0, 0]
        (x + ((p 1 : ℝ) : AddCircle Manhattan.torusPeriod)) =
      rowSymbol lambda p x := by
  rw [rowSymbol, rowSymbol, fourier_add_arg, fourier_neg_one_coe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul]
  congr 2
  ring_nf

/-- **Summand 1 of (22) is exact.**  With the (shift) phase in place the
concrete degree-one `H₁` energy of the competitor is the paper's
`degreeOneEnergy`, not merely comparable to it. -/
theorem hEnergy_degreeOneRowShift (lambda : ℝ) (p : Fin 2 → ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
          (rowTorusShift (p 1) (Manhattan.realTorusL2 f hf))) =
      Manhattan.Estimates.torusIntegral (fun r : ℝ =>
        (lambda + Manhattan.Estimates.dispersion (p 0) +
          Manhattan.Estimates.dispersion r) * ‖f r‖ ^ 2) := by
  have hshift := integral_add_right_eq_self
    (μ := (AddCircle.haarAddCircle : Measure (AddCircle Manhattan.torusPeriod)))
    (fun y : AddCircle Manhattan.torusPeriod =>
      rowSymbol lambda ![p 0, 0] y *
        ‖(Manhattan.realTorusL2 f hf : AddCircle Manhattan.torusPeriod → ℂ) y‖ ^ 2)
    ((p 1 : ℝ) : AddCircle Manhattan.torusPeriod)
  rw [hEnergy_degreeOneRow]
  have hstep : ∫ x, rowSymbol lambda p x *
        ‖(rowTorusShift (p 1) (Manhattan.realTorusL2 f hf) :
          AddCircle Manhattan.torusPeriod → ℂ) x‖ ^ 2 ∂haarTorus =
      ∫ y, rowSymbol lambda ![p 0, 0] y *
        ‖(Manhattan.realTorusL2 f hf :
          AddCircle Manhattan.torusPeriod → ℂ) y‖ ^ 2 ∂haarTorus := by
    rw [← hshift]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rowTorusShift (p 1) (Manhattan.realTorusL2 f hf)]
      with x hx
    rw [hx, rowSymbol_add_shift]
  rw [hstep, ← hEnergy_degreeOneRow lambda ![p 0, 0]
    (Manhattan.realTorusL2 f hf),
    show Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
        (Manhattan.realTorusL2 f hf) =
      Manhattan.degreeOneRealFrequencySynthesis Manhattan.Axis.horizontal f hf
      from rfl,
    hEnergy_degreeOneRealRow]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]

/-! ### The bound from Lemma 4.1 v3 -/

/-- The shifted and unshifted degree-one weights are comparable.
-/
theorem rowWeight_le {lambda : ℝ} (hlambda : 0 ≤ lambda) {p : Fin 2 → ℝ}
    (hp₀ : p 0 ∈ Manhattan.Estimates.torus) (horder : |p 1| ≤ |p 0|) (r : ℝ) :
    lambda + Manhattan.Estimates.dispersion (p 0) +
        Manhattan.Estimates.dispersion (p 1 + r) ≤
      3 * (lambda + Manhattan.Estimates.dispersion (p 0) +
        Manhattan.Estimates.dispersion r) := by
  have hpi : |p 0| ≤ Real.pi := by
    rcases hp₀ with ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨h1.le, h2⟩
  have h1 : Manhattan.Estimates.dispersion (p 1) ≤
      Manhattan.Estimates.dispersion (p 0) := dispersion_le_of_abs_le hpi horder
  have h2 := dispersion_add_le (p 1) r
  have h3 := Manhattan.Estimates.dispersion_nonneg r
  have h4 := Manhattan.Estimates.dispersion_nonneg (p 0)
  linarith

end Manhattan.Glue

