import Manhattan.V4.PeriodicProfile

/-!
# Version 4, Move 1: the pieces of the competitor cost

Everything Move 1 needs about the Version 4 competitor, other than the four
sector identifications themselves.

* `type112DStarTwoRow_rawShiftTwist` is **(P3) at the Walsh level**: 's
  `rawD2StarTwoRow_offDiagonalPart` is a statement about the *raw* lowering
  symbol, and `Manhattan.Glue.walshSectorComponent_two_concreteFiberA_eq` needs
  the *Walsh* statement `type112DStarTwoRow p k_p = 0`.  The bridge is
  `Manhattan.Glue.type112DStarTwoRow_eq`, which reads the competitor at column
  index zero, together with the oddness of the parity kernel in the column
  frequency.
* `scaleProfile` is the `√2` rescaling of the scalar minimizer that 's
  kernel normalization forces.
* `degreeOne_cost_le` and `twoRow_cost_le` are the two halves of estimate (4)
  against the effective weight `q(r) = |r|/√(log(1/|r|))`.
* `v4_residual_le` and `v4_sigmaEnergy_le` are the scalar bounds at the
  minimizer `u = w/(B+σ)`; no completion of the square is needed, because the
  weights `18` and `4` produced by the sector splitting are absorbed directly
  into the constant `40` of `mixedResidual_integral_le` and
  `paritySigmaEnergy_scaled_le`.
* `norm_v4MixedSymbol_sq` evaluates the mixed symbol at the purely imaginary
  degree-one profile `g = -iφ`, where it is the real function
  `w - (√2)⁻¹ σ v`, `w(r) = sin(r) φ(r)`.
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue

/-- A raw kernel that is odd in the column frequency has vanishing Fourier
coefficients at column index zero. -/
theorem rawFourierCoefficient_col_zero {k : ℝ → ℝ → ℝ → ℂ}
    (hodd : ∀ r r' b, k r r' (-b) = -k r r' b) {n : Fin 3 → ℤ} (hn : n 2 = 0) :
    rawFourierCoefficient k n = 0 := by
  have hinner : ∀ r r' : ℝ,
      (Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 0) r * intCharacter (-n 1) r' *
          intCharacter (-n 2) beta * k r r' beta) = 0 := by
    intro r r'
    refine torusIntegral_of_odd (fun beta => ?_)
    rw [hn]
    simp only [neg_zero, intCharacter_index_zero, mul_one, hodd r r' beta]
    ring
  rw [rawFourierCoefficient]
  simp only [hinner]
  simp

/-- A triple whose two row indices coincide is not a type-`112` index. -/
theorem not_isType112_tripleToFinset_rowDiag (m j : ℤ) :
    ¬ IsType112Index (tripleToFinset (m, m, j)) := by
  intro h
  have hs : tripleToFinset (m, m, j)
      = ({(Axis.horizontal, m), (Axis.vertical, j)} : Finset LineIndex) := by
    rw [tripleToFinset, Finset.insert_idem]
  have hcard : (tripleToFinset (m, m, j)).card ≤ 2 := by
    rw [hs]
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  rw [h.1] at hcard
  omega

/-- The canonical ordered coordinates of a triple with column index pinned to
the origin. -/
theorem type112RawIndex_tripleToFinset_col {m m' j : ℤ} (hm : m ≠ m')
    (h : IsType112Index (tripleToFinset (m, m', j))) :
    Manhattan.type112RawIndex ⟨tripleToFinset (m, m', j), h⟩ =
      ![min m m', max m m', j] := by
  have hlt : min m m' < max m m' := min_lt_max.mpr hm
  set n : Manhattan.OrderedType112Index :=
    ⟨![min m m', max m m', j], by simpa using hlt⟩ with hn
  have hset : Manhattan.orderedType112Lines n = tripleToFinset (m, m', j) := by
    rw [hn, Manhattan.orderedType112Lines]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rcases lt_or_gt_of_ne hm with hlt' | hgt'
    · rw [min_eq_left hlt'.le, max_eq_right hlt'.le]
      rfl
    · rw [min_eq_right hgt'.le, max_eq_left hgt'.le]
      ext l
      simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton]
      tauto
  have hequiv : Manhattan.orderedType112Equiv n = ⟨tripleToFinset (m, m', j), h⟩ :=
    Subtype.ext hset
  rw [Manhattan.type112RawIndex, ← hequiv, Equiv.symm_apply_apply, hn]

/-- **(P3) at the Walsh level.**  The two-row component of `D₂*` at the Version 4
competitor vanishes identically, because the parity kernel is odd in the column
frequency and `(D2a)` reads its input at column index zero. -/
theorem type112CoefficientAt_rawShiftTwist_col_zero {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (hodd : ∀ r r' b, k r r' (-b) = -k r r' b)
    (p₁ p₂ : ℝ) (m m' : ℤ) :
    type112CoefficientAt
        (Manhattan.type112ShiftTwist p₁ p₂ (rawType112Coefficients hk))
        (tripleToFinset (m, m', 0)) = 0 := by
  rw [type112CoefficientAt]
  by_cases h112 : IsType112Index (tripleToFinset (m, m', 0))
  · have hmm : m ≠ m' := by
      intro hEq
      subst hEq
      exact not_isType112_tripleToFinset_rowDiag m 0 h112
    rw [dif_pos h112, Manhattan.type112ShiftTwist_apply, rawType112Coefficients_apply,
      mFourierCoeff_rawL2 hk, type112RawIndex_tripleToFinset_col hmm h112]
    rw [rawFourierCoefficient_col_zero hodd (n := ![min m m', max m m', 0]) rfl, mul_zero]
  · rw [dif_neg h112]

/-- **(P3) at the Walsh level.**  The two-row lowering component of the Version 4
degree-three competitor vanishes identically. -/
theorem type112DStarTwoRow_rawShiftTwist {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (hodd : ∀ r r' b, k r r' (-b) = -k r r' b)
    (p : Fin 2 → ℝ) :
    Manhattan.type112DStarTwoRow p
        (Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hk)) = 0 := by
  apply lp.ext
  funext T
  have h := type112DStarTwoRow_eq p
    (Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hk)) T
  rw [type112CoefficientAt_rawShiftTwist_col_zero hk hodd (p 0) (p 1)
      (type11RawIndex T 0 + 1) (type11RawIndex T 1 + 1),
    type112CoefficientAt_rawShiftTwist_col_zero hk hodd (p 0) (p 1)
      (type11RawIndex T 0 - 1) (type11RawIndex T 1 - 1)] at h
  simp only [mul_zero, sub_zero] at h
  simpa using h

/-! ## A scaled parity profile -/

/-- A constant multiple of a parity profile is a parity profile.  The Version 4
competitor is `√2` times the scalar minimizer `v = w/(B+σ)`, because
put the `(√2)⁻¹` into the kernel. -/
def scaleProfile (c : ℝ) (v : ParityProfile) : ParityProfile where
  toFun := fun r beta => c * v.toFun r beta
  meas := measurable_const.mul v.meas
  bound := |c| * v.bound
  abs_le := by
    intro r beta
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (v.abs_le r beta) (abs_nonneg c)
  odd_row := by
    intro r beta
    show c * v.toFun (-r) beta = -(c * v.toFun r beta)
    rw [v.odd_row]
    ring
  even_col := by
    intro r beta
    show c * v.toFun r (-beta) = c * v.toFun r beta
    rw [v.even_col]
  periodic_row := by
    intro beta r
    have h := v.periodic_row beta r
    simp only at h
    show c * v.toFun (r + 2 * Real.pi) beta = c * v.toFun r beta
    rw [h]

@[simp] theorem scaleProfile_toFun (c : ℝ) (v : ParityProfile) (r beta : ℝ) :
    (scaleProfile c v).toFun r beta = c * v.toFun r beta := rfl

/-! ## The two halves of the Move 1 cost -/

open Manhattan.V4.Frequency in
/-- The degree-one energy density of estimate (4) against the effective
weight. -/
theorem degreeOne_cost_le {mu delta r0 : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hmud : mu ≤ delta ^ 2) (hr0 : r0 ≤ 1 / 4)
    {phi : ℝ → ℝ}
    (hsupp : ∀ r ∈ Estimates.torus, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus)) :
    Estimates.torusIntegral (fun r => (mu + Estimates.dispersion r) * phi r ^ 2)
      ≤ 6 * Estimates.torusIntegral
          (fun r => Energy.effectiveWeight r * phi r ^ 2) := by
  rw [← Estimates.torusIntegral_smul_left]
  refine Estimates.torusIntegral_mono_on ?_ (hint.const_mul 6) ?_
  · intro x _
    have := Estimates.dispersion_nonneg x
    have : (0:ℝ) ≤ mu + Estimates.dispersion x := by linarith
    exact mul_nonneg this (sq_nonneg _)
  · intro x hx
    by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
    · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
      have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
      have h1 : mu + Estimates.dispersion x ≤ 6 * (delta + x ^ 2) :=
        degreeOne_symbol_le hmu hdelta hdelta1 hmud
      have h2 : delta + x ^ 2 ≤ Energy.effectiveWeight x :=
        Energy.add_sq_le_effectiveWeight hdelta.le hmem.1 hxpos hx14
      have h3 : mu + Estimates.dispersion x ≤ 6 * Energy.effectiveWeight x := by
        linarith
      have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (phi x))
      calc (mu + Estimates.dispersion x) * phi x ^ 2
          ≤ 6 * Energy.effectiveWeight x * phi x ^ 2 := this
        _ = 6 * (Energy.effectiveWeight x * phi x ^ 2) := by ring
    · rw [hsupp x hx hmem]
      simp

open Manhattan.V4.Frequency in
/-- The two-row density `2 s² J(μ)` of estimate (4) against the effective
weight. -/
theorem twoRow_cost_le {mu delta r0 s : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hmud : mu ≤ delta ^ 2) (hs : s ^ 2 ≤ 2 * mu)
    (hr0 : r0 ≤ 1 / 4) {phi : ℝ → ℝ}
    (hsupp : ∀ r ∈ Estimates.torus, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus)) :
    Estimates.torusIntegral
        (fun r => 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) * phi r ^ 2)
      ≤ 6 * Estimates.torusIntegral
          (fun r => Energy.effectiveWeight r * phi r ^ 2) := by
  have hJnn : (0:ℝ) ≤ 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) := by positivity
  rw [← Estimates.torusIntegral_smul_left]
  refine Estimates.torusIntegral_mono_on ?_ (hint.const_mul 6) ?_
  · intro x _
    exact mul_nonneg hJnn (sq_nonneg _)
  · intro x hx
    by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
    · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
      have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
      have h1 := Energy.degreeOne_multiplier_le (mu := mu) (delta := delta) (s := s)
        (r := x) hmu hdelta hdelta1 hmud hs
      have hd := Estimates.dispersion_nonneg x
      have h2 : 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) ≤ 6 * (delta + x ^ 2) := by
        linarith
      have h3 : delta + x ^ 2 ≤ Energy.effectiveWeight x :=
        Energy.add_sq_le_effectiveWeight hdelta.le hmem.1 hxpos hx14
      have h4 : 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) ≤ 6 * Energy.effectiveWeight x := by
        linarith
      have := mul_le_mul_of_nonneg_right h4 (sq_nonneg (phi x))
      calc 2 * s ^ 2 / Real.sqrt (mu * (mu + 2)) * phi x ^ 2
          ≤ 6 * Energy.effectiveWeight x * phi x ^ 2 := this
        _ = 6 * (Energy.effectiveWeight x * phi x ^ 2) := by ring
    · rw [hsupp x hx hmem]
      simp

/-! ## The scalar bounds at the Version 4 competitor `v = √2 w/(B+σ)` -/

/-- The degree-three density at the Version 4 competitor is twice the density at
the unscaled minimizer: the `√2` normalization squares. -/
theorem paritySigma_scaled_sq (sigma x : ℝ) :
    sigma * (Real.sqrt 2 * x) ^ 2 = 2 * (sigma * x ^ 2) := by
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- The `(√2)⁻¹` of the mixed symbol cancels the `√2` of the competitor. -/
theorem inv_sqrt_two_mul_scaled (sigma x : ℝ) :
    (Real.sqrt 2)⁻¹ * (sigma * (Real.sqrt 2 * x)) = sigma * x := by
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

/-- **The degree-two residual density at the scalar minimizer.**  With
`u = w/(B+σ)` the residual is `w²B/(B+σ)²`, which is at most the Move 1 density
`w²/(B+σ)`.  No completion of the square is needed: the weight `4` of the sector
splitting is absorbed directly. -/
theorem v4_residual_le {B sigma w : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    (w - sigma * (w / (B + sigma))) ^ 2 / B ≤ w ^ 2 / (B + sigma) := by
  have hD : 0 < B + sigma := by linarith
  have e3 : w - sigma * (w / (B + sigma)) = w * B / (B + sigma) := by
    field_simp
    ring
  rw [e3, div_pow, div_div, div_le_div_iff₀ (by positivity) hD]
  have hw := sq_nonneg w
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hw hB.le) hD.le) hsigma]

/-- The degree-three density at the scalar minimizer is at most the Move 1
density. -/
theorem v4_sigmaEnergy_le {B sigma w : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma) :
    sigma * (w / (B + sigma)) ^ 2 ≤ w ^ 2 / (B + sigma) := by
  have hD : 0 < B + sigma := by linarith
  have hrw : sigma * (w / (B + sigma)) ^ 2 = sigma * w ^ 2 / (B + sigma) ^ 2 := by
    rw [div_pow]
    ring
  rw [hrw, div_le_div_iff₀ (by positivity) hD]
  have hw := sq_nonneg w
  nlinarith [mul_nonneg (mul_nonneg hw hD.le) hB.le]

variable {kappa delta : ℝ}

/-- **The degree-two residual density, integrated.**  At the Version 4
competitor the residual `(w - σv/√2)²/B` integrates to at most the Move 1
density `∫ w² J₃`. -/
theorem mixedResidual_integral_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) {Kw : ℝ} {w : ℝ → ℝ}
    (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    Estimates.torusIntegral (fun r => Estimates.torusIntegral (fun beta =>
        (w r - paritySigma kappa delta r beta
            * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
          / Estimates.correctionB q r beta))
      ≤ Estimates.torusIntegral (fun r => w r ^ 2 * parityFibreJ q kappa delta r) := by
  have hKw : 0 ≤ Kw := le_trans (abs_nonneg _) (hbw 0)
  have hBpos : ∀ r beta : ℝ, 0 < Estimates.correctionB q r beta :=
    fun r beta => lt_of_lt_of_le hlam (correctionB_ge q r beta)
  have hsig : ∀ r beta : ℝ, 0 ≤ paritySigma kappa delta r beta :=
    fun r beta => paritySigma_nonneg hkappa hdelta r beta
  have hpt : ∀ r beta : ℝ,
      (w r - paritySigma kappa delta r beta
          * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
        / Estimates.correctionB q r beta
      ≤ w r ^ 2 / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
    intro r beta
    have hV : parityV q kappa delta (fun r' _ => w r') r beta
        = w r / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := rfl
    rw [hV]
    exact v4_residual_le (hBpos r beta) (hsig r beta)
  have hbound : ∀ r beta : ℝ, |w r ^ 2 / (Estimates.correctionB q r beta
      + paritySigma kappa delta r beta)| ≤ Kw ^ 2 / q.lambda := by
    intro r beta
    have hden : q.lambda ≤ Estimates.correctionB q r beta + paritySigma kappa delta r beta :=
      lambda_le_correctionB_add_paritySigma hkappa hdelta r beta
    have hdenpos : 0 < Estimates.correctionB q r beta + paritySigma kappa delta r beta := by
      linarith
    have hnum : w r ^ 2 ≤ Kw ^ 2 := by nlinarith [hbw r, abs_nonneg (w r), sq_abs (w r)]
    rw [abs_of_nonneg (by positivity)]
    calc w r ^ 2 / (Estimates.correctionB q r beta + paritySigma kappa delta r beta)
        ≤ Kw ^ 2 / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
          gcongr
      _ ≤ Kw ^ 2 / q.lambda := by gcongr
  have hinner : ∀ r : ℝ,
      Estimates.torusIntegral (fun beta =>
          (w r - paritySigma kappa delta r beta
              * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
            / Estimates.correctionB q r beta)
        ≤ w r ^ 2 * parityFibreJ q kappa delta r := by
    intro r
    have hstep : Estimates.torusIntegral (fun beta =>
        (w r - paritySigma kappa delta r beta
            * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
          / Estimates.correctionB q r beta)
        ≤ Estimates.torusIntegral (fun beta => w r ^ 2
            / (Estimates.correctionB q r beta + paritySigma kappa delta r beta)) := by
      refine Estimates.torusIntegral_mono' (fun beta => ?_) ?_ (fun beta => hpt r beta)
      · have := hBpos r beta
        positivity
      refine Estimates.integrableOn_torus_of_bounded (C := Kw ^ 2 / q.lambda) ?_
        (fun beta => hbound r beta)
      have hmz := measurable_rowQuotient (kappa := kappa) (delta := delta) (q := q) hmw
      exact hmz.comp (measurable_id.prodMk measurable_const)
    refine hstep.trans (le_of_eq ?_)
    rw [parityFibreJ, ← Estimates.torusIntegral_smul_left]
    congr 1
  refine Estimates.torusIntegral_mono' ?_ ?_ hinner
  · intro r
    refine Estimates.torusIntegral_nonneg' fun beta => ?_
    have := hBpos r beta
    positivity
  · refine Estimates.integrableOn_torus_of_bounded (C := Kw ^ 2 / q.lambda) ?_ ?_
    · exact (hmw.pow_const 2).mul parityFibreJ_measurable
    · intro r
      have hJ := parityFibreJ_le hlam hkappa hdelta r
      have hJ0 := parityFibreJ_nonneg hlam hkappa hdelta r
      have hnum : w r ^ 2 ≤ Kw ^ 2 := by nlinarith [hbw r, abs_nonneg (w r), sq_abs (w r)]
      rw [abs_of_nonneg (by positivity)]
      have h0 : (0:ℝ) ≤ w r ^ 2 := sq_nonneg _
      calc w r ^ 2 * parityFibreJ q kappa delta r ≤ Kw ^ 2 * q.lambda⁻¹ := by
            exact mul_le_mul hnum hJ hJ0 (by positivity)
        _ = Kw ^ 2 / q.lambda := by rw [div_eq_mul_inv]

/-- **The degree-three energy at the Version 4 competitor.**  The `√2` of part
V4-2's normalization doubles the density; the result is still at most twice the
Move 1 density. -/
theorem paritySigmaEnergy_scaled_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) {Kw : ℝ} {w : ℝ → ℝ}
    (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma kappa delta r beta
          * (Real.sqrt 2 * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2))
      ≤ 2 * Estimates.torusIntegral
          (fun r => w r ^ 2 * parityFibreJ q kappa delta r) := by
  have hrw : (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma kappa delta r beta
          * (Real.sqrt 2 * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2))
      = fun beta => 2 * Estimates.torusIntegral (fun r =>
          paritySigma kappa delta r beta
            * parityV q kappa delta (fun r' _ => w r') r beta ^ 2) := by
    funext beta
    rw [← Estimates.torusIntegral_smul_left]
    congr 1
    funext r
    exact paritySigma_scaled_sq _ _
  rw [hrw, Estimates.torusIntegral_smul_left]
  exact mul_le_mul_of_nonneg_left
    (paritySigmaEnergy_le_density hlam hkappa hdelta hmw hbw) (by norm_num)

/-- **The Version 4 mixed symbol is real.**  For the purely imaginary degree-one
profile `g = -iφ` the raising half `i sin(r) g(r)` is the real row symbol
`w(r) = sin(r) φ(r)`, so the whole mixed symbol is
`w - (√2)⁻¹ σ v`. -/
theorem v4MixedSymbol_neg_I (kappa delta : ℝ) (v : ParityProfile) (phi : ℝ → ℝ)
    (r beta : ℝ) :
    v4MixedSymbol kappa delta v.toFun (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) r beta
      = (((Real.sin r * phi r
          - (Real.sqrt 2)⁻¹ * (paritySigma kappa delta r beta * v.toFun r beta) : ℝ) : ℂ)) := by
  rw [v4MixedSymbol, parityMixedSymbol]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : Complex.I * ((Real.sin r : ℝ) : ℂ) * (-Complex.I * ((phi r : ℝ) : ℂ))
      = ((Real.sin r : ℝ) : ℂ) * ((phi r : ℝ) : ℂ) := by
    linear_combination (-(((Real.sin r : ℝ) : ℂ) * ((phi r : ℝ) : ℂ))) * hI
  rw [h1]
  push_cast
  ring

theorem norm_v4MixedSymbol_sq (kappa delta : ℝ) (v : ParityProfile) (phi : ℝ → ℝ)
    (r beta : ℝ) :
    ‖v4MixedSymbol kappa delta v.toFun (fun x => -Complex.I * ((phi x : ℝ) : ℂ)) r beta‖ ^ 2
      = (Real.sin r * phi r
          - (Real.sqrt 2)⁻¹ * (paritySigma kappa delta r beta * v.toFun r beta)) ^ 2 := by
  rw [v4MixedSymbol_neg_I, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Manhattan.V4
