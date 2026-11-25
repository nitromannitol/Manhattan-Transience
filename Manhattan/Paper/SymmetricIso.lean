import Manhattan.Paper.LowDegreeFormulas
import Manhattan.Glue.SummandFour

/-!
# The quadratic forms of the multipliers in symmetric coefficients

Equation `eq:iso` (`manuscript.tex:725-728`) states `⟨F, G⟩ = n! ⟨f, g⟩` for
the symmetric coefficients `f`, `g` of two degree-`n` elements, and
`eq:Hsym` (`manuscript.tex:749`) that `H_n` is multiplication by
`λ + θ(P)`.  This file proves the form of both used by the paper's
calculations: for a degree-`n` element `F` with symmetric coefficient
`f = Manhattan.Paper.symCoeff n F` and every continuous multiplier `m(P)`,

  `⟨f, m(P) f⟩ = (n!)⁻¹ ⟨c, m(P) c⟩`,

where `c` is the sorted coefficient of `F` (`inner_symCoeff_orderedMultiplier`),
and `‖F‖²_{H⁻¹} = n! ⟨f, (λ + θ(P))⁻¹ f⟩` (`hMinusEnergy_eq_symCoeff`).

The ordered tuples split into the classes `slotClass n π` of tuples whose
reordering by `π` is sorted; the symmetric coefficient is the average of the
`n!` reorderings of the sorted coefficient, which are supported on distinct
classes.  Every multiplier commutes with the reorderings and with the
projections onto the classes, because these commute with the simultaneous
translations of the line indices
(`Manhattan.Paper.comp_orderedMultiplier_of_commute`).
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

attribute [local instance] Manhattan.Glue.lineOrder

/-! ### Reorderings and classes commute with the multipliers -/

theorem slotPermute_orderedTranslate (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Operator.Lattice)
    (c : OrderedCoefficient n) :
    slotPermute n π (orderedTranslate n x c) = orderedTranslate n x (slotPermute n π c) := by
  apply lp.ext
  funext t
  rw [slotPermute_apply, orderedTranslate_apply, orderedTranslate_apply, slotPermute_apply]
  rfl

theorem slotPermute_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ) (π : Equiv.Perm (Fin n))
    (m : C(UnitAddTorus (Fin 2), ℂ)) (c : OrderedCoefficient n) :
    slotPermute n π (orderedMultiplier n p m c) = orderedMultiplier n p m (slotPermute n π c) := by
  have h := comp_orderedMultiplier_of_commute n p
    (slotPermute n π).toLinearIsometry.toContinuousLinearMap
    (fun x c => slotPermute_orderedTranslate n π x c) m
  exact congrArg (fun T => T c) h

/-- The ordered tuples whose reordering by `π` is the sorted enumeration of
their set of lines. -/
def slotClass (n : ℕ) (π : Equiv.Perm (Fin n)) : Set (Fin n → LineIndex) :=
  {t | t ∘ π ∈ degreeRange n}

theorem tupleTranslate_mem_slotClass (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Operator.Lattice)
    (t : Fin n → LineIndex) :
    tupleTranslate n x t ∈ slotClass n π ↔ t ∈ slotClass n π :=
  tupleTranslate_mem_degreeRange n x (t ∘ π)

theorem slotClassProjection_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ) (π : Equiv.Perm (Fin n))
    (m : C(UnitAddTorus (Fin 2), ℂ)) (c : OrderedCoefficient n) :
    l2SupportProjection (slotClass n π) (orderedMultiplier n p m c) =
      orderedMultiplier n p m (l2SupportProjection (slotClass n π) c) := by
  have h := comp_orderedMultiplier_of_commute n p (l2SupportProjection (slotClass n π))
    (fun x c => l2SupportProjection_l2CongrLeft (slotClass n π) (tupleTranslate n x)
      (tupleTranslate_mem_slotClass n π x) c) m
  exact congrArg (fun T => T c) h

theorem not_mem_slotClass_of_mem {n : ℕ} {π π' : Equiv.Perm (Fin n)} (hπ : π ≠ π')
    {t : Fin n → LineIndex} (ht : t ∈ slotClass n π) : t ∉ slotClass n π' := by
  intro ht'
  obtain ⟨S, hS⟩ := ht
  obtain ⟨S', hS'⟩ := ht'
  have hinj : Function.Injective t := by
    have h1 : Function.Injective (t ∘ π) := by
      rw [← hS]
      exact injective_degreeEnum_apply S
    intro a b hab
    have := @h1 (π.symm a) (π.symm b) (by simpa using hab)
    simpa using this
  have hset : S = S' := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← range_degreeEnum, ← range_degreeEnum, hS, hS', Set.range_comp, Set.range_comp,
      Equiv.range_eq_univ, Equiv.range_eq_univ]
  apply hπ
  have h1 : t ∘ π = t ∘ π' := by rw [← hS, ← hS', hset]
  exact Equiv.ext fun a => hinj (congrFun h1 a)

theorem slotPermute_walshOrdered_supported (n : ℕ) (π : Equiv.Perm (Fin n))
    (c : DegreeCoefficient n) :
    l2SupportProjection (slotClass n π) (slotPermute n π (walshOrdered n c)) =
      slotPermute n π (walshOrdered n c) := by
  apply lp.ext
  funext t
  rw [l2SupportProjection_apply]
  by_cases ht : t ∈ slotClass n π
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, slotPermute_apply,
      walshOrdered_apply_of_notMem_degreeRange n c ht]

theorem slotClassProjection_slotPermute_walshOrdered {n : ℕ} {π π' : Equiv.Perm (Fin n)}
    (hπ : π ≠ π') (c : DegreeCoefficient n) :
    l2SupportProjection (slotClass n π') (slotPermute n π (walshOrdered n c)) = 0 := by
  apply lp.ext
  funext t
  rw [l2SupportProjection_apply]
  by_cases ht : t ∈ slotClass n π'
  · rw [Set.indicator_of_mem ht, slotPermute_apply,
      walshOrdered_apply_of_notMem_degreeRange n c (not_mem_slotClass_of_mem (Ne.symm hπ) ht)]
    rfl
  · rw [Set.indicator_of_notMem ht]
    rfl

/-! ### `eq:iso` with a multiplier -/

theorem walshSectorAnalysis_homogeneousWalshSynthesis (n : ℕ) (c : DegreeCoefficient n) :
    walshSectorAnalysis (fun S => S.card = n) (homogeneousWalshSynthesis n c) = c := by
  apply lp.ext
  funext S
  rw [walshSectorAnalysis_apply]
  exact inner_walshL2_homogeneousWalshSynthesis n c S

theorem symCoeff_homogeneousWalshSynthesis (n : ℕ) (c : DegreeCoefficient n) :
    symCoeff n (homogeneousWalshSynthesis n c) =
      ((n.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin n), slotPermute n π (walshOrdered n c) := by
  rw [symCoeff, walshSectorAnalysis_homogeneousWalshSynthesis]

/-- **`eq:iso` with a multiplier.**  For a degree-`n` element with sorted
coefficient `c`, the quadratic form of a continuous multiplier `m(P)` at the
symmetric coefficient is `(n!)⁻¹` times its value at the sorted coefficient. -/
theorem inner_symCoeff_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ)
    (m : C(UnitAddTorus (Fin 2), ℂ)) (c : DegreeCoefficient n) :
    inner ℂ (symCoeff n (homogeneousWalshSynthesis n c))
        (orderedMultiplier n p m (symCoeff n (homogeneousWalshSynthesis n c))) =
      (n.factorial : ℂ)⁻¹ *
        inner ℂ (walshOrdered n c) (orderedMultiplier n p m (walshOrdered n c)) := by
  classical
  set w : OrderedCoefficient n := walshOrdered n c with hw
  have hoff : ∀ π π' : Equiv.Perm (Fin n), π ≠ π' →
      inner ℂ (slotPermute n π w) (orderedMultiplier n p m (slotPermute n π' w)) = 0 := by
    intro π π' hπ
    rw [← slotPermute_walshOrdered_supported n π' c, ← slotClassProjection_orderedMultiplier,
      ← l2SupportProjection_sym, slotClassProjection_slotPermute_walshOrdered hπ c,
      inner_zero_left]
  have hdiag : ∀ π : Equiv.Perm (Fin n),
      inner ℂ (slotPermute n π w) (orderedMultiplier n p m (slotPermute n π w)) =
        inner ℂ w (orderedMultiplier n p m w) := by
    intro π
    rw [← slotPermute_orderedMultiplier, LinearIsometryEquiv.inner_map_map]
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [symCoeff_homogeneousWalshSynthesis, ← hw, map_smul, inner_smul_left, inner_smul_right,
    map_sum, sum_inner]
  simp only [inner_sum]
  rw [Finset.sum_congr rfl fun π _ => Finset.sum_eq_single π
      (fun π' _ hπ' => hoff π π' (Ne.symm hπ')) (by simp)]
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, map_inv₀, map_natCast]
  field_simp

/-! ### The `H⁻¹` multiplier -/

/-- The function `ψ ↦ cos(2π ψ)` on the unit circle. -/
def cosMap : C(UnitAddCircle, ℝ) :=
  ⟨fun ψ => (fourier 1 ψ).re, Complex.continuous_re.comp (fourier 1).continuous⟩

theorem cosMap_coe (x : ℝ) : cosMap ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) = Real.cos x := by
  show (fourier 1 ((x / (2 * Real.pi) : ℝ) : UnitAddCircle)).re = _
  rw [fourier_coe_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * ((x / (2 * Real.pi) : ℝ) : ℂ) /
      ((1 : ℝ) : ℂ) = (x : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [h, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `λ + θ(P)`, as a function on the two-torus. -/
def symbolMap (lam : ℝ) : C(UnitAddTorus (Fin 2), ℝ) :=
  ⟨fun ψ => lam + ((1 - cosMap (ψ 0)) + (1 - cosMap (ψ 1))), by
    exact continuous_const.add ((continuous_const.sub (cosMap.continuous.comp
      (continuous_apply 0))).add (continuous_const.sub (cosMap.continuous.comp
        (continuous_apply 1))))⟩

theorem symbolMap_totalFrequencyPoint (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    symbolMap lam (totalFrequencyPoint n p σ t) = symbolWeight n lam p σ t := by
  show lam + ((1 - cosMap _) + (1 - cosMap _)) = _
  simp only [totalFrequencyPoint, cosMap_coe]
  rw [symbolWeight_def, Estimates.theta, Estimates.dispersion, Estimates.dispersion]

theorem symbolMap_pos {lam : ℝ} (hlam : 0 < lam) (ψ : UnitAddTorus (Fin 2)) :
    0 < symbolMap lam ψ := by
  have h : ∀ φ : UnitAddCircle, cosMap φ ≤ 1 := by
    intro φ
    show (fourier 1 φ).re ≤ 1
    calc (fourier 1 φ).re ≤ ‖fourier 1 φ‖ := Complex.re_le_norm _
      _ = 1 := by
          have := fourier_coe_apply (T := 1) (n := 1) (x := (AddCircle.equivIco 1 0 φ : ℝ))
          rw [AddCircle.coe_equivIco] at this
          rw [this, Complex.norm_exp]
          simp
  show 0 < lam + ((1 - cosMap (ψ 0)) + (1 - cosMap (ψ 1)))
  linarith [h (ψ 0), h (ψ 1)]

/-- The multiplier `(λ + θ(P))⁻¹` of `H⁻¹`. -/
def hInvMap {lam : ℝ} (hlam : 0 < lam) : C(UnitAddTorus (Fin 2), ℂ) :=
  ⟨fun ψ => (((symbolMap lam ψ)⁻¹ : ℝ) : ℂ), Complex.continuous_ofReal.comp
    ((symbolMap lam).continuous.inv₀ fun ψ => (symbolMap_pos hlam ψ).ne')⟩

theorem hInvMap_totalFrequency {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (p : Fin 2 → ℝ)
    (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) :
    hInvMap hlam (fun i => ((totalFrequency n p σ t i / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
      (((symbolWeight n lam p σ t)⁻¹ : ℝ) : ℂ) := by
  show (((symbolMap lam (totalFrequencyPoint n p σ t))⁻¹ : ℝ) : ℂ) = _
  rw [symbolMap_totalFrequencyPoint]

/-- The quadratic form of a real multiplier on the frequency side. -/
theorem re_inner_freqMultiplier (n : ℕ) (p : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (v : LineFreqL2 n) :
    RCLike.re (inner ℂ v (freqMultiplier n p (hInvMap hlam) v)) =
      ∑ σ : Fin n → Axis, ∫ t, (symbolWeight n lam p σ t)⁻¹ *
        ‖(v σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [inner_lineFreq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [L2.inner_def, ← integral_re]
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_freqMultiplier n p (hInvMap hlam) v σ] with t ht
    rw [ht, hInvMap_totalFrequency, RCLike.inner_apply, mul_assoc, Complex.mul_conj',
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  · exact L2.integrable_inner _ _

/-- **`‖F‖²_{H⁻¹}` in symmetric coefficients.**  For a degree-`n` element `F`
with symmetric coefficient `f`, the `H⁻¹` energy of `eq:var` is
`n! ⟨f, (λ + θ(P))⁻¹ f⟩`. -/
theorem hMinusEnergy_eq_symCoeff (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (homogeneousWalshSynthesis n c) =
      n.factorial * RCLike.re (inner ℂ (symCoeff n (homogeneousWalshSynthesis n c))
        (orderedMultiplier n p (hInvMap hlam) (symCoeff n (homogeneousWalshSynthesis n c)))) := by
  rw [inner_symCoeff_orderedMultiplier, hMinusEnergy_homogeneousWalshSynthesis n hlam p c]
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hre : RCLike.re ((n.factorial : ℂ)⁻¹ * inner ℂ (walshOrdered n c)
      (orderedMultiplier n p (hInvMap hlam) (walshOrdered n c))) =
      (n.factorial : ℝ)⁻¹ * RCLike.re (inner ℂ (walshOrdered n c)
        (orderedMultiplier n p (hInvMap hlam) (walshOrdered n c))) := by
    rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      RCLike.re_to_complex, RCLike.re_to_complex, Complex.re_ofReal_mul]
  rw [hre, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]
  rw [← (orderedFourierEquiv n).inner_map_map, orderedFourierEquiv_apply,
    orderedFourierEquiv_apply, orderedFourier_orderedMultiplier, re_inner_freqMultiplier,
    tsum_fintype]
  rfl

/-! ### The line-frequency coefficient of a reordering -/

theorem slotPermute_single (n : ℕ) (π : Equiv.Perm (Fin n)) (t : Fin n → LineIndex) (a : ℂ) :
    slotPermute n π (lp.single 2 t a) = lp.single 2 (t ∘ π.symm) a := by
  classical
  apply lp.ext
  funext u
  rw [slotPermute_apply, lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl
    funext b
    simp
  · rintro rfl
    funext b
    simp

theorem torusPerm_mFourierLp (n : ℕ) (π : Equiv.Perm (Fin n)) (k : Fin n → ℤ) :
    torusPerm n π (mFourierLp 2 k) = mFourierLp 2 (k ∘ π.symm) := by
  apply Lp.ext
  have h1 := coeFn_torusPerm n π (mFourierLp 2 k)
  have h2 := (measurePreserving_torusPermMap n π).quasiMeasurePreserving.ae_eq_comp
    (coeFn_mFourierLp (d := Fin n) 2 k)
  filter_upwards [h1, h2, coeFn_mFourierLp (d := Fin n) 2 (k ∘ π.symm)] with θ e1 e2 e3
  rw [e1, e3]
  simp only [Function.comp_apply, torusPermMap_apply] at e2
  rw [e2]
  show (∏ a : Fin n, fourier (k a) ((θ ∘ π) a)) = ∏ b : Fin n, fourier ((k ∘ π.symm) b) (θ b)
  calc (∏ a : Fin n, fourier (k a) ((θ ∘ π) a))
      = ∏ a : Fin n, (fun b => fourier ((k ∘ π.symm) b) (θ b)) (π a) := by simp
    _ = ∏ b : Fin n, fourier ((k ∘ π.symm) b) (θ b) :=
        Equiv.prod_comp π (fun b => fourier ((k ∘ π.symm) b) (θ b))

/-- **The line-frequency coefficient of a reordering.**  Reordering the slots
of an ordered coefficient by `π` permutes the axis patterns and the line
frequencies in the same way. -/
theorem orderedFourier_slotPermute (n : ℕ) (π : Equiv.Perm (Fin n)) (c : OrderedCoefficient n)
    (σ : Fin n → Axis) :
    (orderedFourier n (slotPermute n π c)) σ =
      torusPerm n π ((orderedFourier n c) (σ ∘ π)) := by
  classical
  refine l2_ext_on_single
    ((freqEval n σ).comp ((orderedFourier n).toContinuousLinearMap.comp
      (slotPermute n π).toLinearIsometry.toContinuousLinearMap))
    ((torusPerm n π).toContinuousLinearMap.comp ((freqEval n (σ ∘ π)).comp
      (orderedFourier n).toContinuousLinearMap)) (fun t => ?_) c
  change (orderedFourier n (slotPermute n π (lp.single 2 t (1 : ℂ)))) σ =
    torusPerm n π ((orderedFourier n (lp.single 2 t (1 : ℂ))) (σ ∘ π))
  rw [slotPermute_single, orderedFourier_single, orderedFourier_single, one_smul, one_smul,
    orderedFreqFamily, orderedFreqFamily]
  have hpat : tuplePattern (t ∘ π.symm) = tuplePattern t ∘ π.symm := rfl
  have hcoord : tupleCoord (t ∘ π.symm) = tupleCoord t ∘ π.symm := rfl
  by_cases hσ : σ ∘ π = tuplePattern t
  · have hσ' : σ = tuplePattern (t ∘ π.symm) := by
      rw [hpat, ← hσ]
      funext b
      simp
    conv_lhs => rw [hσ', lp.single_apply_self]
    rw [hσ, lp.single_apply_self, hcoord, torusPerm_mFourierLp]
  · have hσ' : σ ≠ tuplePattern (t ∘ π.symm) := by
      intro h
      apply hσ
      rw [h, hpat]
      funext b
      simp
    rw [lp.single_apply_ne _ _ _ hσ', lp.single_apply_ne _ _ _ hσ, map_zero]

/-! ### The multiplier `M` of `eq:M` -/

/-- The multiplier `M(P) = κ(λ + θ(P) + 2|sin(P₁/2)| + 2|sin(P₂/2)|)` of `eq:M`,
as a function on the two-torus. -/
def multiplierMap (kappa : ℝ) (q : Estimates.Parameters) : C(UnitAddTorus (Fin 2), ℝ) :=
  ⟨fun ψ => kappa * (q.lambda + ((1 - cosMap (ψ 0)) + (1 - cosMap (ψ 1))) +
      Real.sqrt (2 * (1 - cosMap (ψ 0))) + Real.sqrt (2 * (1 - cosMap (ψ 1)))), by
    have h0 : Continuous fun ψ : UnitAddTorus (Fin 2) => cosMap (ψ 0) :=
      cosMap.continuous.comp (continuous_apply 0)
    have h1 : Continuous fun ψ : UnitAddTorus (Fin 2) => cosMap (ψ 1) :=
      cosMap.continuous.comp (continuous_apply 1)
    fun_prop⟩

theorem multiplierMap_totalFrequencyPoint (kappa : ℝ) (q : Estimates.Parameters) (n : ℕ)
    (p : Fin 2 → ℝ) (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) :
    multiplierMap kappa q (totalFrequencyPoint n p σ t) =
      Estimates.multiplier kappa q (totalFrequency n p σ t) := by
  show kappa * (q.lambda + ((1 - cosMap _) + (1 - cosMap _)) + Real.sqrt (2 * (1 - cosMap _)) +
    Real.sqrt (2 * (1 - cosMap _))) = _
  simp only [totalFrequencyPoint, cosMap_coe]
  rw [multiplier_eq_sqrt, Estimates.theta, Estimates.dispersion, Estimates.dispersion]

/-- `M` as a complex multiplier. -/
def multiplierMapC (kappa : ℝ) (q : Estimates.Parameters) : C(UnitAddTorus (Fin 2), ℂ) :=
  ⟨fun ψ => ((multiplierMap kappa q ψ : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (multiplierMap kappa q).continuous⟩

/-- The quadratic form of `M` on the frequency side. -/
theorem re_inner_freqMultiplier_multiplier (n : ℕ) (p : Fin 2 → ℝ) (kappa : ℝ)
    (q : Estimates.Parameters) (v : LineFreqL2 n) :
    RCLike.re (inner ℂ v (freqMultiplier n p (multiplierMapC kappa q) v)) =
      ∑ σ : Fin n → Axis, ∫ t, Estimates.multiplier kappa q (totalFrequency n p σ t) *
        ‖(v σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [inner_lineFreq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [L2.inner_def, ← integral_re]
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_freqMultiplier n p (multiplierMapC kappa q) v σ] with t ht
    rw [ht, RCLike.inner_apply]
    show RCLike.re ((((multiplierMap kappa q (totalFrequencyPoint n p σ t) : ℝ) : ℂ) *
        (v σ : UnitAddTorus (Fin n) → ℂ) t) * (starRingEnd ℂ) ((v σ : UnitAddTorus (Fin n) → ℂ) t)) = _
    rw [multiplierMap_totalFrequencyPoint, mul_assoc, Complex.mul_conj',
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  · exact L2.integrable_inner _ _

end

end Manhattan.Paper
