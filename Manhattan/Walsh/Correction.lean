import Manhattan.Walsh.LowDegree
import Manhattan.Estimates.DegreeThree
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Ordered coordinates for the type-`(1,1,2)` correction

The homogeneous Walsh carrier remains Finset-indexed.  The raw correction is
first represented by two ordered row indices and one column index; the strict
ordering below is the canonical representative used when the coincident-row
diagonal is removed.  This is the concrete bridge from the ordered raw
calculation to `Type112Index`.

Paper: `manuscript.tex:719-740`, `manuscript.tex:1045-1052`, and
`manuscript.tex:1208-1219`.
-/

namespace Manhattan

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance (p : Prop) : Decidable p := Classical.propDecidable p

open MeasureTheory

attribute [local instance] Real.fact_zero_lt_one

/-- The unit circle carries its normalized Haar measure throughout this file. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Three integer line coordinates: two rows followed by one column. -/
abbrev RawType112Index := Fin 3 → ℤ

/-- The ordered off-diagonal part of the raw type-`(1,1,2)` carrier. -/
abbrev OrderedType112Index :=
  {n : RawType112Index // n 0 < n 1}

/-- The Finset of lines represented by ordered type-`(1,1,2)` coordinates. -/
def orderedType112Lines (n : OrderedType112Index) : Finset LineIndex :=
  {(Axis.horizontal, n.1 0), (Axis.horizontal, n.1 1),
    (Axis.vertical, n.1 2)}

theorem orderedType112Lines_isType112 (n : OrderedType112Index) :
    IsType112Index (orderedType112Lines n) := by
  classical
  have hne : n.1 0 ≠ n.1 1 := ne_of_lt n.2
  constructor
  · simp [orderedType112Lines, hne]
  · rw [show (orderedType112Lines n).filter
        (fun l => l.1 = Axis.horizontal) =
        {(Axis.horizontal, n.1 0), (Axis.horizontal, n.1 1)} by
      ext l
      rcases l with ⟨i, k⟩
      cases i <;> simp [orderedType112Lines]]
    simp [hne]

/-- Canonical ordered coordinates give a genuine Finset type-`(1,1,2)`
index. -/
def orderedType112IndexToFinset (n : OrderedType112Index) : Type112Index :=
  ⟨orderedType112Lines n, orderedType112Lines_isType112 n⟩

theorem orderedType112IndexToFinset_injective :
    Function.Injective orderedType112IndexToFinset := by
  intro n m h
  apply Subtype.ext
  funext i
  have hsets : orderedType112Lines n = orderedType112Lines m :=
    congrArg Subtype.val h
  fin_cases i
  · change n.1 0 = m.1 0
    have hnmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, n.1 0) ∈ s) hsets
    have hmmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, m.1 0) ∈ s) hsets
    simp [orderedType112Lines] at hnmem hmmem
    omega
  · change n.1 1 = m.1 1
    have hnmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, n.1 1) ∈ s) hsets
    have hmmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, m.1 1) ∈ s) hsets
    simp [orderedType112Lines] at hnmem hmmem
    omega
  · have hnmem : (Axis.vertical, n.1 2) ∈ orderedType112Lines m := by
      rw [← hsets]
      simp [orderedType112Lines]
    change n.1 2 = m.1 2
    simpa [orderedType112Lines] using hnmem

theorem orderedType112IndexToFinset_surjective :
    Function.Surjective orderedType112IndexToFinset := by
  intro S
  classical
  let H := S.1.filter fun l => l.1 = Axis.horizontal
  let V := S.1.filter fun l => ¬l.1 = Axis.horizontal
  have hHcard : H.card = 2 := S.2.2
  have hVcard : V.card = 1 := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S.1) (fun l => l.1 = Axis.horizontal)
    change H.card + V.card = S.1.card at hsplit
    have hScard : S.1.card = 3 := S.2.1
    omega
  obtain ⟨x, y, hxy, hH⟩ := Finset.card_eq_two.mp hHcard
  obtain ⟨z, hV⟩ := Finset.card_eq_one.mp hVcard
  have hxH : x.1 = Axis.horizontal := by
    have : x ∈ H := by simp [hH]
    exact (Finset.mem_filter.mp this).2
  have hyH : y.1 = Axis.horizontal := by
    have : y ∈ H := by simp [hH]
    exact (Finset.mem_filter.mp this).2
  have hzV : z.1 = Axis.vertical := by
    have hz : ¬z.1 = Axis.horizontal := by
      have : z ∈ V := by simp [hV]
      exact (Finset.mem_filter.mp this).2
    cases hzaxis : z.1
    · simp [hzaxis] at hz
    · rfl
  rcases x with ⟨ix, k⟩
  rcases y with ⟨iy, l⟩
  rcases z with ⟨iz, m⟩
  change ix = Axis.horizontal at hxH
  change iy = Axis.horizontal at hyH
  change iz = Axis.vertical at hzV
  subst ix
  subst iy
  subst iz
  have hkl : k ≠ l := by
    intro h
    apply hxy
    simp [h]
  have hS : S.1 =
      {(Axis.horizontal, k), (Axis.horizontal, l), (Axis.vertical, m)} := by
    apply Finset.ext
    intro w
    constructor
    · intro hw
      by_cases hwH : w.1 = Axis.horizontal
      · have : w ∈ H := Finset.mem_filter.mpr ⟨hw, hwH⟩
        rw [hH] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl <;> simp
      · have : w ∈ V := Finset.mem_filter.mpr ⟨hw, hwH⟩
        rw [hV] at this
        have hwz : w = (Axis.vertical, m) := by simpa using this
        simp [hwz]
    · intro hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · have : (Axis.horizontal, k) ∈ H := by simp [hH]
        exact (Finset.mem_filter.mp this).1
      · have : (Axis.horizontal, l) ∈ H := by simp [hH]
        exact (Finset.mem_filter.mp this).1
      · have : (Axis.vertical, m) ∈ V := by simp [hV]
        exact (Finset.mem_filter.mp this).1
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · let n : OrderedType112Index := ⟨![k, l, m], by simpa⟩
    refine ⟨n, Subtype.ext ?_⟩
    simpa [orderedType112IndexToFinset, orderedType112Lines, n] using hS.symm
  · let n : OrderedType112Index := ⟨![l, k, m], by simpa⟩
    refine ⟨n, Subtype.ext ?_⟩
    change orderedType112Lines n = S.1
    change {(Axis.horizontal, l), (Axis.horizontal, k),
      (Axis.vertical, m)} = S.1
    simpa [Finset.insert_comm] using hS.symm

/-- The canonical identification between ordered distinct triples and the
Finset-indexed type-`(1,1,2)` Walsh carrier. -/
noncomputable def orderedType112Equiv : OrderedType112Index ≃ Type112Index :=
  Equiv.ofBijective orderedType112IndexToFinset
    ⟨orderedType112IndexToFinset_injective,
      orderedType112IndexToFinset_surjective⟩

/-- The physical ordered representative of a Finset type-`(1,1,2)` index. -/
def type112RawIndex (S : Type112Index) : RawType112Index :=
  (orderedType112Equiv.symm S).1

theorem type112RawIndex_injective : Function.Injective type112RawIndex := by
  intro S T h
  apply orderedType112Equiv.symm.injective
  exact Subtype.ext h

/-- Restrict an ordered raw square-summable coefficient to the strict
off-diagonal and reindex it by the Finset carrier.  This is the coefficient
form of the diagonal projection `Π₃`. -/
noncomputable def type112DiagonalProjection
    (c : ℓ²(RawType112Index, ℂ)) : ℓ²(Type112Index, ℂ) :=
  ⟨fun S => c (type112RawIndex S), by
    apply memℓp_gen
    simpa using ((lp.memℓp c).summable (by norm_num)).comp_injective
      type112RawIndex_injective⟩

@[simp] theorem type112DiagonalProjection_apply
    (c : ℓ²(RawType112Index, ℂ)) (S : Type112Index) :
    type112DiagonalProjection c S = c (type112RawIndex S) := rfl

/-- Removing the coincident-row diagonal is contractive. -/
theorem norm_type112DiagonalProjection_le
    (c : ℓ²(RawType112Index, ℂ)) :
    ‖type112DiagonalProjection c‖ ≤ ‖c‖ := by
  have hsquares : ‖type112DiagonalProjection c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
    rw [show ‖type112DiagonalProjection c‖ ^ 2 =
        ∑' S, ‖type112DiagonalProjection c S‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (by norm_num)
        (type112DiagonalProjection c)]
    rw [show ‖c‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (by norm_num) c]
    have hsum : Summable (fun S => ‖type112DiagonalProjection c S‖ ^ 2) := by
      simpa [Function.comp_def] using
        (((lp.memℓp c).summable (by norm_num)).comp_injective
          type112RawIndex_injective)
    have hraw : Summable (fun n => ‖c n‖ ^ 2) := by
      simpa using (lp.memℓp c).summable (by norm_num)
    exact hsum.tsum_le_tsum_of_inj type112RawIndex
      type112RawIndex_injective (fun _ _ => sq_nonneg _)
      (fun _ => le_rfl) hraw
  nlinarith [norm_nonneg (type112DiagonalProjection c), norm_nonneg c]

/-- The representative angle in `(-π,π]` of a point on the unit additive
circle. -/
noncomputable def unitTorusAngle (x : UnitAddCircle) : ℝ :=
  2 * Real.pi * (AddCircle.measurableEquivIoc 1 (-(1 / 2 : ℝ)) x).1

theorem unitTorusAngle_measurable : Measurable unitTorusAngle := by
  unfold unitTorusAngle
  fun_prop

/-- The paper's raw, possibly-diagonal correction as a function on the
three-dimensional normalized torus. -/
noncomputable def rawCorrectionFunction (kappa : ℝ)
    (q : Estimates.Parameters) (a p₂ : ℝ) (x : UnitAddTorus (Fin 3)) : ℂ :=
  Estimates.correctionCoefficient kappa q a p₂
    (unitTorusAngle (x 0)) (unitTorusAngle (x 1))
    (unitTorusAngle (x 2))

/-- The explicit raw coefficient is symmetric in its two row-frequency
variables. -/
theorem correctionCoefficient_swap (kappa : ℝ)
    (q : Estimates.Parameters) (a p₂ r r' beta : ℝ) :
    Estimates.correctionCoefficient kappa q a p₂ r r' beta =
      Estimates.correctionCoefficient kappa q a p₂ r' r beta := by
  unfold Estimates.correctionCoefficient
  rw [show r' + r - p₂ = r + r' - p₂ by ring]
  ring

theorem correctionV_measurable (kappa : ℝ)
    (q : Estimates.Parameters) (a : ℝ) :
    Measurable (fun z : ℝ × ℝ =>
      Estimates.correctionV kappa q a z.1 z.2) := by
  unfold Estimates.correctionV
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst
  · apply Measurable.inv
    apply Measurable.add
    · unfold Estimates.correctionB Estimates.dispersion
      fun_prop
    · exact Estimates.correctionSigma_measurable kappa q a
  · exact measurable_const

private theorem firstCorrectionIndicator_measurable
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    MeasurableSet {z : ℝ × ℝ × ℝ |
      z.1 + z.2.1 - p₂ ∈ Estimates.correctionInterval q a z.1 z.2.2} := by
  unfold Estimates.correctionInterval Estimates.Parameters.supportInterval
    Estimates.Parameters.delta Estimates.Parameters.r0
  measurability

private theorem secondCorrectionIndicator_measurable
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    MeasurableSet {z : ℝ × ℝ × ℝ |
      z.1 + z.2.1 - p₂ ∈ Estimates.correctionInterval q a z.2.1 z.2.2} := by
  unfold Estimates.correctionInterval Estimates.Parameters.supportInterval
    Estimates.Parameters.delta Estimates.Parameters.r0
  measurability

theorem correctionCoefficient_measurable (kappa : ℝ)
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    Measurable (fun z : ℝ × ℝ × ℝ =>
      Estimates.correctionCoefficient kappa q a p₂ z.1 z.2.1 z.2.2) := by
  let r : ℝ × ℝ × ℝ → ℝ := fun z => z.1
  let r' : ℝ × ℝ × ℝ → ℝ := fun z => z.2.1
  let beta : ℝ × ℝ × ℝ → ℝ := fun z => z.2.2
  let alpha : ℝ × ℝ × ℝ → ℝ := fun z => r z + r' z - p₂
  have hr : Measurable r := measurable_fst
  have hr' : Measurable r' := measurable_fst.comp measurable_snd
  have hbeta : Measurable beta := measurable_snd.comp measurable_snd
  have halpha : Measurable alpha := (hr.add hr').sub measurable_const
  have hmult : Measurable (fun z =>
      (Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency (beta z) (alpha z)) : ℂ)) := by
    simp only [Estimates.multiplier, Estimates.mixedTotalFrequency,
      Estimates.theta, Estimates.dispersion, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    fun_prop
  have hv : Measurable (fun z =>
      (Estimates.correctionV kappa q a (r z) (beta z) : ℂ)) :=
    ((correctionV_measurable kappa q a).comp (hr.prodMk hbeta)).complex_ofReal
  have hv' : Measurable (fun z =>
      (Estimates.correctionV kappa q a (r' z) (beta z) : ℂ)) :=
    ((correctionV_measurable kappa q a).comp (hr'.prodMk hbeta)).complex_ofReal
  have hi : Measurable (fun z : ℝ × ℝ × ℝ =>
      if alpha z ∈ Estimates.correctionInterval q a (r z) (beta z) then
        (1 : ℂ) else 0) :=
    measurable_const.ite (by
      simpa only [r, r', beta, alpha] using
        firstCorrectionIndicator_measurable q a p₂) measurable_const
  have hi' : Measurable (fun z : ℝ × ℝ × ℝ =>
      if alpha z ∈ Estimates.correctionInterval q a (r' z) (beta z) then
        (1 : ℂ) else 0) :=
    measurable_const.ite (by
      simpa only [r, r', beta, alpha] using
        secondCorrectionIndicator_measurable q a p₂) measurable_const
  simpa only [Estimates.correctionCoefficient, r, r', beta, alpha] using
    ((measurable_const.mul
      (Real.continuous_sin.measurable.comp hbeta).complex_ofReal).div hmult).mul
        ((hv.mul hi).add (hv'.mul hi'))

theorem rawCorrectionFunction_measurable (kappa : ℝ)
    (q : Estimates.Parameters) (a p₂ : ℝ) :
    Measurable (rawCorrectionFunction kappa q a p₂) := by
  let φ : UnitAddTorus (Fin 3) → ℝ × ℝ × ℝ := fun x =>
    (unitTorusAngle (x 0), unitTorusAngle (x 1), unitTorusAngle (x 2))
  have h0 : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 0)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 1)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  have h2 : Measurable (fun x : UnitAddTorus (Fin 3) =>
      unitTorusAngle (x 2)) :=
    unitTorusAngle_measurable.comp (measurable_pi_apply 2)
  have hφ : Measurable φ := h0.prodMk (h1.prodMk h2)
  have hcomp := (correctionCoefficient_measurable kappa q a p₂).comp hφ
  simpa only [rawCorrectionFunction, φ] using hcomp

theorem abs_correctionV_le_inv {kappa : ℝ} {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hlambda : 0 < q.lambda) (a r beta : ℝ) :
    |Estimates.correctionV kappa q a r beta| ≤ q.lambda⁻¹ := by
  classical
  rw [Estimates.correctionV]
  split_ifs with hr
  · have hdenPos := Estimates.correctionDenominator_pos hkappa hlambda a r beta
    rw [abs_of_pos (inv_pos.mpr hdenPos)]
    apply (inv_le_inv₀ hdenPos hlambda).2
    unfold Estimates.correctionB
    linarith [Estimates.dispersion_nonneg r,
      Estimates.dispersion_nonneg beta,
      Estimates.correctionSigma_nonneg hkappa hlambda a r beta]
  · exact (abs_zero.trans_le (inv_nonneg.mpr hlambda.le))

theorem correctionCoefficient_norm_bound {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ r r' beta : ℝ) :
    ‖Estimates.correctionCoefficient kappa q a p₂ r r' beta‖ ≤
      (kappa * q.lambda)⁻¹ * (2 * q.lambda⁻¹) := by
  classical
  let alpha := r + r' - p₂
  let m := Estimates.multiplier kappa q
    (Estimates.mixedTotalFrequency beta alpha)
  let v := Estimates.correctionV kappa q a r beta
  let v' := Estimates.correctionV kappa q a r' beta
  let e : ℂ := if alpha ∈ Estimates.correctionInterval q a r beta then 1 else 0
  let e' : ℂ := if alpha ∈ Estimates.correctionInterval q a r' beta then 1 else 0
  have hmPos : 0 < m := Estimates.multiplier_pos hkappa hlambda _
  have hmLower : kappa * q.lambda ≤ m := by
    unfold m Estimates.multiplier
    apply mul_le_mul_of_nonneg_left _ hkappa.le
    have htheta := Estimates.theta_nonneg
      (Estimates.mixedTotalFrequency beta alpha)
    have hsin0 : 0 ≤ |Real.sin
        (Estimates.mixedTotalFrequency beta alpha 0 / 2)| := abs_nonneg _
    have hsin1 : 0 ≤ |Real.sin
        (Estimates.mixedTotalFrequency beta alpha 1 / 2)| := abs_nonneg _
    linarith
  have hprodPos : 0 < kappa * q.lambda := mul_pos hkappa hlambda
  have hminv : m⁻¹ ≤ (kappa * q.lambda)⁻¹ :=
    (inv_le_inv₀ hmPos hprodPos).2 hmLower
  have hfirst :
      ‖Complex.I * (Real.sin beta : ℂ) / (m : ℂ)‖ ≤
        (kappa * q.lambda)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real]
    simp only [Real.norm_eq_abs, abs_of_pos hmPos, div_eq_mul_inv]
    have hsin : |Real.sin beta| ≤ 1 := Real.abs_sin_le_one beta
    simpa only [one_mul] using mul_le_mul hsin hminv
      (inv_nonneg.mpr hmPos.le) zero_le_one
  have he : ‖e‖ ≤ 1 := by
    unfold e
    split_ifs <;> simp
  have he' : ‖e'‖ ≤ 1 := by
    unfold e'
    split_ifs <;> simp
  have hinvNonneg : 0 ≤ q.lambda⁻¹ := inv_nonneg.mpr hlambda.le
  have hv : ‖(v : ℂ)‖ ≤ q.lambda⁻¹ := by
    simpa only [Complex.norm_real, v] using
      abs_correctionV_le_inv hkappa hlambda a r beta
  have hv' : ‖(v' : ℂ)‖ ≤ q.lambda⁻¹ := by
    simpa only [Complex.norm_real, v'] using
      abs_correctionV_le_inv hkappa hlambda a r' beta
  have hve : ‖(v : ℂ) * e‖ ≤ q.lambda⁻¹ := by
    rw [norm_mul]
    simpa only [mul_one] using
      mul_le_mul hv he (norm_nonneg _) hinvNonneg
  have hve' : ‖(v' : ℂ) * e'‖ ≤ q.lambda⁻¹ := by
    rw [norm_mul]
    simpa only [mul_one] using
      mul_le_mul hv' he' (norm_nonneg _) hinvNonneg
  have hsum : ‖(v : ℂ) * e + (v' : ℂ) * e'‖ ≤ 2 * q.lambda⁻¹ := by
    calc
      _ ≤ ‖(v : ℂ) * e‖ + ‖(v' : ℂ) * e'‖ := norm_add_le _ _
      _ ≤ q.lambda⁻¹ + q.lambda⁻¹ := add_le_add hve hve'
      _ = 2 * q.lambda⁻¹ := by ring
  change ‖Complex.I * (Real.sin beta : ℂ) / (m : ℂ) *
      ((v : ℂ) * e + (v' : ℂ) * e')‖ ≤ _
  calc
    _ ≤ ‖Complex.I * (Real.sin beta : ℂ) / (m : ℂ)‖ *
        ‖(v : ℂ) * e + (v' : ℂ) * e'‖ := norm_mul_le _ _
    _ ≤ (kappa * q.lambda)⁻¹ * (2 * q.lambda⁻¹) :=
      mul_le_mul hfirst hsum (norm_nonneg _)
        (inv_nonneg.mpr hprodPos.le)

/-- The raw correction is square-integrable on the three-dimensional
normalized torus.  This is the analytic square-summability input for the
Fourier coefficient sequence. -/
theorem rawCorrectionFunction_memLp {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    MemLp (rawCorrectionFunction kappa q a p₂) 2
      (volume : Measure (UnitAddTorus (Fin 3))) := by
  apply MemLp.of_bound
    (rawCorrectionFunction_measurable kappa q a p₂).aestronglyMeasurable
    ((kappa * q.lambda)⁻¹ * (2 * q.lambda⁻¹))
  filter_upwards with x
  exact correctionCoefficient_norm_bound hkappa hlambda a p₂
    (unitTorusAngle (x 0)) (unitTorusAngle (x 1))
    (unitTorusAngle (x 2))

/-- The raw correction as an honest `L²` vector. -/
noncomputable def rawCorrectionL2 {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  (rawCorrectionFunction_memLp hkappa hlambda a p₂).toLp
    (rawCorrectionFunction kappa q a p₂)

/-- Fourier coefficients of the raw, possibly-coincident correction. -/
noncomputable def rawCorrectionFourierCoefficients {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    ℓ²(RawType112Index, ℂ) :=
  UnitAddTorus.mFourierBasis.repr
    (rawCorrectionL2 hkappa hlambda a p₂)

/-- The diagonal-free Finset coefficient `Π₃ k̃`. -/
noncomputable def correctionType112Coefficients {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    ℓ²(Type112Index, ℂ) :=
  type112DiagonalProjection
    (rawCorrectionFourierCoefficients hkappa hlambda a p₂)

/-- The actual degree-three Walsh vector `k_p` obtained after `Π₃`. -/
noncomputable def correctionWalsh {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) : WalshL2 :=
  type112WalshSynthesis
    (correctionType112Coefficients hkappa hlambda a p₂)

/-- The raw Fourier coefficients are square-summable by construction.
-/
theorem rawCorrectionFourierCoefficients_memℓp {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    Memℓp (rawCorrectionFourierCoefficients hkappa hlambda a p₂ :
      RawType112Index → ℂ) 2 :=
  lp.memℓp _

/-- Each projected Finset coefficient is the multivariate Fourier
coefficient of the explicit raw correction at the canonical ordered spatial
index. -/
theorem correctionType112Coefficients_apply {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (S : Type112Index) :
    correctionType112Coefficients hkappa hlambda a p₂ S =
      UnitAddTorus.mFourierCoeff
        (rawCorrectionL2 hkappa hlambda a p₂) (type112RawIndex S) := by
  simp [correctionType112Coefficients, rawCorrectionFourierCoefficients,
    UnitAddTorus.mFourierBasis_repr]

/-- `Π₃` cannot increase the norm of the raw correction. -/
theorem norm_correctionType112Coefficients_le {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    ‖correctionType112Coefficients hkappa hlambda a p₂‖ ≤
      ‖rawCorrectionFourierCoefficients hkappa hlambda a p₂‖ :=
  norm_type112DiagonalProjection_le _

/-- The synthesized correction has exactly the projected coefficient norm.
-/
theorem norm_correctionWalsh {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    ‖correctionWalsh hkappa hlambda a p₂‖ =
      ‖correctionType112Coefficients hkappa hlambda a p₂‖ := by
  simp [correctionWalsh]

/-- The projected correction lies in homogeneous Walsh degree three. -/
theorem correctionWalsh_mem_degree {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    correctionWalsh hkappa hlambda a p₂ ∈ walshDegree 3 :=
  type112WalshSynthesis_mem_degree _

/-! ### The `(shift)` phase

The manuscript writes every scalar object of Lemmas 4.1, 5.2 and 6.4 in the
shifted variables `r=p₂+s`, `r'=p₂+s'`, `β=p₁+u` of `manuscript.tex:791-800`,
where `(s,s',u)` are the Walsh line frequencies.  The Fourier coefficient of
`k̃(p₂+s,p₂+s',p₁+u)` at the line index `(m,m',n)` is the coefficient of
`k̃` there times the unimodular phase `e^{i(m+m')p₂+inp₁}`, which is the value
at the raw index of the multivariate character attached to the point
`(p₂/2π,p₂/2π,p₁/2π)` of the frequency torus.  The declarations below install
that phase; the coefficient moduli, and hence every `ℓ²` norm, are unchanged.
-/

/-- The point of the three-dimensional line-frequency torus by which the
substitution `r=p₂+s`, `r'=p₂+s'`, `β=p₁+u` of (shift) translates. -/
noncomputable def shiftTorusPoint (p₁ p₂ : ℝ) : UnitAddTorus (Fin 3) :=
  ![((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle),
    ((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle),
    ((p₁ / (2 * Real.pi) : ℝ) : UnitAddCircle)]

/-- The `(shift)` phase `e^{i(m+m')p₂+inp₁}` at a raw type-`(1,1,2)` line
index. -/
noncomputable def rawType112ShiftPhase (p₁ p₂ : ℝ) (n : RawType112Index) : ℂ :=
  UnitAddTorus.mFourier n (shiftTorusPoint p₁ p₂)

/-- The phase is the manuscript's `e^{i(m+m')p₂+inp₁}`. -/
theorem rawType112ShiftPhase_eq (p₁ p₂ : ℝ) (n : RawType112Index) :
    rawType112ShiftPhase p₁ p₂ n =
      Complex.exp (Complex.I *
        ((((n 0 : ℝ) + (n 1 : ℝ)) * p₂ + (n 2 : ℝ) * p₁ : ℝ) : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  show (∏ i : Fin 3, fourier (n i) (shiftTorusPoint p₁ p₂ i)) = _
  rw [Fin.prod_univ_three]
  simp only [shiftTorusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

theorem norm_rawType112ShiftPhase (p₁ p₂ : ℝ) (n : RawType112Index) :
    ‖rawType112ShiftPhase p₁ p₂ n‖ = 1 := by
  show ‖∏ i : Fin 3, fourier (n i) (shiftTorusPoint p₁ p₂ i)‖ = 1
  simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

/-- The pointwise product of a type-`(1,1,2)` coefficient with the (shift)
phase. -/
noncomputable def type112ShiftTwistFun (p₁ p₂ : ℝ) (c : ℓ²(Type112Index, ℂ)) :
    ℓ²(Type112Index, ℂ) :=
  ⟨fun S => rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * c S, by
    apply memℓp_gen
    refine ((lp.memℓp c).summable (by norm_num)).congr fun S => ?_
    rw [norm_mul, norm_rawType112ShiftPhase, one_mul]⟩

@[simp] theorem type112ShiftTwistFun_apply (p₁ p₂ : ℝ)
    (c : ℓ²(Type112Index, ℂ)) (S : Type112Index) :
    type112ShiftTwistFun p₁ p₂ c S =
      rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * c S := rfl

theorem norm_type112ShiftTwistFun_apply (p₁ p₂ : ℝ)
    (c : ℓ²(Type112Index, ℂ)) (S : Type112Index) :
    ‖type112ShiftTwistFun p₁ p₂ c S‖ = ‖c S‖ := by
  rw [type112ShiftTwistFun_apply, norm_mul, norm_rawType112ShiftPhase, one_mul]

/-- The phase is unimodular, so the twist moves no coefficient modulus. -/
theorem norm_type112ShiftTwistFun (p₁ p₂ : ℝ) (c : ℓ²(Type112Index, ℂ)) :
    ‖type112ShiftTwistFun p₁ p₂ c‖ = ‖c‖ := by
  have hsq : ‖type112ShiftTwistFun p₁ p₂ c‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [show ‖type112ShiftTwistFun p₁ p₂ c‖ ^ 2 =
        ∑' S, ‖type112ShiftTwistFun p₁ p₂ c S‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (by norm_num)
        (type112ShiftTwistFun p₁ p₂ c)]
    rw [show ‖c‖ ^ 2 = ∑' S, ‖c S‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (by norm_num) c]
    exact tsum_congr fun S => by rw [norm_type112ShiftTwistFun_apply]
  have h1 := norm_nonneg (type112ShiftTwistFun p₁ p₂ c)
  have h2 := norm_nonneg c
  nlinarith

/-- Multiplication of a type-`(1,1,2)` coefficient by the (shift) phase, as a
linear isometry.  This is the passage from the manuscript's coefficients read
at the unshifted line frequencies to the coefficients read at the true
frequencies `(r,r',β)`. -/
noncomputable def type112ShiftTwist (p₁ p₂ : ℝ) :
    ℓ²(Type112Index, ℂ) →ₗᵢ[ℂ] ℓ²(Type112Index, ℂ) where
  toFun := type112ShiftTwistFun p₁ p₂
  map_add' c d := by
    apply lp.ext
    funext S
    show rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * (c + d) S = _
    rw [lp.coeFn_add]
    show _ = type112ShiftTwistFun p₁ p₂ c S + type112ShiftTwistFun p₁ p₂ d S
    simp only [type112ShiftTwistFun_apply, Pi.add_apply]
    ring
  map_smul' z c := by
    apply lp.ext
    funext S
    show rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * (z • c) S = _
    rw [lp.coeFn_smul]
    show _ = z * type112ShiftTwistFun p₁ p₂ c S
    simp only [type112ShiftTwistFun_apply, Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' := norm_type112ShiftTwistFun p₁ p₂

@[simp] theorem type112ShiftTwist_apply (p₁ p₂ : ℝ)
    (c : ℓ²(Type112Index, ℂ)) (S : Type112Index) :
    type112ShiftTwist p₁ p₂ c S =
      rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * c S := rfl

theorem norm_type112ShiftTwist (p₁ p₂ : ℝ) (c : ℓ²(Type112Index, ℂ)) :
    ‖type112ShiftTwist p₁ p₂ c‖ = ‖c‖ :=
  norm_type112ShiftTwistFun p₁ p₂ c

theorem type112ShiftTwist_eq_zero {p₁ p₂ : ℝ} {c : ℓ²(Type112Index, ℂ)}
    {S : Type112Index} (h : c S = 0) : type112ShiftTwist p₁ p₂ c S = 0 := by
  rw [type112ShiftTwist_apply, h, mul_zero]

/-- The twist of a single basis coefficient. -/
theorem type112ShiftTwist_single (p₁ p₂ : ℝ) (S : Type112Index) (a : ℂ) :
    type112ShiftTwist p₁ p₂ (lp.single 2 S a) =
      lp.single 2 S (rawType112ShiftPhase p₁ p₂ (type112RawIndex S) * a) := by
  apply lp.ext
  funext T
  rw [show (type112ShiftTwist p₁ p₂ (lp.single 2 S a) : Type112Index → ℂ) T =
      rawType112ShiftPhase p₁ p₂ (type112RawIndex T) *
        (lp.single 2 S a : Type112Index → ℂ) T from rfl]
  by_cases h : T = S
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ h, lp.single_apply_ne _ _ _ h, mul_zero]

/-- **The competitor's degree-three coefficient.**  This is `Π₃k̃` read at the
manuscript's shifted variables `(r,r',β)` of (shift), i.e. the projected
Fourier coefficients of `k̃` carrying the compensating unimodular phase. -/
noncomputable def shiftedCorrectionType112Coefficients {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) : ℓ²(Type112Index, ℂ) :=
  type112ShiftTwist p₁ p₂ (correctionType112Coefficients hkappa hlambda a p₂)

@[simp] theorem shiftedCorrectionType112Coefficients_apply {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (S : Type112Index) :
    shiftedCorrectionType112Coefficients hkappa hlambda a p₁ p₂ S =
      rawType112ShiftPhase p₁ p₂ (type112RawIndex S) *
        correctionType112Coefficients hkappa hlambda a p₂ S := rfl

/-- The phase does not move any coefficient modulus. -/
theorem norm_shiftedCorrectionType112Coefficients {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) :
    ‖shiftedCorrectionType112Coefficients hkappa hlambda a p₁ p₂‖ =
      ‖correctionType112Coefficients hkappa hlambda a p₂‖ :=
  norm_type112ShiftTwist _ _ _

/-- **The competitor's degree-three Walsh vector `k_p`.** -/
noncomputable def shiftedCorrectionWalsh {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) : WalshL2 :=
  type112WalshSynthesis
    (shiftedCorrectionType112Coefficients hkappa hlambda a p₁ p₂)

theorem norm_shiftedCorrectionWalsh {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) :
    ‖shiftedCorrectionWalsh hkappa hlambda a p₁ p₂‖ =
      ‖correctionType112Coefficients hkappa hlambda a p₂‖ := by
  rw [shiftedCorrectionWalsh, type112WalshSynthesis.norm_map,
    norm_shiftedCorrectionType112Coefficients]

theorem shiftedCorrectionWalsh_mem_degree {kappa : ℝ}
    {q : Estimates.Parameters} (hkappa : 0 < kappa)
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) :
    shiftedCorrectionWalsh hkappa hlambda a p₁ p₂ ∈ walshDegree 3 :=
  type112WalshSynthesis_mem_degree _

end

end Manhattan
