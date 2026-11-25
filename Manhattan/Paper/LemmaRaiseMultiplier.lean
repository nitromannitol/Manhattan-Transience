import Manhattan.Paper.LemmaRaise
import Manhattan.Glue.SummandFourAssembly

/-!
# Lemma 5.1, last clause: `Π_n` commutes with the multipliers of `P`

The last sentence of `lem:raise` (`manuscript.tex:1179-1191`) is that `Π_n`
commutes with every continuous multiplier that is a function of the total
frequency `P`.  This file proves it on ordered coefficients.

* Equation (20), `Manhattan.Glue.orderedFourier n`, is unitary
  (`orderedFourierEquiv`): the exponential monomials of the axis sectors are a
  Hilbert basis of `LineFreqL2 n`.
* A continuous function `m` on the two-torus `ℝ²/(2πℤ)²` acts on the sector of
  axis pattern `σ` by multiplication by `m(P)`, where `P` is the total
  frequency (`freqMultiplier`); `orderedMultiplier` is the same operator on
  ordered coefficients.
* `offDiagonalProjection_comp_orderedMultiplier` is the clause.  The proof is
  the paper's: multiplication by `e^{i y·P}` is a constant multiple of the
  simultaneous translation of all line indices by `y`, which preserves
  distinctness, and the trigonometric polynomials are uniformly dense
  (`UnitAddTorus.span_mFourier_closure_eq_top`).

The two-torus is parametrized by `UnitAddTorus (Fin 2)` through `P ↦ P/(2π)`.
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

/-! ### Equation (20) is unitary -/

theorem orthogonal_span_orderedFreqFamily (n : ℕ) :
    (Submodule.span ℂ (Set.range (orderedFreqFamily n)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hzero : ∀ t, inner ℂ (orderedFreqFamily n t) v = 0 := fun t =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self t)) hv
  apply lp.ext
  funext σ
  have hσ : ∀ k : Fin n → ℤ, inner ℂ (mFourierLp 2 k) (v σ) = 0 := by
    intro k
    have h := hzero (fun a => (σ a, k a))
    rwa [orderedFreqFamily, lp.inner_single_left] at h
  have hrepr : (mFourierBasis (d := Fin n)).repr (v σ) = 0 := by
    apply lp.ext
    funext k
    rw [HilbertBasis.repr_apply_apply, coe_mFourierBasis]
    exact hσ k
  have h0 : v σ = 0 :=
    (mFourierBasis (d := Fin n)).repr.injective (hrepr.trans (map_zero _).symm)
  rw [h0]
  rfl

/-- The exponential monomials of the axis sectors form a Hilbert basis. -/
def freqBasis (n : ℕ) : HilbertBasis (Fin n → LineIndex) ℂ (LineFreqL2 n) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_orderedFreqFamily n)
    (orthogonal_span_orderedFreqFamily n)

theorem orderedFourier_eq_freqBasis (n : ℕ) (c : OrderedCoefficient n) :
    orderedFourier n c = (freqBasis n).repr.symm c := by
  classical
  refine l2_ext_on_single (orderedFourier n).toContinuousLinearMap
    (freqBasis n).repr.symm.toLinearIsometry.toContinuousLinearMap (fun t => ?_) c
  change orderedFourier n (lp.single 2 t (1 : ℂ)) = (freqBasis n).repr.symm (lp.single 2 t 1)
  rw [orderedFourier_single, one_smul, HilbertBasis.repr_symm_single, freqBasis,
    HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **Equation (20) is unitary.** -/
def orderedFourierEquiv (n : ℕ) : OrderedCoefficient n ≃ₗᵢ[ℂ] LineFreqL2 n :=
  (freqBasis n).repr.symm

theorem orderedFourierEquiv_apply (n : ℕ) (c : OrderedCoefficient n) :
    orderedFourierEquiv n c = orderedFourier n c :=
  (orderedFourier_eq_freqBasis n c).symm

/-! ### The total frequency on the two-torus -/

/-- The total frequency `P`, read on the two-torus `ℝ²/(2πℤ)²` through
`P ↦ P/(2π)`. -/
def totalFrequencyPoint (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : UnitAddTorus (Fin 2) :=
  fun i => ((totalFrequency n p σ t i / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem totalFrequencyPoint_eq (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    totalFrequencyPoint n p σ t = fun i =>
      ((p i / (2 * Real.pi) : ℝ) : UnitAddCircle) +
        ∑ a : Fin n, lineShiftVector n (Operator.axisVector i) σ a • t a := by
  funext i
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h : totalFrequency n p σ t i / (2 * Real.pi) =
      p i / (2 * Real.pi) +
        ∑ a : Fin n, lineShiftVector n (Operator.axisVector i) σ a • torusLift (t a) := by
    simp only [totalFrequency, lineFrequency, zsmul_eq_mul]
    field_simp
  rw [totalFrequencyPoint, h, AddCircle.coe_add]
  congr 1
  rw [← QuotientAddGroup.mk'_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [QuotientAddGroup.mk'_apply, AddCircle.coe_zsmul, torusLift_coe]

theorem continuous_totalFrequencyPoint (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    Continuous (totalFrequencyPoint n p σ) := by
  have h : totalFrequencyPoint n p σ = fun t i =>
      ((p i / (2 * Real.pi) : ℝ) : UnitAddCircle) +
        ∑ a : Fin n, lineShiftVector n (Operator.axisVector i) σ a • t a := by
    funext t
    exact totalFrequencyPoint_eq n p σ t
  rw [h]
  fun_prop

/-- The total frequency as a continuous map into the two-torus. -/
def totalFrequencyMap (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    C(UnitAddTorus (Fin n), UnitAddTorus (Fin 2)) :=
  ⟨totalFrequencyPoint n p σ, continuous_totalFrequencyPoint n p σ⟩

/-! ### The multiplier `m(P)` -/

theorem norm_contMulL_le (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ)) :
    ‖contMulL n g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

theorem norm_comp_totalFrequencyMap_le (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (m : C(UnitAddTorus (Fin 2), ℂ)) : ‖m.comp (totalFrequencyMap n p σ)‖ ≤ ‖m‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg m)).2 fun _ => m.norm_coe_le_norm _

theorem contMul_add_left {n : ℕ} (g g' : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (g + g') u = contMul n g u + contMul n g' u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (g + g') u, Lp.coeFn_add (contMul n g u) (contMul n g' u),
    coeFn_contMul g u, coeFn_contMul g' u] with t h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4, ContinuousMap.add_apply, add_mul]

theorem contMul_smul_left {n : ℕ} (a : ℂ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (a • g) u = a • contMul n g u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (a • g) u, Lp.coeFn_smul a (contMul n g u),
    coeFn_contMul g u] with t h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, ContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The multiplier by a continuous function `m` of the total frequency `P`, on
the frequency side of equation (20): in the sector of axis pattern `σ` it is
multiplication by `m(P)`. -/
def freqMultiplier (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ)) :
    LineFreqL2 n →L[ℂ] LineFreqL2 n :=
  ∑ σ : Fin n → Axis,
    (lp.singleContinuousLinearMap ℂ (fun _ : Fin n → Axis => Lp ℂ 2 (LineTorusMeasure n)) 2 σ)
      ∘L (contMulL n (m.comp (totalFrequencyMap n p σ)) ∘L freqEval n σ)

theorem freqMultiplier_apply (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ))
    (v : LineFreqL2 n) (σ : Fin n → Axis) :
    freqMultiplier n p m v σ = contMul n (m.comp (totalFrequencyMap n p σ)) (v σ) := by
  classical
  rw [← freqEval_apply n σ, freqMultiplier, sum_apply, map_sum]
  simp only [ContinuousLinearMap.comp_apply, freqEval_apply,
    lp.singleContinuousLinearMap_apply, lp.single_apply]
  rw [Finset.sum_pi_single, if_pos (Finset.mem_univ σ)]
  rfl

theorem freqMultiplier_add (n : ℕ) (p : Fin 2 → ℝ) (m m' : C(UnitAddTorus (Fin 2), ℂ)) :
    freqMultiplier n p (m + m') = freqMultiplier n p m + freqMultiplier n p m' := by
  ext1 v
  apply lp.ext
  funext σ
  rw [add_apply, lp.coeFn_add, Pi.add_apply, freqMultiplier_apply,
    freqMultiplier_apply, freqMultiplier_apply, ContinuousMap.add_comp, contMul_add_left]

theorem freqMultiplier_smul (n : ℕ) (p : Fin 2 → ℝ) (a : ℂ) (m : C(UnitAddTorus (Fin 2), ℂ)) :
    freqMultiplier n p (a • m) = a • freqMultiplier n p m := by
  ext1 v
  apply lp.ext
  funext σ
  rw [smul_apply, lp.coeFn_smul, Pi.smul_apply, freqMultiplier_apply,
    freqMultiplier_apply, ContinuousMap.smul_comp, contMul_smul_left]

theorem norm_freqMultiplier_le (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ)) :
    ‖freqMultiplier n p m‖ ≤ (Fintype.card (Fin n → Axis) : ℝ) * ‖m‖ := by
  rw [freqMultiplier]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum fun σ _ => ?_
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖lp.singleContinuousLinearMap ℂ
      (fun _ : Fin n → Axis => Lp ℂ 2 (LineTorusMeasure n)) 2 σ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul, lp.singleContinuousLinearMap_apply, lp.norm_single (by norm_num)]
  have h2 : ‖contMulL n (m.comp (totalFrequencyMap n p σ)) ∘L freqEval n σ‖ ≤ ‖m‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : ‖freqEval n σ‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
    calc ‖contMulL n (m.comp (totalFrequencyMap n p σ))‖ * ‖freqEval n σ‖
        ≤ ‖m‖ * 1 := mul_le_mul ((norm_contMulL_le n _).trans
          (norm_comp_totalFrequencyMap_le n p σ m)) h3 (norm_nonneg _) (norm_nonneg _)
      _ = ‖m‖ := mul_one _
  calc _ ≤ 1 * ‖m‖ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = ‖m‖ := one_mul _

/-- In the sector `σ` the multiplier is multiplication by `m(P)`. -/
theorem coeFn_freqMultiplier (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ))
    (v : LineFreqL2 n) (σ : Fin n → Axis) :
    (freqMultiplier n p m v σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n] fun t =>
      m (fun i => ((totalFrequency n p σ t i / (2 * Real.pi) : ℝ) : UnitAddCircle)) *
        (v σ : UnitAddTorus (Fin n) → ℂ) t := by
  rw [freqMultiplier_apply]
  exact coeFn_contMul _ _

/-- The multiplier `m(P)` on ordered coefficients. -/
def orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ)) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  (orderedFourierEquiv n).symm.toLinearIsometry.toContinuousLinearMap ∘L
    (freqMultiplier n p m ∘L (orderedFourierEquiv n).toLinearIsometry.toContinuousLinearMap)

theorem orderedFourier_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ)
    (m : C(UnitAddTorus (Fin 2), ℂ)) (c : OrderedCoefficient n) :
    orderedFourier n (orderedMultiplier n p m c) = freqMultiplier n p m (orderedFourier n c) := by
  rw [← orderedFourierEquiv_apply, ← orderedFourierEquiv_apply]
  simp only [orderedMultiplier, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-! ### The characters -/

theorem sum_mul_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) (y : Fin 2 → ℤ) :
    ∑ i : Fin 2, (y i : ℝ) * totalFrequency n p σ t i =
      ∑ i : Fin 2, (y i : ℝ) * p i +
        2 * Real.pi * ∑ a : Fin n, (lineShiftVector n y σ a : ℝ) * torusLift (t a) := by
  simp only [totalFrequency, lineFrequency, Fin.sum_univ_two, lineShiftVector_axisVector]
  have hterm : ∀ a : Fin n, (lineShiftVector n y σ a : ℝ) =
      (y 0 : ℝ) * ((if σ a = finAxis 0 then 0 else 1 : ℤ) : ℝ) +
        (y 1 : ℝ) * ((if σ a = finAxis 1 then 0 else 1 : ℤ) : ℝ) := by
    intro a
    cases h : σ a <;>
      simp [lineShiftVector, latticeToSite, transverseCoordinate, finAxis, h]
  simp only [hterm, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem mFourier_totalFrequencyPoint (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) (y : Fin 2 → ℤ) :
    mFourier y (totalFrequencyPoint n p σ t) =
      Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) *
        mFourier (lineShiftVector n y σ) t := by
  have hP : mFourier y (totalFrequencyPoint n p σ t) =
      Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * totalFrequency n p σ t i : ℝ) : ℂ)) := by
    show (∏ i : Fin 2, fourier (y i) (totalFrequencyPoint n p σ t i)) = _
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [totalFrequencyPoint, fourier_coe_apply, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hP, mFourier_eq_exp, ← Complex.exp_add, sum_mul_totalFrequency]
  congr 1
  push_cast
  ring

/-- Multiplication by the character `e^{i y·P}` is `e^{i y·p}` times the
frequency-side translation by `y`. -/
theorem freqMultiplier_mFourier (n : ℕ) (p : Fin 2 → ℝ) (y : Fin 2 → ℤ) :
    freqMultiplier n p (mFourier y) =
      Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) •
        (freqShift n y).toLinearIsometry.toContinuousLinearMap := by
  ext1 v
  apply lp.ext
  funext σ
  apply Lp.ext
  have hsmul : ((Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) •
      (freqShift n y).toLinearIsometry.toContinuousLinearMap) v) σ =
      Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) •
        charMul n (lineShiftVector n y σ) (v σ) := by
    rw [smul_apply, lp.coeFn_smul]
    rfl
  rw [hsmul]
  filter_upwards [coeFn_freqMultiplier n p (mFourier y) v σ,
    Lp.coeFn_smul (Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)))
      (charMul n (lineShiftVector n y σ) (v σ)),
    coeFn_charMul n (lineShiftVector n y σ) (v σ)] with t h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul,
    show (fun i => ((totalFrequency n p σ t i / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
      totalFrequencyPoint n p σ t from rfl, mFourier_totalFrequencyPoint]
  ring

theorem orderedMultiplier_mFourier (n : ℕ) (p : Fin 2 → ℝ) (y : Fin 2 → ℤ) :
    orderedMultiplier n p (mFourier y) =
      Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) •
        (orderedTranslate n y).toLinearIsometry.toContinuousLinearMap := by
  ext1 c
  apply (orderedFourierEquiv n).injective
  rw [orderedFourierEquiv_apply, orderedFourierEquiv_apply, orderedFourier_orderedMultiplier,
    freqMultiplier_mFourier, smul_apply, smul_apply,
    map_smul]
  congr 1
  exact (orderedFourier_orderedTranslate n y c).symm

/-! ### The commutation -/

/-- The multiplier depends linearly and continuously on `m`. -/
def orderedMultiplierCLM (n : ℕ) (p : Fin 2 → ℝ) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] (OrderedCoefficient n →L[ℂ] OrderedCoefficient n) :=
  LinearMap.mkContinuous
    { toFun := orderedMultiplier n p
      map_add' := fun m m' => by
        simp only [orderedMultiplier, freqMultiplier_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' := fun a m => by
        simp only [orderedMultiplier, freqMultiplier_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    (Fintype.card (Fin n → Axis) : ℝ) <| by
      intro m
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun c => ?_
      show ‖orderedMultiplier n p m c‖ ≤ _ * ‖c‖
      rw [← (orderedFourierEquiv n).norm_map, orderedFourierEquiv_apply,
        orderedFourier_orderedMultiplier, ← orderedFourierEquiv_apply,
        ← (orderedFourierEquiv n).norm_map c]
      exact ((freqMultiplier n p m).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_freqMultiplier_le n p m) (norm_nonneg _))

theorem orderedMultiplierCLM_apply (n : ℕ) (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ)) :
    orderedMultiplierCLM n p m = orderedMultiplier n p m := rfl

/-- **`Π_n` commutes with every continuous multiplier that is a function of
`P`** (`lem:raise`, `manuscript.tex:1189-1190`). -/
theorem offDiagonalProjection_comp_orderedMultiplier (n : ℕ) (p : Fin 2 → ℝ)
    (m : C(UnitAddTorus (Fin 2), ℂ)) :
    offDiagonalProjection n ∘L orderedMultiplier n p m =
      orderedMultiplier n p m ∘L offDiagonalProjection n := by
  set Ψ : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ]
      (OrderedCoefficient n →L[ℂ] OrderedCoefficient n) :=
    (ContinuousLinearMap.compL ℂ _ _ _ (offDiagonalProjection n)) ∘L orderedMultiplierCLM n p -
      ((ContinuousLinearMap.compL ℂ _ _ _).flip (offDiagonalProjection n)) ∘L
        orderedMultiplierCLM n p with hΨ
  have hΨapply : ∀ m, Ψ m = offDiagonalProjection n ∘L orderedMultiplier n p m -
      orderedMultiplier n p m ∘L offDiagonalProjection n := fun m => rfl
  let Ψl : C(UnitAddTorus (Fin 2), ℂ) →ₗ[ℂ]
      (OrderedCoefficient n →L[ℂ] OrderedCoefficient n) := Ψ
  have hspan : Submodule.span ℂ (Set.range (mFourier (d := Fin 2))) ≤ LinearMap.ker Ψl := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΨapply,
      orderedMultiplier_mFourier, sub_eq_zero]
    ext1 c
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      orderedTranslate_comm_offDiagonalProjection]
  have hclosed : IsClosed (LinearMap.ker Ψl : Set C(UnitAddTorus (Fin 2), ℂ)) :=
    ContinuousLinearMap.isClosed_ker Ψ
  have htop : (⊤ : Submodule ℂ C(UnitAddTorus (Fin 2), ℂ)) ≤ LinearMap.ker Ψl := by
    rw [← span_mFourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  have hm : m ∈ LinearMap.ker Ψl := htop Submodule.mem_top
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΨapply, sub_eq_zero] at hm
  exact hm

end

end Manhattan.Paper
