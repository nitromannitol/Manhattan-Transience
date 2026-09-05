import Manhattan.Glue.JointFiberization
import Manhattan.Model.LowDegree

/-!
# The negative-phase vector-valued position Fourier transform

The paper uses `sum_z exp(-i p·z) F(z)`.  Mathlib's multivariate Fourier
basis has the positive phase, so we construct the reindexed negative-phase
basis explicitly.  Applying it in every Walsh coordinate gives an honest
unitary transform, not a scalar proxy.

Paper: `manuscript.tex:555-583`.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Manhattan.Glue

/-- The normalized two-torus frequency Hilbert space. -/
abbrev PositionFrequencyL2 :=
  Lp ℂ 2 (Measure.pi fun _ : Fin 2 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle))

set_option maxHeartbeats 800000 in
/-- The negative-phase Fourier basis `z ↦ exp(-2πi z·t)`. -/
noncomputable def negativeMFourierBasis :
    HilbertBasis Operator.Lattice ℂ PositionFrequencyL2 := by
  let v : Operator.Lattice → PositionFrequencyL2 := fun z => mFourierLp 2 (-z)
  have hv : Orthonormal ℂ v := by
    exact orthonormal_mFourier.comp (fun z => -z) neg_injective
  apply HilbertBasis.mk hv
  have hrange : Set.range v =
      Set.range (mFourierLp (d := Fin 2) 2) := by
    ext f
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨-z, by simp [v]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨-z, by simp [v]⟩
  rw [hrange, span_mFourierLp_closure_eq_top (by simp)]

/-- Plancherel Fourier transform with exactly the paper's negative phase. -/
noncomputable def negativePositionFourier :
    Operator.PositionL2 ≃ₗᵢ[ℂ] PositionFrequencyL2 :=
  (negativeMFourierBasis).repr.symm

@[simp] theorem negativePositionFourier_norm (f : Operator.PositionL2) :
    ‖negativePositionFourier f‖ = ‖f‖ :=
  negativePositionFourier.norm_map f

/-- A lattice delta transforms to the negative exponential monomial.  This
fixes the `p=-2πt` ambiguity identified in the cone audit. -/
@[simp] theorem negativePositionFourier_single (z : Operator.Lattice) :
    negativePositionFourier (lp.single 2 z (1 : ℂ)) = mFourierLp 2 (-z) := by
  rw [negativePositionFourier, HilbertBasis.repr_symm_single]
  simp [negativeMFourierBasis]

/-- Coordinatewise application of a linear isometric equivalence to an
infinite Hilbert sum. -/
noncomputable def l2CongrRight {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) : ℓ²(I, E) ≃ₗᵢ[ℂ] ℓ²(I, F) where
  toFun x := ⟨fun i => e (x i), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, LinearIsometryEquiv.norm_map] using
      x.prop.summable (by norm_num : 0 < ENNReal.toReal 2)⟩
  invFun y := ⟨fun i => e.symm (y i), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, LinearIsometryEquiv.norm_map] using
      y.prop.summable (by norm_num : 0 < ENNReal.toReal 2)⟩
  left_inv x := by
    apply lp.ext
    funext i
    exact e.symm_apply_apply (x i)
  right_inv y := by
    apply lp.ext
    funext i
    exact e.apply_symm_apply (y i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact e.map_add (x i) (y i)
  map_smul' a x := by
    apply lp.ext
    funext i
    exact e.map_smul a (x i)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    change (∑' i, ‖e (x i)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    simp only [LinearIsometryEquiv.norm_map]

@[simp] theorem l2CongrRight_apply {I E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (x : ℓ²(I, E)) (i : I) :
    l2CongrRight e x i = e (x i) := rfl

set_option maxHeartbeats 800000

/-- Reindex an infinite Hilbert sum by an equivalence of its coordinates. -/
noncomputable def l2CongrLeft {I J E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : I ≃ J) : ℓ²(I, E) ≃ₗᵢ[ℂ] ℓ²(J, E) where
  toFun x := ⟨fun j => x (e.symm j), by
    apply memℓp_gen
    have hx := x.prop.summable (by norm_num : 0 < ENNReal.toReal 2)
    exact e.symm.summable_iff.mpr hx⟩
  invFun y := ⟨fun i => y (e i), by
    apply memℓp_gen
    have hy := y.prop.summable (by norm_num : 0 < ENNReal.toReal 2)
    exact e.summable_iff.mpr hy⟩
  left_inv x := by
    apply lp.ext
    funext i
    simp
  right_inv y := by
    apply lp.ext
    funext j
    simp
  map_add' x y := rfl
  map_smul' a x := rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    change (∑' j, ‖x (e.symm j)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    congr 1
    exact e.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ))

@[simp] theorem l2CongrLeft_apply {I J E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : I ≃ J) (x : ℓ²(I, E)) (j : J) :
    l2CongrLeft e x j = x (e.symm j) := rfl

set_option maxHeartbeats 200000

/-- Joint position functions after Walsh expansion: each Walsh coefficient
is an `ℓ²(ℤ²)` position function. -/
abbrev JointPositionL2 :=
  ℓ²(Finset LineIndex, Operator.PositionL2)

/-- The corresponding vector-valued frequency space: each Walsh coefficient
is an honest normalized-torus `L²` function. -/
abbrev JointFrequencyL2 :=
  ℓ²(Finset LineIndex, PositionFrequencyL2)

/-- The paper's vector-valued Fourier transform, applied coordinatewise in
the complete Walsh basis. -/
noncomputable def jointPositionFourier :
    JointPositionL2 ≃ₗᵢ[ℂ] JointFrequencyL2 :=
  l2CongrRight negativePositionFourier

@[simp] theorem jointPositionFourier_norm (F : JointPositionL2) :
    ‖jointPositionFourier F‖ = ‖F‖ :=
  jointPositionFourier.norm_map F

/-- The transform of the elementary vector at Walsh index `S` and position
`z`; this is the explicit vector-valued phase convention used here. -/
@[simp] theorem jointPositionFourier_single (S : Finset LineIndex)
    (z : Operator.Lattice) :
    jointPositionFourier
        (lp.single 2 S (lp.single 2 z (1 : ℂ))) =
      lp.single 2 S (mFourierLp 2 (-z)) := by
  rw [jointPositionFourier]
  apply lp.ext
  funext T
  by_cases hTS : T = S
  · subst T
    simp [l2CongrRight]
  · simp [l2CongrRight, hTS]

end Manhattan.Glue
