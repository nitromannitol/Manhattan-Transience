import Manhattan.Walsh.Completeness
import Manhattan.Operator.Fourier

/-!
# The concrete environment fiber

This module instantiates the abstract `Operator.FiberEnvironment` on the
fair-coin environment `WalshL2`. Environment translations and multiplication
by the two signs at the origin are constructed as unitary permutations of the
complete Walsh basis.

Paper: `manuscript.tex:543-608`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace MeasureTheory RCLike
open scoped BigOperators ComplexConjugate InnerProduct symmDiff

namespace Manhattan

/-- Identify the operator layer's functional lattice with concrete sites. -/
def latticeToSite (x : Operator.Lattice) : Site := (x 0, x 1)

@[simp] theorem latticeToSite_zero : latticeToSite 0 = 0 := by
  ext <;> rfl

@[simp] theorem latticeToSite_neg (x : Operator.Lattice) :
    latticeToSite (-x) = -latticeToSite x := by
  ext <;> rfl

theorem latticeToSite_add (x y : Operator.Lattice) :
    latticeToSite (x + y) = latticeToSite x + latticeToSite y := by
  ext <;> rfl

private noncomputable def reindexedWalshBasis
    (e : Finset LineIndex ≃ Finset LineIndex) :
    HilbertBasis (Finset LineIndex) ℂ WalshL2 :=
  HilbertBasis.mk (orthonormal_walshL2.comp e e.injective) <| by
    rw [e.surjective.range_comp, ← walshClosedSpan, walsh_complete]

/-- The unitary operator induced by a permutation of the Walsh indices. -/
private noncomputable def walshPermutation
    (e : Finset LineIndex ≃ Finset LineIndex) : WalshL2 ≃ₗᵢ[ℂ] WalshL2 :=
  walshBasis.repr.trans (reindexedWalshBasis e).repr.symm

private theorem walshPermutation_apply (e : Finset LineIndex ≃ Finset LineIndex)
    (S : Finset LineIndex) :
    walshPermutation e (walshL2 S) = walshL2 (e S) := by
  rw [← walshBasis_apply S, walshPermutation, LinearIsometryEquiv.trans_apply,
    HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  unfold reindexedWalshBasis
  rw [HilbertBasis.coe_mk]
  rfl

private theorem walshPermutation_symm_apply
    (e : Finset LineIndex ≃ Finset LineIndex) (S : Finset LineIndex) :
    (walshPermutation e).symm (walshL2 S) = walshL2 (e.symm S) := by
  apply (walshPermutation e).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, walshPermutation_apply,
    Equiv.apply_symm_apply]

private def translateFinset (x : Operator.Lattice) :
    Finset LineIndex ≃ Finset LineIndex :=
  (lineTranslation (latticeToSite x)).finsetCongr

private def toggleFinset (l : LineIndex) :
    Finset LineIndex ≃ Finset LineIndex where
  toFun S := S ∆ {l}
  invFun S := S ∆ {l}
  left_inv S := by
    ext k
    simp only [Finset.mem_symmDiff, Finset.mem_singleton]
    tauto
  right_inv S := by
    ext k
    simp only [Finset.mem_symmDiff, Finset.mem_singleton]
    tauto

@[simp] private theorem translateFinset_apply (x : Operator.Lattice)
    (S : Finset LineIndex) :
    translateFinset x S =
      Finset.map (lineTranslation (latticeToSite x)).toEmbedding S := by
  rfl

@[simp] private theorem toggleFinset_apply (l : LineIndex) (S : Finset LineIndex) :
    toggleFinset l S = S ∆ {l} := by
  rfl

private theorem translateFinset_neg (x : Operator.Lattice) (S : Finset LineIndex) :
    translateFinset (-x) S = (translateFinset x).symm S := by
  ext l
  rcases l with ⟨i, k⟩
  cases i <;>
    simp [translateFinset, Equiv.finsetCongr_apply, lineTranslation, latticeToSite,
      transverseCoordinate]

private theorem translateFinset_zero (S : Finset LineIndex) :
    translateFinset 0 S = S := by
  ext l
  rcases l with ⟨i, k⟩
  cases i <;>
    simp [translateFinset_apply, lineTranslation, latticeToSite, transverseCoordinate]

private theorem lineTranslation_lattice_add (x y : Operator.Lattice) :
    lineTranslation (latticeToSite (x + y)) =
      (lineTranslation (latticeToSite y)).trans (lineTranslation (latticeToSite x)) := by
  apply Equiv.ext
  intro l
  rcases l with ⟨i, k⟩
  cases i <;>
    simp [lineTranslation, latticeToSite, transverseCoordinate] <;> ring_nf

private theorem translateFinset_add (x y : Operator.Lattice) (S : Finset LineIndex) :
    translateFinset (x + y) S = translateFinset x (translateFinset y S) := by
  calc
    translateFinset (x + y) S =
        ((lineTranslation (latticeToSite y)).trans
          (lineTranslation (latticeToSite x))).finsetCongr S :=
      congrArg (fun e : LineIndex ≃ LineIndex => e.finsetCongr S)
        (lineTranslation_lattice_add x y)
    _ = ((lineTranslation (latticeToSite y)).finsetCongr.trans
          (lineTranslation (latticeToSite x)).finsetCongr) S := by
      rw [Equiv.finsetCongr_trans]
    _ = translateFinset x (translateFinset y S) := rfl

private theorem toggleFinset_symm (l : LineIndex) :
    (toggleFinset l).symm = toggleFinset l := by
  rfl

private theorem walsh_span_dense :
    Dense (Submodule.span ℂ (Set.range walshL2) : Set WalshL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact walsh_complete

private theorem continuousLinearMap_ext_walsh
    (T U : WalshL2 →L[ℂ] WalshL2)
    (h : ∀ S : Finset LineIndex, T (walshL2 S) = U (walshL2 S)) : T = U := by
  apply ContinuousLinearMap.ext_on walsh_span_dense
  rintro _ ⟨S, rfl⟩
  exact h S

/-- The `Fin 2` direction as the corresponding concrete axis. -/
def finAxis (i : Fin 2) : Axis := if i = 0 then .horizontal else .vertical

@[simp] theorem finAxis_zero : finAxis 0 = .horizontal := by simp [finAxis]

@[simp] theorem finAxis_one : finAxis 1 = .vertical := by simp [finAxis]

/-- The line through the origin in direction `i`. -/
def originLine (i : Fin 2) : LineIndex := (finAxis i, 0)

/-- The unitary action of a lattice translation on the environment fiber. -/
noncomputable def environmentShift (x : Operator.Lattice) : WalshL2 →L[ℂ] WalshL2 :=
  walshPermutation (translateFinset x)

/-- Multiplication by the sign of the line through the origin in direction
`i`, realized on the Walsh basis by toggling that line. -/
noncomputable def originSignMultiplier (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  walshPermutation (toggleFinset (originLine i))

@[simp] theorem environmentShift_walshL2 (x : Operator.Lattice)
    (S : Finset LineIndex) :
    environmentShift x (walshL2 S) = walshL2 (translateFinset x S) :=
  by simpa [environmentShift] using walshPermutation_apply (translateFinset x) S

@[simp] theorem originSignMultiplier_walshL2 (i : Fin 2)
    (S : Finset LineIndex) :
    originSignMultiplier i (walshL2 S) = walshL2 (toggleFinset (originLine i) S) :=
  by simpa [originSignMultiplier] using
    walshPermutation_apply (toggleFinset (originLine i)) S

theorem environmentShift_norm_le (x : Operator.Lattice) :
    ‖environmentShift x‖ ≤ 1 :=
  (walshPermutation (translateFinset x)).toLinearIsometry.norm_toContinuousLinearMap_le

theorem originSignMultiplier_norm_le (i : Fin 2) :
    ‖originSignMultiplier i‖ ≤ 1 :=
  (walshPermutation (toggleFinset (originLine i))).toLinearIsometry.norm_toContinuousLinearMap_le

@[simp] theorem environmentShift_zero :
    environmentShift 0 = ContinuousLinearMap.id ℂ WalshL2 := by
  apply continuousLinearMap_ext_walsh
  intro S
  rw [environmentShift_walshL2, translateFinset_zero]
  rfl

theorem environmentShift_add (x y : Operator.Lattice) :
    environmentShift (x + y) = environmentShift x ∘L environmentShift y := by
  apply continuousLinearMap_ext_walsh
  intro S
  simp only [environmentShift_walshL2, ContinuousLinearMap.comp_apply]
  rw [translateFinset_add]

private theorem walshCharacter_translateEnvironment (x : Operator.Lattice)
    (S : Finset LineIndex) (omega : Environment) :
    walshCharacter S (translateEnvironment (latticeToSite x) omega) =
      walshCharacter (translateFinset x S) omega := by
  classical
  simp only [walshCharacter, coordinateCharacter, translateEnvironment,
    translateFinset_apply, Finset.prod_map]
  rfl

/-- On every Walsh monomial, `environmentShift x` is composition with the
concrete environment translation `tau_x`. -/
theorem coeFn_environmentShift_walshL2 (x : Operator.Lattice)
    (S : Finset LineIndex) :
    (environmentShift x (walshL2 S) : Environment → ℂ) =ᵐ[environmentLaw]
      fun omega => walshCharacter S (translateEnvironment (latticeToSite x) omega) := by
  rw [environmentShift_walshL2]
  filter_upwards [coeFn_walshL2 (translateFinset x S)] with omega homega
  rw [homega, walshCharacter_translateEnvironment]

private theorem walshCharacter_toggle (l : LineIndex) (S : Finset LineIndex)
    (omega : Environment) :
    walshCharacter (toggleFinset l S) omega =
      coordinateCharacter l omega * walshCharacter S omega := by
  by_cases hl : l ∈ S
  · rw [coordinate_mul_walshCharacter, if_pos hl]
    congr 1
    ext k
    simp only [toggleFinset_apply, Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_erase]
    by_cases hkl : k = l <;> simp_all
  · rw [coordinate_mul_walshCharacter, if_neg hl]
    congr 1
    ext k
    simp only [toggleFinset_apply, Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    by_cases hkl : k = l <;> simp_all

/-- On every Walsh monomial, `originSignMultiplier i` is multiplication by
the concrete orientation sign at the line through the origin. -/
theorem coeFn_originSignMultiplier_walshL2 (i : Fin 2)
    (S : Finset LineIndex) :
    (originSignMultiplier i (walshL2 S) : Environment → ℂ) =ᵐ[environmentLaw]
      fun omega => coordinateCharacter (originLine i) omega * walshCharacter S omega := by
  rw [originSignMultiplier_walshL2]
  filter_upwards [coeFn_walshL2 (toggleFinset (originLine i) S)] with omega homega
  rw [homega, walshCharacter_toggle]

@[simp] theorem environmentShift_adjoint (x : Operator.Lattice) :
    (environmentShift x)† = environmentShift (-x) := by
  apply continuousLinearMap_ext_walsh
  intro S
  rw [environmentShift, LinearIsometryEquiv.adjoint_eq_symm]
  change (walshPermutation (translateFinset x)).symm (walshL2 S) =
    environmentShift (-x) (walshL2 S)
  rw [walshPermutation_symm_apply, environmentShift_walshL2, translateFinset_neg]

@[simp] theorem originSignMultiplier_adjoint (i : Fin 2) :
    (originSignMultiplier i)† = originSignMultiplier i := by
  apply continuousLinearMap_ext_walsh
  intro S
  rw [originSignMultiplier, LinearIsometryEquiv.adjoint_eq_symm]
  change (walshPermutation (toggleFinset (originLine i))).symm (walshL2 S) =
    walshPermutation (toggleFinset (originLine i)) (walshL2 S)
  rw [walshPermutation_symm_apply, walshPermutation_apply, toggleFinset_symm]

theorem originSignMultiplier_isSelfAdjoint (i : Fin 2) :
    IsSelfAdjoint (originSignMultiplier i) :=
  originSignMultiplier_adjoint i

private theorem lineTranslation_originLine_axis (i : Fin 2) (sign : ℤ) :
    lineTranslation (latticeToSite (sign • Operator.axisVector i)) (originLine i) =
      originLine i := by
  fin_cases i <;>
    simp [lineTranslation, latticeToSite, transverseCoordinate, Operator.axisVector,
      originLine, finAxis]

private theorem translate_toggle_axis (i : Fin 2) (sign : ℤ)
    (S : Finset LineIndex) :
    translateFinset (sign • Operator.axisVector i) (toggleFinset (originLine i) S) =
      toggleFinset (originLine i) (translateFinset (sign • Operator.axisVector i) S) := by
  ext l
  have heq :
      (lineTranslation (latticeToSite (sign • Operator.axisVector i))).symm l =
        originLine i ↔ l = originLine i := by
    rw [Equiv.symm_apply_eq, lineTranslation_originLine_axis]
  simp only [translateFinset_apply, toggleFinset_apply,
    Finset.mem_map_equiv, Finset.mem_symmDiff, Finset.mem_singleton]
  rw [heq]

theorem originSignMultiplier_commute_axis (i : Fin 2) (sign : ℤ)
    :
    originSignMultiplier i ∘L environmentShift (sign • Operator.axisVector i) =
      environmentShift (sign • Operator.axisVector i) ∘L originSignMultiplier i := by
  apply continuousLinearMap_ext_walsh
  intro S
  ·
    simp only [ContinuousLinearMap.comp_apply, environmentShift_walshL2,
      originSignMultiplier_walshL2]
    rw [translate_toggle_axis i sign S]

/-- A unitary environment shift with the Fourier phase from Proposition 2.1. -/
noncomputable def phasedShift (p : Fin 2 → ℝ) (i : Fin 2) : WalshL2 →L[ℂ] WalshL2 :=
  Complex.exp (Complex.I * p i) • environmentShift (Operator.axisVector i)

@[simp] theorem phasedShift_adjoint (p : Fin 2 → ℝ) (i : Fin 2) :
    (phasedShift p i)† =
      Complex.exp (-Complex.I * p i) • environmentShift (-Operator.axisVector i) := by
  rw [phasedShift, map_smulₛₗ, environmentShift_adjoint, ← Complex.exp_conj]
  congr 2
  simp

theorem phasedShift_norm_apply (p : Fin 2 → ℝ) (i : Fin 2) (f : WalshL2) :
    ‖phasedShift p i f‖ = ‖f‖ := by
  rw [phasedShift, ContinuousLinearMap.smul_apply, norm_smul,
    Complex.norm_exp_I_mul_ofReal]
  simp only [one_mul]
  change ‖walshPermutation (translateFinset (Operator.axisVector i)) f‖ = ‖f‖
  exact (walshPermutation (translateFinset (Operator.axisVector i))).norm_map f

/-- One self-adjoint dissipative summand of the fiber symmetric part. -/
noncomputable def fiberSymmetricTerm (p : Fin 2 → ℝ) (i : Fin 2) :
    WalshL2 →L[ℂ] WalshL2 :=
  phasedShift p i + (phasedShift p i)† - (2 : ℂ) • ContinuousLinearMap.id ℂ WalshL2

/-- One skew-adjoint difference entering the fiber antisymmetric part. -/
noncomputable def fiberSkewTerm (p : Fin 2 → ℝ) (i : Fin 2) :
    WalshL2 →L[ℂ] WalshL2 :=
  phasedShift p i - (phasedShift p i)†

theorem fiberSymmetricTerm_isSelfAdjoint (p : Fin 2 → ℝ) (i : Fin 2) :
    IsSelfAdjoint (fiberSymmetricTerm p i) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [fiberSymmetricTerm, map_sub, map_add,
    ContinuousLinearMap.adjoint_adjoint, map_smulₛₗ, map_ofNat,
    ContinuousLinearMap.adjoint_id]
  abel

theorem fiberSymmetricTerm_re_inner (p : Fin 2 → ℝ) (i : Fin 2)
    (f : WalshL2) :
    re ⟪fiberSymmetricTerm p i f, f⟫_ℂ = -‖phasedShift p i f - f‖ ^ 2 := by
  simp only [fiberSymmetricTerm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_add_left, inner_smul_left,
    map_sub, map_add, mul_re, ContinuousLinearMap.adjoint_inner_left, inner_re_symm,
    map_ofNat, inner_self_eq_norm_sq, inner_self_im]
  rw [@norm_sub_sq ℂ WalshL2, phasedShift_norm_apply]
  have hre : re ⟪f, phasedShift p i f⟫_ℂ = re ⟪phasedShift p i f, f⟫_ℂ :=
    inner_re_symm f (phasedShift p i f)
  rw [hre]
  norm_num
  ring

theorem fiberSkewTerm_adjoint (p : Fin 2 → ℝ) (i : Fin 2) :
    (fiberSkewTerm p i)† = -fiberSkewTerm p i := by
  simp only [fiberSkewTerm, map_sub, ContinuousLinearMap.adjoint_adjoint]
  abel

theorem phasedShift_norm_le (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖phasedShift p i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  rw [phasedShift_norm_apply]
  simp

theorem phasedShift_adjoint_norm_le (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖(phasedShift p i)†‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  rw [phasedShift_adjoint, ContinuousLinearMap.smul_apply, norm_smul]
  have hphase : ‖Complex.exp (-Complex.I * p i)‖ = 1 := by
    convert Complex.norm_exp_I_mul_ofReal (-p i) using 1
    push_cast
    ring_nf
  rw [hphase]
  simp only [one_mul]
  have hnorm := (walshPermutation
    (translateFinset (-Operator.axisVector i))).norm_map f
  exact le_of_eq hnorm

theorem fiberSymmetricTerm_norm_le (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖fiberSymmetricTerm p i‖ ≤ 4 := by
  calc
    ‖fiberSymmetricTerm p i‖ ≤
        ‖phasedShift p i‖ + ‖(phasedShift p i)†‖ +
          ‖(2 : ℂ) • ContinuousLinearMap.id ℂ WalshL2‖ := by
      unfold fiberSymmetricTerm
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1 + 1 + 2 := by
      have hV : ‖phasedShift p i‖ ≤ 1 := phasedShift_norm_le p i
      have hVstar : ‖(phasedShift p i)†‖ ≤ 1 := phasedShift_adjoint_norm_le p i
      have hId : ‖(2 : ℂ) • ContinuousLinearMap.id ℂ WalshL2‖ ≤ 2 := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun f => ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul]
        norm_num
      linarith
    _ = 4 := by norm_num

theorem fiberSkewTerm_norm_le (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖fiberSkewTerm p i‖ ≤ 2 := by
  calc
    ‖fiberSkewTerm p i‖ ≤ ‖phasedShift p i‖ + ‖(phasedShift p i)†‖ := by
      exact norm_sub_le _ _
    _ ≤ 1 + 1 := by
      have hV : ‖phasedShift p i‖ ≤ 1 := phasedShift_norm_le p i
      have hVstar : ‖(phasedShift p i)†‖ ≤ 1 := phasedShift_adjoint_norm_le p i
      exact add_le_add hV hVstar
    _ = 2 := by norm_num

private theorem originSignMultiplier_commute_phasedShift (p : Fin 2 → ℝ)
    (i : Fin 2) :
    originSignMultiplier i ∘L phasedShift p i =
      phasedShift p i ∘L originSignMultiplier i := by
  have h := originSignMultiplier_commute_axis i 1
  rw [phasedShift, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  exact congrArg _ (by simpa using h)

private theorem originSignMultiplier_commute_phasedShift_adjoint (p : Fin 2 → ℝ)
    (i : Fin 2) :
    originSignMultiplier i ∘L (phasedShift p i)† =
      (phasedShift p i)† ∘L originSignMultiplier i := by
  have h := originSignMultiplier_commute_axis i (-1)
  rw [phasedShift_adjoint]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  exact congrArg _ (by simpa using h)

private theorem originSignMultiplier_commute_fiberSkewTerm (p : Fin 2 → ℝ)
    (i : Fin 2) :
    originSignMultiplier i ∘L fiberSkewTerm p i =
      fiberSkewTerm p i ∘L originSignMultiplier i := by
  rw [fiberSkewTerm, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    originSignMultiplier_commute_phasedShift,
    originSignMultiplier_commute_phasedShift_adjoint]

private theorem fiberAntisymmetricSummand_adjoint (p : Fin 2 → ℝ) (i : Fin 2) :
    (originSignMultiplier i ∘L fiberSkewTerm p i)† =
      -(originSignMultiplier i ∘L fiberSkewTerm p i) := by
  rw [ContinuousLinearMap.adjoint_comp, originSignMultiplier_adjoint,
    fiberSkewTerm_adjoint]
  ext f
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  rw [← ContinuousLinearMap.comp_apply, ← originSignMultiplier_commute_fiberSkewTerm,
    ContinuousLinearMap.comp_apply]

/-- The symmetric part of the concrete Fourier fiber. -/
noncomputable def concreteFiberS (p : Fin 2 → ℝ) : WalshL2 →L[ℂ] WalshL2 :=
  (2 : ℂ)⁻¹ • ∑ i, fiberSymmetricTerm p i

/-- The antisymmetric part of the concrete Fourier fiber. -/
noncomputable def concreteFiberA (p : Fin 2 → ℝ) : WalshL2 →L[ℂ] WalshL2 :=
  (2 : ℂ)⁻¹ • ∑ i, originSignMultiplier i ∘L fiberSkewTerm p i

theorem concreteFiberS_formula (p : Fin 2 → ℝ) :
    concreteFiberS p = (2 : ℂ)⁻¹ • ∑ i,
      (Complex.exp (Complex.I * p i) • environmentShift (Operator.axisVector i) +
       Complex.exp (-Complex.I * p i) • environmentShift (-Operator.axisVector i) -
       (2 : ℂ) • ContinuousLinearMap.id ℂ WalshL2) := by
  unfold concreteFiberS
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [fiberSymmetricTerm, phasedShift_adjoint, phasedShift]

theorem concreteFiberA_formula (p : Fin 2 → ℝ) :
    concreteFiberA p = (2 : ℂ)⁻¹ • ∑ i, originSignMultiplier i ∘L
      (Complex.exp (Complex.I * p i) • environmentShift (Operator.axisVector i) -
       Complex.exp (-Complex.I * p i) • environmentShift (-Operator.axisVector i)) := by
  unfold concreteFiberA
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [fiberSkewTerm, phasedShift_adjoint, phasedShift]

theorem concreteFiberS_selfAdjoint (p : Fin 2 → ℝ) :
    IsSelfAdjoint (concreteFiberS p) := by
  have hsum : IsSelfAdjoint (∑ i, fiberSymmetricTerm p i) :=
    isSelfAdjoint_sum Finset.univ fun i _ => fiberSymmetricTerm_isSelfAdjoint p i
  have hhalf : IsSelfAdjoint ((2 : ℂ)⁻¹) := by
    norm_num [isSelfAdjoint_iff]
  exact hhalf.smul hsum

theorem concreteFiberS_nonpositive (p : Fin 2 → ℝ) (f : WalshL2) :
    re ⟪concreteFiberS p f, f⟫_ℂ ≤ 0 := by
  have hform :
      re ⟪concreteFiberS p f, f⟫_ℂ =
        (2 : ℝ)⁻¹ * ∑ i, re ⟪fiberSymmetricTerm p i f, f⟫_ℂ := by
    rw [concreteFiberS, Fin.sum_univ_two]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      inner_smul_left, inner_add_left, map_add, mul_re]
    norm_num
  rw [hform]
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  exact Finset.sum_nonpos fun i _ => by
    rw [fiberSymmetricTerm_re_inner]
    exact neg_nonpos.mpr (sq_nonneg _)

theorem concreteFiberS_norm_le (p : Fin 2 → ℝ) : ‖concreteFiberS p‖ ≤ 4 := by
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖concreteFiberS p‖ ≤
        ‖(2 : ℂ)⁻¹‖ * ‖∑ i, fiberSymmetricTerm p i‖ := by
      unfold concreteFiberS
      exact ContinuousLinearMap.opNorm_smul_le ((2 : ℂ)⁻¹)
        (∑ i, fiberSymmetricTerm p i)
    _ = (2 : ℝ)⁻¹ * ‖∑ i, fiberSymmetricTerm p i‖ := by rw [hhalf]
    _ ≤ (2 : ℝ)⁻¹ * ∑ i, ‖fiberSymmetricTerm p i‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ * ∑ _i : Fin 2, 4 := by
      gcongr with i
      exact fiberSymmetricTerm_norm_le p i
    _ = 4 := by norm_num [Fin.sum_univ_two]

theorem concreteFiberA_skewAdjoint (p : Fin 2 → ℝ) :
    (concreteFiberA p)† = -concreteFiberA p := by
  unfold concreteFiberA
  rw [map_smulₛₗ, map_sum]
  have hhalf : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [hhalf]
  simp_rw [fiberAntisymmetricSummand_adjoint]
  simp only [Finset.sum_neg_distrib, smul_neg]

private theorem fiberAntisymmetricSummand_norm_le (p : Fin 2 → ℝ) (i : Fin 2) :
    ‖originSignMultiplier i ∘L fiberSkewTerm p i‖ ≤ 2 := by
  calc
    ‖originSignMultiplier i ∘L fiberSkewTerm p i‖ ≤
        ‖originSignMultiplier i‖ * ‖fiberSkewTerm p i‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 2 := by
      exact mul_le_mul (originSignMultiplier_norm_le i) (fiberSkewTerm_norm_le p i)
        (norm_nonneg _) zero_le_one
    _ = 2 := by norm_num

theorem concreteFiberA_norm_le (p : Fin 2 → ℝ) : ‖concreteFiberA p‖ ≤ 2 := by
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  calc
    ‖concreteFiberA p‖ ≤
        ‖(2 : ℂ)⁻¹‖ * ‖∑ i, originSignMultiplier i ∘L fiberSkewTerm p i‖ := by
      unfold concreteFiberA
      exact ContinuousLinearMap.opNorm_smul_le ((2 : ℂ)⁻¹)
        (∑ i, originSignMultiplier i ∘L fiberSkewTerm p i)
    _ = (2 : ℝ)⁻¹ * ‖∑ i, originSignMultiplier i ∘L fiberSkewTerm p i‖ := by
      rw [hhalf]
    _ ≤ (2 : ℝ)⁻¹ * ∑ i, ‖originSignMultiplier i ∘L fiberSkewTerm p i‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2 : ℝ)⁻¹ * ∑ _i : Fin 2, 2 := by
      gcongr with i
      exact fiberAntisymmetricSummand_norm_le p i
    _ = 2 := by norm_num [Fin.sum_univ_two]

/-- The concrete fair-coin instance of the operator layer's fiber interface. -/
noncomputable def concreteFiberEnvironment : Operator.FiberEnvironment WalshL2 where
  shift := environmentShift
  omega := originSignMultiplier
  fiberS := concreteFiberS
  fiberA := concreteFiberA
  fiberS_formula := concreteFiberS_formula
  fiberA_formula := concreteFiberA_formula
  fiberS_selfAdjoint_spec := concreteFiberS_selfAdjoint
  fiberS_nonpositive_spec := concreteFiberS_nonpositive
  fiberS_norm_le_spec := concreteFiberS_norm_le
  fiberA_skewAdjoint_spec := concreteFiberA_skewAdjoint
  fiberA_norm_le_spec := concreteFiberA_norm_le

end Manhattan
