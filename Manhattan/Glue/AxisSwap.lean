import Manhattan.Model.LowDegree

/-!
# Exchange of the two coordinate axes

The Manhattan environment law and the concrete Fourier fibers are invariant
under exchanging horizontal and vertical lines. This file realizes that
symmetry as a unitary permutation of the complete Finset-indexed Walsh basis
and proves its intertwining with the concrete symmetric and skew operators.

Paper: `manuscript.tex:1156`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike
open scoped BigOperators ComplexConjugate InnerProduct

namespace Manhattan.Glue

/-- Exchange horizontal and vertical axes. -/
def axisSwap : Axis → Axis
  | .horizontal => .vertical
  | .vertical => .horizontal

@[simp] theorem axisSwap_horizontal : axisSwap .horizontal = .vertical := rfl

@[simp] theorem axisSwap_vertical : axisSwap .vertical = .horizontal := rfl

@[simp] theorem axisSwap_involutive (i : Axis) : axisSwap (axisSwap i) = i := by
  cases i <;> rfl

/-- Exchange the two elements of `Fin 2`. -/
def axisSwapFin (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem axisSwapFin_zero : axisSwapFin 0 = 1 := by simp [axisSwapFin]

@[simp] theorem axisSwapFin_one : axisSwapFin 1 = 0 := by simp [axisSwapFin]

@[simp] theorem axisSwapFin_involutive (i : Fin 2) : axisSwapFin (axisSwapFin i) = i := by
  fin_cases i <;> simp

@[simp] theorem finAxis_axisSwapFin (i : Fin 2) :
    Manhattan.finAxis (axisSwapFin i) = axisSwap (Manhattan.finAxis i) := by
  fin_cases i <;> simp

/-- Exchange the two coordinates of a lattice vector. -/
def axisSwapLattice (x : Manhattan.Operator.Lattice) : Manhattan.Operator.Lattice :=
  fun i => x (axisSwapFin i)

@[simp] theorem axisSwapLattice_apply (x : Manhattan.Operator.Lattice) (i : Fin 2) :
    axisSwapLattice x i = x (axisSwapFin i) := rfl

@[simp] theorem axisSwapLattice_involutive (x : Manhattan.Operator.Lattice) :
    axisSwapLattice (axisSwapLattice x) = x := by
  funext i
  simp

@[simp] theorem axisSwapLattice_neg (x : Manhattan.Operator.Lattice) :
    axisSwapLattice (-x) = -axisSwapLattice x := by
  funext i
  rfl

@[simp] theorem axisSwapLattice_axisVector (i : Fin 2) :
    axisSwapLattice (Manhattan.Operator.axisVector i) =
      Manhattan.Operator.axisVector (axisSwapFin i) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [axisSwapLattice, axisSwapFin, Manhattan.Operator.axisVector]

/-- Exchange the two coordinates of a frequency vector. -/
def axisSwapFrequency (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => p (axisSwapFin i)

@[simp] theorem axisSwapFrequency_apply (p : Fin 2 → ℝ) (i : Fin 2) :
    axisSwapFrequency p i = p (axisSwapFin i) := rfl

@[simp] theorem axisSwapFrequency_zero (p : Fin 2 → ℝ) :
    axisSwapFrequency p 0 = p 1 := by simp

@[simp] theorem axisSwapFrequency_one (p : Fin 2 → ℝ) :
    axisSwapFrequency p 1 = p 0 := by simp

@[simp] theorem axisSwapFrequency_involutive (p : Fin 2 → ℝ) :
    axisSwapFrequency (axisSwapFrequency p) = p := by
  funext i
  simp

/-- Exchange the axis coordinate of a line index. -/
def axisSwapLineEquiv : Manhattan.LineIndex ≃ Manhattan.LineIndex where
  toFun l := (axisSwap l.1, l.2)
  invFun l := (axisSwap l.1, l.2)
  left_inv l := by rcases l with ⟨i, k⟩; cases i <;> rfl
  right_inv l := by rcases l with ⟨i, k⟩; cases i <;> rfl

/-- The induced permutation of finite Walsh indices. -/
def axisSwapWalshIndexEquiv :
    Finset Manhattan.LineIndex ≃ Finset Manhattan.LineIndex :=
  axisSwapLineEquiv.finsetCongr

@[simp] theorem axisSwapWalshIndexEquiv_empty :
    axisSwapWalshIndexEquiv ∅ = ∅ := by
  rfl

private theorem axisSwapLine_translate (x : Manhattan.Operator.Lattice)
    (l : Manhattan.LineIndex) :
    axisSwapLineEquiv
        (Manhattan.lineTranslation (Manhattan.latticeToSite x) l) =
      Manhattan.lineTranslation (Manhattan.latticeToSite (axisSwapLattice x))
        (axisSwapLineEquiv l) := by
  rcases l with ⟨i, k⟩
  cases i <;> simp [axisSwapLineEquiv, Manhattan.lineTranslation,
    Manhattan.latticeToSite, Manhattan.transverseCoordinate, axisSwapLattice]

private theorem axisSwapLine_translate_symm (x : Manhattan.Operator.Lattice)
    (l : Manhattan.LineIndex) :
    (Manhattan.lineTranslation (Manhattan.latticeToSite x)).symm
        (axisSwapLineEquiv.symm l) =
      axisSwapLineEquiv.symm
        ((Manhattan.lineTranslation
          (Manhattan.latticeToSite (axisSwapLattice x))).symm l) := by
  rcases l with ⟨i, k⟩
  cases i <;> simp [axisSwapLineEquiv, Manhattan.lineTranslation,
    Manhattan.latticeToSite, Manhattan.transverseCoordinate, axisSwapLattice]

theorem axisSwapWalshIndex_translate (x : Manhattan.Operator.Lattice)
    (S : Finset Manhattan.LineIndex) :
    axisSwapWalshIndexEquiv (Manhattan.translateWalshIndex x S) =
      Manhattan.translateWalshIndex (axisSwapLattice x)
        (axisSwapWalshIndexEquiv S) := by
  classical
  ext l
  simp only [axisSwapWalshIndexEquiv, Equiv.finsetCongr_apply,
    Manhattan.translateWalshIndex, Finset.mem_map_equiv]
  rw [axisSwapLine_translate_symm]

@[simp] theorem axisSwap_originLine (i : Fin 2) :
    axisSwapLineEquiv (Manhattan.originLine i) =
      Manhattan.originLine (axisSwapFin i) := by
  fin_cases i <;> simp [axisSwapLineEquiv, Manhattan.originLine]

theorem axisSwapWalshIndex_toggle (i : Fin 2)
    (S : Finset Manhattan.LineIndex) :
    axisSwapWalshIndexEquiv (Manhattan.toggleOriginWalshIndex i S) =
      Manhattan.toggleOriginWalshIndex (axisSwapFin i)
        (axisSwapWalshIndexEquiv S) := by
  classical
  ext l
  simp only [axisSwapWalshIndexEquiv, Equiv.finsetCongr_apply,
    Manhattan.toggleOriginWalshIndex, Finset.mem_map_equiv,
    Finset.mem_symmDiff, Finset.mem_singleton]
  rw [axisSwapLineEquiv.symm_apply_eq]
  simp only [axisSwap_originLine]

private noncomputable def axisSwapWalshBasis :
    HilbertBasis (Finset Manhattan.LineIndex) ℂ Manhattan.WalshL2 :=
  HilbertBasis.mk
    (Manhattan.orthonormal_walshL2.comp axisSwapWalshIndexEquiv
      axisSwapWalshIndexEquiv.injective) <| by
      rw [axisSwapWalshIndexEquiv.surjective.range_comp,
        ← Manhattan.walshClosedSpan, Manhattan.walsh_complete]

/-- The row/column exchange as a unitary operator on the concrete Walsh fiber. -/
noncomputable def axisSwapUnitary : Manhattan.WalshL2 ≃ₗᵢ[ℂ] Manhattan.WalshL2 :=
  Manhattan.walshBasis.repr.trans axisSwapWalshBasis.repr.symm

@[simp] theorem axisSwapUnitary_walshL2 (S : Finset Manhattan.LineIndex) :
    axisSwapUnitary (Manhattan.walshL2 S) =
      Manhattan.walshL2 (axisSwapWalshIndexEquiv S) := by
  rw [← Manhattan.walshBasis_apply S, axisSwapUnitary,
    LinearIsometryEquiv.trans_apply, HilbertBasis.repr_self,
    HilbertBasis.repr_symm_single]
  unfold axisSwapWalshBasis
  rw [HilbertBasis.coe_mk]
  rfl

@[simp] theorem axisSwapUnitary_empty :
    axisSwapUnitary (Manhattan.walshL2 ∅) = Manhattan.walshL2 ∅ := by
  rw [axisSwapUnitary_walshL2, axisSwapWalshIndexEquiv_empty]

private theorem walsh_span_dense :
    Dense (Submodule.span ℂ
      (Set.range Manhattan.walshL2) : Set Manhattan.WalshL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact Manhattan.walsh_complete

private theorem continuousLinearMap_ext_walsh
    (T U : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2)
    (h : ∀ S : Finset Manhattan.LineIndex,
      T (Manhattan.walshL2 S) = U (Manhattan.walshL2 S)) : T = U := by
  apply ContinuousLinearMap.ext_on walsh_span_dense
  rintro _ ⟨S, rfl⟩
  exact h S

/-- The continuous linear operator underlying `axisSwapUnitary`. -/
noncomputable def axisSwapOperator : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 :=
  axisSwapUnitary.toLinearIsometry.toContinuousLinearMap

@[simp] theorem axisSwapOperator_apply (f : Manhattan.WalshL2) :
    axisSwapOperator f = axisSwapUnitary f := rfl

/-- Row/column exchange intertwines all environment translations. -/
theorem axisSwap_environmentShift (x : Manhattan.Operator.Lattice) :
    axisSwapOperator ∘L Manhattan.environmentShift x =
      Manhattan.environmentShift (axisSwapLattice x) ∘L axisSwapOperator := by
  apply continuousLinearMap_ext_walsh
  intro S
  simp only [ContinuousLinearMap.comp_apply, axisSwapOperator_apply,
    Manhattan.environmentShift_walshL2_public, axisSwapUnitary_walshL2]
  rw [axisSwapWalshIndex_translate]

/-- Row/column exchange intertwines the two origin-sign multipliers. -/
theorem axisSwap_originSignMultiplier (i : Fin 2) :
    axisSwapOperator ∘L Manhattan.originSignMultiplier i =
      Manhattan.originSignMultiplier (axisSwapFin i) ∘L axisSwapOperator := by
  apply continuousLinearMap_ext_walsh
  intro S
  simp only [ContinuousLinearMap.comp_apply, axisSwapOperator_apply,
    Manhattan.originSignMultiplier_walshL2_public, axisSwapUnitary_walshL2]
  rw [axisSwapWalshIndex_toggle]

theorem axisSwap_originSignMultiplier_apply (i : Fin 2) (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.originSignMultiplier i f) =
      Manhattan.originSignMultiplier (axisSwapFin i) (axisSwapUnitary f) := by
  have h := congrArg (fun T : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 => T f)
    (axisSwap_originSignMultiplier i)
  simpa only [ContinuousLinearMap.comp_apply, axisSwapOperator_apply] using h

theorem axisSwap_phasedShift (p : Fin 2 → ℝ) (i : Fin 2)
    (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.phasedShift p i f) =
      Manhattan.phasedShift (axisSwapFrequency p) (axisSwapFin i)
        (axisSwapUnitary f) := by
  rw [Manhattan.phasedShift]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  have hshift := congrArg
    (fun T : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 => T f)
    (axisSwap_environmentShift (Manhattan.Operator.axisVector i))
  simp only [ContinuousLinearMap.comp_apply, axisSwapOperator_apply,
    axisSwapLattice_axisVector] at hshift
  rw [hshift]
  congr 1
  simp

theorem axisSwap_phasedShift_adjoint (p : Fin 2 → ℝ) (i : Fin 2)
    (f : Manhattan.WalshL2) :
    axisSwapUnitary (((Manhattan.phasedShift p i)†) f) =
      ((Manhattan.phasedShift (axisSwapFrequency p) (axisSwapFin i))†)
        (axisSwapUnitary f) := by
  rw [Manhattan.phasedShift_adjoint, Manhattan.phasedShift_adjoint]
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  have hshift := congrArg
    (fun T : Manhattan.WalshL2 →L[ℂ] Manhattan.WalshL2 => T f)
    (axisSwap_environmentShift (-Manhattan.Operator.axisVector i))
  simp only [ContinuousLinearMap.comp_apply, axisSwapOperator_apply,
    axisSwapLattice_neg, axisSwapLattice_axisVector] at hshift
  rw [hshift]
  congr 1
  simp

theorem axisSwap_fiberSymmetricTerm (p : Fin 2 → ℝ) (i : Fin 2)
    (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.fiberSymmetricTerm p i f) =
      Manhattan.fiberSymmetricTerm (axisSwapFrequency p) (axisSwapFin i)
        (axisSwapUnitary f) := by
  simp only [Manhattan.fiberSymmetricTerm, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_add, map_smul,
    axisSwap_phasedShift, axisSwap_phasedShift_adjoint]

theorem axisSwap_fiberSkewTerm (p : Fin 2 → ℝ) (i : Fin 2)
    (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.fiberSkewTerm p i f) =
      Manhattan.fiberSkewTerm (axisSwapFrequency p) (axisSwapFin i)
        (axisSwapUnitary f) := by
  simp only [Manhattan.fiberSkewTerm, ContinuousLinearMap.sub_apply, map_sub,
    axisSwap_phasedShift, axisSwap_phasedShift_adjoint]

/-- The axis-swap unitary intertwines the concrete symmetric fibers. -/
theorem axisSwap_concreteFiberS (p : Fin 2 → ℝ) (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.concreteFiberS p f) =
      Manhattan.concreteFiberS (axisSwapFrequency p) (axisSwapUnitary f) := by
  unfold Manhattan.concreteFiberS
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    map_smul, map_add, Fin.sum_univ_two, axisSwap_fiberSymmetricTerm,
    axisSwapFin_zero, axisSwapFin_one]
  congr 1
  exact add_comm _ _

/-- The axis-swap unitary intertwines the concrete skew fibers. -/
theorem axisSwap_concreteFiberA (p : Fin 2 → ℝ) (f : Manhattan.WalshL2) :
    axisSwapUnitary (Manhattan.concreteFiberA p f) =
      Manhattan.concreteFiberA (axisSwapFrequency p) (axisSwapUnitary f) := by
  unfold Manhattan.concreteFiberA
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add,
    Fin.sum_univ_two, axisSwap_originSignMultiplier_apply,
    axisSwap_fiberSkewTerm, axisSwapFin_zero, axisSwapFin_one]
  congr 1
  exact add_comm _ _

theorem axisSwap_H (lambda : ℝ) (p : Fin 2 → ℝ) (f : Manhattan.WalshL2) :
    axisSwapUnitary
        ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).H lambda f) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (axisSwapFrequency p)).H lambda (axisSwapUnitary f) := by
  simp only [Manhattan.Operator.DissipativeSkewPair.H,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_smul]
  exact congrArg (fun x => (lambda : ℂ) • axisSwapUnitary f - x)
    (axisSwap_concreteFiberS p f)

theorem axisSwap_hEnergy (lambda : ℝ) (p : Fin 2 → ℝ)
    (f : Manhattan.WalshL2) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (axisSwapFrequency p)).hEnergy lambda (axisSwapUnitary f) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda f := by
  rw [Manhattan.Operator.DissipativeSkewPair.hEnergy]
  rw [← axisSwap_H]
  exact congrArg re (axisSwapUnitary.inner_map_map _ _)

theorem axisSwap_hEquiv_symm {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (f : Manhattan.WalshL2) :
    ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (axisSwapFrequency p)).hEquiv hlambda).symm (axisSwapUnitary f) =
      axisSwapUnitary
        (((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEquiv
          hlambda).symm f) := by
  let P := Manhattan.concreteFiberEnvironment.dissipativeSkewPair p
  let P' := Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    (axisSwapFrequency p)
  apply (P'.H_bijective hlambda).1
  rw [P'.H_apply_inverse]
  rw [← axisSwap_H, P.H_apply_inverse]

theorem axisSwap_hMinusEnergy {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (f : Manhattan.WalshL2) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
        (axisSwapFrequency p)).hMinusEnergy hlambda (axisSwapUnitary f) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda f := by
  rw [Manhattan.Operator.DissipativeSkewPair.hMinusEnergy,
    axisSwap_hEquiv_symm]
  exact congrArg re (axisSwapUnitary.inner_map_map _ _)

/-- The complete variational competitor objective is invariant under axis swap. -/
theorem axisSwap_competitorObjective {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (g : Manhattan.WalshL2) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
          (axisSwapFrequency p)).hEnergy lambda (axisSwapUnitary g) +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
          (axisSwapFrequency p)).hMinusEnergy hlambda
            (Manhattan.walshL2 ∅ -
              Manhattan.concreteFiberA (axisSwapFrequency p) (axisSwapUnitary g)) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g) := by
  rw [axisSwap_hEnergy]
  rw [← axisSwap_hMinusEnergy hlambda p
    (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)]
  congr 2
  rw [map_sub, axisSwapUnitary_empty, axisSwap_concreteFiberA]

@[simp] theorem axisSwap_maxFrequency (p : Fin 2 → ℝ) :
    Manhattan.Operator.maxFrequency (axisSwapFrequency p) =
      Manhattan.Operator.maxFrequency p := by
  simp [Manhattan.Operator.maxFrequency, max_comm]

@[simp] theorem axisSwap_theta (p : Fin 2 → ℝ) :
    Manhattan.Operator.theta (axisSwapFrequency p) = Manhattan.Operator.theta p := by
  simp [Manhattan.Operator.theta, Fin.sum_univ_two, add_comm]

@[simp] theorem axisSwap_frequencyLogScale (r0 lambda : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.Operator.frequencyLogScale r0 lambda (axisSwapFrequency p) =
      Manhattan.Operator.frequencyLogScale r0 lambda p := by
  simp [Manhattan.Operator.frequencyLogScale]

@[simp] theorem axisSwap_driftlessMajorant (lambda : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.Operator.driftlessMajorant lambda (axisSwapFrequency p) =
      Manhattan.Operator.driftlessMajorant lambda p := by
  simp [Manhattan.Operator.driftlessMajorant]

@[simp] theorem axisSwap_correctedMajorant (r0 lambda : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.Operator.correctedMajorant r0 lambda (axisSwapFrequency p) =
      Manhattan.Operator.correctedMajorant r0 lambda p := by
  simp [Manhattan.Operator.correctedMajorant]

@[simp] theorem axisSwap_frequencyMajorant (r0 lambda : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.Operator.frequencyMajorant r0 lambda (axisSwapFrequency p) =
      Manhattan.Operator.frequencyMajorant r0 lambda p := by
  simp [Manhattan.Operator.frequencyMajorant]

/-- Any corrected competitor for the swapped frequency transports back with
the same objective and the same scalar majorant. -/
theorem correctedCompetitor_of_axisSwap {r0 C lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ)
    (h : ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
            (axisSwapFrequency p)).hEnergy lambda g +
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
            (axisSwapFrequency p)).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ -
                Manhattan.concreteFiberA (axisSwapFrequency p) g) ≤
        C * Manhattan.Operator.correctedMajorant r0 lambda
          (axisSwapFrequency p)) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g +
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g) ≤
        C * Manhattan.Operator.correctedMajorant r0 lambda p := by
  obtain ⟨g, hg⟩ := h
  refine ⟨axisSwapUnitary.symm g, ?_⟩
  rw [← axisSwap_competitorObjective hlambda p (axisSwapUnitary.symm g)]
  simpa using hg

end Manhattan.Glue
