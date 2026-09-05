import Manhattan.Glue.EnergyAssembly
import Manhattan.Walsh.LowDegreeSectors

/-!
# Walsh degree sectors of the corrected competitor residual

The paper evaluates the variational objective (20) at `g=(f+k)/b` with
`f` of Walsh degree one and `k` of Walsh degree three, and reads the answer
off the four-sector quadratic form `E_p(f,k)` of (22).  The four sectors are
`⟨f,H₁f⟩`, `⟨k,H₃k⟩`, the degree-two residual `D₁f-D₂^*k`, and the
degree-four residual `D₃k`.

This file supplies the missing structural step: the residual
`b·1-A_p(f+k)` really is supported in Walsh degrees two and four once the
degree-zero component cancels, so the objective is dominated by a universal
multiple of `E_p(f,k)`.  Everything here is unconditional.

Paper: `manuscript.tex:762-790`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

local instance dischargePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

section Sectors

/-- The Walsh family restricted to an arbitrary index predicate. -/
def walshSectorFamily (P : Finset LineIndex → Prop)
    (S : {S : Finset LineIndex // P S}) : WalshL2 := Manhattan.walshL2 S.1

theorem orthonormal_walshSectorFamily (P : Finset LineIndex → Prop) :
    Orthonormal ℂ (walshSectorFamily P) :=
  Manhattan.orthonormal_walshL2.comp Subtype.val Subtype.val_injective

/-- Synthesis on an arbitrary Walsh sector. -/
def walshSectorSynthesis (P : Finset LineIndex → Prop) :
    ℓ²({S : Finset LineIndex // P S}, ℂ) →ₗᵢ[ℂ] WalshL2 :=
  (orthonormal_walshSectorFamily P).orthogonalFamily.linearIsometry

@[simp] theorem walshSectorSynthesis_single (P : Finset LineIndex → Prop)
    (S : {S : Finset LineIndex // P S}) (a : ℂ) :
    walshSectorSynthesis P (lp.single 2 S a) = a • Manhattan.walshL2 S.1 := by
  rw [walshSectorSynthesis, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- The orthogonal component of `x` in the Walsh sector `P`. -/
def walshSectorComponent (P : Finset LineIndex → Prop) (x : WalshL2) : WalshL2 :=
  walshSectorSynthesis P (Manhattan.walshSectorAnalysis P x)

/-- Coefficients of a sector component: the sector's own coefficients are
kept and all others are discarded. -/
theorem inner_walshL2_walshSectorComponent (P : Finset LineIndex → Prop)
    (x : WalshL2) (U : Finset LineIndex) :
    inner ℂ (Manhattan.walshL2 U) (walshSectorComponent P x) =
      if P U then inner ℂ (Manhattan.walshL2 U) x else 0 := by
  classical
  by_cases hU : P U
  · have hone : walshSectorSynthesis P (lp.single 2 (⟨U, hU⟩ :
        {S : Finset LineIndex // P S}) (1 : ℂ)) = Manhattan.walshL2 U := by
      rw [walshSectorSynthesis_single, one_smul]
    rw [walshSectorComponent, ← hone, (walshSectorSynthesis P).inner_map_map,
      lp.inner_single_left, Manhattan.walshSectorAnalysis_apply, if_pos hU]
    simp
  · rw [if_neg hU, walshSectorComponent]
    have hs : HasSum (fun T : {S : Finset LineIndex // P S} =>
        Manhattan.walshSectorAnalysis P x T • Manhattan.walshL2 T.1)
        (walshSectorSynthesis P (Manhattan.walshSectorAnalysis P x)) := by
      simpa only [walshSectorSynthesis, walshSectorFamily,
        LinearIsometry.toSpanSingleton_apply] using
        (orthonormal_walshSectorFamily P).orthogonalFamily.hasSum_linearIsometry
          (Manhattan.walshSectorAnalysis P x)
    have hm := hs.mapL (innerSL ℂ (Manhattan.walshL2 U))
    have hterm : ∀ T : {S : Finset LineIndex // P S},
        (innerSL ℂ (Manhattan.walshL2 U))
            (Manhattan.walshSectorAnalysis P x T • Manhattan.walshL2 T.1) = 0 := by
      intro T
      simp only [innerSL_apply_apply, inner_smul_right, Manhattan.inner_walshL2]
      rw [if_neg (fun hUT : U = T.1 => hU (by rw [hUT]; exact T.2))]
      simp
    refine hm.unique ?_
    rw [funext hterm]
    exact hasSum_zero

end Sectors

section Coefficients

/-- Two Walsh-space vectors with the same Walsh coefficients agree. -/
theorem walshL2_ext {x y : WalshL2}
    (h : ∀ S : Finset LineIndex,
      inner ℂ (Manhattan.walshL2 S) x = inner ℂ (Manhattan.walshL2 S) y) :
    x = y := by
  apply Manhattan.walshBasis.repr.injective
  apply lp.ext
  funext S
  rw [Manhattan.walshBasis.repr_apply_apply, Manhattan.walshBasis.repr_apply_apply,
    Manhattan.walshBasis_apply, h]

/-- The Walsh coefficient of a finite synthesis is the finitely supported
coefficient itself. -/
theorem inner_walshL2_walshSynthesis (U : Finset LineIndex)
    (c : Manhattan.WalshCoefficient) :
    inner ℂ (Manhattan.walshL2 U) (Manhattan.walshSynthesis c) = c U := by
  classical
  have hU : Manhattan.walshL2 U = Manhattan.walshSynthesis (Finsupp.single U 1) := by
    simp
  rw [hU, Manhattan.inner_walshSynthesis, Manhattan.walshCoefficientInner,
    Finsupp.sum_single_index] <;> simp

/-- Pairing a finite synthesis on the left against an arbitrary vector. -/
theorem inner_walshSynthesis_left (c : Manhattan.WalshCoefficient) (x : WalshL2) :
    inner ℂ (Manhattan.walshSynthesis c) x =
      c.sum fun S a => conj a * inner ℂ (Manhattan.walshL2 S) x := by
  classical
  rw [Manhattan.walshSynthesis, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  apply Finsupp.sum_congr
  intro S _
  simp only [smul_eq_mul]

/-- A Walsh character outside degree `n` is orthogonal to every vector of
Walsh degree `n`. -/
theorem inner_walshL2_eq_zero_of_mem_walshDegree {n : ℕ} {x : WalshL2}
    (hx : x ∈ Manhattan.walshDegree n) {S : Finset LineIndex} (hS : S.card ≠ n) :
    inner ℂ (Manhattan.walshL2 S) x = 0 := by
  classical
  have hspan :
      Submodule.span ℂ {f | ∃ T : Finset LineIndex, T.card = n ∧ f = Manhattan.walshL2 T} ≤
        LinearMap.ker (innerSL ℂ (Manhattan.walshL2 S) : WalshL2 →L[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨T, hT, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker,
      innerSL_apply_apply, Manhattan.inner_walshL2]
    rw [if_neg (fun hST : S = T => hS (by rw [hST]; exact hT))]
  have hclosed : IsClosed
      ((LinearMap.ker (innerSL ℂ (Manhattan.walshL2 S) : WalshL2 →L[ℂ] ℂ)) : Set WalshL2) :=
    ContinuousLinearMap.isClosed_ker (innerSL ℂ (Manhattan.walshL2 S))
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hx

/-- A homogeneous finite coefficient of degree `m` is orthogonal to every
vector of Walsh degree `n ≠ m`. -/
theorem inner_walshSynthesis_eq_zero_of_mem_walshDegree {m n : ℕ}
    {c : Manhattan.WalshCoefficient} (hc : Manhattan.IsWalshDegree m c)
    {x : WalshL2} (hx : x ∈ Manhattan.walshDegree n) (hmn : m ≠ n) :
    inner ℂ (Manhattan.walshSynthesis c) x = 0 := by
  classical
  rw [inner_walshSynthesis_left, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [inner_walshL2_eq_zero_of_mem_walshDegree hx (by rw [hc S hS]; exact hmn), mul_zero]

end Coefficients

section SkewSupport

/-- Lemma 5.1's structural content: the concrete skew fiber shifts Walsh
degree by exactly one, so a Walsh character whose degree is neither `n-1`
nor `n+1` is orthogonal to `A_p x` for every `x` of degree `n`. -/
theorem inner_walshL2_concreteFiberA_eq_zero {n : ℕ} {x : WalshL2}
    (hx : x ∈ Manhattan.walshDegree n) (p : Fin 2 → ℝ) {U : Finset LineIndex}
    (hup : U.card + 1 ≠ n) (hdown : U.card - 1 ≠ n) :
    inner ℂ (Manhattan.walshL2 U) (Manhattan.concreteFiberA p x) = 0 := by
  rw [← (Manhattan.concreteFiberA p).adjoint_inner_left,
    Manhattan.concreteFiberA_skewAdjoint, ContinuousLinearMap.neg_apply,
    Manhattan.concreteFiberA_walshL2_eq_D_sub_DStar, inner_neg_left,
    inner_sub_left,
    inner_walshSynthesis_eq_zero_of_mem_walshDegree
      (Manhattan.isWalshDegree_fiberDRaisingSpatialCoefficient p U rfl) hx hup,
    inner_walshSynthesis_eq_zero_of_mem_walshDegree
      (Manhattan.isWalshDegree_fiberDStarLoweringSpatialCoefficient p U rfl) hx
      hdown]
  simp

/-- The unnormalized residual of a degree-one plus degree-three competitor,
as in (20) and (24). -/
def unnormalizedResidual (p : Fin 2 → ℝ) (b : ℝ) (f k : WalshL2) : WalshL2 :=
  (b : ℂ) • Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p (f + k)

/-- After the exact degree-zero cancellation of (24), the residual really is
the sum of its degree-two and degree-four sectors. -/
theorem unnormalizedResidual_eq_sector_sum (p : Fin 2 → ℝ) (b : ℝ)
    {f k : WalshL2} (hf : f ∈ Manhattan.walshDegree 1)
    (hk : k ∈ Manhattan.walshDegree 3)
    (hcancel : inner ℂ (Manhattan.walshL2 ∅) (unnormalizedResidual p b f k) = 0) :
    unnormalizedResidual p b f k =
      walshSectorComponent (fun S => S.card = 2) (unnormalizedResidual p b f k) +
        walshSectorComponent (fun S => S.card = 4)
          (unnormalizedResidual p b f k) := by
  classical
  apply walshL2_ext
  intro U
  rw [inner_add_right, inner_walshL2_walshSectorComponent,
    inner_walshL2_walshSectorComponent]
  by_cases h2 : U.card = 2
  · rw [if_pos h2, if_neg (by omega), add_zero]
  by_cases h4 : U.card = 4
  · rw [if_neg h2, if_pos h4, zero_add]
  rw [if_neg h2, if_neg h4, add_zero]
  by_cases hempty : U = ∅
  · rw [hempty]; exact hcancel
  have hcard : U.card ≠ 0 := fun h => hempty (Finset.card_eq_zero.mp h)
  rw [unnormalizedResidual, inner_sub_right, inner_smul_right,
    Manhattan.inner_walshL2, if_neg hempty, map_add, inner_add_right,
    inner_walshL2_concreteFiberA_eq_zero hf p (by omega) (by omega),
    inner_walshL2_concreteFiberA_eq_zero hk p (by omega) (by omega)]
  simp

/-- The degree-two sector of the residual is `-(D₁f-D₂^*k)`: the constant
`b·1` does not contribute. -/
theorem walshSectorComponent_two_unnormalizedResidual (p : Fin 2 → ℝ) (b : ℝ)
    (f k : WalshL2) :
    walshSectorComponent (fun S => S.card = 2) (unnormalizedResidual p b f k) =
      -walshSectorComponent (fun S => S.card = 2)
        (Manhattan.concreteFiberA p (f + k)) := by
  classical
  apply walshL2_ext
  intro U
  rw [inner_walshL2_walshSectorComponent, inner_neg_right,
    inner_walshL2_walshSectorComponent]
  by_cases h2 : U.card = 2
  · rw [if_pos h2, if_pos h2, unnormalizedResidual, inner_sub_right,
      inner_smul_right, Manhattan.inner_walshL2,
      if_neg (fun hU : U = ∅ => by rw [hU] at h2; simp at h2)]
    ring
  · rw [if_neg h2, if_neg h2, neg_zero]

/-- The degree-four sector of the residual is `-D₃k`: neither `b·1` nor the
degree-one part contributes. -/
theorem walshSectorComponent_four_unnormalizedResidual (p : Fin 2 → ℝ) (b : ℝ)
    {f k : WalshL2} (hf : f ∈ Manhattan.walshDegree 1) :
    walshSectorComponent (fun S => S.card = 4) (unnormalizedResidual p b f k) =
      -walshSectorComponent (fun S => S.card = 4)
        (Manhattan.concreteFiberA p k) := by
  classical
  apply walshL2_ext
  intro U
  rw [inner_walshL2_walshSectorComponent, inner_neg_right,
    inner_walshL2_walshSectorComponent]
  by_cases h4 : U.card = 4
  · rw [if_pos h4, if_pos h4, unnormalizedResidual, inner_sub_right,
      inner_smul_right, Manhattan.inner_walshL2,
      if_neg (fun hU : U = ∅ => by rw [hU] at h4; simp at h4), map_add,
      inner_add_right,
      inner_walshL2_concreteFiberA_eq_zero hf p (by omega) (by omega)]
    ring
  · rw [if_neg h4, if_neg h4, neg_zero]

end SkewSupport

section QuadraticForms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

open Manhattan.Operator

/-- The dual energy of `u` is the primal energy of `H^{-1}u`. -/
theorem hMinusEnergy_eq_hEnergy (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (u : E) :
    P.hMinusEnergy hlambda u = P.hEnergy lambda ((P.hEquiv hlambda).symm u) := by
  rw [DissipativeSkewPair.hMinusEnergy, DissipativeSkewPair.hEnergy,
    DissipativeSkewPair.H_apply_inverse]

/-- The primal energy is a positive semidefinite quadratic form, so it obeys
the parallelogram bound. -/
theorem hEnergy_add_le (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 ≤ lambda) (x y : E) :
    P.hEnergy lambda (x + y) ≤
      2 * P.hEnergy lambda x + 2 * P.hEnergy lambda y := by
  have hsum : P.hEnergy lambda (x + y) + P.hEnergy lambda (x - y) =
      2 * P.hEnergy lambda x + 2 * P.hEnergy lambda y := by
    simp only [DissipativeSkewPair.hEnergy, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right]
    ring
  have hnn : 0 ≤ P.hEnergy lambda (x - y) := P.hEnergy_nonneg hlambda (x - y)
  linarith

/-- The dual energy obeys the same parallelogram bound. -/
theorem hMinusEnergy_add_le (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (u v : E) :
    P.hMinusEnergy hlambda (u + v) ≤
      2 * P.hMinusEnergy hlambda u + 2 * P.hMinusEnergy hlambda v := by
  rw [hMinusEnergy_eq_hEnergy P hlambda, hMinusEnergy_eq_hEnergy P hlambda,
    hMinusEnergy_eq_hEnergy P hlambda, map_add]
  exact hEnergy_add_le P hlambda.le _ _

/-- Both energies are even. -/
theorem hEnergy_neg (P : DissipativeSkewPair E) (lambda : ℝ) (x : E) :
    P.hEnergy lambda (-x) = P.hEnergy lambda x := by
  rw [show -x = ((-1 : ℂ)) • x by module, hEnergy_smul]
  simp

theorem hMinusEnergy_neg (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (u : E) :
    P.hMinusEnergy hlambda (-u) = P.hMinusEnergy hlambda u := by
  rw [show -u = ((-1 : ℂ)) • u by module, hMinusEnergy_smul]
  simp

end QuadraticForms

section Objective

/-- Paper (22): the four-sector quadratic form `E_p(f,k)` of the concrete
degree-one plus degree-three competitor.  The two dual terms are exactly
`‖D₁f-D₂^*k‖²_{-1}` and `‖D₃k‖²_{-1}`, read off as the degree-two and
degree-four Walsh sectors of the unnormalized residual. -/
def sectorObjective {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (b : ℝ) (f k : WalshL2) : ℝ :=
  (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda f +
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda k +
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
      hlambda
      (walshSectorComponent (fun S => S.card = 2)
        (unnormalizedResidual p b f k)) +
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
      hlambda
      (walshSectorComponent (fun S => S.card = 4)
        (unnormalizedResidual p b f k))

/-- The degree-two dual term of (22) does not see the constant `b·1`: it may
be computed on `A_p(f+k)` directly. -/
theorem hMinusEnergy_sector_two_residual {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (b : ℝ) (f k : WalshL2) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 2)
          (unnormalizedResidual p b f k)) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 2)
          (Manhattan.concreteFiberA p (f + k))) := by
  rw [walshSectorComponent_two_unnormalizedResidual, hMinusEnergy_neg]

/-- The degree-four dual term of (22) sees only the degree-three half: it may
be computed on `A_p k` directly. -/
theorem hMinusEnergy_sector_four_residual {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (b : ℝ) {f k : WalshL2}
    (hf : f ∈ Manhattan.walshDegree 1) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 4)
          (unnormalizedResidual p b f k)) =
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda (walshSectorComponent (fun S => S.card = 4)
          (Manhattan.concreteFiberA p k)) := by
  rw [walshSectorComponent_four_unnormalizedResidual p b hf, hMinusEnergy_neg]

/-- The unnormalized objective of (24) is dominated by twice the paper's
four-sector form `E_p(f,k)`.  This is the only place where the degree-zero
cancellation is used. -/
theorem unnormalizedObjective_le_sectorObjective {lambda : ℝ}
    (hlambda : 0 < lambda) (p : Fin 2 → ℝ) (b : ℝ) {f k : WalshL2}
    (hf : f ∈ Manhattan.walshDegree 1) (hk : k ∈ Manhattan.walshDegree 3)
    (hcancel : inner ℂ (Manhattan.walshL2 ∅) (unnormalizedResidual p b f k) = 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
          (f + k) +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (unnormalizedResidual p b f k) ≤
      2 * sectorObjective hlambda p b f k := by
  have hplus := hEnergy_add_le
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda.le f k
  have hminus := hMinusEnergy_add_le
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda
    (walshSectorComponent (fun S => S.card = 2) (unnormalizedResidual p b f k))
    (walshSectorComponent (fun S => S.card = 4) (unnormalizedResidual p b f k))
  rw [← unnormalizedResidual_eq_sector_sum p b hf hk hcancel] at hminus
  rw [sectorObjective]
  linarith

end Objective

end Manhattan.Glue
