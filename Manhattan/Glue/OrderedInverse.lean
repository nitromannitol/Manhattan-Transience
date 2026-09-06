import Manhattan.Glue.OrderedContractivity
import Manhattan.Glue.Transport
import Manhattan.Glue.ConcreteRaisingFourier
import Manhattan.Walsh.LowDegreeSectors

/-!
# The inverse of the ordered multiplier, and the symmetrized Fourier representative

Two prerequisites that were missing for the degree-four
raising sector, both stated for a general coefficient.  (The first of them was
in the end not consumed by that sector; see the correction on
`re_inner_image_orderedRestrict_orderedHInv_le` below.)

## 1.  The inverse of `orderedH`

`Manhattan.Glue.re_inner_image_orderedRestrict_le` compares the `N`-energy of
an image before and after the passage to the ordered representative, for any
nonnegative `N` commuting with the projection.  The weight the paper's `H^{-1}`
step needs is `N = (orderedH n lam p)^{-1}`, and only the Finset picture had an
inverse (`Manhattan.Glue.coeffH_bijective`).  This file supplies the ordered
one, by the same route: the ordered symmetric part `orderedFiberS` is
self-adjoint and dissipative, so it assembles into a
`Manhattan.Operator.DissipativeSkewPair`, whose `H` is *definitionally*
`orderedH` and whose coercive form is invertible by Lax--Milgram.  The inverse
is bounded by `lambda^{-1}`, is nonnegative, and commutes with both the
coincident-row projection and the choice of ordered representative, so it feeds
straight into (46).  The `H^{-1}` quadratic form is then the explicit weighted
integral `int (lambda + theta P)^{-1} |k|^2` of (20).

## 2.  The symmetrized Fourier representative

`Manhattan.Glue.inner_walshL2_walshRaiseDir_mFourierCoeff` requires its
frequency function `F` to reproduce the Walsh coefficient at *every* frequency
index `m`, ordered or not.  The Walsh coefficient at
`patternLines type112Pattern m` is symmetric under exchanging `m 0` and `m 1`,
because the two horizontal lines enter a `Finset`
(`patternLines_type112Pattern_rawSwap`), whereas
`mFourierCoeff (type112FreqFun c) m = rawExtend c m` vanishes as soon as
`m 0 >= m 1`.  So `type112FreqFun` is not admissible.  The admissible
representative is the symmetrization `type112SymmFreqFun`, whose Fourier
coefficient at `m` is `rawExtend c m + rawExtend c (rawSwap m)`; on the
diagonal `m 0 = m 1` both sides vanish, because there
`patternLines type112Pattern m` has two elements and cannot be a
type-`(1,1,2)` index.

Paper: `manuscript.tex:1193-1198` (equation (46), `eq:contract`), `manuscript.tex:1176-1200`
(equation (45)), `manuscript.tex:719-751` (equations (19), (20) and (Hsym)).
-/

noncomputable section

open MeasureTheory

namespace Manhattan.Glue

/-! ## Part 1: the inverse of the ordered multiplier -/

section L2Congr

variable {ι : Type*}

/-- A coordinate permutation moves to the other side of the inner product as its
inverse. -/
theorem inner_l2CongrLeft_left (e : ι ≃ ι) (c d : ℓ²(ι, ℂ)) :
    (inner ℂ (l2CongrLeft e c) d : ℂ) = inner ℂ c (l2CongrLeft e.symm d) := by
  rw [lp.inner_eq_tsum (𝕜 := ℂ) (l2CongrLeft e c) d,
    lp.inner_eq_tsum (𝕜 := ℂ) c (l2CongrLeft e.symm d)]
  rw [← e.tsum_eq (fun j => (inner ℂ ((l2CongrLeft e c) j) (d j) : ℂ))]
  refine tsum_congr fun i => ?_
  rw [l2CongrLeft_apply, l2CongrLeft_apply, Equiv.symm_apply_apply, Equiv.symm_symm]

theorem tupleTranslate_symm (n : ℕ) (x : Operator.Lattice) :
    (tupleTranslate n x).symm = tupleTranslate n (-x) := by
  apply Equiv.ext
  intro t
  rw [Equiv.symm_apply_eq]
  funext a
  rw [tupleTranslate_apply, tupleTranslate_apply]
  rcases h : t a with ⟨i, k⟩
  cases i <;>
    simp [lineTranslation, latticeToSite, transverseCoordinate]

theorem inner_orderedTranslate_left (n : ℕ) (x : Operator.Lattice)
    (c d : OrderedCoefficient n) :
    (inner ℂ (orderedTranslate n x c) d : ℂ)
      = inner ℂ c (orderedTranslate n (-x) d) := by
  rw [orderedTranslate, orderedTranslate, inner_l2CongrLeft_left, tupleTranslate_symm]

end L2Congr

theorem inner_orderedFiberS_symm (n : ℕ) (p : Fin 2 → ℝ)
    (c d : OrderedCoefficient n) :
    (inner ℂ (orderedFiberS n p c) d : ℂ) = inner ℂ c (orderedFiberS n p d) := by
  rw [orderedFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  have hconj2 : (starRingEnd ℂ) (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofNat]
  rw [hconj2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hexp : (starRingEnd ℂ) (Complex.exp (Complex.I * (p i : ℂ)))
      = Complex.exp (-Complex.I * (p i : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hexp' : (starRingEnd ℂ) (Complex.exp (-Complex.I * (p i : ℂ)))
      = Complex.exp (Complex.I * (p i : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_smul_left, inner_sub_right, inner_add_right, inner_smul_right,
    inner_smul_right, inner_smul_right, hexp, hexp',
    inner_orderedTranslate_left n (Operator.axisVector i) c d,
    inner_orderedTranslate_left n (-Operator.axisVector i) c d, neg_neg]
  have hconj2' : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := Complex.conj_ofNat 2
  rw [hconj2']
  ring

/-- The ordered-picture dissipative pair. -/
def orderedPair (n : ℕ) (p : Fin 2 → ℝ) :
    Operator.DissipativeSkewPair (OrderedCoefficient n) where
  S := orderedFiberS n p
  A := 0
  selfAdjoint_S := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro c d
    exact inner_orderedFiberS_symm n p c d
  nonpositive_S := re_inner_orderedFiberS_nonpos n p
  skewAdjoint_A := by simp

theorem orderedPair_H (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    (orderedPair n p).H lam = orderedH n lam p := rfl

/-- The route through this file
runs on `Manhattan.Glue.orderedHInv` and
`Manhattan.Glue.re_inner_orderedHInv_eq_integral` instead. -/
theorem orderedH_bijective (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) :
    Function.Bijective (orderedH n lam p) :=
  (orderedPair n p).H_bijective hlam

theorem orderedH_selfAdjoint (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    IsSelfAdjoint (orderedH n lam p) :=
  (orderedPair n p).H_selfAdjoint lam

/-- The bounded inverse of the ordered multiplier. -/
def orderedHInv (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  (((orderedPair n p).hEquiv hlam).symm :
    OrderedCoefficient n ≃L[ℂ] OrderedCoefficient n)

@[simp] theorem orderedH_orderedHInv (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    orderedH n lam p (orderedHInv n hlam p c) = c :=
  (orderedPair n p).H_apply_inverse hlam c

@[simp] theorem orderedHInv_orderedH (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    orderedHInv n hlam p (orderedH n lam p c) = c :=
  ((orderedPair n p).hEquiv hlam).symm_apply_apply c

section AbstractInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator that commutes with a projection has an inverse that commutes
with it. -/
theorem comm_of_inverse (T N P : E →L[ℂ] E)
    (hleft : ∀ c, N (T c) = c) (hright : ∀ c, T (N c) = c)
    (hcomm : ∀ c, P (T c) = T (P c)) (c : E) : P (N c) = N (P c) := by
  have h1 : P (T (N c)) = T (P (N c)) := hcomm (N c)
  rw [hright] at h1
  rw [h1, hleft]

/-- The inverse of a nonnegative operator is nonnegative. -/
theorem re_inner_inverse_nonneg (T N : E →L[ℂ] E) (hright : ∀ c, T (N c) = c)
    (hpos : ∀ x : E, 0 ≤ RCLike.re (inner ℂ (T x) x)) (c : E) :
    0 ≤ RCLike.re (inner ℂ (N c) c) := by
  have h1 : (inner ℂ (N c) c : ℂ) = inner ℂ (N c) (T (N c)) := by rw [hright]
  have h2 : (inner ℂ (N c) (T (N c)) : ℂ)
      = (starRingEnd ℂ) (inner ℂ (T (N c)) (N c)) := (inner_conj_symm _ _).symm
  rw [h1, h2, RCLike.conj_re]
  exact hpos (N c)

end AbstractInverse

theorem orderedHInv_comm_orderedRepresentativeProjection (n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (orderedHInv n hlam p c)
      = orderedHInv n hlam p (orderedRepresentativeProjection n c) :=
  comm_of_inverse (orderedH n lam p) (orderedHInv n hlam p)
    (orderedRepresentativeProjection n) (orderedHInv_orderedH n hlam p)
    (orderedH_orderedHInv n hlam p)
    (orderedH_comm_orderedRepresentativeProjection n lam p) c

theorem orderedHInv_comm_offDiagonalProjection (n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    offDiagonalProjection n (orderedHInv n hlam p c)
      = orderedHInv n hlam p (offDiagonalProjection n c) :=
  comm_of_inverse (orderedH n lam p) (orderedHInv n hlam p)
    (offDiagonalProjection n) (orderedHInv_orderedH n hlam p)
    (orderedH_orderedHInv n hlam p)
    (orderedH_comm_offDiagonalProjection n lam p) c

theorem re_inner_orderedHInv_nonneg (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    0 ≤ RCLike.re (inner ℂ (orderedHInv n hlam p c) c) :=
  re_inner_inverse_nonneg (orderedH n lam p) (orderedHInv n hlam p)
    (orderedH_orderedHInv n hlam p)
    (re_inner_orderedH_nonneg n (le_of_lt hlam) p) c

/-- Equation (46) for the ordered representative with the `H⁻¹` weight. -/
theorem re_inner_orderedHInv_orderedRepresentativeProjection_le (n : ℕ)
    {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedHInv n hlam p (orderedRepresentativeProjection n c))
        (orderedRepresentativeProjection n c))
      ≤ RCLike.re (inner ℂ (orderedHInv n hlam p c) c) :=
  re_inner_orderedRepresentativeProjection_le n (orderedHInv n hlam p)
    (orderedHInv_comm_orderedRepresentativeProjection n hlam p)
    (re_inner_orderedHInv_nonneg n hlam p) c

/-- The image form with the `H⁻¹` weight, for a general intertwining map `A`.
Correct and non-trivial as stated, but UNUSED: contrary to the earlier wording
here and in the module docstring above, the degree-four raising step does NOT
consume it.  Its only instantiation anywhere in the tree is
`Manhattan.Glue.re_inner_orderedHInv_orderedRaise_le`
(`Manhattan/Glue/OrderedRaising.lean`), which shows is vacuous,
so this lemma has zero external consumers.

MUST NOT SEAL: not
load-bearing.  -/
theorem re_inner_image_orderedRestrict_orderedHInv_le (m n : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (A : OrderedCoefficient m →L[ℂ] OrderedCoefficient n)
    (hAP : ∀ c, A (orderedRepresentativeProjection m c)
      = orderedRepresentativeProjection n (A c)) (c : OrderedCoefficient m) :
    RCLike.re (inner ℂ (orderedHInv n hlam p (A (orderedRepresentativeProjection m c)))
        (A (orderedRepresentativeProjection m c)))
      ≤ RCLike.re (inner ℂ (orderedHInv n hlam p (A c)) (A c)) :=
  re_inner_image_orderedRestrict_le m A (orderedRepresentativeProjection n)
    (orderedHInv n hlam p) hAP (orderedRepresentativeProjection_idem n)
    (orderedRepresentativeProjection_sym n)
    (orderedHInv_comm_orderedRepresentativeProjection n hlam p)
    (re_inner_orderedHInv_nonneg n hlam p) c

private theorem inner_lp_eq_integral' {n : ℕ} (u v : Lp ℂ 2 (LineTorusMeasure n))
    (w : UnitAddTorus (Fin n) → ℝ)
    (huv : (u : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => ((w t : ℝ) : ℂ) * v t) :
    RCLike.re (inner ℂ u v) = ∫ t, w t * ‖v t‖ ^ 2 ∂(LineTorusMeasure n) := by
  have hinner : inner ℂ u v = ∫ t, inner ℂ (u t) (v t) ∂(LineTorusMeasure n) :=
    L2.inner_def u v
  have hcongr : (∫ t, inner ℂ (u t) (v t) ∂(LineTorusMeasure n)) =
      ∫ t, ((w t * ‖v t‖ ^ 2 : ℝ) : ℂ) ∂(LineTorusMeasure n) := by
    refine integral_congr_ae ?_
    filter_upwards [huv] with t ht
    have hvv : (starRingEnd ℂ) ((v : UnitAddTorus (Fin n) → ℂ) t) *
        ((v : UnitAddTorus (Fin n) → ℂ) t) =
        ((‖(v : UnitAddTorus (Fin n) → ℂ) t‖ : ℝ) : ℂ) ^ 2 := by
      simpa using Complex.conj_mul' ((v : UnitAddTorus (Fin n) → ℂ) t)
    rw [ht]
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination ((w t : ℝ) : ℂ) * hvv
  rw [hinner, hcongr, integral_complex_ofReal]
  simp

/-- Consequence (i) in the ordered picture: the `H` quadratic form of an
ordered coefficient is the weighted integral of its line-frequency
coefficient. -/
theorem re_inner_orderedH_eq_integral (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedH n lam p c) c) =
      ∑' σ : Fin n → Axis,
        ∫ t, symbolWeight n lam p σ t *
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  have hΦ : inner ℂ (orderedH n lam p c) c =
      inner ℂ (freqH n lam p (orderedFourier n c)) (orderedFourier n c) := by
    rw [← (orderedFourier n).inner_map_map, orderedFourier_orderedH]
  have hs := lp.hasSum_inner (𝕜 := ℂ)
    (freqH n lam p (orderedFourier n c)) (orderedFourier n c)
  have hre := RCLike.hasSum_re ℂ hs
  have hterm : ∀ σ : Fin n → Axis,
      RCLike.re (inner ℂ ((freqH n lam p (orderedFourier n c)) σ)
          ((orderedFourier n c) σ)) =
        ∫ t, symbolWeight n lam p σ t *
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
    intro σ
    exact inner_lp_eq_integral' _ _ _ (coeFn_freqH n lam p (orderedFourier n c) σ)
  rw [hΦ]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [hterm] using hre

/-- Consequence (i) for `H⁻¹` in the ordered picture: if `orderedH n lam p d = c`
then the `H⁻¹` quadratic form of `c` is the integral of `(lambda + theta P)⁻¹`
against the squared modulus of its line-frequency coefficient. -/
theorem re_inner_orderedH_inv_eq_integral (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c d : OrderedCoefficient n) (hd : orderedH n lam p d = c) :
    RCLike.re (inner ℂ d c) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  have hΦ : inner ℂ d c =
      inner ℂ (orderedFourier n d) (orderedFourier n c) :=
    ((orderedFourier n).inner_map_map d c).symm
  have hgf : freqH n lam p (orderedFourier n d) = orderedFourier n c := by
    rw [← orderedFourier_orderedH, hd]
  have hcoe : ∀ σ : Fin n → Axis,
      ((orderedFourier n d) σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
        fun t => (((symbolWeight n lam p σ t)⁻¹ : ℝ) : ℂ) *
          ((orderedFourier n c) σ) t := by
    intro σ
    have h1 := coeFn_freqH n lam p (orderedFourier n d) σ
    rw [hgf] at h1
    filter_upwards [h1] with t ht
    have hw : symbolWeight n lam p σ t ≠ 0 := ne_of_gt (symbolWeight_pos n hlam p σ t)
    have hwC : ((symbolWeight n lam p σ t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
    rw [ht]
    push_cast
    field_simp
  have hs := lp.hasSum_inner (𝕜 := ℂ) (orderedFourier n d) (orderedFourier n c)
  have hre := RCLike.hasSum_re ℂ hs
  have hterm : ∀ σ : Fin n → Axis,
      RCLike.re (inner ℂ ((orderedFourier n d) σ) ((orderedFourier n c) σ)) =
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
    intro σ
    exact inner_lp_eq_integral' _ _ _ (hcoe σ)
  rw [hΦ]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [hterm] using hre

/-- The `H⁻¹` energy of an ordered coefficient, as an explicit weighted
integral. -/
theorem re_inner_orderedHInv_eq_integral (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedHInv n hlam p c) c) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) :=
  re_inner_orderedH_inv_eq_integral n hlam p c (orderedHInv n hlam p c)
    (orderedH_orderedHInv n hlam p c)

theorem norm_orderedH_lower (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) : lam * ‖c‖ ≤ ‖orderedH n lam p c‖ := by
  have hlow : lam * ‖c‖ ^ 2 ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) :=
    (orderedPair n p).hEnergy_lower lam c
  have hup : RCLike.re (inner ℂ (orderedH n lam p c) c) ≤ ‖orderedH n lam p c‖ * ‖c‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg c) with hc | hc
  · rw [← hc]
    simp
  · nlinarith [hlow, hup]

/-- The inverse is bounded by `lambda⁻¹`.
-/
theorem norm_orderedHInv_le (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) : ‖orderedHInv n hlam p c‖ ≤ lam⁻¹ * ‖c‖ := by
  have h := norm_orderedH_lower n lam p (orderedHInv n hlam p c)
  rw [orderedH_orderedHInv] at h
  rw [inv_mul_eq_div, le_div_iff₀ hlam]
  linarith [h]

/-! ## Part 2: the symmetrized Fourier representative -/

/-- Exchanging the two row coordinates of a raw type-`(1,1,2)` index. -/
def rawSwap : Manhattan.RawType112Index ≃ Manhattan.RawType112Index :=
  (Equiv.swap (0 : Fin 3) 1).arrowCongr (Equiv.refl ℤ)

@[simp] theorem rawSwap_apply (n : Manhattan.RawType112Index) (a : Fin 3) :
    rawSwap n a = n (Equiv.swap (0 : Fin 3) 1 a) := by
  simp [rawSwap, Equiv.arrowCongr]

theorem rawSwap_symm : rawSwap.symm = rawSwap := by
  apply Equiv.ext
  intro n
  funext a
  rw [rawSwap_apply]
  simp [rawSwap, Equiv.arrowCongr]

theorem rawSwap_zero (n : Manhattan.RawType112Index) : rawSwap n 0 = n 1 := by
  simp

theorem rawSwap_one (n : Manhattan.RawType112Index) : rawSwap n 1 = n 0 := by
  simp

theorem rawSwap_two (n : Manhattan.RawType112Index) : rawSwap n 2 = n 2 := by
  rw [rawSwap_apply, Equiv.swap_apply_of_ne_of_ne] <;> decide

theorem rawExtend_apply_of_not_lt (c : ℓ²(Manhattan.Type112Index, ℂ))
    {n : Manhattan.RawType112Index} (h : ¬ n 0 < n 1) : rawExtend c n = 0 := by
  rw [rawExtend]
  refine l2Extend_apply_of_notMem _ Manhattan.type112RawIndex_injective _ n ?_
  intro S hS
  exact h (hS ▸ type112RawIndex_lt S)

theorem rawExtend_apply_type112RawIndex (c : ℓ²(Manhattan.Type112Index, ℂ))
    (S : Manhattan.Type112Index) :
    rawExtend c (Manhattan.type112RawIndex S) = c S :=
  l2Extend_apply_image _ Manhattan.type112RawIndex_injective _ S

/-- The lines of the type-`(1,1,2)` pattern at frequency `m`. -/
theorem patternLines_type112Pattern (m : Fin 3 → ℤ) :
    patternLines type112Pattern m =
      ({(Axis.horizontal, m 0), (Axis.horizontal, m 1),
        (Axis.vertical, m 2)} : Finset LineIndex) := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [patternLines, huniv]
  simp [type112Pattern]

/-- **Obstruction (a).**  The Walsh index carried by the type-`(1,1,2)` pattern
is symmetric under exchanging the two row frequencies: the two horizontal lines
enter a `Finset`.  Any admissible frequency function must therefore have
symmetric Fourier coefficients, which `type112FreqFun` does not.
-/
theorem patternLines_type112Pattern_rawSwap (m : Fin 3 → ℤ) :
    patternLines type112Pattern (rawSwap m) = patternLines type112Pattern m := by
  rw [patternLines_type112Pattern, patternLines_type112Pattern, rawSwap_zero,
    rawSwap_one, rawSwap_two]
  exact Finset.insert_comm _ _ _

/-- The Walsh coefficient of a type-`(1,1,2)` synthesis at the pattern
frequency `m`, computed in the raw coordinates. -/
theorem type112CoefficientAt_patternLines (c : ℓ²(Manhattan.Type112Index, ℂ))
    (m : Fin 3 → ℤ) :
    Manhattan.type112CoefficientAt c (patternLines type112Pattern m)
      = rawExtend c m + rawExtend c (rawSwap m) := by
  classical
  rcases lt_trichotomy (m 0) (m 1) with hlt | heq | hgt
  · obtain ⟨T, hT⟩ := exists_type112RawIndex hlt
    have hset : patternLines type112Pattern m = T.1 := by
      rw [patternLines_type112Pattern, ← hT]
      exact type112Lines_eq T
    have hswap : ¬ (rawSwap m 0 < rawSwap m 1) := by
      rw [rawSwap_zero, rawSwap_one]
      omega
    rw [hset, Manhattan.type112CoefficientAt, dif_pos T.2,
      rawExtend_apply_of_not_lt c hswap, add_zero, ← hT,
      rawExtend_apply_type112RawIndex]
  · have h0 : ¬ (m 0 < m 1) := by omega
    have h1 : ¬ (rawSwap m 0 < rawSwap m 1) := by
      rw [rawSwap_zero, rawSwap_one]
      omega
    have hnot : ¬ Manhattan.IsType112Index (patternLines type112Pattern m) := by
      rw [patternLines_type112Pattern, heq]
      intro hS
      have hcard : ({(Axis.horizontal, m 1), (Axis.horizontal, m 1),
          (Axis.vertical, m 2)} : Finset LineIndex).card = 3 := hS.1
      rw [Finset.insert_idem] at hcard
      have : ({(Axis.horizontal, m 1), (Axis.vertical, m 2)} : Finset LineIndex).card ≤ 2 :=
        Finset.card_insert_le _ _ |>.trans (by simp)
      omega
    rw [Manhattan.type112CoefficientAt, dif_neg hnot,
      rawExtend_apply_of_not_lt c h0, rawExtend_apply_of_not_lt c h1, add_zero]
  · have hlt' : rawSwap m 0 < rawSwap m 1 := by
      rw [rawSwap_zero, rawSwap_one]
      omega
    obtain ⟨T, hT⟩ := exists_type112RawIndex hlt'
    have hset : patternLines type112Pattern m = T.1 := by
      rw [patternLines_type112Pattern, ← type112Lines_eq T, hT, rawSwap_zero,
        rawSwap_one, rawSwap_two]
      exact Finset.insert_comm _ _ _
    have h0 : ¬ (m 0 < m 1) := by omega
    rw [hset, Manhattan.type112CoefficientAt, dif_pos T.2,
      rawExtend_apply_of_not_lt c h0, zero_add, ← hT,
      rawExtend_apply_type112RawIndex]

/-- The symmetrized line-frequency function of a type-`(1,1,2)` coefficient:
the extension by zero to the raw coordinates, symmetrized in the two row
frequencies.  Unlike `type112FreqFun`, whose Fourier coefficients vanish off
the strictly ordered row pairs, this is the representative whose Fourier
coefficient sequence *is* the Walsh coefficient sequence of the pattern. -/
def type112SymmFreqFun (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    Lp ℂ 2 (LineTorusMeasure 3) :=
  (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
    (rawExtend c + l2CongrLeft rawSwap (rawExtend c))

theorem mFourierCoeff_type112SymmFreqFun (c : ℓ²(Manhattan.Type112Index, ℂ))
    (m : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (type112SymmFreqFun c) m
      = rawExtend c m + rawExtend c (rawSwap m) := by
  rw [← UnitAddTorus.mFourierBasis_repr, type112SymmFreqFun,
    LinearIsometryEquiv.apply_symm_apply]
  show (rawExtend c : Manhattan.RawType112Index → ℂ) m
    + (l2CongrLeft rawSwap (rawExtend c) : Manhattan.RawType112Index → ℂ) m = _
  rw [l2CongrLeft_apply, rawSwap_symm]

/-- **The Fourier-coefficient hypothesis, for the symmetrized representative.**
Every Walsh coefficient of a type-`(1,1,2)` synthesis at the pattern
`(horizontal, horizontal, vertical)` is the corresponding Fourier coefficient
of `type112SymmFreqFun`, for *every* frequency index, ordered or not. -/
theorem inner_walshL2_patternLines_type112WalshSynthesis
    (c : ℓ²(Manhattan.Type112Index, ℂ)) (m : Fin 3 → ℤ) :
    inner ℂ (Manhattan.walshL2 (patternLines type112Pattern m))
        (Manhattan.type112WalshSynthesis c)
      = UnitAddTorus.mFourierCoeff (type112SymmFreqFun c) m := by
  rw [Manhattan.inner_walshL2_type112WalshSynthesis,
    type112CoefficientAt_patternLines, mFourierCoeff_type112SymmFreqFun]

attribute [local instance] Real.fact_zero_lt_one

/-- The unit circle carries its normalized Haar measure throughout this file. -/
local instance orderedInverseUnitAddCircleMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance orderedInverseUnitAddCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integrable_type112SymmFreqFun (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    Integrable (type112SymmFreqFun c : UnitAddTorus (Fin 3) → ℂ) volume :=
  (Lp.memLp (type112SymmFreqFun c)).integrable (by norm_num)

/-- **The admissible representative works.**  With the symmetrized frequency
function the degree-four raising identity applies to a type-`(1,1,2)`
synthesis: the Walsh coefficient of the raised vector at the index obtained by
appending the origin line of type `i` is the Fourier coefficient of
`i sin(P_i)` times the symmetrized representative. -/
theorem inner_walshL2_walshRaiseDir_type112SymmFreqFun
    (c : ℓ²(Manhattan.Type112Index, ℂ)) (p : Fin 2 → ℝ) (i : Fin 2)
    (n : Fin 3 → ℤ) (hn : Manhattan.originLine i ∉ patternLines type112Pattern n) :
    inner ℂ (Manhattan.walshL2
        (insert (Manhattan.originLine i) (patternLines type112Pattern n)))
        (walshRaiseDir p i (Manhattan.type112WalshSynthesis c))
      = UnitAddTorus.mFourierCoeff
          (fun t => raisingSymbol p i type112Pattern t *
            (type112SymmFreqFun c : UnitAddTorus (Fin 3) → ℂ) t) n :=
  inner_walshL2_walshRaiseDir_mFourierCoeff type112Pattern p i
    (Manhattan.type112WalshSynthesis c) _ (integrable_type112SymmFreqFun c)
    (inner_walshL2_patternLines_type112WalshSynthesis c) n hn

end Manhattan.Glue
