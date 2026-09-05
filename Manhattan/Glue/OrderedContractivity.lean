import Manhattan.Glue.ConcreteMultiplier

/-!
# Weighted contractivity of the ordered representative

Paper: `manuscript.tex:1193-1198` (equation (46), `eq:contract`) and
`manuscript.tex:1233-1235` (the sentence "a multiplier depending on $P$ is a
linear combination of simultaneous translations of all line indices"; its
statement form is the commutation clause of Lemma 5.1 at
`manuscript.tex:1189-1190`), `manuscript.tex:1212-1221` (Lemma 5.3,
`lem:distinct`).

the formalization proved the analogous statement for the *coincident-row diagonal*
(`Manhattan.Glue.diagonalMultiplierEnergy_le_rawMultiplierEnergy`), and
`Manhattan.norm_type112DiagonalProjection_le` is the *unweighted* contractivity
of the passage to the ordered representative. This file supplies the missing
weighted statement: passing from a raw coefficient indexed by ordered, possibly
coincident tuples of lines to its ordered off-diagonal representative (the
sorted enumeration `Manhattan.Glue.degreeEnum` of a Finset Walsh index) is
contractive for the quadratic form of any operator that commutes with the
restriction, and in particular for the multiplier `H_n = lambda + theta(P)`.

The mechanism is entirely elementary and is the paper's own argument: the
restriction is an orthogonal projection onto a coordinate subspace, lattice
translations permute the coordinates preserving that subspace, and every
multiplier in the total frequency `P` is assembled from such translations, so
the quadratic form splits with no cross term.
-/

noncomputable section

open MeasureTheory

namespace Manhattan.Glue

/-! ### An abstract splitting device

If a bounded operator commutes with an orthogonal projection, its quadratic
form splits as the sum of the forms on the range and on the kernel. Positivity
of the operator then gives contractivity. No square root and no spectral
theory is needed. -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The quadratic form of an operator commuting with an orthogonal projection
splits along that projection: there is no cross term. -/
theorem inner_split_of_commuting_projection (T P : E →L[ℂ] E)
    (hidem : ∀ c, P (P c) = P c)
    (hsym : ∀ x y : E, inner ℂ (P x) y = inner ℂ x (P y))
    (hcomm : ∀ c, P (T c) = T (P c)) (c : E) :
    (inner ℂ (T c) c : ℂ)
      = inner ℂ (T (P c)) (P c) + inner ℂ (T (c - P c)) (c - P c) := by
  have hPzero : P (c - P c) = 0 := by
    rw [map_sub, hidem, sub_self]
  have hcross1 : (inner ℂ (T (P c)) (c - P c) : ℂ) = 0 := by
    rw [← hcomm, hsym, hPzero, inner_zero_right]
  have hcross2 : (inner ℂ (T (c - P c)) (P c) : ℂ) = 0 := by
    rw [← hsym, hcomm, hPzero, map_zero, inner_zero_left]
  have h1 : (inner ℂ (T (P c)) c : ℂ) = inner ℂ (T (P c)) (P c) := by
    rw [inner_sub_right] at hcross1
    exact (sub_eq_zero.mp hcross1).symm ▸ rfl
  have h2 : (inner ℂ (T (c - P c)) c : ℂ) = inner ℂ (T (c - P c)) (c - P c) := by
    have hsplit : (inner ℂ (T (c - P c)) c : ℂ)
        - inner ℂ (T (c - P c)) (c - P c) = inner ℂ (T (c - P c)) (P c) := by
      rw [← inner_sub_right]
      congr 1
      abel
    rw [hcross2] at hsplit
    exact sub_eq_zero.mp hsplit
  have hTc : T c = T (P c) + T (c - P c) := by
    rw [← map_add]
    congr 1
    abel
  rw [hTc, inner_add_left, h1, h2]

/-- Equation (46) in the abstract: a positive operator commuting with an
orthogonal projection has smaller energy on the projected vector. -/
theorem re_inner_le_of_commuting_projection (T P : E →L[ℂ] E)
    (hidem : ∀ c, P (P c) = P c)
    (hsym : ∀ x y : E, inner ℂ (P x) y = inner ℂ x (P y))
    (hcomm : ∀ c, P (T c) = T (P c))
    (hpos : ∀ x : E, 0 ≤ RCLike.re (inner ℂ (T x) x)) (c : E) :
    RCLike.re (inner ℂ (T (P c)) (P c)) ≤ RCLike.re (inner ℂ (T c) c) := by
  rw [inner_split_of_commuting_projection T P hidem hsym hcomm c, map_add]
  linarith [hpos (c - P c)]

/-- The same, transported through an intertwining map. This is the form used
for the image energies: if `A` intertwines a projection `P` upstairs with a
projection `Q` downstairs, and the weight `N` commutes with `Q`, then the
`N`-energy of `A` applied to the projected vector is no larger. -/
theorem re_inner_image_le_of_intertwining (A : E →L[ℂ] F) (P : E →L[ℂ] E)
    (Q N : F →L[ℂ] F) (hAP : ∀ c, A (P c) = Q (A c))
    (hidem : ∀ y, Q (Q y) = Q y)
    (hsym : ∀ x y : F, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hcomm : ∀ y, Q (N y) = N (Q y))
    (hpos : ∀ y : F, 0 ≤ RCLike.re (inner ℂ (N y) y)) (c : E) :
    RCLike.re (inner ℂ (N (A (P c))) (A (P c)))
      ≤ RCLike.re (inner ℂ (N (A c)) (A c)) := by
  rw [hAP]
  exact re_inner_le_of_commuting_projection N Q hidem hsym hcomm hpos (A c)

end Abstract

/-! ### Coordinate support projections on `l^2` -/

section Support

variable {ι : Type*}

private theorem indicator_norm_rpow_le (s : Set ι) (c : ℓ²(ι, ℂ)) (i : ι) :
    ‖s.indicator (fun j => (c j : ℂ)) i‖ ^ ENNReal.toReal 2
      ≤ ‖c i‖ ^ ENNReal.toReal 2 := by
  by_cases h : i ∈ s
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, norm_zero,
      Real.zero_rpow (by norm_num : ENNReal.toReal 2 ≠ 0)]
    positivity

private theorem memlp_indicator (s : Set ι) (c : ℓ²(ι, ℂ)) :
    Memℓp (s.indicator (fun j => (c j : ℂ))) 2 := by
  apply memℓp_gen
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (indicator_norm_rpow_le s c)
    (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2))

/-- Restriction of a square-summable family to a set of coordinates. This is
the orthogonal projection onto the closed span of the corresponding standard
vectors. -/
def l2SupportProjection (s : Set ι) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨_, memlp_indicator s c⟩
      map_add' := by
        intro c d
        apply lp.ext
        funext i
        show s.indicator (fun j => ((c + d : ℓ²(ι, ℂ)) j : ℂ)) i
          = s.indicator (fun j => (c j : ℂ)) i + s.indicator (fun j => (d j : ℂ)) i
        by_cases h : i ∈ s <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      map_smul' := by
        intro a c
        apply lp.ext
        funext i
        show s.indicator (fun j => ((a • c : ℓ²(ι, ℂ)) j : ℂ)) i
          = a • s.indicator (fun j => (c j : ℂ)) i
        by_cases h : i ∈ s <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h] }
    1 <| by
      intro c
      rw [one_mul, lp.norm_eq_tsum_rpow (by norm_num),
        lp.norm_eq_tsum_rpow (by norm_num)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact Summable.tsum_le_tsum (indicator_norm_rpow_le s c)
        (Summable.of_nonneg_of_le (fun _ => by positivity)
          (indicator_norm_rpow_le s c)
          (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2)))
        (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2))

@[simp] theorem l2SupportProjection_apply (s : Set ι) (c : ℓ²(ι, ℂ)) (i : ι) :
    l2SupportProjection s c i = s.indicator (fun j => (c j : ℂ)) i := rfl

theorem l2SupportProjection_idem (s : Set ι) (c : ℓ²(ι, ℂ)) :
    l2SupportProjection s (l2SupportProjection s c) = l2SupportProjection s c := by
  apply lp.ext
  funext i
  by_cases h : i ∈ s <;>
    simp [l2SupportProjection_apply, Set.indicator_of_mem,
      Set.indicator_of_notMem, h]

theorem l2SupportProjection_sym (s : Set ι) (c d : ℓ²(ι, ℂ)) :
    inner ℂ (l2SupportProjection s c) d = inner ℂ c (l2SupportProjection s d) := by
  rw [lp.inner_eq_tsum (𝕜 := ℂ) (l2SupportProjection s c) d,
    lp.inner_eq_tsum (𝕜 := ℂ) c (l2SupportProjection s d)]
  refine tsum_congr fun i => ?_
  by_cases h : i ∈ s <;>
    simp [l2SupportProjection_apply, Set.indicator_of_mem,
      Set.indicator_of_notMem, h]

theorem norm_l2SupportProjection_le (s : Set ι) (c : ℓ²(ι, ℂ)) :
    ‖l2SupportProjection s c‖ ≤ ‖c‖ := by
  have h2 : ‖l2SupportProjection (ι := ι) s‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ (by norm_num) _
  calc ‖l2SupportProjection s c‖
      ≤ ‖l2SupportProjection (ι := ι) s‖ * ‖c‖ :=
        (l2SupportProjection s).le_opNorm c
    _ ≤ 1 * ‖c‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg c)
    _ = ‖c‖ := one_mul _

/-- A coordinate permutation preserving the support set commutes with the
support projection. -/
theorem l2SupportProjection_l2CongrLeft (s : Set ι) (e : ι ≃ ι)
    (he : ∀ i, e i ∈ s ↔ i ∈ s) (c : ℓ²(ι, ℂ)) :
    l2SupportProjection s (l2CongrLeft e c)
      = l2CongrLeft e (l2SupportProjection s c) := by
  apply lp.ext
  funext i
  have hi : (i ∈ s) ↔ (e.symm i ∈ s) := by
    have := he (e.symm i)
    rwa [Equiv.apply_symm_apply] at this
  rw [l2SupportProjection_apply, l2CongrLeft_apply, l2SupportProjection_apply]
  by_cases h : i ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hi.mp h), l2CongrLeft_apply]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hc => h (hi.mpr hc))]

end Support

/-! ### Extensionality on the standard `l^2` vectors -/

section Ext

variable {ι : Type*}

/-- Coordinate evaluation as a bounded linear functional. -/
def l2Eval (i : ι) : ℓ²(ι, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun c => c i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun c => by
      simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) c i)

@[simp] theorem l2Eval_apply (i : ι) (c : ℓ²(ι, ℂ)) : l2Eval i c = c i := rfl

private def l2StandardBasis (ι : Type*) : HilbertBasis ι ℂ (ℓ²(ι, ℂ)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

private theorem l2StandardBasis_apply [DecidableEq ι] (i : ι) :
    l2StandardBasis ι i = lp.single 2 i (1 : ℂ) :=
  (HilbertBasis.repr_symm_single (l2StandardBasis ι) i).symm

/-- Two bounded operators out of `l^2` agreeing on the standard vectors agree. -/
theorem l2_ext_on_single [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T U : ℓ²(ι, ℂ) →L[ℂ] E)
    (h : ∀ i : ι, T (lp.single 2 i (1 : ℂ)) = U (lp.single 2 i (1 : ℂ)))
    (c : ℓ²(ι, ℂ)) : T c = U c := by
  have hTU : T = U := by
    refine ContinuousLinearMap.ext_on (s := Set.range (l2StandardBasis ι)) ?_ ?_
    · rw [Submodule.dense_iff_topologicalClosure_eq_top]
      exact (l2StandardBasis ι).dense_span
    · rintro _ ⟨i, rfl⟩
      rw [l2StandardBasis_apply]
      exact h i
  rw [hTU]

end Ext

/-! ### The ordered representatives

The sorted enumeration `degreeEnum` of a Finset Walsh index is the paper's
choice of ordered representative for an off-diagonal tuple of lines. Its
range is the set of ordered representatives, and restriction to that range is
the orthogonal projection realising the passage from a raw, possibly
coincident, ordered coefficient to its Finset coefficient. -/

section Ordered

variable (n : ℕ)

/-- The ordered representatives: tuples that are the sorted enumeration of a
degree-`n` Walsh index. -/
def degreeRange : Set (Fin n → LineIndex) := Set.range (degreeEnum (n := n))

theorem mem_degreeRange_iff (t : Fin n → LineIndex) :
    t ∈ degreeRange n ↔ ∃ S : WalshDegreeIndex n, degreeEnum S = t := Iff.rfl

/-- The orthogonal projection onto the ordered representatives. -/
def orderedRepresentativeProjection :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  l2SupportProjection (degreeRange n)

@[simp] theorem orderedRepresentativeProjection_apply (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) :
    orderedRepresentativeProjection n c t =
      (degreeRange n).indicator (fun u => (c u : ℂ)) t := rfl

theorem orderedRepresentativeProjection_idem (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (orderedRepresentativeProjection n c)
      = orderedRepresentativeProjection n c :=
  l2SupportProjection_idem _ c

theorem orderedRepresentativeProjection_sym (c d : OrderedCoefficient n) :
    inner ℂ (orderedRepresentativeProjection n c) d
      = inner ℂ c (orderedRepresentativeProjection n d) :=
  l2SupportProjection_sym _ c d

theorem norm_orderedRepresentativeProjection_le (c : OrderedCoefficient n) :
    ‖orderedRepresentativeProjection n c‖ ≤ ‖c‖ :=
  norm_l2SupportProjection_le _ c

private theorem memlp_orderedRestrict (c : OrderedCoefficient n) :
    Memℓp (fun S : WalshDegreeIndex n => (c (degreeEnum S) : ℂ)) 2 := by
  apply memℓp_gen
  simpa [Function.comp_def] using
    ((lp.memℓp c).summable (by norm_num : 0 < ENNReal.toReal 2)).comp_injective
      (degreeEnum_injective n)

/-- Passing from an ordered coefficient to the Finset coefficient by reading it
at the sorted representatives. This is the ordered analogue of
`Manhattan.type112DiagonalProjection`. -/
def orderedRestrict : OrderedCoefficient n →L[ℂ] DegreeCoefficient n :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨_, memlp_orderedRestrict n c⟩
      map_add' := by
        intro c d
        apply lp.ext
        funext S
        rfl
      map_smul' := by
        intro a c
        apply lp.ext
        funext S
        rfl }
    1 <| by
      intro c
      rw [one_mul, lp.norm_eq_tsum_rpow (by norm_num),
        lp.norm_eq_tsum_rpow (by norm_num)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have hraw : Summable fun t : Fin n → LineIndex =>
          ‖c t‖ ^ ENNReal.toReal 2 :=
        (lp.memℓp c).summable (by norm_num : 0 < ENNReal.toReal 2)
      have hsum : Summable fun S : WalshDegreeIndex n =>
          ‖c (degreeEnum S)‖ ^ ENNReal.toReal 2 := by
        simpa [Function.comp_def] using hraw.comp_injective (degreeEnum_injective n)
      exact hsum.tsum_le_tsum_of_inj (degreeEnum (n := n)) (degreeEnum_injective n)
        (fun _ _ => by positivity) (fun _ => le_rfl) hraw

@[simp] theorem orderedRestrict_apply (c : OrderedCoefficient n)
    (S : WalshDegreeIndex n) : orderedRestrict n c S = c (degreeEnum S) := rfl

/-- The sorted enumeration reads the Walsh coefficient it carries. -/
theorem walshOrdered_apply_degreeEnum (d : DegreeCoefficient n)
    (S : WalshDegreeIndex n) : walshOrdered n d (degreeEnum S) = d S := by
  refine l2_ext_on_single
    ((l2Eval (degreeEnum S)).comp (walshOrdered n).toContinuousLinearMap)
    (l2Eval S) ?_ d
  intro T
  show (walshOrdered n (lp.single 2 T (1 : ℂ)) : (Fin n → LineIndex) → ℂ)
      (degreeEnum S) = (lp.single 2 T (1 : ℂ) : WalshDegreeIndex n → ℂ) S
  rw [walshOrdered_single, one_smul]
  by_cases h : T = S
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne 2 _ _
      (fun hc : degreeEnum S = degreeEnum T => h (degreeEnum_injective n hc.symm)),
      lp.single_apply_ne 2 _ _ (fun hc : S = T => h hc.symm)]

/-- Off the ordered representatives the sorted enumeration carries nothing. -/
theorem walshOrdered_apply_of_notMem_degreeRange (d : DegreeCoefficient n)
    {t : Fin n → LineIndex} (ht : t ∉ degreeRange n) :
    walshOrdered n d t = 0 := by
  refine l2_ext_on_single
    ((l2Eval t).comp (walshOrdered n).toContinuousLinearMap) 0 ?_ d
  intro T
  show (walshOrdered n (lp.single 2 T (1 : ℂ)) : (Fin n → LineIndex) → ℂ) t = 0
  rw [walshOrdered_single, one_smul]
  exact lp.single_apply_ne 2 _ _ (fun hc : t = degreeEnum T => ht ⟨T, hc.symm⟩)

/-- The passage to the ordered representative is exactly the orthogonal
projection onto the ordered representatives, read in the Finset picture. -/
theorem walshOrdered_orderedRestrict (c : OrderedCoefficient n) :
    walshOrdered n (orderedRestrict n c) = orderedRepresentativeProjection n c := by
  apply lp.ext
  funext t
  by_cases h : t ∈ degreeRange n
  · obtain ⟨S, rfl⟩ := h
    have hmem : degreeEnum S ∈ degreeRange n := ⟨S, rfl⟩
    rw [walshOrdered_apply_degreeEnum, orderedRestrict_apply,
      orderedRepresentativeProjection_apply, Set.indicator_of_mem hmem]
  · rw [walshOrdered_apply_of_notMem_degreeRange n _ h,
      orderedRepresentativeProjection_apply, Set.indicator_of_notMem h]

/-- The ordered representative of an ordered coefficient has the norm of its
projection: `Pi_n` followed by the choice of representative is an isometry on
the ordered subspace. -/
theorem norm_orderedRestrict (c : OrderedCoefficient n) :
    ‖orderedRestrict n c‖ = ‖orderedRepresentativeProjection n c‖ := by
  rw [← walshOrdered_orderedRestrict, (walshOrdered n).norm_map]

/-! ### Translations preserve the ordered representatives

This is the paper's "a multiplier in `P` is a combination of simultaneous
translations of all line indices, which preserve distinctness"
(`manuscript.tex:1233-1235`). Sorting is equivariant
(`Manhattan.Glue.degreeEnum_translateDegreeIndex`), so a simultaneous
translation not only preserves distinctness but also preserves the *choice of
ordered representative*. That is what upgrades L3's
`orderedH_comm_offDiagonalProjection` to the statement needed for (46). -/

theorem tupleTranslate_image_degreeRange (x : Operator.Lattice) :
    (tupleTranslate n x) '' (degreeRange n) = degreeRange n := by
  have hcomp : (tupleTranslate n x) ∘ (degreeEnum (n := n))
      = (degreeEnum (n := n)) ∘ (translateDegreeIndex n x) := by
    funext S
    funext a
    exact (degreeEnum_translateDegreeIndex x S a).symm
  calc (tupleTranslate n x) '' (degreeRange n)
      = Set.range ((tupleTranslate n x) ∘ (degreeEnum (n := n))) := by
        rw [degreeRange, Set.range_comp]
    _ = Set.range ((degreeEnum (n := n)) ∘ (translateDegreeIndex n x)) := by
        rw [hcomp]
    _ = degreeRange n := (translateDegreeIndex n x).surjective.range_comp _

theorem tupleTranslate_mem_degreeRange (x : Operator.Lattice)
    (t : Fin n → LineIndex) :
    tupleTranslate n x t ∈ degreeRange n ↔ t ∈ degreeRange n := by
  have himg := tupleTranslate_image_degreeRange n x
  constructor
  · intro h
    rw [← himg] at h
    obtain ⟨u, hu, heq⟩ := h
    exact (tupleTranslate n x).injective heq ▸ hu
  · intro h
    rw [← himg]
    exact ⟨t, h, rfl⟩

theorem orderedTranslate_comm_orderedRepresentativeProjection
    (x : Operator.Lattice) (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (orderedTranslate n x c)
      = orderedTranslate n x (orderedRepresentativeProjection n c) :=
  l2SupportProjection_l2CongrLeft (degreeRange n) (tupleTranslate n x)
    (tupleTranslate_mem_degreeRange n x) c

theorem orderedFiberS_comm_orderedRepresentativeProjection (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (orderedFiberS n p c)
      = orderedFiberS n p (orderedRepresentativeProjection n c) := by
  rw [orderedFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sum, map_add, map_sub,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orderedTranslate_comm_orderedRepresentativeProjection,
    orderedTranslate_comm_orderedRepresentativeProjection]

/-- Equation (46)'s commutation clause for the *ordered representative*: the
multiplier `lambda + theta(P)` commutes with the choice of ordered
representative, not merely with the removal of the coincident-row diagonal. -/
theorem orderedH_comm_orderedRepresentativeProjection (lam : ℝ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (orderedH n lam p c)
      = orderedH n lam p (orderedRepresentativeProjection n c) := by
  rw [orderedH]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_smul,
    orderedFiberS_comm_orderedRepresentativeProjection]

/-! ### Positivity of the ordered multiplier -/

private theorem re_ofReal_mul (r : ℝ) (z : ℂ) :
    RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by simp

private theorem re_inner_unitary_smul_le {m : ℕ}
    (T : OrderedCoefficient m ≃ₗᵢ[ℂ] OrderedCoefficient m) (a : ℂ) (ha : ‖a‖ = 1)
    (c : OrderedCoefficient m) :
    RCLike.re (inner ℂ (a • T c) c) ≤ ‖c‖ ^ 2 := by
  calc RCLike.re (inner ℂ (a • T c) c)
      ≤ ‖(inner ℂ (a • T c) c : ℂ)‖ := RCLike.re_le_norm _
    _ ≤ ‖a • T c‖ * ‖c‖ := norm_inner_le_norm _ _
    _ = ‖c‖ ^ 2 := by
        rw [norm_smul, ha, one_mul, T.norm_map]
        ring

/-- The ordered symmetric part is dissipative. -/
theorem re_inner_orderedFiberS_nonpos (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedFiberS n p c) c) ≤ 0 := by
  have hnormexp : ∀ z : ℝ, ‖Complex.exp (Complex.I * (z : ℂ))‖ = 1 := by
    intro z
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I z
  have hnormexp' : ∀ z : ℝ, ‖Complex.exp (-Complex.I * (z : ℂ))‖ = 1 := by
    intro z
    have : (-Complex.I) * (z : ℂ) = ((-z : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hself : RCLike.re (inner ℂ ((2 : ℂ) • c) c) = 2 * ‖c‖ ^ 2 := by
    rw [two_smul, inner_add_left, map_add, inner_self_eq_norm_sq]
    ring
  have hterm : ∀ i : Fin 2, RCLike.re (inner ℂ
      (Complex.exp (Complex.I * (p i : ℂ)) •
          (orderedTranslate n (Operator.axisVector i) c)
        + Complex.exp (-Complex.I * (p i : ℂ)) •
          (orderedTranslate n (-Operator.axisVector i) c)
        - (2 : ℂ) • c) c) ≤ 0 := by
    intro i
    rw [inner_sub_left, inner_add_left, map_sub, map_add, hself]
    have h1 := re_inner_unitary_smul_le (orderedTranslate n (Operator.axisVector i))
      _ (hnormexp (p i)) c
    have h2 := re_inner_unitary_smul_le
      (orderedTranslate n (-Operator.axisVector i)) _ (hnormexp' (p i)) c
    linarith
  rw [orderedFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_smul_left, sum_inner]
  have hhalf : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by
    have h2 : ((2 : ℂ))⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.conj_ofReal]
  rw [hhalf]
  have hre : RCLike.re ((((2 : ℝ)⁻¹ : ℝ) : ℂ) *
      ∑ i : Fin 2, inner ℂ
        (Complex.exp (Complex.I * (p i : ℂ)) •
            (orderedTranslate n (Operator.axisVector i) c)
          + Complex.exp (-Complex.I * (p i : ℂ)) •
            (orderedTranslate n (-Operator.axisVector i) c)
          - (2 : ℂ) • c) c)
      = (2 : ℝ)⁻¹ * RCLike.re (∑ i : Fin 2, inner ℂ
        (Complex.exp (Complex.I * (p i : ℂ)) •
            (orderedTranslate n (Operator.axisVector i) c)
          + Complex.exp (-Complex.I * (p i : ℂ)) •
            (orderedTranslate n (-Operator.axisVector i) c)
          - (2 : ℂ) • c) c) := re_ofReal_mul _ _
  rw [hre, map_sum]
  have hsum : (∑ i : Fin 2, RCLike.re (inner ℂ
      (Complex.exp (Complex.I * (p i : ℂ)) •
          (orderedTranslate n (Operator.axisVector i) c)
        + Complex.exp (-Complex.I * (p i : ℂ)) •
          (orderedTranslate n (-Operator.axisVector i) c)
        - (2 : ℂ) • c) c)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hterm i
  nlinarith [hsum]

/-- `H_n` is nonnegative in the ordered picture. -/
theorem re_inner_orderedH_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    0 ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) := by
  have hlower : lam * ‖c‖ ^ 2 ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) := by
    rw [orderedH]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    rw [inner_sub_left, map_sub, inner_smul_left]
    have hconj : (starRingEnd ℂ) ((lam : ℝ) : ℂ) = ((lam : ℝ) : ℂ) :=
      Complex.conj_ofReal lam
    rw [hconj]
    have hre : RCLike.re (((lam : ℝ) : ℂ) * inner ℂ c c) = lam * ‖c‖ ^ 2 := by
      rw [re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hre]
    linarith [re_inner_orderedFiberS_nonpos n p c]
  nlinarith [sq_nonneg ‖c‖, hlam]

/-! ### The ordered representatives are off-diagonal

The sorted enumeration of an `n`-element Finset is injective as a tuple, so the
ordered representatives already lie in the range of the paper's `Pi_n`. The
passage to the ordered representative therefore *factors through* the removal
of the coincident-row diagonal, and the contractivity below refines the formalizations
diagonal statement rather than repeating it. -/

theorem injective_degreeEnum_tuple (S : WalshDegreeIndex n) :
    Function.Injective (degreeEnum S) := by
  classical
  have himg : Finset.univ.image (degreeEnum S) = S.1 := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, range_degreeEnum]
  have hcard : (Finset.univ.image (degreeEnum S)).card
      = (Finset.univ : Finset (Fin n)).card := by
    rw [himg, S.2, Finset.card_univ, Fintype.card_fin]
  have hinjOn : Set.InjOn (degreeEnum S) ((Finset.univ : Finset (Fin n)) : Set (Fin n)) :=
    Finset.card_image_iff.mp hcard
  rw [Finset.coe_univ] at hinjOn
  exact Set.injOn_univ.mp hinjOn

theorem orderedRepresentativeProjection_offDiagonalProjection
    (c : OrderedCoefficient n) :
    orderedRepresentativeProjection n (offDiagonalProjection n c)
      = orderedRepresentativeProjection n c := by
  apply lp.ext
  funext t
  by_cases h : t ∈ degreeRange n
  · obtain ⟨S, rfl⟩ := h
    have hmem : degreeEnum S ∈ degreeRange n := ⟨S, rfl⟩
    rw [orderedRepresentativeProjection_apply, Set.indicator_of_mem hmem,
      orderedRepresentativeProjection_apply, Set.indicator_of_mem hmem,
      offDiagonalProjection_apply, if_pos (injective_degreeEnum_tuple n S)]
  · rw [orderedRepresentativeProjection_apply, Set.indicator_of_notMem h,
      orderedRepresentativeProjection_apply, Set.indicator_of_notMem h]

theorem orderedRestrict_offDiagonalProjection (c : OrderedCoefficient n) :
    orderedRestrict n (offDiagonalProjection n c) = orderedRestrict n c := by
  apply (walshOrdered n).injective
  rw [walshOrdered_orderedRestrict, walshOrdered_orderedRestrict,
    orderedRepresentativeProjection_offDiagonalProjection]

/-! ### Equation (46) for the ordered representative -/

theorem offDiagonalProjection_idem' (c : OrderedCoefficient n) :
    offDiagonalProjection n (offDiagonalProjection n c) = offDiagonalProjection n c :=
  congrFun (congrArg (fun T : OrderedCoefficient n →L[ℂ] OrderedCoefficient n =>
    (T : OrderedCoefficient n → OrderedCoefficient n)) (offDiagonalProjection_idem n)) c

theorem offDiagonalProjection_sym (c d : OrderedCoefficient n) :
    inner ℂ (offDiagonalProjection n c) d = inner ℂ c (offDiagonalProjection n d) := by
  rw [lp.inner_eq_tsum (𝕜 := ℂ) (offDiagonalProjection n c) d,
    lp.inner_eq_tsum (𝕜 := ℂ) c (offDiagonalProjection n d)]
  refine tsum_congr fun t => ?_
  by_cases h : Function.Injective t <;> simp [h]

/-- **Equation (46) for a general weight.** Any nonnegative operator on the
ordered coefficients that commutes with the choice of ordered representative
has smaller energy after the passage to that representative. -/
theorem re_inner_orderedRepresentativeProjection_le
    (T : OrderedCoefficient n →L[ℂ] OrderedCoefficient n)
    (hcomm : ∀ c, orderedRepresentativeProjection n (T c)
      = T (orderedRepresentativeProjection n c))
    (hpos : ∀ x : OrderedCoefficient n, 0 ≤ RCLike.re (inner ℂ (T x) x))
    (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (T (orderedRepresentativeProjection n c))
        (orderedRepresentativeProjection n c))
      ≤ RCLike.re (inner ℂ (T c) c) :=
  re_inner_le_of_commuting_projection T (orderedRepresentativeProjection n)
    (orderedRepresentativeProjection_idem n)
    (orderedRepresentativeProjection_sym n) hcomm hpos c

/-- **Equation (46) for the removal of the coincident-row diagonal**, in the
ordered coefficient picture. This is the operator-side companion of the formalizations
`diagonalMultiplierEnergy_le_rawMultiplierEnergy`. -/
theorem re_inner_orderedH_offDiagonalProjection_le {lam : ℝ} (hlam : 0 ≤ lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedH n lam p (offDiagonalProjection n c))
        (offDiagonalProjection n c))
      ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) :=
  re_inner_le_of_commuting_projection (orderedH n lam p) (offDiagonalProjection n)
    (offDiagonalProjection_idem' n) (offDiagonalProjection_sym n)
    (orderedH_comm_offDiagonalProjection n lam p)
    (re_inner_orderedH_nonneg n hlam p) c

/-- **Equation (46) for the ordered representative, with the `H_n` weight.**
Passing from a raw coefficient on ordered, possibly coincident, tuples of lines
to its ordered off-diagonal representative is contractive for the quadratic
form of the multiplier `lambda + theta(P)`. -/
theorem re_inner_orderedH_orderedRepresentativeProjection_le {lam : ℝ}
    (hlam : 0 ≤ lam) (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (orderedH n lam p (orderedRepresentativeProjection n c))
        (orderedRepresentativeProjection n c))
      ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) :=
  re_inner_orderedRepresentativeProjection_le n (orderedH n lam p)
    (orderedH_comm_orderedRepresentativeProjection n lam p)
    (re_inner_orderedH_nonneg n hlam p) c

/-- **The target statement.** Reading a raw ordered coefficient at the sorted
representatives, that is, passing to the Finset-indexed Walsh coefficient of
degree `n`, is contractive for the `H_n` energy. This is the weighted
analogue of `Manhattan.norm_type112DiagonalProjection_le`. -/
theorem re_inner_coeffH_orderedRestrict_le {lam : ℝ} (hlam : 0 ≤ lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (coeffH n lam p (orderedRestrict n c)) (orderedRestrict n c))
      ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) := by
  have hiso : (inner ℂ (coeffH n lam p (orderedRestrict n c))
        (orderedRestrict n c) : ℂ)
      = inner ℂ (orderedH n lam p (orderedRepresentativeProjection n c))
          (orderedRepresentativeProjection n c) := by
    rw [← (walshOrdered n).inner_map_map (coeffH n lam p (orderedRestrict n c))
      (orderedRestrict n c), walshOrdered_coeffH, walshOrdered_orderedRestrict]
  rw [hiso]
  exact re_inner_orderedH_orderedRepresentativeProjection_le n hlam p c

/-- The same, with the left-hand side written as the explicit weighted integral
of (20): the `H`-energy of the ordered representative is at most the raw
`H`-energy. -/
theorem hWeight_integral_orderedRestrict_le {lam : ℝ} (hlam : 0 ≤ lam)
    (p : Fin 2 → ℝ) (c : OrderedCoefficient n) :
    (∑' σ : Fin n → Axis, ∫ t, symbolWeight n lam p σ t *
        ‖((lineIndexFourier n (orderedRestrict n c)) σ) t‖ ^ 2
          ∂(LineTorusMeasure n))
      ≤ RCLike.re (inner ℂ (orderedH n lam p c) c) := by
  rw [← re_inner_coeffH_eq_integral]
  exact re_inner_coeffH_orderedRestrict_le n hlam p c

/-- The image form, for weights carried by an intertwining map: this is the
shape in which the `D_3`-image energy of the paper's Step 3 is compared. -/
theorem re_inner_image_orderedRestrict_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (A : OrderedCoefficient n →L[ℂ] F) (Q N : F →L[ℂ] F)
    (hAP : ∀ c, A (orderedRepresentativeProjection n c) = Q (A c))
    (hidem : ∀ y, Q (Q y) = Q y)
    (hsym : ∀ x y : F, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hcomm : ∀ y, Q (N y) = N (Q y))
    (hpos : ∀ y : F, 0 ≤ RCLike.re (inner ℂ (N y) y)) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ (N (A (orderedRepresentativeProjection n c)))
        (A (orderedRepresentativeProjection n c)))
      ≤ RCLike.re (inner ℂ (N (A c)) (A c)) :=
  re_inner_image_le_of_intertwining A (orderedRepresentativeProjection n) Q N
    hAP hidem hsym hcomm hpos c

end Ordered

end Manhattan.Glue
