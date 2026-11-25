import Manhattan.Paper.SymmetricIso

/-!
# Lemma 5.3: projecting the degree-three coefficient onto distinct indices

`lem:distinct` (`manuscript.tex:1212-1221`): for a coefficient `k̃` of type
`112` whose two row indices may coincide, and `k = Π₃ k̃`, the difference
`Π₂ D̃₂* k̃ - D₂* k` has only a mixed component, and its squared `H⁻¹` norm is
at most `C ⟨k̃, M k̃⟩`.

By Lemma 5.1, `D₂ = Π₃ D̃₂ Π₂`, so `D₂* = Π₂ D̃₂* Π₃` and the difference is
`Π₂ D̃₂* ℓ` with `ℓ = (I - Π₃) k̃`, the part of `k̃` at coincident row indices.
This file proves the first clause in position space
(`rawLowerDifference_apply_eq_zero`): removing the column sign from `ℓ` lands on
coincident row indices, which `Π₂` removes, and removing a row sign lands on a
mixed index.
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

/-! ### Coefficients of type `112` -/

/-- The raw coefficient of type `112` with normalized coefficient function `K`,
in position space. -/
def type112Coeff (K : Lp ℂ 2 (LineTorusMeasure 3)) : OrderedCoefficient 3 :=
  (orderedFourierEquiv 3).symm (type112Freq K)

theorem orderedFourier_type112Coeff (K : Lp ℂ 2 (LineTorusMeasure 3)) :
    orderedFourier 3 (type112Coeff K) = type112Freq K := by
  rw [← orderedFourierEquiv_apply, type112Coeff, LinearIsometryEquiv.apply_symm_apply]

/-- The value of an ordered coefficient at a tuple is the Fourier coefficient
of its line-frequency coefficient in the sector of the tuple's axis pattern. -/
theorem apply_eq_inner_orderedFourier (n : ℕ) (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) :
    c t = inner ℂ (mFourierLp 2 (tupleCoord t)) ((orderedFourier n c) (tuplePattern t)) := by
  have h1 : c t = inner ℂ (lp.single 2 t (1 : ℂ)) c := by
    rw [lp.inner_single_left]
    simp
  rw [h1, ← (orderedFourier n).inner_map_map, orderedFourier_single, one_smul,
    orderedFreqFamily, lp.inner_single_left]

/-- The three axis patterns of a coefficient of type `112`. -/
def IsType112Pattern (σ : Fin 3 → Axis) : Prop :=
  σ = ![Axis.horizontal, Axis.horizontal, Axis.vertical] ∨
    σ = ![Axis.horizontal, Axis.vertical, Axis.horizontal] ∨
    σ = ![Axis.vertical, Axis.horizontal, Axis.horizontal]

instance (σ : Fin 3 → Axis) : Decidable (IsType112Pattern σ) := by
  unfold IsType112Pattern
  infer_instance

theorem type112Coeff_apply_of_not (K : Lp ℂ 2 (LineTorusMeasure 3)) (t : Fin 3 → LineIndex)
    (ht : ¬ IsType112Pattern (tuplePattern t)) : type112Coeff K t = 0 := by
  rw [apply_eq_inner_orderedFourier, orderedFourier_type112Coeff, type112Freq_apply]
  simp only [IsType112Pattern, not_or] at ht
  rw [if_neg ht.1, if_neg ht.2.1, if_neg ht.2.2, add_zero, add_zero, inner_zero_right]

/-! ### The raw lowering in position space -/

theorem rawLower_apply (n : ℕ) (p : Fin 2 → ℝ) (k : OrderedCoefficient (n + 1))
    (v : Fin n → LineIndex) :
    rawLower n p k v = ((n + 1 : ℕ) : ℂ) *
      inner ℂ (rawRaise n p (lp.single 2 v (1 : ℂ))) k := by
  rw [rawLower, smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    ← ContinuousLinearMap.adjoint_inner_right]
  congr 1
  rw [lp.inner_single_left]
  simp

/-- A tuple in the support of the raw raising of a single tuple `v` carries an
origin line in some slot, and deleting it leaves a translate of `v`. -/
theorem rawRaise_single_ne_zero {n : ℕ} {p : Fin 2 → ℝ} {v : Fin n → LineIndex}
    {u : Fin (n + 1) → LineIndex} (hu : rawRaise n p (lp.single 2 v (1 : ℂ)) u ≠ 0) :
    ∃ (i : Fin 2) (r : Fin (n + 1)), u r = originLine i ∧
      (tupleTranslate n (-Operator.axisVector i) (Fin.removeNth r u) = v ∨
        tupleTranslate n (Operator.axisVector i) (Fin.removeNth r u) = v) := by
  classical
  rw [rawRaise_apply] at hu
  have hu' := right_ne_zero_of_mul hu
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu'
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  by_cases hur : u r = originLine i
  · rw [if_pos hur, orderedRaiseShift_apply] at hr
    refine ⟨i, r, hur, ?_⟩
    by_contra hne
    push Not at hne
    apply hr
    rw [lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply, if_neg hne.1,
      if_neg hne.2]
    ring
  · rw [if_neg hur] at hr
    exact absurd rfl hr

theorem rawLower_apply_eq_zero {n : ℕ} {p : Fin 2 → ℝ} {k : OrderedCoefficient (n + 1)}
    {v : Fin n → LineIndex}
    (h : ∀ u : Fin (n + 1) → LineIndex, rawRaise n p (lp.single 2 v (1 : ℂ)) u ≠ 0 → k u = 0) :
    rawLower n p k v = 0 := by
  rw [rawLower_apply, lp.inner_eq_tsum]
  have : (fun u => inner ℂ ((rawRaise n p (lp.single 2 v (1 : ℂ))) u) (k u)) = fun _ => 0 := by
    funext u
    by_cases hu : rawRaise n p (lp.single 2 v (1 : ℂ)) u = 0
    · rw [hu, inner_zero_left]
    · rw [h u hu, inner_zero_right]
  rw [this, tsum_zero, mul_zero]

/-! ### The difference has only a mixed component -/

theorem sub_offDiagonalProjection_apply_of_injective (n : ℕ) (c : OrderedCoefficient n)
    {t : Fin n → LineIndex} (ht : Function.Injective t) :
    (c - offDiagonalProjection n c) t = 0 := by
  rw [lp.coeFn_sub, Pi.sub_apply, offDiagonalProjection_apply, if_pos ht, sub_self]

theorem sub_offDiagonalProjection_apply_of_eq_zero (n : ℕ) (c : OrderedCoefficient n)
    {t : Fin n → LineIndex} (h : c t = 0) :
    (c - offDiagonalProjection n c) t = 0 := by
  rw [lp.coeFn_sub, Pi.sub_apply, offDiagonalProjection_apply]
  split_ifs <;> simp [h]

theorem insertNth_injective {n : ℕ} {r : Fin (n + 1)} {x : LineIndex} {w : Fin n → LineIndex}
    (hw : Function.Injective w) (hx : ∀ a, w a ≠ x) :
    Function.Injective (Fin.insertNth r x w) := by
  intro a b hab
  rcases Fin.eq_self_or_eq_succAbove r a with ha | ⟨a', ha⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove r b with hb | ⟨b', hb⟩ <;> subst ha <;> subst hb
  · rfl
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
    exact absurd hab.symm (hx b')
  · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
    exact absurd hab (hx a')
  · simp only [Fin.insertNth_apply_succAbove] at hab
    rw [hw hab]

theorem removeNth_eq_of_tupleTranslate {n : ℕ} {x : Operator.Lattice}
    {w v : Fin n → LineIndex} (h : tupleTranslate n x w = v) :
    w = tupleTranslate n (-x) v := by
  rw [← h, ← tupleTranslate_symm_apply, Equiv.symm_apply_apply]

/-- **`lem:distinct`, first clause.**  The difference
`Π₂ D̃₂* k̃ - D₂* k = Π₂ D̃₂* (k̃ - Π₃ k̃)` vanishes at every tuple of two
row lines and at every tuple of two column lines: it has only a mixed
component. -/
theorem rawLowerDifference_apply_eq_zero (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3))
    (v : Fin 2 → LineIndex)
    (hv : tuplePattern v = twoRowPattern ∨
      tuplePattern v = ![Axis.vertical, Axis.vertical]) :
    offDiagonalProjection 2 (rawLower 2 p
      (type112Coeff K - offDiagonalProjection 3 (type112Coeff K))) v = 0 := by
  rw [offDiagonalProjection_apply]
  split_ifs with hinj
  · apply rawLower_apply_eq_zero
    intro u hu
    obtain ⟨i, r, hur, htr⟩ := rawRaise_single_ne_zero hu
    obtain ⟨y, hy, hrem⟩ : ∃ y : Operator.Lattice, (y = Operator.axisVector i ∨
        y = -Operator.axisVector i) ∧ Fin.removeNth r u = tupleTranslate 2 y v := by
      rcases htr with h | h
      · exact ⟨Operator.axisVector i, Or.inl rfl, by rw [removeNth_eq_of_tupleTranslate h, neg_neg]⟩
      · exact ⟨-Operator.axisVector i, Or.inr rfl, removeNth_eq_of_tupleTranslate h⟩
    have hu_eq : u = Fin.insertNth r (originLine i) (Fin.removeNth r u) := by
      rw [← hur, Fin.insertNth_self_removeNth]
    have hpat : tuplePattern u = Fin.insertNth r (finAxis i) (tuplePattern v) := by
      rw [hu_eq, tuplePattern_insertNth, hrem, tuplePattern_tupleTranslate]
      rfl
    by_cases h112 : IsType112Pattern (tuplePattern u)
    · have hcase : i = 1 ∧ tuplePattern v = twoRowPattern := by
        rw [hpat] at h112
        rcases hv with hv | hv <;> rw [hv] at h112 ⊢ <;> fin_cases i <;> fin_cases r <;>
          simp (config := { decide := true }) at h112 ⊢
      obtain ⟨hi, hvpat⟩ := hcase
      apply sub_offDiagonalProjection_apply_of_injective
      rw [hu_eq, hrem]
      refine insertNth_injective ((injective_tupleTranslate_iff 2 y v).mpr hinj) fun a ha => ?_
      have h1 : (tupleTranslate 2 y v a).1 = Axis.horizontal := by
        have h2 : (v a).1 = twoRowPattern a := congrFun hvpat a
        have h3 : (tupleTranslate 2 y v a).1 = (v a).1 := rfl
        rw [h3, h2]
        fin_cases a <;> rfl
      rw [ha, hi] at h1
      exact absurd h1 (by decide)
    · exact sub_offDiagonalProjection_apply_of_eq_zero 3 _ (type112Coeff_apply_of_not K u h112)
  · rfl

/-! ### Coefficients at coincident row indices -/

/-- The index of a coefficient of type `112` at coincident row indices. -/
def coincidentTuple (k : Fin 2 → ℤ) : Fin 3 → LineIndex :=
  ![(Axis.horizontal, k 0), (Axis.horizontal, k 0), (Axis.vertical, k 1)]

theorem coincidentTuple_injective : Function.Injective coincidentTuple := by
  intro k k' h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [coincidentTuple, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Prod.mk.injEq, true_and] at h0 h2
  funext j
  fin_cases j
  · exact h0
  · exact h2

/-- The monomials of `T³` constant along the anti-diagonal of the two row
frequencies. -/
def coincidentFamily (k : Fin 2 → ℤ) : Lp ℂ 2 (LineTorusMeasure 3) :=
  mFourierLp 2 ![k 0, k 0, k 1]

theorem orthonormal_coincidentFamily : Orthonormal ℂ coincidentFamily := by
  have h := (orthonormal_mFourier (d := Fin 3)).comp (fun k : Fin 2 → ℤ => ![k 0, k 0, k 1])
    (by
      intro k k' hk
      have h0 := congrFun hk 0
      have h2 := congrFun hk 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons] at h0 h2
      funext j
      fin_cases j
      · exact h0
      · exact h2)
  exact h

/-- Reading a function of `(α, β)` as the function `(θ₀, θ₁, θ₂) ↦ Y(θ₀ + θ₁, θ₂)`
of the two row frequencies and the column frequency, on the Fourier basis. -/
def coincidentLift : Lp ℂ 2 (LineTorusMeasure 2) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure 3) :=
  orthonormal_coincidentFamily.orthogonalFamily.linearIsometry.comp
    (mFourierBasis (d := Fin 2)).repr.toLinearIsometry

theorem coincidentLift_mFourierLp (k : Fin 2 → ℤ) :
    coincidentLift (mFourierLp 2 k) = mFourierLp 2 ![k 0, k 0, k 1] := by
  classical
  have hb : (mFourierBasis (d := Fin 2)).repr (mFourierLp 2 k) = lp.single 2 k 1 := by
    rw [← coe_mFourierBasis, HilbertBasis.repr_self]
  show orthonormal_coincidentFamily.orthogonalFamily.linearIsometry
    ((mFourierBasis (d := Fin 2)).repr (mFourierLp 2 k)) = _
  rw [hb, OrthogonalFamily.linearIsometry_apply_single]
  simp [coincidentFamily]

/-! ### Sectors and slot integrals of monomials -/

/-- The tuples of one axis pattern. -/
def patternSet (n : ℕ) (σ : Fin n → Axis) : Set (Fin n → LineIndex) := {t | tuplePattern t = σ}

/-- The sector `σ` of the line-frequency coefficient only sees the tuples of
axis pattern `σ`. -/
theorem orderedFourier_patternProjection (n : ℕ) (σ : Fin n → Axis) (c : OrderedCoefficient n) :
    (orderedFourier n (l2SupportProjection (patternSet n σ) c)) σ = (orderedFourier n c) σ := by
  classical
  refine l2_ext_on_single
    ((freqEval n σ).comp ((orderedFourier n).toContinuousLinearMap.comp
      (l2SupportProjection (patternSet n σ))))
    ((freqEval n σ).comp (orderedFourier n).toContinuousLinearMap) (fun t => ?_) c
  change (orderedFourier n (l2SupportProjection (patternSet n σ) (lp.single 2 t (1 : ℂ)))) σ =
    (orderedFourier n (lp.single 2 t (1 : ℂ))) σ
  by_cases ht : tuplePattern t = σ
  · have : l2SupportProjection (patternSet n σ) (lp.single 2 t (1 : ℂ)) = lp.single 2 t 1 := by
      apply lp.ext
      funext u
      rw [l2SupportProjection_apply]
      by_cases hu : u = t
      · subst hu
        rw [Set.indicator_of_mem (show u ∈ patternSet n σ from ht)]
      · rw [lp.single_apply, Pi.single_apply, if_neg hu]
        by_cases hu' : u ∈ patternSet n σ
        · rw [Set.indicator_of_mem hu', lp.single_apply, Pi.single_apply, if_neg hu]
        · rw [Set.indicator_of_notMem hu']
    rw [this]
  · have : l2SupportProjection (patternSet n σ) (lp.single 2 t (1 : ℂ)) = 0 := by
      apply lp.ext
      funext u
      rw [l2SupportProjection_apply]
      by_cases hu : u ∈ patternSet n σ
      · rw [Set.indicator_of_mem hu, lp.single_apply, Pi.single_apply, if_neg]
        · rfl
        · rintro rfl
          exact ht hu
      · rw [Set.indicator_of_notMem hu]
        rfl
    rw [this, map_zero, orderedFourier_single, one_smul, orderedFreqFamily,
      lp.single_apply_ne _ _ _ (Ne.symm ht)]
    rfl

theorem orderedFourier_sector_congr (n : ℕ) (σ : Fin n → Axis) {c c' : OrderedCoefficient n}
    (h : ∀ t, tuplePattern t = σ → c t = c' t) :
    (orderedFourier n c) σ = (orderedFourier n c') σ := by
  have hP : l2SupportProjection (patternSet n σ) c = l2SupportProjection (patternSet n σ) c' := by
    apply lp.ext
    funext t
    rw [l2SupportProjection_apply, l2SupportProjection_apply]
    by_cases ht : t ∈ patternSet n σ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact h t ht
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  rw [← orderedFourier_patternProjection n σ c, ← orderedFourier_patternProjection n σ c', hP]

theorem inner_mFourierLp_eq (n : ℕ) (j m : Fin n → ℤ) :
    inner ℂ (mFourierLp 2 j) (mFourierLp 2 m : Lp ℂ 2 (LineTorusMeasure n)) =
      if j = m then 1 else 0 := by
  have := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin n))) j m
  exact this

/-- The slot integral of a monomial. -/
theorem slotIntegral_mFourierLp (n : ℕ) (r : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    slotIntegral n r (mFourierLp 2 m) =
      if m r = 0 then mFourierLp 2 (Fin.removeNth r m) else 0 := by
  classical
  apply (mFourierBasis (d := Fin n)).repr.injective
  apply lp.ext
  funext j
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, coe_mFourierBasis,
    inner_slotIntegral, torusRemove_mFourierLp, inner_mFourierLp_eq]
  split_ifs with h1 h2 h2
  · rw [inner_mFourierLp_eq, if_pos]
    rw [← h1, Fin.removeNth_insertNth]
  · exact absurd (h1 ▸ Fin.insertNth_apply_same _ _ _) h2
  · rw [inner_mFourierLp_eq, if_neg]
    intro hj
    apply h1
    rw [hj, ← h2, Fin.insertNth_self_removeNth]
  · rw [inner_zero_right]

/-! ### Symmetry of the coefficient of type `112` -/

theorem torusPerm_torusPerm (n : ℕ) (π π' : Equiv.Perm (Fin n)) (f : Lp ℂ 2 (LineTorusMeasure n)) :
    torusPerm n π (torusPerm n π' f) = torusPerm n (π * π') f := by
  apply Lp.ext
  have h := (measurePreserving_torusPermMap n π).quasiMeasurePreserving.ae_eq_comp
    (coeFn_torusPerm n π' f)
  filter_upwards [coeFn_torusPerm n π (torusPerm n π' f), h, coeFn_torusPerm n (π * π') f]
    with θ h1 h2 h3
  rw [h1, h3]
  simp only [Function.comp_apply, torusPermMap_apply] at h2
  rw [h2]
  rfl

theorem offDiagonalProjection_slotPermute (n : ℕ) (π : Equiv.Perm (Fin n))
    (c : OrderedCoefficient n) :
    offDiagonalProjection n (slotPermute n π c) = slotPermute n π (offDiagonalProjection n c) := by
  apply lp.ext
  funext t
  rw [offDiagonalProjection_apply, slotPermute_apply, slotPermute_apply,
    offDiagonalProjection_apply]
  have h : Function.Injective (t ∘ π) ↔ Function.Injective t := by
    constructor
    · intro h a b hab
      have := @h (π.symm a) (π.symm b) (by simpa using hab)
      simpa using this
    · intro h
      exact h.comp π.injective
  simp only [h]

/-- The patterns of length three. -/
theorem pattern_cases (σ : Fin 3 → Axis) : σ = ![σ 0, σ 1, σ 2] := by
  funext i
  fin_cases i <;> rfl

theorem torusPerm_one (n : ℕ) (f : Lp ℂ 2 (LineTorusMeasure n)) : torusPerm n 1 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_torusPerm n 1 f] with θ h
  rw [h]
  rfl

theorem type112Freq_slotPermute (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) (π : Equiv.Perm (Fin 3))
    (hπ : π = Equiv.swap 1 2 ∨ π = finRotate 3) (σ : Fin 3 → Axis) :
    torusPerm 3 π ((type112Freq K) (σ ∘ π)) = (type112Freq K) σ := by
  have hclass : ∀ π₁ π₂ : Equiv.Perm (Fin 3), (π₁ = π₂ ∨ π₁ = π₂ * Equiv.swap 0 1) →
      torusPerm 3 π₁ K = torusPerm 3 π₂ K := by
    rintro π₁ π₂ (rfl | rfl)
    · rfl
    · rw [← torusPerm_torusPerm, hK]
  rw [pattern_cases σ]
  rcases hπ with rfl | rfl <;>
  rcases h0 : σ 0 <;> rcases h1 : σ 1 <;> rcases h2 : σ 2 <;>
  simp (config := { decide := true }) only [type112Freq_apply, Function.comp_def, if_true,
    if_false, add_zero, zero_add, map_zero, map_smul, torusPerm_torusPerm] <;>
  first
    | rfl
    | (congr 1; exact hclass _ _ (by decide))
    | (congr 1; conv_rhs => rw [← torusPerm_one 3 K]
       exact hclass _ _ (by decide))

/-! ### The coincident part in line frequencies -/

/-- The part of the coefficient of type `112` at coincident row indices. -/
def coincidentPart (K : Lp ℂ 2 (LineTorusMeasure 3)) : OrderedCoefficient 3 :=
  type112Coeff K - offDiagonalProjection 3 (type112Coeff K)

/-- Its coefficients at `(row a, row a, column c)`, as a function of `(α, β)`. -/
def coincidentProfile (K : Lp ℂ 2 (LineTorusMeasure 3)) : Lp ℂ 2 (LineTorusMeasure 2) :=
  (mFourierBasis (d := Fin 2)).repr.symm
    (l2Restrict coincidentTuple coincidentTuple_injective (coincidentPart K))

theorem coincidentPart_apply_of_injective (K : Lp ℂ 2 (LineTorusMeasure 3))
    {t : Fin 3 → LineIndex} (ht : Function.Injective t) : coincidentPart K t = 0 :=
  sub_offDiagonalProjection_apply_of_injective 3 _ ht

theorem coincidentPart_apply_of_not (K : Lp ℂ 2 (LineTorusMeasure 3)) {t : Fin 3 → LineIndex}
    (ht : ¬ IsType112Pattern (tuplePattern t)) : coincidentPart K t = 0 :=
  sub_offDiagonalProjection_apply_of_eq_zero 3 _ (type112Coeff_apply_of_not K t ht)

/-- The sectors outside the three patterns of type `112` vanish. -/
theorem orderedFourier_coincidentPart_of_not (K : Lp ℂ 2 (LineTorusMeasure 3))
    {σ : Fin 3 → Axis} (hσ : ¬ IsType112Pattern σ) :
    (orderedFourier 3 (coincidentPart K)) σ = 0 := by
  have h := orderedFourier_sector_congr 3 σ (c := coincidentPart K) (c' := 0)
    (fun t ht => by rw [coincidentPart_apply_of_not K (ht ▸ hσ)]; rfl)
  rw [h]
  simp

/-- The tuples at coincident row indices. -/
abbrev coincidentSet : Set (Fin 3 → LineIndex) := Set.range coincidentTuple

theorem orderedFourier_coincidentProjection (c : OrderedCoefficient 3) :
    (orderedFourier 3 (l2SupportProjection coincidentSet c))
        ![Axis.horizontal, Axis.horizontal, Axis.vertical] =
      coincidentLift ((mFourierBasis (d := Fin 2)).repr.symm
        (l2Restrict coincidentTuple coincidentTuple_injective c)) := by
  classical
  refine l2_ext_on_single
    ((freqEval 3 ![Axis.horizontal, Axis.horizontal, Axis.vertical]).comp
      ((orderedFourier 3).toContinuousLinearMap.comp (l2SupportProjection coincidentSet)))
    (coincidentLift.toContinuousLinearMap.comp
      ((mFourierBasis (d := Fin 2)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
        (l2Restrict coincidentTuple coincidentTuple_injective))) (fun t => ?_) c
  change (orderedFourier 3 (l2SupportProjection coincidentSet (lp.single 2 t (1 : ℂ))))
      ![Axis.horizontal, Axis.horizontal, Axis.vertical] =
    coincidentLift ((mFourierBasis (d := Fin 2)).repr.symm
      (l2Restrict coincidentTuple coincidentTuple_injective (lp.single 2 t (1 : ℂ))))
  by_cases ht : t ∈ coincidentSet
  · obtain ⟨k, rfl⟩ := ht
    have h1 : l2SupportProjection coincidentSet (lp.single 2 (coincidentTuple k) (1 : ℂ)) =
        lp.single 2 (coincidentTuple k) 1 := by
      apply lp.ext
      funext u
      rw [l2SupportProjection_apply]
      by_cases hu : u ∈ coincidentSet
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, lp.single_apply, Pi.single_apply, if_neg]
        rintro rfl
        exact hu ⟨k, rfl⟩
    have h2 : l2Restrict coincidentTuple coincidentTuple_injective
        (lp.single 2 (coincidentTuple k) (1 : ℂ)) = lp.single 2 k 1 := by
      apply lp.ext
      funext j
      rw [l2Restrict_apply, lp.single_apply, lp.single_apply, Pi.single_apply,
        Pi.single_apply]
      simp only [coincidentTuple_injective.eq_iff]
    rw [h1, h2, HilbertBasis.repr_symm_single, coe_mFourierBasis, coincidentLift_mFourierLp,
      orderedFourier_single, one_smul, orderedFreqFamily]
    have hpat : tuplePattern (coincidentTuple k) =
        ![Axis.horizontal, Axis.horizontal, Axis.vertical] := by
      funext a
      fin_cases a <;> rfl
    have hcoord : tupleCoord (coincidentTuple k) = ![k 0, k 0, k 1] := by
      funext a
      fin_cases a <;> rfl
    rw [hpat, lp.single_apply_self, hcoord]
  · have h1 : l2SupportProjection coincidentSet (lp.single 2 t (1 : ℂ)) = 0 := by
      apply lp.ext
      funext u
      rw [l2SupportProjection_apply]
      by_cases hu : u ∈ coincidentSet
      · rw [Set.indicator_of_mem hu, lp.single_apply, Pi.single_apply, if_neg]
        · rfl
        · rintro rfl
          exact ht hu
      · rw [Set.indicator_of_notMem hu]
        rfl
    have h2 : l2Restrict coincidentTuple coincidentTuple_injective
        (lp.single 2 t (1 : ℂ)) = 0 := by
      apply lp.ext
      funext j
      rw [l2Restrict_apply, lp.single_apply, Pi.single_apply, if_neg]
      · rfl
      · intro h
        exact ht ⟨j, h⟩
    rw [h1, h2]
    simp

theorem orderedFourier_coincidentPart_hhv (K : Lp ℂ 2 (LineTorusMeasure 3)) :
    (orderedFourier 3 (coincidentPart K)) ![Axis.horizontal, Axis.horizontal, Axis.vertical] =
      coincidentLift (coincidentProfile K) := by
  rw [coincidentProfile, ← orderedFourier_coincidentProjection]
  refine orderedFourier_sector_congr 3 _ fun t ht => ?_
  rw [l2SupportProjection_apply]
  by_cases hc : t ∈ coincidentSet
  · rw [Set.indicator_of_mem hc]
  · rw [Set.indicator_of_notMem hc]
    apply coincidentPart_apply_of_injective
    have h0 : (t 0).1 = Axis.horizontal := congrFun ht 0
    have h1 : (t 1).1 = Axis.horizontal := congrFun ht 1
    have h2 : (t 2).1 = Axis.vertical := congrFun ht 2
    have h01 : t 0 ≠ t 1 := by
      intro h
      apply hc
      refine ⟨![(t 0).2, (t 2).2], ?_⟩
      funext a
      fin_cases a
      · exact Prod.ext h0.symm rfl
      · show ((Axis.horizontal, (t 0).2) : LineIndex) = t 1
        rw [h]
        exact Prod.ext h1.symm rfl
      · exact Prod.ext h2.symm rfl
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | exact absurd hab h01
      | exact absurd hab.symm h01
      | (exfalso; have := congrArg Prod.fst hab; simp_all)

theorem dense_span_mFourierLp (n : ℕ) :
    Dense (Submodule.span ℂ (Set.range (mFourierLp (d := Fin n) 2)) :
      Set (Lp ℂ 2 (LineTorusMeasure n))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact span_mFourierLp_closure_eq_top (by norm_num)

/-- Integrating the coincident lift over either row frequency integrates the
profile over `α`. -/
theorem slotIntegral_coincidentLift (r : Fin 3) (hr : r = 0 ∨ r = 1)
    (Y : Lp ℂ 2 (LineTorusMeasure 2)) :
    slotIntegral 2 r (coincidentLift Y) = torusRemove 1 0 (slotIntegral 1 0 Y) := by
  have h : (slotIntegral 2 r).comp coincidentLift.toContinuousLinearMap =
      (torusRemove 1 0).toContinuousLinearMap.comp (slotIntegral 1 0) := by
    refine ContinuousLinearMap.ext_on (dense_span_mFourierLp 2) ?_
    rintro _ ⟨k, rfl⟩
    show slotIntegral 2 r (coincidentLift (mFourierLp 2 k)) =
      torusRemove 1 0 (slotIntegral 1 0 (mFourierLp 2 k))
    rw [coincidentLift_mFourierLp, slotIntegral_mFourierLp, slotIntegral_mFourierLp]
    have hk : (![k 0, k 0, k 1] : Fin 3 → ℤ) r = k 0 := by
      rcases hr with rfl | rfl <;> rfl
    rw [hk]
    split_ifs with h0
    · rw [torusRemove_mFourierLp]
      congr 1
      funext a
      rcases hr with rfl | rfl <;> fin_cases a <;> simp [Fin.removeNth, Fin.insertNth, h0] <;> rfl
    · rw [map_zero]
  exact congrArg (fun T => T Y) h

/-! ### The mixed component in line frequencies -/

theorem slotPermute_type112Coeff (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) (π : Equiv.Perm (Fin 3))
    (hπ : π = Equiv.swap 1 2 ∨ π = finRotate 3) :
    slotPermute 3 π (type112Coeff K) = type112Coeff K := by
  apply (orderedFourier 3).injective
  apply lp.ext
  funext σ
  rw [orderedFourier_slotPermute, orderedFourier_type112Coeff,
    type112Freq_slotPermute K hK π hπ σ]

theorem slotPermute_coincidentPart (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) (π : Equiv.Perm (Fin 3))
    (hπ : π = Equiv.swap 1 2 ∨ π = finRotate 3) :
    slotPermute 3 π (coincidentPart K) = coincidentPart K := by
  rw [coincidentPart, map_sub, ← offDiagonalProjection_slotPermute,
    slotPermute_type112Coeff K hK π hπ]

theorem orderedFourier_coincidentPart_hvh (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (orderedFourier 3 (coincidentPart K)) ![Axis.horizontal, Axis.vertical, Axis.horizontal] =
      torusPerm 3 (Equiv.swap 1 2) (coincidentLift (coincidentProfile K)) := by
  conv_lhs => rw [← slotPermute_coincidentPart K hK (Equiv.swap 1 2) (Or.inl rfl)]
  rw [orderedFourier_slotPermute, ← orderedFourier_coincidentPart_hhv]
  rw [show (![Axis.horizontal, Axis.vertical, Axis.horizontal] ∘ ⇑(Equiv.swap (1 : Fin 3) 2) :
    Fin 3 → Axis) = ![Axis.horizontal, Axis.horizontal, Axis.vertical] by
      funext a; fin_cases a <;> rfl]

/-- The difference `Π₂ D̃₂* k̃ - D₂* k` of `lem:distinct`. -/
def rawLowerDifference (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3)) : OrderedCoefficient 2 :=
  offDiagonalProjection 2 (rawLower 2 p (coincidentPart K))

/-- **The mixed component of the difference**: in the sector of a row sign
followed by a column sign it is `-3i sin(β)` times the integral of the
coincident profile over `α`, independent of the row frequency. -/
theorem orderedFourier_rawLowerDifference_mixed (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (orderedFourier 2 (rawLowerDifference p K)) mixedPattern =
      (3 : ℂ) • contMul 2 (star (raisingSymbolMap 2 p 0 mixedPattern))
        (torusRemove 1 0 (slotIntegral 1 0 (coincidentProfile K))) := by
  have hsec : (orderedFourier 2 (rawLowerDifference p K)) mixedPattern =
      (orderedFourier 2 (rawLower 2 p (coincidentPart K))) mixedPattern := by
    refine orderedFourier_sector_congr 2 mixedPattern fun t ht => ?_
    rw [rawLowerDifference, offDiagonalProjection_apply, if_pos]
    intro a b hab
    have h0 : (t 0).1 = Axis.horizontal := congrFun ht 0
    have h1 : (t 1).1 = Axis.vertical := congrFun ht 1
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso; have := congrArg Prod.fst hab; simp_all)
  rw [hsec, orderedFourier_rawLower, rawLowerFreq_apply, rawLowerSector, Fin.sum_univ_three]
  simp only [sum_univ_axis]
  have e0 : (Fin.insertNth 0 Axis.horizontal mixedPattern : Fin 3 → Axis) =
      ![Axis.horizontal, Axis.horizontal, Axis.vertical] := by
    funext a; fin_cases a <;> rfl
  have e1 : (Fin.insertNth 1 Axis.horizontal mixedPattern : Fin 3 → Axis) =
      ![Axis.horizontal, Axis.horizontal, Axis.vertical] := by
    funext a; fin_cases a <;> rfl
  have e2 : (Fin.insertNth 2 Axis.horizontal mixedPattern : Fin 3 → Axis) =
      ![Axis.horizontal, Axis.vertical, Axis.horizontal] := by
    funext a; fin_cases a <;> rfl
  have z0 : (orderedFourier 3 (coincidentPart K)) (Fin.insertNth 0 Axis.vertical mixedPattern) = 0 :=
    orderedFourier_coincidentPart_of_not K (by
      rw [show (Fin.insertNth 0 Axis.vertical mixedPattern : Fin 3 → Axis) =
        ![Axis.vertical, Axis.horizontal, Axis.vertical] by funext a; fin_cases a <;> rfl]
      decide)
  have z1 : (orderedFourier 3 (coincidentPart K)) (Fin.insertNth 1 Axis.vertical mixedPattern) = 0 :=
    orderedFourier_coincidentPart_of_not K (by
      rw [show (Fin.insertNth 1 Axis.vertical mixedPattern : Fin 3 → Axis) =
        ![Axis.horizontal, Axis.vertical, Axis.vertical] by funext a; fin_cases a <;> rfl]
      decide)
  have z2 : (orderedFourier 3 (coincidentPart K)) (Fin.insertNth 2 Axis.vertical mixedPattern) = 0 :=
    orderedFourier_coincidentPart_of_not K (by
      rw [show (Fin.insertNth 2 Axis.vertical mixedPattern : Fin 3 → Axis) =
        ![Axis.horizontal, Axis.vertical, Axis.vertical] by funext a; fin_cases a <;> rfl]
      decide)
  rw [z0, z1, z2, e0, e1, e2, orderedFourier_coincidentPart_hhv,
    orderedFourier_coincidentPart_hvh K hK,
    slotIntegral_torusPerm 2 _ (r' := 1) (fun θ => by funext a; fin_cases a <;> rfl),
    slotIntegral_coincidentLift 0 (Or.inl rfl), slotIntegral_coincidentLift 1 (Or.inr rfl)]
  simp only [map_zero, contMul_zero, add_zero, show axisIndex Axis.horizontal = 0 from rfl]
  module

/-! ### A weighted Cauchy-Schwarz inequality -/

theorem sq_norm_integral_le_weighted {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ} {a : α → ℝ} (ha : ∀ x, 0 < a x) {B : ℝ}
    (hB : ∀ x, (a x)⁻¹ ≤ B) (hma : Measurable a) (hf : AEStronglyMeasurable f μ)
    (hfa : Integrable (fun x => a x * ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ (∫ x, (a x)⁻¹ ∂μ) * ∫ x, a x * ‖f x‖ ^ 2 ∂μ := by
  set F : α → ℝ := fun x => Real.sqrt (a x) * ‖f x‖ with hF
  set G : α → ℝ := fun x => (Real.sqrt (a x))⁻¹ with hG
  have hFG : ∀ x, F x * G x = ‖f x‖ := by
    intro x
    have : 0 < Real.sqrt (a x) := Real.sqrt_pos.mpr (ha x)
    simp only [hF, hG]
    field_simp
  have hF2 : ∀ x, F x ^ 2 = a x * ‖f x‖ ^ 2 := by
    intro x
    simp only [hF]
    rw [mul_pow, Real.sq_sqrt (ha x).le]
  have hG2 : ∀ x, G x ^ 2 = (a x)⁻¹ := by
    intro x
    simp only [hG]
    rw [inv_pow, Real.sq_sqrt (ha x).le]
  have hFm : AEStronglyMeasurable F μ :=
    (hma.sqrt.aestronglyMeasurable).mul hf.norm
  have hGm : AEStronglyMeasurable G μ := (hma.sqrt.inv).aestronglyMeasurable
  have hFL : MemLp F (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num, memLp_two_iff_integrable_sq hFm]
    simpa only [hF2] using hfa
  have hGL : MemLp G (ENNReal.ofReal 2) μ := by
    refine MemLp.of_bound hGm (Real.sqrt (max B 0)) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by simp only [hG]; positivity)]
    simp only [hG]
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt ((hB x).trans (le_max_left _ _))
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => by simp only [hF]; positivity)
    (Filter.Eventually.of_forall fun x => by simp only [hG]; positivity) hFL hGL
  simp only [hFG, Real.rpow_two, hF2, hG2] at hH
  have h1 : ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
  have hI1 : 0 ≤ ∫ x, a x * ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (ha x).le (sq_nonneg _)
  have hI2 : 0 ≤ ∫ x, (a x)⁻¹ ∂μ := integral_nonneg fun x => (inv_pos.mpr (ha x)).le
  have h2 : (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ (∫ x, a x * ‖f x‖ ^ 2 ∂μ) * ∫ x, (a x)⁻¹ ∂μ := by
    have h0 : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg fun x => norm_nonneg _
    calc (∫ x, ‖f x‖ ∂μ) ^ 2
        ≤ ((∫ x, a x * ‖f x‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, (a x)⁻¹ ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := pow_le_pow_left₀ h0 hH 2
      _ = (∫ x, a x * ‖f x‖ ^ 2 ∂μ) * ∫ x, (a x)⁻¹ ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hI1,
            ← Real.rpow_mul hI2]
          norm_num
  calc ‖∫ x, f x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by linarith

/-! ### The estimate of the mixed component -/

theorem totalFrequency_rowCol_zero (p : Fin 2 → ℝ) (r : Fin 2) (t : UnitAddCircle)
    (θ : UnitAddTorus (Fin 1)) :
    totalFrequency 2 p (Fin.insertNth r Axis.horizontal ![Axis.vertical]) (Fin.insertNth r t θ) 0 =
      p 0 + 2 * Real.pi * torusLift (θ 0) := by
  have h := totalFrequency_insertNth p 0 r ![Axis.vertical] t θ 0
  rw [axisShift_finAxis_self] at h
  rw [show Axis.horizontal = finAxis 0 from rfl, h]
  simp [totalFrequency, lineFrequency, lineShiftVector_axisVector, finAxis]

theorem totalFrequency_rowCol_one (p : Fin 2 → ℝ) (r : Fin 2) (t : UnitAddCircle)
    (θ : UnitAddTorus (Fin 1)) :
    totalFrequency 2 p (Fin.insertNth r Axis.horizontal ![Axis.vertical]) (Fin.insertNth r t θ) 1 =
      p 1 + 2 * Real.pi * torusLift t := by
  have h := totalFrequency_insertNth p 0 r ![Axis.vertical] t θ 1
  rw [show (1 : Fin 2) = otherAxisIndex 0 from rfl, axisShift_finAxis_other] at h
  rw [show Axis.horizontal = finAxis 0 from rfl, show (1 : Fin 2) = otherAxisIndex 0 from rfl, h]
  simp [totalFrequency, lineFrequency, lineShiftVector_axisVector, finAxis, otherAxisIndex]

theorem continuous_insertNth_prod {n : ℕ} (r : Fin (n + 1)) :
    Continuous fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
      Fin.insertNth (α := fun _ => UnitAddCircle) r z.1 z.2 :=
  Continuous.finInsertNth r continuous_fst continuous_snd

theorem sin_sq_mul_line_sq_le {mu x : ℝ} (hmu : 0 < mu) (hx : Real.sin x ^ 2 ≤ 2 * mu) :
    Real.sin x ^ 2 * ((Real.sqrt (mu * (mu + 2)))⁻¹) ^ 2 ≤ 1 := by
  rw [inv_pow, Real.sq_sqrt (by positivity), ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith

theorem integrable_insertNth_comp' {E : Type*} [NormedAddCommGroup E] (n : ℕ) (r : Fin (n + 1))
    {g : UnitAddTorus (Fin (n + 1)) → E} (hg : Integrable g (LineTorusMeasure (n + 1))) :
    Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin n) => g (Fin.insertNth r z.1 z.2))
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r
  have hmp := (measurePreserving_slotSplit n r).symm e
  exact (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr hg

theorem integral_insertNth_comp' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (r : Fin (n + 1)) (g : UnitAddTorus (Fin (n + 1)) → E) :
    ∫ z, g (Fin.insertNth r z.1 z.2)
        ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) =
      ∫ θ, g θ ∂(LineTorusMeasure (n + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r
  have hmp := (measurePreserving_slotSplit n r).symm e
  exact hmp.integral_comp e.symm.measurableEmbedding g

theorem integral_insertNth_comp_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Fin 2) (g : UnitAddTorus (Fin 2) → E) :
    ∫ θ, g θ ∂(LineTorusMeasure 2) =
      ∫ z, g (Fin.insertNth r z.1 z.2)
        ∂((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure 1)) :=
  (integral_insertNth_comp' 1 r g).symm

/-- The row-and-column pattern with the row sign in slot `r`. -/
abbrev rowColPattern (r : Fin 2) : Fin 2 → Axis := Fin.insertNth r Axis.horizontal ![Axis.vertical]

theorem integrable_norm_sq_slice (n : ℕ) (r : Fin (n + 1)) (Y : Lp ℂ 2 (LineTorusMeasure (n + 1)))
    {m : UnitAddTorus (Fin (n + 1)) → ℝ} (hm : Measurable m) {C : ℝ} (hC : ∀ z, |m z| ≤ C) :
    Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
        m (Fin.insertNth r z.1 z.2) * ‖(Y : UnitAddTorus (Fin (n + 1)) → ℂ) (Fin.insertNth r z.1 z.2)‖ ^ 2)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure n)) := by
  have hY : Integrable (fun z : UnitAddTorus (Fin (n + 1)) =>
      m z * ‖(Y : UnitAddTorus (Fin (n + 1)) → ℂ) z‖ ^ 2) (LineTorusMeasure (n + 1)) :=
    (integrable_norm_sq_lp (n + 1) Y).bdd_mul (c := C) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)
  exact integrable_insertNth_comp' n r hY

/-- **The mixed-sector estimate of `lem:distinct`.**  A degree-two coefficient
whose line-frequency coefficient in the sector of a row sign and a column sign
is `-3i sin(β)` times the `α`-integral of a profile `Y(α, β)` has squared `H⁻¹`
norm in that sector at most `9/κ` times the quadratic form of `M` at `Y`. -/
theorem integral_mixedSector_le {kappa : ℝ} (hkappa : 0 < kappa) {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (r : Fin 2) (Y : Lp ℂ 2 (LineTorusMeasure 2)) :
    ∫ θ, (symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ *
        ‖(((3 : ℂ) • contMul 2 (star (raisingSymbolMap 2 p 0 (rowColPattern r)))
          (torusRemove 1 r (slotIntegral 1 0 Y)) : Lp ℂ 2 (LineTorusMeasure 2)) :
            UnitAddTorus (Fin 2) → ℂ) θ‖ ^ 2 ∂(LineTorusMeasure 2) ≤
      9 / kappa * ∫ z, Estimates.multiplier kappa q (totalFrequency 2 p (rowColPattern 0) z) *
        ‖(Y : UnitAddTorus (Fin 2) → ℂ) z‖ ^ 2 ∂(LineTorusMeasure 2) := by
  set h : Lp ℂ 2 (LineTorusMeasure 1) := slotIntegral 1 0 Y with hh
  set c : UnitAddTorus (Fin 1) → ℝ := fun θ' => p 0 + 2 * Real.pi * torusLift (θ' 0) with hc
  set μ : UnitAddTorus (Fin 1) → ℝ := fun θ' => q.lambda + Estimates.dispersion (c θ') with hμ
  have hμpos : ∀ θ', 0 < μ θ' := fun θ' => by
    have := Estimates.dispersion_nonneg (c θ')
    show 0 < q.lambda + Estimates.dispersion (c θ')
    linarith
  set J : UnitAddTorus (Fin 1) → ℝ := fun θ' => (Real.sqrt (μ θ' * (μ θ' + 2)))⁻¹ with hJ
  set S : UnitAddTorus (Fin 1) → ℝ := fun θ' => ∫ α, Estimates.multiplier kappa q
      (totalFrequency 2 p (rowColPattern 0) (Fin.insertNth 0 α θ')) *
      ‖(Y : UnitAddTorus (Fin 2) → ℂ) (Fin.insertNth 0 α θ')‖ ^ 2
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) with hS
  -- the weight in the row-and-column sector
  have hw : ∀ (t : UnitAddCircle) (θ' : UnitAddTorus (Fin 1)),
      symbolWeight 2 q.lambda p (rowColPattern r) (Fin.insertNth r t θ') =
        μ θ' + Estimates.dispersion (p 1 + 2 * Real.pi * torusLift t) := by
    intro t θ'
    rw [symbolWeight_def, Estimates.theta, totalFrequency_rowCol_zero, totalFrequency_rowCol_one]
    simp only [hμ, hc]
    ring
  have hMt : ∀ (α : UnitAddCircle) (θ' : UnitAddTorus (Fin 1)),
      kappa * (μ θ' + Estimates.dispersion (p 1 + 2 * Real.pi * torusLift α)) ≤
        Estimates.multiplier kappa q
          (totalFrequency 2 p (rowColPattern 0) (Fin.insertNth 0 α θ')) := by
    intro α θ'
    have h0 := totalFrequency_rowCol_zero p 0 α θ'
    have h1 := totalFrequency_rowCol_one p 0 α θ'
    rw [Estimates.multiplier, Estimates.theta, h0, h1]
    have hs0 := abs_nonneg (Real.sin ((p 0 + 2 * Real.pi * torusLift (θ' 0)) / 2))
    have hs1 := abs_nonneg (Real.sin ((p 1 + 2 * Real.pi * torusLift α) / 2))
    simp only [hμ, hc]
    nlinarith
  -- Step A: the integrand
  set R : C(UnitAddTorus (Fin 2), ℂ) := raisingSymbolMap 2 p 0 (rowColPattern r) with hR
  have hRnorm : ∀ (t : UnitAddCircle) (θ' : UnitAddTorus (Fin 1)),
      ‖R (Fin.insertNth r t θ')‖ ^ 2 = Real.sin (c θ') ^ 2 := by
    intro t θ'
    rw [hR, raisingSymbolMap_apply, totalFrequency_rowCol_zero, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hA : ∀ᵐ θ ∂(LineTorusMeasure 2),
      (symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ *
        ‖(((3 : ℂ) • contMul 2 (star R) (torusRemove 1 r h) : Lp ℂ 2 (LineTorusMeasure 2)) :
            UnitAddTorus (Fin 2) → ℂ) θ‖ ^ 2 =
      ((symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ * (9 * ‖R θ‖ ^ 2)) *
          ‖(h : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth r θ)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_smul (3 : ℂ) (contMul 2 (star R) (torusRemove 1 r h)),
      coeFn_contMul (star R) (torusRemove 1 r h), coeFn_torusRemove 1 r h] with θ h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul, norm_mul, norm_mul, ContinuousMap.star_apply,
      norm_star]
    norm_num
    ring
  rw [integral_congr_ae hA]
  -- the bounded factor
  have hbdd : ∀ θ, ‖(symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ * (9 * ‖R θ‖ ^ 2)‖ ≤
      q.lambda⁻¹ * 9 := by
    intro θ
    have hw0 := symbolWeight_ge 2 q.lambda p (rowColPattern r) θ
    have hR1 : ‖R θ‖ ≤ 1 := by
      rw [hR, raisingSymbolMap_apply, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hinv : (symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ ≤ q.lambda⁻¹ :=
      inv_anti₀ hlam hw0
    rw [Real.norm_of_nonneg (by
      have := symbolWeight_pos 2 hlam p (rowColPattern r) θ
      positivity)]
    have hR2 : ‖R θ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (R θ)]
    have : 0 ≤ (symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ :=
      (inv_pos.mpr (symbolWeight_pos 2 hlam p (rowColPattern r) θ)).le
    nlinarith
  have hcontW : Continuous fun θ => (symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ *
      (9 * ‖R θ‖ ^ 2) :=
    (continuous_inv_symbolWeight 2 hlam p _).mul (continuous_const.mul
      ((continuous_norm.comp R.continuous).pow 2))
  have hintB : Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin 1) =>
      ((symbolWeight 2 q.lambda p (rowColPattern r) (Fin.insertNth r z.1 z.2))⁻¹ *
        (9 * ‖R (Fin.insertNth r z.1 z.2)‖ ^ 2)) *
        ‖(h : UnitAddTorus (Fin 1) → ℂ) z.2‖ ^ 2)
      ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure 1)) := by
    have hg : Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin 1) =>
        (1 : ℝ) * ‖(h : UnitAddTorus (Fin 1) → ℂ) z.2‖ ^ 2)
        ((AddCircle.haarAddCircle : Measure UnitAddCircle).prod (LineTorusMeasure 1)) :=
      (integrable_const (1 : ℝ)).mul_prod (integrable_norm_sq_lp 1 h)
    refine (hg.bdd_mul (c := q.lambda⁻¹ * 9) (f := fun z : UnitAddCircle × UnitAddTorus (Fin 1) =>
      (symbolWeight 2 q.lambda p (rowColPattern r) (Fin.insertNth r z.1 z.2))⁻¹ *
        (9 * ‖R (Fin.insertNth r z.1 z.2)‖ ^ 2)) ?_ ?_).congr ?_
    · exact (hcontW.comp (continuous_insertNth_prod r)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => hbdd _
    · exact Filter.Eventually.of_forall fun z => by simp only [one_mul]
  -- Step B: integrate over the row frequency
  have hB : ∫ θ, ((symbolWeight 2 q.lambda p (rowColPattern r) θ)⁻¹ * (9 * ‖R θ‖ ^ 2)) *
        ‖(h : UnitAddTorus (Fin 1) → ℂ) (Fin.removeNth r θ)‖ ^ 2 ∂(LineTorusMeasure 2) =
      ∫ θ', J θ' * (9 * Real.sin (c θ') ^ 2 * ‖(h : UnitAddTorus (Fin 1) → ℂ) θ'‖ ^ 2)
        ∂(LineTorusMeasure 1) := by
    rw [integral_insertNth_comp_two r]
    simp only [Fin.removeNth_insertNth]
    rw [integral_prod_symm _ hintB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ' => ?_)
    simp only [hRnorm, hw]
    rw [integral_mul_const, integral_mul_const, integral_haar_inv_dispersion (hμpos θ') (p 1)]
    simp only [hJ]
    ring
  rw [hB]
  -- Step D: the right side as an iterated integral
  set Mt : UnitAddTorus (Fin 2) → ℝ := fun z =>
    Estimates.multiplier kappa q (totalFrequency 2 p (rowColPattern 0) z) with hMtdef
  have hMtc : Continuous Mt := continuous_multiplier_totalFrequency 2 kappa q p _
  have hMtb : ∀ z, |Mt z| ≤ kappa * (q.lambda + 8) := fun z => by
    rw [← Real.norm_eq_abs]
    exact multiplier_le_bound hkappa.le hlam.le _
  have hMtpos : ∀ z, kappa * q.lambda ≤ Mt z := fun z => by
    have := symbolWeight_ge 2 q.lambda p (rowColPattern 0) z
    have h2 := Estimates.theta_nonneg (totalFrequency 2 p (rowColPattern 0) z)
    simp only [hMtdef, Estimates.multiplier]
    have hs0 := abs_nonneg (Real.sin (totalFrequency 2 p (rowColPattern 0) z 0 / 2))
    have hs1 := abs_nonneg (Real.sin (totalFrequency 2 p (rowColPattern 0) z 1 / 2))
    nlinarith
  have hslice := integrable_norm_sq_slice 1 0 Y hMtc.measurable hMtb
  have hYint : Integrable (Y : UnitAddTorus (Fin 2) → ℂ) (LineTorusMeasure 2) :=
    (Lp.memLp Y).integrable one_le_two
  have hYslice := integrable_insertNth_comp' 1 0 hYint
  have hD : ∫ z, Mt z * ‖(Y : UnitAddTorus (Fin 2) → ℂ) z‖ ^ 2 ∂(LineTorusMeasure 2) =
      ∫ θ', S θ' ∂(LineTorusMeasure 1) := by
    rw [integral_insertNth_comp_two 0,
      integral_prod_symm _ hslice]
  rw [hD, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ' => ?_)
    (hslice.integral_prod_right.const_mul _) ?_
  · have : 0 ≤ J θ' := by simp only [hJ]; positivity
    positivity
  -- Step C: Cauchy-Schwarz in `α`
  filter_upwards [coeFn_slotIntegral 1 0 Y, hslice.prod_left_ae, hYslice.prod_left_ae]
    with θ' h1 h2 h3
  have hapos : ∀ α : UnitAddCircle, 0 < Mt (Fin.insertNth 0 α θ') := fun α =>
    lt_of_lt_of_le (mul_pos hkappa hlam) (hMtpos _)
  have hcs := sq_norm_integral_le_weighted (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (f := fun α => (Y : UnitAddTorus (Fin 2) → ℂ) (Fin.insertNth 0 α θ'))
    (a := fun α => Mt (Fin.insertNth 0 α θ')) hapos (B := (kappa * q.lambda)⁻¹)
    (fun α => inv_anti₀ (mul_pos hkappa hlam) (hMtpos _))
    (hMtc.comp (Continuous.finInsertNth 0 continuous_id continuous_const)).measurable
    h3.aestronglyMeasurable h2
  have hw0 : ∀ α : UnitAddCircle, symbolWeight 2 q.lambda p (rowColPattern 0)
      (Fin.insertNth 0 α θ') = μ θ' + Estimates.dispersion (p 1 + 2 * Real.pi * torusLift α) := by
    intro α
    rw [symbolWeight_def, Estimates.theta, totalFrequency_rowCol_zero, totalFrequency_rowCol_one]
    simp only [hμ, hc]
    ring
  have hinv : ∫ α, (Mt (Fin.insertNth 0 α θ'))⁻¹ ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      ≤ kappa⁻¹ * J θ' := by
    have hcomp : ∀ α : UnitAddCircle, (Mt (Fin.insertNth 0 α θ'))⁻¹ ≤ kappa⁻¹ *
        (symbolWeight 2 q.lambda p (rowColPattern 0) (Fin.insertNth 0 α θ'))⁻¹ := by
      intro α
      rw [← mul_inv]
      refine inv_anti₀ (mul_pos hkappa (symbolWeight_pos 2 hlam p _ _)) ?_
      rw [hw0]
      exact hMt α θ'
    have hc1 : Continuous fun α : UnitAddCircle => (Mt (Fin.insertNth 0 α θ'))⁻¹ :=
      (hMtc.comp (Continuous.finInsertNth 0 continuous_id continuous_const)).inv₀
        fun α => (hapos α).ne'
    have hc2 : Continuous fun α : UnitAddCircle => kappa⁻¹ *
        (symbolWeight 2 q.lambda p (rowColPattern 0) (Fin.insertNth 0 α θ'))⁻¹ :=
      continuous_const.mul ((continuous_inv_symbolWeight 2 hlam p _).comp
        (Continuous.finInsertNth 0 continuous_id continuous_const))
    calc ∫ α, (Mt (Fin.insertNth 0 α θ'))⁻¹ ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
        ≤ ∫ α, kappa⁻¹ * (symbolWeight 2 q.lambda p (rowColPattern 0)
            (Fin.insertNth 0 α θ'))⁻¹ ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) :=
          integral_mono (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcomp
      _ = kappa⁻¹ * J θ' := by
          rw [integral_const_mul]
          simp only [hw0]
          rw [integral_haar_inv_dispersion (hμpos θ') (p 1)]
  have hsin : Real.sin (c θ') ^ 2 ≤ 2 * μ θ' := by
    have h1 := Real.sin_sq_add_cos_sq (c θ')
    have h2 := Real.neg_one_le_cos (c θ')
    have h3 := Real.cos_le_one (c θ')
    simp only [hμ, Estimates.dispersion]
    nlinarith
  have hsj := sin_sq_mul_line_sq_le (hμpos θ') hsin
  have hJnn : 0 ≤ J θ' := by simp only [hJ]; positivity
  have hSnn : 0 ≤ S θ' := integral_nonneg fun α =>
    mul_nonneg (hapos α).le (sq_nonneg _)
  rw [h1]
  have hsq : ‖∫ α, (Y : UnitAddTorus (Fin 2) → ℂ) (Fin.insertNth 0 α θ')
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)‖ ^ 2 ≤ kappa⁻¹ * J θ' * S θ' :=
    hcs.trans (mul_le_mul_of_nonneg_right hinv hSnn)
  calc J θ' * (9 * Real.sin (c θ') ^ 2 * ‖∫ α, (Y : UnitAddTorus (Fin 2) → ℂ)
        (Fin.insertNth 0 α θ') ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)‖ ^ 2)
      ≤ J θ' * (9 * Real.sin (c θ') ^ 2 * (kappa⁻¹ * J θ' * S θ')) := by
        gcongr
    _ = 9 / kappa * (Real.sin (c θ') ^ 2 * J θ' ^ 2) * S θ' := by ring
    _ ≤ 9 / kappa * 1 * S θ' := by gcongr
    _ = 9 / kappa * S θ' := by ring

/-- Integrating the reordered coincident lift over a row slot, in the
column-and-row sector. -/
theorem slotIntegral_torusPerm_coincidentLift (r : Fin 3) (π : Equiv.Perm (Fin 3))
    (hrπ : (r = 0 ∧ π = Equiv.swap 1 2) ∨ (r = 1 ∧ π = finRotate 3) ∨ (r = 2 ∧ π = finRotate 3))
    (Y : Lp ℂ 2 (LineTorusMeasure 2)) :
    slotIntegral 2 r (torusPerm 3 π (coincidentLift Y)) = torusRemove 1 1 (slotIntegral 1 0 Y) := by
  have h : (slotIntegral 2 r).comp ((torusPerm 3 π).toContinuousLinearMap.comp
      coincidentLift.toContinuousLinearMap) =
      (torusRemove 1 1).toContinuousLinearMap.comp (slotIntegral 1 0) := by
    refine ContinuousLinearMap.ext_on (dense_span_mFourierLp 2) ?_
    rintro _ ⟨k, rfl⟩
    show slotIntegral 2 r (torusPerm 3 π (coincidentLift (mFourierLp 2 k))) =
      torusRemove 1 1 (slotIntegral 1 0 (mFourierLp 2 k))
    rw [coincidentLift_mFourierLp, torusPerm_mFourierLp, slotIntegral_mFourierLp,
      slotIntegral_mFourierLp]
    have hk : ((![k 0, k 0, k 1] : Fin 3 → ℤ) ∘ π.symm) r = k 0 := by
      rcases hrπ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [hk]
    split_ifs with h0
    · rw [torusRemove_mFourierLp]
      congr 1
      funext a
      rcases hrπ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases a <;>
        simp [Fin.removeNth, Fin.insertNth, h0] <;> rfl
    · rw [map_zero]
  exact congrArg (fun T => T Y) h

theorem orderedFourier_coincidentPart_vhh (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (orderedFourier 3 (coincidentPart K)) ![Axis.vertical, Axis.horizontal, Axis.horizontal] =
      torusPerm 3 (finRotate 3) (coincidentLift (coincidentProfile K)) := by
  conv_lhs => rw [← slotPermute_coincidentPart K hK (finRotate 3) (Or.inr rfl)]
  rw [orderedFourier_slotPermute, ← orderedFourier_coincidentPart_hhv]
  rw [show (![Axis.vertical, Axis.horizontal, Axis.horizontal] ∘ ⇑(finRotate 3) :
    Fin 3 → Axis) = ![Axis.horizontal, Axis.horizontal, Axis.vertical] by
      funext a; fin_cases a <;> rfl]

/-- The mixed component of the difference in the sector of a column sign
followed by a row sign. -/
theorem orderedFourier_rawLowerDifference_colRow (p : Fin 2 → ℝ)
    (K : Lp ℂ 2 (LineTorusMeasure 3)) (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (orderedFourier 2 (rawLowerDifference p K)) (rowColPattern 1) =
      (3 : ℂ) • contMul 2 (star (raisingSymbolMap 2 p 0 (rowColPattern 1)))
        (torusRemove 1 1 (slotIntegral 1 0 (coincidentProfile K))) := by
  have hpat : (rowColPattern 1 : Fin 2 → Axis) = ![Axis.vertical, Axis.horizontal] := by
    funext a; fin_cases a <;> rfl
  have hsec : (orderedFourier 2 (rawLowerDifference p K)) (rowColPattern 1) =
      (orderedFourier 2 (rawLower 2 p (coincidentPart K))) (rowColPattern 1) := by
    refine orderedFourier_sector_congr 2 _ fun t ht => ?_
    rw [rawLowerDifference, offDiagonalProjection_apply, if_pos]
    rw [hpat] at ht
    intro a b hab
    have h0 : (t 0).1 = Axis.vertical := congrFun ht 0
    have h1 : (t 1).1 = Axis.horizontal := congrFun ht 1
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso; have := congrArg Prod.fst hab; simp_all)
  rw [hsec, orderedFourier_rawLower, rawLowerFreq_apply, rawLowerSector, Fin.sum_univ_three]
  simp only [sum_univ_axis]
  have e0 : (Fin.insertNth 0 Axis.horizontal (rowColPattern 1) : Fin 3 → Axis) =
      ![Axis.horizontal, Axis.vertical, Axis.horizontal] := by
    funext a; fin_cases a <;> rfl
  have e1 : (Fin.insertNth 1 Axis.horizontal (rowColPattern 1) : Fin 3 → Axis) =
      ![Axis.vertical, Axis.horizontal, Axis.horizontal] := by
    funext a; fin_cases a <;> rfl
  have e2 : (Fin.insertNth 2 Axis.horizontal (rowColPattern 1) : Fin 3 → Axis) =
      ![Axis.vertical, Axis.horizontal, Axis.horizontal] := by
    funext a; fin_cases a <;> rfl
  have z : ∀ r : Fin 3,
      (orderedFourier 3 (coincidentPart K)) (Fin.insertNth r Axis.vertical (rowColPattern 1)) = 0 := by
    intro r
    apply orderedFourier_coincidentPart_of_not K
    fin_cases r <;> decide
  rw [z 0, z 1, z 2, e0, e1, e2, orderedFourier_coincidentPart_hvh K hK,
    orderedFourier_coincidentPart_vhh K hK,
    slotIntegral_torusPerm_coincidentLift 0 _ (Or.inl ⟨rfl, rfl⟩),
    slotIntegral_torusPerm_coincidentLift 1 _ (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    slotIntegral_torusPerm_coincidentLift 2 _ (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  simp only [map_zero, contMul_zero, add_zero, show axisIndex Axis.horizontal = 0 from rfl]
  module

/-! ### The coincident lift intertwines the multipliers -/

theorem contMul_mFourier (n : ℕ) (j : Fin n → ℤ) (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (mFourier j) u = charMul n j u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (mFourier j) u, coeFn_charMul n j u] with t h1 h2
  rw [h1, h2]

theorem coincidentLift_charMul (y : Fin 2 → ℤ) (Y : Lp ℂ 2 (LineTorusMeasure 2)) :
    coincidentLift (charMul 2 ![y 1, y 0] Y) = charMul 3 ![y 1, y 1, y 0] (coincidentLift Y) := by
  have h : coincidentLift.toContinuousLinearMap.comp
      (charMul 2 ![y 1, y 0]).toLinearIsometry.toContinuousLinearMap =
      (charMul 3 ![y 1, y 1, y 0]).toLinearIsometry.toContinuousLinearMap.comp
        coincidentLift.toContinuousLinearMap := by
    refine ContinuousLinearMap.ext_on (dense_span_mFourierLp 2) ?_
    rintro _ ⟨k, rfl⟩
    show coincidentLift (charMul 2 ![y 1, y 0] (mFourierLp 2 k)) =
      charMul 3 ![y 1, y 1, y 0] (coincidentLift (mFourierLp 2 k))
    rw [charMul_mFourierLp, coincidentLift_mFourierLp, coincidentLift_mFourierLp,
      charMul_mFourierLp]
    congr 1
    funext a
    fin_cases a <;> rfl
  exact congrArg (fun T => T Y) h

theorem lineShiftVector_hhv (y : Fin 2 → ℤ) :
    lineShiftVector 3 y ![Axis.horizontal, Axis.horizontal, Axis.vertical] = ![y 1, y 1, y 0] := by
  funext a
  fin_cases a <;> rfl

theorem lineShiftVector_rowCol0 (y : Fin 2 → ℤ) :
    lineShiftVector 2 y (rowColPattern 0) = ![y 1, y 0] := by
  funext a
  fin_cases a <;> rfl

/-- Multiplication by `m(P)` in the pattern of two row signs and a column sign,
after the coincident lift, is the lift of multiplication by `m(P)` in the
pattern of a row sign and a column sign. -/
theorem contMul_coincidentLift (p : Fin 2 → ℝ) (m : C(UnitAddTorus (Fin 2), ℂ))
    (Y : Lp ℂ 2 (LineTorusMeasure 2)) :
    contMul 3 (m.comp (totalFrequencyMap 3 p ![Axis.horizontal, Axis.horizontal, Axis.vertical]))
        (coincidentLift Y) =
      coincidentLift (contMul 2 (m.comp (totalFrequencyMap 2 p (rowColPattern 0))) Y) := by
  set A : C(UnitAddTorus (Fin 2), ℂ) →ₗ[ℂ] Lp ℂ 2 (LineTorusMeasure 3) :=
    { toFun := fun m => contMul 3 (m.comp (totalFrequencyMap 3 p
        ![Axis.horizontal, Axis.horizontal, Axis.vertical])) (coincidentLift Y) -
        coincidentLift (contMul 2 (m.comp (totalFrequencyMap 2 p (rowColPattern 0))) Y)
      map_add' := fun m m' => by
        rw [ContinuousMap.add_comp, ContinuousMap.add_comp, contMul_add_left, contMul_add_left,
          map_add]
        abel
      map_smul' := fun a m => by
        rw [ContinuousMap.smul_comp, ContinuousMap.smul_comp, contMul_smul_left,
          contMul_smul_left, map_smul, RingHom.id_apply, smul_sub] } with hA
  have hbound : ∀ m, ‖A m‖ ≤ (‖Y‖ + ‖Y‖) * ‖m‖ := by
    intro m
    show ‖contMul 3 _ (coincidentLift Y) - coincidentLift (contMul 2 _ Y)‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [LinearIsometry.norm_map, add_mul]
    refine add_le_add ((norm_contMul_le _ _).trans ?_) ((norm_contMul_le _ _).trans ?_)
    · rw [LinearIsometry.norm_map, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_comp_totalFrequencyMap_le 3 p _ m) (norm_nonneg _)
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_comp_totalFrequencyMap_le 2 p _ m) (norm_nonneg _)
  have hAcont : Continuous A := (A.mkContinuous _ hbound).continuous
  have hspan : Submodule.span ℂ (Set.range (mFourier (d := Fin 2))) ≤ LinearMap.ker A := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show contMul 3 _ (coincidentLift Y) - coincidentLift (contMul 2 _ Y) = 0
    rw [sub_eq_zero]
    have e : ∀ (n : ℕ) (σ : Fin n → Axis) (u : Lp ℂ 2 (LineTorusMeasure n)),
        contMul n ((mFourier y).comp (totalFrequencyMap n p σ)) u =
          Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)) •
            charMul n (lineShiftVector n y σ) u := by
      intro n σ u
      apply Lp.ext
      filter_upwards [coeFn_contMul ((mFourier y).comp (totalFrequencyMap n p σ)) u,
        Lp.coeFn_smul (Complex.exp (Complex.I * ((∑ i : Fin 2, (y i : ℝ) * p i : ℝ) : ℂ)))
          (charMul n (lineShiftVector n y σ) u),
        coeFn_charMul n (lineShiftVector n y σ) u] with t h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, ContinuousMap.comp_apply]
      show mFourier y (totalFrequencyPoint n p σ t) * _ = _
      rw [mFourier_totalFrequencyPoint]
      ring
    rw [e, e, lineShiftVector_hhv, lineShiftVector_rowCol0, map_smul, coincidentLift_charMul]
  have hclosed : IsClosed (LinearMap.ker A : Set C(UnitAddTorus (Fin 2), ℂ)) :=
    isClosed_eq hAcont continuous_const
  have htop : (⊤ : Submodule ℂ C(UnitAddTorus (Fin 2), ℂ)) ≤ LinearMap.ker A := by
    rw [← span_mFourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan hclosed
  have hm := htop (Submodule.mem_top (x := m))
  rw [LinearMap.mem_ker] at hm
  exact sub_eq_zero.mp hm

/-! ### `lem:distinct` -/

theorem re_inner_orderedMultiplier_multiplier (n : ℕ) (p : Fin 2 → ℝ) (kappa : ℝ)
    (q : Estimates.Parameters) (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ c (orderedMultiplier n p (multiplierMapC kappa q) c)) =
      ∑ σ : Fin n → Axis, ∫ t, Estimates.multiplier kappa q (totalFrequency n p σ t) *
        ‖((orderedFourier n c) σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [← (orderedFourierEquiv n).inner_map_map, orderedFourierEquiv_apply,
    orderedFourierEquiv_apply, orderedFourier_orderedMultiplier,
    re_inner_freqMultiplier_multiplier]

theorem re_inner_orderedMultiplier_hInv (n : ℕ) (p : Fin 2 → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (c : OrderedCoefficient n) :
    RCLike.re (inner ℂ c (orderedMultiplier n p (hInvMap hlam) c)) =
      ∑ σ : Fin n → Axis, ∫ t, (symbolWeight n lam p σ t)⁻¹ *
        ‖((orderedFourier n c) σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [← (orderedFourierEquiv n).inner_map_map, orderedFourierEquiv_apply,
    orderedFourierEquiv_apply, orderedFourier_orderedMultiplier, re_inner_freqMultiplier]

theorem multiplier_nonneg' {kappa : ℝ} (hkappa : 0 ≤ kappa) {q : Estimates.Parameters}
    (hlam : 0 ≤ q.lambda) (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) :
    0 ≤ Estimates.multiplier kappa q (totalFrequency n p σ t) :=
  Estimates.multiplier_nonneg hkappa hlam _

theorem re_inner_contMul_real (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ))
    (G : UnitAddTorus (Fin n) → ℝ) (hg : ∀ t, g t = G t) (u : Lp ℂ 2 (LineTorusMeasure n)) :
    RCLike.re (inner ℂ u (contMul n g u)) =
      ∫ t, G t * ‖(u : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_contMul g u] with t ht
  rw [ht, RCLike.inner_apply, hg, mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

/-- The multiplier form of the coincident profile is at most that of the
coefficient. -/
theorem coincidentProfile_le {kappa : ℝ} (hkappa : 0 ≤ kappa) {q : Estimates.Parameters}
    (hlam : 0 ≤ q.lambda) (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3)) :
    ∫ z, Estimates.multiplier kappa q (totalFrequency 2 p (rowColPattern 0) z) *
        ‖(coincidentProfile K : UnitAddTorus (Fin 2) → ℂ) z‖ ^ 2 ∂(LineTorusMeasure 2) ≤
      RCLike.re (inner ℂ (type112Coeff K)
        (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K))) := by
  set Y := coincidentProfile K with hY
  set m := multiplierMapC kappa q with hm
  set M := orderedMultiplier 3 p m with hM
  set ℓ := coincidentPart K with hℓ
  set kt := type112Coeff K with hkt
  set P3 := offDiagonalProjection 3 with hP3
  have hval : ∀ (n : ℕ) (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)),
      (m.comp (totalFrequencyMap n p σ)) t =
        ((Estimates.multiplier kappa q (totalFrequency n p σ t) : ℝ) : ℂ) := by
    intro n σ t
    show ((multiplierMap kappa q (totalFrequencyPoint n p σ t) : ℝ) : ℂ) = _
    rw [multiplierMap_totalFrequencyPoint]
  -- the profile form is the form of the `hhv` sector of `ℓ`
  have h1 : ∫ z, Estimates.multiplier kappa q (totalFrequency 2 p (rowColPattern 0) z) *
        ‖(Y : UnitAddTorus (Fin 2) → ℂ) z‖ ^ 2 ∂(LineTorusMeasure 2) =
      ∫ t, Estimates.multiplier kappa q (totalFrequency 3 p
          ![Axis.horizontal, Axis.horizontal, Axis.vertical] t) *
        ‖((orderedFourier 3 ℓ) ![Axis.horizontal, Axis.horizontal, Axis.vertical] :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
    rw [← re_inner_contMul_real 2 _ _ (hval 2 (rowColPattern 0)) Y,
      ← re_inner_contMul_real 3 _ _ (hval 3 _), orderedFourier_coincidentPart_hhv,
      contMul_coincidentLift, LinearIsometry.inner_map_map]
  -- the `hhv` sector is part of the form of `ℓ`
  have h2 : ∫ t, Estimates.multiplier kappa q (totalFrequency 3 p
          ![Axis.horizontal, Axis.horizontal, Axis.vertical] t) *
        ‖((orderedFourier 3 ℓ) ![Axis.horizontal, Axis.horizontal, Axis.vertical] :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) ≤
      RCLike.re (inner ℂ ℓ (M ℓ)) := by
    rw [hM, re_inner_orderedMultiplier_multiplier]
    exact Finset.single_le_sum (f := fun σ => ∫ t, Estimates.multiplier kappa q
        (totalFrequency 3 p σ t) * ‖((orderedFourier 3 ℓ) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3))
      (fun σ _ => integral_nonneg fun t =>
        mul_nonneg (multiplier_nonneg' hkappa hlam 3 p σ t) (sq_nonneg _))
      (Finset.mem_univ _)
  -- the form of `ℓ = (I - Π₃) k̃` is at most that of `k̃`
  have hcomm : ∀ c, P3 (M c) = M (P3 c) := fun c =>
    congrArg (fun T => T c) (offDiagonalProjection_comp_orderedMultiplier 3 p m)
  have hidem : ∀ c, P3 (P3 c) = P3 c := fun c =>
    congrArg (fun T => T c) (offDiagonalProjection_idem 3)
  have hsa : ∀ c d, inner ℂ (P3 c) d = inner ℂ c (P3 d) := by
    intro c d
    have := offDiagonalProjection_isSelfAdjoint 3
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at this
    rw [← ContinuousLinearMap.adjoint_inner_right, this]
  have hsplit : kt = P3 kt + ℓ := by rw [hℓ, coincidentPart]; abel
  have hPl : P3 ℓ = 0 := by rw [hℓ, coincidentPart, map_sub, hidem, sub_self]
  have hx1 : inner ℂ (P3 kt) (M ℓ) = 0 := by
    rw [hsa, hcomm, hPl, map_zero, inner_zero_right]
  have hx2 : inner ℂ ℓ (M (P3 kt)) = 0 := by
    rw [← hcomm, ← hsa, hPl, inner_zero_left]
  have hpos : 0 ≤ RCLike.re (inner ℂ (P3 kt) (M (P3 kt))) := by
    rw [hM, re_inner_orderedMultiplier_multiplier]
    exact Finset.sum_nonneg fun σ _ => integral_nonneg fun t =>
      mul_nonneg (multiplier_nonneg' hkappa hlam 3 p σ t) (sq_nonneg _)
  have h3 : RCLike.re (inner ℂ ℓ (M ℓ)) ≤ RCLike.re (inner ℂ kt (M kt)) := by
    conv_rhs => rw [hsplit]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hx1, hx2, map_add, map_add,
      map_add]
    simp only [map_zero, add_zero, zero_add]
    linarith
  rw [h1]
  exact h2.trans h3

/-- **`lem:distinct`** (`manuscript.tex:1212-1221`).  Let `k̃` be the coefficient
of type `112` with normalized coefficient function `K(r, r', β)`, symmetric in
the two row frequencies and without the restriction that the two row indices
be distinct, and let `k = Π₃ k̃`.  Then the difference
`Π₂ D̃₂* k̃ - D₂* k = Π₂ D̃₂* (k̃ - Π₃ k̃)` has only a mixed component, and its
squared `H⁻¹` norm `2! ⟨·, (λ + θ(P))⁻¹ ·⟩` is at most `6/κ` times
`⟨k̃, M k̃⟩ = 3! ⟨k̃, M k̃⟩_{ℓ²}` for the multiplier `M` of `eq:M`. -/
theorem lemma_distinct {kappa : ℝ} (hkappa : 0 < kappa) {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (K : Lp ℂ 2 (LineTorusMeasure 3))
    (hK : torusPerm 3 (Equiv.swap 0 1) K = K) :
    (∀ v : Fin 2 → LineIndex, (tuplePattern v = twoRowPattern ∨
        tuplePattern v = ![Axis.vertical, Axis.vertical]) → rawLowerDifference p K v = 0) ∧
      2 * RCLike.re (inner ℂ (rawLowerDifference p K)
          (orderedMultiplier 2 p (hInvMap hlam) (rawLowerDifference p K))) ≤
        6 / kappa * (6 * RCLike.re (inner ℂ (type112Coeff K)
          (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K)))) := by
  have hsupp : ∀ v : Fin 2 → LineIndex, (tuplePattern v = twoRowPattern ∨
      tuplePattern v = ![Axis.vertical, Axis.vertical]) → rawLowerDifference p K v = 0 :=
    fun v hv => rawLowerDifference_apply_eq_zero p K v hv
  refine ⟨hsupp, ?_⟩
  set D := rawLowerDifference p K with hD
  set Y := coincidentProfile K with hY
  set I := ∫ z, Estimates.multiplier kappa q (totalFrequency 2 p (rowColPattern 0) z) *
      ‖(Y : UnitAddTorus (Fin 2) → ℂ) z‖ ^ 2 ∂(LineTorusMeasure 2) with hI
  have hmix0 : (mixedPattern : Fin 2 → Axis) = rowColPattern 0 := by
    funext a; fin_cases a <;> rfl
  have hsec0 : ∀ σ : Fin 2 → Axis, σ ≠ rowColPattern 0 → σ ≠ rowColPattern 1 →
      (orderedFourier 2 D) σ = 0 := by
    intro σ h0 h1
    have hσ : σ = twoRowPattern ∨ σ = ![Axis.vertical, Axis.vertical] := by
      have hc : σ = ![σ 0, σ 1] := by funext a; fin_cases a <;> rfl
      rw [hc] at h0 h1 ⊢
      revert h0 h1
      rcases σ 0 <;> rcases σ 1 <;> intro h0 h1 <;>
        first
          | exact Or.inl rfl
          | exact Or.inr rfl
          | exact absurd (by decide) h0
          | exact absurd (by decide) h1
    have h := orderedFourier_sector_congr 2 σ (c := D) (c' := 0)
      (fun t ht => by rw [hsupp t (ht ▸ hσ)]; rfl)
    rw [h]
    simp
  rw [re_inner_orderedMultiplier_hInv,
    Fintype.sum_eq_add (rowColPattern 0) (rowColPattern 1) (by decide) (fun σ hσ => by
      rw [hsec0 σ hσ.1 hσ.2]
      simp)]
  have hA : ∫ t, (symbolWeight 2 q.lambda p (rowColPattern 0) t)⁻¹ *
      ‖((orderedFourier 2 D) (rowColPattern 0) : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2) ≤ 9 / kappa * I := by
    have h := orderedFourier_rawLowerDifference_mixed p K hK
    rw [hmix0] at h
    rw [h]
    exact integral_mixedSector_le hkappa hlam p 0 Y
  have hB : ∫ t, (symbolWeight 2 q.lambda p (rowColPattern 1) t)⁻¹ *
      ‖((orderedFourier 2 D) (rowColPattern 1) : UnitAddTorus (Fin 2) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 2) ≤ 9 / kappa * I := by
    rw [orderedFourier_rawLowerDifference_colRow p K hK]
    exact integral_mixedSector_le hkappa hlam p 1 Y
  have hC := coincidentProfile_le hkappa.le hlam.le p K
  have hk : 0 < 9 / kappa := by positivity
  have h9 : 9 / kappa * I ≤ 9 / kappa * RCLike.re (inner ℂ (type112Coeff K)
      (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K))) :=
    mul_le_mul_of_nonneg_left hC hk.le
  have e : 6 / kappa * (6 * RCLike.re (inner ℂ (type112Coeff K)
      (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K)))) =
      4 * (9 / kappa * RCLike.re (inner ℂ (type112Coeff K)
        (orderedMultiplier 3 p (multiplierMapC kappa q) (type112Coeff K)))) := by ring
  rw [e]
  linarith

end

end Manhattan.Paper
