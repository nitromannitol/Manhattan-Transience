import Manhattan.Model.LowDegree
import Manhattan.Glue.VectorFourier
import Manhattan.Estimates.Elementary
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# (Hsym) in the concrete model

This file proves the paper's equation (Hsym) for the concrete fair-coin fiber
`Manhattan.concreteFiberEnvironment`: on the homogeneous Walsh subspace of
degree `n`, the operator `H = lambda - S_p` is, after the line-index Fourier
transform (20), multiplication by `lambda + theta P` with
`P = p + q_1 + ... + q_n` the total frequency.

Paper: `manuscript.tex:692-760` and `manuscript.tex:576-600`.
-/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped BigOperators

namespace Manhattan.Glue

/-! ### A translation-compatible linear order on line indices

Equation (20) needs an ordering of the `n` lines of a Walsh index.  Sorting by
axis first and transverse coordinate second is preserved by every lattice
translation, which is what makes the resulting enumeration equivariant. -/

private def axisNum : Axis → ℤ
  | .horizontal => 0
  | .vertical => 1

private theorem axisNum_injective : Function.Injective axisNum := by decide

private def lineKey (l : LineIndex) : ℤ ×ₗ ℤ := toLex (axisNum l.1, l.2)

private theorem lineKey_injective : Function.Injective lineKey := by
  rintro ⟨i, k⟩ ⟨j, m⟩ h
  have h' : ((axisNum i, k) : ℤ × ℤ) = (axisNum j, m) := congrArg ofLex h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  subst h2
  rw [axisNum_injective h1]

/-- The translation-compatible linear order on line indices: axis first,
transverse coordinate second.  Exported (as a non-instance) so that other
files can compute the sorted enumeration `degreeEnum`. -/
abbrev lineOrder : LinearOrder LineIndex :=
  LinearOrder.lift' lineKey lineKey_injective

attribute [local instance] lineOrder

/-- Lines of the same axis are ordered by their transverse coordinate. -/
theorem lineIndex_lt_of_coord_lt {a : Axis} {k m : ℤ} (h : k < m) :
    ((a, k) : LineIndex) < (a, m) := by
  show lineKey (a, k) < lineKey (a, m)
  rw [lineKey, lineKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, h⟩

/-- Horizontal lines precede vertical ones. -/
theorem horizontal_lt_vertical (k m : ℤ) :
    ((Axis.horizontal, k) : LineIndex) < (Axis.vertical, m) := by
  show lineKey (Axis.horizontal, k) < lineKey (Axis.vertical, m)
  rw [lineKey, lineKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (by norm_num [axisNum])

private theorem lineTranslation_strictMono (x : Site) :
    StrictMono (lineTranslation x) := by
  rintro ⟨i, k⟩ ⟨j, m⟩ h
  have h' : lineKey (i, k) < lineKey (j, m) := h
  rw [lineKey, lineKey, Prod.Lex.toLex_lt_toLex] at h'
  show lineKey (lineTranslation x (i, k)) < lineKey (lineTranslation x (j, m))
  simp only [lineTranslation, Equiv.coe_fn_mk, lineKey, Prod.Lex.toLex_lt_toLex]
  rcases h' with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    have hij : i = j := axisNum_injective h1
    subst hij
    simpa using h2

/-! ### The sorted enumeration of a degree-`n` Walsh index -/

/-- The `n` lines of a degree-`n` Walsh index, sorted by axis and then by
transverse coordinate. -/
def degreeEnum {n : ℕ} (S : WalshDegreeIndex n) : Fin n → LineIndex :=
  S.1.orderEmbOfFin S.2

theorem degreeEnum_mem {n : ℕ} (S : WalshDegreeIndex n) (a : Fin n) :
    degreeEnum S a ∈ S.1 :=
  Finset.orderEmbOfFin_mem S.1 S.2 a

theorem range_degreeEnum {n : ℕ} (S : WalshDegreeIndex n) :
    Set.range (degreeEnum S) = (S.1 : Set LineIndex) :=
  Finset.range_orderEmbOfFin S.1 S.2

theorem degreeEnum_injective (n : ℕ) :
    Function.Injective (degreeEnum (n := n)) := by
  intro S T h
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← range_degreeEnum S, ← range_degreeEnum T, h]

/-- Translation of a degree-`n` Walsh index. -/
def translateDegreeIndex (n : ℕ) (x : Operator.Lattice) :
    WalshDegreeIndex n ≃ WalshDegreeIndex n :=
  Equiv.subtypeEquiv (lineTranslation (latticeToSite x)).finsetCongr (fun S => by
    simp [Equiv.finsetCongr_apply])

@[simp] theorem translateDegreeIndex_coe (n : ℕ) (x : Operator.Lattice)
    (S : WalshDegreeIndex n) :
    (translateDegreeIndex n x S).1 = translateWalshIndex x S.1 := rfl

/-- The sorted enumeration is equivariant: translating a Walsh index
translates each of its sorted lines. -/
theorem degreeEnum_translateDegreeIndex {n : ℕ} (x : Operator.Lattice)
    (S : WalshDegreeIndex n) (a : Fin n) :
    degreeEnum (translateDegreeIndex n x S) a =
      lineTranslation (latticeToSite x) (degreeEnum S a) := by
  have hmem : ∀ b : Fin n,
      lineTranslation (latticeToSite x) (degreeEnum S b) ∈
        (translateDegreeIndex n x S).1 := by
    intro b
    rw [translateDegreeIndex_coe, translateWalshIndex, Finset.mem_map]
    exact ⟨degreeEnum S b, degreeEnum_mem S b, rfl⟩
  have hmono : StrictMono fun b : Fin n =>
      lineTranslation (latticeToSite x) (degreeEnum S b) :=
    (lineTranslation_strictMono (latticeToSite x)).comp
      (S.1.orderEmbOfFin S.2).strictMono
  have huniq := Finset.orderEmbOfFin_unique (translateDegreeIndex n x S).2 hmem hmono
  exact (congrFun huniq a).symm

/-! ### The three coefficient spaces and equation (20) -/

/-- Square-summable degree-`n` Finset Walsh coefficients. -/
abbrev DegreeCoefficient (n : ℕ) := ℓ²(WalshDegreeIndex n, ℂ)

/-- Square-summable coefficients indexed by ordered `n`-tuples of lines. -/
abbrev OrderedCoefficient (n : ℕ) := ℓ²(Fin n → LineIndex, ℂ)

/-- The `n`-fold normalized torus of line frequencies. -/
abbrev LineTorusMeasure (n : ℕ) : Measure (UnitAddTorus (Fin n)) :=
  Measure.pi fun _ => (AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- The frequency side of equation (20): an axis pattern for the `n` lines
together with an `L²` function of the `n` line frequencies. -/
abbrev LineFreqL2 (n : ℕ) := ℓ²(Fin n → Axis, Lp ℂ 2 (LineTorusMeasure n))

/-- The axis pattern of an ordered tuple of lines. -/
def tuplePattern {n : ℕ} (t : Fin n → LineIndex) : Fin n → Axis := fun a => (t a).1

/-- The transverse coordinates of an ordered tuple of lines. -/
def tupleCoord {n : ℕ} (t : Fin n → LineIndex) : Fin n → ℤ := fun a => (t a).2

theorem tuple_ext {n : ℕ} {t u : Fin n → LineIndex}
    (h1 : tuplePattern t = tuplePattern u) (h2 : tupleCoord t = tupleCoord u) :
    t = u := by
  funext a
  exact Prod.ext (congrFun h1 a) (congrFun h2 a)

/-- The exponential monomial attached to an ordered tuple of lines: the
character of the tuple's transverse coordinates, placed in the sector of the
tuple's axis pattern.  This is the elementary vector of equation (20). -/
def orderedFreqFamily (n : ℕ) (t : Fin n → LineIndex) : LineFreqL2 n :=
  lp.single 2 (tuplePattern t) (mFourierLp 2 (tupleCoord t))

private theorem orthonormal_l2Single (ι : Type*) [DecidableEq ι] :
    Orthonormal ℂ (fun i : ι => lp.single 2 i (1 : ℂ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left]
  by_cases h : i = j
  · subst h
    simp
  · simp [lp.single_apply, h]

theorem orthonormal_orderedFreqFamily (n : ℕ) :
    Orthonormal ℂ (orderedFreqFamily n) := by
  rw [orthonormal_iff_ite]
  intro t u
  rw [orderedFreqFamily, orderedFreqFamily, lp.inner_single_left]
  by_cases hpat : tuplePattern t = tuplePattern u
  · rw [hpat]
    rw [show (lp.single 2 (tuplePattern u) (mFourierLp 2 (tupleCoord u)) :
        LineFreqL2 n) (tuplePattern u) = mFourierLp 2 (tupleCoord u) from
      lp.single_apply_self 2 _ _]
    have hmF := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin n)))
      (tupleCoord t) (tupleCoord u)
    rw [hmF]
    by_cases hcoord : tupleCoord t = tupleCoord u
    · rw [if_pos hcoord, if_pos (tuple_ext hpat hcoord)]
    · rw [if_neg hcoord, if_neg]
      intro htu
      exact hcoord (by rw [htu])
  · rw [show (lp.single 2 (tuplePattern u) (mFourierLp 2 (tupleCoord u)) :
        LineFreqL2 n) (tuplePattern t) = 0 from
      lp.single_apply_ne 2 _ _ hpat]
    rw [inner_zero_right, if_neg]
    intro htu
    exact hpat (by rw [htu])

/-- Equation (20) on ordered tuples: Fourier series in each line index. -/
def orderedFourier (n : ℕ) : OrderedCoefficient n →ₗᵢ[ℂ] LineFreqL2 n :=
  (orthonormal_orderedFreqFamily n).orthogonalFamily.linearIsometry

@[simp] theorem orderedFourier_single (n : ℕ) (t : Fin n → LineIndex) (a : ℂ) :
    orderedFourier n (lp.single 2 t a) = a • orderedFreqFamily n t := by
  rw [orderedFourier, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Reading a degree-`n` Walsh coefficient as an ordered coefficient through
the sorted enumeration. -/
def walshOrdered (n : ℕ) : DegreeCoefficient n →ₗᵢ[ℂ] OrderedCoefficient n :=
  (((orthonormal_l2Single (Fin n → LineIndex)).comp _
    (degreeEnum_injective n))).orthogonalFamily.linearIsometry

@[simp] theorem walshOrdered_single (n : ℕ) (S : WalshDegreeIndex n) (a : ℂ) :
    walshOrdered n (lp.single 2 S a) = a • lp.single 2 (degreeEnum S) (1 : ℂ) := by
  rw [walshOrdered, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Equation (20) for degree-`n` Finset Walsh coefficients. -/
def lineIndexFourier (n : ℕ) : DegreeCoefficient n →ₗᵢ[ℂ] LineFreqL2 n :=
  (orderedFourier n).comp (walshOrdered n)

@[simp] theorem lineIndexFourier_single (n : ℕ) (S : WalshDegreeIndex n) (a : ℂ) :
    lineIndexFourier n (lp.single 2 S a) = a • orderedFreqFamily n (degreeEnum S) := by
  change orderedFourier n (walshOrdered n (lp.single 2 S a)) = _
  rw [walshOrdered_single, map_smul, orderedFourier_single, one_smul]

/-! ### Extensionality on the standard `l²` vectors -/

private def l2Basis (ι : Type*) : HilbertBasis ι ℂ (ℓ²(ι, ℂ)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

private theorem l2Basis_apply {ι : Type*} [DecidableEq ι] (i : ι) :
    l2Basis ι i = lp.single 2 i (1 : ℂ) :=
  (HilbertBasis.repr_symm_single (l2Basis ι) i).symm

private theorem l2_ext {ι : Type*} [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T U : ℓ²(ι, ℂ) →L[ℂ] E)
    (h : ∀ i : ι, T (lp.single 2 i (1 : ℂ)) = U (lp.single 2 i (1 : ℂ))) :
    T = U := by
  refine ContinuousLinearMap.ext_on (s := Set.range (l2Basis ι)) ?_ ?_
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact (l2Basis ι).dense_span
  rintro _ ⟨i, rfl⟩
  rw [l2Basis_apply]
  exact h i

private theorem l2_ext_apply {ι : Type*} [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T U : ℓ²(ι, ℂ) →L[ℂ] E)
    (h : ∀ i : ι, T (lp.single 2 i (1 : ℂ)) = U (lp.single 2 i (1 : ℂ)))
    (c : ℓ²(ι, ℂ)) : T c = U c := by
  rw [l2_ext T U h]

/-! ### Translations on the three spaces -/

/-- Translation of ordered tuples of lines. -/
def tupleTranslate (n : ℕ) (x : Operator.Lattice) :
    (Fin n → LineIndex) ≃ (Fin n → LineIndex) :=
  Equiv.piCongrRight fun _ : Fin n => lineTranslation (latticeToSite x)

@[simp] theorem tupleTranslate_apply (n : ℕ) (x : Operator.Lattice)
    (t : Fin n → LineIndex) (a : Fin n) :
    tupleTranslate n x t a = lineTranslation (latticeToSite x) (t a) := rfl

/-- Translation of degree-`n` Walsh coefficients. -/
def translateCoeff (n : ℕ) (x : Operator.Lattice) :
    DegreeCoefficient n ≃ₗᵢ[ℂ] DegreeCoefficient n :=
  l2CongrLeft (translateDegreeIndex n x)

/-- Translation of ordered coefficients. -/
def orderedTranslate (n : ℕ) (x : Operator.Lattice) :
    OrderedCoefficient n ≃ₗᵢ[ℂ] OrderedCoefficient n :=
  l2CongrLeft (tupleTranslate n x)

private theorem l2CongrLeft_single {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (i : I) (a : ℂ) :
    l2CongrLeft (E := ℂ) e (lp.single 2 i a) = lp.single 2 (e i) a := by
  apply lp.ext
  funext j
  rw [l2CongrLeft_apply]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases hj : j = e i
  · subst hj
    simp
  · rw [if_neg hj, if_neg]
    intro hji
    exact hj (by rw [← hji, Equiv.apply_symm_apply])

@[simp] theorem translateCoeff_single (n : ℕ) (x : Operator.Lattice)
    (S : WalshDegreeIndex n) (a : ℂ) :
    translateCoeff n x (lp.single 2 S a) =
      lp.single 2 (translateDegreeIndex n x S) a :=
  l2CongrLeft_single _ _ _

@[simp] theorem orderedTranslate_single (n : ℕ) (x : Operator.Lattice)
    (t : Fin n → LineIndex) (a : ℂ) :
    orderedTranslate n x (lp.single 2 t a) =
      lp.single 2 (tupleTranslate n x t) a :=
  l2CongrLeft_single _ _ _

theorem walshOrdered_translateCoeff (n : ℕ) (x : Operator.Lattice)
    (c : DegreeCoefficient n) :
    walshOrdered n (translateCoeff n x c) =
      orderedTranslate n x (walshOrdered n c) := by
  refine l2_ext_apply
    ((walshOrdered n).toContinuousLinearMap.comp
      (translateCoeff n x).toLinearIsometry.toContinuousLinearMap)
    ((orderedTranslate n x).toLinearIsometry.toContinuousLinearMap.comp
      (walshOrdered n).toContinuousLinearMap) ?_ c
  intro S
  change walshOrdered n (translateCoeff n x (lp.single 2 S (1 : ℂ))) =
    orderedTranslate n x (walshOrdered n (lp.single 2 S (1 : ℂ)))
  rw [translateCoeff_single, walshOrdered_single, walshOrdered_single,
    map_smul, orderedTranslate_single]
  congr 2
  funext a
  exact degreeEnum_translateDegreeIndex x S a

/-! ### The frequency-side shift -/

/-- Coordinatewise application of a family of unitaries to a Hilbert sum. -/
def l2CongrRightDep {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : I → (E ≃ₗᵢ[ℂ] E)) : ℓ²(I, E) ≃ₗᵢ[ℂ] ℓ²(I, E) where
  toFun x := ⟨fun i => e i (x i), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, LinearIsometryEquiv.norm_map] using
      x.prop.summable (by norm_num : 0 < ENNReal.toReal 2)⟩
  invFun y := ⟨fun i => (e i).symm (y i), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, LinearIsometryEquiv.norm_map] using
      y.prop.summable (by norm_num : 0 < ENNReal.toReal 2)⟩
  left_inv x := by
    apply lp.ext
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv y := by
    apply lp.ext
    funext i
    exact (e i).apply_symm_apply (y i)
  map_add' x y := by
    apply lp.ext
    funext i
    exact (e i).map_add (x i) (y i)
  map_smul' a x := by
    apply lp.ext
    funext i
    exact (e i).map_smul a (x i)
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    change (∑' i, ‖e i (x i)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (∑' i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
    simp only [LinearIsometryEquiv.norm_map]

@[simp] theorem l2CongrRightDep_apply {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (e : I → (E ≃ₗᵢ[ℂ] E)) (x : ℓ²(I, E)) (i : I) :
    l2CongrRightDep e x i = e i (x i) := rfl

theorem l2CongrRightDep_single {I E : Type*} [DecidableEq I] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (e : I → (E ≃ₗᵢ[ℂ] E)) (i : I) (v : E) :
    l2CongrRightDep e (lp.single 2 i v) = lp.single 2 i (e i v) := by
  apply lp.ext
  funext j
  rw [l2CongrRightDep_apply]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- The exponential monomials are unimodular. -/
theorem norm_mFourier_apply {n : ℕ} (m : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
    ‖mFourier m t‖ = 1 := by
  simp [mFourier]

theorem memLp_charMul {n : ℕ} (m : Fin n → ℤ) (f : Lp ℂ 2 (LineTorusMeasure n)) :
    MemLp (fun t => mFourier m t * f t) 2 (LineTorusMeasure n) := by
  refine (Lp.memLp f).mono ?_ ?_
  · exact ((mFourier m).continuous.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)
  · filter_upwards with t
    rw [norm_mul, norm_mFourier_apply, one_mul]

/-- Multiplication by the exponential monomial with frequency `m` on the
`n`-torus of line frequencies. -/
def charMul (n : ℕ) (m : Fin n → ℤ) :
    Lp ℂ 2 (LineTorusMeasure n) ≃ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure n) where
  toFun f := (memLp_charMul m f).toLp _
  invFun f := (memLp_charMul (-m) f).toLp _
  left_inv f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_charMul (-m) ((memLp_charMul m f).toLp _)),
      MemLp.coeFn_toLp (memLp_charMul m f)] with t h1 h2
    rw [h1, h2, ← mul_assoc, ← mFourier_add]
    simp [mFourier_zero]
  right_inv f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_charMul m ((memLp_charMul (-m) f).toLp _)),
      MemLp.coeFn_toLp (memLp_charMul (-m) f)] with t h1 h2
    rw [h1, h2, ← mul_assoc, ← mFourier_add]
    simp [mFourier_zero]
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_charMul m (f + g)),
      Lp.coeFn_add ((memLp_charMul m f).toLp _) ((memLp_charMul m g).toLp _),
      MemLp.coeFn_toLp (memLp_charMul m f), MemLp.coeFn_toLp (memLp_charMul m g),
      Lp.coeFn_add f g] with t h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_charMul m (a • f)),
      Lp.coeFn_smul a ((memLp_charMul m f).toLp _),
      MemLp.coeFn_toLp (memLp_charMul m f), Lp.coeFn_smul a f] with t h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  norm_map' f := by
    show ‖(memLp_charMul m f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    refine le_antisymm (eLpNorm_mono_ae ?_) (eLpNorm_mono_ae ?_)
    · filter_upwards with t
      rw [norm_mul, norm_mFourier_apply, one_mul]
    · filter_upwards with t
      rw [norm_mul, norm_mFourier_apply, one_mul]

theorem coeFn_charMul (n : ℕ) (m : Fin n → ℤ) (f : Lp ℂ 2 (LineTorusMeasure n)) :
    (charMul n m f : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => mFourier m t * f t :=
  MemLp.coeFn_toLp (memLp_charMul m f)

@[simp] theorem charMul_mFourierLp (n : ℕ) (m k : Fin n → ℤ) :
    charMul n m (mFourierLp 2 k) = mFourierLp 2 (k + m) := by
  apply Lp.ext
  filter_upwards [coeFn_charMul n m (mFourierLp 2 k), coeFn_mFourierLp (d := Fin n) 2 k,
    coeFn_mFourierLp (d := Fin n) 2 (k + m)] with t h1 h2 h3
  rw [h1, h2, h3, ← mFourier_add]
  rw [add_comm m k]

/-- The frequency shift attached to a lattice translation and an axis
pattern: translating by `x` shifts the frequency of every line by the
transverse coordinate of `x` along that line's axis. -/
def lineShiftVector (n : ℕ) (x : Operator.Lattice) (σ : Fin n → Axis) : Fin n → ℤ :=
  fun a => transverseCoordinate (latticeToSite x) (σ a)

@[simp] theorem tuplePattern_tupleTranslate (n : ℕ) (x : Operator.Lattice)
    (t : Fin n → LineIndex) :
    tuplePattern (tupleTranslate n x t) = tuplePattern t := rfl

theorem tupleCoord_tupleTranslate (n : ℕ) (x : Operator.Lattice)
    (t : Fin n → LineIndex) :
    tupleCoord (tupleTranslate n x t) =
      tupleCoord t + lineShiftVector n x (tuplePattern t) := rfl

/-- The frequency-side realization of a lattice translation: in the sector of
axis pattern `σ` it is multiplication by the character of `lineShiftVector`. -/
def freqShift (n : ℕ) (x : Operator.Lattice) :
    LineFreqL2 n ≃ₗᵢ[ℂ] LineFreqL2 n :=
  l2CongrRightDep fun σ => charMul n (lineShiftVector n x σ)

@[simp] theorem freqShift_single (n : ℕ) (x : Operator.Lattice)
    (σ : Fin n → Axis) (v : Lp ℂ 2 (LineTorusMeasure n)) :
    freqShift n x (lp.single 2 σ v) =
      lp.single 2 σ (charMul n (lineShiftVector n x σ) v) :=
  l2CongrRightDep_single _ _ _

theorem orderedFourier_orderedTranslate (n : ℕ) (x : Operator.Lattice)
    (c : OrderedCoefficient n) :
    orderedFourier n (orderedTranslate n x c) =
      freqShift n x (orderedFourier n c) := by
  refine l2_ext_apply
    ((orderedFourier n).toContinuousLinearMap.comp
      (orderedTranslate n x).toLinearIsometry.toContinuousLinearMap)
    ((freqShift n x).toLinearIsometry.toContinuousLinearMap.comp
      (orderedFourier n).toContinuousLinearMap) ?_ c
  intro t
  change orderedFourier n (orderedTranslate n x (lp.single 2 t (1 : ℂ))) =
    freqShift n x (orderedFourier n (lp.single 2 t (1 : ℂ)))
  rw [orderedTranslate_single, orderedFourier_single, orderedFourier_single,
    one_smul, one_smul, orderedFreqFamily, orderedFreqFamily, freqShift_single,
    tuplePattern_tupleTranslate, charMul_mFourierLp,
    tupleCoord_tupleTranslate]

/-- Equation (20) intertwines the translation of Walsh indices with the
frequency-side character multiplication. -/
theorem lineIndexFourier_translateCoeff (n : ℕ) (x : Operator.Lattice)
    (c : DegreeCoefficient n) :
    lineIndexFourier n (translateCoeff n x c) =
      freqShift n x (lineIndexFourier n c) := by
  change orderedFourier n (walshOrdered n (translateCoeff n x c)) = _
  rw [walshOrdered_translateCoeff, orderedFourier_orderedTranslate]
  rfl

/-! ### The concrete fiber operator on the degree-`n` subspace -/

theorem environmentShift_homogeneousWalshSynthesis (n : ℕ) (x : Operator.Lattice)
    (c : DegreeCoefficient n) :
    environmentShift x (homogeneousWalshSynthesis n c) =
      homogeneousWalshSynthesis n (translateCoeff n x c) := by
  refine l2_ext_apply
    ((environmentShift x).comp (homogeneousWalshSynthesis n).toContinuousLinearMap)
    ((homogeneousWalshSynthesis n).toContinuousLinearMap.comp
      (translateCoeff n x).toLinearIsometry.toContinuousLinearMap) ?_ c
  intro S
  change environmentShift x (homogeneousWalshSynthesis n (lp.single 2 S (1 : ℂ))) =
    homogeneousWalshSynthesis n (translateCoeff n x (lp.single 2 S (1 : ℂ)))
  rw [translateCoeff_single, homogeneousWalshSynthesis_single,
    homogeneousWalshSynthesis_single, one_smul, one_smul,
    environmentShift_walshL2_public, translateDegreeIndex_coe]

/-- The symmetric part of the fiber, read on degree-`n` coefficients. -/
def coeffFiberS (n : ℕ) (p : Fin 2 → ℝ) :
    DegreeCoefficient n →L[ℂ] DegreeCoefficient n :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Complex.exp (Complex.I * p i) •
        (translateCoeff n (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap +
      Complex.exp (-Complex.I * p i) •
        (translateCoeff n (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
      (2 : ℂ) • ContinuousLinearMap.id ℂ (DegreeCoefficient n))

theorem concreteFiberS_homogeneousWalshSynthesis (n : ℕ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    concreteFiberS p (homogeneousWalshSynthesis n c) =
      homogeneousWalshSynthesis n (coeffFiberS n p c) := by
  rw [concreteFiberS_formula, coeffFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_smul, map_sum,
    LinearIsometry.map_add, LinearIsometry.map_sub]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [environmentShift_homogeneousWalshSynthesis,
    environmentShift_homogeneousWalshSynthesis]
  rfl

/-! ### The frequency-side operator -/

/-- The symmetric part of the fiber on the frequency side of (20). -/
def freqFiberS (n : ℕ) (p : Fin 2 → ℝ) : LineFreqL2 n →L[ℂ] LineFreqL2 n :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Complex.exp (Complex.I * p i) •
        (freqShift n (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap +
      Complex.exp (-Complex.I * p i) •
        (freqShift n (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
      (2 : ℂ) • ContinuousLinearMap.id ℂ (LineFreqL2 n))

theorem lineIndexFourier_coeffFiberS (n : ℕ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    lineIndexFourier n (coeffFiberS n p c) =
      freqFiberS n p (lineIndexFourier n c) := by
  rw [coeffFiberS, freqFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_smul, map_sum,
    LinearIsometry.map_add, LinearIsometry.map_sub,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lineIndexFourier_translateCoeff, lineIndexFourier_translateCoeff]

/-- `H_n = lambda - S_p` on degree-`n` Walsh coefficients. -/
def coeffPair (n : ℕ) (p : Fin 2 → ℝ) :
    Operator.DissipativeSkewPair (DegreeCoefficient n) where
  S := coeffFiberS n p
  A := 0
  selfAdjoint_S := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro c d
    rw [← (homogeneousWalshSynthesis n).inner_map_map,
      ← (homogeneousWalshSynthesis n).inner_map_map c (coeffFiberS n p d),
      ← concreteFiberS_homogeneousWalshSynthesis,
      ← concreteFiberS_homogeneousWalshSynthesis]
    have hsa := concreteFiberS_selfAdjoint p
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hsa
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa]
  nonpositive_S := by
    intro c
    rw [← (homogeneousWalshSynthesis n).inner_map_map,
      ← concreteFiberS_homogeneousWalshSynthesis]
    exact concreteFiberS_nonpositive p _
  skewAdjoint_A := by simp

/-- The degree-`n` block of `H = lambda - S_p`. -/
def coeffH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    DegreeCoefficient n →L[ℂ] DegreeCoefficient n :=
  (coeffPair n p).H lam

theorem coeffH_eq (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    coeffH n lam p =
      (lam : ℂ) • ContinuousLinearMap.id ℂ (DegreeCoefficient n) - coeffFiberS n p := rfl

/-- The frequency-side block of `H`. -/
def freqH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) : LineFreqL2 n →L[ℂ] LineFreqL2 n :=
  (lam : ℂ) • ContinuousLinearMap.id ℂ (LineFreqL2 n) - freqFiberS n p

/-- (Hsym), operator form: equation (20) intertwines the degree-`n` block of
`H` with the frequency-side block. -/
theorem lineIndexFourier_coeffH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    lineIndexFourier n (coeffH n lam p c) = freqH n lam p (lineIndexFourier n c) := by
  rw [coeffH_eq, freqH]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_sub, LinearIsometry.map_smul,
    lineIndexFourier_coeffFiberS]

/-- The degree-`n` subspaces are invariant. -/
theorem fiberH_homogeneousWalshSynthesis (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    (concreteFiberEnvironment.dissipativeSkewPair p).H lam
        (homogeneousWalshSynthesis n c) =
      homogeneousWalshSynthesis n (coeffH n lam p c) := by
  rw [coeffH_eq]
  show ((lam : ℂ) • ContinuousLinearMap.id ℂ WalshL2 - concreteFiberS p)
      (homogeneousWalshSynthesis n c) = _
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_sub, LinearIsometry.map_smul,
    concreteFiberS_homogeneousWalshSynthesis]

theorem walshDegree_eq_range (n : ℕ) :
    (walshDegree n : Set WalshL2) = Set.range (homogeneousWalshSynthesis n) := by
  apply Set.Subset.antisymm
  · have hrange :
        LinearMap.range (homogeneousWalshSynthesis n).toLinearMap =
          (⨆ S : WalshDegreeIndex n, LinearMap.range
            (LinearIsometry.toSpanSingleton ℂ WalshL2
              ((orthonormal_homogeneousWalshFamily n).1 S)).toLinearMap).topologicalClosure :=
      OrthogonalFamily.range_linearIsometry _
    have hclosed : IsClosed
        (LinearMap.range (homogeneousWalshSynthesis n).toLinearMap : Set WalshL2) := by
      rw [hrange]
      exact Submodule.isClosed_topologicalClosure _
    have hle : walshDegree n ≤ LinearMap.range (homogeneousWalshSynthesis n).toLinearMap := by
      refine Submodule.topologicalClosure_minimal _ ?_ hclosed
      rw [Submodule.span_le]
      rintro f ⟨S, hS, rfl⟩
      refine ⟨lp.single 2 ⟨S, hS⟩ (1 : ℂ), ?_⟩
      show homogeneousWalshSynthesis n (lp.single 2 ⟨S, hS⟩ (1 : ℂ)) = walshL2 S
      rw [homogeneousWalshSynthesis_single, one_smul]
    intro f hf
    obtain ⟨c, hc⟩ := hle hf
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact homogeneousWalshSynthesis_mem_degree n c

theorem concreteFiberS_mem_walshDegree' (n : ℕ) (p : Fin 2 → ℝ)
    {F : WalshL2} (hF : F ∈ walshDegree n) :
    concreteFiberS p F ∈ walshDegree n := by
  have h1 : F ∈ Set.range (homogeneousWalshSynthesis n) := by
    rw [← walshDegree_eq_range]; exact hF
  obtain ⟨c, rfl⟩ := h1
  rw [concreteFiberS_homogeneousWalshSynthesis]
  exact homogeneousWalshSynthesis_mem_degree n _

theorem fiberH_mem_walshDegree' (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    {F : WalshL2} (hF : F ∈ walshDegree n) :
    (concreteFiberEnvironment.dissipativeSkewPair p).H lam F ∈ walshDegree n := by
  have h1 : F ∈ Set.range (homogeneousWalshSynthesis n) := by
    rw [← walshDegree_eq_range]; exact hF
  obtain ⟨c, rfl⟩ := h1
  rw [fiberH_homogeneousWalshSynthesis]
  exact homogeneousWalshSynthesis_mem_degree n _

theorem concreteFiberS_mem_walshDegree (n : ℕ) (p : Fin 2 → ℝ)
    {F : WalshL2} (hF : F ∈ Set.range (homogeneousWalshSynthesis n)) :
    concreteFiberS p F ∈ Set.range (homogeneousWalshSynthesis n) := by
  obtain ⟨c, rfl⟩ := hF
  exact ⟨coeffFiberS n p c, (concreteFiberS_homogeneousWalshSynthesis n p c).symm⟩

theorem fiberH_mem_walshDegree (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    {F : WalshL2} (hF : F ∈ Set.range (homogeneousWalshSynthesis n)) :
    (concreteFiberEnvironment.dissipativeSkewPair p).H lam F ∈
      Set.range (homogeneousWalshSynthesis n) := by
  obtain ⟨c, rfl⟩ := hF
  exact ⟨coeffH n lam p c, (fiberH_homogeneousWalshSynthesis n lam p c).symm⟩

/-- `H_n` is bounded below by `lambda`.
-/
theorem coeffH_energy_lower (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    lam * ‖c‖ ^ 2 ≤ RCLike.re (inner ℂ (coeffH n lam p c) c) :=
  (coeffPair n p).hEnergy_lower lam c

theorem coeffH_nonneg (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    0 ≤ RCLike.re (inner ℂ (coeffH n lam p c) c) :=
  (coeffPair n p).hEnergy_nonneg hlam c

theorem coeffH_selfAdjoint (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    IsSelfAdjoint (coeffH n lam p) :=
  (coeffPair n p).H_selfAdjoint lam

theorem coeffH_bijective (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ) :
    Function.Bijective (coeffH n lam p) :=
  (coeffPair n p).H_bijective hlam

/-! ### The multiplier `lambda + theta P` -/

private theorem transverseCoordinate_neg (z : Site) (i : Axis) :
    transverseCoordinate (-z) i = -transverseCoordinate z i := by
  cases i <;> rfl

theorem lineShiftVector_neg (n : ℕ) (x : Operator.Lattice) (σ : Fin n → Axis) :
    lineShiftVector n (-x) σ = -lineShiftVector n x σ := by
  funext a
  simp [lineShiftVector, transverseCoordinate_neg]

/-- A line contributes its frequency to the coordinate transverse to its own
axis, and not at all to the coordinate along it. -/
theorem lineShiftVector_axisVector (n : ℕ) (i : Fin 2) (σ : Fin n → Axis) (a : Fin n) :
    lineShiftVector n (Operator.axisVector i) σ a = if σ a = finAxis i then 0 else 1 := by
  fin_cases i <;> cases h : σ a <;>
    simp [lineShiftVector, latticeToSite, Operator.axisVector, transverseCoordinate,
      finAxis, h]

/-- A real representative of a point of the frequency torus. -/
def torusLift (x : UnitAddCircle) : ℝ := Quotient.out x

@[simp] theorem torusLift_coe (x : UnitAddCircle) :
    ((torusLift x : ℝ) : UnitAddCircle) = x :=
  Quotient.out_eq x

theorem mFourier_eq_exp {n : ℕ} (m : Fin n → ℤ) (t : UnitAddTorus (Fin n)) :
    mFourier m t =
      Complex.exp (Complex.I *
        ((2 * Real.pi * ∑ a : Fin n, (m a : ℝ) * torusLift (t a) : ℝ) : ℂ)) := by
  have hterm : ∀ a : Fin n, fourier (m a) (t a) =
      Complex.exp (2 * Real.pi * Complex.I * (m a : ℂ) * ((torusLift (t a) : ℝ) : ℂ) / 1) := by
    intro a
    conv_lhs => rw [← torusLift_coe (t a)]
    rw [fourier_coe_apply]
    norm_num
  show (∏ a : Fin n, fourier (m a) (t a)) = _
  rw [Finset.prod_congr rfl fun a _ => hterm a, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [div_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The line-frequency contribution `q_1 + ... + q_n` to the total frequency,
in physical units. -/
def lineFrequency (n : ℕ) (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) (i : Fin 2) : ℝ :=
  2 * Real.pi *
    ∑ a : Fin n, ((lineShiftVector n (Operator.axisVector i) σ a : ℤ) : ℝ) * torusLift (t a)

/-- Equation (19): the total frequency `P = p + q_1 + ... + q_n`. -/
def totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : Fin 2 → ℝ :=
  fun i => p i + lineFrequency n σ t i

/-- The multiplier of (Hsym): `lambda + theta P`. -/
def symbolWeight (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : ℝ :=
  lam + Estimates.theta (totalFrequency n p σ t)

theorem symbolWeight_def (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    symbolWeight n lam p σ t = lam + Estimates.theta (totalFrequency n p σ t) := rfl

theorem symbolWeight_ge (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : lam ≤ symbolWeight n lam p σ t := by
  have := Estimates.theta_nonneg (totalFrequency n p σ t)
  simp only [symbolWeight]
  linarith

theorem symbolWeight_le (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : symbolWeight n lam p σ t ≤ lam + 4 := by
  have h0 := Real.neg_one_le_cos (totalFrequency n p σ t 0)
  have h1 := Real.neg_one_le_cos (totalFrequency n p σ t 1)
  simp only [symbolWeight, Estimates.theta, Estimates.dispersion]
  linarith

theorem symbolWeight_pos (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) : 0 < symbolWeight n lam p σ t :=
  lt_of_lt_of_le hlam (symbolWeight_ge n lam p σ t)

/-- The frequency-side symbol of the symmetric part. -/
def lineSymbol (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ i : Fin 2,
    (Complex.exp (Complex.I * (p i : ℂ)) *
        mFourier (lineShiftVector n (Operator.axisVector i) σ) t +
      Complex.exp (-Complex.I * (p i : ℂ)) *
        mFourier (lineShiftVector n (-Operator.axisVector i) σ) t - 2)

private theorem exp_add_exp_neg (w : ℝ) :
    Complex.exp (Complex.I * (w : ℂ)) + Complex.exp (-(Complex.I * (w : ℂ))) =
      2 * ((Real.cos w : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * (w : ℂ)) =
      Complex.cos (w : ℂ) + Complex.sin (w : ℂ) * Complex.I := by
    rw [mul_comm]
    exact Complex.exp_mul_I (w : ℂ)
  have h2 : Complex.exp (-(Complex.I * (w : ℂ))) =
      Complex.cos (w : ℂ) - Complex.sin (w : ℂ) * Complex.I := by
    rw [show -(Complex.I * (w : ℂ)) = (-(w : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, Complex.ofReal_cos]
  ring

/-- (Hsym) at the level of symbols: the symmetric part is multiplication by
`-theta P`, hence `H` is multiplication by `lambda + theta P`. -/
theorem lineSymbol_eq (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    lineSymbol n p σ t = -((Estimates.theta (totalFrequency n p σ t) : ℝ) : ℂ) := by
  have key : ∀ i : Fin 2,
      Complex.exp (Complex.I * (p i : ℂ)) *
          mFourier (lineShiftVector n (Operator.axisVector i) σ) t +
        Complex.exp (-Complex.I * (p i : ℂ)) *
          mFourier (lineShiftVector n (-Operator.axisVector i) σ) t - 2 =
        2 * ((Real.cos (totalFrequency n p σ t i) : ℝ) : ℂ) - 2 := by
    intro i
    rw [lineShiftVector_neg, mFourier_eq_exp, mFourier_eq_exp]
    rw [← Complex.exp_add, ← Complex.exp_add]
    have h1 : Complex.I * (p i : ℂ) +
        Complex.I * ((2 * Real.pi *
          ∑ a : Fin n, ((lineShiftVector n (Operator.axisVector i) σ a : ℤ) : ℝ) *
            torusLift (t a) : ℝ) : ℂ) =
        Complex.I * ((totalFrequency n p σ t i : ℝ) : ℂ) := by
      simp only [totalFrequency, lineFrequency]
      push_cast
      ring
    have h2 : -Complex.I * (p i : ℂ) +
        Complex.I * ((2 * Real.pi *
          ∑ a : Fin n, (((-lineShiftVector n (Operator.axisVector i) σ) a : ℤ) : ℝ) *
            torusLift (t a) : ℝ) : ℂ) =
        -(Complex.I * ((totalFrequency n p σ t i : ℝ) : ℂ)) := by
      have hsum : (2 * Real.pi *
          ∑ a : Fin n, (((-lineShiftVector n (Operator.axisVector i) σ) a : ℤ) : ℝ) *
            torusLift (t a) : ℝ) = -lineFrequency n σ t i := by
        simp only [lineFrequency, Pi.neg_apply, Int.cast_neg, neg_mul,
          Finset.sum_neg_distrib]
        ring
      rw [hsum]
      simp only [totalFrequency]
      push_cast
      ring
    rw [h1, h2, exp_add_exp_neg]
  rw [lineSymbol, Fin.sum_univ_two, key 0, key 1]
  simp only [Estimates.theta, Estimates.dispersion]
  push_cast
  ring

/-! ### Multiplication by a continuous symbol -/

theorem memLp_contMul {n : ℕ} (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    MemLp (fun t => g t * u t) 2 (LineTorusMeasure n) := by
  refine ((Lp.memLp u).const_mul ((‖g‖ : ℝ) : ℂ)).mono ?_ ?_
  · exact (g.continuous.aestronglyMeasurable).mul (Lp.aestronglyMeasurable u)
  · filter_upwards with t
    rw [norm_mul, norm_mul]
    have hnorm : ‖((‖g‖ : ℝ) : ℂ)‖ = ‖g‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg g)]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg _)

/-- Multiplication of an `L²` function of the line frequencies by a
continuous symbol. -/
def contMul (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) : Lp ℂ 2 (LineTorusMeasure n) :=
  (memLp_contMul g u).toLp _

theorem coeFn_contMul {n : ℕ} (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    (contMul n g u : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => g t * u t :=
  MemLp.coeFn_toLp (memLp_contMul g u)

theorem charMul_eq_contMul (n : ℕ) (m : Fin n → ℤ)
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    charMul n m u = contMul n (mFourier m) u := rfl

theorem contMul_add_left {n : ℕ} (g h : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (g + h) u = contMul n g u + contMul n h u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (g + h) u, Lp.coeFn_add (contMul n g u) (contMul n h u),
    coeFn_contMul g u, coeFn_contMul h u] with t h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4, ContinuousMap.add_apply, add_mul]

theorem contMul_sub_left {n : ℕ} (g h : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (g - h) u = contMul n g u - contMul n h u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (g - h) u, Lp.coeFn_sub (contMul n g u) (contMul n h u),
    coeFn_contMul g u, coeFn_contMul h u] with t h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4, ContinuousMap.sub_apply, sub_mul]

theorem contMul_smul_left {n : ℕ} (a : ℂ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n (a • g) u = a • contMul n g u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (a • g) u, Lp.coeFn_smul a (contMul n g u),
    coeFn_contMul g u] with t h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, ContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_assoc]

theorem contMul_one {n : ℕ} (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n 1 u = u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul (1 : C(UnitAddTorus (Fin n), ℂ)) u] with t h1
  rw [h1, ContinuousMap.one_apply, one_mul]

/-- The continuous symbol of the symmetric part. -/
def lineSymbolMap (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    C(UnitAddTorus (Fin n), ℂ) :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Complex.exp (Complex.I * (p i : ℂ)) •
        mFourier (lineShiftVector n (Operator.axisVector i) σ) +
      Complex.exp (-Complex.I * (p i : ℂ)) •
        mFourier (lineShiftVector n (-Operator.axisVector i) σ) -
      (2 : ℂ) • (1 : C(UnitAddTorus (Fin n), ℂ)))

@[simp] theorem lineSymbolMap_apply (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    lineSymbolMap n p σ t = lineSymbol n p σ t := by
  simp only [lineSymbolMap, lineSymbol, Fin.sum_univ_two, ContinuousMap.smul_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    smul_eq_mul]
  ring

theorem freqFiberS_apply (n : ℕ) (p : Fin 2 → ℝ) (f : LineFreqL2 n)
    (σ : Fin n → Axis) :
    (freqFiberS n p f) σ = contMul n (lineSymbolMap n p σ) (f σ) := by
  have hexpand : (freqFiberS n p f) σ =
      (2 : ℂ)⁻¹ • ((Complex.exp (Complex.I * (p 0 : ℂ)) •
            charMul n (lineShiftVector n (Operator.axisVector 0) σ) (f σ) +
          Complex.exp (-Complex.I * (p 0 : ℂ)) •
            charMul n (lineShiftVector n (-Operator.axisVector 0) σ) (f σ) -
          (2 : ℂ) • f σ) +
        (Complex.exp (Complex.I * (p 1 : ℂ)) •
            charMul n (lineShiftVector n (Operator.axisVector 1) σ) (f σ) +
          Complex.exp (-Complex.I * (p 1 : ℂ)) •
            charMul n (lineShiftVector n (-Operator.axisVector 1) σ) (f σ) -
          (2 : ℂ) • f σ)) := by
    simp only [freqFiberS, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, Fin.sum_univ_two]
    rfl
  rw [hexpand, lineSymbolMap, Fin.sum_univ_two]
  simp only [contMul_smul_left, contMul_add_left, contMul_sub_left, contMul_one,
    charMul_eq_contMul]

theorem coeFn_freqFiberS (n : ℕ) (p : Fin 2 → ℝ) (f : LineFreqL2 n)
    (σ : Fin n → Axis) :
    ((freqFiberS n p f) σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => lineSymbol n p σ t * (f σ) t := by
  rw [freqFiberS_apply]
  filter_upwards [coeFn_contMul (lineSymbolMap n p σ) (f σ)] with t ht
  rw [ht, lineSymbolMap_apply]

/-- (Hsym) in the model: after equation (20), `H_n` is multiplication by
`lambda + theta P`, with `P = p + q_1 + ... + q_n`. -/
theorem coeFn_freqH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (f : LineFreqL2 n)
    (σ : Fin n → Axis) :
    ((freqH n lam p f) σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
      fun t => ((symbolWeight n lam p σ t : ℝ) : ℂ) * (f σ) t := by
  have hcomp : (freqH n lam p f) σ = (lam : ℂ) • f σ - (freqFiberS n p f) σ := rfl
  rw [hcomp]
  filter_upwards [Lp.coeFn_sub ((lam : ℂ) • f σ) ((freqFiberS n p f) σ),
    Lp.coeFn_smul ((lam : ℂ)) (f σ), coeFn_freqFiberS n p f σ] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, lineSymbol_eq,
    symbolWeight]
  push_cast
  ring

/-! ### The `H` and `H⁻¹` quadratic forms as weighted integrals -/

private theorem inner_lp_eq_integral {n : ℕ} (u v : Lp ℂ 2 (LineTorusMeasure n))
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

/-- Consequence (i): the `H` quadratic form of a degree-`n` element is the
weighted integral of its line-frequency coefficient. -/
theorem re_inner_coeffH_eq_integral (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    RCLike.re (inner ℂ (coeffH n lam p c) c) =
      ∑' σ : Fin n → Axis,
        ∫ t, symbolWeight n lam p σ t *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  have hΦ : inner ℂ (coeffH n lam p c) c =
      inner ℂ (freqH n lam p (lineIndexFourier n c)) (lineIndexFourier n c) := by
    rw [← (lineIndexFourier n).inner_map_map, lineIndexFourier_coeffH]
  have hs := lp.hasSum_inner (𝕜 := ℂ)
    (freqH n lam p (lineIndexFourier n c)) (lineIndexFourier n c)
  have hre := RCLike.hasSum_re ℂ hs
  have hterm : ∀ σ : Fin n → Axis,
      RCLike.re (inner ℂ ((freqH n lam p (lineIndexFourier n c)) σ)
          ((lineIndexFourier n c) σ)) =
        ∫ t, symbolWeight n lam p σ t *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
    intro σ
    exact inner_lp_eq_integral _ _ _ (coeFn_freqH n lam p (lineIndexFourier n c) σ)
  rw [hΦ]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [hterm] using hre

/-- Consequence (i) for `H⁻¹`: if `coeffH n lam p d = c`, the `H⁻¹`
quadratic form of `c` is the integral of `(lambda + theta P)⁻¹` against the
squared modulus of the line-frequency coefficient. -/
theorem re_inner_coeffH_inv_eq_integral (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (c d : DegreeCoefficient n) (hd : coeffH n lam p d = c) :
    RCLike.re (inner ℂ d c) =
      ∑' σ : Fin n → Axis,
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  have hΦ : inner ℂ d c =
      inner ℂ (lineIndexFourier n d) (lineIndexFourier n c) :=
    ((lineIndexFourier n).inner_map_map d c).symm
  have hgf : freqH n lam p (lineIndexFourier n d) = lineIndexFourier n c := by
    rw [← lineIndexFourier_coeffH, hd]
  have hcoe : ∀ σ : Fin n → Axis,
      ((lineIndexFourier n d) σ : UnitAddTorus (Fin n) → ℂ) =ᵐ[LineTorusMeasure n]
        fun t => (((symbolWeight n lam p σ t)⁻¹ : ℝ) : ℂ) *
          ((lineIndexFourier n c) σ) t := by
    intro σ
    have h1 := coeFn_freqH n lam p (lineIndexFourier n d) σ
    rw [hgf] at h1
    filter_upwards [h1] with t ht
    have hw : symbolWeight n lam p σ t ≠ 0 := ne_of_gt (symbolWeight_pos n hlam p σ t)
    have hwC : ((symbolWeight n lam p σ t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
    rw [ht]
    push_cast
    field_simp
  have hs := lp.hasSum_inner (𝕜 := ℂ) (lineIndexFourier n d) (lineIndexFourier n c)
  have hre := RCLike.hasSum_re ℂ hs
  have hterm : ∀ σ : Fin n → Axis,
      RCLike.re (inner ℂ ((lineIndexFourier n d) σ) ((lineIndexFourier n c) σ)) =
        ∫ t, (symbolWeight n lam p σ t)⁻¹ *
          ‖((lineIndexFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
    intro σ
    exact inner_lp_eq_integral _ _ _ (hcoe σ)
  rw [hΦ]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [hterm] using hre

/-! ### Consequence (ii): the off-diagonal projection commutes with the
multiplier

In the ordered picture the paper's `Pi_n` is multiplication by the indicator of
the tuples with distinct entries.  Lattice translations permute those tuples,
so every operator assembled from translations, in particular the multiplier by
`lambda + theta P`, commutes with the projection. -/

private theorem offDiagonal_norm_le {n : ℕ} (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) :
    ‖(if Function.Injective t then (c t : ℂ) else 0)‖ ^ ENNReal.toReal 2 ≤
      ‖c t‖ ^ ENNReal.toReal 2 := by
  by_cases h : Function.Injective t
  · simp [h]
  · simp only [h, if_false, norm_zero,
      Real.zero_rpow (by norm_num : ENNReal.toReal 2 ≠ 0)]
    positivity

private theorem memlp_offDiagonal {n : ℕ} (c : OrderedCoefficient n) :
    Memℓp (fun t : Fin n → LineIndex =>
      if Function.Injective t then (c t : ℂ) else 0) 2 := by
  apply memℓp_gen
  exact Summable.of_nonneg_of_le (fun t => by positivity) (offDiagonal_norm_le c)
    (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2))

/-- The paper's off-diagonal projection `Pi_n`. -/
def offDiagonalProjection (n : ℕ) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨_, memlp_offDiagonal c⟩
      map_add' := by
        intro c d
        apply lp.ext
        funext t
        show (if Function.Injective t then ((c + d : OrderedCoefficient n) t : ℂ) else 0) =
          (if Function.Injective t then (c t : ℂ) else 0) +
            (if Function.Injective t then (d t : ℂ) else 0)
        by_cases h : Function.Injective t <;> simp [h]
      map_smul' := by
        intro a c
        apply lp.ext
        funext t
        show (if Function.Injective t then ((a • c : OrderedCoefficient n) t : ℂ) else 0) =
          a • (if Function.Injective t then (c t : ℂ) else 0)
        by_cases h : Function.Injective t <;> simp [h] }
    1 <| by
      intro c
      rw [one_mul, lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      exact Summable.tsum_le_tsum (offDiagonal_norm_le c)
        (Summable.of_nonneg_of_le (fun t => by positivity) (offDiagonal_norm_le c)
          (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2)))
        (c.prop.summable (by norm_num : 0 < ENNReal.toReal 2))

@[simp] theorem offDiagonalProjection_apply (n : ℕ) (c : OrderedCoefficient n)
    (t : Fin n → LineIndex) :
    offDiagonalProjection n c t = if Function.Injective t then c t else 0 := rfl

theorem offDiagonalProjection_idem (n : ℕ) :
    offDiagonalProjection n ∘L offDiagonalProjection n = offDiagonalProjection n := by
  refine ContinuousLinearMap.ext fun c => ?_
  apply lp.ext
  funext t
  by_cases h : Function.Injective t <;> simp [h]

theorem offDiagonalProjection_isSelfAdjoint (n : ℕ) :
    IsSelfAdjoint (offDiagonalProjection n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro c d
  rw [lp.inner_eq_tsum (𝕜 := ℂ) (offDiagonalProjection n c) d,
    lp.inner_eq_tsum (𝕜 := ℂ) c (offDiagonalProjection n d)]
  refine tsum_congr fun t => ?_
  by_cases h : Function.Injective t <;> simp [h]

theorem injective_tupleTranslate (n : ℕ) (x : Operator.Lattice)
    (t : Fin n → LineIndex) :
    Function.Injective (tupleTranslate n x t) ↔ Function.Injective t := by
  constructor
  · intro h a b hab
    exact h (by simp only [tupleTranslate_apply, hab])
  · intro h a b hab
    exact h ((lineTranslation (latticeToSite x)).injective hab)

theorem orderedTranslate_comm_offDiagonalProjection (n : ℕ) (x : Operator.Lattice)
    (c : OrderedCoefficient n) :
    offDiagonalProjection n (orderedTranslate n x c) =
      orderedTranslate n x (offDiagonalProjection n c) := by
  refine lp.ext ?_
  funext t
  have hcomp : ∀ a : Fin n, (tupleTranslate n x).symm t a =
      (lineTranslation (latticeToSite x)).symm (t a) := fun _ => rfl
  have hinj : Function.Injective ((tupleTranslate n x).symm t) ↔ Function.Injective t := by
    constructor
    · intro h a b hab
      exact h (by simp only [hcomp, hab])
    · intro h a b hab
      simp only [hcomp] at hab
      exact h ((lineTranslation (latticeToSite x)).symm.injective hab)
  show (if Function.Injective t then (orderedTranslate n x c) t else 0) =
    (offDiagonalProjection n c) ((tupleTranslate n x).symm t)
  rw [offDiagonalProjection_apply]
  show (if Function.Injective t then c ((tupleTranslate n x).symm t) else 0) =
    if Function.Injective ((tupleTranslate n x).symm t) then
      c ((tupleTranslate n x).symm t) else 0
  by_cases h : Function.Injective t
  · rw [if_pos h, if_pos (hinj.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hinj.mp hc))]

/-- The symmetric part in the ordered picture. -/
def orderedFiberS (n : ℕ) (p : Fin 2 → ℝ) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  (2 : ℂ)⁻¹ • ∑ i : Fin 2,
    (Complex.exp (Complex.I * p i) •
        (orderedTranslate n (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap +
      Complex.exp (-Complex.I * p i) •
        (orderedTranslate n (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
      (2 : ℂ) • ContinuousLinearMap.id ℂ (OrderedCoefficient n))

/-- The multiplier by `lambda + theta P` in the ordered picture. -/
def orderedH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient n :=
  (lam : ℂ) • ContinuousLinearMap.id ℂ (OrderedCoefficient n) - orderedFiberS n p

theorem orderedFourier_orderedFiberS (n : ℕ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    orderedFourier n (orderedFiberS n p c) =
      freqFiberS n p (orderedFourier n c) := by
  rw [orderedFiberS, freqFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_smul, map_sum,
    LinearIsometry.map_add, LinearIsometry.map_sub,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orderedFourier_orderedTranslate, orderedFourier_orderedTranslate]

/-- The ordered multiplier is the one of (Hsym). -/
theorem orderedFourier_orderedH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    orderedFourier n (orderedH n lam p c) = freqH n lam p (orderedFourier n c) := by
  rw [orderedH, freqH]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_sub, LinearIsometry.map_smul,
    orderedFourier_orderedFiberS]

theorem orderedFiberS_comm_offDiagonalProjection (n : ℕ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    offDiagonalProjection n (orderedFiberS n p c) =
      orderedFiberS n p (offDiagonalProjection n c) := by
  rw [orderedFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_smul, map_sum, map_add, map_sub,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orderedTranslate_comm_offDiagonalProjection,
    orderedTranslate_comm_offDiagonalProjection]

/-- The commutation of Lemma 5.1's last sentence, **for the single multiplier
`lambda + theta(P)` only** -- not for every function of `P`, which is what the
lemma claims (`manuscript.tex:1189-1190`).  `orderedH` IS that one multiplier,
so nothing here covers the general form.

The two other multipliers the formalization needs are handled separately and
directly, neither of them through this theorem:

* the multiplier `M` of (35), by
  `Manhattan.Glue.diagonalMultiplierEnergy_le_rawMultiplierEnergy`
  (`Manhattan/Glue/ProjectionDischarge.lean`), a fibrewise argument -- and it is
  precisely because `M` is not a trigonometric polynomial that the paper's own
  justification at `manuscript.tex:1233-1235` does not cover it;
* the raw weight of the ordered representative, s
  `Manhattan.Glue.rawOrderedProjection_comm_rawWeightOp`
  (`Manhattan/Glue/SummandFourAssembly.lean`). -/
theorem orderedH_comm_offDiagonalProjection (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : OrderedCoefficient n) :
    offDiagonalProjection n (orderedH n lam p c) =
      orderedH n lam p (offDiagonalProjection n c) := by
  rw [orderedH]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_sub, map_smul,
    orderedFiberS_comm_offDiagonalProjection]

/-! ### Bridges to the scalar weights of `Manhattan.Estimates` -/

theorem symbolWeight_eq_hWeight (n : ℕ) (q : Estimates.Parameters) (p : Fin 2 → ℝ)
    (σ : Fin n → Axis) (t : UnitAddTorus (Fin n)) :
    symbolWeight n q.lambda p σ t = Estimates.hWeight q (totalFrequency n p σ t) := rfl

theorem inv_hWeight_eq_mixedHMinusWeight (q : Estimates.Parameters) (r beta : ℝ) :
    (Estimates.hWeight q ![r, beta])⁻¹ = Estimates.mixedHMinusWeight q r beta := by
  simp only [Estimates.hWeight, Estimates.mixedHMinusWeight, Estimates.theta,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [add_assoc]

theorem inv_hWeight_eq_twoRowHMinusWeight (q : Estimates.Parameters) (p₁ alpha : ℝ) :
    (Estimates.hWeight q ![p₁, alpha])⁻¹ = Estimates.twoRowHMinusWeight q p₁ alpha := by
  simp only [Estimates.hWeight, Estimates.twoRowHMinusWeight, Estimates.theta,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [add_assoc]

/-- The sorted enumeration intertwines the Finset picture with the ordered
picture used for the off-diagonal projection. -/
theorem walshOrdered_coeffFiberS (n : ℕ) (p : Fin 2 → ℝ) (c : DegreeCoefficient n) :
    walshOrdered n (coeffFiberS n p c) = orderedFiberS n p (walshOrdered n c) := by
  rw [coeffFiberS, orderedFiberS]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_smul, map_sum,
    LinearIsometry.map_add, LinearIsometry.map_sub,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [walshOrdered_translateCoeff, walshOrdered_translateCoeff]

theorem walshOrdered_coeffH (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (c : DegreeCoefficient n) :
    walshOrdered n (coeffH n lam p c) = orderedH n lam p (walshOrdered n c) := by
  rw [coeffH_eq, orderedH]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.map_sub, LinearIsometry.map_smul,
    walshOrdered_coeffFiberS]

theorem lineIndexFourier_eq_comp (n : ℕ) (c : DegreeCoefficient n) :
    lineIndexFourier n c = orderedFourier n (walshOrdered n c) := rfl

end Manhattan.Glue
