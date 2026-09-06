import Manhattan.Glue.ConcreteLowering

/-!
# (D2a) and (D2b): the concrete lowering formulas in line frequencies

The Walsh carrier is Finset-indexed, so the manuscript's tuple
normalizations `sqrt 2`, `2`, `sqrt 18` of `manuscript.tex:822-825` are not
imported.  Instead the ordered coefficient functions of the manuscript are
*defined* from the Finset coefficients here, and the constants relating the
two are derived from the literal Finset isometry (17).

Paper: `manuscript.tex:793-840` and `manuscript.tex:1176-1230`.
-/

open ComplexConjugate MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Manhattan.Glue

noncomputable section

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance concreteLoweringPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## Index maps -/

/-- The three-line Walsh index carrying two rows and one column. -/
def tripleToFinset (t : ℤ × ℤ × ℤ) : Finset LineIndex :=
  {(Axis.horizontal, t.1), (Axis.horizontal, t.2.1), (Axis.vertical, t.2.2)}

/-- The two-row Walsh index. -/
def rowPairFinset (t : ℤ × ℤ) : Finset LineIndex :=
  {(Axis.horizontal, t.1), (Axis.horizontal, t.2)}

/-- The mixed Walsh index: one row and one column. -/
def mixedPairFinset (t : ℤ × ℤ) : Finset LineIndex :=
  {(Axis.horizontal, t.1), (Axis.vertical, t.2)}

theorem tripleToFinset_swap (a b c : ℤ) :
    tripleToFinset (a, b, c) = tripleToFinset (b, a, c) := by
  ext l
  simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem tripleToFinset_isType112 {t : ℤ × ℤ × ℤ} (ht : t.1 ≠ t.2.1) :
    IsType112Index (tripleToFinset t) := by
  obtain ⟨a, b, c⟩ := t
  simp only at ht
  constructor
  · simp [tripleToFinset, ht]
  · have hfilter : (tripleToFinset (a, b, c)).filter
        (fun l => l.1 = Axis.horizontal) =
        {(Axis.horizontal, a), (Axis.horizontal, b)} := by
      ext l
      obtain ⟨i, j⟩ := l
      cases i <;> simp [tripleToFinset]
    rw [hfilter]
    simp [ht]

/-- On strictly ordered triples the three-line index map is injective. -/
theorem tripleToFinset_strict_injOn :
    Set.InjOn tripleToFinset {t : ℤ × ℤ × ℤ | t.1 < t.2.1} := by
  rintro ⟨a, b, c⟩ ha ⟨x, y, z⟩ hx h
  simp only [Set.mem_setOf_eq] at ha hx
  have h1 : (Axis.horizontal, a) ∈ tripleToFinset (x, y, z) := by
    rw [← h]; simp [tripleToFinset]
  have h2 : (Axis.horizontal, b) ∈ tripleToFinset (x, y, z) := by
    rw [← h]; simp [tripleToFinset]
  have h3 : (Axis.vertical, c) ∈ tripleToFinset (x, y, z) := by
    rw [← h]; simp [tripleToFinset]
  have h4 : (Axis.horizontal, x) ∈ tripleToFinset (a, b, c) := by
    rw [h]; simp [tripleToFinset]
  have h5 : (Axis.horizontal, y) ∈ tripleToFinset (a, b, c) := by
    rw [h]; simp [tripleToFinset]
  simp [tripleToFinset] at h1 h2 h3 h4 h5
  simp only [Prod.mk.injEq]
  refine ⟨by omega, by omega, by omega⟩

/-! ## Failure of the type-`112` pattern -/

theorem not_isType112_of_card_ne {S : Finset LineIndex} (hS : S.card ≠ 3) :
    ¬ IsType112Index S := fun h => hS h.1

theorem not_isType112_of_no_vertical {S : Finset LineIndex}
    (hS : ∀ l ∈ S, l.1 = Axis.horizontal) : ¬ IsType112Index S := by
  intro h
  have hfilter : S.filter (fun l => l.1 = Axis.horizontal) = S :=
    Finset.filter_true_of_mem hS
  have h2 := h.2
  rw [hfilter, h.1] at h2
  omega

theorem not_isType112_of_two_vertical {S : Finset LineIndex}
    {u v : LineIndex} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hu1 : u.1 = Axis.vertical) (hv1 : v.1 = Axis.vertical) :
    ¬ IsType112Index S := by
  intro h
  have hsub : ({u, v} : Finset LineIndex) ⊆
      S.filter (fun l => ¬ l.1 = Axis.horizontal) := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hu, by simp [hu1]⟩
    · exact Finset.mem_filter.mpr ⟨hv, by simp [hv1]⟩
  have hcard : 2 ≤ (S.filter (fun l => ¬ l.1 = Axis.horizontal)).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton] at this
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S) (fun l => l.1 = Axis.horizontal)
  rw [h.1, h.2] at hsplit
  omega

/-! ## The Finset coefficient of an ordered kernel -/

theorem mapDomain_apply_eq {α β : Type*} [DecidableEq β] (f : α → β)
    (v : α →₀ ℂ) (b : β) :
    Finsupp.mapDomain f v b = ∑ t ∈ v.support, if f t = b then v t else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun t _ => by simp [Finsupp.single_apply]

/-- The ordered kernel restricted to its strictly ordered representatives,
rescaled by the constant that the Finset isometry forces. -/
def strictType112Kernel (k : (ℤ × ℤ × ℤ) →₀ ℂ) : (ℤ × ℤ × ℤ) →₀ ℂ :=
  Finsupp.filter (fun t => t.1 < t.2.1) (((Real.sqrt 2 : ℝ) : ℂ) • k)

theorem strict_of_mem_support_strictType112Kernel {k : (ℤ × ℤ × ℤ) →₀ ℂ}
    {t : ℤ × ℤ × ℤ} (ht : t ∈ (strictType112Kernel k).support) : t.1 < t.2.1 := by
  rw [strictType112Kernel, Finsupp.support_filter, Finset.mem_filter] at ht
  exact ht.2

theorem strictType112Kernel_apply {k : (ℤ × ℤ × ℤ) →₀ ℂ} {t : ℤ × ℤ × ℤ}
    (ht : t.1 < t.2.1) :
    strictType112Kernel k t = ((Real.sqrt 2 : ℝ) : ℂ) * k t := by
  rw [strictType112Kernel, Finsupp.filter_apply, if_pos ht]
  simp

/-- The Finset-indexed degree-three Walsh coefficient of a normalized ordered
type-`112` kernel.  The constant `sqrt 2` is not imported from the manuscript:
it is exactly the constant that makes the Finset isometry (17) agree with the
ordered square-summable norm, because each unordered index is represented by
two ordered triples. -/
def type112FinsetCoefficient (k : (ℤ × ℤ × ℤ) →₀ ℂ) : WalshCoefficient :=
  Finsupp.mapDomain tripleToFinset (strictType112Kernel k)

/-- The Finset coefficient is supported on genuine type-`112` indices. -/
theorem type112FinsetCoefficient_eq_zero_of_not_isType112
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) {S : Finset LineIndex} (hS : ¬ IsType112Index S) :
    type112FinsetCoefficient k S = 0 := by
  rw [type112FinsetCoefficient, mapDomain_apply_eq]
  refine Finset.sum_eq_zero fun t ht => if_neg fun hts => hS ?_
  rw [← hts]
  exact tripleToFinset_isType112
    (ne_of_lt (strict_of_mem_support_strictType112Kernel ht))

theorem type112FinsetCoefficient_apply_strict (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    {t : ℤ × ℤ × ℤ} (ht : t.1 < t.2.1) :
    type112FinsetCoefficient k (tripleToFinset t) =
      ((Real.sqrt 2 : ℝ) : ℂ) * k t := by
  rw [type112FinsetCoefficient, mapDomain_apply_eq]
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl, strictType112Kernel_apply ht]
  · intro s hs hst
    refine if_neg fun hts => hst ?_
    exact tripleToFinset_strict_injOn
      (strict_of_mem_support_strictType112Kernel hs) ht hts
  · intro hts
    rw [if_pos rfl]
    exact Finsupp.notMem_support_iff.mp hts

/-- **The derived type-`112` normalization.**  For a kernel symmetric in its
two row indices, the Finset coefficient at an off-diagonal index is
`sqrt 2` times the ordered kernel.  This is the manuscript's `sqrt 18`
normalization of `manuscript.tex:822-825` rewritten in Finset coordinates. -/
theorem type112FinsetCoefficient_apply (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    {t : ℤ × ℤ × ℤ} (ht : t.1 ≠ t.2.1) :
    type112FinsetCoefficient k (tripleToFinset t) =
      ((Real.sqrt 2 : ℝ) : ℂ) * k t := by
  obtain ⟨a, b, c⟩ := t
  simp only at ht
  rcases lt_or_gt_of_ne ht with h | h
  · exact type112FinsetCoefficient_apply_strict k h
  · rw [tripleToFinset_swap,
      type112FinsetCoefficient_apply_strict k (t := (b, a, c)) h, hsymm]

/-! ## The four neighbours of a degree-two index -/

@[simp] theorem latticeToSite_axisVector_zero :
    latticeToSite (Operator.axisVector 0) = (1, 0) := by
  simp [latticeToSite, Operator.axisVector]

@[simp] theorem latticeToSite_axisVector_one :
    latticeToSite (Operator.axisVector 1) = (0, 1) := by
  simp [latticeToSite, Operator.axisVector]

theorem translateWalshIndex_rowPair (x : Operator.Lattice) (m m' : ℤ) :
    translateWalshIndex x (rowPairFinset (m, m')) =
      rowPairFinset (m + (latticeToSite x).2, m' + (latticeToSite x).2) := by
  simp [translateWalshIndex, rowPairFinset, lineTranslation, transverseCoordinate]

theorem translateWalshIndex_mixedPair (x : Operator.Lattice) (m n : ℤ) :
    translateWalshIndex x (mixedPairFinset (m, n)) =
      mixedPairFinset (m + (latticeToSite x).2, n + (latticeToSite x).1) := by
  simp [translateWalshIndex, mixedPairFinset, lineTranslation, transverseCoordinate]

theorem toggle_vertical_rowPair (m m' : ℤ) :
    toggleOriginWalshIndex 1 (rowPairFinset (m, m')) = tripleToFinset (m, m', 0) := by
  ext l
  simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
    rowPairFinset, tripleToFinset, Finset.mem_insert, originLine, finAxis_one]
  obtain ⟨i, j⟩ := l
  cases i <;> simp

theorem horizontal_of_mem_toggle_horizontal_rowPair {m m' : ℤ}
    {l : LineIndex} (hl : l ∈ toggleOriginWalshIndex 0 (rowPairFinset (m, m'))) :
    l.1 = Axis.horizontal := by
  simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
    rowPairFinset, Finset.mem_insert, originLine, finAxis_zero] at hl
  obtain ⟨i, j⟩ := l
  cases i <;> simp_all

/-- The two-row index has no type-`112` neighbour along the row axis. -/
theorem not_isType112_toggle_horizontal_rowPair (m m' : ℤ) :
    ¬ IsType112Index (toggleOriginWalshIndex 0 (rowPairFinset (m, m'))) :=
  not_isType112_of_no_vertical fun _ hl =>
    horizontal_of_mem_toggle_horizontal_rowPair hl

theorem toggle_horizontal_mixedPair_of_ne {m n : ℤ} (hm : m ≠ 0) :
    toggleOriginWalshIndex 0 (mixedPairFinset (m, n)) = tripleToFinset (m, 0, n) := by
  ext l
  simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
    mixedPairFinset, tripleToFinset, Finset.mem_insert, originLine, finAxis_zero]
  obtain ⟨i, j⟩ := l
  cases i
  · simp
    omega
  · simp

theorem toggle_horizontal_mixedPair_zero (n : ℤ) :
    toggleOriginWalshIndex 0 (mixedPairFinset (0, n)) =
      {(Axis.vertical, n)} := by
  ext l
  simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
    mixedPairFinset, Finset.mem_insert, originLine, finAxis_zero]
  obtain ⟨i, j⟩ := l
  cases i <;> simp

/-- The mixed index has no type-`112` neighbour along the column axis. -/
theorem not_isType112_toggle_vertical_mixedPair (m n : ℤ) :
    ¬ IsType112Index (toggleOriginWalshIndex 1 (mixedPairFinset (m, n))) := by
  by_cases hn : n = 0
  · subst hn
    apply not_isType112_of_card_ne
    have hset : toggleOriginWalshIndex 1 (mixedPairFinset (m, 0)) =
        {(Axis.horizontal, m)} := by
      ext l
      simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
        mixedPairFinset, Finset.mem_insert, originLine, finAxis_one]
      obtain ⟨i, j⟩ := l
      cases i <;> simp
    rw [hset]
    simp
  · refine not_isType112_of_two_vertical (u := (Axis.vertical, n))
      (v := (Axis.vertical, 0)) ?_ ?_ (by simp [hn]) rfl rfl
    · simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
        mixedPairFinset, Finset.mem_insert, originLine, finAxis_one]
      simp [hn]
    · simp only [toggleOriginWalshIndex, Finset.mem_symmDiff, Finset.mem_singleton,
        mixedPairFinset, Finset.mem_insert, originLine, finAxis_one]
      simp [Ne.symm hn]

/-! ## (D2a) and (D2b) in line-index (spatial) coordinates -/

/-- **(D2a), spatial form.**  Only the column axis contributes to the two-row
component of `D₂*`, and it does so by one signed lattice step in both row
indices.  The overall `sqrt 2` is the derived type-`112` normalization; after
dividing by the equal type-`11` normalization it disappears, exactly as in the
manuscript's (D2a). -/
theorem loweringCoefficient_rowPair (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c)) {m m' : ℤ} (hne : m ≠ m') :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (rowPairFinset (m, m')) =
      ((Real.sqrt 2 : ℝ) : ℂ) *
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) * k (m + 1, m' + 1, 0) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) * k (m - 1, m' - 1, 0)) := by
  have e0p : translateWalshIndex (Operator.axisVector 0) (rowPairFinset (m, m'))
      = rowPairFinset (m, m') := by
    rw [translateWalshIndex_rowPair]; simp
  have e0m : translateWalshIndex (-Operator.axisVector 0) (rowPairFinset (m, m'))
      = rowPairFinset (m, m') := by
    rw [translateWalshIndex_rowPair]; simp
  have e1p : translateWalshIndex (Operator.axisVector 1) (rowPairFinset (m, m'))
      = rowPairFinset (m + 1, m' + 1) := by
    rw [translateWalshIndex_rowPair]; simp
  have e1m : translateWalshIndex (-Operator.axisVector 1) (rowPairFinset (m, m'))
      = rowPairFinset (m - 1, m' - 1) := by
    rw [translateWalshIndex_rowPair]; simp [sub_eq_add_neg]
  rw [loweringCoefficient_walshSynthesis, Fin.sum_univ_two, e0p, e0m, e1p, e1m,
    toggle_vertical_rowPair, toggle_vertical_rowPair,
    type112FinsetCoefficient_eq_zero_of_not_isType112 k
      (not_isType112_toggle_horizontal_rowPair m m'),
    type112FinsetCoefficient_apply k hsymm (t := (m + 1, m' + 1, 0))
      (by simpa using fun h => hne (by omega)),
    type112FinsetCoefficient_apply k hsymm (t := (m - 1, m' - 1, 0))
      (by simpa using fun h => hne (by omega))]
  ring

/-- **(D2b), spatial form.**  Only the row axis contributes to the mixed
component of `D₂*`, and it does so by one signed lattice step in the column
index while the second row index is pinned to the origin.

**Domain restriction**: this establishes (28) only for
DIAGONAL-FREE kernels -- the hypothesis `hdiag`.  The frequency-side statements
`Manhattan.Glue.frequency_D2a` and `Manhattan.Glue.frequency_D2b` below are
themselves unconditional; it is this spatial identification of the concrete
`D₂*` with the raw mixed symbol that needs `hdiag`.  For the paper's actual
competitor, whose `k̃` does carry coincident rows, the mixed identity is part
A8's `Manhattan.Glue.mixedFourierCoefficient_correction`, packaged as
`Manhattan.Glue.concreteLoweringFormula_correction_certified`
(`Manhattan/Glue/CorrectionLowering.lean`). -/
theorem loweringCoefficient_mixedPair (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) (m n : ℤ) :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (mixedPairFinset (m, n)) =
      ((Real.sqrt 2 : ℝ) : ℂ) *
        (((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) * k (m, 0, n + 1) -
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) * k (m, 0, n - 1)) := by
  have e0p : translateWalshIndex (Operator.axisVector 0) (mixedPairFinset (m, n))
      = mixedPairFinset (m, n + 1) := by
    rw [translateWalshIndex_mixedPair]; simp
  have e0m : translateWalshIndex (-Operator.axisVector 0) (mixedPairFinset (m, n))
      = mixedPairFinset (m, n - 1) := by
    rw [translateWalshIndex_mixedPair]; simp [sub_eq_add_neg]
  have e1p : translateWalshIndex (Operator.axisVector 1) (mixedPairFinset (m, n))
      = mixedPairFinset (m + 1, n) := by
    rw [translateWalshIndex_mixedPair]; simp
  have e1m : translateWalshIndex (-Operator.axisVector 1) (mixedPairFinset (m, n))
      = mixedPairFinset (m - 1, n) := by
    rw [translateWalshIndex_mixedPair]; simp [sub_eq_add_neg]
  rw [loweringCoefficient_walshSynthesis, Fin.sum_univ_two, e0p, e0m, e1p, e1m,
    type112FinsetCoefficient_eq_zero_of_not_isType112 k
      (not_isType112_toggle_vertical_mixedPair (m + 1) n),
    type112FinsetCoefficient_eq_zero_of_not_isType112 k
      (not_isType112_toggle_vertical_mixedPair (m - 1) n)]
  by_cases hm : m = 0
  · subst hm
    rw [toggle_horizontal_mixedPair_zero, toggle_horizontal_mixedPair_zero,
      type112FinsetCoefficient_eq_zero_of_not_isType112 k
        (not_isType112_of_card_ne (S := {(Axis.vertical, n + 1)}) (by simp)),
      type112FinsetCoefficient_eq_zero_of_not_isType112 k
        (not_isType112_of_card_ne (S := {(Axis.vertical, n - 1)}) (by simp)),
      hdiag, hdiag]
    ring
  · rw [toggle_horizontal_mixedPair_of_ne hm, toggle_horizontal_mixedPair_of_ne hm,
      type112FinsetCoefficient_apply k hsymm (t := (m, 0, n + 1)) hm,
      type112FinsetCoefficient_apply k hsymm (t := (m, 0, n - 1)) hm]
    ring

/-! ## Line characters and the normalized torus mean -/

/-- The character of one line frequency, `e^{i n x}`.  The frequency variable
is the *unshifted* line frequency: the manuscript's `r`, `r'`, `beta` are
`p₂ + s`, `p₂ + s'`, `p₁ + u` in these variables (`manuscript.tex:797-806`). -/
def lineCharacter (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((n : ℂ) * (x : ℂ)))

theorem lineCharacter_add (a b : ℤ) (x : ℝ) :
    lineCharacter (a + b) x = lineCharacter a x * lineCharacter b x := by
  rw [lineCharacter, lineCharacter, lineCharacter, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Orthogonality of the line characters against the normalized torus
measure `dm`. -/
theorem torusIntegral_lineCharacter (n : ℤ) :
    Estimates.torusIntegral (lineCharacter n) = if n = 0 then 1 else 0 := by
  rw [Estimates.torusIntegral, Estimates.torus]
  have hpi : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hn : n = 0
  · subst hn
    have hone : (fun x : ℝ => lineCharacter 0 x) = fun _ : ℝ => (1 : ℂ) := by
      funext x
      simp [lineCharacter]
    rw [if_pos rfl, hone, MeasureTheory.setIntegral_const,
      Real.volume_real_Ioc_of_le hpi, smul_smul]
    norm_num
    have hpine : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  · rw [if_neg hn]
    have hint : (∫ x in Set.Ioc (-Real.pi) Real.pi, lineCharacter n x) = 0 := by
      rw [← intervalIntegral.integral_of_le hpi]
      have hfun : (fun x : ℝ => lineCharacter n x) =
          fun x : ℝ => Complex.exp ((Complex.I * (n : ℂ)) * (x : ℂ)) := by
        funext x
        rw [lineCharacter, mul_assoc]
      rw [hfun]
      have hc : Complex.I * (n : ℂ) ≠ 0 := by
        simp [Complex.I_ne_zero, hn]
      rw [integral_exp_mul_complex hc]
      have h1 : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
        Complex.exp_int_mul_two_pi_mul_I n
      have h2 : Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ)) =
          Complex.exp (Complex.I * (n : ℂ) * ((-Real.pi : ℝ) : ℂ)) *
            Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
        rw [← Complex.exp_add]
        push_cast
        ring_nf
      rw [h2, h1, mul_one, sub_self, zero_div]
    rw [hint, smul_zero]

/-! ## Frequency functions of the ordered kernels -/

/-- The three-frequency function of an ordered type-`112` kernel, in the
unshifted line frequencies. -/
def orderedFreqThree (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' u : ℝ) : ℂ :=
  k.sum fun t z =>
    z * lineCharacter t.1 s * lineCharacter t.2.1 s' * lineCharacter t.2.2 u

/-- The two-frequency function of an ordered degree-two kernel. -/
def orderedFreqTwo (v : (ℤ × ℤ) →₀ ℂ) (s s' : ℝ) : ℂ :=
  v.sum fun q z => z * lineCharacter q.1 s * lineCharacter q.2 s'

/-- The zero column-frequency slice, i.e. `∫ K dm(β)` of the manuscript. -/
def columnZeroFreq (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' : ℝ) : ℂ :=
  ∑ t ∈ k.support,
    if t.2.2 = 0 then k t * lineCharacter t.1 s * lineCharacter t.2.1 s' else 0

/-- The zero second-row-frequency slice, i.e. `∫ K dm(r')` of the
manuscript. -/
def rowZeroFreq (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s u : ℝ) : ℂ :=
  ∑ t ∈ k.support,
    if t.2.1 = 0 then k t * lineCharacter t.1 s * lineCharacter t.2.2 u else 0

theorem orderedFreqTwo_sub (v w : (ℤ × ℤ) →₀ ℂ) (s s' : ℝ) :
    orderedFreqTwo (v - w) s s' = orderedFreqTwo v s s' - orderedFreqTwo w s s' := by
  refine Finsupp.sum_sub_index fun a b₁ b₂ => ?_
  simp [sub_mul]

theorem orderedFreqTwo_smul (c : ℂ) (v : (ℤ × ℤ) →₀ ℂ) (s s' : ℝ) :
    orderedFreqTwo (c • v) s s' = c * orderedFreqTwo v s s' := by
  rw [orderedFreqTwo, orderedFreqTwo, Finsupp.sum, Finsupp.sum, Finset.mul_sum,
    Finset.sum_subset (Finsupp.support_smul (b := c) (g := v))]
  · exact Finset.sum_congr rfl fun q _ => by
      simp only [Finsupp.smul_apply, smul_eq_mul]; ring
  · intro q _ hq
    rw [Finsupp.notMem_support_iff.mp hq]
    ring

theorem torusIntegral_const_mul (c : ℂ) (f : ℝ → ℂ) :
    Estimates.torusIntegral (fun x => c * f x) =
      c * Estimates.torusIntegral f := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral, integral_const_mul,
    Complex.real_smul, Complex.real_smul]
  ring

private theorem integrableOn_const_mul_lineCharacter (c : ℂ) (n : ℤ) :
    IntegrableOn (fun x : ℝ => c * lineCharacter n x) Estimates.torus := by
  rw [Estimates.torus]
  apply Continuous.integrableOn_Ioc
  unfold lineCharacter
  fun_prop

theorem torusIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, IntegrableOn (f i) Estimates.torus) :
    Estimates.torusIntegral (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, Estimates.torusIntegral (f i) := by
  rw [Estimates.torusIntegral, MeasureTheory.integral_finset_sum _ hf,
    Finset.smul_sum]
  rfl

theorem torusIntegral_orderedFreqThree (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' : ℝ) :
    Estimates.torusIntegral (fun u => orderedFreqThree k s s' u) =
      columnZeroFreq k s s' := by
  have hsum : (fun u => orderedFreqThree k s s' u) =
      fun u => ∑ t ∈ k.support,
        (k t * lineCharacter t.1 s * lineCharacter t.2.1 s') *
          lineCharacter t.2.2 u := by
    funext u
    rw [orderedFreqThree, Finsupp.sum]
  rw [hsum, torusIntegral_finset_sum _ _
      (fun t _ => integrableOn_const_mul_lineCharacter _ _),
    columnZeroFreq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [torusIntegral_const_mul, torusIntegral_lineCharacter]
  by_cases h : t.2.2 = 0 <;> simp [h]

theorem torusIntegral_orderedFreqThree_row (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s u : ℝ) :
    Estimates.torusIntegral (fun s' => orderedFreqThree k s s' u) =
      rowZeroFreq k s u := by
  have hsum : (fun s' => orderedFreqThree k s s' u) =
      fun s' => ∑ t ∈ k.support,
        (k t * lineCharacter t.1 s * lineCharacter t.2.2 u) *
          lineCharacter t.2.1 s' := by
    funext s'
    rw [orderedFreqThree, Finsupp.sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hsum, torusIntegral_finset_sum _ _
      (fun t _ => integrableOn_const_mul_lineCharacter _ _),
    rowZeroFreq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [torusIntegral_const_mul, torusIntegral_lineCharacter]
  by_cases h : t.2.1 = 0 <;> simp [h]

/-! ## The lowered kernels and the manuscript's (D2a), (D2b) -/

/-- The index shift produced by one signed lattice step in both rows. -/
def twoRowShift (c : ℤ) (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.1 + c, t.2.1 + c)

/-- The index shift produced by one signed lattice step in the column. -/
def mixedShift (c : ℤ) (t : ℤ × ℤ × ℤ) : ℤ × ℤ := (t.1, t.2.2 + c)

@[simp] theorem twoRowShift_fst (c : ℤ) (t : ℤ × ℤ × ℤ) :
    (twoRowShift c t).1 = t.1 + c := rfl

@[simp] theorem twoRowShift_snd (c : ℤ) (t : ℤ × ℤ × ℤ) :
    (twoRowShift c t).2 = t.2.1 + c := rfl

@[simp] theorem mixedShift_fst (c : ℤ) (t : ℤ × ℤ × ℤ) :
    (mixedShift c t).1 = t.1 := rfl

@[simp] theorem mixedShift_snd (c : ℤ) (t : ℤ × ℤ × ℤ) :
    (mixedShift c t).2 = t.2.2 + c := rfl

theorem mapDomain_filter_apply {α β : Type*} [DecidableEq β] (f : α → β)
    (k : α →₀ ℂ) (P : α → Prop) [DecidablePred P] (t₀ : α) (hP : P t₀)
    (huniq : ∀ t, P t → f t = f t₀ → t = t₀) :
    Finsupp.mapDomain f (Finsupp.filter P k) (f t₀) = k t₀ := by
  rw [mapDomain_apply_eq, Finset.sum_eq_single t₀]
  · rw [if_pos rfl, Finsupp.filter_apply, if_pos hP]
  · intro t ht htne
    refine if_neg fun hft => htne ?_
    have hPt : P t := by
      rw [Finsupp.support_filter, Finset.mem_filter] at ht
      exact ht.2
    exact huniq t hPt hft
  · intro hns
    rw [if_pos rfl]
    exact Finsupp.notMem_support_iff.mp hns

/-- The normalized two-row coefficient of `D₂*` as an ordered kernel. -/
def twoRowLoweredKernel (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ) : (ℤ × ℤ) →₀ ℂ :=
  ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) •
      Finsupp.mapDomain (twoRowShift (-1))
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) k) -
    ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) •
      Finsupp.mapDomain (twoRowShift 1)
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) k)

/-- The normalized mixed coefficient of `D₂*` as an ordered kernel.  The
`sqrt 2` here is the ratio of the derived type-`112` and type-`12`
normalizations; it is the manuscript's `sqrt 2` in (D2b). -/
def mixedLoweredKernel (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ) : (ℤ × ℤ) →₀ ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ) * ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0))) •
      Finsupp.mapDomain (mixedShift (-1))
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) k) -
    (((Real.sqrt 2 : ℝ) : ℂ) * ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0))) •
      Finsupp.mapDomain (mixedShift 1)
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) k)

theorem twoRowLoweredKernel_apply (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (m m' : ℤ) :
    twoRowLoweredKernel p k (m, m') =
      ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 1)) * k (m + 1, m' + 1, 0) -
        ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 1)) * k (m - 1, m' - 1, 0) := by
  have h1 : Finsupp.mapDomain (twoRowShift (-1))
      (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) k) (m, m') =
      k (m + 1, m' + 1, 0) := by
    have hu : ∀ t : ℤ × ℤ × ℤ, t.2.2 = 0 →
        twoRowShift (-1) t = twoRowShift (-1) (m + 1, m' + 1, 0) →
        t = (m + 1, m' + 1, 0) := by
      rintro ⟨a, b, c⟩ hP hft
      simp only [twoRowShift, Prod.mk.injEq] at hft
      simp only at hP
      simp only [Prod.mk.injEq]
      refine ⟨by omega, by omega, hP⟩
    have h := mapDomain_filter_apply (twoRowShift (-1)) k
      (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) (m + 1, m' + 1, 0) rfl hu
    rwa [show twoRowShift (-1) (m + 1, m' + 1, 0) = (m, m') from by
      simp [twoRowShift]] at h
  have h2 : Finsupp.mapDomain (twoRowShift 1)
      (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) k) (m, m') =
      k (m - 1, m' - 1, 0) := by
    have hu : ∀ t : ℤ × ℤ × ℤ, t.2.2 = 0 →
        twoRowShift 1 t = twoRowShift 1 (m - 1, m' - 1, 0) →
        t = (m - 1, m' - 1, 0) := by
      rintro ⟨a, b, c⟩ hP hft
      simp only [twoRowShift, Prod.mk.injEq] at hft
      simp only at hP
      simp only [Prod.mk.injEq]
      refine ⟨by omega, by omega, hP⟩
    have h := mapDomain_filter_apply (twoRowShift 1) k
      (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) (m - 1, m' - 1, 0) rfl hu
    rwa [show twoRowShift 1 (m - 1, m' - 1, 0) = (m, m') from by
      simp [twoRowShift]] at h
  rw [twoRowLoweredKernel]
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h1, h2]

theorem mixedLoweredKernel_apply (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (m n : ℤ) :
    mixedLoweredKernel p k (m, n) =
      ((Real.sqrt 2 : ℝ) : ℂ) *
          ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p 0)) * k (m, 0, n + 1) -
        ((Real.sqrt 2 : ℝ) : ℂ) *
          ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p 0)) * k (m, 0, n - 1) := by
  have h1 : Finsupp.mapDomain (mixedShift (-1))
      (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) k) (m, n) =
      k (m, 0, n + 1) := by
    have hu : ∀ t : ℤ × ℤ × ℤ, t.2.1 = 0 →
        mixedShift (-1) t = mixedShift (-1) (m, 0, n + 1) → t = (m, 0, n + 1) := by
      rintro ⟨a, b, c⟩ hP hft
      simp only [mixedShift, Prod.mk.injEq] at hft
      simp only at hP
      simp only [Prod.mk.injEq]
      refine ⟨hft.1, hP, by omega⟩
    have h := mapDomain_filter_apply (mixedShift (-1)) k
      (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) (m, 0, n + 1) rfl hu
    rwa [show mixedShift (-1) (m, 0, n + 1) = (m, n) from by
      simp [mixedShift]] at h
  have h2 : Finsupp.mapDomain (mixedShift 1)
      (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) k) (m, n) =
      k (m, 0, n - 1) := by
    have hu : ∀ t : ℤ × ℤ × ℤ, t.2.1 = 0 →
        mixedShift 1 t = mixedShift 1 (m, 0, n - 1) → t = (m, 0, n - 1) := by
      rintro ⟨a, b, c⟩ hP hft
      simp only [mixedShift, Prod.mk.injEq] at hft
      simp only at hP
      simp only [Prod.mk.injEq]
      refine ⟨hft.1, hP, by omega⟩
    have h := mapDomain_filter_apply (mixedShift 1) k
      (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) (m, 0, n - 1) rfl hu
    rwa [show mixedShift 1 (m, 0, n - 1) = (m, n) from by
      simp [mixedShift]] at h
  rw [mixedLoweredKernel]
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h1, h2]

/-- The two-row Walsh coefficient of `D₂*` is `sqrt 2` times the normalized
ordered kernel, exactly as the type-`112` coefficient is `sqrt 2` times its
own ordered kernel.  The two `sqrt 2`s cancel, which is why (D2a) carries no
constant. -/
theorem loweringCoefficient_rowPair_eq_kernel (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    {m m' : ℤ} (hne : m ≠ m') :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (rowPairFinset (m, m')) =
      ((Real.sqrt 2 : ℝ) : ℂ) * twoRowLoweredKernel p k (m, m') := by
  rw [loweringCoefficient_rowPair p k hsymm hne, twoRowLoweredKernel_apply]

/-- The mixed Walsh coefficient of `D₂*` equals its normalized ordered kernel:
the type-`12` normalization is one. -/
theorem loweringCoefficient_mixedPair_eq_kernel (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) (m n : ℤ) :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (mixedPairFinset (m, n)) =
      mixedLoweredKernel p k (m, n) := by
  rw [loweringCoefficient_mixedPair p k hsymm hdiag, mixedLoweredKernel_apply]
  ring

theorem orderedFreqTwo_mapDomain_twoRowShift (c : ℤ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (s s' : ℝ) :
    orderedFreqTwo (Finsupp.mapDomain (twoRowShift c)
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.2 = 0) k)) s s' =
      lineCharacter c s * lineCharacter c s' * columnZeroFreq k s s' := by
  rw [orderedFreqTwo,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum, Finsupp.support_filter, Finset.sum_filter, columnZeroFreq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t.2.2 = 0
  · rw [if_pos h, if_pos h, Finsupp.filter_apply, if_pos h]
    simp only [twoRowShift_fst, twoRowShift_snd, lineCharacter_add]
    ring
  · rw [if_neg h, if_neg h, mul_zero]

theorem orderedFreqTwo_mapDomain_mixedShift (c : ℤ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (s u : ℝ) :
    orderedFreqTwo (Finsupp.mapDomain (mixedShift c)
        (Finsupp.filter (fun t : ℤ × ℤ × ℤ => t.2.1 = 0) k)) s u =
      lineCharacter c u * rowZeroFreq k s u := by
  rw [orderedFreqTwo,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum, Finsupp.support_filter, Finset.sum_filter, rowZeroFreq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t.2.1 = 0
  · rw [if_pos h, if_pos h, Finsupp.filter_apply, if_pos h]
    simp only [mixedShift_fst, mixedShift_snd, lineCharacter_add]
    ring
  · rw [if_neg h, if_neg h, mul_zero]

/-- **(D2a).**  In the unshifted line frequencies `s`, `s'` this is the
manuscript's `-i sin(alpha) ∫ k dm(beta)` with `alpha = p₂ + s + s'`
(`manuscript.tex:797-806`, `manuscript.tex:827-834`).  No factorial and no
extra constant appears: the type-`112` and type-`11` normalizations are equal
and cancel. -/
theorem frequency_D2a (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' : ℝ) :
    orderedFreqTwo (twoRowLoweredKernel p k) s s' =
      -(Complex.I * (Real.sin (p 1 + s + s') : ℂ)) *
        Estimates.torusIntegral (fun u => orderedFreqThree k s s' u) := by
  rw [twoRowLoweredKernel, orderedFreqTwo_sub, orderedFreqTwo_smul,
    orderedFreqTwo_smul, orderedFreqTwo_mapDomain_twoRowShift,
    orderedFreqTwo_mapDomain_twoRowShift, torusIntegral_orderedFreqThree]
  have hA : ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * ((p 1 : ℝ) : ℂ))) *
      (lineCharacter (-1) s * lineCharacter (-1) s') =
      (2 : ℂ)⁻¹ * Complex.exp (-Complex.I * ((p 1 + s + s' : ℝ) : ℂ)) := by
    unfold lineCharacter
    rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hB : ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * ((p 1 : ℝ) : ℂ))) *
      (lineCharacter 1 s * lineCharacter 1 s') =
      (2 : ℂ)⁻¹ * Complex.exp (Complex.I * ((p 1 + s + s' : ℝ) : ℂ)) := by
    unfold lineCharacter
    rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hC := half_exp_neg_sub_half_exp (p 1 + s + s')
  linear_combination (columnZeroFreq k s s') * hA -
    (columnZeroFreq k s s') * hB + (columnZeroFreq k s s') * hC

/-- **(D2b).**  In the unshifted line frequencies `s`, `u` this is the
manuscript's `-i sqrt 2 sin(beta) ∫ k dm(r')` with `beta = p₁ + u`.  The
`sqrt 2` is *derived*: it is the ratio of the type-`112` normalization
(`sqrt 2`) to the type-`12` normalization (`1`) in the Finset isometry. -/
theorem frequency_D2b (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s u : ℝ) :
    orderedFreqTwo (mixedLoweredKernel p k) s u =
      -(((Real.sqrt 2 : ℝ) : ℂ) * Complex.I * (Real.sin (p 0 + u) : ℂ)) *
        Estimates.torusIntegral (fun s' => orderedFreqThree k s s' u) := by
  rw [mixedLoweredKernel, orderedFreqTwo_sub, orderedFreqTwo_smul,
    orderedFreqTwo_smul, orderedFreqTwo_mapDomain_mixedShift,
    orderedFreqTwo_mapDomain_mixedShift, torusIntegral_orderedFreqThree_row]
  have hA : ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * ((p 0 : ℝ) : ℂ))) *
      lineCharacter (-1) u =
      (2 : ℂ)⁻¹ * Complex.exp (-Complex.I * ((p 0 + u : ℝ) : ℂ)) := by
    unfold lineCharacter
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hB : ((2 : ℂ)⁻¹ * Complex.exp (Complex.I * ((p 0 : ℝ) : ℂ))) *
      lineCharacter 1 u =
      (2 : ℂ)⁻¹ * Complex.exp (Complex.I * ((p 0 + u : ℝ) : ℂ)) := by
    unfold lineCharacter
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hC := half_exp_neg_sub_half_exp (p 0 + u)
  linear_combination (((Real.sqrt 2 : ℝ) : ℂ) * rowZeroFreq k s u) * hA -
    (((Real.sqrt 2 : ℝ) : ℂ) * rowZeroFreq k s u) * hB +
    (((Real.sqrt 2 : ℝ) : ℂ) * rowZeroFreq k s u) * hC

/-! ## Deriving the normalizations inside the Finset isometry (17) -/

/-- The Finset isometry (17): no factorial, the squared norm of a finite
Walsh polynomial is the plain sum of squared coefficients. -/
theorem norm_sq_walshSynthesis (g : WalshCoefficient) :
    ‖walshSynthesis g‖ ^ 2 = ∑ S ∈ g.support, ‖g S‖ ^ 2 := by
  have h := inner_walshSynthesis g g
  rw [walshCoefficientInner, Finsupp.sum] at h
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact RCLike.ofReal_re _

/-- Squared-norm transport along an injectively reindexed coefficient. -/
theorem sum_normSq_mapDomain {α β : Type*} [DecidableEq β] (f : α → β)
    (v : α →₀ ℂ) (hinj : Set.InjOn f v.support) :
    ∑ S ∈ (Finsupp.mapDomain f v).support, ‖Finsupp.mapDomain f v S‖ ^ 2 =
      ∑ a ∈ v.support, ‖v a‖ ^ 2 := by
  have hinj' : ∀ x ∈ v.support, ∀ y ∈ v.support, f x = f y → x = y := by
    intro x hx y hy hxy
    exact hinj (by simpa using hx) (by simpa using hy) hxy
  rw [Finset.sum_subset Finsupp.mapDomain_support, Finset.sum_image hinj']
  · refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finsupp.mapDomain_apply' (v.support : Set α) v (le_refl _) hinj (by simpa using ha)]
  · intro S _ hS
    rw [Finsupp.notMem_support_iff.mp hS]
    simp

/-- A coefficient which is invariant under an involution exchanging the two
halves of its support has twice the squared norm of either half.  This is the
combinatorial content of the manuscript's tuple normalizations. -/
theorem sum_normSq_eq_two_mul_of_involution {α : Type*} (v : α →₀ ℂ)
    (σ : α → α) (P : α → Prop) [DecidablePred P]
    (hσ : ∀ a, σ (σ a) = a) (hv : ∀ a, v (σ a) = v a)
    (hP : ∀ a ∈ v.support, (P a ↔ ¬ P (σ a))) :
    ∑ a ∈ v.support, ‖v a‖ ^ 2 =
      2 * ∑ a ∈ v.support.filter P, ‖v a‖ ^ 2 := by
  classical
  have hmem : ∀ a, σ a ∈ v.support ↔ a ∈ v.support := by
    intro a
    constructor <;> intro h <;>
      simp only [Finsupp.mem_support_iff] at h ⊢
    · rw [hv] at h; exact h
    · rw [hv]; exact h
  have himg : (v.support.filter (fun a => ¬ P a)).image σ = v.support.filter P := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨ha, hna⟩, rfl⟩
      refine ⟨(hmem a).mpr ha, ?_⟩
      by_contra hPb
      exact hna ((hP a ha).mpr hPb)
    · rintro ⟨hb, hPb⟩
      refine ⟨σ b, ⟨(hmem b).mpr hb, ?_⟩, hσ b⟩
      exact fun hcon => ((hP b hb).mp hPb) hcon
  have hinj : ∀ x ∈ v.support.filter (fun a => ¬ P a),
      ∀ y ∈ v.support.filter (fun a => ¬ P a), σ x = σ y → x = y := by
    intro x _ y _ hxy
    rw [← hσ x, ← hσ y, hxy]
  have hhalf : ∑ a ∈ v.support.filter (fun a => ¬ P a), ‖v a‖ ^ 2 =
      ∑ a ∈ v.support.filter P, ‖v a‖ ^ 2 := by
    rw [← himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun a _ => by rw [hv]
  rw [← Finset.sum_filter_add_sum_filter_not v.support P, hhalf]
  ring

theorem support_strictType112Kernel (k : (ℤ × ℤ × ℤ) →₀ ℂ) :
    (strictType112Kernel k).support =
      k.support.filter (fun t => t.1 < t.2.1) := by
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [strictType112Kernel, Finsupp.support_filter, Finsupp.support_smul_eq hne]

/-- The squared norm of the synthesized type-`112` element, in ordered
coordinates.  Every unordered index carries two ordered triples: this is the
`sqrt 2` of `type112FinsetCoefficient`, derived rather than imported. -/
theorem norm_sq_type112Synthesis (k : (ℤ × ℤ × ℤ) →₀ ℂ) :
    ‖walshSynthesis (type112FinsetCoefficient k)‖ ^ 2 =
      2 * ∑ t ∈ k.support.filter (fun t => t.1 < t.2.1), ‖k t‖ ^ 2 := by
  rw [type112FinsetCoefficient, norm_sq_walshSynthesis,
    sum_normSq_mapDomain _ _ ?inj]
  case inj =>
    intro a ha b hb hab
    exact tripleToFinset_strict_injOn
      (strict_of_mem_support_strictType112Kernel (by simpa using ha))
      (strict_of_mem_support_strictType112Kernel (by simpa using hb)) hab
  rw [support_strictType112Kernel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_filter] at ht
  rw [strictType112Kernel_apply ht.2, norm_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- **The type-`112` normalization is exactly `sqrt 2`.**  With it the Finset
isometry reproduces the ordered square-summable norm of the manuscript's
coefficient `k`, so no `sqrt 18` (equivalently, no `3!`) is imported.
-/
theorem norm_sq_type112Synthesis_eq_ordered (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    ‖walshSynthesis (type112FinsetCoefficient k)‖ ^ 2 =
      ∑ t ∈ k.support, ‖k t‖ ^ 2 := by
  rw [norm_sq_type112Synthesis]
  refine (sum_normSq_eq_two_mul_of_involution k
    (fun t => (t.2.1, t.1, t.2.2)) (fun t => t.1 < t.2.1) (fun _ => rfl)
    (fun t => hsymm t.1 t.2.1 t.2.2) ?_).symm
  rintro ⟨a, b, c⟩ ht
  have hab : a ≠ b := by
    intro hab
    subst hab
    exact (Finsupp.mem_support_iff.mp ht) (hdiag a c)
  simp only [not_lt]
  omega

/-! ## The degree-two carriers and their derived normalizations -/

theorem mixedPairFinset_injective : Function.Injective mixedPairFinset := by
  rintro ⟨a, b⟩ ⟨x, y⟩ h
  have h1 : (Axis.horizontal, a) ∈ mixedPairFinset (x, y) := by
    rw [← h]; simp [mixedPairFinset]
  have h2 : (Axis.vertical, b) ∈ mixedPairFinset (x, y) := by
    rw [← h]; simp [mixedPairFinset]
  simp [mixedPairFinset] at h1 h2
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

theorem rowPairFinset_strict_injOn :
    Set.InjOn rowPairFinset {q : ℤ × ℤ | q.1 < q.2} := by
  rintro ⟨a, b⟩ ha ⟨x, y⟩ hx h
  simp only [Set.mem_setOf_eq] at ha hx
  have h1 : (Axis.horizontal, a) ∈ rowPairFinset (x, y) := by
    rw [← h]; simp [rowPairFinset]
  have h2 : (Axis.horizontal, b) ∈ rowPairFinset (x, y) := by
    rw [← h]; simp [rowPairFinset]
  have h3 : (Axis.horizontal, x) ∈ rowPairFinset (a, b) := by
    rw [h]; simp [rowPairFinset]
  have h4 : (Axis.horizontal, y) ∈ rowPairFinset (a, b) := by
    rw [h]; simp [rowPairFinset]
  simp [rowPairFinset] at h1 h2 h3 h4
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

theorem rowPairFinset_swap (a b : ℤ) :
    rowPairFinset (a, b) = rowPairFinset (b, a) := by
  ext l
  simp only [rowPairFinset, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The Finset coefficient of a mixed (type-`12`) ordered kernel.  Its
normalization is one: the row and the column index are distinguishable, so
each Finset index has a single ordered representative. -/
def type12FinsetCoefficient (e : (ℤ × ℤ) →₀ ℂ) : WalshCoefficient :=
  Finsupp.mapDomain mixedPairFinset e

@[simp] theorem type12FinsetCoefficient_apply (e : (ℤ × ℤ) →₀ ℂ) (q : ℤ × ℤ) :
    type12FinsetCoefficient e (mixedPairFinset q) = e q :=
  Finsupp.mapDomain_apply mixedPairFinset_injective e q

/-- **The type-`12` normalization is one.** -/
theorem norm_sq_type12Synthesis (e : (ℤ × ℤ) →₀ ℂ) :
    ‖walshSynthesis (type12FinsetCoefficient e)‖ ^ 2 =
      ∑ q ∈ e.support, ‖e q‖ ^ 2 := by
  rw [type12FinsetCoefficient, norm_sq_walshSynthesis,
    sum_normSq_mapDomain _ _ mixedPairFinset_injective.injOn]

/-- The strictly ordered representative of a two-row kernel, rescaled by the
constant the Finset isometry forces. -/
def strictType11Kernel (d : (ℤ × ℤ) →₀ ℂ) : (ℤ × ℤ) →₀ ℂ :=
  Finsupp.filter (fun q => q.1 < q.2) (((Real.sqrt 2 : ℝ) : ℂ) • d)

theorem strict_of_mem_support_strictType11Kernel {d : (ℤ × ℤ) →₀ ℂ}
    {q : ℤ × ℤ} (hq : q ∈ (strictType11Kernel d).support) : q.1 < q.2 := by
  rw [strictType11Kernel, Finsupp.support_filter, Finset.mem_filter] at hq
  exact hq.2

theorem strictType11Kernel_apply {d : (ℤ × ℤ) →₀ ℂ} {q : ℤ × ℤ}
    (hq : q.1 < q.2) :
    strictType11Kernel d q = ((Real.sqrt 2 : ℝ) : ℂ) * d q := by
  rw [strictType11Kernel, Finsupp.filter_apply, if_pos hq]
  simp

theorem support_strictType11Kernel (d : (ℤ × ℤ) →₀ ℂ) :
    (strictType11Kernel d).support = d.support.filter (fun q => q.1 < q.2) := by
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [strictType11Kernel, Finsupp.support_filter, Finsupp.support_smul_eq hne]

/-- The Finset coefficient of a two-row (type-`11`) ordered kernel.  Its
normalization is `sqrt 2`, the same as for type `112`. -/
def type11FinsetCoefficient (d : (ℤ × ℤ) →₀ ℂ) : WalshCoefficient :=
  Finsupp.mapDomain rowPairFinset (strictType11Kernel d)

theorem type11FinsetCoefficient_apply_strict (d : (ℤ × ℤ) →₀ ℂ) {q : ℤ × ℤ}
    (hq : q.1 < q.2) :
    type11FinsetCoefficient d (rowPairFinset q) =
      ((Real.sqrt 2 : ℝ) : ℂ) * d q := by
  rw [type11FinsetCoefficient, mapDomain_apply_eq, Finset.sum_eq_single q]
  · rw [if_pos rfl, strictType11Kernel_apply hq]
  · intro r hr hrq
    refine if_neg fun hfr => hrq ?_
    exact rowPairFinset_strict_injOn
      (strict_of_mem_support_strictType11Kernel hr) hq hfr
  · intro hns
    rw [if_pos rfl]
    exact Finsupp.notMem_support_iff.mp hns

theorem type11FinsetCoefficient_apply (d : (ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b : ℤ, d (b, a) = d (a, b)) {q : ℤ × ℤ} (hq : q.1 ≠ q.2) :
    type11FinsetCoefficient d (rowPairFinset q) =
      ((Real.sqrt 2 : ℝ) : ℂ) * d q := by
  obtain ⟨a, b⟩ := q
  simp only at hq
  rcases lt_or_gt_of_ne hq with h | h
  · exact type11FinsetCoefficient_apply_strict d h
  · rw [rowPairFinset_swap,
      type11FinsetCoefficient_apply_strict d (q := (b, a)) h, hsymm]

/-- **The type-`11` normalization is `sqrt 2`.** -/
theorem norm_sq_type11Synthesis_eq_ordered (d : (ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b : ℤ, d (b, a) = d (a, b)) (hdiag : ∀ a : ℤ, d (a, a) = 0) :
    ‖walshSynthesis (type11FinsetCoefficient d)‖ ^ 2 =
      ∑ q ∈ d.support, ‖d q‖ ^ 2 := by
  have hstep : ‖walshSynthesis (type11FinsetCoefficient d)‖ ^ 2 =
      2 * ∑ q ∈ d.support.filter (fun q => q.1 < q.2), ‖d q‖ ^ 2 := by
    rw [type11FinsetCoefficient, norm_sq_walshSynthesis,
      sum_normSq_mapDomain _ _ ?inj]
    case inj =>
      intro a ha b hb hab
      exact rowPairFinset_strict_injOn
        (strict_of_mem_support_strictType11Kernel (by simpa using ha))
        (strict_of_mem_support_strictType11Kernel (by simpa using hb)) hab
    rw [support_strictType11Kernel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_filter] at hq
    rw [strictType11Kernel_apply hq.2, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hstep]
  refine (sum_normSq_eq_two_mul_of_involution d
    (fun q => (q.2, q.1)) (fun q => q.1 < q.2) (fun _ => rfl)
    (fun q => hsymm q.1 q.2) ?_).symm
  rintro ⟨a, b⟩ hq
  have hab : a ≠ b := by
    intro hab
    subst hab
    exact (Finsupp.mem_support_iff.mp hq) (hdiag a)
  simp only [not_lt]
  omega

/-! ## The two lowering components as Finset coefficients -/

theorem twoRowLoweredKernel_symm (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c)) (a b : ℤ) :
    twoRowLoweredKernel p k (b, a) = twoRowLoweredKernel p k (a, b) := by
  rw [twoRowLoweredKernel_apply, twoRowLoweredKernel_apply,
    hsymm (a + 1) (b + 1) 0, hsymm (a - 1) (b - 1) 0]

/-- **(D2a) as a Walsh coefficient identity.**  The two-row Walsh coefficient
of `D₂* k` is the type-`11` Finset coefficient of `twoRowLoweredKernel`, whose
frequency function is the manuscript's `-i sin(alpha) ∫ k dm(beta)`. -/
theorem loweringCoefficient_eq_type11FinsetCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    {m m' : ℤ} (hne : m ≠ m') :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (rowPairFinset (m, m')) =
      type11FinsetCoefficient (twoRowLoweredKernel p k) (rowPairFinset (m, m')) := by
  rw [loweringCoefficient_rowPair_eq_kernel p k hsymm hne,
    type11FinsetCoefficient_apply _
      (fun a b => twoRowLoweredKernel_symm p k hsymm a b) hne]

/-- **(D2b) as a Walsh coefficient identity.**  The mixed Walsh coefficient of
`D₂* k` is the type-`12` Finset coefficient of `mixedLoweredKernel`, whose
frequency function is the manuscript's `-i sqrt 2 sin(beta) ∫ k dm(r')`. -/
theorem loweringCoefficient_eq_type12FinsetCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) (m n : ℤ) :
    loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (mixedPairFinset (m, n)) =
      type12FinsetCoefficient (mixedLoweredKernel p k) (mixedPairFinset (m, n)) := by
  rw [loweringCoefficient_mixedPair_eq_kernel p k hsymm hdiag,
    type12FinsetCoefficient_apply]

end

end Manhattan.Glue
