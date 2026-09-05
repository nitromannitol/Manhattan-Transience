import Manhattan.Glue.OrderedInverse

/-!
# The ordered raising map and its frequency form

Steps 3 and 4 of the degree-four raising sector, for a general degree-three
coefficient.

## Obstruction (b): the appended line is not last

`lineIndexFourier` reads a degree-four coefficient through `degreeEnum`, which
*sorts* the four lines.  The appended line is the origin line `(finAxis i, 0)`,
and its slot in the sorted enumeration depends on the signs of the transverse
coordinates already present: it is last only when all of those are negative.
This file defines that slot explicitly as `insertRank`, the number of existing
lines preceding the new one, and proves in `degreeEnum_eq_insertNth` that the
sorted enumeration of the enlarged Walsh index is the sorted enumeration of the
original index with the new line inserted at that slot, `Fin.insertNth`, not
appended.

The axis *pattern* is nevertheless constant, because `horizontal_lt_vertical`
puts every horizontal line before every vertical one: `insertRank` is at most
the vertical slot when the appended line is horizontal, and at least it when the
appended line is vertical, so `tuplePattern_degreeEnum_raiseIndex` gives the
single pattern `raisedPattern i`.  The appended line's transverse coordinate is
`0` whatever the slot, so `mFourier_tupleCoord_degreeEnum_raiseIndex` shows the
enlarged character is the degree-three character of the remaining variables:
constant in the new line's torus variable.

## The ordered raising map

`orderedRaise p i` is the composition of the ordered representative
`orderedRestrict 3`, the Finset-picture raising map `degreeRaiseDir p i` (the
Fourier symbol of `manuscript.tex:1181-1188` followed by the appending of the
origin line), and the sorted enumeration `walshOrdered 4`.  It is bounded by
`1`, and it realizes `walshRaiseDir p i` (`degreeRaiseDir_apply`,
`orderedRaise_apply_degreeEnum`).

Because `orderedRaise` already begins with `orderedRestrict 3` and ends with
`walshOrdered 4`, the passage to the ordered representative happens *inside* it.
The two declarations at the end of this section that were once advertised as the
intertwining hypothesis and as equation (46) for the ordered raising map,
`orderedRaise_orderedRepresentativeProjection` and
`re_inner_orderedHInv_orderedRaise_le`, are for that reason trivial: after
unfolding they read `X = X` and `X ≤ X`.  They are kept, with corrected
docstrings, and MUST NOT BE SEALED.

## The frequency form

`degreeRaiseDir_raiseIndex_type112` and `orderedRaise_insertNth_type112`: for a
general type-`(1,1,2)` coefficient the degree-four entry at the enlarged index
is the Fourier coefficient of `raisingSymbol p i` times the *symmetrized*
degree-three frequency function, at the original three frequencies.
The symmetrized representative is the admissible one; `type112FreqFun` provably
is not (`patternLines_type112Pattern_rawSwap`).

Paper: `manuscript.tex:1182-1186` (equation (45), `eq:raise`),
`manuscript.tex:1193-1198` (equation (46), `eq:contract`),
`manuscript.tex:1200-1207` (Lemma 5.2, `lem:four`).
-/

noncomputable section

open MeasureTheory

namespace Manhattan.Glue

/-! ### Restriction along an injection -/

section L2Restrict

variable {ι κ : Type*}

private theorem memlp_l2Restrict (f : ι → κ) (hf : Function.Injective f) (c : ℓ²(κ, ℂ)) :
    Memℓp (fun i : ι => (c (f i) : ℂ)) 2 := by
  apply memℓp_gen
  simpa [Function.comp_def] using
    ((lp.memℓp c).summable (by norm_num : 0 < ENNReal.toReal 2)).comp_injective hf

/-- Reading a square-summable family along an injection. -/
def l2Restrict (f : ι → κ) (hf : Function.Injective f) : ℓ²(κ, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨_, memlp_l2Restrict f hf c⟩
      map_add' := by intro c d; apply lp.ext; funext i; rfl
      map_smul' := by intro a c; apply lp.ext; funext i; rfl }
    1 <| by
      intro c
      rw [one_mul, lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have hraw : Summable fun k : κ => ‖c k‖ ^ ENNReal.toReal 2 :=
        (lp.memℓp c).summable (by norm_num : 0 < ENNReal.toReal 2)
      have hsum : Summable fun i : ι => ‖c (f i)‖ ^ ENNReal.toReal 2 := by
        simpa [Function.comp_def] using hraw.comp_injective hf
      exact hsum.tsum_le_tsum_of_inj f hf (fun _ _ => by positivity) (fun _ => le_rfl) hraw

@[simp] theorem l2Restrict_apply (f : ι → κ) (hf : Function.Injective f) (c : ℓ²(κ, ℂ))
    (i : ι) : l2Restrict f hf c i = c (f i) := rfl

theorem norm_l2Restrict_le (f : ι → κ) (hf : Function.Injective f) (c : ℓ²(κ, ℂ)) :
    ‖l2Restrict f hf c‖ ≤ ‖c‖ := by
  have h2 : ‖l2Restrict f hf‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ (by norm_num) _
  calc ‖l2Restrict f hf c‖ ≤ ‖l2Restrict f hf‖ * ‖c‖ := (l2Restrict f hf).le_opNorm c
    _ ≤ 1 * ‖c‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg c)
    _ = ‖c‖ := one_mul _

end L2Restrict

/-! ### Appending the origin line to a degree-three Walsh index -/

/-- Degree-three Walsh indices that do not already contain the origin line of
type `i`. -/
abbrev FreeIndex (i : Fin 2) := {S : WalshDegreeIndex 3 // Manhattan.originLine i ∉ S.1}

/-- The degree-four Walsh index obtained by appending the origin line. -/
def raiseIndex (i : Fin 2) (S : FreeIndex i) : WalshDegreeIndex 4 :=
  ⟨insert (Manhattan.originLine i) S.1.1, by
    rw [Finset.card_insert_of_notMem S.2, S.1.2]⟩

@[simp] theorem raiseIndex_coe (i : Fin 2) (S : FreeIndex i) :
    (raiseIndex i S).1 = insert (Manhattan.originLine i) S.1.1 := rfl

theorem originLine_mem_raiseIndex (i : Fin 2) (S : FreeIndex i) :
    Manhattan.originLine i ∈ (raiseIndex i S).1 := Finset.mem_insert_self _ _

theorem raiseIndex_injective (i : Fin 2) : Function.Injective (raiseIndex i) := by
  intro S T h
  have h' : insert (Manhattan.originLine i) S.1.1 = insert (Manhattan.originLine i) T.1.1 :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply Subtype.ext
  rw [← Finset.erase_insert S.2, ← Finset.erase_insert T.2, h']

theorem exists_raiseIndex (i : Fin 2) (T : WalshDegreeIndex 4)
    (hT : Manhattan.originLine i ∈ T.1) : ∃ S : FreeIndex i, raiseIndex i S = T := by
  refine ⟨⟨⟨T.1.erase (Manhattan.originLine i), ?_⟩, Finset.notMem_erase _ _⟩, ?_⟩
  · rw [Finset.card_erase_of_mem hT, T.2]
  · apply Subtype.ext
    exact Finset.insert_erase hT

/-! ### The degree-three symbol and the extension -/


theorem inner_walshL2_homogeneousWalshSynthesis (n : ℕ) (c : DegreeCoefficient n)
    (T : WalshDegreeIndex n) :
    inner ℂ (Manhattan.walshL2 T.1) (homogeneousWalshSynthesis n c) = c T := by
  have hone : homogeneousWalshSynthesis n (lp.single 2 T (1 : ℂ)) = Manhattan.walshL2 T.1 := by
    rw [homogeneousWalshSynthesis_single, one_smul]
  rw [← hone, (homogeneousWalshSynthesis n).inner_map_map, lp.inner_single_left]
  simp

/-- Pullback of a degree-`n` coefficient along a translation of Walsh indices. -/
def pullTranslate (n : ℕ) (x : Operator.Lattice) :
    DegreeCoefficient n ≃ₗᵢ[ℂ] DegreeCoefficient n :=
  l2CongrLeft (translateDegreeIndex n x).symm

@[simp] theorem pullTranslate_apply (n : ℕ) (x : Operator.Lattice) (c : DegreeCoefficient n)
    (S : WalshDegreeIndex n) :
    pullTranslate n x c S = c (translateDegreeIndex n x S) := by
  rw [pullTranslate, l2CongrLeft_apply, Equiv.symm_symm]

/-- The Fourier symbol of the raising operator, on degree-three coefficients. -/
def degreeRaiseSymbol (p : Fin 2 → ℝ) (i : Fin 2) :
    DegreeCoefficient 3 →L[ℂ] DegreeCoefficient 3 :=
  (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) •
      (pullTranslate 3 (-Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap -
    Complex.exp (-Complex.I * p i) •
      (pullTranslate 3 (Operator.axisVector i)).toLinearIsometry.toContinuousLinearMap)

theorem degreeRaiseSymbol_apply (p : Fin 2 → ℝ) (i : Fin 2) (c : DegreeCoefficient 3)
    (S : WalshDegreeIndex 3) :
    degreeRaiseSymbol p i c S =
      (2 : ℂ)⁻¹ * (Complex.exp (Complex.I * p i) *
          c (translateDegreeIndex 3 (-Operator.axisVector i) S) -
        Complex.exp (-Complex.I * p i) *
          c (translateDegreeIndex 3 (Operator.axisVector i) S)) := by
  rw [degreeRaiseSymbol]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_toContinuousLinearMap,
    lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    pullTranslate_apply]

theorem norm_degreeRaiseSymbol_le (p : Fin 2 → ℝ) (i : Fin 2) (c : DegreeCoefficient 3) :
    ‖degreeRaiseSymbol p i c‖ ≤ ‖c‖ := by
  have h1 : ‖Complex.exp (Complex.I * (p i : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I (p i)
  have h2 : ‖Complex.exp (-Complex.I * (p i : ℂ))‖ = 1 := by
    have : (-Complex.I) * (p i : ℂ) = ((-(p i) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [degreeRaiseSymbol]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_toContinuousLinearMap]
  calc ‖(2 : ℂ)⁻¹ • (Complex.exp (Complex.I * (p i : ℂ)) •
        (pullTranslate 3 (-Operator.axisVector i)) c -
      Complex.exp (-Complex.I * (p i : ℂ)) • (pullTranslate 3 (Operator.axisVector i)) c)‖
      = (2 : ℝ)⁻¹ * ‖Complex.exp (Complex.I * (p i : ℂ)) •
          (pullTranslate 3 (-Operator.axisVector i)) c -
        Complex.exp (-Complex.I * (p i : ℂ)) • (pullTranslate 3 (Operator.axisVector i)) c‖ := by
        rw [norm_smul]; norm_num
    _ ≤ (2 : ℝ)⁻¹ * (‖c‖ + ‖c‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, h1, h2, one_mul, one_mul,
          (pullTranslate 3 (-Operator.axisVector i)).norm_map,
          (pullTranslate 3 (Operator.axisVector i)).norm_map]
    _ = ‖c‖ := by ring

/-! ### The degree-four raising map on Finset coefficients -/

/-- Extension by zero of a degree-three coefficient to the degree-four indices
containing the origin line of type `i`. -/
def degreeRaise (i : Fin 2) : DegreeCoefficient 3 →L[ℂ] DegreeCoefficient 4 :=
  (l2Extend (raiseIndex i) (raiseIndex_injective i)).toContinuousLinearMap ∘L
    l2Restrict (fun S : FreeIndex i => S.1) Subtype.val_injective

theorem degreeRaise_apply_raiseIndex (i : Fin 2) (c : DegreeCoefficient 3) (S : FreeIndex i) :
    degreeRaise i c (raiseIndex i S) = c S.1 :=
  l2Extend_apply_image (raiseIndex i) (raiseIndex_injective i) _ S

theorem degreeRaise_apply_of_notMem (i : Fin 2) (c : DegreeCoefficient 3)
    (T : WalshDegreeIndex 4) (hT : Manhattan.originLine i ∉ T.1) :
    degreeRaise i c T = 0 :=
  l2Extend_apply_of_notMem (raiseIndex i) (raiseIndex_injective i) _ T
    (fun S hc => hT (hc ▸ originLine_mem_raiseIndex i S))

theorem norm_degreeRaise_le (i : Fin 2) (c : DegreeCoefficient 3) :
    ‖degreeRaise i c‖ ≤ ‖c‖ := by
  show ‖l2Extend (raiseIndex i) (raiseIndex_injective i)
      (l2Restrict (fun S : FreeIndex i => S.1) Subtype.val_injective c)‖ ≤ ‖c‖
  rw [(l2Extend (raiseIndex i) (raiseIndex_injective i)).norm_map]
  exact norm_l2Restrict_le _ _ c

/-- The degree-three-to-degree-four raising map: the Fourier symbol followed by
the appending of the origin line of type `i`. -/
def degreeRaiseDir (p : Fin 2 → ℝ) (i : Fin 2) :
    DegreeCoefficient 3 →L[ℂ] DegreeCoefficient 4 :=
  degreeRaise i ∘L degreeRaiseSymbol p i

theorem norm_degreeRaiseDir_le (p : Fin 2 → ℝ) (i : Fin 2) (c : DegreeCoefficient 3) :
    ‖degreeRaiseDir p i c‖ ≤ ‖c‖ :=
  le_trans (norm_degreeRaise_le i _) (norm_degreeRaiseSymbol_le p i c)

/-- **The raising map realizes `walshRaiseDir`.**  For a degree-three
coefficient `c`, every degree-four Walsh coefficient of the raised vector
`walshRaiseDir p i (synthesis c)` is the corresponding entry of
`degreeRaiseDir p i c`. -/
theorem degreeRaiseDir_apply (p : Fin 2 → ℝ) (i : Fin 2) (c : DegreeCoefficient 3)
    (T : WalshDegreeIndex 4) :
    degreeRaiseDir p i c T =
      inner ℂ (Manhattan.walshL2 T.1)
        (walshRaiseDir p i (homogeneousWalshSynthesis 3 c)) := by
  rw [inner_walshL2_walshRaiseDir]
  by_cases hT : Manhattan.originLine i ∈ T.1
  · obtain ⟨S, rfl⟩ := exists_raiseIndex i T hT
    have herase : (raiseIndex i S).1.erase (Manhattan.originLine i) = S.1.1 :=
      Finset.erase_insert S.2
    rw [if_pos hT, herase, ← translateDegreeIndex_coe 3 (-Operator.axisVector i) S.1,
      ← translateDegreeIndex_coe 3 (Operator.axisVector i) S.1,
      inner_walshL2_homogeneousWalshSynthesis, inner_walshL2_homogeneousWalshSynthesis,
      degreeRaiseDir]
    show degreeRaise i (degreeRaiseSymbol p i c) (raiseIndex i S) = _
    rw [degreeRaise_apply_raiseIndex, degreeRaiseSymbol_apply]
  · rw [if_neg hT, degreeRaiseDir]
    exact degreeRaise_apply_of_notMem i _ T hT

/-! ### The ordered picture -/

theorem orderedRestrict_walshOrdered (n : ℕ) (d : DegreeCoefficient n) :
    orderedRestrict n (walshOrdered n d) = d := by
  apply lp.ext
  funext S
  rw [orderedRestrict_apply, walshOrdered_apply_degreeEnum]

theorem orderedRestrict_orderedRepresentativeProjection (n : ℕ) (c : OrderedCoefficient n) :
    orderedRestrict n (orderedRepresentativeProjection n c) = orderedRestrict n c := by
  apply lp.ext
  funext S
  have hmem : degreeEnum S ∈ degreeRange n := ⟨S, rfl⟩
  rw [orderedRestrict_apply, orderedRestrict_apply, orderedRepresentativeProjection_apply,
    Set.indicator_of_mem hmem]

theorem orderedRepresentativeProjection_walshOrdered (n : ℕ) (d : DegreeCoefficient n) :
    orderedRepresentativeProjection n (walshOrdered n d) = walshOrdered n d := by
  rw [← walshOrdered_orderedRestrict, orderedRestrict_walshOrdered]

/-- **The ordered raising map.**  Reading a degree-three ordered coefficient at
its sorted representatives, raising, and reading the result back as an ordered
degree-four coefficient. -/
def orderedRaise (p : Fin 2 → ℝ) (i : Fin 2) :
    OrderedCoefficient 3 →L[ℂ] OrderedCoefficient 4 :=
  (walshOrdered 4).toContinuousLinearMap ∘L degreeRaiseDir p i ∘L orderedRestrict 3

theorem orderedRaise_apply (p : Fin 2 → ℝ) (i : Fin 2) (c : OrderedCoefficient 3) :
    orderedRaise p i c = walshOrdered 4 (degreeRaiseDir p i (orderedRestrict 3 c)) := rfl

theorem orderedRaise_walshOrdered (p : Fin 2 → ℝ) (i : Fin 2) (d : DegreeCoefficient 3) :
    orderedRaise p i (walshOrdered 3 d) = walshOrdered 4 (degreeRaiseDir p i d) := by
  rw [orderedRaise_apply, orderedRestrict_walshOrdered]

theorem norm_orderedRaise_le (p : Fin 2 → ℝ) (i : Fin 2) (c : OrderedCoefficient 3) :
    ‖orderedRaise p i c‖ ≤ ‖c‖ := by
  rw [orderedRaise_apply, (walshOrdered 4).norm_map]
  refine le_trans (norm_degreeRaiseDir_le p i _) ?_
  rw [norm_orderedRestrict]
  exact norm_orderedRepresentativeProjection_le 3 c

/-- **A trivial identity.  NOT the intertwining hypothesis it was once
advertised as.**  Both sides are the same term as `orderedRaise p i c`:
`orderedRaise` starts with `orderedRestrict 3`, so
`orderedRestrict_orderedRepresentativeProjection` erases the inner projection,
and it ends with `walshOrdered 4`, so `orderedRepresentativeProjection_walshOrdered`
erases the outer one.  The passage to the ordered representative already happens
inside `orderedRaise`; after unfolding this statement reads `X = X` and carries
no mathematical content.

MUST NOT SEAL: vacuous.
Never cite it as equation (46) (`eq:contract`, `manuscript.tex:1193-1198`) or as
any other paper statement.  It is used only to instantiate
`re_inner_image_orderedRestrict_orderedHInv_le` below, which is itself unused. -/
theorem orderedRaise_orderedRepresentativeProjection (p : Fin 2 → ℝ) (i : Fin 2)
    (c : OrderedCoefficient 3) :
    orderedRaise p i (orderedRepresentativeProjection 3 c)
      = orderedRepresentativeProjection 4 (orderedRaise p i c) := by
  rw [orderedRaise_apply, orderedRaise_apply,
    orderedRestrict_orderedRepresentativeProjection,
    orderedRepresentativeProjection_walshOrdered]

/-- **The ordered raising map realizes `walshRaiseDir`.**  Read at the sorted
enumeration of a degree-four Walsh index, the ordered raising map returns the
degree-four Walsh coefficient of the raised vector.
-/
theorem orderedRaise_apply_degreeEnum (p : Fin 2 → ℝ) (i : Fin 2)
    (d : DegreeCoefficient 3) (T : WalshDegreeIndex 4) :
    orderedRaise p i (walshOrdered 3 d) (degreeEnum T) =
      inner ℂ (Manhattan.walshL2 T.1)
        (walshRaiseDir p i (homogeneousWalshSynthesis 3 d)) := by
  rw [orderedRaise_walshOrdered, walshOrdered_apply_degreeEnum, degreeRaiseDir_apply]

/-- **A trivial inequality.  NOT equation (46) for the ordered raising map.**
Its two sides are the same term, because
`orderedRaise p i (orderedRepresentativeProjection 3 c) = orderedRaise p i c`
by `orderedRaise_orderedRepresentativeProjection`, which is itself `X = X`.
After unfolding this statement therefore reads `X ≤ X`.  The genuine ordered
form of equation (46) is
`re_inner_orderedHInv_orderedRepresentativeProjection_le`
(`Manhattan/Glue/OrderedInverse.lean`), which compares a real projection against
the raw coefficient.

MUST NOT SEAL: vacuous.
Never cite it as equation (46) (`eq:contract`, `manuscript.tex:1193-1198`).
-/
theorem re_inner_orderedHInv_orderedRaise_le {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (i : Fin 2) (c : OrderedCoefficient 3) :
    RCLike.re (inner ℂ (orderedHInv 4 hlam p
          (orderedRaise p i (orderedRepresentativeProjection 3 c)))
        (orderedRaise p i (orderedRepresentativeProjection 3 c)))
      ≤ RCLike.re (inner ℂ (orderedHInv 4 hlam p (orderedRaise p i c)) (orderedRaise p i c)) :=
  re_inner_image_orderedRestrict_orderedHInv_le 3 4 hlam p (orderedRaise p i)
    (orderedRaise_orderedRepresentativeProjection p i) c

/-! ### The insertion position

The appended origin line is *not* last in the sorted enumeration of the enlarged
Walsh index: its slot is the rank of its transverse coordinate among the
existing lines of the same axis.  That rank is defined here, and the sorted
enumeration of the enlarged index is the sorted enumeration of the original one
with the new line inserted at that slot. -/

section Enumeration

attribute [local instance] lineOrder

/-- The insertion slot of a line in an ordered tuple of lines: the number of
entries of the tuple that precede it. -/
def insertRank {n : ℕ} (a : LineIndex) (t : Fin n → LineIndex) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun y : Fin n => t y < a).card, by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun y => t y < a)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

theorem insertRank_coe {n : ℕ} (a : LineIndex) (t : Fin n → LineIndex) :
    ((insertRank a t : Fin (n + 1)) : ℕ)
      = (Finset.univ.filter fun y : Fin n => t y < a).card := rfl

/-- Every entry preceding the new line sits below its slot. -/
theorem lt_insertRank_of_lt {n : ℕ} {a : LineIndex} {t : Fin n → LineIndex}
    (hmono : StrictMono t) {y : Fin n} (h : t y < a) :
    (y : ℕ) < ((insertRank a t : Fin (n + 1)) : ℕ) := by
  have hsub : Finset.Iic y ⊆ Finset.univ.filter fun z : Fin n => t z < a := by
    intro z hz
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, lt_of_le_of_lt (hmono.monotone (Finset.mem_Iic.mp hz)) h⟩
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Iic] at hcard
  rw [insertRank_coe]
  omega

/-- Every entry not preceding the new line sits at or above its slot. -/
theorem insertRank_le_of_not_lt {n : ℕ} {a : LineIndex} {t : Fin n → LineIndex}
    (hmono : StrictMono t) {y : Fin n} (h : ¬ t y < a) :
    ((insertRank a t : Fin (n + 1)) : ℕ) ≤ (y : ℕ) := by
  have hsub : (Finset.univ.filter fun z : Fin n => t z < a) ⊆ Finset.Iio y := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_Iio]
    by_contra hc
    exact h (lt_of_le_of_lt (hmono.monotone (not_lt.mp hc)) hz.2)
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Iio] at hcard
  rw [insertRank_coe]
  omega

theorem lt_of_lt_insertRank {n : ℕ} {a : LineIndex} {t : Fin n → LineIndex}
    (hmono : StrictMono t) {y : Fin n}
    (h : (y : ℕ) < ((insertRank a t : Fin (n + 1)) : ℕ)) : t y < a := by
  by_contra hc
  have := insertRank_le_of_not_lt hmono hc
  omega

theorem lt_of_insertRank_le {n : ℕ} {a : LineIndex} {t : Fin n → LineIndex}
    (hmono : StrictMono t) (hne : ∀ y, t y ≠ a) {y : Fin n}
    (h : ((insertRank a t : Fin (n + 1)) : ℕ) ≤ (y : ℕ)) : a < t y := by
  rcases lt_trichotomy (t y) a with hlt | heq | hgt
  · have := lt_insertRank_of_lt hmono hlt
    omega
  · exact absurd heq (hne y)
  · exact hgt

theorem strictMono_degreeEnum {n : ℕ} (S : WalshDegreeIndex n) :
    StrictMono (degreeEnum S) := (S.1.orderEmbOfFin S.2).strictMono

/-- **The permutation of obstruction (b).**  The sorted enumeration of a Walsh
index enlarged by one new line is the sorted enumeration of the original index
with the new line inserted at its rank, not appended at the end. -/
theorem degreeEnum_eq_insertNth {n : ℕ} (a : LineIndex) (S : WalshDegreeIndex n)
    (ha : a ∉ S.1) (T : WalshDegreeIndex (n + 1)) (hT : T.1 = insert a S.1) :
    degreeEnum T = Fin.insertNth (insertRank a (degreeEnum S)) a (degreeEnum S) := by
  have hmono : StrictMono (degreeEnum S) := strictMono_degreeEnum S
  have hne : ∀ y, degreeEnum S y ≠ a := fun y hy => ha (hy ▸ degreeEnum_mem S y)
  symm
  refine Finset.orderEmbOfFin_unique T.2 ?_ ?_
  · refine (Fin.forall_iff_succAbove (insertRank a (degreeEnum S))).mpr ⟨?_, ?_⟩
    · rw [Fin.insertNth_apply_same, hT]
      exact Finset.mem_insert_self _ _
    · intro y
      rw [Fin.insertNth_apply_succAbove, hT]
      exact Finset.mem_insert_of_mem (degreeEnum_mem S y)
  · intro x z hxz
    rcases Fin.eq_self_or_eq_succAbove (insertRank a (degreeEnum S)) x with rfl | ⟨y, rfl⟩
    · rcases Fin.eq_self_or_eq_succAbove (insertRank a (degreeEnum S)) z with rfl | ⟨w, rfl⟩
      · exact absurd hxz (lt_irrefl _)
      · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        refine lt_of_insertRank_le hmono hne ?_
        have hle := (Fin.lt_succAbove_iff_le_castSucc _ w).mp hxz
        simpa [Fin.le_def] using hle
    · rcases Fin.eq_self_or_eq_succAbove (insertRank a (degreeEnum S)) z with rfl | ⟨w, rfl⟩
      · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
        refine lt_of_lt_insertRank hmono ?_
        have hlt := (Fin.succAbove_lt_iff_castSucc_lt _ y).mp hxz
        simpa [Fin.lt_def] using hlt
      · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact hmono (Fin.succAbove_lt_succAbove_iff.mp hxz)

end Enumeration

/-! ### The axis pattern of the enlarged index

Although the slot of the appended line moves with the transverse coordinates,
the *axis pattern* of the enlarged sorted enumeration does not: appending a
horizontal line to a type-`(1,1,2)` index always gives `(h,h,h,v)` and appending
a vertical one always gives `(h,h,v,v)`, because `horizontal_lt_vertical` puts
every horizontal line before every vertical one. -/

section Pattern

attribute [local instance] lineOrder

private theorem fin_two_cases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide

theorem comp_insertNth {α β : Type*} {n : ℕ} (g : α → β) (r : Fin (n + 1)) (a : α)
    (t : Fin n → α) :
    (fun x => g ((Fin.insertNth (α := fun _ => α) r a t) x))
      = Fin.insertNth (α := fun _ => β) r (g a) (fun y => g (t y)) := by
  funext x
  rcases Fin.eq_self_or_eq_succAbove r x with rfl | ⟨y, rfl⟩ <;> simp

theorem tuplePattern_insertNth {n : ℕ} (r : Fin (n + 1)) (a : LineIndex)
    (t : Fin n → LineIndex) :
    tuplePattern (Fin.insertNth r a t) = Fin.insertNth r a.1 (tuplePattern t) :=
  comp_insertNth Prod.fst r a t

theorem tupleCoord_insertNth {n : ℕ} (r : Fin (n + 1)) (a : LineIndex)
    (t : Fin n → LineIndex) :
    tupleCoord (Fin.insertNth r a t) = Fin.insertNth r a.2 (tupleCoord t) :=
  comp_insertNth Prod.snd r a t

/-- The axis pattern of a type-`(1,1,2)` index enlarged by the origin line of
type `i`. -/
def raisedPattern (i : Fin 2) : Fin 4 → Axis :=
  if i = 0 then ![Axis.horizontal, Axis.horizontal, Axis.horizontal, Axis.vertical]
  else ![Axis.horizontal, Axis.horizontal, Axis.vertical, Axis.vertical]

theorem insertNth_type112Pattern_horizontal {r : Fin 4} (hr : (r : ℕ) ≤ 2) :
    Fin.insertNth r Axis.horizontal type112Pattern = raisedPattern 0 := by
  fin_cases r
  · decide
  · decide
  · decide
  · exact absurd hr (by decide)

theorem insertNth_type112Pattern_vertical {r : Fin 4} (hr : 2 ≤ (r : ℕ)) :
    Fin.insertNth r Axis.vertical type112Pattern = raisedPattern 1 := by
  fin_cases r
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · decide
  · decide

/-- The sorted enumeration of a type-`(1,1,2)` index enlarged by the origin
line of type `i`. -/
theorem degreeEnum_raiseIndex_type112 (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    degreeEnum (raiseIndex i ⟨type112Degree T, hT⟩)
      = Fin.insertNth (insertRank (Manhattan.originLine i) (degreeEnum (type112Degree T)))
          (Manhattan.originLine i) (degreeEnum (type112Degree T)) :=
  degreeEnum_eq_insertNth _ _ hT _ rfl

/-- A horizontal origin line is inserted at or before the vertical slot. -/
theorem insertRank_horizontal_le (T : Manhattan.Type112Index) :
    ((insertRank (Manhattan.originLine 0) (degreeEnum (type112Degree T)) : Fin 4) : ℕ) ≤ 2 := by
  have hval : degreeEnum (type112Degree T) 2
      = ((Axis.vertical, Manhattan.type112RawIndex T 2) : LineIndex) := by
    rw [degreeEnum_type112Degree]
    rfl
  have hlt : ((Axis.horizontal, (0 : ℤ)) : LineIndex)
      < (Axis.vertical, Manhattan.type112RawIndex T 2) :=
    horizontal_lt_vertical _ _
  have hnot : ¬ degreeEnum (type112Degree T) 2 < Manhattan.originLine 0 := by
    rw [hval]
    have : Manhattan.originLine 0 = ((Axis.horizontal, (0 : ℤ)) : LineIndex) := by
      simp [Manhattan.originLine]
    rw [this]
    exact asymm hlt
  have h := insertRank_le_of_not_lt (strictMono_degreeEnum (type112Degree T)) hnot
  simpa using h

/-- A vertical origin line is inserted after both horizontal slots. -/
theorem two_le_insertRank_vertical (T : Manhattan.Type112Index) :
    2 ≤ ((insertRank (Manhattan.originLine 1) (degreeEnum (type112Degree T)) : Fin 4) : ℕ) := by
  have hval : degreeEnum (type112Degree T) 1
      = ((Axis.horizontal, Manhattan.type112RawIndex T 1) : LineIndex) := by
    rw [degreeEnum_type112Degree]
    rfl
  have hlt : degreeEnum (type112Degree T) 1 < Manhattan.originLine 1 := by
    rw [hval]
    have : Manhattan.originLine 1 = ((Axis.vertical, (0 : ℤ)) : LineIndex) := by
      simp [Manhattan.originLine]
    rw [this]
    exact horizontal_lt_vertical _ _
  have h := lt_insertRank_of_lt (strictMono_degreeEnum (type112Degree T)) hlt
  simp only [Fin.val_one] at h
  omega

/-- **The axis pattern is constant.**  Enlarging a type-`(1,1,2)` index by the
origin line of type `i` gives a sorted enumeration whose axis pattern is
`raisedPattern i`, whatever the transverse coordinates. -/
theorem tuplePattern_degreeEnum_raiseIndex (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    tuplePattern (degreeEnum (raiseIndex i ⟨type112Degree T, hT⟩)) = raisedPattern i := by
  rw [degreeEnum_raiseIndex_type112, tuplePattern_insertNth, tuplePattern_degreeEnum_type112]
  rcases fin_two_cases i with rfl | rfl
  · have h : (Manhattan.originLine 0).1 = Axis.horizontal := by simp [Manhattan.originLine]
    rw [h]
    exact insertNth_type112Pattern_horizontal (insertRank_horizontal_le T)
  · have h : (Manhattan.originLine 1).1 = Axis.vertical := by simp [Manhattan.originLine]
    rw [h]
    exact insertNth_type112Pattern_vertical (two_le_insertRank_vertical T)

/-- **The appended line carries transverse coordinate zero.**  Its slot is the
insertion rank, and its Fourier factor is therefore `1`. -/
theorem tupleCoord_degreeEnum_raiseIndex (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    tupleCoord (degreeEnum (raiseIndex i ⟨type112Degree T, hT⟩))
      = Fin.insertNth (insertRank (Manhattan.originLine i) (degreeEnum (type112Degree T)))
          (0 : ℤ) (Manhattan.type112RawIndex T) := by
  rw [degreeEnum_raiseIndex_type112, tupleCoord_insertNth, tupleCoord_degreeEnum_type112]
  rfl

end Pattern

/-! ### The frequency form

The Walsh coefficient of the raised vector at the enlarged index is the
`raisingSymbol` multiple of the degree-three frequency function, read at the
*original* three frequencies: the appended line carries transverse coordinate
`0`, so its Fourier factor is `1` and the enlarged character does not depend on
the new torus variable. -/

section Frequency

attribute [local instance] lineOrder
attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] orderedInverseUnitAddCircleMeasureSpace
attribute [local instance] orderedInverseUnitAddCircleIsProbabilityMeasure

open UnitAddTorus

/-- **The appended line's Fourier factor is `1`.**  A character whose frequency
is `0` in one slot does not depend on the torus variable of that slot. -/
theorem mFourier_insertNth_zero {n : ℕ} (r : Fin (n + 1)) (k : Fin n → ℤ)
    (t : UnitAddTorus (Fin (n + 1))) :
    mFourier (Fin.insertNth (α := fun _ => ℤ) r (0 : ℤ) k) t
      = mFourier k (Fin.removeNth r t) := by
  show (∏ a : Fin (n + 1),
      fourier ((Fin.insertNth (α := fun _ => ℤ) r (0 : ℤ) k) a) (t a))
    = ∏ y : Fin n, fourier (k y) (t (r.succAbove y))
  rw [Fin.prod_univ_succAbove _ r]
  simp

/-- **The degree-four coefficient of the raising map, in frequency form.**  For
a general type-`(1,1,2)` coefficient `c`, the entry of `degreeRaiseDir p i` at
the index obtained by appending the origin line of type `i` is the Fourier
coefficient of `raisingSymbol p i` times the symmetrized degree-three frequency
function. -/
theorem degreeRaiseDir_raiseIndex_type112 (c : ℓ²(Manhattan.Type112Index, ℂ))
    (p : Fin 2 → ℝ) (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    degreeRaiseDir p i (type112Extend c) (raiseIndex i ⟨type112Degree T, hT⟩)
      = mFourierCoeff
          (fun t => raisingSymbol p i type112Pattern t *
            (type112SymmFreqFun c : UnitAddTorus (Fin 3) → ℂ) t)
          (Manhattan.type112RawIndex T) := by
  have hlines : patternLines type112Pattern (Manhattan.type112RawIndex T) = T.1 := by
    rw [patternLines_type112Pattern]
    exact type112Lines_eq T
  have hset : (raiseIndex i ⟨type112Degree T, hT⟩).1
      = insert (Manhattan.originLine i)
          (patternLines type112Pattern (Manhattan.type112RawIndex T)) := by
    rw [hlines]
    rfl
  rw [degreeRaiseDir_apply, ← type112WalshSynthesis_eq_homogeneous, hset]
  refine inner_walshL2_walshRaiseDir_type112SymmFreqFun c p i
    (Manhattan.type112RawIndex T) ?_
  rw [hlines]
  exact hT

/-- **The ordered raising map in frequency form.**  Read at the sorted
enumeration of the enlarged index, that is, at the degree-three sorted tuple
with the origin line inserted at its rank, the ordered raising map returns the
Fourier coefficient of `raisingSymbol p i` times the degree-three frequency
function.
-/
theorem orderedRaise_insertNth_type112 (c : ℓ²(Manhattan.Type112Index, ℂ))
    (p : Fin 2 → ℝ) (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    orderedRaise p i (walshOrdered 3 (type112Extend c))
        (Fin.insertNth (insertRank (Manhattan.originLine i) (degreeEnum (type112Degree T)))
          (Manhattan.originLine i) (degreeEnum (type112Degree T)))
      = mFourierCoeff
          (fun t => raisingSymbol p i type112Pattern t *
            (type112SymmFreqFun c : UnitAddTorus (Fin 3) → ℂ) t)
          (Manhattan.type112RawIndex T) := by
  rw [orderedRaise_walshOrdered, ← degreeEnum_raiseIndex_type112 i T hT,
    walshOrdered_apply_degreeEnum]
  exact degreeRaiseDir_raiseIndex_type112 c p i T hT

/-- The elementary frequency vector of the enlarged index: one axis pattern,
and the degree-three frequencies with a `0` inserted at the new slot.
-/
theorem orderedFreqFamily_degreeEnum_raiseIndex (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) :
    orderedFreqFamily 4 (degreeEnum (raiseIndex i ⟨type112Degree T, hT⟩))
      = lp.single 2 (raisedPattern i)
          (mFourierLp 2 (Fin.insertNth (α := fun _ => ℤ)
            (insertRank (Manhattan.originLine i) (degreeEnum (type112Degree T)))
            (0 : ℤ) (Manhattan.type112RawIndex T))) := by
  rw [orderedFreqFamily, tuplePattern_degreeEnum_raiseIndex,
    tupleCoord_degreeEnum_raiseIndex]

/-- **Constant in the new line's torus variable.**  The degree-four character of
the enlarged index is the degree-three character of the original frequencies,
evaluated after deleting the new slot.
-/
theorem mFourier_tupleCoord_degreeEnum_raiseIndex (i : Fin 2) (T : Manhattan.Type112Index)
    (hT : Manhattan.originLine i ∉ T.1) (t : UnitAddTorus (Fin 4)) :
    mFourier (tupleCoord (degreeEnum (raiseIndex i ⟨type112Degree T, hT⟩))) t
      = mFourier (Manhattan.type112RawIndex T)
          (Fin.removeNth
            (insertRank (Manhattan.originLine i) (degreeEnum (type112Degree T))) t) := by
  rw [tupleCoord_degreeEnum_raiseIndex, mFourier_insertNth_zero]

end Frequency

end Manhattan.Glue
