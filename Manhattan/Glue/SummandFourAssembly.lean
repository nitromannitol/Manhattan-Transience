import Manhattan.Glue.SummandFour
import Manhattan.Glue.RaisingEnergy
import Manhattan.Glue.OrderedContractivityType112
import Manhattan.Glue.TransportDischarge

/-!
# Summand 4 of (22), assembled

the formalization proved the operator half of Lemma 5.2 for a general
degree-three coefficient (`tsum_integral_inv_symbolWeight_degreeRaiseDir_le`),
and the formalization reduced summand 4 of (22) to that bound
(`sectorDFourForm_le_dir_integrals`, `summandFourBound_of_sectorDFour`). Two
things stood between them and `SummandFourBound`, and this file supplies both.

* The **synthesis identity** `homogeneousWalshSynthesis 4 (degreeRaiseDir p i g)
  = walshRaiseDir p i (homogeneousWalshSynthesis 3 g)`, which says that module
  A5's coefficient-side raising map realises the operator `D` in degree four.
  It is `degreeRaiseDir_apply` together with the vanishing of the
  Walsh coefficients of a degree-four vector off cardinality four.
* **Equation (46) for the multiplier weight**
  (`multiplier_integral_type112DiagonalProjection_le`). The manuscript's
  `Pi_3` is realised on the raw type-`(1,1,2)` Fourier coefficients by the
  restriction to the strictly ordered row pairs, and the formalization proved that any
  nonnegative operator commuting with that restriction has smaller energy after
  it (`re_inner_rawOrderedProjection_le`); what was missing was the operator.
  The multiplier `M(P)` of `eq:M` = (35) (`manuscript.tex:983`) is
  multiplication, in the line-frequency variables, by a function of the *sum* of
  the two row frequencies and of the column frequency, so its Fourier
  coefficients are carried by the vectors with equal row entries, and those
  shifts preserve the strict order of the two rows
  (`inner_mFourierLp_contMul_eq_zero`,
  `rawOrderedProjection_comm_rawWeightOp`). That is an argument from `M`'s own
  Fourier support, and it deliberately does **not** invoke the manuscript's
  closing justification for Lemma 5.1, "a multiplier depending on `P` is a
  linear combination of simultaneous translations of all line indices"
  (`manuscript.tex:1233-1235`). Finite combinations of those translations are
  exactly the trigonometric polynomials in `P`, and the terms `2|sin(P_i/2)|` of
  `M` are not: their Fourier coefficients are `O(n^{-2})` and none vanishes.
  The conclusion of Lemma 5.1 is true in full generality all the same; ruling
  The stated reason is recorded as the underspecification E-010,
  with no paper edit.

With the `(shift)` phase of `Manhattan.type112ShiftTwist` in place the momentum
bridge is an identity (`multiplier_integral_type112ShiftTwist_frozen`), exactly
as for summand 2, so no momentum comparison is needed. The chain closes at
`rawCubicMultiplierEnergy`, which Proposition 4.2 bounds by `2C√L`, and summand
4 is discharged with the constant `16 C`
(`sectorDFourForm_shiftedCorrectionWalsh_le`, `summandFourBound_proved`).

Paper: `manuscript.tex:1196-1205` (Lemma 5.2), `manuscript.tex:1257-1272` (its
proof), `manuscript.tex:1193-1198` (equation (46), `eq:contract`), `manuscript.tex:812-814`
(`eq:shift`).
-/

noncomputable section
open MeasureTheory UnitAddTorus Set
open ComplexConjugate InnerProductSpace RCLike
namespace Manhattan.Glue
attribute [local instance] Real.fact_zero_lt_one

private theorem walshVector_ext' {x y : WalshL2}
    (h : ∀ S : Finset LineIndex,
      inner ℂ (Manhattan.walshL2 S) x = inner ℂ (Manhattan.walshL2 S) y) :
    x = y := by
  apply Manhattan.walshBasis.repr.injective
  apply lp.ext
  funext S
  rw [Manhattan.walshBasis.repr_apply_apply, Manhattan.walshBasis.repr_apply_apply,
    Manhattan.walshBasis_apply, h]

/-- **The synthesis identity for the raising map.** -/
theorem homogeneousWalshSynthesis_degreeRaiseDir (p : Fin 2 → ℝ) (i : Fin 2)
    (g : DegreeCoefficient 3) :
    homogeneousWalshSynthesis 4 (degreeRaiseDir p i g) =
      walshRaiseDir p i (homogeneousWalshSynthesis 3 g) := by
  refine walshVector_ext' fun U => ?_
  by_cases hU : U.card = 4
  · have h := inner_walshL2_homogeneousWalshSynthesis 4 (degreeRaiseDir p i g) ⟨U, hU⟩
    rw [show ((⟨U, hU⟩ : WalshDegreeIndex 4) : Finset LineIndex) = U from rfl] at h
    rw [h, degreeRaiseDir_apply]
  · rw [inner_walshL2_eq_zero_of_mem_walshDegree
      (homogeneousWalshSynthesis_mem_degree 4 _) hU,
      inner_walshL2_walshRaiseDir_eq_zero p i
        (homogeneousWalshSynthesis_mem_degree 3 g) hU]

def antiShift (c : UnitAddCircle) : UnitAddTorus (Fin 3) := ![c, -c, 0]

private theorem exists_int_eq {r : ℝ} (h : ((r : ℝ) : UnitAddCircle) = 0) :
    ∃ k : ℤ, r = (k : ℝ) := by
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h
  exact ⟨k, by simpa using hk.symm⟩

theorem torusLift_add_antiShift (x y c : UnitAddCircle) :
    ∃ k : ℤ, torusLift (x + c) + torusLift (y + (-c))
      = torusLift x + torusLift y + (k : ℝ) := by
  have hzero : ((torusLift (x + c) + torusLift (y + (-c)) - torusLift x - torusLift y : ℝ) :
      UnitAddCircle) = 0 := by
    show ((torusLift (x + c) : ℝ) : UnitAddCircle) + ((torusLift (y + (-c)) : ℝ) : UnitAddCircle)
        - ((torusLift x : ℝ) : UnitAddCircle) - ((torusLift y : ℝ) : UnitAddCircle) = 0
    rw [torusLift_coe, torusLift_coe, torusLift_coe, torusLift_coe]
    abel
  obtain ⟨k, hk⟩ := exists_int_eq hzero
  exact ⟨k, by linarith⟩

theorem multiplier_congr_int (kappa : ℝ) (q : Estimates.Parameters) (P Q : Fin 2 → ℝ)
    (h : ∀ k : Fin 2, ∃ j : ℤ, P k = Q k + j * (2 * Real.pi)) :
    Estimates.multiplier kappa q P = Estimates.multiplier kappa q Q := by
  obtain ⟨j0, h0⟩ := h 0
  obtain ⟨j1, h1⟩ := h 1
  have d0 : Estimates.dispersion (P 0) = Estimates.dispersion (Q 0) := by
    rw [h0, dispersion_add_int_two_pi]
  have d1 : Estimates.dispersion (P 1) = Estimates.dispersion (Q 1) := by
    rw [h1, dispersion_add_int_two_pi]
  rw [multiplier_eq_sqrt, multiplier_eq_sqrt, Estimates.theta, Estimates.theta, d0, d1]

theorem multiplier_totalFrequency_antiShift (kappa : ℝ) (q : Estimates.Parameters)
    (P : Fin 2 → ℝ) (c : UnitAddCircle) (t : UnitAddTorus (Fin 3)) :
    Estimates.multiplier kappa q (totalFrequency 3 P type112Pattern (t + antiShift c))
      = Estimates.multiplier kappa q (totalFrequency 3 P type112Pattern t) := by
  refine multiplier_congr_int _ _ _ _ ?_
  intro k
  fin_cases k
  · refine ⟨0, ?_⟩
    show totalFrequency 3 P type112Pattern (t + antiShift c) 0
      = totalFrequency 3 P type112Pattern t 0 + ((0 : ℤ) : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_zero, totalFrequency_type112_zero,
      show (t + antiShift c) 2 = t 2 by
        show t 2 + antiShift c 2 = t 2
        rw [show antiShift c 2 = (0 : UnitAddCircle) from rfl, add_zero]]
    push_cast; ring
  · obtain ⟨j, hj⟩ := torusLift_add_antiShift (t 0) (t 1) c
    refine ⟨j, ?_⟩
    show totalFrequency 3 P type112Pattern (t + antiShift c) 1
      = totalFrequency 3 P type112Pattern t 1 + (j : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_one, totalFrequency_type112_one,
      show (t + antiShift c) 0 = t 0 + c from rfl,
      show (t + antiShift c) 1 = t 1 + (-c) from rfl, hj]
    ring

/-- The multiplier weight of the type-`(1,1,2)` pattern, as a continuous symbol. -/
def multiplierWeightMap (q : Estimates.Parameters) (P : Fin 2 → ℝ) :
    C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨fun t => ((Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      (continuous_multiplier_totalFrequency 3 40 q P type112Pattern)⟩

@[simp] theorem multiplierWeightMap_apply (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (t : UnitAddTorus (Fin 3)) :
    multiplierWeightMap q P t =
      ((Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) : ℝ) : ℂ) := rfl


theorem mFourier_antiShift (v : RawType112Index) (r : ℝ) :
    mFourier v (antiShift ((r : ℝ) : UnitAddCircle))
      = Complex.exp (2 * Real.pi * Complex.I * ((v 0 - v 1 : ℤ) : ℂ) * (r : ℂ)) := by
  have h : mFourier v (antiShift ((r : ℝ) : UnitAddCircle))
      = fourier (v 0) (((r : ℝ) : UnitAddCircle)) * fourier (v 1) ((((-r) : ℝ) : UnitAddCircle))
        * fourier (v 2) (0 : UnitAddCircle) := by
    show (∏ i : Fin 3, fourier (v i) (antiShift ((r : ℝ) : UnitAddCircle) i)) = _
    rw [Fin.prod_univ_three]
    rfl
  rw [h, fourier_eval_zero, fourier_coe_apply, fourier_coe_apply, mul_one, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **The Fourier support of the multiplier weight.** The weight depends on
the two row frequencies only through their sum, so its Fourier coefficients
vanish off the vectors with equal row entries. -/
theorem inner_mFourierLp_contMul_eq_zero (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    {m n : Manhattan.RawType112Index} (h : m 0 - n 0 ≠ m 1 - n 1) :
    inner ℂ (mFourierLp 2 n) (contMul 3 (multiplierWeightMap q P) (mFourierLp 2 m)) = 0 := by
  classical
  set W := multiplierWeightMap q P with hW
  set f : UnitAddTorus (Fin 3) → ℂ :=
    fun t => (starRingEnd ℂ) (mFourier n t) * (W t * mFourier m t) with hf
  have hI : inner ℂ (mFourierLp 2 n) (contMul 3 W (mFourierLp 2 m))
      = ∫ t, f t ∂(LineTorusMeasure 3) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mFourierLp (d := Fin 3) 2 n, coeFn_contMul W (mFourierLp 2 m),
      coeFn_mFourierLp (d := Fin 3) 2 m] with t h1 h2 h3
    rw [RCLike.inner_apply, h1, h2, h3, hf]
    ring
  set K : ℤ := (m 0 - n 0) - (m 1 - n 1) with hK
  have hKne : K ≠ 0 := by
    rw [hK]; omega
  set r : ℝ := 1 / (2 * (K : ℝ)) with hr
  set cc : UnitAddCircle := ((r : ℝ) : UnitAddCircle) with hcc
  set θ : UnitAddTorus (Fin 3) := antiShift cc with hθ
  have hKcast : ((K : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hKne
  have hphase : mFourier (m - n) θ = -1 := by
    rw [hθ, hcc, mFourier_antiShift]
    have hv : ((m - n) 0 - (m - n) 1 : ℤ) = K := by
      simp only [Pi.sub_apply, hK]
    rw [hv]
    have : 2 * (Real.pi : ℂ) * Complex.I * ((K : ℤ) : ℂ) * (r : ℂ)
        = (Real.pi : ℂ) * Complex.I := by
      rw [hr]
      have hKC : ((K : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hKne
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hshiftf : ∀ t : UnitAddTorus (Fin 3), f (t + θ) = (-1 : ℂ) * f t := by
    intro t
    have e1 : mFourier n (t + θ) = mFourier n t * mFourier n θ := mFourier_add_arg n t θ
    have e2 : mFourier m (t + θ) = mFourier m t * mFourier m θ := mFourier_add_arg m t θ
    have e3 : W (t + θ) = W t := by
      rw [hW, multiplierWeightMap_apply, multiplierWeightMap_apply, hθ,
        multiplier_totalFrequency_antiShift]
    have e4 : (starRingEnd ℂ) (mFourier n θ) * mFourier m θ = mFourier (m - n) θ := by
      rw [← mFourier_neg, ← mFourier_add,
        show (-n + m : Manhattan.RawType112Index) = m - n from by abel]
    rw [hf]
    simp only
    rw [e1, e2, e3, map_mul, ← hphase, ← e4]
    ring
  have hself : (∫ t, f (t + θ) ∂(LineTorusMeasure 3)) = ∫ t, f t ∂(LineTorusMeasure 3) :=
    integral_add_right_eq_self f θ
  have hneg : (∫ t, f t ∂(LineTorusMeasure 3)) = -∫ t, f t ∂(LineTorusMeasure 3) := by
    calc (∫ t, f t ∂(LineTorusMeasure 3))
        = ∫ t, f (t + θ) ∂(LineTorusMeasure 3) := hself.symm
      _ = ∫ t, (-1 : ℂ) * f t ∂(LineTorusMeasure 3) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [hshiftf t]
      _ = -∫ t, f t ∂(LineTorusMeasure 3) := by
          rw [integral_const_mul]; ring
  rw [hI]
  linear_combination hneg / 2


theorem contMul_add_right {n : ℕ} (g : C(UnitAddTorus (Fin n), ℂ))
    (u v : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n g (u + v) = contMul n g u + contMul n g v := by
  apply Lp.ext
  filter_upwards [coeFn_contMul g (u + v), Lp.coeFn_add (contMul n g u) (contMul n g v),
    coeFn_contMul g u, coeFn_contMul g v, Lp.coeFn_add u v] with t h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]

theorem contMul_smul_right {n : ℕ} (a : ℂ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    contMul n g (a • u) = a • contMul n g u := by
  apply Lp.ext
  filter_upwards [coeFn_contMul g (a • u), Lp.coeFn_smul a (contMul n g u),
    coeFn_contMul g u, Lp.coeFn_smul a u] with t h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem norm_contMul_le {n : ℕ} (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) :
    ‖contMul n g u‖ ≤ ‖g‖ * ‖u‖ := by
  have hle : ‖contMul n g u‖ ≤ ‖((‖g‖ : ℝ) : ℂ) • u‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_contMul g u, Lp.coeFn_smul ((‖g‖ : ℝ) : ℂ) u] with t h1 h2
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg g)]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm t) (norm_nonneg _)
  refine hle.trans (le_of_eq ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg g)]

/-- Multiplication by a continuous symbol, as a bounded operator. -/
def contMulL (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ)) :
    Lp ℂ 2 (LineTorusMeasure n) →L[ℂ] Lp ℂ 2 (LineTorusMeasure n) :=
  LinearMap.mkContinuous
    { toFun := contMul n g
      map_add' := contMul_add_right g
      map_smul' := fun a u => contMul_smul_right a g u }
    ‖g‖ (fun u => norm_contMul_le g u)

@[simp] theorem contMulL_apply (n : ℕ) (g : C(UnitAddTorus (Fin n), ℂ))
    (u : Lp ℂ 2 (LineTorusMeasure n)) : contMulL n g u = contMul n g u := rfl


/-! ### The multiplier weight transported to the raw type-`(1,1,2)` carrier -/

/-- The multiplier in the total frequency `P`, read on the raw type-`(1,1,2)`
Fourier coefficients. -/
def rawWeightOp (q : Estimates.Parameters) (P : Fin 2 → ℝ) :
    ℓ²(Manhattan.RawType112Index, ℂ) →L[ℂ] ℓ²(Manhattan.RawType112Index, ℂ) :=
  (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.toLinearIsometry.toContinuousLinearMap ∘L
    (contMulL 3 (multiplierWeightMap q P) ∘L
      (UnitAddTorus.mFourierBasis
        (d := Fin 3)).repr.symm.toLinearIsometry.toContinuousLinearMap)

theorem rawWeightOp_apply (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    rawWeightOp q P c =
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr
        (contMul 3 (multiplierWeightMap q P)
          ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c)) := rfl

/-- The transported quadratic form is the weighted integral. -/
theorem re_inner_rawWeightOp_eq_integral (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    RCLike.re (inner ℂ (rawWeightOp q P c) c) =
      ∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  set F := (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c with hF
  have hc : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr F = c := by
    rw [hF, LinearIsometryEquiv.apply_symm_apply]
  have hinner : inner ℂ (rawWeightOp q P c) c =
      inner ℂ (contMul 3 (multiplierWeightMap q P) F) F := by
    rw [rawWeightOp_apply, ← hF, ← hc,
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.inner_map_map]
  rw [hinner]
  refine inner_lp_eq_weighted_integral _ _ _ ?_
  filter_upwards [coeFn_contMul (multiplierWeightMap q P) F] with t ht
  rw [ht, multiplierWeightMap_apply]

theorem re_inner_rawWeightOp_nonneg {q : Estimates.Parameters} (hlam : 0 ≤ q.lambda)
    (P : Fin 2 → ℝ) (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    0 ≤ RCLike.re (inner ℂ (rawWeightOp q P c) c) := by
  rw [re_inner_rawWeightOp_eq_integral]
  refine integral_nonneg fun t => ?_
  exact mul_nonneg (Estimates.multiplier_nonneg (by norm_num) hlam _) (sq_nonneg _)

theorem rawWeightOp_single (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (m n : Manhattan.RawType112Index) :
    (rawWeightOp q P (lp.single 2 m (1 : ℂ))) n =
      inner ℂ (mFourierLp 2 n) (contMul 3 (multiplierWeightMap q P) (mFourierLp 2 m)) := by
  have hsym : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (lp.single 2 m (1 : ℂ))
      = mFourierLp 2 m := by
    rw [HilbertBasis.repr_symm_single, UnitAddTorus.coe_mFourierBasis]
  rw [rawWeightOp_apply, hsym,
    (UnitAddTorus.mFourierBasis (d := Fin 3)).repr_apply_apply,
    UnitAddTorus.coe_mFourierBasis]

theorem rawOrderedProjection_single_of_mem {m : Manhattan.RawType112Index}
    (hm : m ∈ rawOrderedSet) :
    rawOrderedProjection (lp.single 2 m (1 : ℂ) : ℓ²(Manhattan.RawType112Index, ℂ))
      = lp.single 2 m (1 : ℂ) := by
  classical
  apply lp.ext
  funext n
  rw [rawOrderedProjection_apply]
  by_cases hn : n ∈ rawOrderedSet
  · rw [Set.indicator_of_mem hn]
  · rw [Set.indicator_of_notMem hn, lp.single_apply, Pi.single_apply, if_neg]
    rintro rfl
    exact hn hm

theorem rawOrderedProjection_single_of_notMem {m : Manhattan.RawType112Index}
    (hm : m ∉ rawOrderedSet) :
    rawOrderedProjection (lp.single 2 m (1 : ℂ) : ℓ²(Manhattan.RawType112Index, ℂ)) = 0 := by
  classical
  apply lp.ext
  funext n
  rw [rawOrderedProjection_apply]
  by_cases hn : n ∈ rawOrderedSet
  · rw [Set.indicator_of_mem hn, lp.single_apply, Pi.single_apply, if_neg]
    · rfl
    · rintro rfl
      exact hm hn
  · rw [Set.indicator_of_notMem hn]
    rfl

/-- **The multiplier commutes with the ordered-representative projection.** -/
theorem rawOrderedProjection_comm_rawWeightOp (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    rawOrderedProjection (rawWeightOp q P c) = rawWeightOp q P (rawOrderedProjection c) := by
  classical
  refine l2_ext' (rawOrderedProjection ∘L rawWeightOp q P)
    (rawWeightOp q P ∘L rawOrderedProjection) ?_ c
  intro m
  show rawOrderedProjection (rawWeightOp q P (lp.single 2 m (1 : ℂ)))
    = rawWeightOp q P (rawOrderedProjection (lp.single 2 m (1 : ℂ)))
  have hzero : ∀ n : Manhattan.RawType112Index,
      ¬ ((n ∈ rawOrderedSet) ↔ (m ∈ rawOrderedSet)) →
      (rawWeightOp q P (lp.single 2 m (1 : ℂ))) n = 0 := by
    intro n hn
    refine (rawWeightOp_single q P m n).trans ?_
    refine inner_mFourierLp_contMul_eq_zero q P ?_
    intro hdiff
    refine hn ?_
    simp only [mem_rawOrderedSet]
    omega
  apply lp.ext
  funext n
  by_cases hm : m ∈ rawOrderedSet
  · rw [rawOrderedProjection_single_of_mem hm, rawOrderedProjection_apply]
    by_cases hn : n ∈ rawOrderedSet
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      exact (hzero n (by tauto)).symm
  · rw [rawOrderedProjection_single_of_notMem hm, map_zero, rawOrderedProjection_apply]
    by_cases hn : n ∈ rawOrderedSet
    · rw [Set.indicator_of_mem hn]
      exact hzero n (by tauto)
    · rw [Set.indicator_of_notMem hn]
      rfl

/-- **Equation (46) for the multiplier weight.** Restricting the raw
type-`(1,1,2)` Fourier coefficients to the strictly ordered row pairs cannot
increase the multiplier energy. -/
theorem multiplier_integral_rawOrderedProjection_le {q : Estimates.Parameters}
    (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    (∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (rawOrderedProjection c)) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      ≤ ∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  rw [← re_inner_rawWeightOp_eq_integral, ← re_inner_rawWeightOp_eq_integral]
  exact re_inner_rawOrderedProjection_le (rawWeightOp q P)
    (rawOrderedProjection_comm_rawWeightOp q P)
    (fun x => re_inner_rawWeightOp_nonneg hlam P x) c

/-! ### The projected type-`(1,1,2)` coefficient -/

theorem rawExtend_type112DiagonalProjection (d : ℓ²(Manhattan.RawType112Index, ℂ)) :
    rawExtend (Manhattan.type112DiagonalProjection d) = rawOrderedProjection d := by
  classical
  apply lp.ext
  funext n
  rw [rawOrderedProjection_apply]
  by_cases hn : n 0 < n 1
  · have hS : Manhattan.type112RawIndex
        (Manhattan.orderedType112Equiv ⟨n, hn⟩) = n :=
      type112RawIndex_orderedType112Equiv ⟨n, hn⟩
    have h1 : rawExtend (Manhattan.type112DiagonalProjection d)
        (Manhattan.type112RawIndex (Manhattan.orderedType112Equiv ⟨n, hn⟩))
        = Manhattan.type112DiagonalProjection d
          (Manhattan.orderedType112Equiv ⟨n, hn⟩) :=
      rawExtend_apply_type112RawIndex _ _
    rw [hS] at h1
    rw [h1, Manhattan.type112DiagonalProjection_apply, hS,
      Set.indicator_of_mem (by simpa using hn)]
  · rw [rawExtend_apply_of_not_lt _ hn, Set.indicator_of_notMem (by simpa using hn)]

theorem type112FreqFun_eq_repr_symm (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    type112FreqFun c
      = (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (rawExtend c) := rfl

/-- **Equation (46) for the multiplier weight, in the type-`(1,1,2)`
coordinates.** -/
theorem multiplier_integral_type112DiagonalProjection_le {q : Estimates.Parameters}
    (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) (d : ℓ²(Manhattan.RawType112Index, ℂ)) :
    (∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112DiagonalProjection d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      ≤ ∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  rw [type112FreqFun_eq_repr_symm, rawExtend_type112DiagonalProjection]
  exact multiplier_integral_rawOrderedProjection_le hlam P d

/-! ### The frozen momentum is the manuscript's total frequency -/

theorem multiplier_totalFrequency_type112Pattern (q : Estimates.Parameters) (p₂ : ℝ)
    (t : UnitAddTorus (Fin 3)) :
    Estimates.multiplier 40 q (totalFrequency 3 ![0, -p₂] type112Pattern t)
      = Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ t) := by
  refine multiplier_congr_int _ _ _ _ ?_
  intro k
  obtain ⟨k0, hk0⟩ := two_pi_torusLift (t 0)
  obtain ⟨k1, hk1⟩ := two_pi_torusLift (t 1)
  obtain ⟨k2, hk2⟩ := two_pi_torusLift (t 2)
  fin_cases k
  · refine ⟨k2, ?_⟩
    show totalFrequency 3 ![0, -p₂] type112Pattern t 0
      = rawCorrectionTotalFrequency p₂ t 0 + (k2 : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_zero,
      show (![(0 : ℝ), -p₂] : Fin 2 → ℝ) 0 = 0 from rfl,
      show rawCorrectionTotalFrequency p₂ t 0 = Manhattan.unitTorusAngle (t 2) by
        simp [rawCorrectionTotalFrequency, Estimates.mixedTotalFrequency]]
    linarith
  · refine ⟨k0 + k1, ?_⟩
    show totalFrequency 3 ![0, -p₂] type112Pattern t 1
      = rawCorrectionTotalFrequency p₂ t 1 + ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_one,
      show (![(0 : ℝ), -p₂] : Fin 2 → ℝ) 1 = -p₂ from rfl,
      show rawCorrectionTotalFrequency p₂ t 1
          = Manhattan.unitTorusAngle (t 0) + Manhattan.unitTorusAngle (t 1) - p₂ by
        simp [rawCorrectionTotalFrequency, Estimates.mixedTotalFrequency]]
    push_cast
    linarith

/-! ### The (shift) phase moves the momentum of the multiplier form -/

theorem multiplier_totalFrequency_type112_add_shiftTorusPoint (q : Estimates.Parameters)
    (P : Fin 2 → ℝ) (p₁ p₂ : ℝ) (t : UnitAddTorus (Fin 3)) :
    Estimates.multiplier 40 q
        (totalFrequency 3 P type112Pattern (t + Manhattan.shiftTorusPoint p₁ p₂))
      = Estimates.multiplier 40 q
        (totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t) := by
  obtain ⟨k0, hk0⟩ := torusLift_add_shift (t 0) p₂
  obtain ⟨k1, hk1⟩ := torusLift_add_shift (t 1) p₂
  obtain ⟨k2, hk2⟩ := torusLift_add_shift (t 2) p₁
  have e0 : (t + Manhattan.shiftTorusPoint p₁ p₂) 0 =
      t 0 + ((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  have e1 : (t + Manhattan.shiftTorusPoint p₁ p₂) 1 =
      t 1 + ((p₂ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  have e2 : (t + Manhattan.shiftTorusPoint p₁ p₂) 2 =
      t 2 + ((p₁ / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  rw [← e0] at hk0
  rw [← e1] at hk1
  rw [← e2] at hk2
  refine multiplier_congr_int _ _ _ _ ?_
  intro k
  fin_cases k
  · refine ⟨k2, ?_⟩
    show totalFrequency 3 P type112Pattern (t + Manhattan.shiftTorusPoint p₁ p₂) 0
      = totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t 0 +
        (k2 : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_zero, totalFrequency_type112_zero,
      show (![P 0 + p₁, P 1 + (p₂ + p₂)] : Fin 2 → ℝ) 0 = P 0 + p₁ from rfl]
    linarith
  · refine ⟨k0 + k1, ?_⟩
    show totalFrequency 3 P type112Pattern (t + Manhattan.shiftTorusPoint p₁ p₂) 1
      = totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t 1 +
        ((k0 + k1 : ℤ) : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_one, totalFrequency_type112_one,
      show (![P 0 + p₁, P 1 + (p₂ + p₂)] : Fin 2 → ℝ) 1 = P 1 + (p₂ + p₂) from rfl,
      show 2 * Real.pi * (torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 0) +
            torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 1))
          = 2 * Real.pi * torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 0) +
            2 * Real.pi * torusLift ((t + Manhattan.shiftTorusPoint p₁ p₂) 1) from by ring,
      show 2 * Real.pi * (torusLift (t 0) + torusLift (t 1))
          = 2 * Real.pi * torusLift (t 0) + 2 * Real.pi * torusLift (t 1) from by ring,
      hk0, hk1]
    push_cast
    ring

theorem multiplier_integral_type112ShiftTwist (q : Estimates.Parameters) (P : Fin 2 → ℝ)
    (p₁ p₂ : ℝ) (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    (∫ t, Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112ShiftTwist p₁ p₂ c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = ∫ t, Estimates.multiplier 40 q
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern t) *
          ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have hmom : (![(![P 0 - p₁, P 1 - (p₂ + p₂)] : Fin 2 → ℝ) 0 + p₁,
      (![P 0 - p₁, P 1 - (p₂ + p₂)] : Fin 2 → ℝ) 1 + (p₂ + p₂)] : Fin 2 → ℝ) = P := by
    funext i
    fin_cases i <;> simp
  have hsymb : ∀ t : UnitAddTorus (Fin 3),
      Estimates.multiplier 40 q
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern
            (t + Manhattan.shiftTorusPoint p₁ p₂))
        = Estimates.multiplier 40 q (totalFrequency 3 P type112Pattern t) := fun t => by
    rw [multiplier_totalFrequency_type112_add_shiftTorusPoint, hmom]
  have hshift := integral_add_right_eq_self (μ := LineTorusMeasure 3)
    (fun s : UnitAddTorus (Fin 3) =>
      Estimates.multiplier 40 q
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern s) *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2)
    (Manhattan.shiftTorusPoint p₁ p₂)
  rw [type112FreqFun_type112ShiftTwist, ← hshift]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_torusShift (Manhattan.shiftTorusPoint p₁ p₂)
    (type112FreqFun c)] with t ht
  rw [ht, hsymb t]

theorem multiplier_integral_type112ShiftTwist_frozen (q : Estimates.Parameters)
    (p : Fin 2 → ℝ) (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    (∫ t, Estimates.multiplier 40 q (totalFrequency 3 p type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1) c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = ∫ t, Estimates.multiplier 40 q
          (totalFrequency 3 ![0, -(p 1)] type112Pattern t) *
          ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have hmom : (![p 0 - p 0, p 1 - (p 1 + p 1)] : Fin 2 → ℝ) = ![0, -(p 1)] := by
    funext i
    fin_cases i <;> simp
  rw [multiplier_integral_type112ShiftTwist, hmom]

/-! ### From the general multiplier energy to the raw multiplier energy -/

theorem tsum_multiplier_type112Extend (q : Estimates.Parameters) (p : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    (∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier 40 q (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 (type112Extend c)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3))
      = ∫ t, Estimates.multiplier 40 q (totalFrequency 3 p type112Pattern t) *
          ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  rw [lineIndexFourier_type112Extend]
  exact tsum_single_integral
    (fun σ t => Estimates.multiplier 40 q (totalFrequency 3 p σ t)) (type112FreqFun c)

theorem multiplier_integral_rawCorrectionL2 {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    (∫ t, Estimates.multiplier 40 q (rawCorrectionTotalFrequency p₂ t) *
        ‖(Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = rawCubicMultiplierEnergy q a p₂ := by
  unfold rawCubicMultiplierEnergy
  refine integral_congr_ae ?_
  filter_upwards [(Manhattan.rawCorrectionFunction_memLp (kappa := 40)
    (by norm_num) hlambda a p₂).coeFn_toLp] with t ht
  have h2 : (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
      UnitAddTorus (Fin 3) → ℂ) t = Manhattan.rawCorrectionFunction 40 q a p₂ t := ht
  rw [h2]

/-- **The multiplier energy of the competitor's degree-three coefficient.** -/
theorem multiplier_integral_shiftedCorrection_le {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) :
    (∫ t, Estimates.multiplier 40 q (totalFrequency 3 p type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
            (Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
              hlambda |p 0| (p 1))) : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3))
      ≤ rawCubicMultiplierEnergy q |p 0| (p 1) := by
  set d := Manhattan.rawCorrectionFourierCoefficients (kappa := 40) (by norm_num)
    hlambda |p 0| (p 1) with hd
  have hproj : Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
      hlambda |p 0| (p 1) = Manhattan.type112DiagonalProjection d := rfl
  have hsymm : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d
      = Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda |p 0| (p 1) := by
    rw [hd, Manhattan.rawCorrectionFourierCoefficients,
      LinearIsometryEquiv.symm_apply_apply]
  rw [multiplier_integral_type112ShiftTwist_frozen, hproj]
  refine le_trans (multiplier_integral_type112DiagonalProjection_le hlambda.le _ d) ?_
  rw [hsymm, ← multiplier_integral_rawCorrectionL2 hlambda |p 0| (p 1)]
  refine le_of_eq (integral_congr_ae ?_)
  filter_upwards with t
  rw [multiplier_totalFrequency_type112Pattern]

/-! ### Summand 4 of (22) -/

/-- **The second half of Lemma 5.2 for the concrete competitor.** -/
theorem sectorDFourForm_shiftedCorrectionWalsh_le {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) :
    sectorDFourForm hlambda p
        (Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
          |p 0| (p 0) (p 1))
      ≤ 8 * rawCubicMultiplierEnergy q |p 0| (p 1) := by
  set c := Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
    hlambda |p 0| (p 1) with hc
  set ct := Manhattan.type112ShiftTwist (p 0) (p 1) c with hct
  set g : DegreeCoefficient 3 := type112Extend ct with hg
  have hk : Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num) hlambda
      |p 0| (p 0) (p 1) = homogeneousWalshSynthesis 3 g := by
    show Manhattan.type112WalshSynthesis ct = homogeneousWalshSynthesis 3 (type112Extend ct)
    exact type112WalshSynthesis_eq_homogeneous ct
  rw [hk]
  have hmem : homogeneousWalshSynthesis 3 g ∈ Manhattan.walshDegree 3 :=
    homogeneousWalshSynthesis_mem_degree 3 g
  have hsplit := sectorDFourForm_le_dir_integrals hlambda p hmem
    (fun i => degreeRaiseDir p i g)
    (fun i => homogeneousWalshSynthesis_degreeRaiseDir p i g)
  simp only at hsplit
  have hM : (∑' σ : Fin 3 → Axis, ∫ t,
      Estimates.multiplier 40 q (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3))
      ≤ rawCubicMultiplierEnergy q |p 0| (p 1) := by
    rw [hg, tsum_multiplier_type112Extend, hct, hc]
    exact multiplier_integral_shiftedCorrection_le hlambda p
  have h0 := tsum_integral_inv_symbolWeight_degreeRaiseDir_le hlambda p 0 g
  have h1 := tsum_integral_inv_symbolWeight_degreeRaiseDir_le hlambda p 1 g
  linarith

/-- **Summand 4 is discharged.** -/
theorem summandFourBound_proved : ∃ C : ℝ, 0 ≤ C ∧ SummandFourBound C := by
  obtain ⟨C, hC, hfive⟩ := exists_propositionFiveTwo_corrected
  refine ⟨16 * C, by linarith, summandFourBound_of_sectorDFour ?_⟩
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog
  have hK : (1 : ℝ) ≤ (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
      Estimates.Parameters).K := by
    simp [correctedCompetitorK]
  have hrho : (0 : ℝ) ≤ (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
      Estimates.Parameters).rho := by
    simp only [correctedCompetitorRho]
    positivity
  have hrhopi : 3 * (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
      Estimates.Parameters).rho < Real.pi := by
    simp only [correctedCompetitorRho]
    nlinarith [Real.pi_pos]
  have hmain := sectorDFourForm_shiftedCorrectionWalsh_le
    (q := (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ : Estimates.Parameters))
    hlambda p
  have hraw := rawCubicMultiplierEnergy_le_sqrtScale
    (q := (⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ : Estimates.Parameters))
    hlambda hK hrho hrhopi (abs_nonneg (p 0)) horder
    (hfive hlambda hlambdaOne |p 0| (abs_nonneg _) hlog)
  linarith

/-- **The grouped cubic pair, unconditionally.** This is the statement the
discharge chain of `Manhattan/Glue/FinalDischarge.lean` needs: it replaces
`summandTwoFourBound_of_cubicSectors`, whose degree-four hypothesis
`ConcreteDThreeRaisingBound` is no longer required. -/
theorem exists_summandTwoFourBound : ∃ C : ℝ, 0 ≤ C ∧ SummandTwoFourBound C := by
  obtain ⟨C₂, hC₂, h2⟩ := summandTwoBound_proved
  obtain ⟨C₄, hC₄, h4⟩ := summandFourBound_proved
  exact ⟨C₂ + C₄, by linarith, summandTwoFourBound_of_summands h2 h4⟩

end Manhattan.Glue

end
