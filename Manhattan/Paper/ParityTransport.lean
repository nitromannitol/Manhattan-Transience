import Manhattan.Paper.ParityMajorant
import Manhattan.V4.SharpConstant

/-!
# From the Walsh vector of a raw kernel to `∫ M |K|²`

Step 1 of `lem:parity` (`paper/arxiv/main.tex:801-854`) ends with
`‖Π₃K‖₊² + ‖D₃Π₃K‖₋² ≤ ∫ M |K|²`, `M = 4(δ + |r| + |r'| + |β|)`.  The bracket
bound of `Manhattan/Paper/ParityMajorant.lean` is stated for the Walsh vector
of a type-`112` coefficient.  This file carries it to the raw kernel `k` of
`Manhattan.V4.rawWalsh`, in four steps:

* the phase of `eq:shift` moves the momentum to the frozen value `(0, -p₂)`
  (`parityWeight_integral_type112ShiftTwist`);
* removing the coefficients with coincident row indices, and choosing the
  ordered representative of each row pair, keeps exactly half of the energy of
  a kernel symmetric in its two row frequencies
  (`parityWeight_integral_type112DiagonalProjection_le_half`): the projections
  onto `m₀ < m₁` and `m₁ < m₀` commute with the weight, which depends on the two
  row frequencies only through their sum and symmetrically, and the swap of the
  two rows exchanges them;
* the energy of the `L²` vector of `k` is the iterated torus integral
  (`parityWeight_integral_rawL2`);
* the weight is at most `M` (`parityWeight_le_evenMajorant`), using
  `λ + 4|p₂| ≤ 4δ`, which holds for `δ = √λ + a`, `λ ≤ 1`, `|p₂| ≤ a`.

The factor `1/2` is the normalization of the raw kernel: the paper's `K` is
`k/√2` (`Manhattan/V4/MixedBridge.lean`).  The result is
`sectorForms_rawWalsh_le`, the paper's `eq:majorant` with constant one.
-/

open scoped lp
open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

/-- The unit circle carries its normalized Haar measure throughout this file. -/
local instance instMeasureSpaceUnitAddCircleParityTransport : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-! ### The weight -/

/-- The weight `λ + θ(P) + 3(2|sin(P₁/2)| + 2|sin(P₂/2)|)`. -/
def parityWeight (lam : ℝ) (P : Fin 2 → ℝ) : ℝ := lam + Estimates.theta P + 3 * halfSine P

theorem abs_sin_half_add_int_mul_two_pi (y : ℝ) (j : ℤ) :
    |Real.sin ((y + j * (2 * Real.pi)) / 2)| = |Real.sin (y / 2)| := by
  have h : (y + j * (2 * Real.pi)) / 2 = y / 2 + (j : ℝ) * Real.pi := by ring
  have habs : |((-1 : ℝ) ^ j)| = 1 := by
    rw [abs_zpow]
    norm_num
  rw [h, Real.sin_add_int_mul_pi, abs_mul, habs, one_mul]

/-- The weight only sees the total frequency modulo `2π`. -/
theorem parityWeight_congr_int (lam : ℝ) (P Q : Fin 2 → ℝ)
    (h : ∀ k : Fin 2, ∃ j : ℤ, P k = Q k + j * (2 * Real.pi)) :
    parityWeight lam P = parityWeight lam Q := by
  obtain ⟨j0, h0⟩ := h 0
  obtain ⟨j1, h1⟩ := h 1
  rw [parityWeight, parityWeight, Estimates.theta, Estimates.theta, halfSine, halfSine, h0, h1,
    dispersion_add_int_two_pi, dispersion_add_int_two_pi, abs_sin_half_add_int_mul_two_pi,
    abs_sin_half_add_int_mul_two_pi]

theorem parityWeight_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (P : Fin 2 → ℝ) :
    0 ≤ parityWeight lam P := by
  have := Estimates.theta_nonneg P
  have := halfSine_nonneg P
  unfold parityWeight
  linarith

theorem parityWeight_le (lam : ℝ) (P : Fin 2 → ℝ) : parityWeight lam P ≤ lam + 16 := by
  have h0 := Real.neg_one_le_cos (P 0)
  have h1 := Real.neg_one_le_cos (P 1)
  have s0 := Real.abs_sin_le_one (P 0 / 2)
  have s1 := Real.abs_sin_le_one (P 1 / 2)
  unfold parityWeight halfSine Estimates.theta Estimates.dispersion
  linarith

theorem continuous_parityWeight_totalFrequency (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ)
    (σ : Fin n → Axis) :
    Continuous fun t => parityWeight lam (totalFrequency n p σ t) := by
  unfold parityWeight Estimates.theta
  exact ((continuous_const.add ((continuous_dispersion_totalFrequency n p σ 0).add
    (continuous_dispersion_totalFrequency n p σ 1))).add
      (continuous_const.mul (continuous_halfSine_totalFrequency n p σ)))

theorem symbolWeight_add_halfSine (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    symbolWeight n lam p σ t + 3 * halfSine (totalFrequency n p σ t) =
      parityWeight lam (totalFrequency n p σ t) := by
  rw [symbolWeight_def, parityWeight]

/-! ### Three congruences of total frequencies -/

theorem totalFrequency_type112_add_shiftTorusPoint_congr (P : Fin 2 → ℝ) (p₁ p₂ : ℝ)
    (t : UnitAddTorus (Fin 3)) :
    ∀ k : Fin 2, ∃ j : ℤ,
      totalFrequency 3 P type112Pattern (t + Manhattan.shiftTorusPoint p₁ p₂) k =
        totalFrequency 3 ![P 0 + p₁, P 1 + (p₂ + p₂)] type112Pattern t k +
          j * (2 * Real.pi) := by
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

theorem totalFrequency_type112_frozen_congr (p₂ : ℝ) (t : UnitAddTorus (Fin 3)) :
    ∀ k : Fin 2, ∃ j : ℤ, totalFrequency 3 ![0, -p₂] type112Pattern t k =
      rawCorrectionTotalFrequency p₂ t k + j * (2 * Real.pi) := by
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

theorem totalFrequency_type112_antiShift_congr (P : Fin 2 → ℝ) (c : UnitAddCircle)
    (t : UnitAddTorus (Fin 3)) :
    ∀ k : Fin 2, ∃ j : ℤ, totalFrequency 3 P type112Pattern (t + antiShift c) k =
      totalFrequency 3 P type112Pattern t k + j * (2 * Real.pi) := by
  intro k
  fin_cases k
  · refine ⟨0, ?_⟩
    show totalFrequency 3 P type112Pattern (t + antiShift c) 0
      = totalFrequency 3 P type112Pattern t 0 + ((0 : ℤ) : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_zero, totalFrequency_type112_zero,
      show (t + antiShift c) 2 = t 2 by
        show t 2 + antiShift c 2 = t 2
        rw [show antiShift c 2 = (0 : UnitAddCircle) from rfl, add_zero]]
    push_cast
    ring
  · obtain ⟨j, hj⟩ := torusLift_add_antiShift (t 0) (t 1) c
    refine ⟨j, ?_⟩
    show totalFrequency 3 P type112Pattern (t + antiShift c) 1
      = totalFrequency 3 P type112Pattern t 1 + (j : ℝ) * (2 * Real.pi)
    rw [totalFrequency_type112_one, totalFrequency_type112_one,
      show (t + antiShift c) 0 = t 0 + c from rfl,
      show (t + antiShift c) 1 = t 1 + (-c) from rfl, hj]
    ring

/-! ### The weight as a multiplier on the raw coefficients -/

/-- The weight at the momentum `P`, as a function on the raw type-`112` torus. -/
def parityWeightMap (lam : ℝ) (P : Fin 2 → ℝ) : C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨fun t => ((parityWeight lam (totalFrequency 3 P type112Pattern t) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      (continuous_parityWeight_totalFrequency 3 lam P type112Pattern)⟩

@[simp] theorem parityWeightMap_apply (lam : ℝ) (P : Fin 2 → ℝ) (t : UnitAddTorus (Fin 3)) :
    parityWeightMap lam P t =
      ((parityWeight lam (totalFrequency 3 P type112Pattern t) : ℝ) : ℂ) := rfl

theorem parityWeightMap_antiShift (lam : ℝ) (P : Fin 2 → ℝ) (c : UnitAddCircle)
    (t : UnitAddTorus (Fin 3)) :
    parityWeightMap lam P (t + antiShift c) = parityWeightMap lam P t := by
  rw [parityWeightMap_apply, parityWeightMap_apply,
    parityWeight_congr_int lam _ _ (totalFrequency_type112_antiShift_congr P c t)]

/-- The weight is symmetric in the two row frequencies. -/
theorem totalFrequency_type112_swap (P : Fin 2 → ℝ) (t : UnitAddTorus (Fin 3)) :
    totalFrequency 3 P type112Pattern (t ∘ Equiv.swap 0 1) =
      totalFrequency 3 P type112Pattern t := by
  have e0 : (t ∘ Equiv.swap (0 : Fin 3) 1) 0 = t 1 := by
    simp [Equiv.swap_apply_left]
  have e1 : (t ∘ Equiv.swap (0 : Fin 3) 1) 1 = t 0 := by
    simp [Equiv.swap_apply_right]
  have e2 : (t ∘ Equiv.swap (0 : Fin 3) 1) 2 = t 2 := by
    show t (Equiv.swap (0 : Fin 3) 1 2) = t 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
  funext k
  fin_cases k
  · show totalFrequency 3 P type112Pattern (t ∘ Equiv.swap 0 1) 0 =
      totalFrequency 3 P type112Pattern t 0
    rw [totalFrequency_type112_zero, totalFrequency_type112_zero, e2]
  · show totalFrequency 3 P type112Pattern (t ∘ Equiv.swap 0 1) 1 =
      totalFrequency 3 P type112Pattern t 1
    rw [totalFrequency_type112_one, totalFrequency_type112_one, e0, e1]
    ring

/-- Multiplication by the weight, read on the raw type-`112` Fourier coefficients. -/
def parityWeightOp (lam : ℝ) (P : Fin 2 → ℝ) :
    ℓ²(Manhattan.RawType112Index, ℂ) →L[ℂ] ℓ²(Manhattan.RawType112Index, ℂ) :=
  (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.toLinearIsometry.toContinuousLinearMap ∘L
    (contMulL 3 (parityWeightMap lam P) ∘L
      (UnitAddTorus.mFourierBasis
        (d := Fin 3)).repr.symm.toLinearIsometry.toContinuousLinearMap)

theorem parityWeightOp_apply (lam : ℝ) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    parityWeightOp lam P c =
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr
        (contMul 3 (parityWeightMap lam P)
          ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c)) := rfl

theorem re_inner_parityWeightOp_eq_integral (lam : ℝ) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    RCLike.re (inner ℂ (parityWeightOp lam P c) c) =
      ∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  set F := (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm c with hF
  have hc : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr F = c := by
    rw [hF, LinearIsometryEquiv.apply_symm_apply]
  have hinner : inner ℂ (parityWeightOp lam P c) c =
      inner ℂ (contMul 3 (parityWeightMap lam P) F) F := by
    rw [parityWeightOp_apply, ← hF, ← hc,
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.inner_map_map]
  rw [hinner]
  refine inner_lp_eq_weighted_integral _ _ _ ?_
  filter_upwards [coeFn_contMul (parityWeightMap lam P) F] with t ht
  rw [ht, parityWeightMap_apply]

theorem re_inner_parityWeightOp_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (P : Fin 2 → ℝ)
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    0 ≤ RCLike.re (inner ℂ (parityWeightOp lam P c) c) := by
  rw [re_inner_parityWeightOp_eq_integral]
  exact integral_nonneg fun t => mul_nonneg (parityWeight_nonneg hlam _) (sq_nonneg _)

/-- The weight depends on the two row frequencies only through their sum, so its
Fourier coefficients vanish off the vectors with equal row entries. -/
theorem inner_mFourierLp_contMul_parityWeightMap_eq_zero (lam : ℝ) (P : Fin 2 → ℝ)
    {m n : Manhattan.RawType112Index} (h : m 0 - n 0 ≠ m 1 - n 1) :
    inner ℂ (mFourierLp 2 n) (contMul 3 (parityWeightMap lam P) (mFourierLp 2 m)) = 0 := by
  classical
  set W := parityWeightMap lam P with hW
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
      rw [hW, hθ, parityWeightMap_antiShift]
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

theorem parityWeightOp_single (lam : ℝ) (P : Fin 2 → ℝ) (m n : Manhattan.RawType112Index) :
    (parityWeightOp lam P (lp.single 2 m (1 : ℂ))) n =
      inner ℂ (mFourierLp 2 n) (contMul 3 (parityWeightMap lam P) (mFourierLp 2 m)) := by
  have hsym : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (lp.single 2 m (1 : ℂ))
      = mFourierLp 2 m := by
    rw [HilbertBasis.repr_symm_single, UnitAddTorus.coe_mFourierBasis]
  rw [parityWeightOp_apply, hsym,
    (UnitAddTorus.mFourierBasis (d := Fin 3)).repr_apply_apply,
    UnitAddTorus.coe_mFourierBasis]

theorem l2SupportProjection_single_of_mem {S : Set Manhattan.RawType112Index}
    {m : Manhattan.RawType112Index} (hm : m ∈ S) :
    l2SupportProjection S (lp.single 2 m (1 : ℂ) : ℓ²(Manhattan.RawType112Index, ℂ))
      = lp.single 2 m (1 : ℂ) := by
  classical
  apply lp.ext
  funext n
  rw [l2SupportProjection_apply]
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn]
  · rw [Set.indicator_of_notMem hn, lp.single_apply, Pi.single_apply, if_neg]
    rintro rfl
    exact hn hm

theorem l2SupportProjection_single_of_notMem {S : Set Manhattan.RawType112Index}
    {m : Manhattan.RawType112Index} (hm : m ∉ S) :
    l2SupportProjection S (lp.single 2 m (1 : ℂ) : ℓ²(Manhattan.RawType112Index, ℂ)) = 0 := by
  classical
  apply lp.ext
  funext n
  rw [l2SupportProjection_apply]
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn, lp.single_apply, Pi.single_apply, if_neg]
    · rfl
    · rintro rfl
      exact hm hn
  · rw [Set.indicator_of_notMem hn]
    rfl

/-- **The weight commutes with every support projection that sees the two row
indices only through their difference.** -/
theorem l2SupportProjection_comm_parityWeightOp (lam : ℝ) (P : Fin 2 → ℝ)
    (S : Set Manhattan.RawType112Index)
    (hS : ∀ m n : Manhattan.RawType112Index, m 0 - n 0 = m 1 - n 1 → (n ∈ S ↔ m ∈ S))
    (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    l2SupportProjection S (parityWeightOp lam P c) =
      parityWeightOp lam P (l2SupportProjection S c) := by
  classical
  refine l2_ext' (l2SupportProjection S ∘L parityWeightOp lam P)
    (parityWeightOp lam P ∘L l2SupportProjection S) ?_ c
  intro m
  show l2SupportProjection S (parityWeightOp lam P (lp.single 2 m (1 : ℂ)))
    = parityWeightOp lam P (l2SupportProjection S (lp.single 2 m (1 : ℂ)))
  have hzero : ∀ n : Manhattan.RawType112Index, ¬ ((n ∈ S) ↔ (m ∈ S)) →
      (parityWeightOp lam P (lp.single 2 m (1 : ℂ))) n = 0 := by
    intro n hn
    refine (parityWeightOp_single lam P m n).trans ?_
    exact inner_mFourierLp_contMul_parityWeightMap_eq_zero lam P fun hdiff => hn (hS m n hdiff)
  apply lp.ext
  funext n
  by_cases hm : m ∈ S
  · rw [l2SupportProjection_single_of_mem hm, l2SupportProjection_apply]
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      exact (hzero n (by tauto)).symm
  · rw [l2SupportProjection_single_of_notMem hm, map_zero, l2SupportProjection_apply]
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
      exact hzero n (by tauto)
    · rw [Set.indicator_of_notMem hn]
      rfl

/-! ### The swap of the two row indices -/

/-- Exchange of the two row indices of a raw type-`112` index. -/
def rawSwap : Manhattan.RawType112Index ≃ Manhattan.RawType112Index :=
  Equiv.arrowCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl ℤ)

theorem rawSwap_apply (m : Manhattan.RawType112Index) : rawSwap m = m ∘ Equiv.swap 0 1 := by
  funext a
  simp [rawSwap, Equiv.arrowCongr_apply]

theorem l2CongrLeft_rawSwap_single (m : Manhattan.RawType112Index) :
    l2CongrLeft rawSwap (lp.single 2 m (1 : ℂ) : ℓ²(Manhattan.RawType112Index, ℂ)) =
      lp.single 2 (rawSwap m) (1 : ℂ) := by
  classical
  apply lp.ext
  funext j
  rw [l2CongrLeft_apply, lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [← h, Equiv.apply_symm_apply], fun h => by
    rw [h, Equiv.symm_apply_apply]⟩

/-- The row indices `m₁ < m₀` are the swaps of the row indices `m₀ < m₁`, and on the
Fourier side the swap is the exchange of the two row frequencies. -/
theorem repr_symm_reversed_eq (c : ℓ²(Manhattan.RawType112Index, ℂ)) :
    (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
        (l2SupportProjection {m : Manhattan.RawType112Index | m 1 < m 0} c) =
      torusPerm 3 (Equiv.swap 0 1) ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
        (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1}
          (l2CongrLeft rawSwap c))) := by
  classical
  refine l2_ext'
    ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm.toLinearIsometry.toContinuousLinearMap
      ∘L l2SupportProjection {m : Manhattan.RawType112Index | m 1 < m 0})
    ((torusPerm 3 (Equiv.swap 0 1)).toContinuousLinearMap ∘L
      ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm.toLinearIsometry.toContinuousLinearMap
        ∘L (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1} ∘L
          (l2CongrLeft rawSwap).toLinearIsometry.toContinuousLinearMap))) ?_ c
  intro m
  show (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
      (l2SupportProjection {m : Manhattan.RawType112Index | m 1 < m 0} (lp.single 2 m (1 : ℂ))) =
    torusPerm 3 (Equiv.swap 0 1) ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
      (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1}
        (l2CongrLeft rawSwap (lp.single 2 m (1 : ℂ)))))
  have hsw : rawSwap m 0 < rawSwap m 1 ↔ m 1 < m 0 := by
    rw [rawSwap_apply]
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [l2CongrLeft_rawSwap_single]
  by_cases hm : m 1 < m 0
  · rw [l2SupportProjection_single_of_mem (S := {m : Manhattan.RawType112Index | m 1 < m 0}) hm,
      l2SupportProjection_single_of_mem (S := {m : Manhattan.RawType112Index | m 0 < m 1})
        (show rawSwap m ∈ {m : Manhattan.RawType112Index | m 0 < m 1} from hsw.mpr hm),
      HilbertBasis.repr_symm_single, HilbertBasis.repr_symm_single,
      UnitAddTorus.coe_mFourierBasis, torusPerm_mFourierLp, rawSwap_apply, Equiv.symm_swap]
    congr 1
    funext a
    simp
  · rw [l2SupportProjection_single_of_notMem (S := {m : Manhattan.RawType112Index | m 1 < m 0})
      hm, l2SupportProjection_single_of_notMem (S := {m : Manhattan.RawType112Index | m 0 < m 1})
        (show rawSwap m ∉ {m : Manhattan.RawType112Index | m 0 < m 1} from fun h =>
          hm (hsw.mp h))]
    simp

/-- The weighted energy is invariant under the exchange of the two row frequencies. -/
theorem integral_parityWeight_torusPerm_swap (lam : ℝ) (P : Fin 2 → ℝ)
    (F : Lp ℂ 2 (LineTorusMeasure 3)) :
    ∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(torusPerm 3 (Equiv.swap 0 1) F : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) =
      ∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(F : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have h1 : (∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(torusPerm 3 (Equiv.swap 0 1) F : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3)) =
      ∫ t, (fun s => parityWeight lam (totalFrequency 3 P type112Pattern s) *
        ‖(F : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2) (torusPermMap 3 (Equiv.swap 0 1) t)
        ∂(LineTorusMeasure 3) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_torusPerm 3 (Equiv.swap 0 1) F] with t ht
    rw [ht]
    simp only [torusPermMap_apply, totalFrequency_type112_swap]
  rw [h1]
  exact (measurePreserving_torusPermMap 3 (Equiv.swap 0 1)).integral_comp'
    (fun s => parityWeight lam (totalFrequency 3 P type112Pattern s) *
      ‖(F : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2)

/-- **Half of the energy of a symmetric coefficient lies on the ordered row pairs.**
For a raw coefficient symmetric under the exchange of the two row indices, the
weighted energy of its restriction to `m₀ < m₁` is at most half its weighted energy. -/
theorem two_mul_re_inner_parityWeightOp_ordered_le {lam : ℝ} (hlam : 0 ≤ lam)
    (P : Fin 2 → ℝ) (d : ℓ²(Manhattan.RawType112Index, ℂ))
    (hd : l2CongrLeft rawSwap d = d) :
    2 * RCLike.re (inner ℂ
        (parityWeightOp lam P (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1} d))
        (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1} d)) ≤
      RCLike.re (inner ℂ (parityWeightOp lam P d) d) := by
  classical
  set T := parityWeightOp lam P with hT
  set Sp : Set Manhattan.RawType112Index := {m | m 0 < m 1} with hSpdef
  set Sn : Set Manhattan.RawType112Index := {m | m 1 < m 0} with hSndef
  set Sr : Set Manhattan.RawType112Index := {m | m 0 ≠ m 1} with hSrdef
  have hSp : ∀ m n : Manhattan.RawType112Index, m 0 - n 0 = m 1 - n 1 → (n ∈ Sp ↔ m ∈ Sp) := by
    intro m n h
    simp only [hSpdef, Set.mem_setOf_eq]
    omega
  have hSn : ∀ m n : Manhattan.RawType112Index, m 0 - n 0 = m 1 - n 1 → (n ∈ Sn ↔ m ∈ Sn) := by
    intro m n h
    simp only [hSndef, Set.mem_setOf_eq]
    omega
  have hSr : ∀ m n : Manhattan.RawType112Index, m 0 - n 0 = m 1 - n 1 → (n ∈ Sr ↔ m ∈ Sr) := by
    intro m n h
    simp only [hSrdef, Set.mem_setOf_eq]
    omega
  have hpos := re_inner_parityWeightOp_nonneg hlam P
  have h1 : RCLike.re (inner ℂ (T (l2SupportProjection Sr d)) (l2SupportProjection Sr d)) ≤
      RCLike.re (inner ℂ (T d) d) :=
    re_inner_le_of_commuting_projection T (l2SupportProjection Sr)
      (l2SupportProjection_idem Sr) (l2SupportProjection_sym Sr)
      (l2SupportProjection_comm_parityWeightOp lam P Sr hSr) hpos d
  have hsplit : l2SupportProjection Sr d = l2SupportProjection Sp d + l2SupportProjection Sn d := by
    apply lp.ext
    funext m
    rw [lp.coeFn_add, Pi.add_apply, l2SupportProjection_apply, l2SupportProjection_apply,
      l2SupportProjection_apply]
    rcases lt_trichotomy (m 0) (m 1) with h | h | h
    · rw [Set.indicator_of_mem (show m ∈ Sr from ne_of_lt h),
        Set.indicator_of_mem (show m ∈ Sp from h),
        Set.indicator_of_notMem (show m ∉ Sn from fun h' => absurd h' (not_lt.mpr h.le)), add_zero]
    · rw [Set.indicator_of_notMem (show m ∉ Sr from fun h' => h' h),
        Set.indicator_of_notMem (show m ∉ Sp from fun h' => by
          simp only [hSpdef, Set.mem_setOf_eq] at h'
          omega),
        Set.indicator_of_notMem (show m ∉ Sn from fun h' => by
          simp only [hSndef, Set.mem_setOf_eq] at h'
          omega), add_zero]
    · rw [Set.indicator_of_mem (show m ∈ Sr from ne_of_gt h),
        Set.indicator_of_notMem (show m ∉ Sp from fun h' => absurd h' (not_lt.mpr h.le)),
        Set.indicator_of_mem (show m ∈ Sn from h), zero_add]
  have hPQ : ∀ x : ℓ²(Manhattan.RawType112Index, ℂ),
      l2SupportProjection Sp (l2SupportProjection Sn x) = 0 := by
    intro x
    apply lp.ext
    funext m
    rw [l2SupportProjection_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hm : m ∈ Sp
    · rw [Set.indicator_of_mem hm, l2SupportProjection_apply,
        Set.indicator_of_notMem (show m ∉ Sn from fun h' => absurd (show m 0 < m 1 from hm)
          (not_lt.mpr (show m 1 < m 0 from h').le))]
    · rw [Set.indicator_of_notMem hm]
  have hQP : ∀ x : ℓ²(Manhattan.RawType112Index, ℂ),
      l2SupportProjection Sn (l2SupportProjection Sp x) = 0 := by
    intro x
    apply lp.ext
    funext m
    rw [l2SupportProjection_apply, lp.coeFn_zero, Pi.zero_apply]
    by_cases hm : m ∈ Sn
    · rw [Set.indicator_of_mem hm, l2SupportProjection_apply,
        Set.indicator_of_notMem (show m ∉ Sp from fun h' => absurd (show m 1 < m 0 from hm)
          (not_lt.mpr (show m 0 < m 1 from h').le))]
    · rw [Set.indicator_of_notMem hm]
  have hcross1 : inner ℂ (T (l2SupportProjection Sp d)) (l2SupportProjection Sn d) = 0 := by
    rw [← l2SupportProjection_comm_parityWeightOp lam P Sp hSp d, l2SupportProjection_sym, hPQ,
      inner_zero_right]
  have hcross2 : inner ℂ (T (l2SupportProjection Sn d)) (l2SupportProjection Sp d) = 0 := by
    rw [← l2SupportProjection_comm_parityWeightOp lam P Sn hSn d, l2SupportProjection_sym, hQP,
      inner_zero_right]
  have heq : RCLike.re (inner ℂ (T (l2SupportProjection Sn d)) (l2SupportProjection Sn d)) =
      RCLike.re (inner ℂ (T (l2SupportProjection Sp d)) (l2SupportProjection Sp d)) := by
    rw [hT, re_inner_parityWeightOp_eq_integral, re_inner_parityWeightOp_eq_integral,
      hSndef, repr_symm_reversed_eq, hd, integral_parityWeight_torusPerm_swap]
  rw [hsplit, map_add, inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2,
    zero_add, add_zero, map_add, heq] at h1
  linarith

/-! ### The four transfers -/

/-- **The phase of `eq:shift` moves the momentum.** -/
theorem parityWeight_integral_type112ShiftTwist (lam : ℝ) (P : Fin 2 → ℝ) (p₁ p₂ : ℝ)
    (c : ℓ²(Manhattan.Type112Index, ℂ)) :
    (∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112ShiftTwist p₁ p₂ c) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = ∫ t, parityWeight lam
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern t) *
          ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have hmom : (![(![P 0 - p₁, P 1 - (p₂ + p₂)] : Fin 2 → ℝ) 0 + p₁,
      (![P 0 - p₁, P 1 - (p₂ + p₂)] : Fin 2 → ℝ) 1 + (p₂ + p₂)] : Fin 2 → ℝ) = P := by
    funext i
    fin_cases i <;> simp
  have hsymb : ∀ t : UnitAddTorus (Fin 3),
      parityWeight lam
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern
            (t + Manhattan.shiftTorusPoint p₁ p₂))
        = parityWeight lam (totalFrequency 3 P type112Pattern t) := fun t => by
    rw [parityWeight_congr_int lam _ _
      (totalFrequency_type112_add_shiftTorusPoint_congr _ p₁ p₂ t), hmom]
  have hshift := integral_add_right_eq_self (μ := LineTorusMeasure 3)
    (fun s : UnitAddTorus (Fin 3) =>
      parityWeight lam
          (totalFrequency 3 ![P 0 - p₁, P 1 - (p₂ + p₂)] type112Pattern s) *
        ‖(type112FreqFun c : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2)
    (Manhattan.shiftTorusPoint p₁ p₂)
  rw [type112FreqFun_type112ShiftTwist, ← hshift]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_torusShift (Manhattan.shiftTorusPoint p₁ p₂)
    (type112FreqFun c)] with t ht
  rw [ht, hsymb t]

/-- **The projection onto distinct and ordered row indices keeps half of the
energy of a symmetric raw coefficient.** -/
theorem parityWeight_integral_type112DiagonalProjection_le_half {lam : ℝ} (hlam : 0 ≤ lam)
    (P : Fin 2 → ℝ) (d : ℓ²(Manhattan.RawType112Index, ℂ)) (hd : l2CongrLeft rawSwap d = d) :
    (∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112DiagonalProjection d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      ≤ 1 / 2 * ∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have h := two_mul_re_inner_parityWeightOp_ordered_le hlam P d hd
  rw [re_inner_parityWeightOp_eq_integral, re_inner_parityWeightOp_eq_integral] at h
  rw [type112FreqFun_eq_repr_symm, rawExtend_type112DiagonalProjection]
  change (∫ t, parityWeight lam (totalFrequency 3 P type112Pattern t) *
      ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
        (l2SupportProjection {m : Manhattan.RawType112Index | m 0 < m 1} d)) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3)) ≤ _
  linarith

/-- The weighted energy of the raw kernel, in the `(β, r, r')` order of
`Manhattan.V4.evenMajorantEnergy`. -/
def parityWeightEnergy (lam p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta =>
    Estimates.torusIntegral fun r =>
      Estimates.torusIntegral fun r' =>
        parityWeight lam (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
          ‖k r r' beta‖ ^ 2

theorem parityWeight_mixedTotalFrequency (lam beta alpha : ℝ) :
    parityWeight lam (Estimates.mixedTotalFrequency beta alpha) =
      lam + ((1 - Real.cos beta) + (1 - Real.cos alpha)) +
        3 * (2 * |Real.sin (beta / 2)| + 2 * |Real.sin (alpha / 2)|) := by
  simp [parityWeight, Estimates.theta, halfSine, Estimates.mixedTotalFrequency,
    Estimates.dispersion]

/-- **The energy of the `L²` vector of the raw kernel** is the iterated torus
integral. -/
theorem parityWeight_integral_rawL2 {lam : ℝ} (hlam : 0 ≤ lam) (p₂ : ℝ)
    {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k) :
    (∫ t, parityWeight lam (rawCorrectionTotalFrequency p₂ t) *
        ‖(V4.rawL2 hk : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = parityWeightEnergy lam p₂ k := by
  have hmeas := hk.1
  obtain ⟨C, hC⟩ := hk.2
  set F : ℝ → ℝ → ℝ → ℝ := fun r r' beta =>
    parityWeight lam (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
      ‖k r r' beta‖ ^ 2 with hF
  have hFmeas : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2 := by
    refine Measurable.mul ?_ (hmeas.norm.pow_const 2)
    have h : (fun z : ℝ × ℝ × ℝ =>
        parityWeight lam (Estimates.mixedTotalFrequency z.2.2 (mixedAlpha p₂ z.1 z.2.1))) =
        fun z : ℝ × ℝ × ℝ => lam + ((1 - Real.cos z.2.2) + (1 - Real.cos (z.1 + z.2.1 - p₂))) +
          3 * (2 * |Real.sin (z.2.2 / 2)| + 2 * |Real.sin ((z.1 + z.2.1 - p₂) / 2)|) := by
      funext z
      rw [parityWeight_mixedTotalFrequency, mixedAlpha]
    rw [h]
    exact Continuous.measurable (by fun_prop)
  have hFb : ∀ r r' beta, |F r r' beta| ≤ (lam + 16) * C ^ 2 := by
    intro r r' beta
    have hm0 := parityWeight_nonneg hlam
      (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r'))
    have hm := parityWeight_le lam (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r'))
    have hn : ‖k r r' beta‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hC r r' beta) 2
    rw [hF]
    simp only
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _))]
    nlinarith [sq_nonneg (‖k r r' beta‖)]
  have hcongr : (∫ t, parityWeight lam (rawCorrectionTotalFrequency p₂ t) *
      ‖(V4.rawL2 hk : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = ∫ x : UnitAddTorus (Fin 3), F (Manhattan.unitTorusAngle (x 0))
          (Manhattan.unitTorusAngle (x 1)) (Manhattan.unitTorusAngle (x 2)) := by
    refine integral_congr_ae ?_
    filter_upwards [(V4.rawTorusFun_memLp hk).coeFn_toLp] with x hx
    rw [show (V4.rawL2 (k := k) hk : UnitAddTorus (Fin 3) → ℂ) x
        = V4.rawTorusFun k x from hx]
    rfl
  rw [hcongr, integral_unitTorus_three F hFmeas hFb, V4.torusIntegral₃_rotate hFmeas hFb]
  rfl

/-- **The weight is below `M = 4(δ + |r| + |r'| + |β|)`** once `λ + 4|p₂| ≤ 4δ`. -/
theorem parityWeight_le_evenMajorant {lam delta p₂ : ℝ} (hdelta : lam + 4 * |p₂| ≤ 4 * delta)
    (r r' beta : ℝ) :
    parityWeight lam (Estimates.mixedTotalFrequency beta (r + r' - p₂)) ≤
      V4.evenMajorant 4 delta r r' beta := by
  have hbeta : 2 * |Real.sin (beta / 2)| ≤ V4.torusAbs beta :=
    V4.two_abs_sin_half_le_torusAbs beta
  have halpha : 2 * |Real.sin ((r + r' - p₂) / 2)| ≤
      V4.torusAbs r + V4.torusAbs r' + |p₂| := V4.two_abs_sin_half_mixedAlpha_le r r' p₂
  have hdbeta := V4.dispersion_le_two_abs_sin_half beta
  have hdalpha := V4.dispersion_le_two_abs_sin_half (r + r' - p₂)
  simp only [parityWeight, Estimates.theta, halfSine, Estimates.mixedTotalFrequency,
    V4.evenMajorant, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

theorem parityWeightEnergy_le_evenMajorantEnergy {lam delta p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hlam0 : 0 ≤ lam) (hdelta : lam + 4 * |p₂| ≤ 4 * delta) (hk : TorusBoundedThree k) :
    parityWeightEnergy lam p₂ k ≤ V4.evenMajorantEnergy 4 delta k := by
  obtain ⟨hmeas, C, hC⟩ := hk
  have hdelta0 : 0 ≤ delta := by
    have := abs_nonneg p₂
    linarith
  set B : ℝ := ((lam + 16) + 4 * (delta + 3 * Real.pi)) * C ^ 2 with hB
  have hnormsq : ∀ r r' beta : ℝ, ‖k r r' beta‖ ^ 2 ≤ C ^ 2 := fun r r' beta =>
    pow_le_pow_left₀ (norm_nonneg _) (hC r r' beta) 2
  have hWm : Measurable fun z : ℝ × ℝ × ℝ =>
      parityWeight lam (Estimates.mixedTotalFrequency z.1 (mixedAlpha p₂ z.2.1 z.2.2)) := by
    have h : (fun z : ℝ × ℝ × ℝ =>
        parityWeight lam (Estimates.mixedTotalFrequency z.1 (mixedAlpha p₂ z.2.1 z.2.2))) =
        fun z : ℝ × ℝ × ℝ => lam + ((1 - Real.cos z.1) + (1 - Real.cos (z.2.1 + z.2.2 - p₂))) +
          3 * (2 * |Real.sin (z.1 / 2)| + 2 * |Real.sin ((z.2.1 + z.2.2 - p₂) / 2)|) := by
      funext z
      rw [parityWeight_mixedTotalFrequency, mixedAlpha]
    rw [h]
    exact Continuous.measurable (by fun_prop)
  refine V4.torusIntegral₃_mono (C := B) ?_ ?_ ?_ ?_ ?_
  · exact hWm.mul ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · exact ((V4.evenMajorant_measurable 4 delta).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).mul
      ((hmeas.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2)
  · intro beta r r'
    have hm0 := parityWeight_nonneg hlam0
      (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r'))
    have hm := parityWeight_le lam (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r'))
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    have hm0 : 0 ≤ V4.evenMajorant 4 delta r r' beta :=
      V4.evenMajorant_nonneg (by norm_num) hdelta0 r r' beta
    have hm : V4.evenMajorant 4 delta r r' beta ≤ 4 * (delta + 3 * Real.pi) :=
      V4.evenMajorant_le (by norm_num) r r' beta
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _)), hB]
    have hpi := Real.pi_pos
    have hl : 0 ≤ lam + 16 := by linarith
    nlinarith [hnormsq r r' beta, sq_nonneg (‖k r r' beta‖)]
  · intro beta r r'
    exact mul_le_mul_of_nonneg_right
      (parityWeight_le_evenMajorant hdelta r r' beta) (sq_nonneg _)

/-! ### A kernel symmetric in its two row frequencies -/

theorem rawSwap_symm_apply (m : Manhattan.RawType112Index) :
    rawSwap.symm m = m ∘ Equiv.swap 0 1 := by
  rw [Equiv.symm_apply_eq, rawSwap_apply]
  funext a
  simp

theorem torusPerm_swap_rawL2 {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (hsym : ∀ r r' beta, k r r' beta = k r' r beta) :
    torusPerm 3 (Equiv.swap 0 1) (V4.rawL2 hk) = V4.rawL2 hk := by
  apply Lp.ext
  have h2 := (measurePreserving_torusPermMap 3 (Equiv.swap 0 1)).quasiMeasurePreserving.ae_eq_comp
    (V4.rawTorusFun_memLp hk).coeFn_toLp
  filter_upwards [coeFn_torusPerm 3 (Equiv.swap 0 1) (V4.rawL2 hk), h2,
    (V4.rawTorusFun_memLp hk).coeFn_toLp] with t e1 e2 e3
  rw [e1]
  simp only [Function.comp_apply, torusPermMap_apply] at e2
  change (V4.rawL2 hk : UnitAddTorus (Fin 3) → ℂ) (t ∘ Equiv.swap 0 1) = _
  rw [show (V4.rawL2 hk : UnitAddTorus (Fin 3) → ℂ) (t ∘ Equiv.swap 0 1) =
      V4.rawTorusFun k (t ∘ Equiv.swap 0 1) from e2,
    show (V4.rawL2 hk : UnitAddTorus (Fin 3) → ℂ) t = V4.rawTorusFun k t from e3]
  simp only [V4.rawTorusFun, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), hsym]

theorem l2CongrLeft_rawSwap_repr_rawL2 {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (hsym : ∀ r r' beta, k r r' beta = k r' r beta) :
    l2CongrLeft rawSwap ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr (V4.rawL2 hk)) =
      (UnitAddTorus.mFourierBasis (d := Fin 3)).repr (V4.rawL2 hk) := by
  apply lp.ext
  funext j
  rw [l2CongrLeft_apply, rawSwap_symm_apply,
    (UnitAddTorus.mFourierBasis (d := Fin 3)).repr_apply_apply,
    (UnitAddTorus.mFourierBasis (d := Fin 3)).repr_apply_apply,
    UnitAddTorus.coe_mFourierBasis]
  have hperm : mFourierLp 2 (j ∘ Equiv.swap 0 1) =
      torusPerm 3 (Equiv.swap 0 1) (mFourierLp 2 j) := by
    rw [torusPerm_mFourierLp, Equiv.symm_swap]
  rw [hperm]
  conv_lhs => rw [← torusPerm_swap_rawL2 hk hsym]
  exact (torusPerm 3 (Equiv.swap 0 1)).inner_map_map _ _

/-! ### `eq:majorant` for the raw kernel -/

/-- **`eq:majorant` of `lem:parity`** (`paper/arxiv/main.tex:813-854`), with the
constant one of the paper.  For a bounded measurable kernel `k` symmetric in its
two row frequencies, with Walsh vector `Π₃ k` at the momentum `p`,
`‖Π₃ k‖₊² + ‖D₃ Π₃ k‖₋² ≤ ½ ∫ M |k|²`, `M = 4(δ + |r| + |r'| + |β|)`, whenever
`λ + 4|p₂| ≤ 4δ`.  The factor `½` is the normalization `K = k/√2` of the
paper's coefficient. -/
theorem sectorForms_rawWalsh_le {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta : ℝ} (hdelta : q.lambda + 4 * |p 1| ≤ 4 * delta)
    {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (hsym : ∀ r r' beta, k r r' beta = k r' r beta) :
    sectorHThreeForm q.lambda p (V4.rawWalsh p hk) + sectorDFourForm hlambda p (V4.rawWalsh p hk)
      ≤ 1 / 2 * V4.evenMajorantEnergy 4 delta k := by
  set d := (UnitAddTorus.mFourierBasis (d := Fin 3)).repr (V4.rawL2 hk) with hd
  have h1 := sectorForms_type112_le hlambda p
    (Manhattan.type112ShiftTwist (p 0) (p 1) (V4.rawType112Coefficients hk))
  have h2 : (∫ t, (symbolWeight 3 q.lambda p type112Pattern t +
        3 * halfSine (totalFrequency 3 p type112Pattern t)) *
        ‖(type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
          (V4.rawType112Coefficients hk)) : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3)) =
      ∫ t, parityWeight q.lambda (totalFrequency 3 ![0, -(p 1)] type112Pattern t) *
        ‖(type112FreqFun (Manhattan.type112DiagonalProjection d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
    have hmom : (![p 0 - p 0, p 1 - (p 1 + p 1)] : Fin 2 → ℝ) = ![0, -(p 1)] := by
      funext i
      fin_cases i <;> simp
    simp only [symbolWeight_add_halfSine]
    rw [parityWeight_integral_type112ShiftTwist, hmom]
    rfl
  have h3 := parityWeight_integral_type112DiagonalProjection_le_half hlambda.le
    ![0, -(p 1)] d (l2CongrLeft_rawSwap_repr_rawL2 hk hsym)
  have h4 : (∫ t, parityWeight q.lambda (totalFrequency 3 ![0, -(p 1)] type112Pattern t) *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3)) =
      parityWeightEnergy q.lambda (p 1) k := by
    rw [hd, LinearIsometryEquiv.symm_apply_apply, ← parityWeight_integral_rawL2 hlambda.le]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [parityWeight_congr_int q.lambda _ _ (totalFrequency_type112_frozen_congr (p 1) t)]
  have h5 := parityWeightEnergy_le_evenMajorantEnergy hlambda.le hdelta hk
  have hH : sectorHThreeForm q.lambda p (V4.rawWalsh p hk) =
      hThreeForm q.lambda p (Manhattan.type112WalshSynthesis
        (Manhattan.type112ShiftTwist (p 0) (p 1) (V4.rawType112Coefficients hk))) := rfl
  rw [hH]
  rw [h2] at h1
  change _ + sectorDFourForm hlambda p (Manhattan.type112WalshSynthesis
    (Manhattan.type112ShiftTwist (p 0) (p 1) (V4.rawType112Coefficients hk))) ≤ _
  rw [h4] at h3
  linarith

end

end Manhattan.Paper
