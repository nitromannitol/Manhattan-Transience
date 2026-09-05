import Manhattan.Glue.Transport
import Manhattan.Glue.OrderedContractivity

/-!
# The type-`(1,1,2)` sector of the weighted contractivity, and the `H₃` bound

Equation (46) is proved for the ordered representative in the coefficient
picture.  This file transports it to the type-`(1,1,2)` carrier of
`Manhattan/Walsh/Correction.lean` through the sorted enumeration, and combines
it with the Plancherel transport of `Manhattan/Glue/Transport.lean` to discharge
`ConcreteHThreeQuadraticBound`, the `H₃` half of Lemma 5.2 for the actual
corrected coefficient.

Paper: `manuscript.tex:1193-1198` (equation (46), `eq:contract`),
`manuscript.tex:1257-1272` (Lemma 5.2).
-/

noncomputable section

open MeasureTheory UnitAddTorus Set

namespace Manhattan.Glue

/-! ### The raw ordered carrier in the axis pattern `(h,h,v)` -/

/-- The tuple of lines with the type-`(1,1,2)` axis pattern and given
transverse coordinates. -/
def type112Tuple (n : Manhattan.RawType112Index) : Fin 3 → LineIndex :=
  fun a => (type112Pattern a, n a)

theorem type112Tuple_injective : Function.Injective type112Tuple := by
  intro n m h
  funext a
  exact congrArg Prod.snd (congrFun h a)

@[simp] theorem tuplePattern_type112Tuple (n : Manhattan.RawType112Index) :
    tuplePattern (type112Tuple n) = type112Pattern := rfl

@[simp] theorem tupleCoord_type112Tuple (n : Manhattan.RawType112Index) :
    tupleCoord (type112Tuple n) = n := rfl

/-- The raw type-`(1,1,2)` coefficient read as an ordered coefficient of
degree three, supported in the axis pattern `(h,h,v)`. -/
def rawOrdered :
    ℓ²(Manhattan.RawType112Index, ℂ) →ₗᵢ[ℂ] OrderedCoefficient 3 :=
  l2Extend type112Tuple type112Tuple_injective

theorem orderedFourier_rawOrdered (d : ℓ²(Manhattan.RawType112Index, ℂ)) :
    orderedFourier 3 (rawOrdered d) =
      lp.single 2 type112Pattern
        ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d) := by
  refine l2_ext' ((orderedFourier 3).toContinuousLinearMap.comp
      rawOrdered.toContinuousLinearMap)
    (((freqSingle type112Pattern).comp
      ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm.toLinearIsometry
        )).toContinuousLinearMap) ?_ d
  intro n
  change orderedFourier 3 (rawOrdered (lp.single 2 n (1 : ℂ))) =
    lp.single 2 type112Pattern
      ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm (lp.single 2 n (1 : ℂ)))
  rw [rawOrdered, l2Extend_single, orderedFourier_single, one_smul,
    HilbertBasis.repr_symm_single, orderedFreqFamily]
  simp

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section
open MeasureTheory UnitAddTorus Set

theorem isType112_lines {a b c : ℤ} (hab : a ≠ b) :
    Manhattan.IsType112Index
      {(Axis.horizontal, a), (Axis.horizontal, b), (Axis.vertical, c)} := by
  classical
  constructor
  · simp [hab]
  · rw [show Finset.filter (fun l : LineIndex => l.1 = Axis.horizontal)
        {(Axis.horizontal, a), (Axis.horizontal, b), (Axis.vertical, c)} =
        {(Axis.horizontal, a), (Axis.horizontal, b)} by
      ext l
      rcases l with ⟨i, k⟩
      cases i <;> simp]
    simp [hab]

theorem isType112_of_degreeEnum_eq {S : WalshDegreeIndex 3}
    {n : Manhattan.RawType112Index} (h : degreeEnum S = type112Tuple n) :
    Manhattan.IsType112Index S.1 := by
  classical
  have hne : n 0 ≠ n 1 := by
    intro hn
    have : degreeEnum S 0 = degreeEnum S 1 := by
      rw [h]
      show ((type112Pattern 0, n 0) : LineIndex) = (type112Pattern 1, n 1)
      rw [hn]
      rfl
    exact absurd (injective_degreeEnum_tuple 3 S this) (by decide)
  have hset : S.1 =
      ({(Axis.horizontal, n 0), (Axis.horizontal, n 1), (Axis.vertical, n 2)} :
        Finset LineIndex) := by
    apply Finset.coe_injective
    rw [← range_degreeEnum S, h]
    ext l
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [type112Tuple, type112Pattern]
    · intro hl
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hset]
  exact isType112_lines hne

/-- The ordered representative of the raw type-`(1,1,2)` coefficient is exactly
the coincident-row projection `Π₃` of `Manhattan/Walsh/Correction.lean`, read
inside degree three. -/
theorem orderedRestrict_rawOrdered (d : ℓ²(Manhattan.RawType112Index, ℂ)) :
    orderedRestrict 3 (rawOrdered d) =
      type112Extend (Manhattan.type112DiagonalProjection d) := by
  classical
  apply lp.ext
  funext S
  show rawOrdered d (degreeEnum S) =
    type112Extend (Manhattan.type112DiagonalProjection d) S
  by_cases hS : Manhattan.IsType112Index S.1
  · have hSd : type112Degree ⟨S.1, hS⟩ = S := Subtype.ext rfl
    rw [← hSd, degreeEnum_type112Degree,
      type112Extend, l2Extend_apply_image _ type112Degree_injective _ ⟨S.1, hS⟩]
    show rawOrdered d (type112Tuple (Manhattan.type112RawIndex ⟨S.1, hS⟩)) =
      Manhattan.type112DiagonalProjection d ⟨S.1, hS⟩
    rw [rawOrdered, l2Extend_apply_image _ type112Tuple_injective]
    rfl
  · have h1 : rawOrdered d (degreeEnum S) = 0 := by
      refine l2Extend_apply_of_notMem _ type112Tuple_injective _ _ ?_
      intro n hn
      exact hS (isType112_of_degreeEnum_eq hn.symm)
    have h2 : type112Extend (Manhattan.type112DiagonalProjection d) S = 0 := by
      refine l2Extend_apply_of_notMem _ type112Degree_injective _ _ ?_
      intro T hT
      exact hS (hT ▸ T.2)
    rw [h1, h2]

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section
open MeasureTheory UnitAddTorus Set

/-! ### The ordered-side `H` energy as a weighted integral -/

theorem inner_lp_eq_weighted_integral {n : ℕ} (u v : Lp ℂ 2 (LineTorusMeasure n))
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

/-- The ordered-side analogue of `re_inner_coeffH_eq_integral`: the raw
`H`-energy of an ordered coefficient is the weighted integral of its
line-frequency function. -/
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
          ‖((orderedFourier n c) σ) t‖ ^ 2 ∂(LineTorusMeasure n) := fun σ =>
    inner_lp_eq_weighted_integral _ _ _ (coeFn_freqH n lam p (orderedFourier n c) σ)
  rw [hΦ]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [hterm] using hre

/-! ### The weighted contractivity in the type-`(1,1,2)` coordinates -/

/-- **The contractivity (46) transported to the type-`(1,1,2)` sector.**
Restricting the raw Fourier coefficients to the strictly ordered row pairs
cannot increase the weighted energy `∫ (λ + θ(P)) |·|²`. -/
theorem symbolWeight_integral_type112DiagonalProjection_le {lam : ℝ}
    (hlam : 0 ≤ lam) (p : Fin 2 → ℝ) (d : ℓ²(Manhattan.RawType112Index, ℂ)) :
    (∫ t, symbolWeight 3 lam p type112Pattern t *
        ‖(type112FreqFun (Manhattan.type112DiagonalProjection d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      ≤ ∫ t, symbolWeight 3 lam p type112Pattern t *
        ‖(((UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm d) :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have h1 := re_inner_coeffH_orderedRestrict_le 3 hlam p (rawOrdered d)
  rw [orderedRestrict_rawOrdered, re_inner_coeffH_type112Extend,
    re_inner_orderedH_eq_integral 3 lam p (rawOrdered d),
    orderedFourier_rawOrdered, tsum_single_integral] at h1
  exact h1

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section
open MeasureTheory UnitAddTorus Set

/-! ### Discharge of `ConcreteHThreeQuadraticBound` -/

theorem hWeight_integral_rawCorrectionL2 {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    (∫ t, Estimates.hWeight q (rawCorrectionTotalFrequency p₂ t) *
        ‖(Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3))
      = rawCubicHWeightEnergy q a p₂ := by
  unfold rawCubicHWeightEnergy
  refine integral_congr_ae ?_
  filter_upwards [(Manhattan.rawCorrectionFunction_memLp (kappa := 40)
    (by norm_num) hlambda a p₂).coeFn_toLp] with t ht
  have h2 : (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
      UnitAddTorus (Fin 3) → ℂ) t = Manhattan.rawCorrectionFunction 40 q a p₂ t := ht
  rw [h2]

/-- **The blocker (T) of `O5-cubic.md`, discharged.**  The degree-three `H`
quadratic form of the manuscript's coefficient, at the frozen momentum
`(0,-p₂)`, is at most the raw `H`-weight energy of `k̃`. -/
theorem hThreeForm_frozen_correctionWalsh_le {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) :
    hThreeForm q.lambda ![0, -p₂]
        (Manhattan.correctionWalsh (kappa := 40) (by norm_num) hlambda a p₂) ≤
      rawCubicHWeightEnergy q a p₂ := by
  rw [hThreeForm_correctionWalsh hlambda a p₂]
  have hsymm : (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
      (Manhattan.rawCorrectionFourierCoefficients (kappa := 40)
        (by norm_num) hlambda a p₂)
      = Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ := by
    change (UnitAddTorus.mFourierBasis (d := Fin 3)).repr.symm
      ((UnitAddTorus.mFourierBasis (d := Fin 3)).repr
        (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  have key := symbolWeight_integral_type112DiagonalProjection_le hlambda.le
    ![0, -p₂] (Manhattan.rawCorrectionFourierCoefficients (kappa := 40)
      (by norm_num) hlambda a p₂)
  rw [hsymm] at key
  simp only [symbolWeight_eq_hWeight_type112] at key
  rw [← hWeight_integral_rawCorrectionL2 hlambda a p₂]
  exact key

/-- **`ConcreteHThreeQuadraticBound` at the true momentum.**  The `(shift)`
phase of `Manhattan.type112ShiftTwist` moves the frozen momentum `(0,-p₂)` of
 to the momentum `(p₁,p₂)` of the objective, exactly and with no loss;
before the phase was installed only the frozen momentum was reachable. -/
theorem concreteHThreeQuadraticBound {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) :
    ConcreteHThreeQuadraticBound q hlambda a p₁ p₂
      (hThreeForm q.lambda ![p₁, p₂]) := by
  show hThreeForm q.lambda ![p₁, p₂]
    (Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num)
      hlambda a p₁ p₂) ≤ rawCubicHWeightEnergy q a p₂
  have hk : Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num)
      hlambda a p₁ p₂ =
      Manhattan.type112WalshSynthesis
        (Manhattan.type112ShiftTwist (![p₁, p₂] 0) (![p₁, p₂] 1)
          (Manhattan.correctionType112Coefficients (kappa := 40) (by norm_num)
            hlambda a p₂)) := rfl
  rw [hk, hThreeForm_type112ShiftTwist_frozen]
  have hmom : (![p₁, p₂] : Fin 2 → ℝ) 1 = p₂ := rfl
  rw [hmom]
  exact hThreeForm_frozen_correctionWalsh_le hlambda a p₂

end

end Manhattan.Glue

namespace Manhattan.Glue

noncomputable section

/-- Lemma 5.2 and Proposition 4.2 for the concrete correction, with the `H₃`
half now proved: the only remaining premise is the degree-four raising bound.
-/
theorem correctionWalsh_hThree_add_dFour_le_sqrtScale {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) (hrho : 0 ≤ q.rho)
    (hrhopi : 3 * q.rho < Real.pi) {C a p₁ p₂ : ℝ} (ha : 0 ≤ a) (hp₂ : |p₂| ≤ a)
    (dFour : WalshL2 → ℝ)
    (hD : ConcreteDThreeRaisingBound q hlambda a p₁ p₂ dFour)
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C q a) :
    let k := Manhattan.shiftedCorrectionWalsh (kappa := 40) (by norm_num)
      hlambda a p₁ p₂
    hThreeForm q.lambda ![p₁, p₂] k + dFour k ≤
      2 * C * Real.sqrt (q.scaleLog a) :=
  correctionWalsh_cubicEnergy_le_sqrtScale_of_sectors hlambda hK hrho hrhopi ha hp₂
    (hThreeForm q.lambda ![p₁, p₂]) dFour
    (concreteHThreeQuadraticBound hlambda a p₁ p₂) hD hfive

end

end Manhattan.Glue
