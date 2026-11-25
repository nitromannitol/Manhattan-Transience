import Manhattan.Paper.LemmaFour
import Manhattan.Paper.LemmaDistinct
import Mathlib.Algebra.Order.Chebyshev

/-!
# The degree-three cost of a coefficient of type `112`, without loss

Step 1 of `lem:parity` (`paper/arxiv/main.tex:791-858`) bounds
`‖k‖₊² + ‖D₃ k‖₋²` for `k ∈ ℋ₃` of type `112` by the quadratic form of the
bracket

    λ + d(β) + d(α) + 3 sin²β / √(μ_β(μ_β+2)) + 2 sin²α / √(μ_α(μ_α+2)),
    μ_β = λ + d(β), μ_α = λ + d(α),

a function of the total frequency `P = (β, α)`.  The proof, followed here:

* by `eq:iso` the degree-four energy is `4! ⟨Π₄ D̃₃ f, (λ+θ(P))⁻¹ Π₄ D̃₃ f⟩` for the
  symmetric coefficient `f` of `k` (`Manhattan.Paper.hMinusEnergy_eq_symCoeff`,
  `Manhattan.Paper.symCoeff_walshRaise`), and `Π₄` is dropped by `eq:contract`;
* by `eq:raise` each sector of `D̃₃ f` is `¼` times a sum over the four slots;
  a slot contributes only when deleting it leaves a pattern of type `112`, which
  happens for three slots when a row is added and for two when a column is added
  (`card_type112Slots_le`), so the square of the sum is at most that number times
  the sum of squares;
* the frequency of the added line is integrated by `eq:line-integral`
  (`Manhattan.Glue.integral_insertNth_energy`).

The bracket is then bounded by `λ + θ(P) + 3(2|sin(P₁/2)| + 2|sin(P₂/2)|)`
(`lineResolvent_mul_sin_sq_le`), and the result is
`sectorForms_type112_le`.
-/

open scoped lp
open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

noncomputable section

/-! ### The half-sine weight -/

/-- `2|sin(P₁/2)| + 2|sin(P₂/2)|`. -/
def halfSine (P : Fin 2 → ℝ) : ℝ := 2 * |Real.sin (P 0 / 2)| + 2 * |Real.sin (P 1 / 2)|

theorem halfSine_nonneg (P : Fin 2 → ℝ) : 0 ≤ halfSine P := by
  unfold halfSine
  positivity

/-- The half-sine weight as a complex function on the two-torus. -/
def halfSineMapC : C(UnitAddTorus (Fin 2), ℂ) :=
  ⟨fun ψ => ((Real.sqrt (2 * (1 - cosMap (ψ 0))) + Real.sqrt (2 * (1 - cosMap (ψ 1))) : ℝ) : ℂ),
    by
      have h0 : Continuous fun ψ : UnitAddTorus (Fin 2) => cosMap (ψ 0) :=
        cosMap.continuous.comp (continuous_apply 0)
      have h1 : Continuous fun ψ : UnitAddTorus (Fin 2) => cosMap (ψ 1) :=
        cosMap.continuous.comp (continuous_apply 1)
      exact Complex.continuous_ofReal.comp (by fun_prop)⟩

theorem halfSineMapC_totalFrequencyPoint (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    halfSineMapC (totalFrequencyPoint n p σ t) =
      ((halfSine (totalFrequency n p σ t) : ℝ) : ℂ) := by
  show ((Real.sqrt (2 * (1 - cosMap _)) + Real.sqrt (2 * (1 - cosMap _)) : ℝ) : ℂ) = _
  simp only [totalFrequencyPoint, cosMap_coe]
  rw [halfSine, two_abs_sin_half_eq_sqrt, two_abs_sin_half_eq_sqrt, Estimates.dispersion,
    Estimates.dispersion]

theorem continuous_halfSine_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    Continuous fun t => halfSine (totalFrequency n p σ t) := by
  have h : (fun t => halfSine (totalFrequency n p σ t)) =
      fun t => (halfSineMapC (totalFrequencyPoint n p σ t)).re := by
    funext t
    rw [halfSineMapC_totalFrequencyPoint, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp
    (halfSineMapC.continuous.comp (continuous_totalFrequencyPoint n p σ))

/-- The quadratic form of the half-sine multiplier on the frequency side. -/
theorem re_inner_freqMultiplier_halfSine (n : ℕ) (p : Fin 2 → ℝ) (v : LineFreqL2 n) :
    RCLike.re (inner ℂ v (freqMultiplier n p halfSineMapC v)) =
      ∑ σ : Fin n → Axis, ∫ t, halfSine (totalFrequency n p σ t) *
        ‖(v σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [inner_lineFreq, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [L2.inner_def, ← integral_re]
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_freqMultiplier n p halfSineMapC v σ] with t ht
    rw [ht, RCLike.inner_apply]
    show RCLike.re ((halfSineMapC (totalFrequencyPoint n p σ t) *
        (v σ : UnitAddTorus (Fin n) → ℂ) t) *
          (starRingEnd ℂ) ((v σ : UnitAddTorus (Fin n) → ℂ) t)) = _
    rw [halfSineMapC_totalFrequencyPoint, mul_assoc, Complex.mul_conj',
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  · exact L2.integrable_inner _ _

/-- The half-sine quadratic form of an ordered coefficient. -/
theorem re_inner_orderedMultiplier_halfSine (n : ℕ) (p : Fin 2 → ℝ) (w : OrderedCoefficient n) :
    RCLike.re (inner ℂ w (orderedMultiplier n p halfSineMapC w)) =
      ∑ σ : Fin n → Axis, ∫ t, halfSine (totalFrequency n p σ t) *
        ‖((orderedFourier n w) σ : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure n) := by
  rw [← (orderedFourierEquiv n).inner_map_map, orderedFourierEquiv_apply,
    orderedFourierEquiv_apply, orderedFourier_orderedMultiplier, re_inner_freqMultiplier_halfSine]

/-- **`eq:iso` for the half-sine weight.**  Six times the half-sine form of the
symmetric coefficient is the half-sine form of the sorted coefficient. -/
theorem six_mul_halfSine_symCoeff (p : Fin 2 → ℝ) (c : DegreeCoefficient 3) :
    6 * ∑ σ : Fin 3 → Axis, ∫ t, halfSine (totalFrequency 3 p σ t) *
        ‖((orderedFourier 3 (symCoeff 3 (homogeneousWalshSynthesis 3 c))) σ :
          UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) =
      ∑ σ : Fin 3 → Axis, ∫ t, halfSine (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 c) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  have h1 := re_inner_orderedMultiplier_halfSine 3 p (symCoeff 3 (homogeneousWalshSynthesis 3 c))
  have h2 := re_inner_orderedMultiplier_halfSine 3 p (walshOrdered 3 c)
  rw [inner_symCoeff_orderedMultiplier] at h1
  have hfac : ((Nat.factorial 3 : ℕ) : ℂ)⁻¹ = (((6 : ℝ)⁻¹ : ℝ) : ℂ) := by
    norm_num [Nat.factorial]
  rw [hfac, RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, h2] at h1
  change _ = ∑ σ : Fin 3 → Axis, ∫ t, halfSine (totalFrequency 3 p σ t) *
    ‖((orderedFourier 3 (walshOrdered 3 c)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
      ∂(LineTorusMeasure 3)
  rw [← h1]
  ring

/-! ### The scalar step -/

/-- `sin² x / √(μ(μ+2)) ≤ 2|sin(x/2)|` for `μ = λ + d(x)`: the inequalities
`sin² x ≤ |x|√(2d(x))` and `d ≤ μ` of the paper, at the level of `sin(x/2)`. -/
theorem lineResolvent_mul_sin_sq_le {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    (Real.sqrt ((lam + Estimates.dispersion x) * (lam + Estimates.dispersion x + 2)))⁻¹ *
        Real.sin x ^ 2 ≤ 2 * |Real.sin (x / 2)| := by
  set μ := lam + Estimates.dispersion x with hμdef
  have hd := Estimates.dispersion_nonneg x
  have hμ : 0 < μ := by linarith
  have h2μ : Real.sqrt (2 * μ) ≤ Real.sqrt (μ * (μ + 2)) := Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : 0 < Real.sqrt (2 * μ) := Real.sqrt_pos.2 (by linarith)
  have hhalf : 2 * |Real.sin (x / 2)| ≤ Real.sqrt (2 * μ) := by
    rw [two_abs_sin_half_eq_sqrt]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsin : Real.sin x ^ 2 ≤ (2 * |Real.sin (x / 2)|) ^ 2 := by
    have h := Real.sin_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    rw [h, mul_pow, mul_pow, mul_pow, sq_abs]
    nlinarith [Real.cos_sq_le_one (x / 2), sq_nonneg (Real.sin (x / 2))]
  have hA : 0 ≤ 2 * |Real.sin (x / 2)| := by positivity
  calc (Real.sqrt (μ * (μ + 2)))⁻¹ * Real.sin x ^ 2
      ≤ (Real.sqrt (2 * μ))⁻¹ * Real.sin x ^ 2 :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hs2 h2μ) (sq_nonneg _)
    _ ≤ (Real.sqrt (2 * μ))⁻¹ * (2 * |Real.sin (x / 2)| * Real.sqrt (2 * μ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hs2.le)
        nlinarith [hsin, hhalf, hA]
    _ = 2 * |Real.sin (x / 2)| := by field_simp

/-! ### Counting the slots -/

/-- The number of terms of `eq:raise` in a sector of type `1112` (a row added) or
`1122` (a column added). -/
def slotCount (a : Axis) : ℝ := if a = Axis.horizontal then 3 else 2

theorem slotCount_nonneg (a : Axis) : 0 ≤ slotCount a := by
  unfold slotCount
  split_ifs <;> norm_num

/-- In a degree-four pattern, if deleting slot `r` leaves a pattern of type `112`,
then the slots with that property number three when slot `r` is a row and two
when it is a column. -/
theorem card_type112Slots_le (σ : Fin 4 → Axis) (r : Fin 4)
    (hr : IsType112Pattern (Fin.removeNth r σ)) :
    ((Finset.univ.filter fun r' : Fin 4 => IsType112Pattern (Fin.removeNth r' σ)).card : ℝ) ≤
      slotCount (σ r) := by
  have key : ∀ (σ : Fin 4 → Axis) (r : Fin 4), IsType112Pattern (Fin.removeNth r σ) →
      (Finset.univ.filter fun r' : Fin 4 => IsType112Pattern (Fin.removeNth r' σ)).card ≤
        (if σ r = Axis.horizontal then 3 else 2) := by
    decide
  have h := key σ r hr
  unfold slotCount
  split_ifs with ha
  · rw [if_pos ha] at h
    exact_mod_cast h
  · rw [if_neg ha] at h
    exact_mod_cast h

/-- A reordering of the pattern `hhv` is a pattern of type `112`. -/
theorem isType112Pattern_of_comp_eq (τ : Fin 3 → Axis) (π : Equiv.Perm (Fin 3))
    (h : τ ∘ π = type112Pattern) : IsType112Pattern τ := by
  have key : ∀ (τ : Fin 3 → Axis) (π : Equiv.Perm (Fin 3)),
      τ ∘ π = ![Axis.horizontal, Axis.horizontal, Axis.vertical] → IsType112Pattern τ := by
    decide
  exact key τ π h

/-- The symmetric coefficient of a coefficient of type `112` has no
line-frequency component outside the three patterns of type `112`. -/
theorem orderedFourier_symCoeff_type112Extend_of_not (ct : ℓ²(Manhattan.Type112Index, ℂ))
    (τ : Fin 3 → Axis) (hτ : ¬ IsType112Pattern τ) :
    (orderedFourier 3 (symCoeff 3 (homogeneousWalshSynthesis 3 (type112Extend ct)))) τ = 0 := by
  rw [symCoeff_homogeneousWalshSynthesis, ← freqEval_apply 3 τ, map_smul, map_smul, map_sum,
    map_sum]
  refine (smul_eq_zero_of_right _ (Finset.sum_eq_zero fun π _ => ?_))
  rw [freqEval_apply, orderedFourier_slotPermute]
  have hne : τ ∘ π ≠ type112Pattern := fun h => hτ (isType112Pattern_of_comp_eq τ π h)
  change torusPerm 3 π ((lineIndexFourier 3 (type112Extend ct)) (τ ∘ π)) = 0
  rw [lineIndexFourier_type112Extend, lp.single_apply_ne _ _ _ hne, map_zero]

/-! ### Integrability -/

theorem integrable_continuous_mul_norm_sq {n : ℕ} {w : UnitAddTorus (Fin n) → ℝ}
    (hw : Continuous w) (F : Lp ℂ 2 (LineTorusMeasure n)) :
    Integrable (fun t => w t * ‖(F : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2) (LineTorusMeasure n) := by
  set W : C(UnitAddTorus (Fin n), ℝ) := ⟨w, hw⟩ with hW
  refine (integrable_norm_sq_lp n F).bdd_mul (c := ‖W‖) hw.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => W.norm_coe_le_norm t

theorem continuous_lineResolvent_totalFrequency (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (σ : Fin n → Axis) (i : Fin 2) :
    Continuous fun s => (Real.sqrt ((lam + Estimates.dispersion (totalFrequency n p σ s i)) *
      ((lam + Estimates.dispersion (totalFrequency n p σ s i)) + 2)))⁻¹ := by
  have hd := continuous_dispersion_totalFrequency n p σ i
  have hpos : ∀ s, 0 < (lam + Estimates.dispersion (totalFrequency n p σ s i)) *
      ((lam + Estimates.dispersion (totalFrequency n p σ s i)) + 2) := by
    intro s
    have := Estimates.dispersion_nonneg (totalFrequency n p σ s i)
    positivity
  refine Continuous.inv₀ ?_ fun s => (Real.sqrt_pos.2 (hpos s)).ne'
  exact Real.continuous_sqrt.comp ((continuous_const.add hd).mul
    ((continuous_const.add hd).add continuous_const))

theorem continuous_two_abs_sin_half_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (i : Fin 2) :
    Continuous fun s => 2 * |Real.sin (totalFrequency n p σ s i / 2)| := by
  have h : (fun s => 2 * |Real.sin (totalFrequency n p σ s i / 2)|) =
      fun s => Real.sqrt (2 * Estimates.dispersion (totalFrequency n p σ s i)) := by
    funext s
    exact two_abs_sin_half_eq_sqrt _
  rw [h]
  exact Real.continuous_sqrt.comp (continuous_const.mul
    (continuous_dispersion_totalFrequency n p σ i))

/-! ### The raw raising operator against `H⁻¹` -/

/-- The shift of the raising operator keeps every axis sector in which the
coefficient vanishes. -/
theorem orderedFourier_orderedRaiseShift_eq_zero (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2)
    (f : OrderedCoefficient n) {τ : Fin n → Axis} (hτ : (orderedFourier n f) τ = 0) :
    (orderedFourier n (orderedRaiseShift n p i f)) τ = 0 := by
  have hae := orderedFourier_orderedRaiseShift n p i f τ
  rw [hτ] at hae
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hae, Lp.coeFn_zero ℂ 2 (LineTorusMeasure n)] with t h1 h2
  rw [h1, h2]
  simp

/-- **The energy of `D̃₃` on a coefficient of type `112`.**  For a degree-three
ordered coefficient `f` whose line-frequency coefficient vanishes outside the
patterns of type `112`, `⟨D̃₃ f, (λ+θ(P))⁻¹ D̃₃ f⟩` is at most `¾` of the
half-sine form of `f`.  Each sector of `D̃₃ f` is `¼` times a sum of at most
three (row added) or two (column added) nonzero slot terms; the squared sum is
bounded by that number times the sum of squares, and integrating the added
line's frequency gives `sin²(P_i)/√(μ_i(μ_i+2)) ≤ 2|sin(P_i/2)|`. -/
theorem re_inner_rawRaise_hInv_le {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (f : OrderedCoefficient 3)
    (hfz : ∀ τ : Fin 3 → Axis, ¬ IsType112Pattern τ → (orderedFourier 3 f) τ = 0) :
    RCLike.re (inner ℂ (rawRaise 3 p f)
        (orderedMultiplier (3 + 1) p (hInvMap hlam) (rawRaise 3 p f))) ≤
      3 / 4 * ∑ τ : Fin 3 → Axis, ∫ s, halfSine (totalFrequency 3 p τ s) *
        ‖((orderedFourier 3 f) τ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3) := by
  classical
  set G : (Fin (3 + 1) → Axis) → Fin (3 + 1) → Lp ℂ 2 (LineTorusMeasure (3 + 1)) :=
    fun σ r => torusRemove 3 r
      ((orderedFourier 3 (orderedRaiseShift 3 p (axisIndex (σ r)) f)) (Fin.removeNth r σ))
    with hG
  set B : Fin 2 → (Fin 3 → Axis) → ℝ := fun i τ =>
    ∫ s, 2 * |Real.sin (totalFrequency 3 p τ s i / 2)| *
      ‖((orderedFourier 3 f) τ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3)
    with hB
  -- the frequency form of the quadratic form
  have hfreq : RCLike.re (inner ℂ (rawRaise 3 p f)
      (orderedMultiplier (3 + 1) p (hInvMap hlam) (rawRaise 3 p f))) =
      ∑ σ : Fin (3 + 1) → Axis, ∫ t, (symbolWeight (3 + 1) lam p σ t)⁻¹ *
        ‖((orderedFourier (3 + 1) (rawRaise 3 p f)) σ : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure (3 + 1)) := by
    rw [← (orderedFourierEquiv (3 + 1)).inner_map_map, orderedFourierEquiv_apply,
      orderedFourierEquiv_apply, orderedFourier_orderedMultiplier, re_inner_freqMultiplier]
  -- `eq:raise` sector by sector, as a sum of slot terms
  have hsector : ∀ σ : Fin (3 + 1) → Axis, (orderedFourier (3 + 1) (rawRaise 3 p f)) σ =
      (((3 + 1 : ℕ) : ℂ)⁻¹) • ∑ r : Fin (3 + 1), G σ r := by
    intro σ
    have e1 : orderedFourier (3 + 1) (rawRaise 3 p f) = (((3 + 1 : ℕ) : ℂ)⁻¹) •
        ∑ i : Fin 2, ∑ r : Fin (3 + 1),
          orderedFourier (3 + 1) (insertLine 3 r i (orderedRaiseShift 3 p i f)) := by
      rw [rawRaise]
      simp only [smul_apply, sum_apply,
        ContinuousLinearMap.comp_apply, map_smul, map_sum]
    rw [e1, ← freqEval_apply (3 + 1) σ, map_smul]
    simp only [map_sum, freqEval_apply, orderedFourier_insertLine_apply]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    exact sum_ite_finAxis (σ r) (fun i => torusRemove 3 r
      ((orderedFourier 3 (orderedRaiseShift 3 p i f)) (Fin.removeNth r σ)))
  -- a slot term vanishes unless deleting the slot leaves a pattern of type `112`
  have hG0 : ∀ (σ : Fin (3 + 1) → Axis) (r : Fin (3 + 1)),
      ¬ IsType112Pattern (Fin.removeNth r σ) → G σ r = 0 := by
    intro σ r hr
    simp only [hG]
    rw [orderedFourier_orderedRaiseShift_eq_zero 3 p _ f (hfz _ hr), map_zero]
  -- one slot term, by the line integral
  have hslot : ∀ (σ : Fin (3 + 1) → Axis) (r : Fin (3 + 1)),
      ∫ t, (symbolWeight (3 + 1) lam p σ t)⁻¹ *
          ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure (3 + 1)) ≤
        B (axisIndex (σ r)) (Fin.removeNth r σ) := by
    intro σ r
    have hσ : Fin.insertNth r (finAxis (axisIndex (σ r))) (Fin.removeNth r σ) = σ := by
      rw [finAxis_axisIndex, Fin.insertNth_self_removeNth]
    have h := integral_insertNth_energy 3 hlam p (axisIndex (σ r)) r (Fin.removeNth r σ)
      ((orderedFourier 3 (orderedRaiseShift 3 p (axisIndex (σ r)) f)) (Fin.removeNth r σ))
    rw [hσ] at h
    simp only [hG]
    rw [h]
    refine integral_mono_ae (integrable_continuous_mul_norm_sq
        (continuous_lineResolvent_totalFrequency 3 hlam p _ _) _)
      (integrable_continuous_mul_norm_sq (continuous_two_abs_sin_half_totalFrequency 3 p _ _) _)
      ?_
    filter_upwards [orderedFourier_orderedRaiseShift 3 p (axisIndex (σ r)) f
      (Fin.removeNth r σ)] with s hs
    rw [hs, norm_mul, mul_pow, norm_raisingSymbol, sq_abs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (lineResolvent_mul_sin_sq_le hlam _) (sq_nonneg _)
  -- one sector, by Cauchy–Schwarz over the slots
  have hsec : ∀ σ : Fin (3 + 1) → Axis,
      ∫ t, (symbolWeight (3 + 1) lam p σ t)⁻¹ *
          ‖((orderedFourier (3 + 1) (rawRaise 3 p f)) σ : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure (3 + 1)) ≤
        ∑ r : Fin (3 + 1), 1 / 16 * slotCount (σ r) * B (axisIndex (σ r)) (Fin.removeNth r σ) := by
    intro σ
    set R := Finset.univ.filter fun r : Fin (3 + 1) => IsType112Pattern (Fin.removeNth r σ)
      with hR
    have hsum : ∑ r : Fin (3 + 1), G σ r = ∑ r ∈ R, G σ r :=
      (Finset.sum_subset (Finset.subset_univ R) fun r _ hr => hG0 σ r (by
        simpa [hR] using hr)).symm
    have hcard : ∀ r ∈ R, (R.card : ℝ) ≤ slotCount (σ r) := fun r hr =>
      card_type112Slots_le σ r (by simpa [hR] using hr)
    set w : UnitAddTorus (Fin (3 + 1)) → ℝ := fun t => (symbolWeight (3 + 1) lam p σ t)⁻¹
      with hw
    have hwc : Continuous w := continuous_inv_symbolWeight (3 + 1) hlam p σ
    have hw0 : ∀ t, 0 ≤ w t := fun t => inv_nonneg.2 (symbolWeight_pos (3 + 1) hlam p σ t).le
    have hrhs : ∫ t, ∑ r : Fin (3 + 1), 1 / 16 * slotCount (σ r) *
          (w t * ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2) ∂(LineTorusMeasure (3 + 1)) =
        ∑ r : Fin (3 + 1), 1 / 16 * slotCount (σ r) *
          ∫ t, w t * ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure (3 + 1)) := by
      rw [integral_finsetSum _ fun r _ =>
        (integrable_continuous_mul_norm_sq hwc (G σ r)).const_mul _]
      exact Finset.sum_congr rfl fun r _ => integral_const_mul _ _
    have hle : ∫ t, w t *
          ‖((orderedFourier (3 + 1) (rawRaise 3 p f)) σ : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure (3 + 1)) ≤
        ∫ t, ∑ r : Fin (3 + 1), 1 / 16 * slotCount (σ r) *
          (w t * ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2) ∂(LineTorusMeasure (3 + 1)) := by
      refine integral_mono_ae (integrable_continuous_mul_norm_sq hwc _)
        (integrable_finsetSum _ fun r _ =>
          (integrable_continuous_mul_norm_sq hwc (G σ r)).const_mul _) ?_
      rw [hsector σ, hsum]
      filter_upwards [Lp.coeFn_smul (((3 + 1 : ℕ) : ℂ)⁻¹) (∑ r ∈ R, G σ r),
        coeFn_finset_sum R (G σ)] with t h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul, norm_mul, mul_pow]
      have hc : ‖(((3 + 1 : ℕ) : ℂ)⁻¹)‖ ^ 2 = 1 / 16 := by
        rw [norm_inv, Complex.norm_natCast]
        norm_num
      rw [hc]
      have hcs : ‖∑ r ∈ R, (G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2 ≤
          R.card * ∑ r ∈ R, ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2 := by
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
        exact sq_sum_le_card_mul_sum_sq
      have hcount : (R.card : ℝ) * ∑ r ∈ R, ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2 ≤
          ∑ r : Fin (3 + 1), slotCount (σ r) *
            ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum fun r hr =>
          mul_le_mul_of_nonneg_right (hcard r hr) (sq_nonneg _)) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) fun r _ _ =>
          mul_nonneg (slotCount_nonneg _) (sq_nonneg _)
      have hfin : ∑ r : Fin (3 + 1), 1 / 16 * slotCount (σ r) *
            (w t * ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2) =
          w t * (1 / 16 * ∑ r : Fin (3 + 1), slotCount (σ r) *
            ‖(G σ r : UnitAddTorus (Fin (3 + 1)) → ℂ) t‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hfin]
      refine mul_le_mul_of_nonneg_left ?_ (hw0 t)
      nlinarith [hcs, hcount]
    rw [hrhs] at hle
    refine hle.trans (Finset.sum_le_sum fun r _ => ?_)
    exact mul_le_mul_of_nonneg_left (hslot σ r)
      (mul_nonneg (by norm_num) (slotCount_nonneg _))
  -- reindexing the slots
  have hreindex : ∀ r : Fin (3 + 1),
      (∑ σ : Fin (3 + 1) → Axis, 1 / 16 * slotCount (σ r) *
          B (axisIndex (σ r)) (Fin.removeNth r σ)) =
        ∑ τ : Fin 3 → Axis, 1 / 16 * (3 * B 0 τ + 2 * B 1 τ) := by
    intro r
    have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (3 + 1) => Axis) r)
      (fun z : Axis × (Fin 3 → Axis) => 1 / 16 * slotCount z.1 * B (axisIndex z.1) z.2)
      (fun σ => 1 / 16 * slotCount (σ r) * B (axisIndex (σ r)) (Fin.removeNth r σ))
      (fun z => by
        obtain ⟨a, τ⟩ := z
        change 1 / 16 * slotCount a * B (axisIndex a) τ =
          1 / 16 * slotCount (Fin.insertNth (α := fun _ => Axis) r a τ r) *
            B (axisIndex (Fin.insertNth (α := fun _ => Axis) r a τ r))
              (Fin.removeNth r (Fin.insertNth (α := fun _ => Axis) r a τ))
        rw [Fin.insertNth_apply_same, Fin.removeNth_insertNth])
    rw [← h, Fintype.sum_prod_type, sum_univ_axis]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [slotCount, axisIndex, if_true, reduceCtorEq, if_false]
    ring
  -- the half-sine form
  have hB : ∀ τ : Fin 3 → Axis, 3 * B 0 τ + 2 * B 1 τ ≤
      3 * ∫ s, halfSine (totalFrequency 3 p τ s) *
        ‖((orderedFourier 3 f) τ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3) := by
    intro τ
    have hi0 := integrable_continuous_mul_norm_sq
      (continuous_two_abs_sin_half_totalFrequency 3 p τ 0) ((orderedFourier 3 f) τ)
    have hi1 := integrable_continuous_mul_norm_sq
      (continuous_two_abs_sin_half_totalFrequency 3 p τ 1) ((orderedFourier 3 f) τ)
    have hsplit : ∫ s, halfSine (totalFrequency 3 p τ s) *
          ‖((orderedFourier 3 f) τ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3) =
        B 0 τ + B 1 τ := by
      rw [hB, ← integral_add hi0 hi1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [halfSine]
      ring
    have hB1 : 0 ≤ B 1 τ := by
      rw [hB]
      exact integral_nonneg fun s => mul_nonneg (by positivity) (sq_nonneg _)
    rw [hsplit]
    linarith
  -- assembling
  rw [hfreq]
  refine le_trans (Finset.sum_le_sum fun σ _ => hsec σ) ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun r _ => hreindex r, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, Finset.mul_sum]
  have hfin : (↑(3 + 1 : ℕ) : ℝ) * ∑ τ : Fin 3 → Axis, 1 / 16 * (3 * B 0 τ + 2 * B 1 τ) ≤
      3 / 4 * ∑ τ : Fin 3 → Axis, ∫ s, halfSine (totalFrequency 3 p τ s) *
        ‖((orderedFourier 3 f) τ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have := hB τ
    push_cast
    nlinarith
  exact hfin

/-! ### The degree-four energy of a coefficient of type `112` -/

/-- **The degree-four half of `eq:majorant`.**  For `k ∈ ℋ₃` of type `112`,
`‖D₃ k‖₋²` is at most three times the half-sine form of `k`. -/
theorem sectorDFourForm_le_halfSine {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (ct : ℓ²(Manhattan.Type112Index, ℂ)) :
    sectorDFourForm hlam p (homogeneousWalshSynthesis 3 (type112Extend ct)) ≤
      3 * ∑ σ : Fin 3 → Axis, ∫ t, halfSine (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) := by
  have hF3 : homogeneousWalshSynthesis 3 (type112Extend ct) ∈ Manhattan.walshDegree 3 :=
    homogeneousWalshSynthesis_mem_degree 3 _
  have hD4 : walshRaise p (homogeneousWalshSynthesis 3 (type112Extend ct)) ∈
      (Manhattan.walshDegree 4 : Set WalshL2) := walshRaise_mem_walshDegree p hF3
  rw [walshDegree_eq_range] at hD4
  obtain ⟨c4, hc4⟩ := hD4
  have h := hMinusEnergy_eq_symCoeff 4 hlam p c4
  rw [hc4, symCoeff_walshRaise, offDiagonalProjection_symCoeff] at h
  set u := rawRaise 3 p (symCoeff 3 (homogeneousWalshSynthesis 3 (type112Extend ct))) with hu
  set M := orderedMultiplier (3 + 1) p (hInvMap hlam) with hM
  have hconj : ∀ x : OrderedCoefficient (3 + 1),
      RCLike.re (inner ℂ x (M x)) = RCLike.re (inner ℂ (M x) x) := by
    intro x
    rw [← InnerProductSpace.conj_inner_symm, RCLike.conj_re]
  have hpos : ∀ x : OrderedCoefficient (3 + 1), 0 ≤ RCLike.re (inner ℂ (M x) x) := by
    intro x
    rw [← hconj, hM, ← (orderedFourierEquiv (3 + 1)).inner_map_map, orderedFourierEquiv_apply,
      orderedFourierEquiv_apply, orderedFourier_orderedMultiplier, re_inner_freqMultiplier]
    exact Finset.sum_nonneg fun σ _ => integral_nonneg fun t =>
      mul_nonneg (inv_nonneg.2 (symbolWeight_pos (3 + 1) hlam p σ t).le) (sq_nonneg _)
  have hcontr : RCLike.re (inner ℂ (offDiagonalProjection (3 + 1) u)
      (M (offDiagonalProjection (3 + 1) u))) ≤ RCLike.re (inner ℂ u (M u)) := by
    rw [hconj, hconj]
    refine re_inner_le_of_commuting_projection M (offDiagonalProjection (3 + 1)) ?_ ?_ ?_ hpos u
    · intro c
      exact congrArg (fun T => T c) (offDiagonalProjection_idem (3 + 1))
    · intro x y
      exact (offDiagonalProjection_isSelfAdjoint (3 + 1)).isSymmetric x y
    · intro c
      exact congrArg (fun T => T c)
        (offDiagonalProjection_comp_orderedMultiplier (3 + 1) p (hInvMap hlam))
  have hraw := re_inner_rawRaise_hInv_le hlam p
    (symCoeff 3 (homogeneousWalshSynthesis 3 (type112Extend ct)))
    (fun τ hτ => orderedFourier_symCoeff_type112Extend_of_not ct τ hτ)
  have hsix := six_mul_halfSine_symCoeff p (type112Extend ct)
  have hD : sectorDFourForm hlam p (homogeneousWalshSynthesis 3 (type112Extend ct)) =
      24 * RCLike.re (inner ℂ (offDiagonalProjection (3 + 1) u)
        (M (offDiagonalProjection (3 + 1) u))) := by
    show (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (walshSectorComponent (fun S => S.card = 4)
        (concreteFiberA p (homogeneousWalshSynthesis 3 (type112Extend ct)))) = _
    rw [walshSectorComponent_four_walshRaise p hF3, h]
    norm_num [Nat.factorial]
  rw [hD]
  nlinarith [hcontr, hraw, hsix]

/-! ### `eq:majorant` for a coefficient of type `112` -/

/-- **The first display of Step 1 of `lem:parity`, bounded by the half-sine
weight.**  For `k ∈ ℋ₃` of type `112`,
`‖k‖₊² + ‖D₃ k‖₋² ≤ ⟨k, (λ + θ(P) + 3(2|sin(P₁/2)| + 2|sin(P₂/2)|)) k⟩`. -/
theorem sectorForms_le_halfSine {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (ct : ℓ²(Manhattan.Type112Index, ℂ)) :
    sectorHThreeForm lam p (homogeneousWalshSynthesis 3 (type112Extend ct)) +
        sectorDFourForm hlam p (homogeneousWalshSynthesis 3 (type112Extend ct)) ≤
      ∑ σ : Fin 3 → Axis, ∫ t, (symbolWeight 3 lam p σ t +
          3 * halfSine (totalFrequency 3 p σ t)) *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) := by
  have hH : sectorHThreeForm lam p (homogeneousWalshSynthesis 3 (type112Extend ct)) =
      ∑ σ : Fin 3 → Axis, ∫ t, symbolWeight 3 lam p σ t *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) := by
    have h0 := re_inner_coeffH_eq_integral 3 lam p (type112Extend ct)
    rw [tsum_fintype] at h0
    rw [← h0, sectorHThreeForm_eq, hThreeForm, fiberH_homogeneousWalshSynthesis,
      (homogeneousWalshSynthesis 3).inner_map_map]
  have hD := sectorDFourForm_le_halfSine hlam p ct
  have hsplit : ∀ σ : Fin 3 → Axis, ∫ t, (symbolWeight 3 lam p σ t +
        3 * halfSine (totalFrequency 3 p σ t)) *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) =
      ∫ t, symbolWeight 3 lam p σ t *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) +
      3 * ∫ t, halfSine (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 (type112Extend ct)) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) := by
    intro σ
    rw [← integral_const_mul, ← integral_add
      (integrable_continuous_mul_norm_sq (continuous_symbolWeight 3 lam p σ) _)
      ((integrable_continuous_mul_norm_sq (continuous_halfSine_totalFrequency 3 p σ) _).const_mul
        _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  rw [Finset.sum_congr rfl fun σ _ => hsplit σ, Finset.sum_add_distrib, ← Finset.mul_sum, hH]
  linarith

/-- **`eq:majorant` in the type-`112` coordinates**: the same bound for the Walsh
vector of a coefficient of type `112`, whose only axis pattern is `hhv`. -/
theorem sectorForms_type112_le {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (ct : ℓ²(Manhattan.Type112Index, ℂ)) :
    hThreeForm lam p (Manhattan.type112WalshSynthesis ct) +
        sectorDFourForm hlam p (Manhattan.type112WalshSynthesis ct) ≤
      ∫ t, (symbolWeight 3 lam p type112Pattern t +
          3 * halfSine (totalFrequency 3 p type112Pattern t)) *
        ‖(type112FreqFun ct : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 3) := by
  classical
  have h := sectorForms_le_halfSine hlam p ct
  rw [← sectorHThreeForm_eq, type112WalshSynthesis_eq_homogeneous]
  refine h.trans (le_of_eq ?_)
  rw [lineIndexFourier_type112Extend]
  rw [Finset.sum_eq_single type112Pattern (fun σ _ hσ => by
      rw [lp.single_apply_ne _ _ _ hσ]
      exact integral_weight_zero_lp 3 _)
    (fun h => absurd (Finset.mem_univ _) h), lp.single_apply_self]

end

end Manhattan.Paper
