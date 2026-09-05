import Manhattan.Glue.ConcreteRaising
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Equation (45) in line-frequency coordinates

`Manhattan/Glue/ConcreteRaising.lean` proves the exact Walsh coefficient of the
concrete raising operator. Here that coefficient is rewritten in the line
frequencies of `manuscript.tex:743-750`.

A degree-`n` coefficient is indexed by a *pattern* `j : d -> Axis` of line types
together with the transverse integer coordinates `n : d -> Z`. Translating the
environment by `axisVector i` moves a line of type `a` by `axisShift i a`, which
is `0` exactly when `a` is the type of the translation. Consequently the
raising operator is, in the Fourier variables, multiplication by the symbol

  `(1/2) (e^{i p_i} chi_sigma - e^{-i p_i} conj chi_sigma) = i sin(P_i)`,

where `P_i` is the `i`-th coordinate of the total frequency of the *output*.
The appended line has type `i` and therefore contributes nothing to `P_i`; this
is the manuscript's `P'_{j_a} = P_{j_a}` (`manuscript.tex:1197-1198`). Its site
is the origin, so its own Fourier factor is `1` and the symbol does not depend
on the new frequency.

Paper: `manuscript.tex:1176-1200`.
-/

open ComplexConjugate InnerProductSpace MeasureTheory
open scoped BigOperators ComplexConjugate InnerProduct

namespace Manhattan.Glue

noncomputable section

/-! ### Line patterns -/

/-- The transverse displacement of a line of type `a` under the lattice
translation by `axisVector i`. It vanishes exactly when the line is parallel
to the translation. -/
def axisShift (i : Fin 2) (a : Axis) : ℤ := if a = finAxis i then 0 else 1

@[simp] theorem axisShift_self (i : Fin 2) : axisShift i (finAxis i) = 0 := by
  simp [axisShift]

/-- The set of lines with types `j` and transverse coordinates `n`. -/
def patternLines {d : Type} [Fintype d] (j : d → Axis) (n : d → ℤ) :
    Finset LineIndex :=
  Finset.image (fun a => (j a, n a)) Finset.univ

/-- The frequency displacement vector of the translation by `axisVector i`. -/
def patternShift {d : Type} [Fintype d] (i : Fin 2) (j : d → Axis) : d → ℤ :=
  fun a => axisShift i (j a)

theorem mem_patternLines_iff {d : Type} [Fintype d] (j : d → Axis) (n : d → ℤ)
    (l : LineIndex) :
    l ∈ patternLines j n ↔ ∃ a : d, (j a, n a) = l := by
  simp [patternLines]

/-- A criterion for the origin line of type `i` to be a genuinely new index,
i.e. for the manuscript's projection `Pi_{n+1}` to act trivially. -/
theorem originLine_notMem_patternLines {d : Type} [Fintype d] (i : Fin 2)
    (j : d → Axis) (n : d → ℤ) (h : ∀ a : d, j a = finAxis i → n a ≠ 0) :
    originLine i ∉ patternLines j n := by
  rw [mem_patternLines_iff]
  rintro ⟨a, ha⟩
  rw [Prod.ext_iff] at ha
  exact h a ha.1 ha.2

theorem transverseCoordinate_latticeToSite_smul_axisVector (i : Fin 2)
    (sign : ℤ) (a : Axis) :
    transverseCoordinate (latticeToSite (sign • Operator.axisVector i)) a =
      sign * axisShift i a := by
  fin_cases i <;> cases a <;>
    simp [transverseCoordinate, latticeToSite, Operator.axisVector, axisShift,
      finAxis]

/-- Translating the environment translates the line frequencies. -/
theorem translateWalshIndex_patternLines {d : Type} [Fintype d] (i : Fin 2)
    (sign : ℤ) (j : d → Axis) (n : d → ℤ) :
    translateWalshIndex (sign • Operator.axisVector i) (patternLines j n) =
      patternLines j (n + sign • patternShift i j) := by
  classical
  rw [translateWalshIndex, patternLines, patternLines, Finset.map_eq_image,
    Finset.image_image]
  refine Finset.image_congr ?_
  intro a _
  have h := transverseCoordinate_latticeToSite_smul_axisVector i sign (j a)
  simp only [Function.comp_apply, Equiv.coe_toEmbedding, lineTranslation,
    Equiv.coe_fn_mk, Pi.add_apply, Pi.smul_apply, patternShift, smul_eq_mul]
  rw [h]

theorem translateWalshIndex_patternLines_pos {d : Type} [Fintype d] (i : Fin 2)
    (j : d → Axis) (n : d → ℤ) :
    translateWalshIndex (Operator.axisVector i) (patternLines j n) =
      patternLines j (n + patternShift i j) := by
  have h := translateWalshIndex_patternLines i 1 j n
  simpa using h

theorem translateWalshIndex_patternLines_neg {d : Type} [Fintype d] (i : Fin 2)
    (j : d → Axis) (n : d → ℤ) :
    translateWalshIndex (-Operator.axisVector i) (patternLines j n) =
      patternLines j (n - patternShift i j) := by
  have h := translateWalshIndex_patternLines i (-1) j n
  simp only [neg_smul, one_smul, ← sub_eq_add_neg] at h
  exact h

/-! ### Equation (45) in the line frequencies -/

/-- **Lemma 5.1 / equation (45)** in line-frequency coordinates. Raising by
the line of type `i` through the origin is the difference quotient whose Fourier
symbol is `i sin(P_i)`: the coefficient at the frequency index `n` of the output
is built from the coefficients of the input at `n - sigma` and `n + sigma`,
where `sigma` is the displacement vector of the translation by `axisVector i`. -/
theorem inner_walshL2_walshRaiseDir_patternLines {d : Type} [Fintype d]
    (j : d → Axis) (p : Fin 2 → ℝ) (i : Fin 2) (x : WalshL2) (n : d → ℤ)
    (hn : originLine i ∉ patternLines j n) :
    inner ℂ (walshL2 (insert (originLine i) (patternLines j n)))
        (walshRaiseDir p i x) =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * p i) *
            inner ℂ (walshL2 (patternLines j (n - patternShift i j))) x -
          Complex.exp (-Complex.I * p i) *
            inner ℂ (walshL2 (patternLines j (n + patternShift i j))) x) := by
  rw [inner_walshL2_walshRaiseDir, if_pos (Finset.mem_insert_self _ _),
    Finset.erase_insert hn, translateWalshIndex_patternLines_neg,
    translateWalshIndex_patternLines_pos]

theorem originLine_ne (i i' : Fin 2) (h : i ≠ i') :
    originLine i ≠ originLine i' := by
  fin_cases i <;> fin_cases i' <;> simp_all [originLine, finAxis]

/-- The same formula for the full raising operator `D`. Only the direction
whose origin line is appended contributes. -/
theorem inner_walshL2_walshRaise_patternLines {d : Type} [Fintype d]
    (j : d → Axis) (p : Fin 2 → ℝ) (i : Fin 2) (x : WalshL2) (n : d → ℤ)
    (h0 : originLine 0 ∉ patternLines j n)
    (h1 : originLine 1 ∉ patternLines j n) :
    inner ℂ (walshL2 (insert (originLine i) (patternLines j n)))
        (walshRaise p x) =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * p i) *
            inner ℂ (walshL2 (patternLines j (n - patternShift i j))) x -
          Complex.exp (-Complex.I * p i) *
            inner ℂ (walshL2 (patternLines j (n + patternShift i j))) x) := by
  have hn : ∀ i' : Fin 2, originLine i' ∉ patternLines j n := by
    intro i'
    fin_cases i' <;> assumption
  rw [walshRaise, ContinuousLinearMap.sum_apply, inner_sum]
  rw [Finset.sum_eq_single i]
  · exact inner_walshL2_walshRaiseDir_patternLines j p i x n (hn i)
  · intro i' _ hne
    rw [inner_walshL2_walshRaiseDir, if_neg]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact originLine_ne i' i hne h
    · exact hn i' h
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The Fourier symbol `i sin(P_i)` -/

attribute [local instance] Real.fact_zero_lt_one

local instance concreteRaisingUnitAddCircleMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance concreteRaisingUnitAddCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open UnitAddTorus

/-- The Fourier symbol of the direction-`i` raising operator. Written out, it
is `i sin(P_i)`; see `raisingSymbol_apply`. -/
def raisingSymbol (p : Fin 2 → ℝ) (i : Fin 2) {d : Type} [Fintype d]
    (j : d → Axis) : UnitAddTorus d → ℂ := fun t =>
  (2 : ℂ)⁻¹ *
    (Complex.exp (Complex.I * p i) * mFourier (patternShift i j) t -
      Complex.exp (-Complex.I * p i) * mFourier (-patternShift i j) t)

/-- The symbol is exactly the manuscript's `i sin(P_i)`, where `P_i` is the
`i`-th coordinate of the total frequency. Only the frequencies of the lines
*not* parallel to `i` occur, which is the manuscript's `P'_{j_a} = P_{j_a}`. -/
theorem raisingSymbol_apply (p : Fin 2 → ℝ) (i : Fin 2) {d : Type} [Fintype d]
    (j : d → Axis) (θ : d → ℝ) :
    raisingSymbol p i j (fun a => ((θ a : ℝ) : UnitAddCircle)) =
      Complex.I *
        (Real.sin
          (p i + 2 * Real.pi * ∑ a : d, (axisShift i (j a) : ℝ) * θ a) : ℂ) := by
  have hchi : ∀ m : d → ℤ,
      mFourier m (fun a => ((θ a : ℝ) : UnitAddCircle)) =
        Complex.exp (Complex.I *
          ((2 * Real.pi * ∑ a : d, (m a : ℝ) * θ a : ℝ) : ℂ)) := by
    intro m
    have hterm : ∀ a : d,
        (fourier (m a) (((θ a : ℝ)) : UnitAddCircle) : ℂ) =
          Complex.exp (Complex.I * ((2 * Real.pi * ((m a : ℝ) * θ a) : ℝ) : ℂ)) := by
      intro a
      rw [fourier_coe_apply]
      congr 1
      push_cast
      ring
    show (∏ a : d, fourier (m a) ((θ a : ℝ) : UnitAddCircle)) = _
    rw [Finset.prod_congr rfl (fun a (_ : a ∈ Finset.univ) => hterm a),
      ← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum]
  have hs : ∀ m : d → ℤ, (∑ a : d, ((-m) a : ℝ) * θ a) = -(∑ a : d, (m a : ℝ) * θ a) := by
    intro m
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [raisingSymbol, hchi, hchi, hs]
  set u : ℝ := 2 * Real.pi * ∑ a : d, ((patternShift i j) a : ℝ) * θ a with hu
  have hneg : (2 * Real.pi * -(∑ a : d, ((patternShift i j) a : ℝ) * θ a) : ℝ) = -u := by
    rw [hu]; ring
  rw [hneg]
  have h1 : Complex.exp (Complex.I * (p i : ℂ)) *
      Complex.exp (Complex.I * ((u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((p i + u : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (-Complex.I * (p i : ℂ)) *
      Complex.exp (Complex.I * ((-u : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((p i + u : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum : p i + u =
      p i + 2 * Real.pi * ∑ a : d, (axisShift i (j a) : ℝ) * θ a := by
    rw [hu]
    simp only [patternShift]
  rw [h1, h2, half_exp_I_sub_exp_neg_I (p i + u), hsum]

/-! ### The raising operator is multiplication by the symbol -/

theorem mFourierCoeff_index_sub {d : Type} [Fintype d]
    (F : UnitAddTorus d → ℂ) (m n : d → ℤ) :
    mFourierCoeff F (n - m) = mFourierCoeff (fun t => mFourier m t * F t) n := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mFourier_add]
  congr 2
  rw [sub_eq_add_neg, neg_add, neg_neg]

theorem mFourierCoeff_index_add {d : Type} [Fintype d]
    (F : UnitAddTorus d → ℂ) (m n : d → ℤ) :
    mFourierCoeff F (n + m) = mFourierCoeff (fun t => mFourier (-m) t * F t) n := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mFourier_add]
  congr 2
  rw [neg_add]

private theorem norm_mFourier_apply_le {d : Type} [Fintype d] (m : d → ℤ)
    (t : UnitAddTorus d) : ‖mFourier m t‖ ≤ 1 := by
  simpa only [mFourier_norm] using (mFourier m).norm_coe_le_norm t

private theorem integrable_mFourier_mul {d : Type} [Fintype d]
    {F : UnitAddTorus d → ℂ} (hF : Integrable F volume) (m : d → ℤ) :
    Integrable (fun t => mFourier m t * F t) volume :=
  hF.bdd_mul (c := 1) (mFourier m).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_mFourier_apply_le m))

/-- Multiplying the line-frequency coefficient by the symbol `i sin(P_i)` is the
same as forming the phase difference of the two shifted coefficients. -/
theorem mFourierCoeff_raisingSymbol_mul {d : Type} [Fintype d]
    (p : Fin 2 → ℝ) (i : Fin 2) (j : d → Axis) (F : UnitAddTorus d → ℂ)
    (hF : Integrable F volume) (n : d → ℤ) :
    mFourierCoeff (fun t => raisingSymbol p i j t * F t) n =
      (2 : ℂ)⁻¹ *
        (Complex.exp (Complex.I * p i) *
            mFourierCoeff F (n - patternShift i j) -
          Complex.exp (-Complex.I * p i) *
            mFourierCoeff F (n + patternShift i j)) := by
  have hi1 : Integrable
      (fun t => mFourier (-n) t *
        (mFourier (patternShift i j) t * F t)) volume :=
    integrable_mFourier_mul (integrable_mFourier_mul hF _) _
  have hi2 : Integrable
      (fun t => mFourier (-n) t *
        (mFourier (-patternShift i j) t * F t)) volume :=
    integrable_mFourier_mul (integrable_mFourier_mul hF _) _
  rw [mFourierCoeff_index_sub, mFourierCoeff_index_add]
  show (∫ t, mFourier (-n) t • (raisingSymbol p i j t * F t)) = _
  rw [show (∫ t, mFourier (-n) t • (raisingSymbol p i j t * F t)) =
      ∫ t, (((2 : ℂ)⁻¹ * Complex.exp (Complex.I * p i)) *
            (mFourier (-n) t * (mFourier (patternShift i j) t * F t)) -
          ((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) *
            (mFourier (-n) t * (mFourier (-patternShift i j) t * F t))) from
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [raisingSymbol, smul_eq_mul]
      ring)]
  rw [integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul]
  show _ = (2 : ℂ)⁻¹ *
    (Complex.exp (Complex.I * p i) *
        (∫ t, mFourier (-n) t • (mFourier (patternShift i j) t * F t)) -
      Complex.exp (-Complex.I * p i) *
        (∫ t, mFourier (-n) t • (mFourier (-patternShift i j) t * F t)))
  simp only [smul_eq_mul]
  ring

/-! ### Equation (45) as a Fourier multiplier -/

/-- **Lemma 5.1 / equation (45), frequency form.** If the line-frequency
coefficient of `x` along the pattern `j` is the Fourier coefficient sequence of
`F`, then the coefficient of the raised vector at the index set obtained by
appending the origin line of type `i` is the Fourier coefficient sequence of
`i sin(P_i) F`. -/
theorem inner_walshL2_walshRaiseDir_mFourierCoeff {d : Type} [Fintype d]
    (j : d → Axis) (p : Fin 2 → ℝ) (i : Fin 2) (x : WalshL2)
    (F : UnitAddTorus d → ℂ) (hF : Integrable F volume)
    (hFx : ∀ m : d → ℤ,
      inner ℂ (walshL2 (patternLines j m)) x = mFourierCoeff F m)
    (n : d → ℤ) (hn : originLine i ∉ patternLines j n) :
    inner ℂ (walshL2 (insert (originLine i) (patternLines j n)))
        (walshRaiseDir p i x) =
      mFourierCoeff (fun t => raisingSymbol p i j t * F t) n := by
  rw [inner_walshL2_walshRaiseDir_patternLines j p i x n hn, hFx, hFx,
    mFourierCoeff_raisingSymbol_mul p i j F hF n]

/-- The same statement for the full raising operator `D`. -/
theorem inner_walshL2_walshRaise_mFourierCoeff {d : Type} [Fintype d]
    (j : d → Axis) (p : Fin 2 → ℝ) (i : Fin 2) (x : WalshL2)
    (F : UnitAddTorus d → ℂ) (hF : Integrable F volume)
    (hFx : ∀ m : d → ℤ,
      inner ℂ (walshL2 (patternLines j m)) x = mFourierCoeff F m)
    (n : d → ℤ) (h0 : originLine 0 ∉ patternLines j n)
    (h1 : originLine 1 ∉ patternLines j n) :
    inner ℂ (walshL2 (insert (originLine i) (patternLines j n)))
        (walshRaise p x) =
      mFourierCoeff (fun t => raisingSymbol p i j t * F t) n := by
  rw [inner_walshL2_walshRaise_patternLines j p i x n h0 h1, hFx, hFx,
    mFourierCoeff_raisingSymbol_mul p i j F hF n]

end

end Manhattan.Glue
