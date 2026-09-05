import Manhattan.Glue.OrderedRaising
import Manhattan.Glue.ProjectionDischargeTorus

/-!
# The degree-four raising energy bound

Step 5 of the plan of : the operator
half of Lemma 5.2, for a *general* degree-three coefficient.

Paper: `manuscript.tex:1196-1205` (Lemma 5.2), `manuscript.tex:1257-1272`
(its proof), `manuscript.tex:860-867` (equation (22)).
-/

noncomputable section

open MeasureTheory

namespace Manhattan.Glue

open UnitAddTorus

/-! ### The multiplier weight is continuous

`symbolWeight` is written through `torusLift = Quotient.out`, which carries no
measurability of its own.  It is nevertheless a continuous function of the
torus point, because `lineSymbol_eq` identifies `theta` of the total frequency
with the real part of a finite combination of characters. -/

theorem symbolWeight_eq_sub_re (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    symbolWeight n lam p σ t = lam - (lineSymbol n p σ t).re := by
  rw [lineSymbol_eq, symbolWeight]
  simp

theorem continuous_lineSymbol (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    Continuous (lineSymbol n p σ) := by
  unfold lineSymbol
  refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
  exact ((continuous_const.mul (mFourier _).continuous).add
    (continuous_const.mul (mFourier _).continuous)).sub continuous_const

theorem continuous_symbolWeight (n : ℕ) (lam : ℝ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    Continuous (symbolWeight n lam p σ) := by
  have h : symbolWeight n lam p σ = fun t => lam - (lineSymbol n p σ t).re :=
    funext fun t => symbolWeight_eq_sub_re n lam p σ t
  rw [h]
  exact continuous_const.sub (Complex.continuous_re.comp (continuous_lineSymbol n p σ))

theorem continuous_inv_symbolWeight (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (σ : Fin n → Axis) :
    Continuous fun t => (symbolWeight n lam p σ t)⁻¹ :=
  (continuous_symbolWeight n lam p σ).inv₀ fun t => (symbolWeight_pos n hlam p σ t).ne'

/-! ### The one-variable resolvent integral on the frequency circle

Equation (22), transported from the paper's normalized torus to the unit
additive circle and in the shifted form in which the appended line's variable
occurs.  This section deliberately keeps Mathlib's own `MeasureSpace
UnitAddCircle` instance, so that `AddCircle.integral_haarAddCircle` and
`AddCircle.integral_preimage` mean what they say; the statement names
`AddCircle.haarAddCircle` explicitly and is therefore instance-independent. -/

section Resolvent

attribute [local instance] Real.fact_zero_lt_one

theorem integral_haar_inv_dispersion {mu : ℝ} (hmu : 0 < mu) (c : ℝ) :
    ∫ x : UnitAddCircle,
        (mu + Estimates.dispersion (c + 2 * Real.pi * torusLift x))⁻¹
        ∂AddCircle.haarAddCircle
      = (Real.sqrt (mu * (mu + 2)))⁻¹ := by
  classical
  set f : ℝ → ℝ := fun r => (mu + Estimates.dispersion r)⁻¹ with hf
  set G : UnitAddCircle → ℝ := fun x =>
    (mu + 1 - (Complex.exp (Complex.I * (c : ℂ)) * fourier 1 x).re)⁻¹ with hGdef
  have hGcoe : ∀ θ : ℝ, G ((θ : ℝ) : UnitAddCircle) = f (c + 2 * Real.pi * θ) := by
    intro θ
    have hre : (Complex.exp (Complex.I * (c : ℂ)) *
        fourier 1 ((θ : ℝ) : UnitAddCircle)).re = Real.cos (c + 2 * Real.pi * θ) := by
      rw [fourier_coe_apply, ← Complex.exp_add]
      have harg : Complex.I * (c : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (θ : ℂ) / ((1 : ℝ) : ℂ)
          = ((c + 2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.exp_ofReal_mul_I_re]
    rw [hGdef]
    simp only [hre, hf, Estimates.dispersion]
    ring_nf
  have hEq : (fun x : UnitAddCircle =>
      (mu + Estimates.dispersion (c + 2 * Real.pi * torusLift x))⁻¹) = G := by
    funext x
    rw [← torusLift_coe x, hGcoe (torusLift x), torusLift_coe]
  rw [hEq, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (1 : ℝ) (-(1 / 2)) G]
  have hbound : (-(1 / 2) : ℝ) ≤ -(1 / 2) + 1 := by norm_num
  have hstep : (∫ a in Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1), G ((a : ℝ) : UnitAddCircle))
      = ∫ a in (-(1 / 2) : ℝ)..(-(1 / 2) + 1), f (c + 2 * Real.pi * a) := by
    rw [intervalIntegral.integral_of_le hbound]
    exact setIntegral_congr_fun measurableSet_Ioc fun a _ => hGcoe a
  rw [hstep]
  have htwopi : (2 * Real.pi) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (f := fun y => f (c + y)) htwopi]
  have hleft : ((2 * Real.pi) * (-(1 / 2) : ℝ)) = -Real.pi := by ring
  have hright : ((2 * Real.pi) * ((-(1 / 2) : ℝ) + 1)) = Real.pi := by ring
  rw [hleft, hright]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hper : Function.Periodic f (2 * Real.pi) := by
    intro r
    simp only [hf, Estimates.dispersion, Real.cos_add_two_pi]
  have hshape : Estimates.torusIntegral (fun y : ℝ => f (y + c))
      = (2 * Real.pi)⁻¹ • ∫ y in (-Real.pi)..Real.pi, f (c + y) := by
    rw [Estimates.torusIntegral, Estimates.torus, ← intervalIntegral.integral_of_le hpi]
    congr 1
    refine intervalIntegral.integral_congr ?_
    intro y _
    show f (y + c) = f (c + y)
    rw [add_comm]
  rw [inv_one, one_smul, ← hshape, torusIntegral_comp_add_right hper c]
  exact Estimates.lineResolventIdentity_proved mu hmu

end Resolvent

/-! ### The slot integral of the degree-four weight

Inserting the origin line of type `i` in slot `r` leaves the `i`-th coordinate
of the total frequency untouched and lets the other coordinate run over the
circle; this is the manuscript's "adding a sign of type `i` leaves `P_i` fixed
and lets `P_{3-i}` range over `T`". -/

/-- The index of the coordinate transverse to `i`. -/
def otherAxisIndex (i : Fin 2) : Fin 2 := 1 - i

theorem otherAxisIndex_ne (i : Fin 2) : otherAxisIndex i ≠ i := by
  fin_cases i <;> decide

theorem theta_eq_add (P : Fin 2 → ℝ) (i : Fin 2) :
    Estimates.theta P
      = Estimates.dispersion (P i) + Estimates.dispersion (P (otherAxisIndex i)) := by
  fin_cases i
  · simp [Estimates.theta, otherAxisIndex]
  · simp [Estimates.theta, otherAxisIndex, add_comm]

theorem axisShift_finAxis_self (i : Fin 2) : axisShift i (finAxis i) = 0 := by
  simp

theorem axisShift_finAxis_other (i : Fin 2) :
    axisShift (otherAxisIndex i) (finAxis i) = 1 := by
  fin_cases i <;> decide

theorem lineShiftVector_eq_axisShift (n : ℕ) (k : Fin 2) (σ : Fin n → Axis) (a : Fin n) :
    lineShiftVector n (Operator.axisVector k) σ a = axisShift k (σ a) := by
  rw [lineShiftVector_axisVector, axisShift]

theorem totalFrequency_insertNth {n : ℕ} (p : Fin 2 → ℝ) (i : Fin 2) (r : Fin (n + 1))
    (σ : Fin n → Axis) (x : UnitAddCircle) (s : UnitAddTorus (Fin n)) (k : Fin 2) :
    totalFrequency (n + 1) p (Fin.insertNth r (finAxis i) σ)
        (Fin.insertNth r x s) k
      = totalFrequency n p σ s k
        + 2 * Real.pi * ((axisShift k (finAxis i) : ℤ) : ℝ) * torusLift x := by
  simp only [totalFrequency, lineFrequency, lineShiftVector_eq_axisShift]
  rw [Fin.sum_univ_succAbove _ r]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

theorem symbolWeight_insertNth {n : ℕ} (lam : ℝ) (p : Fin 2 → ℝ) (i : Fin 2)
    (r : Fin (n + 1)) (σ : Fin n → Axis) (x : UnitAddCircle) (s : UnitAddTorus (Fin n)) :
    symbolWeight (n + 1) lam p (Fin.insertNth r (finAxis i) σ) (Fin.insertNth r x s)
      = (lam + Estimates.dispersion (totalFrequency n p σ s i))
        + Estimates.dispersion
            (totalFrequency n p σ s (otherAxisIndex i) + 2 * Real.pi * torusLift x) := by
  rw [symbolWeight, theta_eq_add _ i,
    totalFrequency_insertNth p i r σ x s i,
    totalFrequency_insertNth p i r σ x s (otherAxisIndex i),
    axisShift_finAxis_self, axisShift_finAxis_other]
  push_cast
  ring_nf

section SlotIntegral

attribute [local instance] Real.fact_zero_lt_one

/-- **The slot integral.**  Integrating the inverse degree-four weight over the
appended line's frequency gives the closed form of equation (22) at the mass
`lambda + d(P_i)`. -/
theorem integral_haar_inv_symbolWeight_insertNth {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (i : Fin 2) (r : Fin (n + 1)) (σ : Fin n → Axis)
    (s : UnitAddTorus (Fin n)) :
    ∫ x : UnitAddCircle,
        (symbolWeight (n + 1) lam p (Fin.insertNth r (finAxis i) σ)
          (Fin.insertNth r x s))⁻¹ ∂AddCircle.haarAddCircle
      = (Real.sqrt ((lam + Estimates.dispersion (totalFrequency n p σ s i)) *
          ((lam + Estimates.dispersion (totalFrequency n p σ s i)) + 2)))⁻¹ := by
  have hmu : 0 < lam + Estimates.dispersion (totalFrequency n p σ s i) := by
    have := Estimates.dispersion_nonneg (totalFrequency n p σ s i)
    linarith
  rw [show (fun x : UnitAddCircle =>
      (symbolWeight (n + 1) lam p (Fin.insertNth r (finAxis i) σ)
        (Fin.insertNth r x s))⁻¹)
      = fun x : UnitAddCircle =>
        ((lam + Estimates.dispersion (totalFrequency n p σ s i)) +
          Estimates.dispersion (totalFrequency n p σ s (otherAxisIndex i) +
            2 * Real.pi * torusLift x))⁻¹ from
    funext fun x => by rw [symbolWeight_insertNth]]
  exact integral_haar_inv_dispersion hmu _

end SlotIntegral

/-! ### The scalar step of the manuscript's proof

`sin^2(P_i)(\lambda+d(P_i))^{-1/2} \leq 2\sqrt2|\sin(P_i/2)|`, absorbed into the
multiplier `M` with the universal constant `\kappa = 40`. -/

theorem sin_sq_div_sqrt_le_multiplier_div {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) (i : Fin 2) :
    Real.sin (P i) ^ 2 / Real.sqrt (q.lambda + Estimates.dispersion (P i))
      ≤ Estimates.multiplier kappa q P / 8 := by
  have hcases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  have hcore := Estimates.fourEstimateCore_le_multiplier_of_twelve_le hkappa hlam P
  have hw : 0 ≤ Estimates.hWeight q P := by
    have := Estimates.theta_nonneg P
    simp only [Estimates.hWeight]
    linarith
  have h0 : 0 ≤ Real.sin (P 0) ^ 2 / Real.sqrt (q.lambda + Estimates.dispersion (P 0)) := by
    positivity
  have h1 : 0 ≤ Real.sin (P 1) ^ 2 / Real.sqrt (q.lambda + Estimates.dispersion (P 1)) := by
    positivity
  simp only [Estimates.fourEstimateCore] at hcore
  rcases hcases i with rfl | rfl
  · linarith
  · linarith

theorem inv_sqrt_slot_mul_sin_sq_le {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlam : 0 < q.lambda)
    (P : Fin 2 → ℝ) (i : Fin 2) :
    (Real.sqrt ((q.lambda + Estimates.dispersion (P i)) *
        ((q.lambda + Estimates.dispersion (P i)) + 2)))⁻¹ * Real.sin (P i) ^ 2
      ≤ Estimates.multiplier kappa q P / 8 := by
  have hd := Estimates.dispersion_nonneg (P i)
  have hmupos : 0 < q.lambda + Estimates.dispersion (P i) := by linarith
  have hsq : 0 < Real.sqrt (q.lambda + Estimates.dispersion (P i)) := Real.sqrt_pos.2 hmupos
  have hle : Real.sqrt (q.lambda + Estimates.dispersion (P i))
      ≤ Real.sqrt ((q.lambda + Estimates.dispersion (P i)) *
        ((q.lambda + Estimates.dispersion (P i)) + 2)) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith
  have hinv : (Real.sqrt ((q.lambda + Estimates.dispersion (P i)) *
      ((q.lambda + Estimates.dispersion (P i)) + 2)))⁻¹
      ≤ (Real.sqrt (q.lambda + Estimates.dispersion (P i)))⁻¹ := inv_anti₀ hsq hle
  have hstep : (Real.sqrt ((q.lambda + Estimates.dispersion (P i)) *
      ((q.lambda + Estimates.dispersion (P i)) + 2)))⁻¹ * Real.sin (P i) ^ 2
      ≤ Real.sin (P i) ^ 2 / Real.sqrt (q.lambda + Estimates.dispersion (P i)) := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
  exact hstep.trans (sin_sq_div_sqrt_le_multiplier_div hkappa hlam.le P i)

/-! ### Inserting a line in a fixed slot

The ordered picture with the appended origin line placed in a *fixed* slot.
This is the manuscript's `\widetilde D_n`, whose `n+1` terms are indexed by the
slot the new line occupies. -/

section FixedSlot

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] orderedInverseUnitAddCircleMeasureSpace
attribute [local instance] orderedInverseUnitAddCircleIsProbabilityMeasure

open UnitAddTorus

/-- Deleting the coordinate in slot `r` is measure preserving. -/
theorem measurePreserving_removeNthTorus (n : ℕ) (r : Fin (n + 1)) :
    MeasurePreserving (fun t : UnitAddTorus (Fin (n + 1)) => Fin.removeNth r t)
      (LineTorusMeasure (n + 1)) (LineTorusMeasure n) := by
  have h := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) r
  have h2 : MeasurePreserving (Prod.snd : UnitAddCircle × UnitAddTorus (Fin n) → _)
      ((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) (LineTorusMeasure n) :=
    ⟨measurable_snd, Measure.snd_prod⟩
  exact h2.comp h

/-- Inserting a coordinate in slot `r` is measure preserving. -/
theorem measurePreserving_insertNthTorus (n : ℕ) (r : Fin (n + 1)) :
    MeasurePreserving
      (fun z : UnitAddCircle × UnitAddTorus (Fin n) => Fin.insertNth r z.1 z.2)
      ((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) (LineTorusMeasure (n + 1)) :=
  (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (AddCircle.haarAddCircle : Measure UnitAddCircle)) r).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r)

/-- Reading an `L²` function of the remaining line frequencies as an `L²`
function of all of them: the appended variable does not occur. -/
def torusRemove (n : ℕ) (r : Fin (n + 1)) :
    Lp ℂ 2 (LineTorusMeasure n) →ₗᵢ[ℂ] Lp ℂ 2 (LineTorusMeasure (n + 1)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : UnitAddTorus (Fin (n + 1)) => Fin.removeNth r t)
    (measurePreserving_removeNthTorus n r)

theorem coeFn_torusRemove (n : ℕ) (r : Fin (n + 1)) (F : Lp ℂ 2 (LineTorusMeasure n)) :
    (torusRemove n r F : UnitAddTorus (Fin (n + 1)) → ℂ)
      =ᵐ[LineTorusMeasure (n + 1)] fun t => (F : UnitAddTorus (Fin n) → ℂ) (Fin.removeNth r t) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_removeNthTorus n r)

/-- The character of the enlarged index with a zero in the appended slot is the
character of the original index, read after deleting that slot. -/
theorem torusRemove_mFourierLp (n : ℕ) (r : Fin (n + 1)) (k : Fin n → ℤ) :
    torusRemove n r (mFourierLp 2 k)
      = mFourierLp 2 (Fin.insertNth (α := fun _ => ℤ) r (0 : ℤ) k) := by
  apply Lp.ext
  have h1 := coeFn_torusRemove n r (mFourierLp 2 k)
  have h2 : (fun t : UnitAddTorus (Fin (n + 1)) =>
      (mFourierLp 2 k : UnitAddTorus (Fin n) → ℂ) (Fin.removeNth r t))
      =ᵐ[LineTorusMeasure (n + 1)]
      fun t => mFourier k (Fin.removeNth r t) :=
    (measurePreserving_removeNthTorus n r).quasiMeasurePreserving.ae_eq_comp
      (coeFn_mFourierLp (d := Fin n) 2 k)
  have h3 := coeFn_mFourierLp (d := Fin (n + 1)) 2
    (Fin.insertNth (α := fun _ => ℤ) r (0 : ℤ) k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  rw [ht1, ht2, ht3, mFourier_insertNth_zero]

/-- Evaluation of a line-frequency vector in one axis sector. -/
def freqEval (n : ℕ) (σ : Fin n → Axis) :
    LineFreqL2 n →L[ℂ] Lp ℂ 2 (LineTorusMeasure n) :=
  LinearMap.mkContinuous
    { toFun := fun v => v σ
      map_add' := fun v w => by rw [lp.coeFn_add]; rfl
      map_smul' := fun a v => by rw [lp.coeFn_smul]; rfl }
    1 <| by
      intro v
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num) v σ

@[simp] theorem freqEval_apply (n : ℕ) (σ : Fin n → Axis) (v : LineFreqL2 n) :
    freqEval n σ v = v σ := rfl

/-- Placing the origin line of type `i` in slot `r` of an ordered tuple. -/
def insertLineIndex (n : ℕ) (r : Fin (n + 1)) (i : Fin 2) (t : Fin n → LineIndex) :
    Fin (n + 1) → LineIndex :=
  Fin.insertNth r (Manhattan.originLine i) t

theorem insertLineIndex_injective (n : ℕ) (r : Fin (n + 1)) (i : Fin 2) :
    Function.Injective (insertLineIndex n r i) := by
  intro t u h
  have := congrArg (fun v => Fin.removeNth r v) h
  simpa [insertLineIndex, Fin.removeNth_insertNth] using this

/-- **The fixed-slot raising map.**  Extension by zero along the placement of
the origin line of type `i` in slot `r`. -/
def insertLine (n : ℕ) (r : Fin (n + 1)) (i : Fin 2) :
    OrderedCoefficient n →L[ℂ] OrderedCoefficient (n + 1) :=
  (l2Extend (insertLineIndex n r i) (insertLineIndex_injective n r i)).toContinuousLinearMap

@[simp] theorem insertLine_single (n : ℕ) (r : Fin (n + 1)) (i : Fin 2)
    (t : Fin n → LineIndex) (a : ℂ) :
    insertLine n r i (lp.single 2 t a) = lp.single 2 (insertLineIndex n r i t) a :=
  l2Extend_single _ (insertLineIndex_injective n r i) _ _

theorem insertLine_apply_image (n : ℕ) (r : Fin (n + 1)) (i : Fin 2)
    (c : OrderedCoefficient n) (t : Fin n → LineIndex) :
    insertLine n r i c (insertLineIndex n r i t) = c t :=
  l2Extend_apply_image _ (insertLineIndex_injective n r i) c t

theorem insertLine_apply_of_notMem (n : ℕ) (r : Fin (n + 1)) (i : Fin 2)
    (c : OrderedCoefficient n) (u : Fin (n + 1) → LineIndex)
    (hu : u r ≠ Manhattan.originLine i) :
    insertLine n r i c u = 0 := by
  refine l2Extend_apply_of_notMem _ (insertLineIndex_injective n r i) c u ?_
  intro t hc
  exact hu (by rw [← hc]; simp [insertLineIndex])

/-- **The line-frequency coefficient of the fixed-slot raising map.**  It lives
in the single axis sector whose slot `r` entry is the appended line's axis, and
there it is the degree-`n` coefficient read after deleting that slot: constant
in the appended line's torus variable. -/
theorem orderedFourier_insertLine_apply (n : ℕ) (r : Fin (n + 1)) (i : Fin 2)
    (h : OrderedCoefficient n) (σ : Fin (n + 1) → Axis) :
    (orderedFourier (n + 1) (insertLine n r i h)) σ
      = if σ r = finAxis i then
          torusRemove n r ((orderedFourier n h) (Fin.removeNth r σ)) else 0 := by
  classical
  have hpat : ∀ t : Fin n → LineIndex,
      tuplePattern (insertLineIndex n r i t)
        = Fin.insertNth (α := fun _ => Axis) r (finAxis i) (tuplePattern t) := by
    intro t
    exact tuplePattern_insertNth r (Manhattan.originLine i) t
  have hcoord : ∀ t : Fin n → LineIndex,
      tupleCoord (insertLineIndex n r i t)
        = Fin.insertNth (α := fun _ => ℤ) r (0 : ℤ) (tupleCoord t) := by
    intro t
    exact tupleCoord_insertNth r (Manhattan.originLine i) t
  have hsingle : ∀ t : Fin n → LineIndex,
      (orderedFourier (n + 1) (insertLine n r i (lp.single 2 t (1 : ℂ)))) σ
        = if σ = tuplePattern (insertLineIndex n r i t) then
            mFourierLp 2 (tupleCoord (insertLineIndex n r i t)) else 0 := by
    intro t
    rw [insertLine_single, orderedFourier_single, one_smul, orderedFreqFamily]
    by_cases hσt : σ = tuplePattern (insertLineIndex n r i t)
    · rw [if_pos hσt, hσt, lp.single_apply_self]
    · rw [if_neg hσt, lp.single_apply_ne _ _ _ hσt]
  by_cases hσ : σ r = finAxis i
  · rw [if_pos hσ]
    refine l2_ext'
      ((freqEval (n + 1) σ).comp
        ((orderedFourier (n + 1)).toContinuousLinearMap.comp (insertLine n r i)))
      (((torusRemove n r).toContinuousLinearMap).comp
        ((freqEval n (Fin.removeNth r σ)).comp
          (orderedFourier n).toContinuousLinearMap)) ?_ h
    intro t
    change (orderedFourier (n + 1) (insertLine n r i (lp.single 2 t (1 : ℂ)))) σ
      = torusRemove n r ((orderedFourier n (lp.single 2 t (1 : ℂ))) (Fin.removeNth r σ))
    rw [hsingle t, orderedFourier_single, one_smul, orderedFreqFamily]
    by_cases hrt : Fin.removeNth r σ = tuplePattern t
    · have hσeq : σ = tuplePattern (insertLineIndex n r i t) := by
        rw [hpat t, ← hrt, ← hσ]
        exact (Fin.insertNth_self_removeNth r σ).symm
      rw [if_pos hσeq, hrt, lp.single_apply_self, hcoord t, torusRemove_mFourierLp]
    · have hσne : σ ≠ tuplePattern (insertLineIndex n r i t) := by
        intro hc
        apply hrt
        rw [hc, hpat t, Fin.removeNth_insertNth]
      rw [if_neg hσne, lp.single_apply_ne _ _ _ hrt, map_zero]
  · rw [if_neg hσ]
    refine l2_ext'
      ((freqEval (n + 1) σ).comp
        ((orderedFourier (n + 1)).toContinuousLinearMap.comp (insertLine n r i)))
      0 ?_ h
    intro t
    change (orderedFourier (n + 1) (insertLine n r i (lp.single 2 t (1 : ℂ)))) σ = 0
    rw [hsingle t, if_neg]
    intro hc
    apply hσ
    rw [hc, hpat t, Fin.insertNth_apply_same]

/-! ### Fubini in the appended line's frequency -/

theorem measurePreserving_sndTorus (n : ℕ) :
    MeasurePreserving (Prod.snd : UnitAddCircle × UnitAddTorus (Fin n) → UnitAddTorus (Fin n))
      ((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) (LineTorusMeasure n) :=
  ⟨measurable_snd, Measure.snd_prod⟩

theorem measurableEmbedding_insertNthTorus (n : ℕ) (r : Fin (n + 1)) :
    MeasurableEmbedding
      (fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
        Fin.insertNth (α := fun _ => UnitAddCircle) r z.1 z.2) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) r).symm.measurableEmbedding

theorem integrable_norm_sq_lp (n : ℕ) (F : Lp ℂ 2 (LineTorusMeasure n)) :
    Integrable (fun t => ‖(F : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2) (LineTorusMeasure n) :=
  (Lp.memLp F).norm.integrable_sq

theorem integral_weight_zero_lp (n : ℕ) (w : UnitAddTorus (Fin n) → ℝ) :
    ∫ t, w t * ‖((0 : Lp ℂ 2 (LineTorusMeasure n)) : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure n) = 0 := by
  have hzero : (∫ t, w t *
      ‖((0 : Lp ℂ 2 (LineTorusMeasure n)) : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure n)) = ∫ _t, (0 : ℝ) ∂(LineTorusMeasure n) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (LineTorusMeasure n)] with t ht
    rw [ht]
    simp
  rw [hzero, integral_zero]

/-- **Fubini in the appended slot.**  The degree-`(n+1)` energy of a function
that does not depend on the appended line's variable is the degree-`n` energy
against the slot integral of the weight. -/
theorem integral_insertNth_energy (n : ℕ) {lam : ℝ} (hlam : 0 < lam) (p : Fin 2 → ℝ)
    (i : Fin 2) (r : Fin (n + 1)) (σ : Fin n → Axis) (F : Lp ℂ 2 (LineTorusMeasure n)) :
    ∫ t, (symbolWeight (n + 1) lam p (Fin.insertNth r (finAxis i) σ) t)⁻¹ *
        ‖(torusRemove n r F : UnitAddTorus (Fin (n + 1)) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure (n + 1))
      = ∫ s, (Real.sqrt ((lam + Estimates.dispersion (totalFrequency n p σ s i)) *
            ((lam + Estimates.dispersion (totalFrequency n p σ s i)) + 2)))⁻¹ *
          ‖(F : UnitAddTorus (Fin n) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure n) := by
  set w : UnitAddTorus (Fin (n + 1)) → ℝ := fun t =>
    (symbolWeight (n + 1) lam p (Fin.insertNth r (finAxis i) σ) t)⁻¹ with hw
  have hwcont : Continuous w := continuous_inv_symbolWeight (n + 1) hlam p _
  have hwbound : ∀ t, ‖w t‖ ≤ lam⁻¹ := by
    intro t
    have hpos := symbolWeight_pos (n + 1) hlam p (Fin.insertNth r (finAxis i) σ) t
    have hge := symbolWeight_ge (n + 1) lam p (Fin.insertNth r (finAxis i) σ) t
    rw [hw, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_anti₀ hlam hge
  have step1 : (∫ t, w t * ‖(torusRemove n r F : UnitAddTorus (Fin (n + 1)) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure (n + 1)))
      = ∫ t, w t * ‖(F : UnitAddTorus (Fin n) → ℂ) (Fin.removeNth r t)‖ ^ 2
        ∂(LineTorusMeasure (n + 1)) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_torusRemove n r F] with t ht
    rw [ht]
  have step2 : (∫ t, w t * ‖(F : UnitAddTorus (Fin n) → ℂ) (Fin.removeNth r t)‖ ^ 2
        ∂(LineTorusMeasure (n + 1)))
      = ∫ z, w (Fin.insertNth r z.1 z.2) * ‖(F : UnitAddTorus (Fin n) → ℂ) z.2‖ ^ 2
        ∂((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) := by
    rw [← (measurePreserving_insertNthTorus n r).integral_comp
      (measurableEmbedding_insertNthTorus n r)
      (fun t => w t * ‖(F : UnitAddTorus (Fin n) → ℂ) (Fin.removeNth r t)‖ ^ 2)]
    simp only [Fin.removeNth_insertNth]
  have hInt : Integrable
      (fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
        w (Fin.insertNth r z.1 z.2) * ‖(F : UnitAddTorus (Fin n) → ℂ) z.2‖ ^ 2)
      ((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) := by
    have hg : Integrable
        (fun z : UnitAddCircle × UnitAddTorus (Fin n) =>
          ‖(F : UnitAddTorus (Fin n) → ℂ) z.2‖ ^ 2)
        ((AddCircle.haarAddCircle).prod (LineTorusMeasure n)) :=
      (measurePreserving_sndTorus n).integrable_comp_of_integrable (integrable_norm_sq_lp n F)
    refine hg.bdd_mul (c := lam⁻¹) ?_ ?_
    · exact (hwcont.measurable.comp
        (measurableEmbedding_insertNthTorus n r).measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => hwbound _
  rw [step1, step2, integral_prod_symm _ hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only []
  rw [integral_mul_const]
  congr 1
  exact integral_haar_inv_symbolWeight_insertNth hlam p i r σ s

/-- **The energy of the fixed-slot raising map.**  Summing over axis patterns
collapses to the patterns whose slot `r` entry is the appended line's axis, and
Fubini in that slot leaves the degree-`n` energy against the line integral of
equation (22). -/
theorem tsum_integral_inv_symbolWeight_insertLine (n : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (p : Fin 2 → ℝ) (i : Fin 2) (r : Fin (n + 1)) (h : OrderedCoefficient n) :
    (∑' σ : Fin (n + 1) → Axis, ∫ t, (symbolWeight (n + 1) lam p σ t)⁻¹ *
        ‖((orderedFourier (n + 1) (insertLine n r i h)) σ) t‖ ^ 2
        ∂(LineTorusMeasure (n + 1)))
      = ∑' σ : Fin n → Axis, ∫ s,
          (Real.sqrt ((lam + Estimates.dispersion (totalFrequency n p σ s i)) *
            ((lam + Estimates.dispersion (totalFrequency n p σ s i)) + 2)))⁻¹ *
          ‖((orderedFourier n h) σ) s‖ ^ 2 ∂(LineTorusMeasure n) := by
  classical
  set G : (Fin (n + 1) → Axis) → ℝ := fun σ =>
    ∫ t, (symbolWeight (n + 1) lam p σ t)⁻¹ *
      ‖((orderedFourier (n + 1) (insertLine n r i h)) σ) t‖ ^ 2
      ∂(LineTorusMeasure (n + 1)) with hG
  rw [tsum_fintype, tsum_fintype]
  have hreindex : (∑ z : Axis × (Fin n → Axis),
      G (Fin.insertNth (α := fun _ => Axis) r z.1 z.2)) = ∑ σ : Fin (n + 1) → Axis, G σ :=
    Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Axis) r) _ _ fun z => rfl
  rw [← hreindex, Fintype.sum_prod_type]
  have hzero : ∀ a : Axis, a ≠ finAxis i →
      (∑ σ : Fin n → Axis, G (Fin.insertNth (α := fun _ => Axis) r a σ)) = 0 := by
    intro a ha
    refine Finset.sum_eq_zero fun σ _ => ?_
    have hσr : (Fin.insertNth (α := fun _ => Axis) r a σ) r = a := Fin.insertNth_apply_same _ _ _
    have hzero' : (orderedFourier (n + 1) (insertLine n r i h))
        (Fin.insertNth (α := fun _ => Axis) r a σ) = 0 := by
      rw [orderedFourier_insertLine_apply, if_neg]
      rw [hσr]
      exact ha
    rw [hG]
    simp only [hzero']
    exact integral_weight_zero_lp (n + 1) _
  rw [Finset.sum_eq_single (finAxis i) (fun a _ ha => hzero a ha) (fun hc => absurd (Finset.mem_univ _) hc)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hσr : (Fin.insertNth (α := fun _ => Axis) r (finAxis i) σ) r = finAxis i :=
    Fin.insertNth_apply_same _ _ _
  have hval : (orderedFourier (n + 1) (insertLine n r i h))
      (Fin.insertNth (α := fun _ => Axis) r (finAxis i) σ)
      = torusRemove n r ((orderedFourier n h) σ) := by
    rw [orderedFourier_insertLine_apply, if_pos (by rw [hσr]), Fin.removeNth_insertNth]
  rw [hG]
  simp only [hval]
  exact integral_insertNth_energy n hlam p i r σ ((orderedFourier n h) σ)

/-! ### The sorted raising map as a projected sum of fixed-slot raisings

This is the manuscript's `D_n = \Pi_{n+1}\widetilde D_n\Pi_n`: the sorted
degree-four coefficient of the raising is the ordered-representative projection
of the sum over the four slots the appended origin line can occupy. -/

section Sorted

attribute [local instance] lineOrder

theorem orderedRepresentativeProjection_sum_insertLine (p : Fin 2 → ℝ) (i : Fin 2)
    (g : DegreeCoefficient 3) :
    orderedRepresentativeProjection 4
        (∑ r : Fin 4, insertLine 3 r i (walshOrdered 3 (degreeRaiseSymbol p i g)))
      = walshOrdered 4 (degreeRaiseDir p i g) := by
  classical
  set h : OrderedCoefficient 3 := walshOrdered 3 (degreeRaiseSymbol p i g) with hh
  apply lp.ext
  funext u
  rw [orderedRepresentativeProjection_apply]
  by_cases hu : u ∈ degreeRange 4
  · obtain ⟨T, rfl⟩ := hu
    have hmem : degreeEnum T ∈ degreeRange 4 := ⟨T, rfl⟩
    rw [Set.indicator_of_mem hmem, walshOrdered_apply_degreeEnum]
    show (∑ r : Fin 4, insertLine 3 r i h) (degreeEnum T) = degreeRaiseDir p i g T
    rw [lp.coeFn_sum]
    show (∑ r : Fin 4, (insertLine 3 r i h) (degreeEnum T)) = degreeRaiseDir p i g T
    by_cases hT : Manhattan.originLine i ∈ T.1
    · obtain ⟨S, rfl⟩ := exists_raiseIndex i T hT
      have hdeg : degreeEnum (raiseIndex i S)
          = Fin.insertNth (insertRank (Manhattan.originLine i) (degreeEnum S.1))
              (Manhattan.originLine i) (degreeEnum S.1) :=
        degreeEnum_eq_insertNth _ S.1 S.2 _ rfl
      set r₀ := insertRank (Manhattan.originLine i) (degreeEnum S.1) with hr₀
      have hsame : degreeEnum (raiseIndex i S) r₀ = Manhattan.originLine i := by
        rw [hdeg, Fin.insertNth_apply_same]
      have hinj : Function.Injective (degreeEnum (raiseIndex i S)) :=
        (strictMono_degreeEnum _).injective
      have hother : ∀ r : Fin 4, r ≠ r₀ →
          (insertLine 3 r i h) (degreeEnum (raiseIndex i S)) = 0 := by
        intro r hr
        refine insertLine_apply_of_notMem 3 r i h _ ?_
        intro hc
        exact hr (hinj (by rw [hc, hsame]))
      rw [Finset.sum_eq_single r₀ (fun r _ hr => hother r hr)
        (fun hc => absurd (Finset.mem_univ _) hc)]
      have hind : insertLineIndex 3 r₀ i (degreeEnum S.1) = degreeEnum (raiseIndex i S) := by
        rw [hdeg, insertLineIndex]
      rw [← hind, insertLine_apply_image, hh, walshOrdered_apply_degreeEnum]
      show degreeRaiseSymbol p i g S.1 = degreeRaise i (degreeRaiseSymbol p i g) (raiseIndex i S)
      rw [degreeRaise_apply_raiseIndex]
    · have hzeroterms : ∀ r : Fin 4, (insertLine 3 r i h) (degreeEnum T) = 0 := by
        intro r
        refine insertLine_apply_of_notMem 3 r i h _ ?_
        intro hc
        exact hT (hc ▸ degreeEnum_mem T r)
      rw [Finset.sum_congr rfl fun r _ => hzeroterms r, Finset.sum_const_zero]
      show (0 : ℂ) = degreeRaise i (degreeRaiseSymbol p i g) T
      exact (degreeRaise_apply_of_notMem i _ T hT).symm
  · rw [Set.indicator_of_notMem hu]
    have hp4 := congrArg
      (fun c : OrderedCoefficient 4 => (c : (Fin 4 → LineIndex) → ℂ) u)
      (orderedRepresentativeProjection_walshOrdered 4 (degreeRaiseDir p i g))
    simp only [orderedRepresentativeProjection_apply] at hp4
    rw [← hp4, Set.indicator_of_notMem hu]

end Sorted

end FixedSlot

/-! ### Four terms, four times the sum of squares

The manuscript's "bound the square of the four-term sum by four times the sum
of squares", for the quadratic form of any nonnegative operator. -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem re_inner_add_le (N : E →L[ℂ] E)
    (hN : ∀ c : E, 0 ≤ RCLike.re (inner ℂ (N c) c)) (u v : E) :
    RCLike.re (inner ℂ (N (u + v)) (u + v))
      ≤ 2 * RCLike.re (inner ℂ (N u) u) + 2 * RCLike.re (inner ℂ (N v) v) := by
  have hpos := hN (u - v)
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right] at hpos ⊢
  linarith

theorem re_inner_add_four_le (N : E →L[ℂ] E)
    (hN : ∀ c : E, 0 ≤ RCLike.re (inner ℂ (N c) c)) (a b c d : E) :
    RCLike.re (inner ℂ (N (a + b + c + d)) (a + b + c + d))
      ≤ 4 * RCLike.re (inner ℂ (N a) a) + 4 * RCLike.re (inner ℂ (N b) b)
        + 4 * RCLike.re (inner ℂ (N c) c) + 4 * RCLike.re (inner ℂ (N d) d) := by
  have hsplit : a + b + c + d = (a + b) + (c + d) := add_assoc (a + b) c d
  rw [hsplit]
  have h1 := re_inner_add_le N hN (a + b) (c + d)
  have h2 := re_inner_add_le N hN a b
  have h3 := re_inner_add_le N hN c d
  linarith

end Quadratic

/-! ### The degree-three symbol as a Fourier multiplier

Equation (45): the raising symbol acts in each axis sector as multiplication by
`i sin(P_i)`. -/

section Symbol

theorem lineTranslation_neg_cancel (z : Manhattan.Site) (l : LineIndex) :
    Manhattan.lineTranslation (-z) (Manhattan.lineTranslation z l) = l := by
  obtain ⟨a, m⟩ := l
  cases a <;> simp [Manhattan.lineTranslation, Manhattan.transverseCoordinate]

theorem translateWalshIndex_neg_cancel (x : Operator.Lattice) (A : Finset LineIndex) :
    Manhattan.translateWalshIndex (-x) (Manhattan.translateWalshIndex x A) = A := by
  ext l
  simp only [Manhattan.translateWalshIndex, Finset.mem_map, Equiv.coe_toEmbedding,
    Manhattan.latticeToSite_neg]
  constructor
  · rintro ⟨m, ⟨k, hk, rfl⟩, rfl⟩
    rwa [lineTranslation_neg_cancel]
  · intro hl
    refine ⟨Manhattan.lineTranslation (Manhattan.latticeToSite x) l, ⟨l, hl, rfl⟩, ?_⟩
    rw [lineTranslation_neg_cancel]

theorem translateDegreeIndex_neg_cancel (n : ℕ) (x : Operator.Lattice)
    (S : WalshDegreeIndex n) :
    translateDegreeIndex n (-x) (translateDegreeIndex n x S) = S := by
  apply Subtype.ext
  rw [translateDegreeIndex_coe, translateDegreeIndex_coe, translateWalshIndex_neg_cancel]

theorem pullTranslate_eq_translateCoeff (n : ℕ) (x : Operator.Lattice)
    (c : DegreeCoefficient n) :
    pullTranslate n x c = translateCoeff n (-x) c := by
  apply lp.ext
  funext S
  rw [pullTranslate_apply]
  show _ = (l2CongrLeft (translateDegreeIndex n (-x)) c) S
  rw [l2CongrLeft_apply, ← (Equiv.eq_symm_apply
    (translateDegreeIndex n (-x))).mpr (translateDegreeIndex_neg_cancel n x S)]

/-- Equation (45) on the frequency side: the degree-three raising symbol is the
phase difference of the two frequency shifts. -/
theorem lineIndexFourier_degreeRaiseSymbol (p : Fin 2 → ℝ) (i : Fin 2)
    (g : DegreeCoefficient 3) :
    lineIndexFourier 3 (degreeRaiseSymbol p i g)
      = (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) •
            freqShift 3 (Operator.axisVector i) (lineIndexFourier 3 g) -
          Complex.exp (-Complex.I * p i) •
            freqShift 3 (-Operator.axisVector i) (lineIndexFourier 3 g)) := by
  rw [degreeRaiseSymbol]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_toContinuousLinearMap,
    map_smul, map_sub]
  rw [pullTranslate_eq_translateCoeff, pullTranslate_eq_translateCoeff, neg_neg,
    lineIndexFourier_translateCoeff, lineIndexFourier_translateCoeff]

theorem lineShiftVector_eq_patternShift (n : ℕ) (i : Fin 2) (σ : Fin n → Axis) :
    lineShiftVector n (Operator.axisVector i) σ = patternShift i σ := by
  funext a
  rw [lineShiftVector_eq_axisShift]
  rfl

/-- The line-frequency coefficient of the raised degree-three coefficient is
`raisingSymbol` times that of the original, sector by sector. -/
theorem coeFn_lineIndexFourier_degreeRaiseSymbol (p : Fin 2 → ℝ) (i : Fin 2)
    (g : DegreeCoefficient 3) (σ : Fin 3 → Axis) :
    ((lineIndexFourier 3 (degreeRaiseSymbol p i g)) σ : UnitAddTorus (Fin 3) → ℂ)
      =ᵐ[LineTorusMeasure 3] fun t =>
        raisingSymbol p i σ t * ((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t := by
  set v : LineFreqL2 3 := lineIndexFourier 3 g with hv
  have hsmul : ∀ (a : ℂ) (w : LineFreqL2 3),
      ((a • w : LineFreqL2 3) : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ
        = a • ((w : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ) := by
    intro a w
    rw [lp.coeFn_smul]
    rfl
  have hsub : ∀ (w w' : LineFreqL2 3),
      ((w - w' : LineFreqL2 3) : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ
        = ((w : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ)
          - ((w' : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ) := by
    intro w w'
    rw [lp.coeFn_sub]
    rfl
  have hshift : ∀ (x : Operator.Lattice) (w : LineFreqL2 3),
      ((freqShift 3 x w : LineFreqL2 3) : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ
        = charMul 3 (lineShiftVector 3 x σ)
            ((w : (Fin 3 → Axis) → Lp ℂ 2 (LineTorusMeasure 3)) σ) := by
    intro x w
    rw [freqShift, l2CongrRightDep_apply]
  have hsector : (lineIndexFourier 3 (degreeRaiseSymbol p i g)) σ
      = (2 : ℂ)⁻¹ • (Complex.exp (Complex.I * p i) •
            charMul 3 (patternShift i σ) (v σ) -
          Complex.exp (-Complex.I * p i) •
            charMul 3 (-patternShift i σ) (v σ)) := by
    rw [lineIndexFourier_degreeRaiseSymbol, ← hv, hsmul, hsub, hsmul, hsmul, hshift, hshift,
      lineShiftVector_eq_patternShift, lineShiftVector_neg, lineShiftVector_eq_patternShift]
  rw [hsector]
  filter_upwards [Lp.coeFn_smul ((2 : ℂ)⁻¹)
      (Complex.exp (Complex.I * p i) • charMul 3 (patternShift i σ) (v σ) -
        Complex.exp (-Complex.I * p i) • charMul 3 (-patternShift i σ) (v σ)),
    Lp.coeFn_sub (Complex.exp (Complex.I * p i) • charMul 3 (patternShift i σ) (v σ))
      (Complex.exp (-Complex.I * p i) • charMul 3 (-patternShift i σ) (v σ)),
    Lp.coeFn_smul (Complex.exp (Complex.I * p i)) (charMul 3 (patternShift i σ) (v σ)),
    Lp.coeFn_smul (Complex.exp (-Complex.I * p i)) (charMul 3 (-patternShift i σ) (v σ)),
    coeFn_charMul 3 (patternShift i σ) (v σ),
    coeFn_charMul 3 (-patternShift i σ) (v σ)] with t h1 h2 h3 h4 h5 h6
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6,
    raisingSymbol]
  simp only [smul_eq_mul]
  ring

/-- The modulus of the raising symbol is `|sin(P_i)|`. -/
theorem norm_raisingSymbol (n : ℕ) (p : Fin 2 → ℝ) (i : Fin 2) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) :
    ‖raisingSymbol p i σ t‖ = |Real.sin (totalFrequency n p σ t i)| := by
  have ht : t = fun a => ((torusLift (t a) : ℝ) : UnitAddCircle) := by
    funext a
    rw [torusLift_coe]
  have hfreq : totalFrequency n p σ t i
      = p i + 2 * Real.pi * ∑ a : Fin n, ((axisShift i (σ a) : ℤ) : ℝ) * torusLift (t a) := by
    simp only [totalFrequency, lineFrequency, lineShiftVector_eq_axisShift]
  rw [show raisingSymbol p i σ t
      = raisingSymbol p i σ (fun a => ((torusLift (t a) : ℝ) : UnitAddCircle)) from
    congrArg _ ht, raisingSymbol_apply, hfreq]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

end Symbol

/-! ### The multiplier energy at degree three -/

section Multiplier

theorem cos_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (t : UnitAddTorus (Fin n)) (k : Fin 2) :
    Real.cos (totalFrequency n p σ t k)
      = (Complex.exp (Complex.I * (p k : ℂ)) *
          mFourier (lineShiftVector n (Operator.axisVector k) σ) t).re := by
  rw [mFourier_eq_exp, ← Complex.exp_add]
  have harg : Complex.I * (p k : ℂ) +
      Complex.I * ((2 * Real.pi *
        ∑ a : Fin n, ((lineShiftVector n (Operator.axisVector k) σ a : ℤ) : ℝ) *
          torusLift (t a) : ℝ) : ℂ)
      = ((totalFrequency n p σ t k : ℝ) : ℂ) * Complex.I := by
    simp only [totalFrequency, lineFrequency]
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

theorem continuous_cos_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) (k : Fin 2) :
    Continuous fun t => Real.cos (totalFrequency n p σ t k) := by
  have h : (fun t => Real.cos (totalFrequency n p σ t k))
      = fun t => (Complex.exp (Complex.I * (p k : ℂ)) *
          mFourier (lineShiftVector n (Operator.axisVector k) σ) t).re :=
    funext fun t => cos_totalFrequency n p σ t k
  rw [h]
  exact Complex.continuous_re.comp (continuous_const.mul (mFourier _).continuous)

theorem continuous_dispersion_totalFrequency (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis)
    (k : Fin 2) :
    Continuous fun t => Estimates.dispersion (totalFrequency n p σ t k) := by
  simp only [Estimates.dispersion]
  exact continuous_const.sub (continuous_cos_totalFrequency n p σ k)

theorem dispersion_eq_two_mul_sin_sq (x : ℝ) :
    Estimates.dispersion x = 2 * Real.sin (x / 2) ^ 2 := by
  unfold Estimates.dispersion
  rw [show Real.cos x = Real.cos (2 * (x / 2)) by congr 1; ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

theorem two_abs_sin_half_eq_sqrt (x : ℝ) :
    2 * |Real.sin (x / 2)| = Real.sqrt (2 * Estimates.dispersion x) := by
  rw [dispersion_eq_two_mul_sin_sq,
    show 2 * (2 * Real.sin (x / 2) ^ 2) = (2 * |Real.sin (x / 2)|) ^ 2 by
      rw [mul_pow, sq_abs]; ring,
    Real.sqrt_sq (by positivity)]

theorem multiplier_eq_sqrt (kappa : ℝ) (q : Estimates.Parameters) (P : Fin 2 → ℝ) :
    Estimates.multiplier kappa q P
      = kappa * (q.lambda + Estimates.theta P + Real.sqrt (2 * Estimates.dispersion (P 0))
        + Real.sqrt (2 * Estimates.dispersion (P 1))) := by
  rw [Estimates.multiplier, ← two_abs_sin_half_eq_sqrt, ← two_abs_sin_half_eq_sqrt]

theorem continuous_multiplier_totalFrequency (n : ℕ) (kappa : ℝ) (q : Estimates.Parameters)
    (p : Fin 2 → ℝ) (σ : Fin n → Axis) :
    Continuous fun t => Estimates.multiplier kappa q (totalFrequency n p σ t) := by
  have h : (fun t => Estimates.multiplier kappa q (totalFrequency n p σ t))
      = fun t => kappa * (q.lambda +
          (Estimates.dispersion (totalFrequency n p σ t 0) +
            Estimates.dispersion (totalFrequency n p σ t 1)) +
          Real.sqrt (2 * Estimates.dispersion (totalFrequency n p σ t 0)) +
          Real.sqrt (2 * Estimates.dispersion (totalFrequency n p σ t 1))) := by
    funext t
    rw [multiplier_eq_sqrt]
    rfl
  rw [h]
  refine continuous_const.mul ?_
  refine ((continuous_const.add ((continuous_dispersion_totalFrequency n p σ 0).add
    (continuous_dispersion_totalFrequency n p σ 1))).add ?_).add ?_
  · exact (continuous_const.mul (continuous_dispersion_totalFrequency n p σ 0)).sqrt
  · exact (continuous_const.mul (continuous_dispersion_totalFrequency n p σ 1)).sqrt

theorem multiplier_le_bound {q : Estimates.Parameters} {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hlam : 0 ≤ q.lambda) (P : Fin 2 → ℝ) :
    ‖Estimates.multiplier kappa q P‖ ≤ kappa * (q.lambda + 8) := by
  have hd0 : Estimates.dispersion (P 0) ≤ 2 := by
    have := Real.neg_one_le_cos (P 0)
    simp only [Estimates.dispersion]
    linarith
  have hd1 : Estimates.dispersion (P 1) ≤ 2 := by
    have := Real.neg_one_le_cos (P 1)
    simp only [Estimates.dispersion]
    linarith
  have hs0 : |Real.sin (P 0 / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hs1 : |Real.sin (P 1 / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hnn : 0 ≤ Estimates.multiplier kappa q P :=
    Estimates.multiplier_nonneg hkappa hlam P
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, Estimates.multiplier, Estimates.theta]
  nlinarith [hkappa, hd0, hd1, hs0, hs1, hlam]

theorem integrable_multiplier_norm_sq {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 0 ≤ kappa) (hlam : 0 ≤ q.lambda)
    (n : ℕ) (p : Fin 2 → ℝ) (σ : Fin n → Axis) (v : Lp ℂ 2 (LineTorusMeasure n)) :
    Integrable (fun t => Estimates.multiplier kappa q (totalFrequency n p σ t) *
      ‖(v : UnitAddTorus (Fin n) → ℂ) t‖ ^ 2) (LineTorusMeasure n) := by
  refine (integrable_norm_sq_lp n v).bdd_mul (c := kappa * (q.lambda + 8))
    (continuous_multiplier_totalFrequency n kappa q p σ).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => multiplier_le_bound hkappa hlam _

end Multiplier

/-! ### Scaling in the multiplier constant

The multiplier is linear in its constant, so an identity or an inequality
between multiplier integrals proved at one constant holds at every other. -/

theorem integral_multiplier_eq_smul {α : Type*} [MeasurableSpace α]
    (kappa : ℝ) (q : Estimates.Parameters) (mu : MeasureTheory.Measure α)
    (F : α → Fin 2 → ℝ) (g : α → ℝ) :
    (∫ t, Estimates.multiplier kappa q (F t) * g t ∂mu)
      = kappa * ∫ t, Estimates.multiplier 1 q (F t) * g t ∂mu := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Estimates.multiplier]; ring

theorem tsum_integral_multiplier_eq_smul {ι α : Type*} [MeasurableSpace α]
    (kappa : ℝ) (q : Estimates.Parameters) (mu : MeasureTheory.Measure α)
    (F : ι → α → Fin 2 → ℝ) (g : ι → α → ℝ) :
    (∑' i : ι, ∫ t, Estimates.multiplier kappa q (F i t) * g i t ∂mu)
      = kappa * ∑' i : ι, ∫ t, Estimates.multiplier 1 q (F i t) * g i t ∂mu := by
  rw [← tsum_mul_left]
  exact tsum_congr fun i => integral_multiplier_eq_smul kappa q mu (F i) (g i)

/-! ### The pointwise comparison, sector by sector -/

theorem integral_slot_le_multiplier {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) (i : Fin 2) (g : DegreeCoefficient 3) (σ : Fin 3 → Axis) :
    (∫ s, (Real.sqrt ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) *
          ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) + 2)))⁻¹ *
        ‖((lineIndexFourier 3 (degreeRaiseSymbol p i g)) σ :
          UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 ∂(LineTorusMeasure 3))
      ≤ (8 : ℝ)⁻¹ * ∫ s, Estimates.multiplier kappa q (totalFrequency 3 p σ s) *
          ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2
          ∂(LineTorusMeasure 3) := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards with s
    positivity
  · exact (integrable_multiplier_norm_sq (by linarith : (0:ℝ) ≤ kappa) hlam.le 3 p σ ((lineIndexFourier 3 g) σ)).const_mul _
  · filter_upwards [coeFn_lineIndexFourier_degreeRaiseSymbol p i g σ] with s hs
    rw [hs, norm_mul, norm_raisingSymbol, mul_pow, sq_abs]
    have hkey := inv_sqrt_slot_mul_sin_sq_le hkappa hlam (totalFrequency 3 p σ s) i
    calc (Real.sqrt ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) *
            ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) + 2)))⁻¹ *
          (Real.sin (totalFrequency 3 p σ s i) ^ 2 *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2)
        = ((Real.sqrt ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) *
              ((q.lambda + Estimates.dispersion (totalFrequency 3 p σ s i)) + 2)))⁻¹ *
            Real.sin (totalFrequency 3 p σ s i) ^ 2) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 := by ring
      _ ≤ (Estimates.multiplier kappa q (totalFrequency 3 p σ s) / 8) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hkey (sq_nonneg _)
      _ = (8 : ℝ)⁻¹ * (Estimates.multiplier kappa q (totalFrequency 3 p σ s) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) s‖ ^ 2) := by ring

/-! ### The degree-four raising energy bound -/

section Final

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] orderedInverseUnitAddCircleMeasureSpace
attribute [local instance] orderedInverseUnitAddCircleIsProbabilityMeasure

theorem re_inner_orderedHInv_insertLine_le {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) (i : Fin 2) (r : Fin 4) (g : DegreeCoefficient 3) :
    RCLike.re (inner ℂ
        (orderedHInv 4 hlam p (insertLine 3 r i (walshOrdered 3 (degreeRaiseSymbol p i g))))
        (insertLine 3 r i (walshOrdered 3 (degreeRaiseSymbol p i g))))
      ≤ (8 : ℝ)⁻¹ * ∑' σ : Fin 3 → Axis, ∫ t,
          Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure 3) := by
  rw [re_inner_orderedHInv_eq_integral 4 hlam p _,
    tsum_integral_inv_symbolWeight_insertLine 3 hlam p i r _,
    tsum_fintype, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  exact integral_slot_le_multiplier hkappa hlam p i g σ

/-- **The degree-four raising energy bound.**  The operator half of Lemma 5.2,
for a general degree-three coefficient: the `H^{-1}` energy of the raised
degree-four coefficient is at most twice the degree-three multiplier energy at
the same momentum, with the universal constant `kappa = 40`.  No momentum
comparison is used. -/
theorem tsum_integral_inv_symbolWeight_degreeRaiseDir_le {q : Estimates.Parameters}
    {kappa : ℝ} (hkappa : 12 ≤ kappa)
    (hlam : 0 < q.lambda) (p : Fin 2 → ℝ) (i : Fin 2) (g : DegreeCoefficient 3) :
    (∑' σ : Fin 4 → Axis, ∫ t, (symbolWeight 4 q.lambda p σ t)⁻¹ *
        ‖((lineIndexFourier 4 (degreeRaiseDir p i g)) σ :
          UnitAddTorus (Fin 4) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 4))
      ≤ 2 * ∑' σ : Fin 3 → Axis, ∫ t,
          Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure 3) := by
  have hstep0 : (∑' σ : Fin 4 → Axis, ∫ t, (symbolWeight 4 q.lambda p σ t)⁻¹ *
      ‖((lineIndexFourier 4 (degreeRaiseDir p i g)) σ :
        UnitAddTorus (Fin 4) → ℂ) t‖ ^ 2 ∂(LineTorusMeasure 4))
      = RCLike.re (inner ℂ (orderedHInv 4 hlam p (walshOrdered 4 (degreeRaiseDir p i g)))
          (walshOrdered 4 (degreeRaiseDir p i g))) :=
    (re_inner_orderedHInv_eq_integral 4 hlam p (walshOrdered 4 (degreeRaiseDir p i g))).symm
  rw [hstep0, ← orderedRepresentativeProjection_sum_insertLine p i g]
  refine le_trans (re_inner_orderedHInv_orderedRepresentativeProjection_le 4 hlam p _) ?_
  rw [Fin.sum_univ_four]
  refine le_trans (re_inner_add_four_le (orderedHInv 4 hlam p)
    (re_inner_orderedHInv_nonneg 4 hlam p) _ _ _ _) ?_
  have h0 := re_inner_orderedHInv_insertLine_le hkappa hlam p i 0 g
  have h1 := re_inner_orderedHInv_insertLine_le hkappa hlam p i 1 g
  have h2 := re_inner_orderedHInv_insertLine_le hkappa hlam p i 2 g
  have h3 := re_inner_orderedHInv_insertLine_le hkappa hlam p i 3 g
  linarith

end Final

end Manhattan.Glue


