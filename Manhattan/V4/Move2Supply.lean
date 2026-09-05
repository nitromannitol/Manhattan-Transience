import Manhattan.V4.Move1
import Manhattan.V4.Frequency.Uniform
import Manhattan.Glue.AxisSwap

/-!
# Version 4: `V4Move2Supply` is a theorem (residue B-4)

Move 1 leaves four residues.  B-1 is closed by
`Manhattan/V4/MixedBridge.lean`, and B-1b, B-2, B-3 by `Manhattan/V4/MixedSector.lean`,
`Manhattan/V4/TwoRow.lean` and `Manhattan/V4/Sectors.lean`.  This file closes
B-4.

* `v4_move1_at` checks the hypotheses of `Manhattan.V4.v4_move1_objective` at
  `δ = √λ + a(p)` in the improvement region `√λ + a(p) ≤ r₀⁴`.
* `objective_of_axisSwap` transports a competitor objective through the axis
  swap; this is `Manhattan.Glue.correctedCompetitor_of_axisSwap` with an
  arbitrary right-hand side, and it is what supplies the second branch of the
  existential over `s` in `Manhattan.V4.Frequency.V4Move2Supply`.
* `v4_move2_at` is Move 2: `Manhattan.V4.Frequency.move2_bound` at the torus mass
  of the competitor profile, followed by `Manhattan.V4.Zdelta_le_profileMass`.
* `v4Move2Supply_proved` is B-4, and `v4FrequencyBound_proved`,
  `annealedGreenBound_proved` and `theorem_1_1_v4` are the three statements that
  become unconditional with it.

The composed Move 1 constant is `v4Constant = 60 + 40(π² + 60π³)`; the composed
fixed-frequency constant at `r₀ = 1/4` is
`max (max 1 (8π³ · v4Constant)) (outerRegionConstant (1/4))`, and the uniform
Green constant is `(17 + 8π²)` times that
(`Manhattan.V4.Frequency.uniform_green_bound_of_v4FrequencyBound`).

`Manhattan.Frozen.Main.theorem_1_1` is untouched and is still proved by the old
development; `theorem_1_1_v4` is the Version 4 route to the same statement.
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue Manhattan.Operator
open scoped ENNReal

/-- The composed Move 1 constant of Version 4:
`C = C₁ + C₃(π² + π³κ/2)` with `C₁ = 60`, `C₃ = 40` and `κ = 120`. -/
def v4Constant : ℝ := 60 + 40 * (Real.pi ^ 2 + Real.pi ^ 3 * 120 / 2)

theorem v4Constant_pos : 0 < v4Constant := by
  have := Real.pi_pos
  unfold v4Constant
  positivity

/-- The parameter record carrying the Version 4 spectral parameter.  Only
`lambda` is used: the operator estimate `Manhattan.V4.operatorEstimate` needs no
admissibility, and every other object (`correctionB`, `mixedHMinusWeight`,
`parityFibreJ`) depends on `q` only through `q.lambda`. -/
def v4Parameters (lambda : ℝ) : Estimates.Parameters := ⟨lambda, 20, Real.pi / 20⟩

@[simp] theorem v4Parameters_lambda (lambda : ℝ) :
    (v4Parameters lambda).lambda = lambda := rfl

theorem self_le_sqrt {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    lambda ≤ Real.sqrt lambda := by
  have hs := Real.sq_sqrt hlambda.le
  have hpos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  nlinarith [hs, hpos]

/-- **Move 1 in the improvement region.**  All the hypotheses of
`Manhattan.V4.v4_move1_objective` hold at `δ = √λ + a(p)`. -/
theorem v4_move1_at {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (p : Fin 2 → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4)
    (hp0 : |p 0| ≤ Real.pi)
    (hle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0)
                * (t * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) ^ 2
              / (lambda + Operator.theta p)
            + v4Constant
                * (t ^ 2 * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p)) := by
  set a := Operator.maxFrequency p with hadef
  have hann : 0 ≤ a := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  set delta := Real.sqrt lambda + a with hdeltadef
  have hdelta : 0 < delta := by positivity
  have hr4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr014 4
  have hdelta1 : delta ≤ 1 := by
    norm_num at hr4
    linarith
  have hlamdelta : lambda ≤ delta := by
    have := self_le_sqrt hlambda hlambda1
    linarith
  have hp0a : |p 0| ≤ a := le_max_left _ _
  have hp1a : |p 1| ≤ a := le_max_right _ _
  have hsq := Real.sq_sqrt hlambda.le
  have hmud : lambda + Estimates.dispersion (p 0) ≤ delta ^ 2 := by
    have hd := (Estimates.dispersion_quadratic_bounds hp0).2
    have habs : (p 0) ^ 2 ≤ a ^ 2 := by
      have := sq_abs (p 0)
      nlinarith [abs_nonneg (p 0), hp0a]
    have hexp : delta ^ 2 = lambda + 2 * Real.sqrt lambda * a + a ^ 2 := by
      rw [hdeltadef]
      nlinarith [hsq]
    nlinarith [hexp, hd, habs, mul_nonneg hspos.le hann]
  have hp2 : |p 1| ≤ delta := by
    have : a ≤ delta := by rw [hdeltadef]; linarith
    linarith
  have hsqle : Real.sqrt delta ≤ r0 :=
    Frequency.sqrt_le_of_le_pow_four hr0 hr014 hle
  obtain ⟨g, hg⟩ := v4_move1_objective (q := v4Parameters lambda) hlambda p
    hdelta hdelta1 hlamdelta hr014 hsqle hmud hp2 t
  exact ⟨g, hg⟩

/-! ## Transport through the axis swap -/

/-- The Version 4 competitor objective transports through the axis swap.  This
is `Manhattan.Glue.correctedCompetitor_of_axisSwap` with an arbitrary right-hand
side. -/
theorem objective_of_axisSwap {lambda X : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ)
    (h : ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
            (axisSwapFrequency p)).hEnergy lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
              (axisSwapFrequency p)).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ -
                Manhattan.concreteFiberA (axisSwapFrequency p) g) ≤ X) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
        + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g) ≤ X := by
  obtain ⟨g, hg⟩ := h
  refine ⟨axisSwapUnitary.symm g, ?_⟩
  rw [← axisSwap_competitorObjective hlambda p (axisSwapUnitary.symm g)]
  simpa using hg

theorem resolventQuadratic_le_of_objective {lambda X : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ)
    (h : ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
        + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
            (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g) ≤ X) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅) ≤ X := by
  obtain ⟨g, hg⟩ := h
  refine le_trans ?_ hg
  have hcs := (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
    p).resolventQuadratic_le hlambda (Manhattan.walshL2 ∅) g
  have hA : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).A
      = Manhattan.concreteFiberA p := rfl
  rwa [hA] at hcs

/-! ## Move 2 -/

/-- **Move 2 of Version 4.**  The Move 1 family, minimized over the profile
parameter `t`, gives the closed form with the torus mass of the competitor
profile; `Manhattan.V4.Zdelta_le_profileMass` then replaces that mass by `Z_δ`,
which is all Move 3 uses. -/
theorem v4_move2_at {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4)
    (hle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4)
    {s : ℝ}
    (hmove1 : ∀ t : ℝ, ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - s * (t * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) ^ 2
              / (lambda + Operator.theta p)
            + v4Constant
                * (t ^ 2 * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ 1 / (lambda + Operator.theta p
          + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p)
            / v4Constant) := by
  have hann : 0 ≤ Operator.maxFrequency p := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  set delta := Real.sqrt lambda + Operator.maxFrequency p with hdeltadef
  have hdelta : 0 < delta := by positivity
  have hr01 : r0 < 1 := lt_of_le_of_lt hr014 (by norm_num)
  have hr0pi : r0 < Real.pi := by linarith [Real.pi_gt_three]
  have hsqpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have hsqle : Real.sqrt delta ≤ r0 := Frequency.sqrt_le_of_le_pow_four hr0 hr014 hle
  have hZpos : 0 < Zdelta r0 delta :=
    Frequency.Zdelta_pos hr0 hr014 hdelta hle
  have hZle : Zdelta r0 delta ≤ profileMass r0 delta :=
    Zdelta_le_profileMass hsqpos hsqle hr01 hr0pi
  have hMpos : 0 < profileMass r0 delta := lt_of_lt_of_le hZpos hZle
  have hthetann : 0 ≤ Operator.theta p := by
    rw [Manhattan.Estimates.operator_theta_eq]
    exact Manhattan.Estimates.theta_nonneg p
  have hh0 : 0 < lambda + Operator.theta p := by linarith
  have hall : ∀ t : ℝ,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
          hlambda (Manhattan.walshL2 ∅)
        ≤ (1 - s * (t * profileMass r0 delta)) ^ 2 / (lambda + Operator.theta p)
            + v4Constant * (t ^ 2 * profileMass r0 delta) :=
    fun t => resolventQuadratic_le_of_objective hlambda p (hmove1 t)
  have hmove2 := Frequency.move2_bound hh0 hMpos v4Constant_pos hall
  refine hmove2.trans ?_
  have hnum : 0 ≤ s ^ 2 := sq_nonneg s
  have hden1 : 0 < lambda + Operator.theta p
      + s ^ 2 * Zdelta r0 delta / v4Constant := by
    have h0 : 0 ≤ s ^ 2 * Zdelta r0 delta / v4Constant :=
      div_nonneg (mul_nonneg hnum hZpos.le) v4Constant_pos.le
    linarith
  have hstep : lambda + Operator.theta p
      + s ^ 2 * Zdelta r0 delta / v4Constant
      ≤ lambda + Operator.theta p + s ^ 2 * profileMass r0 delta / v4Constant := by
    have hmul : s ^ 2 * Zdelta r0 delta / v4Constant
        ≤ s ^ 2 * profileMass r0 delta / v4Constant := by
      gcongr
      exact v4Constant_pos.le
    linarith
  exact one_div_le_one_div_of_le hden1 hstep

theorem v4_move2_at' {lambda C : ℝ} (hC : 0 < C) (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4)
    (hle : Real.sqrt lambda + Operator.maxFrequency p ≤ r0 ^ 4)
    {s : ℝ}
    (hmove1 : ∀ t : ℝ, ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - s * (t * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) ^ 2
              / (lambda + Operator.theta p)
            + C
                * (t ^ 2 * profileMass r0 (Real.sqrt lambda + Operator.maxFrequency p))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
        hlambda (Manhattan.walshL2 ∅)
      ≤ 1 / (lambda + Operator.theta p
          + s ^ 2 * Zdelta r0 (Real.sqrt lambda + Operator.maxFrequency p)
            / C) := by
  have hann : 0 ≤ Operator.maxFrequency p := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  set delta := Real.sqrt lambda + Operator.maxFrequency p with hdeltadef
  have hdelta : 0 < delta := by positivity
  have hr01 : r0 < 1 := lt_of_le_of_lt hr014 (by norm_num)
  have hr0pi : r0 < Real.pi := by linarith [Real.pi_gt_three]
  have hsqpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have hsqle : Real.sqrt delta ≤ r0 := Frequency.sqrt_le_of_le_pow_four hr0 hr014 hle
  have hZpos : 0 < Zdelta r0 delta :=
    Frequency.Zdelta_pos hr0 hr014 hdelta hle
  have hZle : Zdelta r0 delta ≤ profileMass r0 delta :=
    Zdelta_le_profileMass hsqpos hsqle hr01 hr0pi
  have hMpos : 0 < profileMass r0 delta := lt_of_lt_of_le hZpos hZle
  have hthetann : 0 ≤ Operator.theta p := by
    rw [Manhattan.Estimates.operator_theta_eq]
    exact Manhattan.Estimates.theta_nonneg p
  have hh0 : 0 < lambda + Operator.theta p := by linarith
  have hall : ∀ t : ℝ,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).resolventQuadratic
          hlambda (Manhattan.walshL2 ∅)
        ≤ (1 - s * (t * profileMass r0 delta)) ^ 2 / (lambda + Operator.theta p)
            + C * (t ^ 2 * profileMass r0 delta) :=
    fun t => resolventQuadratic_le_of_objective hlambda p (hmove1 t)
  have hmove2 := Frequency.move2_bound hh0 hMpos hC hall
  refine hmove2.trans ?_
  have hnum : 0 ≤ s ^ 2 := sq_nonneg s
  have hden1 : 0 < lambda + Operator.theta p
      + s ^ 2 * Zdelta r0 delta / C := by
    have h0 : 0 ≤ s ^ 2 * Zdelta r0 delta / C :=
      div_nonneg (mul_nonneg hnum hZpos.le) hC.le
    linarith
  have hstep : lambda + Operator.theta p
      + s ^ 2 * Zdelta r0 delta / C
      ≤ lambda + Operator.theta p + s ^ 2 * profileMass r0 delta / C := by
    have hmul : s ^ 2 * Zdelta r0 delta / C
        ≤ s ^ 2 * profileMass r0 delta / C := by
      gcongr
    linarith
  exact one_div_le_one_div_of_le hden1 hstep

/-! ## `V4Move2Supply` -/

/-- **The Move 2 supply of Version 4, unconditionally.**  This is the last
residue, B-4.  The existential over `s`
is discharged by `sin p₁` on the branch where `a(p) = |p₁|` and by `sin p₂`,
through the axis swap of `Manhattan/Glue/AxisSwap.lean`, on the other. -/
theorem v4Move2Supply_proved {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 v4Constant := by
  intro lambda hlambda hlambda1 p hp0 hp1 hle
  have hp0abs : |p 0| ≤ Real.pi := abs_le.2 ⟨hp0.1.le, hp0.2⟩
  have hp1abs : |p 1| ≤ Real.pi := abs_le.2 ⟨hp1.1.le, hp1.2⟩
  have hann : 0 ≤ Operator.maxFrequency p := Frequency.maxFrequency_nonneg p
  have hspos : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have hr4 : r0 ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hr0.le hr014 4
  have hasmall : Operator.maxFrequency p ≤ Real.pi / 2 := by
    norm_num at hr4
    nlinarith [Real.pi_gt_three, hspos]
  have hjordan : ∀ x : ℝ, |x| = Operator.maxFrequency p →
      (2 / Real.pi) ^ 2 * Operator.maxFrequency p ^ 2 ≤ x.sin ^ 2 := by
    intro x hx
    have hxle : |x| ≤ Real.pi / 2 := by rw [hx]; exact hasmall
    have hj := Real.mul_abs_le_abs_sin hxle
    have hnn : 0 ≤ 2 / Real.pi * |x| := by positivity
    have hsq := mul_self_le_mul_self hnn hj
    rw [hx] at hsq
    nlinarith [sq_abs (Real.sin x), hsq, sq_abs x]
  rcases le_total (|p 1|) (|p 0|) with hbr | hbr
  · have ha : Operator.maxFrequency p = |p 0| := max_eq_left hbr
    refine ⟨Real.sin (p 0), hjordan (p 0) ha.symm, ?_⟩
    exact v4_move2_at hlambda p hr0 hr014 hle
      (fun t => v4_move1_at hlambda hlambda1 p hr0 hr014 hp0abs hle t)
  · have ha : Operator.maxFrequency p = |p 1| := max_eq_right hbr
    refine ⟨Real.sin (p 1), hjordan (p 1) ha.symm, ?_⟩
    refine v4_move2_at hlambda p hr0 hr014 hle ?_
    intro t
    have hswap : Operator.maxFrequency (axisSwapFrequency p) = Operator.maxFrequency p :=
      axisSwap_maxFrequency p
    have hth : Operator.theta (axisSwapFrequency p) = Operator.theta p := axisSwap_theta p
    have hle' : Real.sqrt lambda + Operator.maxFrequency (axisSwapFrequency p) ≤ r0 ^ 4 := by
      rw [hswap]; exact hle
    have h0' : |axisSwapFrequency p 0| ≤ Real.pi := by
      rw [axisSwapFrequency_zero]; exact hp1abs
    have hm := v4_move1_at hlambda hlambda1 (axisSwapFrequency p) hr0 hr014 h0' hle' t
    rw [hswap, hth, axisSwapFrequency_zero] at hm
    exact objective_of_axisSwap hlambda p hm

/-! ## The unconditional consequences -/

/-- **`V4FrequencyBound` is now unconditional.**  At `r₀ = 1/4` the Version 4
fixed-frequency bound holds with the absolute constant
`max (max 1 (8π³ C)) (outerRegionConstant (1/4))`, `C = 60 + 40(π² + 60π³)`. -/
theorem v4FrequencyBound_proved :
    Frequency.V4FrequencyBound
      (max (max 1 (8 * Real.pi ^ 3 * v4Constant))
        (Frequency.outerRegionConstant (1 / 4))) :=
  Frequency.v4FrequencyBound_of_move2Supply (by norm_num) le_rfl v4Constant_pos
    (v4Move2Supply_proved (by norm_num) le_rfl)

/-- **The annealed Green bound (Theorem 1.2) by the Version 4 route**, with no
hypotheses. -/
theorem annealedGreenBound_proved : Manhattan.AnnealedGreenBound :=
  Frequency.annealedGreenBound_of_v4Move2Supply (by norm_num) le_rfl v4Constant_pos
    (v4Move2Supply_proved (by norm_num) le_rfl)

/-- **Theorem 1.1 by the Version 4 route**, with no hypotheses. -/
theorem theorem_1_1_v4 :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ :=
  Frequency.theorem_1_1_of_v4Move2Supply (by norm_num) le_rfl v4Constant_pos
    (v4Move2Supply_proved (by norm_num) le_rfl)

end Manhattan.V4
