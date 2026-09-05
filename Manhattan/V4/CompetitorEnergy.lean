import Manhattan.V4.Parity
import Manhattan.V4.Energy.DegreeOne
import Manhattan.V4.ScalarMinimization
import Manhattan.Glue.SummandsDegreeOne
import Manhattan.Glue.Correction
import Manhattan.V4.ParityIntegral
import Manhattan.V4.Energy.Move1

/-!
# Version 4, Move 1: the two reachable halves of the competitor cost

`Manhattan.V4.Energy.effectiveEnergy_le` carries the competitor
bound itself as the hypothesis `hcompetitor`.  Discharging it end to end needs
four concrete operator identifications: the degree-one energy, the degree-zero
residual, the degree-two dual form at the parity kernel, and the sector
splitting.  Three of the four are reachable from what the sealed development already
proves, and those three are what this file lands; the
fourth, the degree-two dual form at the parity kernel, needs a raw-to-Walsh
bridge that does not exist yet.

* **The degree-one summand.**  `hEnergy_degreeOne_le`.  The sealed
  `Manhattan.Glue.hEnergy_degreeOneRowShift` evaluates the degree-one energy of
  the shifted row synthesis exactly, as `∫ (λ + d(p₁) + d(r)) ‖f(r)‖² dm`, and
  estimate (4) (`Manhattan.V4.Energy.degreeOne_multiplier_le`, here at `s = 0`) turns that
  into `6 ∫ (δ + r²) ‖f(r)‖² dm`.

* **The degree-zero summand.**  `hMinusEnergy_degreeZero` and
  `inner_empty_residual_degreeOne`.  The dual energy of a multiple of the
  constant Walsh vector is `|c|²/(λ + θ(p))`, so Move 1's `h₀` is `λ + θ(p)`;
  and the constant Walsh coefficient of the residual `1 - A_p f` at the purely
  imaginary degree-one competitor `f = -iφ` is `1 - sin(p₁) ∫ φ dm`, Move 1's
  numerator.

* **The competitor energy of Steps 3 and 4.**  `parityCompetitor_density_eq`
  and `paritySigmaEnergy_le_density`.  At the parity minimizer
  `v = w/(B + σ)` of `Manhattan.V4.parityProfileV` the degree-three density
  `σ v²` and the degree-two residual density `(w - σ v)²/B` add up **exactly**
  to the Move 1 density `w(r)² J₃(r)`, `J₃(r) = ∫ dm(β)/(B(r,β) + σ(r,β))`.
  The pointwise step is `Manhattan.V4.scalarCompletion_eq`; the
  analytic step is the interchange of the two torus integrals, which is
  legitimate because the integrand is bounded by `‖w‖_∞²/λ`.

`v4_competitor_cost_le` composes these with
`Manhattan.V4.parity_betaIntegral_le` and
`Manhattan.V4.Energy.move1_energy_le`: the whole Version 4 competitor cost is at
most `(C₁ + C₃(π² + π³κ/2)) ∫ q φ² dm`, `q(r) = |r|/√(log(1/|r|))`.  With
`C₁ = 6` (estimate (4)) and `C₃ = 9` (`Manhattan.V4.operatorEstimate`) and
`κ = 120` (`Manhattan.V4.multiplier_le_evenMajorant`) that constant is
`6 + 9π² + 540π³`.
-/

noncomputable section

open MeasureTheory

namespace Manhattan.V4

/-! ## The degree-one cost of the Version 4 competitor -/

/-- Estimate (4) with the two-row contraction dropped: the bare degree-one
symbol `μ + d(r)` of the shifted row synthesis already obeys the Version 4
bound `6(δ + r²)`.  Specialization of `degreeOne_multiplier_le` at `s = 0`. -/
theorem degreeOne_symbol_le {mu delta r : ℝ} (hmu : 0 < mu) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hmud : mu ≤ delta ^ 2) :
    mu + Manhattan.Estimates.dispersion r ≤ 6 * (delta + r ^ 2) := by
  have h := Energy.degreeOne_multiplier_le (mu := mu) (delta := delta) (s := 0) (r := r)
    hmu hdelta hdelta1 hmud (by norm_num; linarith)
  simpa using h

/-- **Move 1, the degree-one summand, for the concrete model.**  The exact
degree-one energy of the shifted row synthesis
(`Manhattan.Glue.hEnergy_degreeOneRowShift`) is `∫ (λ + d(p₁) + d(r)) ‖f(r)‖² dm`,
and estimate (4) turns that into `6 ∫ (δ + r²) ‖f(r)‖² dm`. -/
theorem hEnergy_degreeOne_le {lambda delta : ℝ} {p : Fin 2 → ℝ}
    (hlam : 0 < lambda) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hmud : lambda + Manhattan.Estimates.dispersion (p 0) ≤ delta ^ 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    (hint : Integrable (fun r => (delta + r ^ 2) * ‖f r‖ ^ 2)
      (volume.restrict Manhattan.Estimates.torus)) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
          (Manhattan.Glue.rowTorusShift (p 1) (Manhattan.realTorusL2 f hf)))
      ≤ 6 * Manhattan.Estimates.torusIntegral (fun r => (delta + r ^ 2) * ‖f r‖ ^ 2) := by
  rw [Manhattan.Glue.hEnergy_degreeOneRowShift lambda p f hf]
  have hmu : 0 < lambda + Manhattan.Estimates.dispersion (p 0) :=
    add_pos_of_pos_of_nonneg hlam (Manhattan.Estimates.dispersion_nonneg (p 0))
  have hmono : Manhattan.Estimates.torusIntegral
      (fun r => (lambda + Manhattan.Estimates.dispersion (p 0)
        + Manhattan.Estimates.dispersion r) * ‖f r‖ ^ 2)
      ≤ Manhattan.Estimates.torusIntegral
        (fun r => 6 * ((delta + r ^ 2) * ‖f r‖ ^ 2)) := by
    refine Manhattan.Estimates.torusIntegral_mono' ?_ (hint.const_mul 6) ?_
    · intro r
      have h1 : 0 ≤ lambda + Manhattan.Estimates.dispersion (p 0)
          + Manhattan.Estimates.dispersion r := by
        have := Manhattan.Estimates.dispersion_nonneg r
        linarith
      positivity
    · intro r
      have hsym := degreeOne_symbol_le (mu := lambda + Manhattan.Estimates.dispersion (p 0))
        (delta := delta) (r := r) hmu hdelta hdelta1 hmud
      have hnn : (0:ℝ) ≤ ‖f r‖ ^ 2 := by positivity
      nlinarith [hsym, hnn]
  rw [Manhattan.Estimates.torusIntegral_smul_left 6
    (fun r => (delta + r ^ 2) * ‖f r‖ ^ 2)] at hmono
  exact hmono

/-! ## The degree-zero summand of the Version 4 competitor -/

/-- **Move 1, the degree-zero summand, for the concrete model.**  The dual
energy of a multiple of the constant Walsh vector is `|c|²/(λ + θ(p))`, so
`h₀ = λ + θ(p)` is the denominator Move 1 writes. -/
theorem hMinusEnergy_degreeZero {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (c : ℂ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (c • Manhattan.walshL2 ∅)
      = ‖c‖ ^ 2 / (lambda + Operator.theta p) := by
  rw [Manhattan.Glue.hMinusEnergy_smul _ hlambda c (Manhattan.walshL2 ∅),
    Manhattan.concrete_hMinusEnergy_empty hlambda p, Operator.driftlessMajorant]
  ring

/-- The Version 4 degree-zero residual `(1 - s ∫ φ dm)²/(λ + θ(p))`, the first
summand of Move 1, is exactly the dual energy of the degree-zero component. -/
theorem hMinusEnergy_degreeZero_real {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (phi : ℝ → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (((1 - Real.sin (p 0) * Estimates.torusIntegral phi : ℝ) : ℂ)
          • Manhattan.walshL2 ∅)
      = (1 - Real.sin (p 0) * Estimates.torusIntegral phi) ^ 2
          / (lambda + Operator.theta p) := by
  rw [hMinusEnergy_degreeZero hlambda p]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The Version 4 degree-zero coefficient.**  For the purely imaginary
degree-one competitor `f = -iφ`, the constant Walsh coefficient of the residual
`1 - A_p f` is `1 - sin(p₁) ∫ φ dm`, the numerator of Move 1. -/
theorem inner_empty_residual_degreeOne (p : Fin 2 → ℝ) (phi : ℝ → ℝ)
    (hf : MemLp (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    inner ℂ (Manhattan.walshL2 ∅) (Manhattan.walshL2 ∅ -
        Manhattan.concreteFiberA p (Manhattan.degreeOneRealFrequencySynthesis
          Manhattan.Axis.horizontal (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) hf))
      = ((1 - Real.sin (p 0) * Estimates.torusIntegral phi : ℝ) : ℂ) := by
  have hlow := Energy.dStarZero_neg_I_mul p phi hf
  have hneg := Manhattan.Glue.loweringCoefficient_eq_neg_inner p
    (Manhattan.degreeOneRealFrequencySynthesis Manhattan.Axis.horizontal
      (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) hf) ∅
  rw [hlow] at hneg
  have hA : inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.concreteFiberA p (Manhattan.degreeOneRealFrequencySynthesis
        Manhattan.Axis.horizontal (fun r => -Complex.I * ((phi r : ℝ) : ℂ)) hf))
      = ((Real.sin (p 0) * Estimates.torusIntegral phi : ℝ) : ℂ) := by
    have h2 : (((-(Real.sin (p 0) * Estimates.torusIntegral phi)) : ℝ) : ℂ)
        = -(((Real.sin (p 0) * Estimates.torusIntegral phi : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h2] at hneg
    exact (neg_inj.mp hneg).symm
  rw [inner_sub_right, hA, Manhattan.inner_walshL2, if_pos rfl]
  push_cast
  ring

/-! ## The competitor energy of Steps 3-4, in the density Move 1 consumes -/

/-- Joint measurability of `(β, r) ↦ w(r)²/(B(r,β) + σ(r,β))`. -/
theorem measurable_rowQuotient {kappa delta : ℝ} {q : Estimates.Parameters}
    {w : ℝ → ℝ} (hmw : Measurable w) :
    Measurable fun z : ℝ × ℝ =>
      w z.2 ^ 2 / (Estimates.correctionB q z.2 z.1 + paritySigma kappa delta z.2 z.1) := by
  have hnum : Measurable fun z : ℝ × ℝ => w z.2 ^ 2 :=
    (hmw.comp measurable_snd).pow_const 2
  have hB : Measurable fun z : ℝ × ℝ => Estimates.correctionB q z.2 z.1 := by
    unfold Estimates.correctionB Estimates.dispersion
    fun_prop
  have hswap : Measurable fun z : ℝ × ℝ => ((z.2, z.1) : ℝ × ℝ) :=
    measurable_snd.prodMk measurable_fst
  have hsig : Measurable fun z : ℝ × ℝ => paritySigma kappa delta z.2 z.1 :=
    Measurable.comp (f := fun z : ℝ × ℝ => ((z.2, z.1) : ℝ × ℝ))
      (g := fun z : ℝ × ℝ => paritySigma kappa delta z.1 z.2)
      (paritySigma_measurable kappa delta) hswap
  exact hnum.div (hB.add hsig)

/-- **The competitor energy of Steps 3 and 4, evaluated.**  For the parity
competitor `v = w/(B + σ)` of `parityProfileV` with a row profile `w` that does
not depend on the column frequency, the sum of the degree-three energy density
`σ v²` and the degree-two residual density `(w - σ v)²/B` is exactly the Move 1
density `w(r)² J₃(r)`, `J₃(r) = ∫ dm(β)/(B(r,β) + σ(r,β))`.

The pointwise step is `Manhattan.V4.scalarCompletion_eq`, applied at
the minimizer; the analytic step is the interchange of the two torus integrals,
legitimate because the integrand is bounded by `‖w‖_∞²/λ`. -/
theorem parityCompetitor_density_eq {kappa delta Kw : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    {w : ℝ → ℝ} (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma kappa delta r beta
            * parityV q kappa delta (fun r' _ => w r') r beta ^ 2
          + (w r - paritySigma kappa delta r beta
              * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
            / Estimates.correctionB q r beta))
      = Estimates.torusIntegral (fun r => w r ^ 2 *
          Estimates.torusIntegral (fun b =>
            (Estimates.correctionB q r b + paritySigma kappa delta r b)⁻¹)) := by
  have hKw : 0 ≤ Kw := le_trans (abs_nonneg _) (hbw 0)
  have hBpos : ∀ r beta : ℝ, 0 < Estimates.correctionB q r beta :=
    fun r beta => lt_of_lt_of_le hlam (correctionB_ge q r beta)
  have hsig : ∀ r beta : ℝ, 0 ≤ paritySigma kappa delta r beta :=
    fun r beta => paritySigma_nonneg hkappa hdelta r beta
  -- (1) the pointwise scalar completion at the minimizer
  have hfun : (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma kappa delta r beta
            * parityV q kappa delta (fun r' _ => w r') r beta ^ 2
          + (w r - paritySigma kappa delta r beta
              * parityV q kappa delta (fun r' _ => w r') r beta) ^ 2
            / Estimates.correctionB q r beta))
      = fun beta => Estimates.torusIntegral (fun r =>
          w r ^ 2 / (Estimates.correctionB q r beta
            + paritySigma kappa delta r beta)) := by
    funext beta
    congr 1
    funext r
    have hV : parityV q kappa delta (fun r' _ => w r') r beta
        = w r / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := rfl
    rw [hV]
    exact scalarCompletion_eq (hBpos r beta) (hsig r beta)
  rw [hfun]
  -- (2) the interchange
  have hbound : ∀ x y : ℝ, |w y ^ 2 / (Estimates.correctionB q y x
      + paritySigma kappa delta y x)| ≤ Kw ^ 2 / q.lambda := by
    intro x y
    have hden : q.lambda ≤ Estimates.correctionB q y x + paritySigma kappa delta y x :=
      lambda_le_correctionB_add_paritySigma hkappa hdelta y x
    have hdenpos : 0 < Estimates.correctionB q y x + paritySigma kappa delta y x := by
      linarith
    have hnum : w y ^ 2 ≤ Kw ^ 2 := by nlinarith [hbw y, abs_nonneg (w y), sq_abs (w y)]
    rw [abs_of_nonneg (by positivity)]
    calc w y ^ 2 / (Estimates.correctionB q y x + paritySigma kappa delta y x)
        ≤ Kw ^ 2 / (Estimates.correctionB q y x + paritySigma kappa delta y x) := by
          gcongr
      _ ≤ Kw ^ 2 / q.lambda := by gcongr
  rw [torusIntegral_swap_of_bounded
    (F := fun beta r => w r ^ 2 / (Estimates.correctionB q r beta
      + paritySigma kappa delta r beta))
    (measurable_rowQuotient hmw) hbound]
  -- (3) the inner integral
  congr 1
  funext r
  have hrw : (fun beta => w r ^ 2 / (Estimates.correctionB q r beta
        + paritySigma kappa delta r beta))
      = fun beta => w r ^ 2 * (Estimates.correctionB q r beta
        + paritySigma kappa delta r beta)⁻¹ := by
    funext beta
    rw [div_eq_mul_inv]
  rw [hrw, Estimates.torusIntegral_smul_left]

/-- The degree-three half alone: `σ v²` integrates to at most the same Move 1
density, because the degree-two residual density `(w - σ v)²/B` is nonnegative.
This is the form the operator estimate `operatorEstimate_parityKernel` produces. -/
theorem paritySigmaEnergy_le_density {kappa delta Kw : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    {w : ℝ → ℝ} (hmw : Measurable w) (hbw : ∀ r, |w r| ≤ Kw) :
    Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
        paritySigma kappa delta r beta
          * parityV q kappa delta (fun r' _ => w r') r beta ^ 2))
      ≤ Estimates.torusIntegral (fun r => w r ^ 2 *
          Estimates.torusIntegral (fun b =>
            (Estimates.correctionB q r b + paritySigma kappa delta r b)⁻¹)) := by
  have hKw : 0 ≤ Kw := le_trans (abs_nonneg _) (hbw 0)
  have hBpos : ∀ r beta : ℝ, 0 < Estimates.correctionB q r beta :=
    fun r beta => lt_of_lt_of_le hlam (correctionB_ge q r beta)
  have hsig : ∀ r beta : ℝ, 0 ≤ paritySigma kappa delta r beta :=
    fun r beta => paritySigma_nonneg hkappa hdelta r beta
  have hbound : ∀ x y : ℝ, |w y ^ 2 / (Estimates.correctionB q y x
      + paritySigma kappa delta y x)| ≤ Kw ^ 2 / q.lambda := by
    intro x y
    have hden : q.lambda ≤ Estimates.correctionB q y x + paritySigma kappa delta y x :=
      lambda_le_correctionB_add_paritySigma hkappa hdelta y x
    have hdenpos : 0 < Estimates.correctionB q y x + paritySigma kappa delta y x := by
      linarith
    have hnum : w y ^ 2 ≤ Kw ^ 2 := by nlinarith [hbw y, abs_nonneg (w y), sq_abs (w y)]
    rw [abs_of_nonneg (by positivity)]
    calc w y ^ 2 / (Estimates.correctionB q y x + paritySigma kappa delta y x)
        ≤ Kw ^ 2 / (Estimates.correctionB q y x + paritySigma kappa delta y x) := by
          gcongr
      _ ≤ Kw ^ 2 / q.lambda := by gcongr
  -- the pointwise bound `σ v² ≤ w²/(B + σ)`
  have hpt : ∀ beta r : ℝ, paritySigma kappa delta r beta
      * parityV q kappa delta (fun r' _ => w r') r beta ^ 2
      ≤ w r ^ 2 / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
    intro beta r
    have hV : parityV q kappa delta (fun r' _ => w r') r beta
        = w r / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := rfl
    have heq := scalarCompletion_eq (B := Estimates.correctionB q r beta)
      (sigma := paritySigma kappa delta r beta) (w := w r) (hBpos r beta) (hsig r beta)
    have hres : 0 ≤ (w r - paritySigma kappa delta r beta
        * (w r / (Estimates.correctionB q r beta + paritySigma kappa delta r beta))) ^ 2
        / Estimates.correctionB q r beta := by
      have := hBpos r beta
      positivity
    rw [hV]
    linarith
  -- the inner integral
  have hinner : ∀ beta : ℝ,
      Estimates.torusIntegral (fun r => paritySigma kappa delta r beta
          * parityV q kappa delta (fun r' _ => w r') r beta ^ 2)
        ≤ Estimates.torusIntegral (fun r => w r ^ 2
            / (Estimates.correctionB q r beta + paritySigma kappa delta r beta)) := by
    intro beta
    refine Estimates.torusIntegral_mono'
      (fun r => mul_nonneg (hsig r beta) (sq_nonneg _)) ?_ (fun r => hpt beta r)
    refine Estimates.integrableOn_torus_of_bounded (C := Kw ^ 2 / q.lambda) ?_
      (fun r => hbound beta r)
    have hmz := measurable_rowQuotient (kappa := kappa) (delta := delta) (q := q) hmw
    exact hmz.comp (measurable_const.prodMk measurable_id)
  -- the outer integral
  have houter : Estimates.torusIntegral (fun beta => Estimates.torusIntegral
        (fun r => paritySigma kappa delta r beta
          * parityV q kappa delta (fun r' _ => w r') r beta ^ 2))
      ≤ Estimates.torusIntegral (fun beta => Estimates.torusIntegral
          (fun r => w r ^ 2
            / (Estimates.correctionB q r beta + paritySigma kappa delta r beta))) := by
    refine Estimates.torusIntegral_mono' ?_ ?_ hinner
    · intro beta
      exact Estimates.torusIntegral_nonneg' fun r =>
        mul_nonneg (hsig r beta) (sq_nonneg _)
    · refine Estimates.integrableOn_torus_of_bounded (C := Kw ^ 2 / q.lambda) ?_ ?_
      · exact (Manhattan.Glue.stronglyMeasurable_torusIntegral
          (measurable_rowQuotient (kappa := kappa) (delta := delta)
            (q := q) hmw).stronglyMeasurable).measurable
      · intro beta
        exact Manhattan.Glue.abs_torusIntegral_le (C := Kw ^ 2 / q.lambda)
          (fun r => hbound beta r)
  refine houter.trans (le_of_eq ?_)
  rw [torusIntegral_swap_of_bounded
    (F := fun beta r => w r ^ 2 / (Estimates.correctionB q r beta
      + paritySigma kappa delta r beta))
    (measurable_rowQuotient hmw) hbound]
  congr 1
  funext r
  have hrw : (fun beta => w r ^ 2 / (Estimates.correctionB q r beta
        + paritySigma kappa delta r beta))
      = fun beta => w r ^ 2 * (Estimates.correctionB q r beta
        + paritySigma kappa delta r beta)⁻¹ := by
    funext beta
    rw [div_eq_mul_inv]
  rw [hrw, Estimates.torusIntegral_smul_left]

/-! ## The composed Version 4 competitor cost -/

/-- The fibre integral `J₃(r) = ∫ dm(β)/(B(r,β) + σ(r,β))` of the Version 4
competitor. -/
def parityFibreJ (q : Estimates.Parameters) (kappa delta r : ℝ) : ℝ :=
  Estimates.torusIntegral fun b =>
    (Estimates.correctionB q r b + paritySigma kappa delta r b)⁻¹

theorem parityFibreJ_nonneg {kappa delta : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta) (r : ℝ) :
    0 ≤ parityFibreJ q kappa delta r := by
  refine Estimates.torusIntegral_nonneg' fun b => inv_nonneg.mpr ?_
  have := lambda_le_correctionB_add_paritySigma (q := q) hkappa hdelta r b
  linarith

theorem parityFibreJ_le {kappa delta : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta) (r : ℝ) :
    parityFibreJ q kappa delta r ≤ q.lambda⁻¹ := by
  refine le_trans (le_abs_self _)
    (Manhattan.Glue.abs_torusIntegral_le (C := q.lambda⁻¹) fun b => ?_)
  have hden := lambda_le_correctionB_add_paritySigma (q := q) hkappa hdelta r b
  have hdenpos : 0 < Estimates.correctionB q r b + paritySigma kappa delta r b := by
    linarith
  rw [abs_of_nonneg (inv_nonneg.mpr hdenpos.le)]
  exact inv_anti₀ hlam hden

theorem parityFibreJ_measurable {kappa delta : ℝ} {q : Estimates.Parameters} :
    Measurable (parityFibreJ q kappa delta) := by
  have hB : Measurable fun z : ℝ × ℝ => Estimates.correctionB q z.1 z.2 := by
    unfold Estimates.correctionB Estimates.dispersion
    fun_prop
  have hmeas : Measurable fun z : ℝ × ℝ =>
      (Estimates.correctionB q z.1 z.2 + paritySigma kappa delta z.1 z.2)⁻¹ :=
    (hB.add (paritySigma_measurable kappa delta)).inv
  exact (Manhattan.Glue.stronglyMeasurable_torusIntegral
    hmeas.stronglyMeasurable).measurable

/-- `∫ dm(β)/(B + σ) ≤ (π² + π³κ/2)/(|r| √(log(1/|r|)))` on `Γ_δ`.  This is
The fibre integral composed with ingredient (d) of Move 1. -/
theorem parityFibreJ_le_weight {kappa delta r : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (hdr : Real.sqrt delta ≤ |r|) (hr1 : |r| ≤ 1 / 4) :
    parityFibreJ q kappa delta r
      ≤ (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
          / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  have hrpos : 0 < |r| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hdr
  have hdsq : delta ≤ |r| ^ 2 := by
    have h := Real.sq_sqrt hdelta.le
    nlinarith [hdr, Real.sqrt_nonneg delta]
  have h := parity_betaIntegral_le (kappa := kappa) (delta := delta)
    (lambda := q.lambda) (r := r) hkappa hdelta hdsq hlam hrpos hr1
  exact h

/-- **The composed Version 4 competitor cost.**  The degree-one cost
`C₁ ∫ (δ + r²) φ² dm` of estimate (4) together with `C₃` times the degree-three
energy `∫∫ σ v² dm dm` of the parity competitor is at most
`(C₁ + C₃(π² + π³κ/2)) ∫ q φ² dm`, `q(r) = |r|/√(log(1/|r|))`.

This composes `parity_betaIntegral_le`, the scalar completion at the
parity minimizer (`paritySigmaEnergy_le_density`) and Move 1
(`Energy.move1_energy_le`).  With `C₁ = 6` (estimate (4)) and `C₃ = 9`
(`operatorEstimate`) the constant is `6 + 9(π² + π³κ/2)`, and at `κ = 120` it is
`6 + 9π² + 540π³`. -/
theorem v4_competitor_cost_le
    {kappa delta r0 Kp C1 C3 : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta) (hr0 : r0 ≤ 1 / 4)
    (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3)
    {phi : ℝ → ℝ} (hmphi : Measurable phi) (hbphi : ∀ r, |phi r| ≤ Kp)
    (hsupp : ∀ r, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Manhattan.Estimates.torus)) :
    C1 * Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2)
        + C3 * Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
            paritySigma kappa delta r beta
              * parityV q kappa delta
                  (fun r' _ => Real.sin r' * phi r') r beta ^ 2))
      ≤ (C1 + C3 * (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2))
          * Estimates.torusIntegral (fun r => Energy.effectiveWeight r * phi r ^ 2) := by
  have hKp : 0 ≤ Kp := le_trans (abs_nonneg _) (hbphi 0)
  set w : ℝ → ℝ := fun r => Real.sin r * phi r with hwdef
  have hmw : Measurable w := Real.measurable_sin.mul hmphi
  have hbw : ∀ r, |w r| ≤ Kp := by
    intro r
    have h1 := Real.abs_sin_le_one r
    have h2 := hbphi r
    simp only [hwdef, abs_mul]
    nlinarith [abs_nonneg (Real.sin r), abs_nonneg (phi r)]
  -- (1) the degree-three energy is at most the Move 1 density
  have hsigma := paritySigmaEnergy_le_density (Kw := Kp) hlam hkappa hdelta hmw hbw
  have hTeq : Estimates.torusIntegral (fun r => w r ^ 2 *
      Estimates.torusIntegral (fun b =>
        (Estimates.correctionB q r b + paritySigma kappa delta r b)⁻¹))
      = Estimates.torusIntegral (fun r => w r ^ 2 * parityFibreJ q kappa delta r) := rfl
  rw [hTeq] at hsigma
  -- (2) Move 1 at `J = C₃ · J₃`
  have hJ0 : ∀ r, 0 ≤ C3 * parityFibreJ q kappa delta r := fun r =>
    mul_nonneg hC3 (parityFibreJ_nonneg hlam hkappa hdelta r)
  have hJ : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 →
      C3 * parityFibreJ q kappa delta r
        ≤ C3 * (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
            / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
    intro r hdr hrr0
    have h := parityFibreJ_le_weight hlam hkappa hdelta hdr (le_trans hrr0 hr0)
    have hmul := mul_le_mul_of_nonneg_left h hC3
    calc C3 * parityFibreJ q kappa delta r
        ≤ C3 * ((Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
            / (|r| * Real.sqrt (Real.log (1 / |r|)))) := hmul
      _ = C3 * (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
            / (|r| * Real.sqrt (Real.log (1 / |r|))) := by ring
  have hmove1 := Energy.move1_energy_le (delta := delta) (C1 := C1)
    (C2 := C3 * (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)) (r0 := r0)
    phi (fun r => C3 * parityFibreJ q kappa delta r) hC1
    (by positivity) hdelta hr0 hsupp hJ hJ0 hint
  -- (3) additivity of the two densities
  have hf : Measurable fun r => C1 * ((delta + r ^ 2) * phi r ^ 2) := by
    fun_prop
  have hg : Measurable fun r =>
      Real.sin r ^ 2 * (C3 * parityFibreJ q kappa delta r) * phi r ^ 2 := by
    have := parityFibreJ_measurable (kappa := kappa) (delta := delta) (q := q)
    fun_prop
  have hfC : ∀ r, |C1 * ((delta + r ^ 2) * phi r ^ 2)|
      ≤ C1 * ((delta + 1 / 16) * Kp ^ 2) := by
    intro r
    by_cases hmem : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
    · have hr1 : |r| ≤ 1 / 4 := le_trans hmem.2 hr0
      have hrsq : r ^ 2 ≤ 1 / 16 := by nlinarith [sq_abs r, abs_nonneg r]
      have hphisq : phi r ^ 2 ≤ Kp ^ 2 := by
        nlinarith [hbphi r, abs_nonneg (phi r), sq_abs (phi r)]
      rw [abs_of_nonneg (by positivity)]
      have h1 : (delta + r ^ 2) * phi r ^ 2 ≤ (delta + 1 / 16) * Kp ^ 2 := by
        nlinarith [sq_nonneg r, sq_nonneg (phi r), hdelta.le]
      exact mul_le_mul_of_nonneg_left h1 hC1
    · rw [hsupp r hmem]
      have : (0:ℝ) ≤ C1 * ((delta + 1 / 16) * Kp ^ 2) := by positivity
      simpa using this
  have hgC : ∀ r, |Real.sin r ^ 2 * (C3 * parityFibreJ q kappa delta r) * phi r ^ 2|
      ≤ C3 * q.lambda⁻¹ * Kp ^ 2 := by
    intro r
    have hJr := parityFibreJ_le hlam hkappa hdelta r
    have hJr0 := parityFibreJ_nonneg hlam hkappa hdelta r
    have hsin1 : Real.sin r ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin r, Real.sin_le_one r]
    have hsin0 : (0:ℝ) ≤ Real.sin r ^ 2 := sq_nonneg _
    have hphisq : phi r ^ 2 ≤ Kp ^ 2 := by
      nlinarith [hbphi r, abs_nonneg (phi r), sq_abs (phi r)]
    have hphi0 : (0:ℝ) ≤ phi r ^ 2 := sq_nonneg _
    rw [abs_of_nonneg (by positivity)]
    have hstep : Real.sin r ^ 2 * (C3 * parityFibreJ q kappa delta r)
        ≤ 1 * (C3 * q.lambda⁻¹) := by
      have h1 : C3 * parityFibreJ q kappa delta r ≤ C3 * q.lambda⁻¹ :=
        mul_le_mul_of_nonneg_left hJr hC3
      exact mul_le_mul hsin1 h1 (by positivity) zero_le_one
    calc Real.sin r ^ 2 * (C3 * parityFibreJ q kappa delta r) * phi r ^ 2
        ≤ 1 * (C3 * q.lambda⁻¹) * Kp ^ 2 := by
          exact mul_le_mul hstep hphisq hphi0 (by positivity)
      _ = C3 * q.lambda⁻¹ * Kp ^ 2 := by ring
  have hadd := torusIntegral_add_of_bounded hf hg hfC hgC
  rw [Estimates.torusIntegral_smul_left C1 (fun r => (delta + r ^ 2) * phi r ^ 2)] at hadd
  have hg2 : (fun r => Real.sin r ^ 2 * (C3 * parityFibreJ q kappa delta r) * phi r ^ 2)
      = fun r => C3 * (w r ^ 2 * parityFibreJ q kappa delta r) := by
    funext r
    simp only [hwdef]
    ring
  rw [hg2, Estimates.torusIntegral_smul_left C3
    (fun r => w r ^ 2 * parityFibreJ q kappa delta r)] at hadd
  rw [hadd] at hmove1
  have hC3mul : C3 * Estimates.torusIntegral (fun beta => Estimates.torusIntegral (fun r =>
      paritySigma kappa delta r beta
        * parityV q kappa delta (fun r' _ => Real.sin r' * phi r') r beta ^ 2))
      ≤ C3 * Estimates.torusIntegral
          (fun r => w r ^ 2 * parityFibreJ q kappa delta r) :=
    mul_le_mul_of_nonneg_left hsigma hC3
  linarith [hmove1, hC3mul]

end Manhattan.V4
