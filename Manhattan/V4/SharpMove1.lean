/-
Move 1 at the sharp operator coefficient.

`Manhattan.V4.v4_move1_objective` runs the competitor at the shared constant
`κ = 120` with the Move 1 coefficient `C₃ = 40`.  The operator estimate behind
it has coefficient `A = 9`, and `40 = 4·9 + 4`.

`Manhattan.V4.operatorEstimate_parityKernel_sharp` gives `A = 1`, at `κ = 14`.
Feeding that through the same assembly gives `C₃ = 4·21 + 4 = 88` and the
logarithmic weight at `κ = 14`.
-/
import Manhattan.V4.Move1
import Manhattan.V4.Move2Supply
import Manhattan.V4.SharpConstant

noncomputable section

open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.Glue Manhattan.Operator Manhattan.V4.Frequency

/-- A constant admissible in the column bound (6) at the shared constant `κ = 14`:
`∫ dm(β)/(B + σ) ≤ C_β/(|r| √(log(1/|r|)))` on the annulus `√δ ≤ |r| ≤ 1/4`. -/
def BetaColumnBound (kappa Cb : ℝ) : Prop :=
  ∀ (q : Estimates.Parameters) (d r : ℝ), 0 < q.lambda → 0 < d →
    Real.sqrt d ≤ |r| → |r| ≤ 1 / 4 →
      parityFibreJ q kappa d r ≤ Cb / (|r| * Real.sqrt (Real.log (1 / |r|)))

/-- The column bound with the inner zone bounded rather than integrated. -/
theorem betaColumnBound_classic {kappa : ℝ} (hkappa : 0 < kappa) :
    BetaColumnBound kappa (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2) :=
  fun _ _ _ hq hd h1 h2 => parityFibreJ_le_weight hq hkappa hd h1 h2

/-- An admissible coefficient in the operator estimate (OP) at the shared
constant `κ`: the degree-three and degree-four sector forms of the parity
competitor are at most `A` times its logarithmic energy. -/
def OperatorCoefficient (kappa A : ℝ) : Prop :=
  ∀ (q : Estimates.Parameters) (hlambda : 0 < q.lambda) (delta : ℝ) (hdelta0 : 0 < delta),
    q.lambda ≤ delta → ∀ (p : Fin 2 → ℝ), |p 1| ≤ delta →
    ∀ (hkappa : 0 < kappa) (v : ParityProfile),
      Manhattan.Glue.sectorHThreeForm q.lambda p
          (rawWalsh p (torusBounded₃_parityKernel hkappa hdelta0 v))
        + Manhattan.Glue.sectorDFourForm hlambda p
          (rawWalsh p (torusBounded₃_parityKernel hkappa hdelta0 v))
        ≤ A * Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
            paritySigma kappa delta r beta * v.toFun r beta ^ 2

/-- (OP) at `κ = 14` with coefficient `21`. -/
theorem operatorCoefficient_fourteen : OperatorCoefficient 14 21 :=
  fun _ hlambda _ hdelta0 hdelta p hp₂ _ v =>
    operatorEstimate_parityKernel_sharp_fourteen hlambda hdelta0 hdelta p hp₂ v

/-- (OP) at `κ = 291` with coefficient `1`. -/
theorem operatorCoefficient_291 : OperatorCoefficient 291 1 :=
  fun _ hlambda _ hdelta0 hdelta p hp₂ _ v => by
    have h := operatorEstimate_parityKernel_sharp hlambda hdelta0 hdelta p hp₂ v
    linarith

theorem v4_move1_objective_of {kappa A Cb : ℝ} (hkappa : 0 < kappa) (hA : 0 ≤ A)
    (hOp : OperatorCoefficient kappa A) (hCb : 0 ≤ Cb) (hB : BetaColumnBound kappa Cb)
    {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) {delta r0 : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hlamdelta : q.lambda ≤ delta)
    (hr014 : r0 ≤ 1 / 4) (hsqle : Real.sqrt delta ≤ r0)
    (hmud : q.lambda + Estimates.dispersion (p 0) ≤ delta ^ 2)
    (hp2 : |p 1| ≤ delta) (t : ℝ) :
    ∃ g : Manhattan.WalshL2,
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda g
          + (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
              (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p g)
        ≤ (1 - Real.sin (p 0) * (t * profileMass r0 delta)) ^ 2
              / (q.lambda + Operator.theta p)
            + (60 + (4 * A + 4) * Cb) * (t ^ 2 * profileMass r0 delta) := by
  classical
  have hpi := Real.pi_pos
  have hr01 : r0 < 1 := lt_of_le_of_lt hr014 (by norm_num)
  have hr0pi : r0 < Real.pi := by linarith [Real.pi_gt_three]
  have hsqpos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
  have h120 : (0:ℝ) < kappa := hkappa
  have hmu : 0 < q.lambda + Estimates.dispersion (p 0) :=
    add_pos_of_pos_of_nonneg hlam (Estimates.dispersion_nonneg (p 0))
  have hsinsq : Real.sin (p 0) ^ 2 ≤ 2 * (q.lambda + Estimates.dispersion (p 0)) := by
    have := sin_sq_le_two_dispersion (p 0)
    linarith
  -- the profile
  set phi : ℝ → ℝ := perProfile r0 delta t with hphidef
  set Kp : ℝ := |t| * (Real.sqrt (-Real.log (Real.sqrt delta)) / Real.sqrt delta) with hKpdef
  have hmphi : Measurable phi := measurable_perProfile r0 delta t
  have hbphi : ∀ r, |phi r| ≤ Kp := fun r => perProfile_abs_le hsqpos hsqle hr01 t r
  have hphieven : ∀ r, phi (-r) = phi r := perProfile_even r0 delta t
  have hphiper : Function.Periodic phi (2 * Real.pi) := perProfile_periodic r0 delta t
  have hsupp : ∀ r ∈ Estimates.torus,
      ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0 :=
    fun r hr h => perProfile_supp_torus hr h
  have hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus) :=
    integrable_effectiveWeight_perProfile hsqpos hsqle hr01 hr0pi t
  -- the degree-one profile
  set g : ℝ → ℂ := fun x => -Complex.I * ((phi x : ℝ) : ℂ) with hgdef
  have hgmeas : Measurable g := measurable_const.mul (Complex.measurable_ofReal.comp hmphi)
  have hgnorm : ∀ r, ‖g r‖ = |phi r| := by
    intro r
    rw [hgdef]
    simp only
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hgb : ∀ r, ‖g r‖ ≤ Kp := fun r => by rw [hgnorm r]; exact hbphi r
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro x
    show -Complex.I * ((phi (x + 2 * Real.pi) : ℝ) : ℂ) = -Complex.I * ((phi x : ℝ) : ℂ)
    rw [hphiper x]
  have hg : MemLp g 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    memLp_neg_I_mul hmphi hbphi
  set cco := fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 g hg)) with hccodef
  -- the parity competitor
  set W : ParityProfile := sineProfile phi hmphi Kp hbphi hphieven hphiper with hWdef
  set vp : ParityProfile := parityProfileV hlam h120 hdelta W with hvpdef
  set v : ParityProfile := scaleProfile (Real.sqrt 2) vp with hvdef
  have hK := torusBounded₃_parityKernel h120 hdelta v
  set kc := Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hK) with hkcdef
  have hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi) :=
    scaleProfile_periodic_col (Real.sqrt 2) vp
      (parityProfileV_periodic_col hlam h120 hdelta W (fun _ _ => rfl))
  -- (P3)
  have hkTwoRow : Manhattan.type112DStarTwoRow p kc = 0 :=
    type112DStarTwoRow_rawShiftTwist hK
      (fun r r' b => parityKernel_neg_col v r r' b) p
  -- the degree-zero coefficient
  have hcc := inner_empty_residual_shifted p hg kc
  refine ⟨Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco
    + Manhattan.type112WalshSynthesis kc, ?_⟩
  refine le_trans (objective_le_v4Move1 hlam p cco kc hkTwoRow hcc) ?_
  -- the two substitution integrals
  have hMass : Estimates.torusIntegral phi = t * profileMass r0 delta :=
    torusIntegral_perProfile r0 delta t
  set E := Estimates.torusIntegral (fun r => Energy.effectiveWeight r * phi r ^ 2) with hEdef
  have hEval : E = t ^ 2 * profileMass r0 delta :=
    torusIntegral_effectiveWeight_perProfile hsqpos hr01 hr0pi t
  set Wr : ℝ → ℝ := fun r => Real.sin r * phi r with hWrdef
  have hmw : Measurable Wr := Real.measurable_sin.mul hmphi
  have hbw : ∀ r, |Wr r| ≤ Kp := by
    intro r
    have h1 := Real.abs_sin_le_one r
    have h2 := hbphi r
    have hKp0 : 0 ≤ Kp := le_trans (abs_nonneg _) (hbphi 0)
    rw [hWrdef]
    simp only
    rw [abs_mul]
    nlinarith [abs_nonneg (Real.sin r), abs_nonneg (phi r)]
  set JJ := Estimates.torusIntegral (fun r => Wr r ^ 2 * parityFibreJ q kappa delta r) with hJJdef
  -- (1) the degree-one energy
  have hE1 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
      (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco) ≤ 6 * E := by
    have heq : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy q.lambda
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco)
        = Estimates.torusIntegral (fun r =>
            (q.lambda + Estimates.dispersion (p 0) + Estimates.dispersion r) * ‖g r‖ ^ 2) :=
      hEnergy_degreeOneRowShift q.lambda p g hg
    rw [heq]
    have hcongr : (fun r => (q.lambda + Estimates.dispersion (p 0)
          + Estimates.dispersion r) * ‖g r‖ ^ 2)
        = fun r => (q.lambda + Estimates.dispersion (p 0)
            + Estimates.dispersion r) * phi r ^ 2 := by
      funext r
      rw [hgnorm r, sq_abs]
    rw [hcongr]
    exact degreeOne_cost_le hmu hdelta hdelta1 hmud hr014 hsupp hint
  -- (2) the two-row sector
  have hE2 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
        (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))))
      ≤ 12 * E := by
    have h := hMinusEnergy_twoRow_le hlam p g hg
    have hcongr : (fun r => ‖g r‖ ^ 2) = fun r => phi r ^ 2 := by
      funext r
      rw [hgnorm r, sq_abs]
    rw [hcongr] at h
    have h2 := twoRow_cost_le (mu := q.lambda + Estimates.dispersion (p 0))
      (s := Real.sin (p 0)) hmu hdelta hdelta1 hmud hsinsq hr014 hsupp hint
    rw [Estimates.torusIntegral_smul_left] at h2
    have hJ0 : (0:ℝ) ≤ Real.sin (p 0) ^ 2
        / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
          * (q.lambda + Estimates.dispersion (p 0) + 2)) := by positivity
    have hkey : 4 * (Real.sin (p 0) ^ 2
          / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
            * (q.lambda + Estimates.dispersion (p 0) + 2)))
        * Estimates.torusIntegral (fun r => phi r ^ 2) ≤ 12 * E := by
      have hrw : 2 * Real.sin (p 0) ^ 2
            / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
              * (q.lambda + Estimates.dispersion (p 0) + 2))
          = 2 * (Real.sin (p 0) ^ 2
            / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
              * (q.lambda + Estimates.dispersion (p 0) + 2))) := by ring
      rw [hrw] at h2
      linarith
    linarith
  -- (3) the degree-three cost
  have hE3 : sectorHThreeForm q.lambda p (Manhattan.type112WalshSynthesis kc)
      + sectorDFourForm hlam p (Manhattan.type112WalshSynthesis kc) ≤ 2 * A * JJ := by
    have hop := hOp q hlam delta hdelta hlamdelta p hp2 h120 v
    have hsc := paritySigmaEnergy_scaled_le (q := q) (kappa := kappa) (delta := delta)
      hlam h120 hdelta hmw hbw
    have hveq : (fun beta => Estimates.torusIntegral (fun r =>
          paritySigma kappa delta r beta * v.toFun r beta ^ 2))
        = fun beta => Estimates.torusIntegral (fun r =>
          paritySigma kappa delta r beta
            * (Real.sqrt 2 * parityV q kappa delta (fun r' _ => Wr r') r beta) ^ 2) := rfl
    rw [hveq] at hop
    have hrw : rawWalsh p (torusBounded₃_parityKernel h120 hdelta v)
        = Manhattan.type112WalshSynthesis kc := rfl
    rw [hrw] at hop
    have hscA := mul_le_mul_of_nonneg_left hsc hA
    have hJJeq : Estimates.torusIntegral
        (fun r => Wr r ^ 2 * parityFibreJ q kappa delta r) = JJ := rfl
    rw [hJJeq] at hscA
    linarith
  -- (4) the mixed sector
  have hE4 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
      (Manhattan.type12WalshSynthesis
        (Manhattan.type12WalshAnalysis (walshRaise p
            (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal cco))
          - Manhattan.type112DStarMixed p kc)) ≤ JJ := by
    have hden := hMinusEnergy_v4Mixed_density (q := q) hlam h120 hdelta v hvcol
      hgmeas hgb hgper hg p
    rw [hden]
    have hcongr : (fun r => Estimates.torusIntegral (fun beta =>
          ‖v4MixedSymbol kappa delta v.toFun g r beta‖ ^ 2 / Estimates.correctionB q r beta))
        = fun r => Estimates.torusIntegral (fun beta =>
          (Wr r - paritySigma kappa delta r beta
              * parityV q kappa delta (fun r' _ => Wr r') r beta) ^ 2
            / Estimates.correctionB q r beta) := by
      funext r
      congr 1
      funext beta
      have hvv : v.toFun r beta
          = Real.sqrt 2 * parityV q kappa delta (fun r' _ => Wr r') r beta := rfl
      rw [norm_v4MixedSymbol_sq kappa delta v phi r beta, hvv,
        inv_sqrt_two_mul_scaled]
    rw [hcongr]
    exact mixedResidual_integral_le hlam h120 hdelta hmw hbw
  -- (5) the Move 1 density
  have hE5 : (4 * A + 4) * JJ ≤ (4 * A + 4) * Cb * E := by
    have h := v4_cost_le_of (q := q) (kappa := kappa) (delta := delta) (r0 := r0)
      (C1 := 0) (C3 := 4 * A + 4) hlam h120 hdelta hr014 le_rfl (by linarith) hCb
      (fun r h1 h2 => hB q delta r hlam hdelta h1 h2) hsupp hint
    have hJJeq : JJ = Estimates.torusIntegral (fun r =>
        Real.sin r ^ 2 * parityFibreJ q kappa delta r * phi r ^ 2) := by
      rw [hJJdef]
      congr 1
      funext r
      rw [hWrdef]
      simp only
      rw [mul_pow]
      ring
    rw [hJJeq]
    have h0 : (0:ℝ) * Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2) = 0 := by
      ring
    rw [h0, zero_add, zero_add] at h
    linarith
  rw [hMass] at hcc ⊢
  rw [hEval] at hE1 hE2 hE5
  linarith

/-! ## The sharp constant, and the Move 2 supply at it -/

/-- `60 + 88 (π² + π³·14/2) = 20,028.4`, against `v4Constant = 74,869.8`. -/
def v4ConstantSharp : ℝ := 60 + 88 * (Real.pi ^ 2 + Real.pi ^ 3 * 14 / 2)

theorem v4ConstantSharp_pos : 0 < v4ConstantSharp := by
  unfold v4ConstantSharp
  have := Real.pi_pos
  positivity

theorem v4_move1_at_of {kappa A Cb : ℝ} (hkappa : 0 < kappa) (hA : 0 ≤ A)
    (hOp : OperatorCoefficient kappa A) (hCb : 0 ≤ Cb) (hB : BetaColumnBound kappa Cb)
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1)
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
            + (60 + (4 * A + 4) * Cb)
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
  obtain ⟨g, hg⟩ := v4_move1_objective_of hkappa hA hOp hCb hB (q := v4Parameters lambda) hlambda p
    hdelta hdelta1 hlamdelta hr014 hsqle hmud hp2 t
  exact ⟨g, hg⟩

theorem v4Move2Supply_proved_of {kappa A Cb : ℝ} (hkappa : 0 < kappa) (hA : 0 ≤ A)
    (hOp : OperatorCoefficient kappa A) (hCb : 0 ≤ Cb) (hB : BetaColumnBound kappa Cb)
    {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 (60 + (4 * A + 4) * Cb) := by
  have hCpos : (0:ℝ) < 60 + (4 * A + 4) * Cb := by nlinarith
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
    exact v4_move2_at' hCpos hlambda p hr0 hr014 hle
      (fun t => v4_move1_at_of hkappa hA hOp hCb hB hlambda hlambda1 p hr0 hr014 hp0abs hle t)
  · have ha : Operator.maxFrequency p = |p 1| := max_eq_right hbr
    refine ⟨Real.sin (p 1), hjordan (p 1) ha.symm, ?_⟩
    refine v4_move2_at' hCpos hlambda p hr0 hr014 hle ?_
    intro t
    have hswap : Operator.maxFrequency (axisSwapFrequency p) = Operator.maxFrequency p :=
      axisSwap_maxFrequency p
    have hth : Operator.theta (axisSwapFrequency p) = Operator.theta p := axisSwap_theta p
    have hle' : Real.sqrt lambda + Operator.maxFrequency (axisSwapFrequency p) ≤ r0 ^ 4 := by
      rw [hswap]; exact hle
    have h0' : |axisSwapFrequency p 0| ≤ Real.pi := by
      rw [axisSwapFrequency_zero]; exact hp1abs
    have hm := v4_move1_at_of hkappa hA hOp hCb hB hlambda hlambda1 (axisSwapFrequency p) hr0 hr014 h0' hle' t
    rw [hswap, hth, axisSwapFrequency_zero] at hm
    exact objective_of_axisSwap hlambda p hm

/-! ## The unconditional consequences at the sharp constant -/

/-- The Version 4 fixed-frequency bound at the sharp constant. -/
theorem v4Move2Supply_proved_sharp {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 v4ConstantSharp := by
  have h := v4Move2Supply_proved_of (kappa := 14) (A := 21) (by norm_num) (by norm_num)
    operatorCoefficient_fourteen (by positivity)
    (betaColumnBound_classic (by norm_num)) hr0 hr014
  have heq : 60 + (4 * (21:ℝ) + 4) * (Real.pi ^ 2 + Real.pi ^ 3 * 14 / 2)
      = v4ConstantSharp := by unfold v4ConstantSharp; ring
  rwa [heq] at h

theorem v4FrequencyBound_proved_sharp :
    Frequency.V4FrequencyBound
      (max (max 1 (8 * Real.pi ^ 3 * v4ConstantSharp))
        (Frequency.outerRegionConstant (1 / 4))) :=
  Frequency.v4FrequencyBound_of_move2Supply (by norm_num) le_rfl v4ConstantSharp_pos
    (v4Move2Supply_proved_sharp (by norm_num) le_rfl)

/-- The annealed Green bound by the sharp route. -/
theorem annealedGreenBound_proved_sharp : Manhattan.AnnealedGreenBound :=
  Frequency.annealedGreenBound_of_v4Move2Supply (by norm_num) le_rfl v4ConstantSharp_pos
    (v4Move2Supply_proved_sharp (by norm_num) le_rfl)

/-- **Theorem 1.1 by the sharp Version 4 route.** -/
theorem theorem_1_1_v4_sharp :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ⊤ :=
  Manhattan.theorem_1_1 annealedGreenBound_proved_sharp

end Manhattan.V4

end
