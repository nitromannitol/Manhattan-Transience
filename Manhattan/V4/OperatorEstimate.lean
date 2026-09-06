import Manhattan.V4.Parity
import Manhattan.Glue.SummandFourAssembly
import Manhattan.Glue.FinalDischarge

/-!
# Version 4, Step 2: the operator estimate with the even majorant

This file proves the operator estimate (OP) of the Version 4 argument
for an arbitrary bounded measurable raw type-`112` kernel `K`:

  `‖Π K‖₊² + ‖D₃ (Π K)‖₋² ≤ 9 ∫ M |K|²`,   `M(r,r',β) = κ(δ + |r| + |r'| + |β|)`.

**Nothing analytic is reproved here.**  The hard content is the existing
development's:

* `Manhattan.Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le`, the
  degree-four raising energy bound with constant `2` (which already contains
  `Manhattan.Estimates.fourEstimateCore_le_multiplier`, the Fubini, and the
  `symbolWeight` measurability repair);
* `Manhattan.Glue.multiplier_integral_type112DiagonalProjection_le` and
  `Manhattan.Glue.symbolWeight_integral_type112DiagonalProjection_le`, the
  **input projection contraction** for the true total-frequency weights, from
  `Manhattan/Glue/OrderedContractivity.lean`;
* `Manhattan.Glue.hThreeForm_type112WalshSynthesis`,
  `Manhattan.Glue.tsum_multiplier_type112Extend` and
  `Manhattan.Glue.multiplier_integral_type112ShiftTwist_frozen`, the transport
  of `Manhattan/Glue/Transport.lean`.

The only new ingredient is **majorization**: the pointwise inequality
`Estimates.multiplier 40 q (β, r+r'-p₂) ≤ evenMajorant 120 δ r r' β` of
`Manhattan/V4/EvenMajorant.lean`, applied under the integral at the very end.

**The order of operations is the point.**  The projection contraction is
applied with the TRUE total-frequency multiplier, and only THEN is the weight
enlarged to `M`.  No commutation of `Π` with `M` is needed anywhere -- which
matters, because `M` depends on `r` and `r'` separately and therefore is *not*
a multiplier in the total frequency, so it does not commute with `Π`.  Compare
ERRATA E-010 /: the manuscript's stated justification of Lemma 5.1
is false for the multiplier of (35); here the question does not arise.

Paper: `manuscript.tex:1196-1205` (Lemma 5.2), `manuscript.tex:1193-1198`
(equation (46)).
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Manhattan.V4

/-- Classical decidability, local to this file: the statements here are analytic, not computational. -/
local instance (p : Prop) : Decidable p := Classical.propDecidable p

attribute [local instance] Real.fact_zero_lt_one

/-- The unit circle carries its normalized Haar measure throughout this file. -/
local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Reordering the iterated torus integral -/

/-- The cyclic reordering `(r,r',β) ↦ (β,r,r')` of the iterated normalized
torus integral, for bounded measurable integrands.  It converts the output of
`Manhattan.Glue.integral_unitTorus_three` into the iteration order of
`Manhattan.Glue.rawMultiplierEnergy`. -/
theorem torusIntegral₃_rotate {F : ℝ → ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2)
    {C : ℝ} (hFb : ∀ x y z, |F x y z| ≤ C) :
    (Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
        Estimates.torusIntegral fun beta => F r r' beta)
      = Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
          Estimates.torusIntegral fun r' => F r r' beta := by
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun r' => Estimates.torusIntegral fun beta => F r r' beta)
        = Estimates.torusIntegral fun beta =>
            Estimates.torusIntegral fun r' => F r r' beta := by
    intro r
    refine torusIntegral_swap_of_bounded (C := C) ?_ (fun r' beta => hFb r r' beta)
    exact hF.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  rw [funext hinner]
  refine torusIntegral_swap_of_bounded (C := C) ?_ (fun r beta => ?_)
  · have hjoint : StronglyMeasurable fun w : (ℝ × ℝ) × ℝ => F w.1.1 w.2 w.1.2 :=
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable
    exact (Glue.stronglyMeasurable_torusIntegral hjoint).measurable
  · exact Glue.abs_torusIntegral_le fun r' => hFb r r' beta

/-! ## The raw kernel as a Walsh competitor -/

/-- A raw kernel, read as a function of the three line frequencies on the
Fourier torus. -/
def rawTorusFun (k : ℝ → ℝ → ℝ → ℂ) (x : UnitAddTorus (Fin 3)) : ℂ :=
  k (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
    (Manhattan.unitTorusAngle (x 2))

theorem rawTorusFun_measurable {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Measurable (rawTorusFun k) := by
  have h0 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 0) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 1) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  have h2 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 2) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 2)
  have hcoord : Measurable fun x : UnitAddTorus (Fin 3) =>
      ((Manhattan.unitTorusAngle (x 0), Manhattan.unitTorusAngle (x 1),
        Manhattan.unitTorusAngle (x 2)) : ℝ × ℝ × ℝ) := h0.prodMk (h1.prodMk h2)
  exact hk.1.comp hcoord

set_option maxHeartbeats 1000000 in
theorem rawTorusFun_memLp {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    MemLp (rawTorusFun k) 2 (volume : Measure (UnitAddTorus (Fin 3))) := by
  obtain ⟨C, hC⟩ := hk.2
  refine MemLp.of_bound (rawTorusFun_measurable hk).aestronglyMeasurable C ?_
  filter_upwards with x
  exact hC _ _ _

/-- The raw kernel as an honest `L²` vector on the Fourier torus. -/
def rawL2 {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3))) :=
  (rawTorusFun_memLp hk).toLp (rawTorusFun k)

/-- `Π₃ K`, as a square-summable coefficient on the `Finset` carrier: the
restriction of the raw Fourier coefficients to the strictly ordered row
pairs. -/
def rawType112Coefficients {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    ℓ²(Manhattan.Type112Index, ℂ) :=
  Manhattan.type112DiagonalProjection
    (UnitAddTorus.mFourierBasis.repr (rawL2 hk))

/-- The degree-three Walsh vector `k = Π K` at the momentum `p`, with the
shift phase of `eq:shift` installed. -/
def rawWalsh (p : Fin 2 → ℝ) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    WalshL2 :=
  Manhattan.type112WalshSynthesis
    (Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hk))

/-! ## The raw multiplier energy of the `L²` vector -/

theorem multiplier_integral_rawL2 {q : Estimates.Parameters} (hlam : 0 ≤ q.lambda)
    (p₂ : ℝ) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    (∫ t, Estimates.multiplier 40 q (Glue.rawCorrectionTotalFrequency p₂ t) *
        ‖(rawL2 hk : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3))
      = Glue.rawMultiplierEnergy 40 q p₂ k := by
  have hmeas := hk.1
  obtain ⟨C, hC⟩ := hk.2
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  set F : ℝ → ℝ → ℝ → ℝ := fun r r' beta =>
    Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r')) *
      ‖k r r' beta‖ ^ 2 with hF
  have hFmeas : Measurable fun z : ℝ × ℝ × ℝ => F z.1 z.2.1 z.2.2 := by
    refine Measurable.mul ?_ ?_
    · refine Glue.measurable_multiplier_comp 40 q (measurable_snd.comp measurable_snd) ?_
      exact (measurable_fst.add (measurable_fst.comp measurable_snd)).sub measurable_const
    · exact (hmeas.norm.pow_const 2)
  have hFb : ∀ r r' beta, |F r r' beta| ≤ 40 * (q.lambda + 8) * C ^ 2 := by
    intro r r' beta
    have hm0 : 0 ≤ Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r')) :=
      Estimates.multiplier_nonneg (by norm_num) hlam _
    have hm : Estimates.multiplier 40 q
        (Estimates.mixedTotalFrequency beta (Glue.mixedAlpha p₂ r r'))
        ≤ 40 * (q.lambda + 8) := Glue.multiplier_le (by norm_num) _
    have hn : ‖k r r' beta‖ ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hC r r' beta) 2
    rw [hF]
    simp only
    rw [abs_of_nonneg (mul_nonneg hm0 (sq_nonneg _))]
    nlinarith [sq_nonneg (‖k r r' beta‖)]
  have hcongr : (∫ t, Estimates.multiplier 40 q (Glue.rawCorrectionTotalFrequency p₂ t) *
      ‖(rawL2 hk : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3))
      = ∫ x : UnitAddTorus (Fin 3), F (Manhattan.unitTorusAngle (x 0))
          (Manhattan.unitTorusAngle (x 1)) (Manhattan.unitTorusAngle (x 2)) := by
    refine integral_congr_ae ?_
    filter_upwards [(rawTorusFun_memLp hk).coeFn_toLp] with x hx
    rw [show (rawL2 (k := k) hk : UnitAddTorus (Fin 3) → ℂ) x
        = rawTorusFun k x from hx]
    rfl
  rw [hcongr, Glue.integral_unitTorus_three F hFmeas hFb,
    torusIntegral₃_rotate hFmeas hFb]
  rfl

/-! ## The two halves of the operator estimate -/

/-- **The sharp symbol-weight bound.**  `symbolWeight = λ + θ(P)` and the
multiplier is `κ(λ + θ(P) + 2|sin(P₀/2)| + 2|sin(P₁/2)|)`, so the inequality
needs only nonnegativity of the two sine terms: `κ = 1` suffices, and the `40`
carried by `symbolWeight_le_multiplier` below is slack inherited from the
normalization of the projection-contraction chain. -/
theorem symbolWeight_le_multiplier_one {q : Estimates.Parameters}
    (p : Fin 2 → ℝ) (σ : Fin 3 → Axis) (t : UnitAddTorus (Fin 3)) :
    Glue.symbolWeight 3 q.lambda p σ t
      ≤ Estimates.multiplier 1 q (Glue.totalFrequency 3 p σ t) := by
  have hθ := Estimates.theta_nonneg (Glue.totalFrequency 3 p σ t)
  have hs0 := abs_nonneg (Real.sin (Glue.totalFrequency 3 p σ t 0 / 2))
  have hs1 := abs_nonneg (Real.sin (Glue.totalFrequency 3 p σ t 1 / 2))
  simp only [Glue.symbolWeight, Estimates.multiplier]
  linarith

theorem symbolWeight_le_multiplier {q : Estimates.Parameters} (hlam : 0 ≤ q.lambda)
    (p : Fin 2 → ℝ) (σ : Fin 3 → Axis) (t : UnitAddTorus (Fin 3)) :
    Glue.symbolWeight 3 q.lambda p σ t
      ≤ Estimates.multiplier 40 q (Glue.totalFrequency 3 p σ t) := by
  have hθ := Estimates.theta_nonneg (Glue.totalFrequency 3 p σ t)
  have hs0 := abs_nonneg (Real.sin (Glue.totalFrequency 3 p σ t 0 / 2))
  have hs1 := abs_nonneg (Real.sin (Glue.totalFrequency 3 p σ t 1 / 2))
  rw [Glue.symbolWeight_def, Estimates.multiplier]
  linarith

/-- The `H₃` half.  The projection contraction is
`Manhattan.Glue.symbolWeight_integral_type112DiagonalProjection_le`. -/
theorem hThreeForm_rawWalsh_le {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
      ≤ Glue.rawMultiplierEnergy 40 q (p 1) k := by
  set d := UnitAddTorus.mFourierBasis.repr (rawL2 hk) with hd
  have hform : Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
      = ∫ t, Glue.symbolWeight 3 q.lambda p Glue.type112Pattern t *
          ‖(Glue.type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
              (Manhattan.type112DiagonalProjection d)) :
            UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3) :=
    Glue.hThreeForm_type112WalshSynthesis q.lambda p _
  rw [hform]
  have hstep1 : (∫ t, Glue.symbolWeight 3 q.lambda p Glue.type112Pattern t *
      ‖(Glue.type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
          (Manhattan.type112DiagonalProjection d)) :
        UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3))
      ≤ ∫ t, Estimates.multiplier 40 q (Glue.totalFrequency 3 p Glue.type112Pattern t) *
          ‖(Glue.type112FreqFun (Manhattan.type112ShiftTwist (p 0) (p 1)
              (Manhattan.type112DiagonalProjection d)) :
            UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2 ∂(Glue.LineTorusMeasure 3) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with t
      exact mul_nonneg (by
        have := Estimates.theta_nonneg (Glue.totalFrequency 3 p Glue.type112Pattern t)
        rw [Glue.symbolWeight_def]; linarith) (sq_nonneg _)
    · exact Glue.integrable_multiplier_norm_sq (by norm_num : (0:ℝ) ≤ 40) hlambda.le 3 p Glue.type112Pattern _
    · filter_upwards with t
      exact mul_le_mul_of_nonneg_right
        (symbolWeight_le_multiplier hlambda.le p Glue.type112Pattern t) (sq_nonneg _)
  refine le_trans hstep1 ?_
  rw [Glue.multiplier_integral_type112ShiftTwist_frozen]
  refine le_trans (Glue.multiplier_integral_type112DiagonalProjection_le
    hlambda.le _ d) ?_
  rw [hd, LinearIsometryEquiv.symm_apply_apply,
    ← multiplier_integral_rawL2 hlambda.le (p 1) hk]
  refine le_of_eq (integral_congr_ae ?_)
  filter_upwards with t
  rw [Glue.multiplier_totalFrequency_type112Pattern]

/-- The `D₃` half.  The raising bound is
`Manhattan.Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le`, with
constant `2` per direction, and the projection contraction is
`Manhattan.Glue.multiplier_integral_type112DiagonalProjection_le`. -/
theorem sectorDFourForm_rawWalsh_le {q : Estimates.Parameters} {kappa : ℝ}
    (hkappa : 12 ≤ kappa) (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorDFourForm hlambda p (rawWalsh p hk)
      ≤ 8 * Glue.rawMultiplierEnergy kappa q (p 1) k := by
  set d := UnitAddTorus.mFourierBasis.repr (rawL2 hk) with hd
  set ct := Manhattan.type112ShiftTwist (p 0) (p 1)
    (Manhattan.type112DiagonalProjection d) with hct
  set g : Glue.DegreeCoefficient 3 := Glue.type112Extend ct with hg
  have hrw : rawWalsh p hk = homogeneousWalshSynthesis 3 g :=
    Glue.type112WalshSynthesis_eq_homogeneous ct
  rw [hrw]
  have hmem : homogeneousWalshSynthesis 3 g ∈ Manhattan.walshDegree 3 :=
    homogeneousWalshSynthesis_mem_degree 3 g
  have hsplit := Glue.sectorDFourForm_le_dir_integrals hlambda p hmem
    (fun i => Glue.degreeRaiseDir p i g)
    (fun i => Glue.homogeneousWalshSynthesis_degreeRaiseDir p i g)
  simp only at hsplit
  have hM40 : (∑' σ : Fin 3 → Axis, ∫ t,
      Estimates.multiplier 40 q (Glue.totalFrequency 3 p σ t) *
        ‖((Glue.lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(Glue.LineTorusMeasure 3))
      ≤ Glue.rawMultiplierEnergy 40 q (p 1) k := by
    rw [hg, Glue.tsum_multiplier_type112Extend, hct,
      Glue.multiplier_integral_type112ShiftTwist_frozen]
    refine le_trans (Glue.multiplier_integral_type112DiagonalProjection_le
      hlambda.le _ d) ?_
    rw [hd, LinearIsometryEquiv.symm_apply_apply,
      ← multiplier_integral_rawL2 hlambda.le (p 1) hk]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards with t
    rw [Glue.multiplier_totalFrequency_type112Pattern]
  have hM : (∑' σ : Fin 3 → Axis, ∫ t,
      Estimates.multiplier kappa q (Glue.totalFrequency 3 p σ t) *
        ‖((Glue.lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(Glue.LineTorusMeasure 3))
      ≤ Glue.rawMultiplierEnergy kappa q (p 1) k := by
    have e40 := Glue.tsum_integral_multiplier_eq_smul (40 : ℝ) q
      (Glue.LineTorusMeasure 3) (fun σ t => Glue.totalFrequency 3 p σ t)
      (fun σ t => ‖((Glue.lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
    have ek := Glue.tsum_integral_multiplier_eq_smul kappa q
      (Glue.LineTorusMeasure 3) (fun σ t => Glue.totalFrequency 3 p σ t)
      (fun σ t => ‖((Glue.lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
    have r40 := Glue.rawMultiplierEnergy_eq_smul (40 : ℝ) q (p 1) k
    have rk := Glue.rawMultiplierEnergy_eq_smul kappa q (p 1) k
    rw [e40, r40] at hM40
    rw [ek, rk]
    have h40 : (0:ℝ) < 40 := by norm_num
    have hk0 : (0:ℝ) ≤ kappa := by linarith
    nlinarith [hM40, hk0, h40]
  have h0 := Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le hkappa hlambda p 0 g
  have h1 := Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le hkappa hlambda p 1 g
  linarith

/-! ## The operator estimate (OP) -/

/-- **The operator estimate (OP).**  For every bounded measurable raw
type-`112` kernel `K`, at every momentum `p`, with `δ ≥ λ` and `|p₂| ≤ δ`,

  `‖Π K‖₊² + ‖D₃ (Π K)‖₋² ≤ 9 ∫ M |K|²`,   `M = evenMajorant 120 δ`.

Projection contraction is applied with the true total-frequency multiplier
(inside `hThreeForm_rawWalsh_le` and `sectorDFourForm_rawWalsh_le`), and the
enlargement to `M` happens only afterwards, in
`Manhattan.V4.rawMultiplierEnergy_le_evenMajorantEnergy`.  `Π` is never
commuted with `M`. -/
theorem operatorEstimate {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k) :
    Glue.sectorHThreeForm q.lambda p (rawWalsh p hk)
        + Glue.sectorDFourForm hlambda p (rawWalsh p hk)
      ≤ 9 * evenMajorantEnergy 120 delta k := by
  have h1 := hThreeForm_rawWalsh_le hlambda p hk
  have h2 := sectorDFourForm_rawWalsh_le (by norm_num : (12:ℝ) ≤ 40) hlambda p hk
  have h3 := rawMultiplierEnergy_le_evenMajorantEnergy (q := q) (delta := delta)
    (p₂ := p 1) (k := k) hlambda.le hdelta hp₂ hk
  linarith

/-- **(OP) at the parity competitor.**  Combining the operator estimate with
the energy identity (P4), the whole degree-three cost of `k = Π K` is the
scalar integral `∫ σ |v|²`.  Together with `rawD2StarMixed_offDiagonalPart`
(`(D₂* k)₁₂ = (√2)⁻¹ σ v`) and `rawD2StarTwoRow_offDiagonalPart`
(`(D₂* k)₁₁ = 0`) this is the whole of Steps 2--3 of the note. -/
theorem operatorEstimate_parityKernel {q : Estimates.Parameters} (hlambda : 0 < q.lambda)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta : q.lambda ≤ delta) (p : Fin 2 → ℝ)
    (hp₂ : |p 1| ≤ delta) (v : ParityProfile) :
    Glue.sectorHThreeForm q.lambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 120) hdelta0 v))
      + Glue.sectorDFourForm hlambda p
        (rawWalsh p (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 120) hdelta0 v))
      ≤ 9 * Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
          paritySigma 120 delta r beta * v.toFun r beta ^ 2 := by
  have h := operatorEstimate hlambda hdelta p hp₂
    (torusBounded₃_parityKernel (by norm_num : (0:ℝ) < 120) hdelta0 v)
  rwa [evenMajorantEnergy_parityKernel (by norm_num : (0:ℝ) < 120) hdelta0 v] at h

end Manhattan.V4

end
