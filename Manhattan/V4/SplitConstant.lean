/-
The manuscript's evaluated `β` split, carried through Move 1.

`Manhattan.V4.parity_betaIntegral_le` bounds the inner zone `|β| ≤ √ρ` by its
value at the endpoint.  The manuscript instead integrates
`(2ρ²/π² + cβ² log(1/ρ))⁻¹` over the line, which is `π/√(AB)`, and the two
outer pieces exactly.  At the optimal shared constant `κ = 291`, where the operator
estimate reads with coefficient one, the Move 1 constant falls from `20,028`
to `669.5`.
-/
import Manhattan.V4.BetaSplit
import Manhattan.V4.SharpMove1

noncomputable section

open MeasureTheory Set

namespace Manhattan.V4

/-- **The `β` integral (6) at the parity correction, with the inner zone
integrated.**  The manuscript splits at `|β| = √ρ` and evaluates both pieces
rather than bounding the inner one; the constant is `π√(π³κ)/4 + π/2` in place
of `π² + π³κ/2`.  At `κ = 14` these read `17.9` and `226.9`. -/
theorem parity_betaIntegral_le_split {kappa delta lambda r : ℝ}
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (hdr : delta ≤ |r| ^ 2)
    (hlam : 0 < lambda) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    Estimates.torusIntegral (fun b =>
        (lambda + Estimates.dispersion r + Estimates.dispersion b
          + paritySigma kappa delta r b)⁻¹)
      ≤ (Real.pi * Real.sqrt (Real.pi ^ 3 * kappa) / 4 + Real.pi / 2)
          / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2:ℝ) ≤ Real.pi := Real.two_le_pi
  have hrpi : |r| ≤ Real.pi := by linarith
  have hc : (0:ℝ) < 2 / (Real.pi ^ 3 * kappa) := by positivity
  have hmeasD : Measurable (fun b : ℝ => Estimates.dispersion b) := by
    unfold Estimates.dispersion
    exact measurable_const.sub Real.continuous_cos.measurable
  have hmeas : Measurable (fun b : ℝ =>
      lambda + Estimates.dispersion r + Estimates.dispersion b + paritySigma kappa delta r b) :=
    (measurable_const.add hmeasD).add (paritySigma_measurable_col r)
  have hdr' : 0 ≤ Estimates.dispersion r := Estimates.dispersion_nonneg r
  have hrow : 2 / Real.pi ^ 2 * |r| ^ 2 ≤ Estimates.dispersion r := by
    have h := Energy.two_sq_div_pi_sq_le_dispersion hrpi
    have h2 : 2 * r ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * r ^ 2 := by ring
    rw [sq_abs]
    linarith
  have h := Beta.torusIntegral_inv_le_split (rho := |r|) (c := 2 / (Real.pi ^ 3 * kappa))
    (m := lambda) hmeas hc hr hr1 hlam
    (fun b => by
      have h1 := Estimates.dispersion_nonneg b
      have h2 := paritySigma_nonneg hkappa hdelta r b
      linarith)
    (fun b hb => by
      have h1 := Estimates.dispersion_nonneg b
      have h2 := paritySigma_inner_lower hkappa hdelta hdr hr hr1 hb
      have h3 : 2 / (Real.pi ^ 3 * kappa) * (b ^ 2 * Real.log (1 / |r|))
          = 2 / (Real.pi ^ 3 * kappa) * (b ^ 2 * Real.log (1 / |r|)) := rfl
      linarith)
    (fun b hb => by
      have h1 := Energy.two_sq_div_pi_sq_le_dispersion hb
      have h2 : 2 * b ^ 2 / Real.pi ^ 2 = 2 / Real.pi ^ 2 * b ^ 2 := by ring
      have h3 := paritySigma_nonneg hkappa hdelta r b
      linarith)
  have hX : (0:ℝ) < Real.pi ^ 3 * kappa := by positivity
  have hXs : 0 < Real.sqrt (Real.pi ^ 3 * kappa) := Real.sqrt_pos.mpr hX
  have hsq : Real.sqrt (2 * (2 / (Real.pi ^ 3 * kappa)))
      = 2 / Real.sqrt (Real.pi ^ 3 * kappa) := by
    rw [show 2 * (2 / (Real.pi ^ 3 * kappa))
        = (2 / Real.sqrt (Real.pi ^ 3 * kappa)) ^ 2 by
      rw [div_pow, Real.sq_sqrt hX.le]; ring, Real.sqrt_sq (by positivity)]
  have hconst : Real.pi / (2 * Real.sqrt (2 * (2 / (Real.pi ^ 3 * kappa)))) + Real.pi / 2
      = Real.pi * Real.sqrt (Real.pi ^ 3 * kappa) / 4 + Real.pi / 2 := by
    rw [hsq]
    field_simp
    ring
  rwa [hconst] at h

/-- `parityFibreJ_le_weight` with the inner zone integrated: the constant is
`π√(π³κ)/4 + π/2`. -/
theorem parityFibreJ_le_weight_split {kappa delta r : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (hdr : Real.sqrt delta ≤ |r|) (hr1 : |r| ≤ 1 / 4) :
    parityFibreJ q kappa delta r
      ≤ (Real.pi * Real.sqrt (Real.pi ^ 3 * kappa) / 4 + Real.pi / 2)
          / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  have hrpos : 0 < |r| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hdr
  have hdsq : delta ≤ |r| ^ 2 := by
    have h := Real.sq_sqrt hdelta.le
    nlinarith [hdr, Real.sqrt_nonneg delta]
  exact parity_betaIntegral_le_split (kappa := kappa) (delta := delta)
    (lambda := q.lambda) (r := r) hkappa hdelta hdsq hlam hrpos hr1

/-! ## The Move 1 constant at the evaluated split -/

/-- The column bound with the inner zone integrated. -/
theorem betaColumnBound_split {kappa : ℝ} (hkappa : 0 < kappa) :
    BetaColumnBound kappa (Real.pi * Real.sqrt (Real.pi ^ 3 * kappa) / 4 + Real.pi / 2) :=
  fun _ _ _ hq hd h1 h2 => parityFibreJ_le_weight_split hq hkappa hd h1 h2

/-- `60 + 8 (π√(291π³)/4 + π/2) = 669.5`, against `v4ConstantSharp = 20,028.4`
and `v4Constant = 74,869.8`.

The shared constant is `κ = 291`, where the operator estimate reads with
coefficient `A = 1` and the Move 1 coefficient is `4A + 4 = 8`.  Since the
operator coefficient scales like `291/κ` and the column constant like `√κ`,
the product `(4·291/κ + 4)√κ` is least exactly at `κ = 291`. -/
def v4ConstantSplit : ℝ :=
  60 + 8 * (Real.pi * Real.sqrt (Real.pi ^ 3 * 291) / 4 + Real.pi / 2)

theorem v4ConstantSplit_pos : 0 < v4ConstantSplit := by
  unfold v4ConstantSplit
  have := Real.pi_pos
  positivity

/-- The value of the sharpened Move 1 constant, certified. -/
theorem v4ConstantSplit_lt : v4ConstantSplit < 670 := by
  have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hsq : Real.pi ^ 2 < 9.8697 := by nlinarith [hpi, hpi0]
  have hcube : Real.pi ^ 3 < 31.008 := by nlinarith [hsq, hpi, hpi0]
  have hs : Real.sqrt (Real.pi ^ 3 * 291) < 95 := by
    have h : Real.pi ^ 3 * 291 < 95 ^ 2 := by nlinarith [hcube]
    calc Real.sqrt (Real.pi ^ 3 * 291) < Real.sqrt (95 ^ 2) :=
          Real.sqrt_lt_sqrt (by positivity) h
      _ = 95 := Real.sqrt_sq (by norm_num)
  have hS0 : (0:ℝ) ≤ Real.sqrt (Real.pi ^ 3 * 291) := Real.sqrt_nonneg _
  have hterm : Real.pi * Real.sqrt (Real.pi ^ 3 * 291) / 4 < 74.62 := by
    nlinarith [hs, hpi, hpi0, hS0]
  unfold v4ConstantSplit
  linarith

theorem v4Move2Supply_proved_split {r0 : ℝ} (hr0 : 0 < r0) (hr014 : r0 ≤ 1 / 4) :
    Frequency.V4Move2Supply r0 v4ConstantSplit := by
  have h := v4Move2Supply_proved_of (kappa := 291) (A := 1) (by norm_num) (by norm_num)
    operatorCoefficient_291 (by have := Real.pi_pos; positivity)
    (betaColumnBound_split (by norm_num)) hr0 hr014
  have heq : 60 + (4 * (1:ℝ) + 4)
      * (Real.pi * Real.sqrt (Real.pi ^ 3 * 291) / 4 + Real.pi / 2)
      = v4ConstantSplit := by unfold v4ConstantSplit; ring
  rwa [heq] at h

/-- The Version 4 fixed-frequency bound at the sharpened constant. -/
theorem v4FrequencyBound_proved_split :
    Frequency.V4FrequencyBound
      (max (max 1 (8 * Real.pi ^ 3 * v4ConstantSplit))
        (Frequency.outerRegionConstant (1 / 4))) :=
  Frequency.v4FrequencyBound_of_move2Supply (by norm_num) le_rfl v4ConstantSplit_pos
    (v4Move2Supply_proved_split (by norm_num) le_rfl)

/-- The annealed Green bound at the sharpened constant. -/
theorem annealedGreenBound_proved_split : Manhattan.AnnealedGreenBound :=
  Frequency.annealedGreenBound_of_v4Move2Supply (by norm_num) le_rfl v4ConstantSplit_pos
    (v4Move2Supply_proved_split (by norm_num) le_rfl)

/-- **Theorem 1.1 with the evaluated `β` split.** -/
theorem theorem_1_1_v4_split :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ⊤ :=
  Manhattan.theorem_1_1 annealedGreenBound_proved_split

end Manhattan.V4

end
