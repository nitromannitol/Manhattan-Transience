import Manhattan.V4.Parity
import Manhattan.V4.Energy.BetaIntegral

/-!
# Version 4: the fibre integral `J` in closed form

The hypothesis `hSlow` of `Manhattan.V4.Energy.betaIntegral_le` needs, through
`Manhattan.V4.Energy.sigma_inner_lower`, a lower bound on the fibre integral

  `J(r,β) = ∫ dm(r') / M(r,r',β)`,   `M = κ(δ + |r|_𝕋 + |r'|_𝕋 + |β|_𝕋)`,

of `Manhattan/V4/Parity.lean`, namely `J ≥ (κπ)⁻¹ log(1 + π/(δ + |r| + |β|))`.
`Manhattan.V4.parityJ_le` gives only the upper bound `J ≤ (κδ)⁻¹`.

What is proved here is the **exact evaluation** `parityJ_eq`, from which the
lower bound `parityJ_ge` follows by `|·|_𝕋 ≤ |·|`.  The `r'` integral is
elementary: on the fundamental domain `M` is `κ(A + |r'|)` with
`A = δ + |r|_𝕋 + |β|_𝕋`, the two halves of the circle contribute equally, and
`∫_0^π dx/(A+x) = log(A+π) - log A`.

The file then composes that evaluation with ingredient (d) of Move 1:
`parity_betaIntegral_le` is the `β` integral `(6)` with the abstract `σ`
replaced by `paritySigma`, with the explicit constant `π² + π³κ/2`.
-/

open MeasureTheory

namespace Manhattan.V4

/-- The distance to `2πℤ` never exceeds the ordinary absolute value. -/
theorem torusAbs_le_abs (x : ℝ) : torusAbs x ≤ |x| := by
  rcases le_or_gt Real.pi |x| with h | h
  · exact (torusAbs_le_pi x).trans h
  · rcases lt_or_ge x 0 with hx | hx
    · have hmem : -x ∈ Estimates.torus := by
        constructor
        · have := abs_of_neg hx; linarith [abs_nonneg x, h, this]
        · have := abs_of_neg hx; linarith
      rw [← torusAbs_neg, torusAbs_eq_abs hmem, abs_neg]
    · have hmem : x ∈ Estimates.torus := by
        constructor
        · have := abs_of_nonneg hx; nlinarith [Real.pi_pos]
        · have := abs_of_nonneg hx; linarith
      rw [torusAbs_eq_abs hmem]

/-- On the closed fundamental domain `[-π, π]` the distance to `2πℤ` is the
ordinary absolute value.  The endpoint `-π` is included, which `torusAbs_eq_abs`
alone does not give. -/
theorem torusAbs_eq_abs_of_abs_le_pi {x : ℝ} (hx : |x| ≤ Real.pi) : torusAbs x = |x| := by
  rcases lt_or_ge (-Real.pi) x with h | h
  · exact torusAbs_eq_abs ⟨h, (abs_le.mp hx).2⟩
  · have hxeq : x = -Real.pi := le_antisymm h (by linarith [(abs_le.mp hx).1])
    have hpi : Real.pi ∈ Estimates.torus := ⟨by linarith [Real.pi_pos], le_rfl⟩
    rw [hxeq, torusAbs_neg, torusAbs_eq_abs hpi, abs_neg, abs_of_pos Real.pi_pos]

/-! ## The fibre integral in closed form -/

/-- `x ↦ (c (A + |x|))⁻¹` is continuous when `A > 0` and `c ≠ 0`. -/
theorem continuous_inv_affine_abs {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    Continuous fun x : ℝ => (c * (A + |x|))⁻¹ := by
  refine Continuous.inv₀ (continuous_const.mul (continuous_const.add continuous_abs)) ?_
  intro x
  have : 0 < c * (A + |x|) := by positivity
  exact this.ne'

/-- `∫_a^b dx / (c (A + x)) = c⁻¹ (log(A+b) - log(A+a))` for `0 ≤ a ≤ b` and `A > 0`. -/
theorem integral_inv_affine {A c a b : ℝ} (hA : 0 < A) (hc : 0 < c)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, (c * (A + x))⁻¹) = c⁻¹ * (Real.log (A + b) - Real.log (A + a)) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => c⁻¹ * Real.log (A + y)) ((c * (A + x))⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < A + x := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => A + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add A
    have h2 : HasDerivAt (fun y : ℝ => Real.log (A + y)) ((A + x)⁻¹) x := by
      simpa using (Real.hasDerivAt_log hxpos.ne').comp x h1
    have h3 := h2.const_mul c⁻¹
    convert h3 using 1
    rw [mul_inv]
  have hint : IntervalIntegrable (fun x : ℝ => (c * (A + x))⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < A + x := by linarith [hx.1]
    refine ContinuousAt.continuousWithinAt (ContinuousAt.inv₀ ?_ ?_)
    · exact continuousAt_const.mul (continuousAt_const.add continuousAt_id)
    · have : 0 < c * (A + x) := by positivity
      exact this.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **The fibre integral in closed form.**  The fibre integral of the even majorant is the
logarithm the note writes:

  `J(r,β) = ∫ dm(r') / M(r,r',β) = (κπ)⁻¹ log(1 + π/(δ + |r|_𝕋 + |β|_𝕋))`.

The `r'` integral is elementary once `M` is written as `κ(A + |r'|)` with
`A = δ + |r|_𝕋 + |β|_𝕋`; the two halves of the circle contribute equally. -/
theorem parityJ_eq {kappa delta : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (r beta : ℝ) :
    parityJ kappa delta r beta
      = (kappa * Real.pi)⁻¹ *
          Real.log (1 + Real.pi / (delta + torusAbs r + torusAbs beta)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  set A : ℝ := delta + torusAbs r + torusAbs beta with hAdef
  have hApos : 0 < A := by
    have := torusAbs_nonneg r
    have := torusAbs_nonneg beta
    simp only [hAdef]
    linarith
  -- rewrite the majorant
  have hM : ∀ r' : ℝ, evenMajorant kappa delta r r' beta = kappa * (A + torusAbs r') := by
    intro r'
    rw [evenMajorant, hAdef]
    ring
  have hstep0 : parityJ kappa delta r beta
      = Estimates.torusIntegral fun r' => (kappa * (A + torusAbs r'))⁻¹ := by
    rw [parityJ]
    exact congrArg _ (funext fun r' => by rw [hM r'])
  rw [hstep0, Energy.torusIntegral_eq_intervalIntegral]
  -- replace `torusAbs` by `|·|` on the fundamental domain
  have hcongr : Set.EqOn (fun x : ℝ => (kappa * (A + torusAbs x))⁻¹)
      (fun x : ℝ => (kappa * (A + |x|))⁻¹) (Set.uIcc (-Real.pi) Real.pi) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -Real.pi ≤ Real.pi)] at hx
    have : |x| ≤ Real.pi := abs_le.mpr ⟨hx.1, hx.2⟩
    simp only [torusAbs_eq_abs_of_abs_le_pi this]
  rw [intervalIntegral.integral_congr hcongr]
  -- split the circle at the origin
  have hcont := continuous_inv_affine_abs hApos hkappa
  have hint1 : IntervalIntegrable (fun x : ℝ => (kappa * (A + |x|))⁻¹) volume
      (-Real.pi) 0 := hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => (kappa * (A + |x|))⁻¹) volume
      0 Real.pi := hcont.intervalIntegrable _ _
  have hsplit : (∫ x in (-Real.pi)..Real.pi, (kappa * (A + |x|))⁻¹)
      = (∫ x in (-Real.pi)..(0:ℝ), (kappa * (A + |x|))⁻¹)
        + (∫ x in (0:ℝ)..Real.pi, (kappa * (A + |x|))⁻¹) :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hrefl : (∫ x in (-Real.pi)..(0:ℝ), (kappa * (A + |x|))⁻¹)
      = (∫ x in (0:ℝ)..Real.pi, (kappa * (A + |x|))⁻¹) := by
    have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := (0:ℝ))
      (fun x : ℝ => (kappa * (A + |x|))⁻¹)
    simpa using h
  have hhalf : (∫ x in (0:ℝ)..Real.pi, (kappa * (A + |x|))⁻¹)
      = kappa⁻¹ * (Real.log (A + Real.pi) - Real.log (A + 0)) := by
    rw [← integral_inv_affine hApos hkappa (le_refl (0:ℝ)) hpi.le]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    rw [Set.uIcc_of_le hpi.le] at hx
    simp only [abs_of_nonneg hx.1]
  rw [hsplit, hrefl, hhalf]
  have hlog : Real.log (A + Real.pi) - Real.log (A + 0)
      = Real.log (1 + Real.pi / A) := by
    rw [add_zero, ← Real.log_div (by linarith) hApos.ne']
    congr 1
    field_simp
  rw [hlog]
  field_simp
  ring

/-- **The lower bound `betaIntegral_le`'s `hSlow` needs**, with the
ordinary absolute value on the right: `|·|_𝕋 ≤ |·|` makes the logarithm larger. -/
theorem parityJ_ge {kappa delta : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (r beta : ℝ) :
    (kappa * Real.pi)⁻¹ * Real.log (1 + Real.pi / (delta + |r| + |beta|))
      ≤ parityJ kappa delta r beta := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [parityJ_eq hkappa hdelta r beta]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.log_le_log (by positivity) ?_
  have hA : 0 < delta + torusAbs r + torusAbs beta := by
    have := torusAbs_nonneg r
    have := torusAbs_nonneg beta
    linarith
  have hmono : delta + torusAbs r + torusAbs beta ≤ delta + |r| + |beta| := by
    have h1 := torusAbs_le_abs r
    have h2 := torusAbs_le_abs beta
    linarith
  have := div_le_div_of_nonneg_left hpi.le hA hmono
  linarith

/-! ## The inner lower bound and the `β` integral at the parity `σ` -/

/-- Measurability of the `β` section of `σ`. -/
theorem paritySigma_measurable_col {kappa delta : ℝ} (r : ℝ) :
    Measurable fun b : ℝ => paritySigma kappa delta r b := by
  have hpair : Measurable (fun b : ℝ => ((r, b) : ℝ × ℝ)) :=
    Measurable.prodMk measurable_const measurable_id
  have hJ : Measurable (fun b : ℝ => parityJ kappa delta r b) :=
    Measurable.comp (f := fun b : ℝ => ((r, b) : ℝ × ℝ))
      (g := fun z : ℝ × ℝ => parityJ kappa delta z.1 z.2) parityJ_measurable hpair
  exact (Real.measurable_sin.pow_const 2).mul hJ

/-- **The lower bound in the form `betaIntegral_le` consumes.**  The parity correction
`σ(r,β) = sin²β · J(r,β)` obeys the inner-zone lower bound with the explicit
constant `c = 2/(π³κ)`. -/
theorem paritySigma_inner_lower {kappa delta r beta : ℝ}
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (hdr : delta ≤ |r| ^ 2)
    (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) (hb : |beta| ≤ Real.sqrt |r|) :
    2 / (Real.pi ^ 3 * kappa) * (beta ^ 2 * Real.log (1 / |r|))
      ≤ paritySigma kappa delta r beta :=
  Energy.sigma_inner_lower hkappa hdelta.le hdr hr hr1 hb
    (parityJ_ge hkappa hdelta r beta)

/-- **The `β` integral (6) at the parity correction.**  Ingredient (d) of Move 1
with the abstract `σ` replaced by `paritySigma`; the
constant is `π² + π³κ/2`. -/
theorem parity_betaIntegral_le {kappa delta lambda r : ℝ}
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (hdr : delta ≤ |r| ^ 2)
    (hlam : 0 < lambda) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4) :
    Estimates.torusIntegral (fun b =>
        (lambda + Estimates.dispersion r + Estimates.dispersion b
          + paritySigma kappa delta r b)⁻¹)
      ≤ (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
          / (|r| * Real.sqrt (Real.log (1 / |r|))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hc : (0:ℝ) < 2 / (Real.pi ^ 3 * kappa) := by positivity
  have h := Energy.betaIntegral_le (lambda := lambda) (c := 2 / (Real.pi ^ 3 * kappa))
    (r := r) (Sig := fun b => paritySigma kappa delta r b)
    (paritySigma_measurable_col r)
    (fun b => paritySigma_nonneg hkappa hdelta r b) hlam hc hr hr1
    (fun b hb => paritySigma_inner_lower hkappa hdelta hdr hr hr1 hb)
  have hconst : Real.pi ^ 2 + 1 / (2 / (Real.pi ^ 3 * kappa))
      = Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2 := by
    field_simp
  rwa [hconst] at h

end Manhattan.V4
