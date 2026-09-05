import Manhattan.V4.Energy.BetaIntegral
import Manhattan.V4.Energy.DegreeOne

/-!
# Version 4, Move 1: the effective-energy inequality

This file assembles the ingredients of Move 1 of the Version 4 argument.
For every real even `φ` supported on `Γ_δ = {√δ ≤ |r| ≤ r₀}`, `r₀ ≤ 1/4`,

    `r_λ(p) ≤ (1 - s ∫ φ dm)² / h₀ + C ∫_{Γ_δ} q φ² dm`, `q(r) = |r|/√(log(1/|r|))`.

What is proved here is the **energy estimate**: the competitor energy density,
namely the degree-one cost `C₁ (δ + r²) φ(r)²` of estimate (4) together with the
`β`-integrated degree-three cost `sin²(r) J(r) φ(r)²` of (5)-(6), is dominated
pointwise and then in the `r` integral by `(C₁ + C₂) q(r) φ(r)²`. The two
inputs are `Manhattan.V4.Energy.add_sq_le_effectiveWeight` (ingredient (e)) and
`Manhattan.V4.Energy.betaIntegral_le` (ingredient (d)).

The final statement `effectiveEnergy_le` carries the competitor bound itself as
the hypothesis `hcompetitor`. That hypothesis is what Step 1 of
the Version 4 argument (`Manhattan.V4.resolventQuadratic_le_cauchySchwarz`, or the
stronger sealed `Manhattan.Operator.DissipativeSkewPair.resolventQuadratic_le`)
delivers once the parity construction of Steps 2-3 supplies
`(D₂* k)₁₂ = σ v` and `(D₂* k)₁₁ = 0`, and the scalar completion of the square
`Manhattan.V4.scalarCompletion_le` is applied pointwise in `(r, β)`. Those two
lowering identities belong to the parity construction and are **not** reproved here; the
present module owns only the estimate that turns the resulting energy into
`C ∫ q φ² dm`.
-/

open MeasureTheory

namespace Manhattan.V4.Energy

/-! ## The pointwise bound -/

/-- **Move 1, integrand form.** On `Γ_δ = {√δ ≤ |r| ≤ 1/4}` the degree-one cost
density `C₁ (δ + r²) φ(r)²` of estimate (4) and the `β`-integrated degree-three
density `sin²(r) J φ(r)²` of (5)-(6) are together dominated by
`(C₁ + C₂) q(r) φ(r)²`. -/
theorem move1_integrand_le
    {delta C1 C2 J r : ℝ} (phi : ℝ → ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hd : 0 ≤ delta) (hdr : Real.sqrt delta ≤ |r|) (hr : 0 < |r|) (hr1 : |r| ≤ 1 / 4)
    (hJ : J ≤ C2 / (|r| * Real.sqrt (Real.log (1 / |r|)))) :
    C1 * ((delta + r ^ 2) * phi r ^ 2) + Real.sin r ^ 2 * J * phi r ^ 2
      ≤ (C1 + C2) * (effectiveWeight r * phi r ^ 2) := by
  have hA : (delta + r ^ 2) * phi r ^ 2 ≤ effectiveWeight r * phi r ^ 2 :=
    mul_le_mul_of_nonneg_right (add_sq_le_effectiveWeight hd hdr hr hr1) (sq_nonneg _)
  have hD : C1 * ((delta + r ^ 2) * phi r ^ 2) ≤ C1 * (effectiveWeight r * phi r ^ 2) :=
    mul_le_mul_of_nonneg_left hA hC1
  have t2 : Real.sin r ^ 2 * J
      ≤ Real.sin r ^ 2 * (C2 / (|r| * Real.sqrt (Real.log (1 / |r|)))) :=
    mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
  have hB : Real.sin r ^ 2 * J ≤ C2 * effectiveWeight r :=
    le_trans t2 (sin_sq_mul_betaBound_le hC2 hr hr1)
  have hC : Real.sin r ^ 2 * J * phi r ^ 2 ≤ C2 * effectiveWeight r * phi r ^ 2 :=
    mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  nlinarith [hD, hC]

/-! ## The integrated bound -/

/-- **Move 1, integrated form.** For `φ` supported in `Γ_δ` the competitor
energy of Version 4 is bounded by `(C₁ + C₂) ∫ q φ² dm`. The support hypothesis
is what makes the pointwise bound of `move1_integrand_le`, valid only on `Γ_δ`,
enough on the whole circle. -/
theorem move1_energy_le
    {delta C1 C2 r0 : ℝ} (phi J : ℝ → ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4)
    (hsupp : ∀ r, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hJ : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 →
      J r ≤ C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
    (hJ0 : ∀ r, 0 ≤ J r)
    (hint : Integrable (fun r => effectiveWeight r * phi r ^ 2)
      (volume.restrict Manhattan.Estimates.torus)) :
    Manhattan.Estimates.torusIntegral
        (fun r => C1 * ((delta + r ^ 2) * phi r ^ 2) + Real.sin r ^ 2 * J r * phi r ^ 2)
      ≤ (C1 + C2) * Manhattan.Estimates.torusIntegral
        (fun r => effectiveWeight r * phi r ^ 2) := by
  set f := fun r => C1 * ((delta + r ^ 2) * phi r ^ 2) + Real.sin r ^ 2 * J r * phi r ^ 2
  set g := fun r => (C1 + C2) * (effectiveWeight r * phi r ^ 2)
  have hfnn : ∀ r, 0 ≤ f r := fun r => by
    unfold f
    have h1 : 0 ≤ delta + r ^ 2 := by nlinarith [sq_nonneg r, hdpos.le]
    have h2 : 0 ≤ C1 * ((delta + r ^ 2) * phi r ^ 2) :=
      mul_nonneg hC1 (mul_nonneg h1 (sq_nonneg _))
    have h3 : 0 ≤ Real.sin r ^ 2 * J r * phi r ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (hJ0 r)) (sq_nonneg _)
    exact add_nonneg h2 h3
  have hgint : Integrable g (volume.restrict Manhattan.Estimates.torus) :=
    hint.const_mul _
  have hle : ∀ r, f r ≤ g r := fun r => by
    by_cases hmem : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
    · obtain ⟨hdr, hr_bound⟩ := hmem
      have hr_pos : 0 < |r| := lt_of_lt_of_le (Real.sqrt_pos.mpr hdpos) hdr
      have hr1_bound : |r| ≤ 1 / 4 := le_trans hr_bound hr0
      exact move1_integrand_le phi hC1 hC2 hdpos.le hdr hr_pos hr1_bound (hJ r hdr hr_bound)
    · simp [hsupp r hmem, f, g]
  have h_mono : Manhattan.Estimates.torusIntegral f ≤ Manhattan.Estimates.torusIntegral g :=
    Manhattan.Estimates.torusIntegral_mono' hfnn hgint hle
  have h_smul : Manhattan.Estimates.torusIntegral g =
      (C1 + C2) * Manhattan.Estimates.torusIntegral
        (fun r => effectiveWeight r * phi r ^ 2) :=
    Manhattan.Estimates.torusIntegral_smul_left (C1 + C2)
      (fun r => effectiveWeight r * phi r ^ 2)
  rw [h_smul] at h_mono
  exact h_mono

/-- **Move 1, integrated form with the `β` integral supplied by (6).** Here the
degree-three density is the actual `β` integral `∫ dm(β)/(B(r,β) + σ(r,β))` of
the manuscript, with `B(r,β) = λ + d(r) + d(β)`, and the constant produced is
`C₁ + π² + 1/c`. Ingredient (d) enters through `betaIntegral_le`, whose only
input from the parity construction is the inner lower bound `hSlow` on `σ`, itself
supplied by `sigma_inner_lower` with `c = 2/(π³κ)`. -/
theorem move1_energy_le_of_betaIntegral
    {delta lambda c r0 C1 : ℝ} (phi : ℝ → ℝ) (Sig : ℝ → ℝ → ℝ)
    (hC1 : 0 ≤ C1) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4)
    (hlam : 0 < lambda) (hc : 0 < c)
    (hmeasSig : ∀ r, Measurable (Sig r)) (hSignn : ∀ r b, 0 ≤ Sig r b)
    (hSlow : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 →
      ∀ b, |b| ≤ Real.sqrt |r| → c * (b ^ 2 * Real.log (1 / |r|)) ≤ Sig r b)
    (hsupp : ∀ r, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => effectiveWeight r * phi r ^ 2)
      (volume.restrict Manhattan.Estimates.torus)) :
    Manhattan.Estimates.torusIntegral
        (fun r => C1 * ((delta + r ^ 2) * phi r ^ 2)
          + Real.sin r ^ 2 *
              Manhattan.Estimates.torusIntegral (fun b =>
                (lambda + Manhattan.Estimates.dispersion r
                  + Manhattan.Estimates.dispersion b + Sig r b)⁻¹) * phi r ^ 2)
      ≤ (C1 + (Real.pi ^ 2 + 1 / c)) * Manhattan.Estimates.torusIntegral
          (fun r => effectiveWeight r * phi r ^ 2) := by
  refine move1_energy_le (delta := delta) (C1 := C1) (C2 := Real.pi ^ 2 + 1 / c) (r0 := r0)
    phi _ hC1 (by positivity) hdpos hr0 hsupp ?_ ?_ hint
  · intro r hdr hr_bound
    have hr_pos : 0 < |r| := lt_of_lt_of_le (Real.sqrt_pos.mpr hdpos) hdr
    exact betaIntegral_le (hmeasSig r) (hSignn r) hlam hc hr_pos
      (le_trans hr_bound hr0) (hSlow r hdr hr_bound)
  · intro r
    refine Manhattan.Estimates.torusIntegral_nonneg' fun b => inv_nonneg.mpr ?_
    have h1 := Manhattan.Estimates.dispersion_nonneg r
    have h2 := Manhattan.Estimates.dispersion_nonneg b
    have h3 := hSignn r b
    linarith


/-- The competitor energy density on the left of `move1_energy_le` is genuinely
integrable when `φ` and `J` are measurable and bounded and `φ` is supported in
`Γ_δ ⊆ {|r| ≤ 1/4}`. Without this the Bochner integral on that side could be
the junk value `0` and the inequality would be uninformative; the support
hypothesis is what makes the unbounded factor `δ + r²` harmless. -/
theorem integrable_move1_density
    {delta C1 r0 Kp Kj : ℝ} (phi J : ℝ → ℝ)
    (hmp : Measurable phi) (hmJ : Measurable J)
    (hsupp : ∀ r, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hr0 : r0 ≤ 1 / 4) (hd : 0 ≤ delta) (hC1 : 0 ≤ C1)
    (hKp0 : 0 ≤ Kp) (hKj0 : 0 ≤ Kj)
    (hKp : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 → |phi r| ≤ Kp)
    (hKj : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 → |J r| ≤ Kj) :
    Integrable (fun r => C1 * ((delta + r ^ 2) * phi r ^ 2)
        + Real.sin r ^ 2 * J r * phi r ^ 2)
      (volume.restrict Manhattan.Estimates.torus) := by
  refine Manhattan.Estimates.integrableOn_torus_of_bounded
    (C := C1 * ((delta + 1 / 16) * Kp ^ 2) + Kj * Kp ^ 2) ?_ ?_
  · exact ((measurable_const.mul ((measurable_const.add (measurable_id.pow_const 2)).mul
      ((hmp.pow_const 2))))).add
      (((Real.measurable_sin.pow_const 2).mul hmJ).mul (hmp.pow_const 2))
  · intro r
    by_cases hmem : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
    · have hr1 : |r| ≤ 1 / 4 := le_trans hmem.2 hr0
      have hrsq : r ^ 2 ≤ 1 / 16 := by
        have := sq_abs r
        nlinarith [abs_nonneg r, hr1]
      have hphisq : phi r ^ 2 ≤ Kp ^ 2 := by
        have := hKp r hmem.1 hmem.2
        nlinarith [abs_nonneg (phi r), sq_abs (phi r)]
      have hphisq0 : 0 ≤ phi r ^ 2 := sq_nonneg _
      have hsin1 : Real.sin r ^ 2 ≤ 1 := by
        nlinarith [Real.neg_one_le_sin r, Real.sin_le_one r]
      have hsin0 : 0 ≤ Real.sin r ^ 2 := sq_nonneg _
      have hJr : |J r| ≤ Kj := hKj r hmem.1 hmem.2
      have hterm1 : |C1 * ((delta + r ^ 2) * phi r ^ 2)| ≤ C1 * ((delta + 1 / 16) * Kp ^ 2) := by
        rw [abs_of_nonneg (by positivity)]
        have h1 : (delta + r ^ 2) * phi r ^ 2 ≤ (delta + 1 / 16) * Kp ^ 2 := by
          nlinarith [sq_nonneg r]
        exact mul_le_mul_of_nonneg_left h1 hC1
      have hterm2 : |Real.sin r ^ 2 * J r * phi r ^ 2| ≤ Kj * Kp ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsin0, abs_of_nonneg hphisq0]
        calc Real.sin r ^ 2 * |J r| * phi r ^ 2 ≤ 1 * Kj * Kp ^ 2 := by
              have h1 : Real.sin r ^ 2 * |J r| ≤ 1 * Kj :=
                mul_le_mul hsin1 hJr (abs_nonneg _) zero_le_one
              exact mul_le_mul h1 hphisq hphisq0 (by positivity)
          _ = Kj * Kp ^ 2 := by ring
      calc |C1 * ((delta + r ^ 2) * phi r ^ 2) + Real.sin r ^ 2 * J r * phi r ^ 2|
          ≤ |C1 * ((delta + r ^ 2) * phi r ^ 2)| + |Real.sin r ^ 2 * J r * phi r ^ 2| :=
            abs_add_le _ _
        _ ≤ C1 * ((delta + 1 / 16) * Kp ^ 2) + Kj * Kp ^ 2 := add_le_add hterm1 hterm2
    · rw [hsupp r hmem]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero, abs_zero]
      positivity

/-! ## The effective-energy inequality -/

/-- **Move 1 of Version 4, the effective-energy inequality (1).**

`hcompetitor` is the competitor bound of Step 1 of the Version 4 argument applied to
`f = -i φ` and the parity competitor `k` of Steps 2-3: its first summand is the
uncancelled degree-zero contribution `(1 - s ∫ φ dm)²/h₀`, produced by
`dStarZero_neg_I_mul` together with the fact that `H` acts on degree zero as
`h₀ = λ + d(p₁) + d(p₂)`, and its second summand is the competitor energy after
`(P1)-(P4)` and the scalar completion of the square. Supplying `hcompetitor` is
the parity construction's job; this file proves that its second summand is at most
`(C₁ + C₂) ∫ q φ² dm`, which is the content of the inequality below. -/
theorem effectiveEnergy_le
    {rlambda h0 s delta C1 C2 r0 : ℝ} (phi J : ℝ → ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hdpos : 0 < delta) (hr0 : r0 ≤ 1 / 4)
    (hsupp : ∀ r, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hJ : ∀ r, Real.sqrt delta ≤ |r| → |r| ≤ r0 →
      J r ≤ C2 / (|r| * Real.sqrt (Real.log (1 / |r|))))
    (hJ0 : ∀ r, 0 ≤ J r)
    (hint : Integrable (fun r => effectiveWeight r * phi r ^ 2)
      (volume.restrict Manhattan.Estimates.torus))
    (hcompetitor : rlambda
      ≤ (1 - s * Manhattan.Estimates.torusIntegral phi) ^ 2 / h0
        + Manhattan.Estimates.torusIntegral
            (fun r => C1 * ((delta + r ^ 2) * phi r ^ 2)
              + Real.sin r ^ 2 * J r * phi r ^ 2)) :
    rlambda ≤ (1 - s * Manhattan.Estimates.torusIntegral phi) ^ 2 / h0
      + (C1 + C2) * Manhattan.Estimates.torusIntegral
          (fun r => effectiveWeight r * phi r ^ 2) := by
  have h := move1_energy_le phi J hC1 hC2 hdpos hr0 hsupp hJ hJ0 hint
  linarith [hcompetitor, h]

end Manhattan.V4.Energy
