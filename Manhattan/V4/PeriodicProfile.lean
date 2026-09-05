import Manhattan.V4.TwoRow
import Manhattan.V4.Frequency.Profile
import Manhattan.V4.CompetitorEnergy

/-!
# Version 4: the `2π`-periodic competitor profile, and the composed cost

Two conventions collide in the Version 4 chain.

* The **operator** side needs the row profile to be a function on the torus:
  `Manhattan.V4.ParityProfile` carries `periodic_row`, and
  `Manhattan.V4.mixedRaising_rowFourier` translates the row Fourier coefficient
  by `Manhattan.Glue.torusIntegral_translate_periodic`.
* The **Move 1** side needs it to be supported in `Γ_δ = {√δ ≤ |r| ≤ r₀}`, and
  `Manhattan.V4.Frequency.profile` is supported there **on the whole line**, so
  it is not periodic.

`perProfile r0 delta t r := Frequency.profile r0 delta t (torusAbs r)` is the
periodic representative: `Manhattan.V4.Frequency.profile` depends on the row
frequency only through `|r|`, and `torusAbs r = |r|` on the torus, so the two
agree there. All the Move 1 estimates are restated with the support hypothesis
required only on the torus (`v4_cost_le`), which is what `perProfile`
satisfies.

`profileMass r0 delta` is the normalized torus mass of the unit profile. It
replaces `Manhattan.V4.Zdelta` in Move 2: the two substitution integrals
`∫ φ = t·profileMass` and `∫ q φ² = t²·profileMass` are exact for it, and
`Zdelta_le_profileMass` is all Move 3 needs, since Move 3 only uses a **lower**
bound on the scale.
-/

noncomputable section
open MeasureTheory Set

namespace Manhattan.V4

open Manhattan.V4.Frequency


/-- Two integrands that agree on the torus have the same normalized torus
integral. -/
theorem torusIntegral_congr_on {f g : ℝ → ℝ}
    (h : ∀ x ∈ Estimates.torus, f x = g x) :
    Estimates.torusIntegral f = Estimates.torusIntegral g := by
  unfold Estimates.torusIntegral
  congr 1
  exact setIntegral_congr_fun Estimates.measurableSet_torus h

/-- The Version 4 competitor profile depends on the row frequency only through
its absolute value. -/
theorem profile_abs (r0 delta t r : ℝ) :
    profile r0 delta t |r| = profile r0 delta t r := by
  simp only [profile, logWeight, abs_abs]

theorem measurable_logWeight : Measurable logWeight := by
  unfold logWeight
  fun_prop

theorem measurable_profile (r0 delta t : ℝ) : Measurable (profile r0 delta t) := by
  unfold profile
  refine Measurable.ite ?_ (measurable_const.mul measurable_logWeight) measurable_const
  have habs : Measurable fun r : ℝ => |r| := by fun_prop
  exact (measurableSet_le measurable_const habs).inter
    (measurableSet_le habs measurable_const)

/-- The `2π`-periodic version of the Version 4 competitor profile. It agrees
with `Manhattan.V4.Frequency.profile` on the torus, and is what the parity and
Fourier machinery needs: `Manhattan.V4.ParityProfile` requires periodicity in
the row frequency, and `Manhattan.V4.mixedRaising_rowFourier` needs it for the
translation of the row Fourier coefficient. -/
def perProfile (r0 delta t : ℝ) (r : ℝ) : ℝ := profile r0 delta t (torusAbs r)

theorem perProfile_eq_on_torus (r0 delta t : ℝ) {r : ℝ} (hr : r ∈ Estimates.torus) :
    perProfile r0 delta t r = profile r0 delta t r := by
  rw [perProfile, torusAbs_eq_abs hr, profile_abs]

theorem perProfile_periodic (r0 delta t : ℝ) :
    Function.Periodic (perProfile r0 delta t) (2 * Real.pi) := by
  intro r
  show profile r0 delta t (torusAbs (r + 2 * Real.pi)) = profile r0 delta t (torusAbs r)
  rw [torusAbs_periodic r]

theorem perProfile_even (r0 delta t r : ℝ) :
    perProfile r0 delta t (-r) = perProfile r0 delta t r := by
  show profile r0 delta t (torusAbs (-r)) = profile r0 delta t (torusAbs r)
  rw [torusAbs_neg]

theorem measurable_perProfile (r0 delta t : ℝ) : Measurable (perProfile r0 delta t) :=
  (measurable_profile r0 delta t).comp torusAbs_measurable

theorem perProfile_abs_le {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1) (t r : ℝ) :
    |perProfile r0 delta t r|
      ≤ |t| * (Real.sqrt (-Real.log (Real.sqrt delta)) / Real.sqrt delta) :=
  profile_abs_le hsq hle hr01 t (torusAbs r)

theorem profile_nonneg {r0 delta t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    0 ≤ profile r0 delta t r := by
  rw [profile]
  split_ifs with h
  · have : 0 ≤ logWeight r := by
      rw [logWeight]; positivity
    exact mul_nonneg ht this
  · exact le_refl 0

theorem perProfile_nonneg {r0 delta t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    0 ≤ perProfile r0 delta t r := profile_nonneg ht _

theorem profile_smul (r0 delta t r : ℝ) :
    profile r0 delta t r = t * profile r0 delta 1 r := by
  rw [profile, profile]
  split_ifs with h
  · ring
  · ring

theorem perProfile_smul (r0 delta t r : ℝ) :
    perProfile r0 delta t r = t * perProfile r0 delta 1 r := profile_smul r0 delta t _

/-- The normalized torus mass of the unit Version 4 competitor profile. -/
def profileMass (r0 delta : ℝ) : ℝ :=
  Estimates.torusIntegral (perProfile r0 delta 1)

theorem torusIntegral_perProfile (r0 delta t : ℝ) :
    Estimates.torusIntegral (perProfile r0 delta t) = t * profileMass r0 delta := by
  rw [profileMass, ← Estimates.torusIntegral_smul_left]
  congr 1
  funext r
  exact perProfile_smul r0 delta t r

theorem perProfile_eq_logWeight {r0 delta : ℝ} (hr0pi : r0 < Real.pi) {r : ℝ}
    (h1 : Real.sqrt delta ≤ |r|) (h2 : |r| ≤ r0) :
    perProfile r0 delta 1 r = logWeight r := by
  have habs : |r| < Real.pi := lt_of_le_of_lt h2 hr0pi
  have hlt := abs_lt.mp habs
  have hrt : r ∈ Estimates.torus := ⟨hlt.1, hlt.2.le⟩
  rw [perProfile_eq_on_torus r0 delta 1 hrt, profile, if_pos ⟨h1, h2⟩, one_mul]

theorem integrableOn_perProfile {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1) (t : ℝ) :
    Integrable (perProfile r0 delta t) (volume.restrict Estimates.torus) :=
  Estimates.integrableOn_torus_of_bounded (measurable_perProfile r0 delta t)
    (fun r => perProfile_abs_le hsq hle hr01 t r)

/-- The normalized torus mass of the competitor profile is at least `Z_δ`: the
torus contains the two components of `Γ_δ`, and the profile is nonnegative. -/
theorem Zdelta_le_profileMass {r0 delta : ℝ} (hsq : 0 < Real.sqrt delta)
    (hle : Real.sqrt delta ≤ r0) (hr01 : r0 < 1) (hr0pi : r0 < Real.pi) :
    Zdelta r0 delta ≤ profileMass r0 delta := by
  have hpi := Real.pi_pos
  set P : ℝ → ℝ := perProfile r0 delta 1 with hP
  have hPnn : ∀ r, 0 ≤ P r := fun r => perProfile_nonneg zero_le_one r
  have hPint : IntegrableOn P Estimates.torus volume :=
    integrableOn_perProfile hsq hle hr01 1
  have hneg : -r0 ≤ -Real.sqrt delta := by linarith
  -- the two components, as set integrals
  have hI1 : (∫ r in -r0..(-Real.sqrt delta), logWeight r)
      = ∫ r in Set.Ioc (-r0) (-Real.sqrt delta), P r := by
    rw [intervalIntegral.integral_of_le hneg]
    refine (setIntegral_congr_fun measurableSet_Ioc ?_).symm
    intro x hx
    have hxneg : x < 0 := by linarith [hx.2]
    have h1 : Real.sqrt delta ≤ |x| := by rw [abs_of_neg hxneg]; linarith [hx.2]
    have h2 : |x| ≤ r0 := by rw [abs_of_neg hxneg]; linarith [hx.1]
    exact perProfile_eq_logWeight hr0pi h1 h2
  have hI2 : (∫ r in Real.sqrt delta..r0, logWeight r)
      = ∫ r in Set.Ioc (Real.sqrt delta) r0, P r := by
    rw [intervalIntegral.integral_of_le hle]
    refine (setIntegral_congr_fun measurableSet_Ioc ?_).symm
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hsq hx.1.le
    have h1 : Real.sqrt delta ≤ |x| := by rw [abs_of_pos hxpos]; linarith [hx.1]
    have h2 : |x| ≤ r0 := by rw [abs_of_pos hxpos]; exact hx.2
    exact perProfile_eq_logWeight hr0pi h1 h2
  -- the disjoint union
  have hdisj : Disjoint (Set.Ioc (-r0) (-Real.sqrt delta)) (Set.Ioc (Real.sqrt delta) r0) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ -Real.sqrt delta := hx.2
    have h2 : Real.sqrt delta < x := hx'.1
    linarith
  have hsub : Set.Ioc (-r0) (-Real.sqrt delta) ∪ Set.Ioc (Real.sqrt delta) r0
      ⊆ Estimates.torus := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hunion : (∫ r in Set.Ioc (-r0) (-Real.sqrt delta), P r)
        + ∫ r in Set.Ioc (Real.sqrt delta) r0, P r
      = ∫ r in Set.Ioc (-r0) (-Real.sqrt delta) ∪ Set.Ioc (Real.sqrt delta) r0, P r := by
    refine (setIntegral_union hdisj measurableSet_Ioc ?_ ?_).symm
    · exact hPint.mono_set (fun x hx => hsub (Or.inl hx))
    · exact hPint.mono_set (fun x hx => hsub (Or.inr hx))
  have hmono : (∫ r in Set.Ioc (-r0) (-Real.sqrt delta) ∪ Set.Ioc (Real.sqrt delta) r0, P r)
      ≤ ∫ r in Estimates.torus, P r := by
    refine setIntegral_mono_set hPint ?_ (Filter.Eventually.of_forall hsub)
    exact Filter.Eventually.of_forall hPnn
  rw [Zdelta_eq_gammaIntegral, gammaIntegral, profileMass, Estimates.torusIntegral,
    hI1, hI2, hunion]
  simp only [smul_eq_mul]
  have hcoef : (0:ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hmono hcoef

theorem perProfile_supp_torus {r0 delta t : ℝ} {r : ℝ} (hr : r ∈ Estimates.torus)
    (h : ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0)) : perProfile r0 delta t r = 0 := by
  rw [perProfile_eq_on_torus r0 delta t hr, profile, if_neg h]

theorem perProfile_eq_mul_logWeight {r0 delta t : ℝ} (hr0pi : r0 < Real.pi) {r : ℝ}
    (h1 : Real.sqrt delta ≤ |r|) (h2 : |r| ≤ r0) :
    perProfile r0 delta t r = t * logWeight r := by
  rw [perProfile_smul, perProfile_eq_logWeight hr0pi h1 h2]

/-- The two spellings of the effective weight `q(r) = |r|/√(log(1/|r|))` agree:
`Manhattan/V4/Energy/Weight.lean` writes `log (1/|r|)` and
`Manhattan/V4/Frequency/Profile.lean` writes `-log |r|`. -/
theorem energyEffectiveWeight_eq (r : ℝ) :
    Energy.effectiveWeight r = effectiveWeight r := by
  rw [Energy.effectiveWeight, effectiveWeight, one_div, Real.log_inv]

/-- The second substitution integral of Move 2, on the torus. -/
theorem torusIntegral_effectiveWeight_perProfile {r0 delta : ℝ}
    (hsq : 0 < Real.sqrt delta) (hr01 : r0 < 1) (hr0pi : r0 < Real.pi) (t : ℝ) :
    Estimates.torusIntegral
        (fun r => Energy.effectiveWeight r * perProfile r0 delta t r ^ 2)
      = t ^ 2 * profileMass r0 delta := by
  rw [profileMass, ← Estimates.torusIntegral_smul_left]
  refine torusIntegral_congr_on ?_
  intro r hrt
  by_cases hmem : Real.sqrt delta ≤ |r| ∧ |r| ≤ r0
  · have hrpos : 0 < |r| := lt_of_lt_of_le hsq hmem.1
    have hrlt : |r| < 1 := lt_of_le_of_lt hmem.2 hr01
    rw [perProfile_eq_mul_logWeight hr0pi hmem.1 hmem.2,
      perProfile_eq_mul_logWeight (t := 1) hr0pi hmem.1 hmem.2,
      energyEffectiveWeight_eq, effectiveWeight, logWeight, one_mul]
    exact effectiveWeight_mul_sq hrpos hrlt
  · have hz : perProfile r0 delta t r = 0 := perProfile_supp_torus hrt hmem
    have hz1 : perProfile r0 delta 1 r = 0 := perProfile_supp_torus hrt hmem
    rw [hz, hz1]
    ring

/-! ## The composed Version 4 competitor cost, with a torus support hypothesis -/

variable {kappa delta : ℝ}

/-- **The composed Version 4 competitor cost.** This is
`Manhattan.V4.v4_competitor_cost_le` restated for the two summands that the
Move 1 assembly actually produces, and with the support hypothesis needed only
**on the torus**, which is what a `2π`-periodic competitor profile can
satisfy. -/
theorem v4_cost_le {r0 C1 C3 : ℝ} {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta) (hr0 : r0 ≤ 1 / 4)
    (hC1 : 0 ≤ C1) (hC3 : 0 ≤ C3) {phi : ℝ → ℝ}
    (hsupp : ∀ r ∈ Estimates.torus, ¬ (Real.sqrt delta ≤ |r| ∧ |r| ≤ r0) → phi r = 0)
    (hint : Integrable (fun r => Energy.effectiveWeight r * phi r ^ 2)
      (volume.restrict Estimates.torus)) :
    C1 * Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2)
        + C3 * Estimates.torusIntegral (fun r =>
            Real.sin r ^ 2 * parityFibreJ q kappa delta r * phi r ^ 2)
      ≤ (C1 + C3 * (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2))
          * Estimates.torusIntegral (fun r => Energy.effectiveWeight r * phi r ^ 2) := by
  set E := Estimates.torusIntegral (fun r => Energy.effectiveWeight r * phi r ^ 2) with hE
  have hA : Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2) ≤ E := by
    refine Estimates.torusIntegral_mono_on ?_ hint ?_
    · intro x _
      have : (0:ℝ) ≤ delta + x ^ 2 := by nlinarith [sq_nonneg x, hdelta.le]
      exact mul_nonneg this (sq_nonneg _)
    · intro x hx
      by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
      · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
        have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
        exact mul_le_mul_of_nonneg_right
          (Energy.add_sq_le_effectiveWeight hdelta.le hmem.1 hxpos hx14) (sq_nonneg _)
      · rw [hsupp x hx hmem]
        simp
  have hB : Estimates.torusIntegral (fun r =>
        Real.sin r ^ 2 * parityFibreJ q kappa delta r * phi r ^ 2)
      ≤ (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2) * E := by
    have hCnn : (0:ℝ) ≤ Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2 := by positivity
    rw [hE, ← Estimates.torusIntegral_smul_left]
    refine Estimates.torusIntegral_mono_on ?_ (hint.const_mul _) ?_
    · intro x _
      exact mul_nonneg (mul_nonneg (sq_nonneg _)
        (parityFibreJ_nonneg hlam hkappa hdelta x)) (sq_nonneg _)
    · intro x hx
      by_cases hmem : Real.sqrt delta ≤ |x| ∧ |x| ≤ r0
      · have hxpos : 0 < |x| := lt_of_lt_of_le (Real.sqrt_pos.2 hdelta) hmem.1
        have hx14 : |x| ≤ 1 / 4 := le_trans hmem.2 hr0
        have hJ := parityFibreJ_le_weight hlam hkappa hdelta hmem.1 hx14
        have h1 : Real.sin x ^ 2 * parityFibreJ q kappa delta x
            ≤ Real.sin x ^ 2 * ((Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
                / (|x| * Real.sqrt (Real.log (1 / |x|)))) :=
          mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
        have h2 := Energy.sin_sq_mul_betaBound_le (C := Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
          hCnn hxpos hx14
        have h3 : Real.sin x ^ 2 * parityFibreJ q kappa delta x
            ≤ (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2) * Energy.effectiveWeight x :=
          le_trans h1 h2
        have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (phi x))
        calc Real.sin x ^ 2 * parityFibreJ q kappa delta x * phi x ^ 2
            ≤ (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2) * Energy.effectiveWeight x
                * phi x ^ 2 := this
          _ = (Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2)
                * (Energy.effectiveWeight x * phi x ^ 2) := by ring
      · rw [hsupp x hx hmem]
        simp
  have h1 : C1 * Estimates.torusIntegral (fun r => (delta + r ^ 2) * phi r ^ 2)
      ≤ C1 * E := mul_le_mul_of_nonneg_left hA hC1
  have h2 : C3 * Estimates.torusIntegral (fun r =>
        Real.sin r ^ 2 * parityFibreJ q kappa delta r * phi r ^ 2)
      ≤ C3 * ((Real.pi ^ 2 + Real.pi ^ 3 * kappa / 2) * E) :=
    mul_le_mul_of_nonneg_left hB hC3
  nlinarith [h1, h2]

end Manhattan.V4
