/-
The manuscript's `eq:beta` split, on the fundamental domain.

`Manhattan/V4/Energy/BetaIntegral.lean` bounds the column-frequency integral by
`(π² + 1/c)/(ρ√(log(1/ρ)))`, bounding the inner region rather than integrating
it.  The manuscript instead splits at `|β| = √ρ` and evaluates both pieces,
which gives `(π/(2√(2c)) + π/2)` in place of `(π² + 1/c)`.  At the shared
constant `κ = 291` those read `76` and `4521`.

The two evaluations are in `Manhattan/V4/BetaIntegral.lean`.  This file puts
them together over `(-π, π]`.
-/
import Manhattan.V4.BetaIntegral
import Manhattan.V4.Energy.BetaIntegral

namespace Manhattan.V4.Beta

open MeasureTheory Set Filter Topology

/-- The left tail, from the right tail by reflection, using evenness of the
weight in the column frequency. -/
theorem outer_piece_le_neg {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hpos : ∀ b, 0 < Phi b) (hev : ∀ b, Phi (-b) = Phi b)
    (h3 : ∀ b, 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    ∫ b in Iic (-Real.sqrt rho), (Phi b)⁻¹
      ≤ Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹ := by
  have hrefl : (∫ b in Iic (-Real.sqrt rho), (Phi b)⁻¹)
      = ∫ b in Ioi (Real.sqrt rho), (Phi b)⁻¹ := by
    rw [← integral_comp_neg_Ioi (Real.sqrt rho) (fun b => (Phi b)⁻¹)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    show (Phi (-b))⁻¹ = (Phi b)⁻¹
    rw [hev b]
  rw [hrefl]
  exact outer_piece_le hrho hpos h3

/-- The three pieces cover the fundamental domain. -/
theorem torus_subset_split (s : ℝ) :
    Manhattan.Estimates.torus ⊆ Iic (-s) ∪ (Ioo (-s) s ∪ Ici s) := by
  intro b _
  rcases le_or_gt b (-s) with h | h
  · exact Or.inl h
  · rcases lt_or_ge b s with h2 | h2
    · exact Or.inr (Or.inl ⟨h, h2⟩)
    · exact Or.inr (Or.inr h2)

/-- **The manuscript's `eq:beta` split, on the fundamental domain.**  Both
pieces are evaluated rather than bounded. -/
theorem torusIntegral_inv_le_sharp {rho A B m : ℝ} (hrho : 0 < rho)
    (hA : 0 < A) (hB : 0 < B) (hm : 0 < m) {Phi : ℝ → ℝ}
    (hmeas : Measurable Phi) (hpos : ∀ b, 0 < Phi b) (hglob : ∀ b, m ≤ Phi b)
    (hev : ∀ b, Phi (-b) = Phi b)
    (hin : ∀ b, |b| ≤ Real.sqrt rho → A + B * b ^ 2 ≤ Phi b)
    (hout : ∀ b, 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    Manhattan.Estimates.torusIntegral (fun b => (Phi b)⁻¹)
      ≤ (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (A * B)
          + Real.pi ^ 2 * (Real.sqrt rho)⁻¹) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hnn : ∀ b, 0 ≤ (Phi b)⁻¹ := fun b => (inv_pos.mpr (hpos b)).le
  have hmi : Measurable fun b => (Phi b)⁻¹ := hmeas.inv
  have hleft := outer_piece_le_neg hrho hpos hev hout
  have hmid := inner_piece_le' hrho hA hB hpos hin
  have hright := outer_piece_le hrho hpos hout
  -- integrability of each piece
  have hdom : ∀ b, 0 < |b| → (Phi b)⁻¹ ≤ Real.pi ^ 2 / 2 * (b ^ 2)⁻¹ := by
    intro b hb
    have hbne : b ≠ 0 := abs_pos.mp hb
    have hb2 : (0:ℝ) < b ^ 2 := by positivity
    have hq : (0:ℝ) < 2 / Real.pi ^ 2 * b ^ 2 := by positivity
    refine (inv_anti₀ hq (hout b)).trans (le_of_eq ?_)
    field_simp
  have iR : IntegrableOn (fun b => (Phi b)⁻¹) (Ioi (Real.sqrt rho)) := by
    refine Integrable.mono' ((integrableOn_inv_sq hs).const_mul (Real.pi ^ 2 / 2))
      hmi.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun b hb => ?_
    have hb0 : 0 < |b| := abs_pos.mpr (ne_of_gt (lt_trans hs (mem_Ioi.mp hb)))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn b)]
    exact hdom b hb0
  have iM : IntegrableOn (fun b => (Phi b)⁻¹) (Ioo (-Real.sqrt rho) (Real.sqrt rho)) := by
    refine Integrable.mono'
      (integrableOn_const (C := m⁻¹) (measure_Ioo_lt_top).ne)
      hmi.aestronglyMeasurable ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn b)]
    exact inv_anti₀ hm (hglob b)
  have iLio : IntegrableOn (fun b => (Phi b)⁻¹) (Iio (-Real.sqrt rho)) := by
    have hpre : (fun b : ℝ => -b) ⁻¹' (Ioi (Real.sqrt rho)) = Iio (-Real.sqrt rho) := by
      ext b; simp
    have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (measurableEmbedding_neg (α := ℝ)) (f := fun b : ℝ => (Phi b)⁻¹)
      (s := Ioi (Real.sqrt rho))
    rw [hpre] at hiff
    have hcomp : ((fun b : ℝ => (Phi b)⁻¹) ∘ (fun b : ℝ => -b)) = fun b => (Phi b)⁻¹ := by
      funext b; show (Phi (-b))⁻¹ = (Phi b)⁻¹; rw [hev b]
    rw [hcomp] at hiff
    exact hiff.mpr iR
  have iL : IntegrableOn (fun b => (Phi b)⁻¹) (Iic (-Real.sqrt rho)) :=
    (integrableOn_Iic_iff_integrableOn_Iio (f := fun b => (Phi b)⁻¹)
      (by finiteness)).mpr iLio
  have iIci : IntegrableOn (fun b => (Phi b)⁻¹) (Ici (Real.sqrt rho)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun b => (Phi b)⁻¹)
      (by finiteness)).mpr iR
  -- the three pieces are disjoint and exhaust the line
  have hd2 : Disjoint (Ioo (-Real.sqrt rho) (Real.sqrt rho)) (Ici (Real.sqrt rho)) := by
    rw [Set.disjoint_left]
    intro b hb hb'
    exact absurd (mem_Ici.mp hb') (not_le.mpr (mem_Ioo.mp hb).2)
  have hd1 : Disjoint (Iic (-Real.sqrt rho))
      (Ioo (-Real.sqrt rho) (Real.sqrt rho) ∪ Ici (Real.sqrt rho)) := by
    rw [Set.disjoint_left]
    intro b hb hb'
    have hble : b ≤ -Real.sqrt rho := mem_Iic.mp hb
    rcases hb' with h | h
    · exact absurd (mem_Ioo.mp h).1 (not_lt.mpr hble)
    · exact absurd (le_trans (mem_Ici.mp h) hble) (by linarith)
  have hcover : Iic (-Real.sqrt rho)
      ∪ (Ioo (-Real.sqrt rho) (Real.sqrt rho) ∪ Ici (Real.sqrt rho)) = univ := by
    ext b
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Ici, mem_univ, iff_true]
    rcases le_or_gt b (-Real.sqrt rho) with h | h
    · exact Or.inl h
    · rcases lt_or_ge b (Real.sqrt rho) with h2 | h2
      · exact Or.inr (Or.inl ⟨h, h2⟩)
      · exact Or.inr (Or.inr h2)
  have iU : IntegrableOn (fun b => (Phi b)⁻¹) univ := by
    rw [← hcover]
    exact iL.union (iM.union iIci)
  -- the exact three-piece decomposition of the integral over the line
  have hsplit : (∫ b in (univ : Set ℝ), (Phi b)⁻¹)
      = (∫ b in Iic (-Real.sqrt rho), (Phi b)⁻¹)
        + ((∫ b in Ioo (-Real.sqrt rho) (Real.sqrt rho), (Phi b)⁻¹)
          + ∫ b in Ioi (Real.sqrt rho), (Phi b)⁻¹) := by
    rw [← hcover,
      setIntegral_union hd1 (measurableSet_Ioo.union measurableSet_Ici) iL (iM.union iIci),
      setIntegral_union hd2 measurableSet_Ici iM iIci, integral_Ici_eq_integral_Ioi]
  -- the fundamental domain sits inside the line
  have hmono : (∫ b in Manhattan.Estimates.torus, (Phi b)⁻¹)
      ≤ ∫ b in (univ : Set ℝ), (Phi b)⁻¹ :=
    setIntegral_mono_set iU (Filter.Eventually.of_forall hnn)
      (Filter.Eventually.of_forall fun _ _ => trivial)
  have hbound : (∫ b in Manhattan.Estimates.torus, (Phi b)⁻¹)
      ≤ Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 * (Real.sqrt rho)⁻¹ := by
    refine hmono.trans ?_
    rw [hsplit]
    have hre : Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹ + (Real.pi / Real.sqrt (A * B)
        + Real.pi ^ 2 / 2 * (Real.sqrt rho)⁻¹)
        = Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 * (Real.sqrt rho)⁻¹ := by ring
    rw [← hre]
    exact add_le_add hleft (add_le_add hmid hright)
  have h2pi : (0:ℝ) < (2 * Real.pi)⁻¹ := by positivity
  simpa only [Manhattan.Estimates.torusIntegral, smul_eq_mul] using
    mul_le_mul_of_nonneg_left hbound h2pi.le

open Manhattan.V4.Energy in
/-- **The `β` integral (6) with the inner zone integrated rather than bounded.**
The hypothesis `hin` is the sum of the two lower bounds that the parity
construction supplies on `|β| ≤ √ρ`: the row weight contributes `2ρ²/π²` and the
logarithmic correction contributes `c β² log(1/ρ)`.  Integrating
`(A + Bβ²)⁻¹` over the line with `A = 2ρ²/π²` and `B = c log(1/ρ)` gives
`π/√(AB)`, and the two outer pieces give `π²/√ρ`, whence the constant
`π/(2√(2c)) + π/2` in place of `π² + 1/c`. -/
theorem torusIntegral_inv_le_split
    {rho c m : ℝ} {Phi : ℝ → ℝ} (hmeas : Measurable Phi)
    (hc : 0 < c) (hrho : 0 < rho) (hrho' : rho ≤ 1 / 4)
    (hm : 0 < m) (hglob : ∀ b, m ≤ Phi b)
    (hin : ∀ b, |b| ≤ Real.sqrt rho →
        2 / Real.pi ^ 2 * rho ^ 2 + c * (b ^ 2 * Real.log (1 / rho)) ≤ Phi b)
    (hout : ∀ b, |b| ≤ Real.pi → 2 / Real.pi ^ 2 * b ^ 2 ≤ Phi b) :
    Manhattan.Estimates.torusIntegral (fun b => (Phi b)⁻¹)
      ≤ (Real.pi / (2 * Real.sqrt (2 * c)) + Real.pi / 2)
          / (rho * Real.sqrt (Real.log (1 / rho))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi2' : (2:ℝ) ≤ Real.pi := Real.two_le_pi
  have hL1 : 1 < Real.log (1 / rho) := one_lt_log_inv hrho hrho'
  have hL0 : (0:ℝ) < Real.log (1 / rho) := by linarith
  have hL2 : rho * Real.log (1 / rho) ≤ 1 := mul_log_inv_le_one hrho hrho'
  set S : ℝ := Real.sqrt (Real.log (1 / rho)) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.mpr hL0
  have hSsq : S ^ 2 = Real.log (1 / rho) := Real.sq_sqrt hL0.le
  set t : ℝ := Real.sqrt rho with htdef
  have htpos : 0 < t := Real.sqrt_pos.mpr hrho
  have htsq : t * t = rho := Real.mul_self_sqrt hrho.le
  have hthalf : t ≤ 1 / 2 := sqrt_le_half hrho'
  have htpi : t ≤ Real.pi := by linarith
  -- `ρ S ≤ t`: this absorbs the outer piece into the main term.
  have htS : t * S ≤ 1 := by nlinarith [mul_pos htpos hS0]
  have hrhoS : rho * S ≤ t := by nlinarith
  have hPhipos : ∀ b, 0 < Phi b := fun b => lt_of_lt_of_le hm (hglob b)
  set F : ℝ → ℝ := fun b => (Phi b)⁻¹ with hF
  have hFpos : ∀ b, 0 < F b := fun b => inv_pos.mpr (hPhipos b)
  have hFabs : ∀ b, |F b| ≤ m⁻¹ := fun b => by
    rw [abs_of_pos (hFpos b)]; exact inv_anti₀ hm (hglob b)
  have hFmeas : Measurable F := hmeas.inv
  have hFii : ∀ a b : ℝ, IntervalIntegrable F volume a b :=
    fun a b => intervalIntegrable_of_bounded hFmeas hFabs a b
  have hFapp : ∀ x, F x = (Phi x)⁻¹ := fun x => by rw [hF]
  -- the inner zone, integrated
  set A : ℝ := 2 / Real.pi ^ 2 * rho ^ 2 with hAdef
  set B : ℝ := c * Real.log (1 / rho) with hBdef
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 < B := by rw [hBdef]; positivity
  have hin' : ∀ b, |b| ≤ Real.sqrt rho → A + B * b ^ 2 ≤ Phi b := by
    intro b hb
    have h := hin b hb
    have : A + B * b ^ 2 = 2 / Real.pi ^ 2 * rho ^ 2 + c * (b ^ 2 * Real.log (1 / rho)) := by
      rw [hAdef, hBdef]; ring
    rw [this]; exact h
  have hmid : (∫ x in (-t)..t, F x) ≤ Real.pi / Real.sqrt (A * B) := by
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have := inner_piece_le' hrho hA hB hPhipos hin'
    simpa only [hF, htdef] using this
  -- the two outer pieces
  have hcoef2 : (0:ℝ) ≤ Real.pi ^ 2 / 2 := by positivity
  have houtpt : ∀ x : ℝ, x ≠ 0 → |x| ≤ Real.pi → F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by
    intro x hxne hxpi
    rw [hFapp x]
    have hden : 0 < 2 / Real.pi ^ 2 * x ^ 2 := by positivity
    have hlow := inv_anti₀ hden (hout x hxpi)
    have heq : (2 / Real.pi ^ 2 * x ^ 2)⁻¹ = (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := by field_simp
    rw [heq] at hlow
    exact hlow
  have bR : (∫ x in t..Real.pi, F x) ≤ (Real.pi ^ 2 / 2) * (1 / t) := by
    have hpt : ∀ x ∈ Set.Icc t Real.pi, F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := fun x hx =>
      houtpt x (ne_of_gt (lt_of_lt_of_le htpos hx.1))
        (by rw [abs_of_pos (lt_of_lt_of_le htpos hx.1)]; exact hx.2)
    have hg : IntervalIntegrable
        (fun x : ℝ => (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹) volume t Real.pi :=
      (intervalIntegrable_inv_sq htpos htpi).const_mul _
    have hmono := intervalIntegral.integral_mono_on htpi (hFii t Real.pi) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_le htpos htpi) hcoef2)
  have bL : (∫ x in (-Real.pi)..(-t), F x) ≤ (Real.pi ^ 2 / 2) * (1 / t) := by
    have hle : -Real.pi ≤ -t := by linarith
    have hpt : ∀ x ∈ Set.Icc (-Real.pi) (-t), F x ≤ (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹ := fun x hx =>
      houtpt x (ne_of_lt (lt_of_le_of_lt hx.2 (by linarith)))
        (by rw [abs_of_neg (lt_of_le_of_lt hx.2 (by linarith))]; linarith [hx.1])
    have hg : IntervalIntegrable
        (fun x : ℝ => (Real.pi ^ 2 / 2) * (x ^ 2)⁻¹) volume (-Real.pi) (-t) :=
      (intervalIntegrable_inv_sq_neg htpos htpi).const_mul _
    have hmono := intervalIntegral.integral_mono_on hle (hFii (-Real.pi) (-t)) hg hpt
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (integral_inv_sq_neg_le htpos htpi) hcoef2)
  -- the three pieces reassemble the fundamental domain
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) (-t)) (hFii (-t) t)
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (hFii (-Real.pi) t) (hFii t Real.pi)
  have hAsum : (∫ x in (-Real.pi)..Real.pi, F x)
      ≤ Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 * (1 / t) := by
    linarith [e1, e2, bL, bR, hmid]
  -- evaluate `√(AB)` and compare with the stated constant
  have hsqrtAB : Real.sqrt (A * B) = rho / Real.pi * (Real.sqrt (2 * c) * S) := by
    have hABeq : A * B = (rho / Real.pi) ^ 2 * (2 * c * Real.log (1 / rho)) := by
      rw [hAdef, hBdef]; field_simp
    rw [hABeq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_mul (by positivity), hSdef]
  have h2c : (0:ℝ) < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  have hterm1 : (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (A * B))
      = Real.pi / (2 * Real.sqrt (2 * c)) / (rho * S) := by
    rw [hsqrtAB]; field_simp
  have hterm2 : (2 * Real.pi)⁻¹ * (Real.pi ^ 2 * (1 / t))
      ≤ Real.pi / 2 / (rho * S) := by
    have hlhs : (2 * Real.pi)⁻¹ * (Real.pi ^ 2 * (1 / t)) = Real.pi / 2 / t := by
      field_simp
    rw [hlhs]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hrhoS
  rw [torusIntegral_eq_intervalIntegral]
  have hfin : (2 * Real.pi)⁻¹ * (∫ x in (-Real.pi)..Real.pi, F x)
      ≤ (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 * (1 / t)) :=
    mul_le_mul_of_nonneg_left hAsum (by positivity)
  refine hfin.trans ?_
  have hexp : (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (A * B) + Real.pi ^ 2 * (1 / t))
      = (2 * Real.pi)⁻¹ * (Real.pi / Real.sqrt (A * B))
        + (2 * Real.pi)⁻¹ * (Real.pi ^ 2 * (1 / t)) := by ring
  rw [hexp, hterm1]
  have hsplit : (Real.pi / (2 * Real.sqrt (2 * c)) + Real.pi / 2) / (rho * S)
      = Real.pi / (2 * Real.sqrt (2 * c)) / (rho * S) + Real.pi / 2 / (rho * S) := by
    field_simp
  rw [hsplit]
  linarith [hterm2]

end Manhattan.V4.Beta
