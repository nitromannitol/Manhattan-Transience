import Manhattan.Estimates.Elementary
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A direct Hilbert--Schmidt bound for integral kernels on the torus

Mathlib v4.26.0 has no theorem bounding the operator norm of an integral
operator by the Hilbert--Schmidt norm of its kernel, and no Schur test.  This
file proves the inequality that Step 3 of Lemma 5.4 needs, directly from
Cauchy--Schwarz and Tonelli:
for a kernel `k` and a function `g` on the torus,
`∫ |∫ k s t * g t dm t|² dm s ≤ (∫∫ k²) * (∫ g²)`.

Everything is stated for `Manhattan.Estimates.torusIntegral`, the normalized
Haar integral on `(-π,π]`.  The file also collects the elementary
one-dimensional integrals that the instantiation in `KernelBoundError.lean`
uses.

Paper: `manuscript.tex:1374-1398`.
-/

open MeasureTheory Set

namespace Manhattan.Estimates

noncomputable section

local instance kernelBoundPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### Basic facts about the normalized torus integral -/

theorem measurableSet_torus : MeasurableSet torus := measurableSet_Ioc

theorem volume_torus : volume torus = ENNReal.ofReal (2 * Real.pi) := by
  rw [torus, Real.volume_Ioc]
  ring_nf

theorem volume_torus_ne_top : volume torus ≠ ⊤ := by
  rw [volume_torus]
  exact ENNReal.ofReal_ne_top

theorem torusIntegral_nonneg' {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ torusIntegral f := by
  rw [torusIntegral, smul_eq_mul]
  exact mul_nonneg (by positivity) (integral_nonneg fun x => hf x)

theorem torusIntegral_mono' {f g : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hg : Integrable g (volume.restrict torus))
    (hfg : ∀ x, f x ≤ g x) :
    torusIntegral f ≤ torusIntegral g := by
  rw [torusIntegral, torusIntegral]
  simp only [smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall hf) hg
    (Filter.Eventually.of_forall hfg)

theorem torusIntegral_mono_on {f g : ℝ → ℝ}
    (hf : ∀ x ∈ torus, 0 ≤ f x)
    (hg : Integrable g (volume.restrict torus))
    (hfg : ∀ x ∈ torus, f x ≤ g x) :
    torusIntegral f ≤ torusIntegral g := by
  rw [torusIntegral, torusIntegral]
  simp only [smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono_of_nonneg ?_ hg ?_
  · exact (ae_restrict_iff' measurableSet_torus).mpr (Filter.Eventually.of_forall hf)
  · exact (ae_restrict_iff' measurableSet_torus).mpr (Filter.Eventually.of_forall hfg)

theorem torusIntegral_smul_left (c : ℝ) (f : ℝ → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  simp only [torusIntegral, integral_const_mul, smul_eq_mul]
  ring

theorem torusIntegral_const' (c : ℝ) : torusIntegral (fun _ : ℝ => c) = c := by
  have := torusIntegral_smul_left c (fun _ : ℝ => (1 : ℝ))
  simpa [torusIntegral_one] using this

instance isFiniteMeasure_restrict_torus :
    IsFiniteMeasure (volume.restrict torus) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_top_iff_ne_top.mpr volume_torus_ne_top

/-- A bounded measurable function is integrable on the torus. -/
theorem integrableOn_torus_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) : Integrable f (volume.restrict torus) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- The normalized measure of a closed subinterval of the torus. -/
theorem torusIntegral_indicator_const_Icc {u v c : ℝ} (huv : u ≤ v)
    (hsub : Set.Icc u v ⊆ torus) :
    torusIntegral (fun t => if t ∈ Set.Icc u v then c else 0) =
      (2 * Real.pi)⁻¹ * (c * (v - u)) := by
  rw [torusIntegral, smul_eq_mul]
  congr 1
  have hfun : (fun t : ℝ => if t ∈ Set.Icc u v then c else 0) =
      (Set.Icc u v).indicator (fun _ => c) := by
    funext t
    by_cases h : t ∈ Set.Icc u v <;> simp [h]
  rw [hfun, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr hsub, setIntegral_const, smul_eq_mul, measureReal_def,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-! ### Cauchy--Schwarz -/

/-- The elementary optimization behind Cauchy--Schwarz. -/
theorem sq_le_mul_of_two_abs_le {X A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * |X| ≤ t * A + t⁻¹ * B) : X ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0`: letting `t → ∞` forces `X = 0`.
    have hX : X = 0 := by
      by_contra hXne
      have hXpos : 0 < |X| := abs_pos.mpr hXne
      have ht : 0 < (B + 1) / |X| := by positivity
      have := h _ ht
      rw [← hA0] at this
      have hinv : ((B + 1) / |X|)⁻¹ * B = |X| * B / (B + 1) := by
        field_simp
      rw [hinv] at this
      have hlt : |X| * B / (B + 1) < |X| := by
        rw [div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    simp [hX, ← hA0]
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · -- `B = 0`: letting `t → 0` forces `X = 0`.
      have hX : X = 0 := by
        by_contra hXne
        have hXpos : 0 < |X| := abs_pos.mpr hXne
        have ht : 0 < |X| / (A + 1) := by positivity
        have := h _ ht
        rw [← hB0] at this
        have hlt : |X| / (A + 1) * A < |X| := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
        simp only [mul_zero, add_zero] at this
        linarith
      simp [hX, ← hB0]
    · -- the genuine case, at `t = √(B/A)`.
      have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
      have ht : 0 < Real.sqrt B / Real.sqrt A := div_pos hsB hsA
      have hkey := h _ ht
      have hA' : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
      have hB' : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
      have hval : Real.sqrt B / Real.sqrt A * A +
          (Real.sqrt B / Real.sqrt A)⁻¹ * B =
          2 * (Real.sqrt A * Real.sqrt B) := by
        field_simp
        nlinarith [hA', hB']
      rw [hval] at hkey
      have habs : |X| ≤ Real.sqrt A * Real.sqrt B := by linarith
      have h2 : X ^ 2 = |X| ^ 2 := (sq_abs X).symm
      nlinarith [abs_nonneg X, Real.sqrt_nonneg A, Real.sqrt_nonneg B]

/-- Cauchy--Schwarz for the normalized torus integral. -/
theorem torusIntegral_mul_sq_le {f g : ℝ → ℝ}
    (hf : Integrable (fun t => f t ^ 2) (volume.restrict torus))
    (hg : Integrable (fun t => g t ^ 2) (volume.restrict torus)) :
    (torusIntegral fun t => f t * g t) ^ 2 ≤
      (torusIntegral fun t => f t ^ 2) * (torusIntegral fun t => g t ^ 2) := by
  refine sq_le_mul_of_two_abs_le (torusIntegral_nonneg' fun t => sq_nonneg _)
    (torusIntegral_nonneg' fun t => sq_nonneg _) ?_
  intro t ht
  have habs : |torusIntegral fun s => f s * g s| ≤
      torusIntegral (fun s => |f s * g s|) := by
    rw [torusIntegral, torusIntegral, smul_eq_mul, smul_eq_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi)⁻¹)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
  have hmaj : ∀ s : ℝ, 2 * |f s * g s| ≤ t * f s ^ 2 + t⁻¹ * g s ^ 2 := by
    intro s
    have hkey : 0 ≤ t⁻¹ * (t * |f s| - |g s|) ^ 2 :=
      mul_nonneg (inv_pos.mpr ht).le (sq_nonneg _)
    have hid : t * |f s| ^ 2 + t⁻¹ * |g s| ^ 2 - 2 * (|f s| * |g s|) =
        t⁻¹ * (t * |f s| - |g s|) ^ 2 := by
      field_simp
      ring
    rw [abs_mul, ← sq_abs (f s), ← sq_abs (g s)]
    linarith
  have hint2 : Integrable (fun s => t * f s ^ 2 + t⁻¹ * g s ^ 2)
      (volume.restrict torus) := (hf.const_mul t).add (hg.const_mul t⁻¹)
  have hmono : torusIntegral (fun s => 2 * |f s * g s|) ≤
      torusIntegral (fun s => t * f s ^ 2 + t⁻¹ * g s ^ 2) :=
    torusIntegral_mono' (fun s => by positivity) hint2 hmaj
  have hright : torusIntegral (fun s => t * f s ^ 2 + t⁻¹ * g s ^ 2) =
      t * torusIntegral (fun s => f s ^ 2) + t⁻¹ * torusIntegral (fun s => g s ^ 2) := by
    simp only [torusIntegral, smul_eq_mul]
    rw [integral_add (hf.const_mul t) (hg.const_mul t⁻¹), integral_const_mul,
      integral_const_mul]
    ring
  have hleft : torusIntegral (fun s => 2 * |f s * g s|) =
      2 * torusIntegral (fun s => |f s * g s|) := torusIntegral_smul_left 2 _
  rw [hleft, hright] at hmono
  linarith

/-! ### The Hilbert--Schmidt bound -/

/-- The Hilbert--Schmidt bound at a fixed output frequency: an integral
operator with kernel `k` maps `g` to a value whose square is at most the
product of the kernel energy and the energy of `g`. -/
theorem torusIntegral_kernel_sq_le {k g : ℝ → ℝ} {HS E : ℝ}
    (hk : Integrable (fun t => k t ^ 2) (volume.restrict torus))
    (hg : Integrable (fun t => g t ^ 2) (volume.restrict torus))
    (hHS : torusIntegral (fun t => k t ^ 2) ≤ HS)
    (hE : torusIntegral (fun t => g t ^ 2) ≤ E)
    (hEnn : 0 ≤ E) :
    (torusIntegral fun t => k t * g t) ^ 2 ≤ HS * E := by
  refine (torusIntegral_mul_sq_le hk hg).trans ?_
  have h1 : 0 ≤ torusIntegral (fun t => k t ^ 2) :=
    torusIntegral_nonneg' fun _ => sq_nonneg _
  have h2 : 0 ≤ torusIntegral (fun t => g t ^ 2) :=
    torusIntegral_nonneg' fun _ => sq_nonneg _
  nlinarith

/-- The Hilbert--Schmidt bound for an integral operator on the torus.  This is
the replacement for the missing Mathlib theorem
`‖∫ k(s,t) φ(t) dt‖_{L²} ≤ ‖k‖_{HS} ‖φ‖_{L²}`: it is proved directly from
Cauchy--Schwarz in `t` and monotonicity in `s`, and it needs no
Hilbert--Schmidt operator theory.

Step 3 of Lemma 5.4 actually goes
through `Manhattan.Estimates.torusIntegral_kernel_sq_le`
(`Manhattan/Estimates/KernelBoundError.lean:966`). -/
theorem torusIntegral_hilbertSchmidt_le {k : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    (hk : ∀ s, Integrable (fun t => k s t ^ 2) (volume.restrict torus))
    (hg : Integrable (fun t => g t ^ 2) (volume.restrict torus))
    (hHS : Integrable (fun s => torusIntegral fun t => k s t ^ 2)
      (volume.restrict torus)) :
    torusIntegral (fun s => (torusIntegral fun t => k s t * g t) ^ 2) ≤
      (torusIntegral fun s => torusIntegral fun t => k s t ^ 2) *
        (torusIntegral fun t => g t ^ 2) := by
  have hpt : ∀ s : ℝ, (torusIntegral fun t => k s t * g t) ^ 2 ≤
      (torusIntegral fun t => g t ^ 2) * (torusIntegral fun t => k s t ^ 2) := by
    intro s
    rw [mul_comm]
    exact torusIntegral_mul_sq_le (hk s) hg
  calc torusIntegral (fun s => (torusIntegral fun t => k s t * g t) ^ 2)
      ≤ torusIntegral (fun s => (torusIntegral fun t => g t ^ 2) *
          (torusIntegral fun t => k s t ^ 2)) :=
        torusIntegral_mono' (fun _ => sq_nonneg _) (hHS.const_mul _) hpt
    _ = (torusIntegral fun s => torusIntegral fun t => k s t ^ 2) *
          (torusIntegral fun t => g t ^ 2) := by
        rw [torusIntegral_smul_left]
        ring

/-! ### The elementary one-dimensional integrals -/

/-- The normalized measure of a measurable subset of an interval. -/
theorem torusIntegral_indicator_const_le {S : Set ℝ} {c d M : ℝ}
    (hS : MeasurableSet S) (hSub : S ⊆ Set.Icc c d) (hcd : c ≤ d) (hM : 0 ≤ M) :
    torusIntegral (fun t => if t ∈ S then M else 0) ≤
      (2 * Real.pi)⁻¹ * (M * (d - c)) := by
  have hval : torusIntegral (fun t => if t ∈ S then M else 0) =
      (2 * Real.pi)⁻¹ * ((volume (torus ∩ S)).toReal * M) := by
    rw [torusIntegral, smul_eq_mul]
    congr 1
    change (∫ t in torus, S.indicator (fun _ => M) t) = _
    rw [integral_indicator hS, Measure.restrict_restrict hS, setIntegral_const,
      smul_eq_mul, Set.inter_comm, measureReal_def]
  rw [hval]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hmeas : volume (torus ∩ S) ≤ ENNReal.ofReal (d - c) := by
    refine le_trans (measure_mono (Set.inter_subset_right.trans hSub)) ?_
    rw [Real.volume_Icc]
  have hle : (volume (torus ∩ S)).toReal ≤ d - c := by
    refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas) ?_
    rw [ENNReal.toReal_ofReal (by linarith)]
  nlinarith

/-- `∫_A^B x⁻³ dx ≤ 1/(2A²)` for `0 < A ≤ B`. -/
theorem intervalIntegral_inv_cube_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, (x ^ 3)⁻¹) ≤ 1 / (2 * A ^ 2) := by
  have hmem : ∀ x ∈ Set.uIcc A B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    exact lt_of_lt_of_le hA hx.1
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun y : ℝ => -(1 / 2 : ℝ) * (y ^ 2)⁻¹) ((x ^ 3)⁻¹) x := by
    intro x hx
    have hx0 : 0 < x := hmem x hx
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ 1) x := by
      simpa using hasDerivAt_pow 2 x
    have hinv : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹)
        (-(2 * x ^ 1) / (x ^ 2) ^ 2) x := hpow.inv (by positivity)
    have hres := hinv.const_mul (-(1 / 2 : ℝ))
    have heq : -(1 / 2 : ℝ) * (-(2 * x ^ 1) / (x ^ 2) ^ 2) = (x ^ 3)⁻¹ := by
      field_simp
    rw [heq] at hres
    exact hres
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 3)⁻¹) volume A B := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    have := hmem y hy
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have h1 : -(1 / 2 : ℝ) * (B ^ 2)⁻¹ ≤ 0 := by
    have : (0 : ℝ) < (B ^ 2)⁻¹ := by positivity
    nlinarith
  have h2 : -(1 / 2 : ℝ) * (A ^ 2)⁻¹ = -(1 / (2 * A ^ 2)) := by
    field_simp
  rw [h2]
  linarith

/-- The tail integral `∫ 1_{s ≥ A} s⁻³ dm(s) ≤ (2π)⁻¹/(2A²)` on the torus. -/
theorem torusIntegral_indicator_inv_cube_le {A : ℝ} (hA : 0 < A) :
    torusIntegral (fun s => if A ≤ s then (s ^ 3)⁻¹ else 0) ≤
      (2 * Real.pi)⁻¹ * (1 / (2 * A ^ 2)) := by
  rcases le_or_gt A Real.pi with hApi | hApi
  · have hIccSub : Set.Icc A Real.pi ⊆ torus := by
      intro x hx
      exact ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) hx.1, hx.2⟩
    have hcongr : ∀ x ∈ torus,
        (if A ≤ x then (x ^ 3)⁻¹ else 0) =
          (Set.Icc A Real.pi).indicator (fun y => (y ^ 3)⁻¹) x := by
      intro x hx
      by_cases hxA : A ≤ x
      · rw [if_pos hxA, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hxA, hx.2⟩)]
      · rw [if_neg hxA, Set.indicator_of_notMem (by simp [hxA])]
    have hstep : torusIntegral (fun s => if A ≤ s then (s ^ 3)⁻¹ else 0) =
        (2 * Real.pi)⁻¹ * ∫ x in A..Real.pi, (x ^ 3)⁻¹ := by
      rw [torusIntegral, smul_eq_mul]
      congr 1
      rw [setIntegral_congr_fun measurableSet_torus hcongr,
        integral_indicator measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Icc,
        Set.inter_eq_left.mpr hIccSub, MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hApi]
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (intervalIntegral_inv_cube_le hA hApi)
      (by positivity)
  · have hzeroOn : ∀ x ∈ torus, (if A ≤ x then (x ^ 3)⁻¹ else 0) = 0 := by
      intro x hx
      exact if_neg (by linarith [hx.2])
    have hval : torusIntegral (fun s => if A ≤ s then (s ^ 3)⁻¹ else 0) = 0 := by
      rw [torusIntegral, smul_eq_mul,
        setIntegral_congr_fun measurableSet_torus hzeroOn, integral_zero, mul_zero]
    rw [hval]
    positivity

/-- The paper's Hilbert--Schmidt tail integral at `manuscript.tex:1389-1393`:
`∫₀^T β² dt/(t+|β|)³ ≤ 1/2`, uniformly in the cutoff `T`. -/
theorem betaCubeTailIntegral_le {b T : ℝ} (hb : 0 < b) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, b ^ 2 / (t + b) ^ 3) ≤ 1 / 2 := by
  have hbne : b ≠ 0 := hb.ne'
  have hmem : ∀ x ∈ Set.uIcc (0 : ℝ) T, 0 < x + b := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h
    · linarith [h.1]
    · linarith [h.1]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun y : ℝ => -(b ^ 2) / 2 * ((y + b) ^ 2)⁻¹)
        (b ^ 2 / (x + b) ^ 3) x := by
    intro x hx
    have hxb : 0 < x + b := hmem x hx
    have hbase : HasDerivAt (fun y : ℝ => y + b) 1 x :=
      (hasDerivAt_id x).add_const b
    have hpow : HasDerivAt (fun y : ℝ => (y + b) ^ 2) (2 * (x + b) ^ 1 * 1) x :=
      hbase.pow 2
    have hinv : HasDerivAt (fun y : ℝ => ((y + b) ^ 2)⁻¹)
        (-(2 * (x + b) ^ 1 * 1) / ((x + b) ^ 2) ^ 2) x :=
      hpow.inv (by positivity)
    have hres := hinv.const_mul (-(b ^ 2) / 2)
    have heq2 : -(b ^ 2) / 2 * (-(2 * (x + b) ^ 1 * 1) / ((x + b) ^ 2) ^ 2) =
        b ^ 2 / (x + b) ^ 3 := by
      field_simp
    rw [heq2] at hres
    exact hres
  have hint : IntervalIntegrable (fun x : ℝ => b ^ 2 / (x + b) ^ 3) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro y hy
    have := hmem y hy
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hTb : 0 < T + b := by linarith
  have hupper : -(b ^ 2) / 2 * ((T + b) ^ 2)⁻¹ ≤ 0 := by
    have h2 : (0 : ℝ) < ((T + b) ^ 2)⁻¹ := by positivity
    nlinarith [sq_nonneg b]
  have hzero : -(b ^ 2) / 2 * (((0 : ℝ) + b) ^ 2)⁻¹ = -(1 / 2) := by
    rw [zero_add]
    field_simp
  rw [hzero]
  linarith

end

end Manhattan.Estimates
