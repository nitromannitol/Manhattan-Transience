import Manhattan.V4.EvenMajorant

/-!
# Version 4, Step 3: the four parity cancellations

This file formalizes the parity construction of the Version 4 argument
(Step 3, reused verbatim in the `VERSION 4` section with `a` replaced by `δ`),
in the concrete raw frequency model of `Manhattan/Glue/ProjectionDischarge.lean`:
a raw type-`112` coefficient is a function `k : ℝ → ℝ → ℝ → ℂ` of the shifted
frequencies `(r, r', β)`, the two lowering components are
`Manhattan.Glue.rawD2StarMixed` and `Manhattan.Glue.rawD2StarTwoRow`, and `Π₃`
is `Manhattan.Glue.rawOffDiagonalPart`.

The competitor is

  `σ(r,β) = sin²β ∫ dm(r')/M(r,r',β)`,   `B(r,β) = λ + d(r) + d(β)`,
  `v = w/(B+σ)`,                          `K(r,r',β) = (i sin β/(√2 M)) (v(r,β) + v(r',β))`,
  `k = Π K`.

Everything rests on three parities, proved first as named lemmas:

* `v` is **odd** in the row frequency `r` and **even** in the column
  frequency `β` (`ParityProfile`);
* `M` is **even in each variable separately** and symmetric in `(r,r')`
  (`Manhattan/V4/EvenMajorant.lean`);
* consequently `σ` and `B` are even in both variables, so `v = w/(B+σ)`
  inherits the parity of `w`.

The four consequences are exact identities, not estimates:

* `parityJ_row_eq_zero` **(P1)**: `∫ v(r',β)/M(r,r',β) dm(r') = 0`, hence
  `rawD2StarMixed_parityKernel`: `(D₂*K)₁₂ = (√2)⁻¹ σ v`;
* `torusIntegral_diagonal_correction_eq_zero` **(P2)**: the projection makes
  **no** mixed correction, `rawD2StarMixed_offDiagonalPart`:
  `(D₂*k)₁₂ = (D₂*K)₁₂`;
* `rawD2StarTwoRow_offDiagonalPart` **(P3)**: `K` is odd in `β`, so
  `(D₂*k)₁₁ = 0`;
* `evenMajorantEnergy_parityKernel` **(P4)**: the cross term vanishes, so
  `∫ M|K|² = ∫ σ|v|²`.

In the old proof (P1)--(P2) were the content of Lemma 5.3, an *estimate* with a
long audit chain.  Under parity they are identities.

## The one normalization discrepancy

With the note's `K = (i sin β/(√2 M))(v + v')` and the **ordered** raw integrals
of `Manhattan.Glue.rawMultiplierEnergy` (which is how the existing development
normalizes the multiplier energy), (P4) holds exactly as the note states it,
`∫ M|K|² = ∫ σ|v|²`, but (P1) gives `(D₂*K)₁₂ = (√2)⁻¹ σ v`, not `σ v`.  The
two claims cannot both hold for one `K`: dropping the `√2` gives `(D₂*K)₁₂ = σ v`
and `∫ M|K|² = 2 ∫ σ|v|²`.  The factor is exactly the one the existing
development already carries as an identity in
`Manhattan.Glue.rawCubicMultiplierEnergy_eq_two_correctionSigmaEnergy` ("the
factor 2 is not slack: it is the two disjoint summands of the symmetrized
coefficient"), i.e. it is ordered-versus-unordered row pairs.  It is a
normalization, not a gap: the scalar completion of the square is applied with
whichever constant the chosen normalization produces, and only the value of the
absolute constant `C` in Move 1 changes.  `parityKernel` is stated with a free
complex scale `c` so that both conventions are available; `c = (√2)⁻¹` is the
note's.
-/

open MeasureTheory

namespace Manhattan.V4

noncomputable section

/-! ## Torus calculus used by the parity arguments -/

theorem torusIntegral_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E) :
    (Estimates.torusIntegral fun s => g (-s)) = Estimates.torusIntegral g := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold Estimates.torusIntegral Estimates.torus
  congr 1
  rw [← intervalIntegral.integral_of_le hpi, ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_neg]
  simp

/-- The normalized integral of an odd function vanishes. -/
theorem torusIntegral_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} (hg : ∀ s, g (-s) = -g s) :
    Estimates.torusIntegral g = 0 := by
  have h1 : (Estimates.torusIntegral fun s => g (-s)) = Estimates.torusIntegral g :=
    torusIntegral_comp_neg g
  have h2 : (Estimates.torusIntegral fun s => g (-s)) = -Estimates.torusIntegral g := by
    simp only [hg]
    rw [Estimates.torusIntegral, Estimates.torusIntegral, integral_neg, smul_neg]
  rw [h1] at h2
  have h3 : (2 : ℝ) • Estimates.torusIntegral g = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h2]
    simp
  simpa using h3

theorem torusIntegral_neg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (Estimates.torusIntegral fun x => -f x) = -Estimates.torusIntegral f := by
  rw [Estimates.torusIntegral, Estimates.torusIntegral, integral_neg, smul_neg]

theorem torusIntegral_real_smul (c : ℝ) (f : ℝ → ℝ) :
    (Estimates.torusIntegral fun x => c * f x) = c * Estimates.torusIntegral f := by
  simp only [Estimates.torusIntegral, integral_const_mul, smul_eq_mul]
  ring

theorem torusIntegral_ofReal (f : ℝ → ℝ) :
    (Estimates.torusIntegral fun x => ((f x : ℝ) : ℂ))
      = ((Estimates.torusIntegral f : ℝ) : ℂ) := by
  unfold Estimates.torusIntegral
  rw [integral_complex_ofReal]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]

theorem integrable_torus_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f (volume.restrict Estimates.torus) :=
  Glue.integrable_torus_of_bound hf.aestronglyMeasurable
    (fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem torusIntegral_add_of_bounded {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ D) :
    (Estimates.torusIntegral fun x => f x + g x)
      = Estimates.torusIntegral f + Estimates.torusIntegral g :=
  Glue.torusIntegral_add (integrable_torus_of_abs_le hf hfC)
    (integrable_torus_of_abs_le hg hgC)

theorem torusIntegral_sub_of_bounded {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hfC : ∀ x, |f x| ≤ C) (hgC : ∀ x, |g x| ≤ D) :
    (Estimates.torusIntegral fun x => f x - g x)
      = Estimates.torusIntegral f - Estimates.torusIntegral g :=
  Glue.torusIntegral_sub (integrable_torus_of_abs_le hf hfC)
    (integrable_torus_of_abs_le hg hgC)

theorem torusIntegral_swap_of_bounded {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2) {C : ℝ} (hC : ∀ x y, |F x y| ≤ C) :
    (Estimates.torusIntegral fun x => Estimates.torusIntegral fun y => F x y)
      = Estimates.torusIntegral fun y => Estimates.torusIntegral fun x => F x y :=
  Glue.torusIntegral_swap
    (Glue.integrable_prod_torus_of_bound (C := C) hF.aestronglyMeasurable
      (fun z => by rw [Real.norm_eq_abs]; exact hC z.1 z.2))

theorem dispersion_neg (s : ℝ) : Estimates.dispersion (-s) = Estimates.dispersion s := by
  unfold Estimates.dispersion
  rw [Real.cos_neg]

/-! ## The profile `v` -/

/-- The parity data of the degree-one profile.  `v` is odd in the row
frequency and even in the column frequency, and is a bounded measurable
`2π`-periodic function of the row frequency. -/
structure ParityProfile where
  /-- The profile itself. -/
  toFun : ℝ → ℝ → ℝ
  /-- Joint measurability. -/
  meas : Measurable fun z : ℝ × ℝ => toFun z.1 z.2
  /-- A uniform bound. -/
  bound : ℝ
  /-- The uniform bound. -/
  abs_le : ∀ r beta, |toFun r beta| ≤ bound
  /-- `v` is odd in the row frequency. -/
  odd_row : ∀ r beta, toFun (-r) beta = -toFun r beta
  /-- `v` is even in the column frequency. -/
  even_col : ∀ r beta, toFun r (-beta) = toFun r beta
  /-- `v` is a function on the torus in the row frequency. -/
  periodic_row : ∀ beta, Function.Periodic (fun r => toFun r beta) (2 * Real.pi)

namespace ParityProfile

variable (v : ParityProfile)

theorem bound_nonneg : 0 ≤ v.bound := le_trans (abs_nonneg _) (v.abs_le 0 0)

theorem measurable_row (beta : ℝ) : Measurable fun r => v.toFun r beta :=
  v.meas.comp (measurable_id.prodMk measurable_const)

end ParityProfile

/-- The Version 4 degree-one profile `w(r) = sin r · φ(r)`
(`VERSION 4`, verification of (1)) with `φ` real and even: it is odd in `r` and
constant, hence even, in `β`.  Recorded so that the parity hypotheses are
visibly non-vacuous. -/
def sineProfile (phi : ℝ → ℝ) (hmeas : Measurable phi) (B : ℝ)
    (hB : ∀ r, |phi r| ≤ B) (heven : ∀ r, phi (-r) = phi r)
    (hper : Function.Periodic phi (2 * Real.pi)) : ParityProfile where
  toFun := fun r _ => Real.sin r * phi r
  meas := (Real.measurable_sin.comp measurable_fst).mul (hmeas.comp measurable_fst)
  bound := B
  abs_le := by
    intro r _
    have h1 := Real.abs_sin_le_one r
    have h2 := hB r
    have hBn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
    rw [abs_mul]
    nlinarith [abs_nonneg (Real.sin r), abs_nonneg (phi r)]
  odd_row := by
    intro r _
    show Real.sin (-r) * phi (-r) = -(Real.sin r * phi r)
    rw [Real.sin_neg, heven]
    ring
  even_col := fun _ _ => rfl
  periodic_row := by
    intro _ r
    show Real.sin (r + 2 * Real.pi) * phi (r + 2 * Real.pi) = Real.sin r * phi r
    rw [Real.sin_add_two_pi, hper r]

/-! ## `J`, `σ` and `B` -/

/-- The fibre integral `J(r,β) = ∫ dm(r')/M(r,r',β)`. -/
def parityJ (kappa delta r beta : ℝ) : ℝ :=
  Estimates.torusIntegral fun r' => (evenMajorant kappa delta r r' beta)⁻¹

/-- The logarithmic correction `σ(r,β) = sin²β ∫ dm(r')/M(r,r',β)`. -/
def paritySigma (kappa delta r beta : ℝ) : ℝ :=
  Real.sin beta ^ 2 * parityJ kappa delta r beta

variable {kappa delta : ℝ}

theorem parityJ_neg_row (r beta : ℝ) :
    parityJ kappa delta (-r) beta = parityJ kappa delta r beta := by
  unfold parityJ
  congr 1
  funext r'
  rw [evenMajorant_neg_row]

theorem parityJ_neg_col (r beta : ℝ) :
    parityJ kappa delta r (-beta) = parityJ kappa delta r beta := by
  unfold parityJ
  congr 1
  funext r'
  rw [evenMajorant_neg_col]

theorem parityJ_nonneg (hkappa : 0 < kappa) (hdelta : 0 < delta) (r beta : ℝ) :
    0 ≤ parityJ kappa delta r beta :=
  Glue.torusIntegral_nonneg fun r' =>
    inv_nonneg.mpr (evenMajorant_pos hkappa hdelta r r' beta).le

theorem parityJ_le (hkappa : 0 < kappa) (hdelta : 0 < delta) (r beta : ℝ) :
    parityJ kappa delta r beta ≤ (kappa * delta)⁻¹ := by
  unfold parityJ
  refine le_trans (le_abs_self _)
    (Glue.abs_torusIntegral_le (C := (kappa * delta)⁻¹) fun r' => ?_)
  rw [abs_of_nonneg (inv_nonneg.mpr (evenMajorant_pos hkappa hdelta r r' beta).le)]
  exact inv_anti₀ (by positivity) (mul_le_evenMajorant hkappa.le delta r r' beta)

theorem parityJ_measurable :
    Measurable fun z : ℝ × ℝ => parityJ kappa delta z.1 z.2 := by
  have h : StronglyMeasurable fun w : (ℝ × ℝ) × ℝ =>
      (evenMajorant kappa delta w.1.1 w.2 w.1.2)⁻¹ := by
    refine (Measurable.inv ?_).stronglyMeasurable
    exact (evenMajorant_measurable kappa delta).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact (Glue.stronglyMeasurable_torusIntegral h).measurable

theorem paritySigma_neg_row (r beta : ℝ) :
    paritySigma kappa delta (-r) beta = paritySigma kappa delta r beta := by
  rw [paritySigma, paritySigma, parityJ_neg_row]

theorem paritySigma_neg_col (r beta : ℝ) :
    paritySigma kappa delta r (-beta) = paritySigma kappa delta r beta := by
  rw [paritySigma, paritySigma, parityJ_neg_col, Real.sin_neg, neg_sq]

theorem paritySigma_nonneg (hkappa : 0 < kappa) (hdelta : 0 < delta) (r beta : ℝ) :
    0 ≤ paritySigma kappa delta r beta :=
  mul_nonneg (sq_nonneg _) (parityJ_nonneg hkappa hdelta r beta)

theorem correctionB_neg_row (q : Estimates.Parameters) (r beta : ℝ) :
    Estimates.correctionB q (-r) beta = Estimates.correctionB q r beta := by
  rw [Estimates.correctionB, Estimates.correctionB, dispersion_neg]

theorem correctionB_neg_col (q : Estimates.Parameters) (r beta : ℝ) :
    Estimates.correctionB q r (-beta) = Estimates.correctionB q r beta := by
  rw [Estimates.correctionB, Estimates.correctionB, dispersion_neg]

theorem correctionB_ge (q : Estimates.Parameters) (r beta : ℝ) :
    q.lambda ≤ Estimates.correctionB q r beta := by
  have h1 := Estimates.dispersion_nonneg r
  have h2 := Estimates.dispersion_nonneg beta
  rw [Estimates.correctionB]
  linarith

/-! ## The kernel `K` -/

/-- The real profile of the type-`112` kernel:
`(v(r,β) + v(r',β)) / (√2 M(r,r',β))`. -/
def parityKernelReal (kappa delta : ℝ) (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) : ℝ :=
  (v r beta + v r' beta) / (Real.sqrt 2 * evenMajorant kappa delta r r' beta)

/-- The symmetric type-`112` kernel
`K(r,r',β) = (i sin β / (√2 M)) (v(r,β) + v(r',β))`. -/
def parityKernel (kappa delta : ℝ) (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) : ℂ :=
  Complex.I * (Real.sin beta : ℂ) * ((parityKernelReal kappa delta v r r' beta : ℝ) : ℂ)

/-- `K` in the form written in the note. -/
theorem parityKernel_eq (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) :
    parityKernel kappa delta v r r' beta =
      Complex.I * (Real.sin beta : ℂ) /
          ((Real.sqrt 2 * evenMajorant kappa delta r r' beta : ℝ) : ℂ) *
        ((v r beta : ℂ) + (v r' beta : ℂ)) := by
  have hM : (0:ℝ) < Real.sqrt 2 * evenMajorant kappa delta r r' beta := by
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact mul_pos h2 (evenMajorant_pos hkappa hdelta r r' beta)
  have hMne : ((Real.sqrt 2 * evenMajorant kappa delta r r' beta : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hM.ne'
  rw [parityKernel, parityKernelReal]
  push_cast
  field_simp

/-! ### Parity of the kernel -/

theorem parityKernelReal_swap (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) :
    parityKernelReal kappa delta v r r' beta = parityKernelReal kappa delta v r' r beta := by
  rw [parityKernelReal, parityKernelReal, evenMajorant_swap]
  ring_nf

theorem parityKernelReal_neg_col (v : ParityProfile) (r r' beta : ℝ) :
    parityKernelReal kappa delta v.toFun r r' (-beta)
      = parityKernelReal kappa delta v.toFun r r' beta := by
  rw [parityKernelReal, parityKernelReal, evenMajorant_neg_col, v.even_col, v.even_col]

/-- `K` is odd under simultaneous negation of the two row frequencies: this is
what makes the fibre average odd. -/
theorem parityKernelReal_neg_row_pair (v : ParityProfile) (r r' beta : ℝ) :
    parityKernelReal kappa delta v.toFun (-r) (-r') beta
      = -parityKernelReal kappa delta v.toFun r r' beta := by
  rw [parityKernelReal, parityKernelReal, evenMajorant_neg_row, evenMajorant_neg_row',
    v.odd_row, v.odd_row]
  ring

theorem parityKernelReal_periodic_row' (v : ParityProfile) (r beta : ℝ) :
    Function.Periodic (fun r' => parityKernelReal kappa delta v.toFun r r' beta)
      (2 * Real.pi) := by
  intro r'
  have hv : v.toFun (r' + 2 * Real.pi) beta = v.toFun r' beta := v.periodic_row beta r'
  have hM : evenMajorant kappa delta r (r' + 2 * Real.pi) beta
      = evenMajorant kappa delta r r' beta :=
    evenMajorant_periodic_row' kappa delta r beta r'
  show parityKernelReal kappa delta v.toFun r (r' + 2 * Real.pi) beta
      = parityKernelReal kappa delta v.toFun r r' beta
  rw [parityKernelReal, parityKernelReal, hv, hM]

/-- `K` is odd in the column frequency. -/
theorem parityKernel_neg_col (v : ParityProfile) (r r' beta : ℝ) :
    parityKernel kappa delta v.toFun r r' (-beta)
      = -parityKernel kappa delta v.toFun r r' beta := by
  rw [parityKernel, parityKernel, parityKernelReal_neg_col, Real.sin_neg]
  push_cast
  ring

theorem parityKernel_neg_row_pair (v : ParityProfile) (r r' beta : ℝ) :
    parityKernel kappa delta v.toFun (-r) (-r') beta
      = -parityKernel kappa delta v.toFun r r' beta := by
  rw [parityKernel, parityKernel, parityKernelReal_neg_row_pair]
  push_cast
  ring

theorem parityKernel_periodic_row' (v : ParityProfile) (r beta : ℝ) :
    Function.Periodic (fun r' => parityKernel kappa delta v.toFun r r' beta)
      (2 * Real.pi) := by
  intro r'
  have hK : parityKernelReal kappa delta v.toFun r (r' + 2 * Real.pi) beta
      = parityKernelReal kappa delta v.toFun r r' beta :=
    parityKernelReal_periodic_row' v r beta r'
  show parityKernel kappa delta v.toFun r (r' + 2 * Real.pi) beta
      = parityKernel kappa delta v.toFun r r' beta
  rw [parityKernel, parityKernel, hK]

/-! ### Size and measurability -/

/-- The uniform bound for the real profile of `K`. -/
def parityKernelBound (kappa delta : ℝ) (v : ParityProfile) : ℝ :=
  2 * v.bound / (Real.sqrt 2 * (kappa * delta))

theorem parityKernelReal_abs_le (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (r r' beta : ℝ) :
    |parityKernelReal kappa delta v.toFun r r' beta| ≤ parityKernelBound kappa delta v := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hMpos : (0:ℝ) < evenMajorant kappa delta r r' beta :=
    evenMajorant_pos hkappa hdelta r r' beta
  have hMlow : kappa * delta ≤ evenMajorant kappa delta r r' beta :=
    mul_le_evenMajorant hkappa.le delta r r' beta
  have hnum : |v.toFun r beta + v.toFun r' beta| ≤ 2 * v.bound := by
    have h1 := v.abs_le r beta
    have h2 := v.abs_le r' beta
    exact (abs_add_le _ _).trans (by linarith)
  have hpos : (0:ℝ) < Real.sqrt 2 * (kappa * delta) := mul_pos h2 (mul_pos hkappa hdelta)
  have hvb : 0 ≤ v.bound := v.bound_nonneg
  rw [parityKernelReal, abs_div, parityKernelBound,
    abs_of_pos (mul_pos h2 hMpos)]
  calc |v.toFun r beta + v.toFun r' beta| /
        (Real.sqrt 2 * evenMajorant kappa delta r r' beta)
      ≤ (2 * v.bound) / (Real.sqrt 2 * evenMajorant kappa delta r r' beta) := by
        gcongr
    _ ≤ (2 * v.bound) / (Real.sqrt 2 * (kappa * delta)) := by
        gcongr

theorem parityKernelReal_measurable (v : ParityProfile) :
    Measurable fun z : ℝ × ℝ × ℝ =>
      parityKernelReal kappa delta v.toFun z.1 z.2.1 z.2.2 := by
  unfold parityKernelReal
  have h1 : Measurable fun z : ℝ × ℝ × ℝ => v.toFun z.1 z.2.2 :=
    v.meas.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable fun z : ℝ × ℝ × ℝ => v.toFun z.2.1 z.2.2 :=
    v.meas.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_snd))
  exact (h1.add h2).div (measurable_const.mul (evenMajorant_measurable kappa delta))

theorem parityKernel_measurable (v : ParityProfile) :
    Measurable fun z : ℝ × ℝ × ℝ => parityKernel kappa delta v.toFun z.1 z.2.1 z.2.2 := by
  unfold parityKernel
  refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_sin.comp (measurable_snd.comp measurable_snd))
  · exact Complex.measurable_ofReal.comp (parityKernelReal_measurable v)

theorem norm_parityKernel_le (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (r r' beta : ℝ) :
    ‖parityKernel kappa delta v.toFun r r' beta‖ ≤ parityKernelBound kappa delta v := by
  rw [parityKernel, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hs : |Real.sin beta| ≤ 1 := Real.abs_sin_le_one beta
  have hk := parityKernelReal_abs_le hkappa hdelta v r r' beta
  nlinarith [abs_nonneg (parityKernelReal kappa delta v.toFun r r' beta),
    abs_nonneg (Real.sin beta)]

theorem torusBounded₃_parityKernel (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) : Glue.TorusBoundedThree (parityKernel kappa delta v.toFun) :=
  ⟨parityKernel_measurable v,
    ⟨parityKernelBound kappa delta v, fun r r' beta =>
      norm_parityKernel_le hkappa hdelta v r r' beta⟩⟩

/-! ## (P1): the odd fibre integral vanishes -/

/-- **(P1).**  `∫ v(r',β)/M(r,r',β) dm(r') = 0`: the integrand is odd in `r'`
because `v` is odd in the row frequency and `M` is even in it. -/
theorem parityJ_row_eq_zero (v : ParityProfile) (r beta : ℝ) :
    (Estimates.torusIntegral fun r' =>
      v.toFun r' beta / evenMajorant kappa delta r r' beta) = 0 := by
  refine torusIntegral_of_odd fun r' => ?_
  rw [evenMajorant_neg_row', v.odd_row, neg_div]

/-- The `r'`-integral of the kernel: only the `v(r,β)` summand survives. -/
theorem torusIntegral_parityKernelReal (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (r beta : ℝ) :
    (Estimates.torusIntegral fun r' => parityKernelReal kappa delta v.toFun r r' beta)
      = (Real.sqrt 2)⁻¹ * (v.toFun r beta * parityJ kappa delta r beta) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hMpos : ∀ r' : ℝ, (0:ℝ) < evenMajorant kappa delta r r' beta := fun r' =>
    evenMajorant_pos hkappa hdelta r r' beta
  have hsplit : ∀ r' : ℝ, parityKernelReal kappa delta v.toFun r r' beta
      = (Real.sqrt 2)⁻¹ * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹)
        + (Real.sqrt 2)⁻¹ * (v.toFun r' beta / evenMajorant kappa delta r r' beta) := by
    intro r'
    rw [parityKernelReal]
    field_simp
  rw [funext hsplit]
  have hb1 : ∀ r' : ℝ,
      |(Real.sqrt 2)⁻¹ * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹)|
        ≤ (Real.sqrt 2)⁻¹ * (v.bound * (kappa * delta)⁻¹) := by
    intro r'
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹),
      abs_of_nonneg (inv_nonneg.mpr (hMpos r').le)]
    have hv := v.abs_le r beta
    have hM : (evenMajorant kappa delta r r' beta)⁻¹ ≤ (kappa * delta)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_evenMajorant hkappa.le delta r r' beta)
    have hvb : 0 ≤ v.bound := v.bound_nonneg
    have : |v.toFun r beta| * (evenMajorant kappa delta r r' beta)⁻¹
        ≤ v.bound * (kappa * delta)⁻¹ := by
      refine mul_le_mul hv hM (inv_nonneg.mpr (hMpos r').le) hvb
    nlinarith [this, (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹)]
  have hb2 : ∀ r' : ℝ,
      |(Real.sqrt 2)⁻¹ * (v.toFun r' beta / evenMajorant kappa delta r r' beta)|
        ≤ (Real.sqrt 2)⁻¹ * (v.bound * (kappa * delta)⁻¹) := by
    intro r'
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹),
      abs_of_pos (hMpos r')]
    have hv := v.abs_le r' beta
    have hM : (evenMajorant kappa delta r r' beta)⁻¹ ≤ (kappa * delta)⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_evenMajorant hkappa.le delta r r' beta)
    have hvb : 0 ≤ v.bound := v.bound_nonneg
    have hdiv : |v.toFun r' beta| / evenMajorant kappa delta r r' beta
        ≤ v.bound * (kappa * delta)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hv hM (inv_nonneg.mpr (hMpos r').le) hvb
    nlinarith [hdiv, (by positivity : (0:ℝ) ≤ (Real.sqrt 2)⁻¹)]
  have hmeas1 : Measurable fun r' : ℝ =>
      (Real.sqrt 2)⁻¹ * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹) := by
    refine measurable_const.mul (measurable_const.mul (Measurable.inv ?_))
    exact (evenMajorant_measurable kappa delta).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hmeas2 : Measurable fun r' : ℝ =>
      (Real.sqrt 2)⁻¹ * (v.toFun r' beta / evenMajorant kappa delta r r' beta) := by
    refine measurable_const.mul (Measurable.div (v.measurable_row beta) ?_)
    exact (evenMajorant_measurable kappa delta).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hI1 : (Estimates.torusIntegral fun r' =>
      (Real.sqrt 2)⁻¹ * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹))
      = (Real.sqrt 2)⁻¹ * (v.toFun r beta * parityJ kappa delta r beta) := by
    rw [torusIntegral_real_smul, torusIntegral_real_smul]
    rfl
  have hI2 : (Estimates.torusIntegral fun r' =>
      (Real.sqrt 2)⁻¹ * (v.toFun r' beta / evenMajorant kappa delta r r' beta)) = 0 := by
    rw [torusIntegral_real_smul, parityJ_row_eq_zero v r beta, mul_zero]
  rw [torusIntegral_add_of_bounded hmeas1 hmeas2 hb1 hb2, hI1, hI2, add_zero]

/-- **(P1), the lowering consequence.**  `(D₂* K)₁₂ = (√2)⁻¹ σ v`, an exact
identity: the `v(r',β)` summand integrates to zero. -/
theorem rawD2StarMixed_parityKernel (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (r beta : ℝ) :
    Glue.rawD2StarMixed (parityKernel kappa delta v.toFun) r beta
      = (((Real.sqrt 2)⁻¹ * (paritySigma kappa delta r beta * v.toFun r beta) : ℝ) : ℂ) := by
  have hinner : (Estimates.torusIntegral fun r' =>
      parityKernel kappa delta v.toFun r r' beta)
      = Complex.I * (Real.sin beta : ℂ) *
        (((Real.sqrt 2)⁻¹ * (v.toFun r beta * parityJ kappa delta r beta) : ℝ) : ℂ) := by
    rw [show (fun r' : ℝ => parityKernel kappa delta v.toFun r r' beta)
        = fun r' : ℝ => (Complex.I * (Real.sin beta : ℂ)) *
          ((parityKernelReal kappa delta v.toFun r r' beta : ℝ) : ℂ) from rfl,
      Glue.torusIntegral_const_mul, torusIntegral_ofReal,
      torusIntegral_parityKernelReal hkappa hdelta v r beta]
  have key : ∀ s x : ℝ,
      -Complex.I * (s : ℂ) * (Complex.I * (s : ℂ) * (x : ℂ)) = ((s ^ 2 * x : ℝ) : ℂ) := by
    intro s x
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (-((s : ℂ) ^ 2 * (x : ℂ))) * hI
  rw [Glue.rawD2StarMixed, hinner, key]
  congr 1
  rw [paritySigma]
  ring

/-! ## (P2): the projection makes no mixed correction -/

/-- The fibre average of `K` along `r + r' = s`, i.e. the coincident-row part
`(I - Π₃) K` read as a function of the sum of the two row frequencies. -/
def parityFibreAverage (kappa delta : ℝ) (v : ℝ → ℝ → ℝ) (beta s : ℝ) : ℂ :=
  Estimates.torusIntegral fun t => parityKernel kappa delta v t (s - t) beta

theorem diagonalRawCarrier_parityKernel (v : ParityProfile) (p₂ r r' beta : ℝ) :
    Glue.diagonalRawCarrier p₂
        (Glue.rawDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' beta
      = parityFibreAverage kappa delta v.toFun beta (r + r') := by
  unfold Glue.diagonalRawCarrier Glue.rawDiagonalPart Glue.mixedAlpha parityFibreAverage
  congr 1
  funext t
  congr 1
  ring

theorem parityFibreAverage_periodic (v : ParityProfile) (beta : ℝ) :
    Function.Periodic (fun s => parityFibreAverage kappa delta v.toFun beta s)
      (2 * Real.pi) := by
  intro s
  show parityFibreAverage kappa delta v.toFun beta (s + 2 * Real.pi)
      = parityFibreAverage kappa delta v.toFun beta s
  unfold parityFibreAverage
  congr 1
  funext t
  rw [show s + 2 * Real.pi - t = (s - t) + 2 * Real.pi by ring]
  exact parityKernel_periodic_row' v t beta (s - t)

/-- The fibre average is **odd** in the sum of the row frequencies: this is the
reflection `(t, s - t) ↦ (-t, -(s-t))`, under which `M` is invariant and `v`
changes sign. -/
theorem parityFibreAverage_odd (v : ParityProfile) (beta s : ℝ) :
    parityFibreAverage kappa delta v.toFun beta (-s)
      = -parityFibreAverage kappa delta v.toFun beta s := by
  have h1 : (Estimates.torusIntegral fun t =>
        parityKernel kappa delta v.toFun t (-s - t) beta)
      = Estimates.torusIntegral fun t =>
          parityKernel kappa delta v.toFun (-t) (-s - -t) beta :=
    (torusIntegral_comp_neg
      (fun t => parityKernel kappa delta v.toFun t (-s - t) beta)).symm
  have h2 : (fun t : ℝ => parityKernel kappa delta v.toFun (-t) (-s - -t) beta)
      = fun t : ℝ => -parityKernel kappa delta v.toFun t (s - t) beta := by
    funext t
    rw [show (-s - -t : ℝ) = -(s - t) by ring]
    exact parityKernel_neg_row_pair v t (s - t) beta
  unfold parityFibreAverage
  rw [h1, h2, torusIntegral_neg']

/-- **(P2).**  `∫ ((I - Π) K)(r,r',β) dm(r') = ∬ K = 0`.  The translation
`r' ↦ r + r'` is legitimate because `K` is a genuine function on the torus in
its second row frequency, and the resulting integral vanishes by oddness. -/
theorem torusIntegral_diagonalRawCarrier_eq_zero (v : ParityProfile)
    (p₂ r beta : ℝ) :
    (Estimates.torusIntegral fun r' =>
        Glue.diagonalRawCarrier p₂
          (Glue.rawDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' beta) = 0 := by
  have hrw : (fun r' : ℝ => Glue.diagonalRawCarrier p₂
        (Glue.rawDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' beta)
      = fun r' : ℝ => parityFibreAverage kappa delta v.toFun beta (r' + r) := by
    funext r'
    rw [diagonalRawCarrier_parityKernel v p₂ r r' beta, add_comm]
  rw [hrw, Glue.torusIntegral_comp_add_right (parityFibreAverage_periodic v beta) r]
  exact torusIntegral_of_odd fun s => parityFibreAverage_odd v beta s

/-- **(P2), the lowering consequence.**  `(D₂* k)₁₂ = (D₂* K)₁₂ = (√2)⁻¹ σ v`:
the projection contributes nothing to the mixed component.  In the old proof
this was Lemma 5.3, an estimate; here it is an identity. -/
theorem rawD2StarMixed_offDiagonalPart (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (p₂ r beta : ℝ) :
    Glue.rawD2StarMixed
        (Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r beta
      = (((Real.sqrt 2)⁻¹ * (paritySigma kappa delta r beta * v.toFun r beta) : ℝ) : ℂ) := by
  have hK := torusBounded₃_parityKernel hkappa hdelta v
  have hcar := (hK.rawDiagonalPart p₂).diagonalRawCarrier p₂
  obtain ⟨C1, hC1⟩ := hK.2
  obtain ⟨C2, hC2⟩ := hcar.2
  have hint1 : Integrable (fun r' => parityKernel kappa delta v.toFun r r' beta)
      (volume.restrict Estimates.torus) :=
    Glue.integrable_torus_of_bound (hK.measurable_row r beta).aestronglyMeasurable
      (fun r' => hC1 r r' beta)
  have hint2 : Integrable (fun r' => Glue.diagonalRawCarrier p₂
      (Glue.rawDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' beta)
      (volume.restrict Estimates.torus) :=
    Glue.integrable_torus_of_bound (hcar.measurable_row r beta).aestronglyMeasurable
      (fun r' => hC2 r r' beta)
  have hsplit : (Estimates.torusIntegral fun r' =>
      Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun) r r' beta)
      = Estimates.torusIntegral fun r' => parityKernel kappa delta v.toFun r r' beta := by
    show (Estimates.torusIntegral fun r' =>
        parityKernel kappa delta v.toFun r r' beta -
          Glue.diagonalRawCarrier p₂
            (Glue.rawDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' beta)
      = _
    rw [Glue.torusIntegral_sub hint1 hint2,
      torusIntegral_diagonalRawCarrier_eq_zero v p₂ r beta, sub_zero]
  rw [Glue.rawD2StarMixed, hsplit, ← Glue.rawD2StarMixed]
  exact rawD2StarMixed_parityKernel hkappa hdelta v r beta

/-! ## (P3): the two-row component vanishes -/

/-- `Π K` is odd in the column frequency, because `K` is. -/
theorem rawOffDiagonalPart_neg_col (v : ParityProfile) (p₂ r r' beta : ℝ) :
    Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun) r r' (-beta)
      = -Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun) r r' beta := by
  have hcongr : (fun t : ℝ => parityKernel kappa delta v.toFun t
        (Glue.mixedAlpha p₂ r r' - t + p₂) (-beta))
      = fun t : ℝ => -parityKernel kappa delta v.toFun t
        (Glue.mixedAlpha p₂ r r' - t + p₂) beta := by
    funext t
    rw [parityKernel_neg_col]
  show parityKernel kappa delta v.toFun r r' (-beta) -
      Estimates.torusIntegral (fun t => parityKernel kappa delta v.toFun t
        (Glue.mixedAlpha p₂ r r' - t + p₂) (-beta)) = _
  rw [parityKernel_neg_col, hcongr, torusIntegral_neg']
  show _ = -(parityKernel kappa delta v.toFun r r' beta -
      Estimates.torusIntegral (fun t => parityKernel kappa delta v.toFun t
        (Glue.mixedAlpha p₂ r r' - t + p₂) beta))
  ring

/-- **(P3).**  `(D₂* k)₁₁ = 0`: the two-row component of the lowering of the
projected kernel vanishes identically, because `K` is odd in `β`. -/
theorem rawD2StarTwoRow_offDiagonalPart (v : ParityProfile) (p₂ r r' : ℝ) :
    Glue.rawD2StarTwoRow p₂
      (Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun)) r r' = 0 := by
  rw [Glue.rawD2StarTwoRow,
    torusIntegral_of_odd (g := fun beta =>
      Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun) r r' beta)
      (fun beta => rawOffDiagonalPart_neg_col v p₂ r r' beta), mul_zero]

/-! ## (P4): the energy cross term vanishes -/

theorem inv_evenMajorant_le (hkappa : 0 < kappa) (hdelta : 0 < delta) (r r' beta : ℝ) :
    (evenMajorant kappa delta r r' beta)⁻¹ ≤ (kappa * delta)⁻¹ :=
  inv_anti₀ (by positivity) (mul_le_evenMajorant hkappa.le delta r r' beta)

theorem inv_evenMajorant_nonneg (hkappa : 0 < kappa) (hdelta : 0 < delta) (r r' beta : ℝ) :
    0 ≤ (evenMajorant kappa delta r r' beta)⁻¹ :=
  inv_nonneg.mpr (evenMajorant_pos hkappa hdelta r r' beta).le

theorem measurable_inv_evenMajorant_row' (kappa delta r beta : ℝ) :
    Measurable fun r' => (evenMajorant kappa delta r r' beta)⁻¹ :=
  Measurable.inv ((evenMajorant_measurable kappa delta).comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

theorem measurable_inv_evenMajorant_row (kappa delta r' beta : ℝ) :
    Measurable fun r => (evenMajorant kappa delta r r' beta)⁻¹ :=
  Measurable.inv ((evenMajorant_measurable kappa delta).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const)))

/-- A uniform bound for every term of the energy integrand. -/
theorem abs_energy_term_le (hkappa : 0 < kappa) (hdelta : 0 < delta)
    {a b w B : ℝ} (hw : |w| ≤ 1) (hB : 0 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B)
    (r r' beta : ℝ) :
    |w * (a * (b * (evenMajorant kappa delta r r' beta)⁻¹))|
      ≤ B ^ 2 * (kappa * delta)⁻¹ := by
  have hMnn := inv_evenMajorant_nonneg hkappa hdelta r r' beta
  have hMle := inv_evenMajorant_le hkappa hdelta r r' beta
  have hkd : (0:ℝ) < (kappa * delta)⁻¹ := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hMnn]
  calc |w| * (|a| * (|b| * (evenMajorant kappa delta r r' beta)⁻¹))
      ≤ 1 * (B * (B * (kappa * delta)⁻¹)) := by gcongr
    _ = B ^ 2 * (kappa * delta)⁻¹ := by ring

/-- **(P1) in the form used by the energy computation.** -/
theorem parityJ_row_mul_inv_eq_zero (v : ParityProfile) (r beta : ℝ) :
    (Estimates.torusIntegral fun r' =>
      v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹) = 0 := by
  refine torusIntegral_of_odd fun r' => ?_
  rw [evenMajorant_neg_row', v.odd_row, neg_mul]

theorem norm_parityKernel_sq (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) :
    ‖parityKernel kappa delta v r r' beta‖ ^ 2
      = Real.sin beta ^ 2 * parityKernelReal kappa delta v r r' beta ^ 2 := by
  rw [parityKernel, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]

/-- The pointwise expansion of the energy integrand into the two diagonal
terms and the cross term. -/
theorem evenMajorant_mul_norm_parityKernel_sq (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) :
    evenMajorant kappa delta r r' beta * ‖parityKernel kappa delta v r r' beta‖ ^ 2
      = (2⁻¹ * (Real.sin beta ^ 2 *
            (v r beta * (v r beta * (evenMajorant kappa delta r r' beta)⁻¹)))
          + Real.sin beta ^ 2 *
            (v r beta * (v r' beta * (evenMajorant kappa delta r r' beta)⁻¹)))
        + 2⁻¹ * (Real.sin beta ^ 2 *
            (v r' beta * (v r' beta * (evenMajorant kappa delta r r' beta)⁻¹))) := by
  have hMpos : (0:ℝ) < evenMajorant kappa delta r r' beta :=
    evenMajorant_pos hkappa hdelta r r' beta
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [norm_parityKernel_sq, parityKernelReal]
  field_simp
  rw [hsq]
  ring

set_option maxHeartbeats 1000000 in
/-- The inner `r'`-integral of the energy: the cross term is killed by (P1). -/
theorem torusIntegral_energy_inner (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (r beta : ℝ) :
    (Estimates.torusIntegral fun r' =>
        evenMajorant kappa delta r r' beta *
          ‖parityKernel kappa delta v.toFun r r' beta‖ ^ 2)
      = 2⁻¹ * (Real.sin beta ^ 2 *
            (v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta)))
        + 2⁻¹ * (Real.sin beta ^ 2 *
            Estimates.torusIntegral fun r' =>
              v.toFun r' beta * (v.toFun r' beta *
                (evenMajorant kappa delta r r' beta)⁻¹)) := by
  have hsin : |Real.sin beta ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_sin beta, Real.sin_le_one beta]
  have hvb := v.bound_nonneg
  set Cb : ℝ := v.bound ^ 2 * (kappa * delta)⁻¹ with hCb
  have hmA : Measurable fun r' : ℝ => 2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹))) :=
    measurable_const.mul (measurable_const.mul (measurable_const.mul
      (measurable_const.mul (measurable_inv_evenMajorant_row' kappa delta r beta))))
  have hmB : Measurable fun r' : ℝ => Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹)) :=
    measurable_const.mul (measurable_const.mul
      ((v.measurable_row beta).mul (measurable_inv_evenMajorant_row' kappa delta r beta)))
  have hmC : Measurable fun r' : ℝ => 2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r' beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹))) :=
    measurable_const.mul (measurable_const.mul ((v.measurable_row beta).mul
      ((v.measurable_row beta).mul (measurable_inv_evenMajorant_row' kappa delta r beta))))
  have hbA : ∀ r' : ℝ, |2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹)))|
      ≤ Cb := by
    intro r'
    have h := abs_energy_term_le hkappa hdelta (B := v.bound) hsin hvb
      (v.abs_le r beta) (v.abs_le r beta) r r' beta
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    have hCbnn : 0 ≤ Cb := by rw [hCb]; positivity
    nlinarith [abs_nonneg (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹)))]
  have hbB : ∀ r' : ℝ, |Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹))|
      ≤ Cb := fun r' => abs_energy_term_le hkappa hdelta (B := v.bound) hsin hvb
        (v.abs_le r beta) (v.abs_le r' beta) r r' beta
  have hbC : ∀ r' : ℝ, |2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r' beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹)))|
      ≤ Cb := by
    intro r'
    have h := abs_energy_term_le hkappa hdelta (B := v.bound) hsin hvb
      (v.abs_le r' beta) (v.abs_le r' beta) r r' beta
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    have hCbnn : 0 ≤ Cb := by rw [hCb]; positivity
    nlinarith [abs_nonneg (Real.sin beta ^ 2 *
      (v.toFun r' beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹)))]
  have hbAB : ∀ r' : ℝ, |(2⁻¹ * (Real.sin beta ^ 2 *
        (v.toFun r beta * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹)))
      + Real.sin beta ^ 2 *
        (v.toFun r beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹)))|
      ≤ Cb + Cb := fun r' => (abs_add_le _ _).trans (by linarith [hbA r', hbB r'])
  have hA : (Estimates.torusIntegral fun r' => 2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * (evenMajorant kappa delta r r' beta)⁻¹))))
      = 2⁻¹ * (Real.sin beta ^ 2 *
        (v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta))) := by
    rw [torusIntegral_real_smul, torusIntegral_real_smul, torusIntegral_real_smul,
      torusIntegral_real_smul]
    rfl
  have hB : (Estimates.torusIntegral fun r' => Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹))) = 0 := by
    rw [torusIntegral_real_smul, torusIntegral_real_smul,
      parityJ_row_mul_inv_eq_zero v r beta, mul_zero, mul_zero]
  have hC : (Estimates.torusIntegral fun r' => 2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r' beta * (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹))))
      = 2⁻¹ * (Real.sin beta ^ 2 * Estimates.torusIntegral fun r' =>
          v.toFun r' beta * (v.toFun r' beta *
            (evenMajorant kappa delta r r' beta)⁻¹)) := by
    rw [torusIntegral_real_smul, torusIntegral_real_smul]
  rw [funext (evenMajorant_mul_norm_parityKernel_sq hkappa hdelta v.toFun r · beta),
    torusIntegral_add_of_bounded (hmA.add hmB) hmC hbAB hbC,
    torusIntegral_add_of_bounded hmA hmB hbA hbB, hA, hB, hC, add_zero]

set_option maxHeartbeats 1000000 in
/-- The second diagonal term symmetrizes into the first: this is the swap
`r ↔ r'`, legitimate because `M` is symmetric in the two row frequencies. -/
theorem torusIntegral_energy_swap (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (beta : ℝ) :
    (Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
        v.toFun r' beta * (v.toFun r' beta *
          (evenMajorant kappa delta r r' beta)⁻¹))
      = Estimates.torusIntegral fun r =>
          v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta) := by
  have hvb := v.bound_nonneg
  have hmeas : Measurable fun z : ℝ × ℝ =>
      v.toFun z.2 beta * (v.toFun z.2 beta *
        (evenMajorant kappa delta z.1 z.2 beta)⁻¹) := by
    have h1 : Measurable fun z : ℝ × ℝ => v.toFun z.2 beta :=
      v.meas.comp (measurable_snd.prodMk measurable_const)
    have h2 : Measurable fun z : ℝ × ℝ => (evenMajorant kappa delta z.1 z.2 beta)⁻¹ :=
      Measurable.inv ((evenMajorant_measurable kappa delta).comp
        (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
    exact h1.mul (h1.mul h2)
  have hbd : ∀ x y : ℝ, |v.toFun y beta * (v.toFun y beta *
      (evenMajorant kappa delta x y beta)⁻¹)| ≤ v.bound ^ 2 * (kappa * delta)⁻¹ := by
    intro x y
    have h := abs_energy_term_le hkappa hdelta (B := v.bound) (w := 1)
      (by norm_num) hvb (v.abs_le y beta) (v.abs_le y beta) x y beta
    simpa using h
  rw [torusIntegral_swap_of_bounded hmeas hbd]
  congr 1
  funext r'
  have hswap : (fun r : ℝ => v.toFun r' beta * (v.toFun r' beta *
      (evenMajorant kappa delta r r' beta)⁻¹))
      = fun r : ℝ => v.toFun r' beta * (v.toFun r' beta *
        (evenMajorant kappa delta r' r beta)⁻¹) := by
    funext r
    rw [evenMajorant_swap]
  rw [hswap, torusIntegral_real_smul, torusIntegral_real_smul]
  rfl

set_option maxHeartbeats 2000000 in
/-- **(P4).**  `∫ M |K|² = ∫ σ |v|²`: the cross term vanishes by (P1) and the
two diagonal terms are equal by the `r ↔ r'` symmetry of `M`.  This is an
identity, with the note's normalization `K = (i sin β/(√2 M))(v + v')` and the
**ordered** raw integrals of `Manhattan.Glue.rawMultiplierEnergy`. -/
theorem evenMajorantEnergy_parityKernel (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) :
    evenMajorantEnergy kappa delta (parityKernel kappa delta v.toFun)
      = Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
          paritySigma kappa delta r beta * v.toFun r beta ^ 2 := by
  unfold evenMajorantEnergy
  congr 1
  funext beta
  have hvb := v.bound_nonneg
  have hsin : |Real.sin beta ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_sin beta, Real.sin_le_one beta]
  set Cb : ℝ := v.bound ^ 2 * (kappa * delta)⁻¹ with hCb
  have hCbnn : 0 ≤ Cb := by rw [hCb]; positivity
  have hm1 : Measurable fun r : ℝ => 2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta))) := by
    have hJ : Measurable fun r : ℝ => parityJ kappa delta r beta :=
      parityJ_measurable.comp (measurable_id.prodMk measurable_const)
    exact measurable_const.mul (measurable_const.mul ((v.measurable_row beta).mul
      ((v.measurable_row beta).mul hJ)))
  have hm2 : Measurable fun r : ℝ => 2⁻¹ * (Real.sin beta ^ 2 *
      Estimates.torusIntegral fun r' => v.toFun r' beta * (v.toFun r' beta *
        (evenMajorant kappa delta r r' beta)⁻¹)) := by
    have hjoint : StronglyMeasurable fun z : ℝ × ℝ =>
        v.toFun z.2 beta * (v.toFun z.2 beta *
          (evenMajorant kappa delta z.1 z.2 beta)⁻¹) := by
      have h1 : Measurable fun z : ℝ × ℝ => v.toFun z.2 beta :=
        v.meas.comp (measurable_snd.prodMk measurable_const)
      have h2 : Measurable fun z : ℝ × ℝ => (evenMajorant kappa delta z.1 z.2 beta)⁻¹ :=
        Measurable.inv ((evenMajorant_measurable kappa delta).comp
          (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
      exact (h1.mul (h1.mul h2)).stronglyMeasurable
    exact measurable_const.mul (measurable_const.mul
      (Glue.stronglyMeasurable_torusIntegral hjoint).measurable)
  have hb1 : ∀ r : ℝ, |2⁻¹ * (Real.sin beta ^ 2 *
      (v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta)))| ≤ Cb := by
    intro r
    have hJnn := parityJ_nonneg hkappa hdelta r beta
    have hJle := parityJ_le hkappa hdelta r beta
    have hv := v.abs_le r beta
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹), abs_of_nonneg hJnn]
    have hstep : |Real.sin beta ^ 2| * (|v.toFun r beta| *
        (|v.toFun r beta| * parityJ kappa delta r beta))
        ≤ 1 * (v.bound * (v.bound * (kappa * delta)⁻¹)) := by gcongr
    have : (2:ℝ)⁻¹ ≤ 1 := by norm_num
    nlinarith [abs_nonneg (Real.sin beta ^ 2), abs_nonneg (v.toFun r beta)]
  have hb2 : ∀ r : ℝ, |2⁻¹ * (Real.sin beta ^ 2 *
      Estimates.torusIntegral fun r' => v.toFun r' beta * (v.toFun r' beta *
        (evenMajorant kappa delta r r' beta)⁻¹))| ≤ Cb := by
    intro r
    have hinner : |Estimates.torusIntegral fun r' => v.toFun r' beta *
        (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹)| ≤ Cb := by
      refine Glue.abs_torusIntegral_le fun r' => ?_
      have h := abs_energy_term_le hkappa hdelta (B := v.bound) (w := 1)
        (by norm_num) hvb (v.abs_le r' beta) (v.abs_le r' beta) r r' beta
      rw [one_mul] at h
      rw [hCb]
      exact h
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    nlinarith [abs_nonneg (Real.sin beta ^ 2), abs_nonneg
      (Estimates.torusIntegral fun r' => v.toFun r' beta *
        (v.toFun r' beta * (evenMajorant kappa delta r r' beta)⁻¹))]
  rw [funext (torusIntegral_energy_inner hkappa hdelta v · beta),
    torusIntegral_add_of_bounded hm1 hm2 hb1 hb2, torusIntegral_real_smul,
    torusIntegral_real_smul, torusIntegral_real_smul, torusIntegral_real_smul,
    torusIntegral_energy_swap hkappa hdelta v beta]
  have hfinal : (Estimates.torusIntegral fun r =>
      paritySigma kappa delta r beta * v.toFun r beta ^ 2)
      = Real.sin beta ^ 2 * Estimates.torusIntegral fun r =>
          v.toFun r beta * (v.toFun r beta * parityJ kappa delta r beta) := by
    rw [← torusIntegral_real_smul]
    congr 1
    funext r
    rw [paritySigma]
    ring
  rw [hfinal]
  ring

/-! ## `L²` legitimacy

The Version 4 argument does not check that its
competitor lies in `L²`.  For a fixed `λ > 0` the two bounds below close that
gap: `‖v‖₂ ≤ λ⁻¹ ‖w‖₂` because `B + σ ≥ λ`, and `‖K‖₂ ≤ (√2/(κδ)) ‖v‖₂`
because `M ≥ κδ`.  Together with `torusBounded₃_rawOffDiagonalPart` this says
that `k = Π K` is a genuine bounded measurable type-`112` coefficient, hence a
degree-three element of the Walsh space. -/

/-- Monotonicity of the doubly iterated normalized torus integral. -/
theorem torusIntegral₂_mono {F G : ℝ → ℝ → ℝ}
    (hF : Measurable fun z : ℝ × ℝ => F z.1 z.2)
    (hG : Measurable fun z : ℝ × ℝ => G z.1 z.2)
    {C : ℝ} (hFb : ∀ x y, |F x y| ≤ C) (hGb : ∀ x y, |G x y| ≤ C)
    (hle : ∀ x y, F x y ≤ G x y) :
    (Estimates.torusIntegral fun x => Estimates.torusIntegral fun y => F x y)
      ≤ Estimates.torusIntegral fun x => Estimates.torusIntegral fun y => G x y := by
  have houter : ∀ (H : ℝ → ℝ → ℝ), (Measurable fun z : ℝ × ℝ => H z.1 z.2) →
      (∀ x y, |H x y| ≤ C) →
      Integrable (fun x : ℝ => Estimates.torusIntegral fun y => H x y)
        (volume.restrict Estimates.torus) := by
    intro H hH hHb
    refine Glue.integrable_torus_of_bound (C := C) ?_ ?_
    · exact (Glue.stronglyMeasurable_torusIntegral hH.stronglyMeasurable).aestronglyMeasurable
    · intro x
      rw [Real.norm_eq_abs]
      exact Glue.abs_torusIntegral_le fun y => hHb x y
  refine Glue.torusIntegral_mono (houter F hF hFb) (houter G hG hGb) fun x => ?_
  refine Glue.torusIntegral_mono ?_ ?_ fun y => hle x y
  · exact integrable_torus_of_abs_le
      (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hFb x y)
  · exact integrable_torus_of_abs_le
      (hG.comp (measurable_const.prodMk measurable_id)) (fun y => hGb x y)

/-- The squared normalized `L²` norm of a function of `(r, β)`. -/
def torusL2SqTwo (f : ℝ → ℝ → ℝ) : ℝ :=
  Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r => f r beta ^ 2

/-- The squared normalized `L²` norm of a raw type-`112` kernel. -/
def torusL2SqThree (k : ℝ → ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
    Estimates.torusIntegral fun r' => ‖k r r' beta‖ ^ 2

/-- `‖K‖₂² ≤ (√2/(κδ))² ‖v‖₂²`: the kernel is in `L²` as soon as `v` is. -/
theorem torusL2SqThree_parityKernel_le (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) :
    torusL2SqThree (parityKernel kappa delta v.toFun)
      ≤ 2 * ((kappa * delta)⁻¹) ^ 2 * torusL2SqTwo v.toFun := by
  have hvb := v.bound_nonneg
  have hkd : (0:ℝ) < kappa * delta := mul_pos hkappa hdelta
  set C : ℝ := (parityKernelBound kappa delta v) ^ 2
      + 2 * v.bound ^ 2 * ((kappa * delta)⁻¹) ^ 2 with hC
  have hCsplit1 : (parityKernelBound kappa delta v) ^ 2 ≤ C := by
    rw [hC]; nlinarith [sq_nonneg (parityKernelBound kappa delta v)]
  have hCsplit2 : 2 * v.bound ^ 2 * ((kappa * delta)⁻¹) ^ 2 ≤ C := by
    rw [hC]; nlinarith [sq_nonneg (parityKernelBound kappa delta v)]
  -- the pointwise comparison
  have hpt : ∀ beta r r' : ℝ,
      ‖parityKernel kappa delta v.toFun r r' beta‖ ^ 2
        ≤ ((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2) := by
    intro beta r r'
    have hMpos : (0:ℝ) < evenMajorant kappa delta r r' beta :=
      evenMajorant_pos hkappa hdelta r r' beta
    have hMlow : kappa * delta ≤ evenMajorant kappa delta r r' beta :=
      mul_le_evenMajorant hkappa.le delta r r' beta
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsin : Real.sin beta ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin beta, Real.sin_le_one beta]
    have hsinnn : 0 ≤ Real.sin beta ^ 2 := sq_nonneg _
    have hinv : (evenMajorant kappa delta r r' beta)⁻¹ ≤ (kappa * delta)⁻¹ :=
      inv_anti₀ hkd hMlow
    have hinvnn : 0 ≤ (evenMajorant kappa delta r r' beta)⁻¹ := (inv_pos.mpr hMpos).le
    have hkey : parityKernelReal kappa delta v.toFun r r' beta ^ 2
        ≤ ((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2) := by
      rw [parityKernelReal, div_pow, mul_pow, hsq]
      have hnum : (v.toFun r beta + v.toFun r' beta) ^ 2
          ≤ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2) := by
        nlinarith [sq_nonneg (v.toFun r beta - v.toFun r' beta)]
      have hden : ((kappa * delta) : ℝ) ^ 2 ≤ evenMajorant kappa delta r r' beta ^ 2 := by
        nlinarith
      have hMsq : (0:ℝ) < evenMajorant kappa delta r r' beta ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      have hstep : (v.toFun r beta + v.toFun r' beta) ^ 2
          ≤ ((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2) *
            (2 * evenMajorant kappa delta r r' beta ^ 2) := by
        have hfac : (2:ℝ) * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2)
            ≤ ((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2) *
              (2 * evenMajorant kappa delta r r' beta ^ 2) := by
          have hone : (1:ℝ) ≤ ((kappa * delta)⁻¹) ^ 2 * evenMajorant kappa delta r r' beta ^ 2 := by
            have hstep : (1:ℝ) ≤ (kappa * delta)⁻¹ * evenMajorant kappa delta r r' beta := by
              rw [← div_eq_inv_mul, le_div_iff₀ hkd, one_mul]
              exact hMlow
            nlinarith [hstep]
          nlinarith [sq_nonneg (v.toFun r beta), sq_nonneg (v.toFun r' beta)]
        linarith
      linarith
    rw [norm_parityKernel_sq]
    nlinarith [sq_nonneg (parityKernelReal kappa delta v.toFun r r' beta)]
  -- the majorant integrates to the right thing
  have hmeasF : Measurable fun z : ℝ × ℝ × ℝ =>
      ‖parityKernel kappa delta v.toFun z.2.1 z.2.2 z.1‖ ^ 2 := by
    exact ((parityKernel_measurable (kappa := kappa) (delta := delta) v).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))).norm.pow_const 2
  have hmeasG : Measurable fun z : ℝ × ℝ × ℝ =>
      ((kappa * delta)⁻¹) ^ 2 * (v.toFun z.2.1 z.1 ^ 2 + v.toFun z.2.2 z.1 ^ 2) := by
    have h1 : Measurable fun z : ℝ × ℝ × ℝ => v.toFun z.2.1 z.1 :=
      v.meas.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have h2 : Measurable fun z : ℝ × ℝ × ℝ => v.toFun z.2.2 z.1 :=
      v.meas.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact measurable_const.mul ((h1.pow_const 2).add (h2.pow_const 2))
  have hbF : ∀ beta r r' : ℝ,
      |‖parityKernel kappa delta v.toFun r r' beta‖ ^ 2| ≤ C := by
    intro beta r r'
    rw [abs_of_nonneg (sq_nonneg _)]
    refine le_trans ?_ hCsplit1
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_parityKernel_le hkappa hdelta v r r' beta) 2
  have hbG : ∀ beta r r' : ℝ,
      |((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2)| ≤ C := by
    intro beta r r'
    have h1 : v.toFun r beta ^ 2 ≤ v.bound ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (v.abs_le r beta) 2
    have h2 : v.toFun r' beta ^ 2 ≤ v.bound ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (v.abs_le r' beta) 2
    rw [abs_of_nonneg (by positivity)]
    refine le_trans ?_ hCsplit2
    have hinvnn : (0:ℝ) ≤ ((kappa * delta)⁻¹) ^ 2 := by positivity
    nlinarith
  have hmono := torusIntegral₃_mono (C := C) hmeasF hmeasG hbF hbG hpt
  refine le_trans hmono (le_of_eq ?_)
  -- evaluate the majorant
  have hinner : ∀ beta r : ℝ,
      (Estimates.torusIntegral fun r' => ((kappa * delta)⁻¹) ^ 2 *
        (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2))
      = ((kappa * delta)⁻¹) ^ 2 * (v.toFun r beta ^ 2 +
          Estimates.torusIntegral fun r' => v.toFun r' beta ^ 2) := by
    intro beta r
    rw [torusIntegral_real_smul]
    congr 1
    have hmeas1 : Measurable fun _ : ℝ => v.toFun r beta ^ 2 := measurable_const
    have hmeas2 : Measurable fun r' : ℝ => v.toFun r' beta ^ 2 :=
      (v.measurable_row beta).pow_const 2
    have hb1 : ∀ _ : ℝ, |v.toFun r beta ^ 2| ≤ v.bound ^ 2 := by
      intro _
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (v.abs_le r beta) 2
    have hb2 : ∀ r' : ℝ, |v.toFun r' beta ^ 2| ≤ v.bound ^ 2 := by
      intro r'
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (v.abs_le r' beta) 2
    rw [torusIntegral_add_of_bounded hmeas1 hmeas2 hb1 hb2, Glue.torusIntegral_const]
  have hmiddle : ∀ beta : ℝ,
      (Estimates.torusIntegral fun r => ((kappa * delta)⁻¹) ^ 2 *
        (v.toFun r beta ^ 2 + Estimates.torusIntegral fun r' => v.toFun r' beta ^ 2))
      = ((kappa * delta)⁻¹) ^ 2 *
          (2 * Estimates.torusIntegral fun r => v.toFun r beta ^ 2) := by
    intro beta
    rw [torusIntegral_real_smul]
    congr 1
    have hmeas1 : Measurable fun r : ℝ => v.toFun r beta ^ 2 :=
      (v.measurable_row beta).pow_const 2
    have hb1 : ∀ r : ℝ, |v.toFun r beta ^ 2| ≤ v.bound ^ 2 := by
      intro r
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (v.abs_le r beta) 2
    have hb2 : ∀ _ : ℝ, |Estimates.torusIntegral fun r' => v.toFun r' beta ^ 2|
        ≤ v.bound ^ 2 := fun _ => Glue.abs_torusIntegral_le hb1
    rw [torusIntegral_add_of_bounded hmeas1 measurable_const hb1 hb2,
      Glue.torusIntegral_const]
    ring
  calc (Estimates.torusIntegral fun beta => Estimates.torusIntegral fun r =>
        Estimates.torusIntegral fun r' => ((kappa * delta)⁻¹) ^ 2 *
          (v.toFun r beta ^ 2 + v.toFun r' beta ^ 2))
      = Estimates.torusIntegral fun beta => ((kappa * delta)⁻¹) ^ 2 *
          (2 * Estimates.torusIntegral fun r => v.toFun r beta ^ 2) := by
        congr 1
        funext beta
        rw [funext (hinner beta), hmiddle beta]
    _ = 2 * ((kappa * delta)⁻¹) ^ 2 * torusL2SqTwo v.toFun := by
        rw [torusIntegral_real_smul, torusIntegral_real_smul]
        unfold torusL2SqTwo
        ring

theorem torusBounded₃_rawOffDiagonalPart {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hk : Glue.TorusBoundedThree k) :
    Glue.TorusBoundedThree (Glue.rawOffDiagonalPart p₂ k) :=
  hk.sub ((hk.rawDiagonalPart p₂).diagonalRawCarrier p₂)

/-! ## The competitor profile `v = w/(B + σ)` -/

/-- The Version 4 scalar minimizer `v = w/(B+σ)`. -/
def parityV (q : Estimates.Parameters) (kappa delta : ℝ) (w : ℝ → ℝ → ℝ)
    (r beta : ℝ) : ℝ :=
  w r beta / (Estimates.correctionB q r beta + paritySigma kappa delta r beta)

theorem lambda_le_correctionB_add_paritySigma {q : Estimates.Parameters}
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (r beta : ℝ) :
    q.lambda ≤ Estimates.correctionB q r beta + paritySigma kappa delta r beta := by
  have h1 := correctionB_ge q r beta
  have h2 := paritySigma_nonneg hkappa hdelta r beta
  linarith

theorem parityJ_periodic_row (kappa delta beta : ℝ) :
    Function.Periodic (fun r => parityJ kappa delta r beta) (2 * Real.pi) := by
  intro r
  show parityJ kappa delta (r + 2 * Real.pi) beta = parityJ kappa delta r beta
  unfold parityJ
  congr 1
  funext r'
  have h : evenMajorant kappa delta (r + 2 * Real.pi) r' beta
      = evenMajorant kappa delta r r' beta :=
    evenMajorant_periodic_row kappa delta r' beta r
  rw [h]

theorem paritySigma_periodic_row (kappa delta beta : ℝ) :
    Function.Periodic (fun r => paritySigma kappa delta r beta) (2 * Real.pi) := by
  intro r
  show paritySigma kappa delta (r + 2 * Real.pi) beta = paritySigma kappa delta r beta
  have h : parityJ kappa delta (r + 2 * Real.pi) beta = parityJ kappa delta r beta :=
    parityJ_periodic_row kappa delta beta r
  rw [paritySigma, paritySigma, h]

theorem paritySigma_measurable (kappa delta : ℝ) :
    Measurable fun z : ℝ × ℝ => paritySigma kappa delta z.1 z.2 := by
  unfold paritySigma
  exact ((Real.measurable_sin.comp measurable_snd).pow_const 2).mul parityJ_measurable

/-- **The competitor profile.**  If `w` is odd in the row frequency and even in
the column frequency, then so is `v = w/(B+σ)`, because `B` and `σ` are even in
both.  This is the instance to which the four parity cancellations are
applied. -/
def parityProfileV {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ParityProfile) : ParityProfile where
  toFun := parityV q kappa delta w.toFun
  meas := by
    unfold parityV
    refine w.meas.div (Measurable.add ?_ (paritySigma_measurable kappa delta))
    unfold Estimates.correctionB Estimates.dispersion
    fun_prop
  bound := w.bound / q.lambda
  abs_le := by
    intro r beta
    have hden := lambda_le_correctionB_add_paritySigma (q := q) hkappa hdelta r beta
    have hdenpos : (0:ℝ) < Estimates.correctionB q r beta + paritySigma kappa delta r beta :=
      lt_of_lt_of_le hlam hden
    have hw := w.abs_le r beta
    have hwb := w.bound_nonneg
    rw [parityV, abs_div, abs_of_pos hdenpos]
    calc |w.toFun r beta| /
          (Estimates.correctionB q r beta + paritySigma kappa delta r beta)
        ≤ w.bound / (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
          gcongr
      _ ≤ w.bound / q.lambda := by gcongr
  odd_row := by
    intro r beta
    rw [parityV, parityV, w.odd_row, correctionB_neg_row, paritySigma_neg_row, neg_div]
  even_col := by
    intro r beta
    rw [parityV, parityV, w.even_col, correctionB_neg_col, paritySigma_neg_col]
  periodic_row := by
    intro beta r
    show parityV q kappa delta w.toFun (r + 2 * Real.pi) beta
        = parityV q kappa delta w.toFun r beta
    have hw : w.toFun (r + 2 * Real.pi) beta = w.toFun r beta := w.periodic_row beta r
    have hs : paritySigma kappa delta (r + 2 * Real.pi) beta
        = paritySigma kappa delta r beta := paritySigma_periodic_row kappa delta beta r
    have hd : Estimates.dispersion (r + 2 * Real.pi) = Estimates.dispersion r :=
      Glue.dispersion_periodic r
    rw [parityV, parityV, hw, hs, Estimates.correctionB, Estimates.correctionB, hd]

@[simp] theorem parityProfileV_toFun {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ParityProfile) :
    (parityProfileV hlam hkappa hdelta w).toFun = parityV q kappa delta w.toFun := rfl

@[simp] theorem parityProfileV_bound {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ParityProfile) :
    (parityProfileV hlam hkappa hdelta w).bound = w.bound / q.lambda := rfl

/-- **The Euler identity `w - σ v = B v`.**  This is the exact cancellation
that Step 4 of the note feeds into the scalar completion of the square
(`Manhattan.V4.scalarCompletion_le` of ). -/
theorem parityV_euler {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ℝ → ℝ → ℝ) (r beta : ℝ) :
    w r beta - paritySigma kappa delta r beta * parityV q kappa delta w r beta
      = Estimates.correctionB q r beta * parityV q kappa delta w r beta := by
  have hden := lambda_le_correctionB_add_paritySigma (q := q) hkappa hdelta r beta
  have hdenpos : (0:ℝ) < Estimates.correctionB q r beta + paritySigma kappa delta r beta :=
    lt_of_lt_of_le hlam hden
  rw [parityV]
  field_simp
  ring

/-- `‖v‖₂² ≤ (λ⁻¹)² ‖w‖₂²`, the `L²` legitimacy of the competitor profile at
fixed `λ > 0`. -/
theorem torusL2SqTwo_parityV_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (w : ParityProfile) :
    torusL2SqTwo (parityV q kappa delta w.toFun)
      ≤ (q.lambda⁻¹) ^ 2 * torusL2SqTwo w.toFun := by
  have hvabs : ∀ r beta : ℝ, |parityV q kappa delta w.toFun r beta| ≤ w.bound / q.lambda :=
    (parityProfileV hlam hkappa hdelta w).abs_le
  have hvmeas : Measurable fun z : ℝ × ℝ => parityV q kappa delta w.toFun z.1 z.2 :=
    (parityProfileV hlam hkappa hdelta w).meas
  have hwb := w.bound_nonneg
  have hpt : ∀ beta r : ℝ, parityV q kappa delta w.toFun r beta ^ 2
      ≤ (q.lambda⁻¹) ^ 2 * w.toFun r beta ^ 2 := by
    intro beta r
    have hden := lambda_le_correctionB_add_paritySigma (q := q) hkappa hdelta r beta
    have hdenpos : (0:ℝ) < Estimates.correctionB q r beta + paritySigma kappa delta r beta :=
      lt_of_lt_of_le hlam hden
    rw [parityV, div_pow, div_le_iff₀ (by positivity)]
    have hone : (1:ℝ) ≤ (q.lambda⁻¹) ^ 2 *
        (Estimates.correctionB q r beta + paritySigma kappa delta r beta) ^ 2 := by
      have hstep : (1:ℝ) ≤ q.lambda⁻¹ *
          (Estimates.correctionB q r beta + paritySigma kappa delta r beta) := by
        rw [← div_eq_inv_mul, le_div_iff₀ hlam, one_mul]
        exact hden
      nlinarith
    nlinarith [sq_nonneg (w.toFun r beta)]
  have hbnd : ∀ beta r : ℝ, |parityV q kappa delta w.toFun r beta ^ 2|
      ≤ (w.bound / q.lambda) ^ 2 + (q.lambda⁻¹) ^ 2 * w.bound ^ 2 := by
    intro beta r
    have h := hvabs r beta
    have : parityV q kappa delta w.toFun r beta ^ 2 ≤ (w.bound / q.lambda) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (w.bound / q.lambda), mul_nonneg
      (sq_nonneg (q.lambda⁻¹)) (sq_nonneg w.bound)]
  have hbnd2 : ∀ beta r : ℝ, |(q.lambda⁻¹) ^ 2 * w.toFun r beta ^ 2|
      ≤ (w.bound / q.lambda) ^ 2 + (q.lambda⁻¹) ^ 2 * w.bound ^ 2 := by
    intro beta r
    have h : w.toFun r beta ^ 2 ≤ w.bound ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (w.abs_le r beta) 2
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (w.bound / q.lambda), sq_nonneg (q.lambda⁻¹)]
  have hmF : Measurable fun z : ℝ × ℝ => parityV q kappa delta w.toFun z.2 z.1 :=
    hvmeas.comp (measurable_snd.prodMk measurable_fst)
  have hmG : Measurable fun z : ℝ × ℝ => w.toFun z.2 z.1 :=
    w.meas.comp (measurable_snd.prodMk measurable_fst)
  have hmono := torusIntegral₂_mono
    (F := fun beta r => parityV q kappa delta w.toFun r beta ^ 2)
    (G := fun beta r => (q.lambda⁻¹) ^ 2 * w.toFun r beta ^ 2)
    (hmF.pow_const 2) (measurable_const.mul (hmG.pow_const 2)) hbnd hbnd2 hpt
  refine le_trans hmono (le_of_eq ?_)
  unfold torusL2SqTwo
  rw [← torusIntegral_real_smul]
  congr 1
  funext beta
  exact torusIntegral_real_smul _ _


end

end Manhattan.V4
