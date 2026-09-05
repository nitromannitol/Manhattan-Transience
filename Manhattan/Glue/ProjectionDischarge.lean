import Manhattan.Glue.ProjectionError
import Manhattan.Glue.ProjectionDischargeTorus
import Manhattan.Glue.ProjectionDischargeIndex
import Mathlib.MeasureTheory.Function.Floor

/-!
# Discharge of the two projection-error interfaces

This file replaces the two open interface hypotheses of
`Manhattan.Glue.ProjectionError` by proofs.

The paper writes a raw type-`112` coefficient in the shifted frequency
variables `(r,r',beta)` of `manuscript.tex:806-819`. Removing the
coincident-row diagonal is, on that side, removing the part that depends on
the two row frequencies only through `alpha = r + r' - p_2`; that part is
recovered by averaging along the fibre, which is the frequency-space form of
the orthogonal projection `I - Pi_3`.

Two facts are then proved with no auxiliary hypothesis beyond periodicity:
`(D2b)` applied to the coincident-row part is independent of the surviving
row frequency and equals `projectionMixedError`, and `(D2a)` applied to it is
a function of `alpha` alone, whose Walsh coefficient at a genuine two-element
row index vanishes by character orthogonality. This is exactly the paper's
"`Pi_2` removes it".

Paper: `manuscript.tex:806-840` and `manuscript.tex:1274-1303`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

/-! ## Integer characters on the normalized torus -/

/-- The line character `x ↦ e^{i n x}`. -/
def intCharacter (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((n : ℝ) * x : ℝ) : ℂ))

@[simp] theorem norm_intCharacter (n : ℤ) (x : ℝ) : ‖intCharacter n x‖ = 1 := by
  rw [intCharacter, mul_comm, Complex.norm_exp_ofReal_mul_I]

@[simp] theorem intCharacter_zero (n : ℤ) : intCharacter n 0 = 1 := by
  rw [intCharacter]
  norm_num

@[simp] theorem intCharacter_index_zero (x : ℝ) : intCharacter 0 x = 1 := by
  rw [intCharacter]
  norm_num

theorem intCharacter_add_arg (n : ℤ) (x y : ℝ) :
    intCharacter n (x + y) = intCharacter n x * intCharacter n y := by
  rw [intCharacter, intCharacter, intCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem intCharacter_add_index (m n : ℤ) (x : ℝ) :
    intCharacter m x * intCharacter n x = intCharacter (m + n) x := by
  rw [intCharacter, intCharacter, intCharacter, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem intCharacter_neg_arg (n : ℤ) (x : ℝ) :
    intCharacter n (-x) = intCharacter (-n) x := by
  rw [intCharacter, intCharacter]
  congr 1
  push_cast
  ring

theorem intCharacter_periodic (n : ℤ) :
    Function.Periodic (intCharacter n) (2 * Real.pi) := by
  intro x
  have h : intCharacter n (2 * Real.pi) = 1 := by
    rw [intCharacter,
      show Complex.I * (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  rw [intCharacter_add_arg, h, mul_one]

@[simp] theorem torusIntegral_intCharacter' (n : ℤ) :
    Estimates.torusIntegral (intCharacter n) = if n = 0 then 1 else 0 :=
  torusIntegral_intCharacter n

/-! ## Bounded measurable coefficients -/

/-- Joint measurability together with a uniform bound, for a two-variable
frequency carrier. -/
def TorusBoundedTwo (f : ℝ → ℝ → ℂ) : Prop :=
  (Measurable fun z : ℝ × ℝ => f z.1 z.2) ∧ ∃ C : ℝ, ∀ x y, ‖f x y‖ ≤ C

/-- Joint measurability together with a uniform bound, for a raw type-`112`
frequency coefficient. -/
def TorusBoundedThree (k : ℝ → ℝ → ℝ → ℂ) : Prop :=
  (Measurable fun z : ℝ × ℝ × ℝ => k z.1 z.2.1 z.2.2) ∧
    ∃ C : ℝ, ∀ r r' beta, ‖k r r' beta‖ ≤ C

theorem TorusBoundedThree.measurable_col {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (r r' : ℝ) : Measurable fun beta => k r r' beta :=
  hk.1.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem TorusBoundedThree.measurable_row {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (r beta : ℝ) : Measurable fun r' => k r r' beta :=
  hk.1.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))

theorem TorusBoundedTwo.measurable_left {f : ℝ → ℝ → ℂ}
    (hf : TorusBoundedTwo f) (y : ℝ) : Measurable fun x => f x y :=
  hf.1.comp (measurable_id.prodMk measurable_const)

theorem TorusBoundedTwo.measurable_right {f : ℝ → ℝ → ℂ}
    (hf : TorusBoundedTwo f) (x : ℝ) : Measurable fun y => f x y :=
  hf.1.comp (measurable_const.prodMk measurable_id)

theorem TorusBoundedThree.sub {k k' : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (hk' : TorusBoundedThree k') :
    TorusBoundedThree fun r r' beta => k r r' beta - k' r r' beta := by
  obtain ⟨hm, C, hC⟩ := hk
  obtain ⟨hm', C', hC'⟩ := hk'
  refine ⟨hm.sub hm', ⟨C + C', fun r r' beta => ?_⟩⟩
  exact (norm_sub_le _ _).trans (add_le_add (hC r r' beta) (hC' r r' beta))

/-! ## The raw frequency model -/

/-- The paper's `alpha = r + r' - p₂` (`manuscript.tex:812`). -/
def mixedAlpha (p₂ r r' : ℝ) : ℝ := r + r' - p₂

/-- The two-row lowering component (D2a), in the Finset normalization. -/
def rawD2StarTwoRow (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) (r r' : ℝ) : ℂ :=
  -Complex.I * (Real.sin (mixedAlpha p₂ r r') : ℂ) *
    Estimates.torusIntegral fun beta => k r r' beta

/-- The mixed lowering component (D2b), in the Finset normalization. -/
def rawD2StarMixed (k : ℝ → ℝ → ℝ → ℂ) (r beta : ℝ) : ℂ :=
  -Complex.I * (Real.sin beta : ℂ) *
    Estimates.torusIntegral fun r' => k r r' beta

/-- Embedding of a coincident-row carrier `ell(alpha,beta)` into the raw
coordinates. A raw coefficient is carried by the coincident-row diagonal
exactly when it is of this form. -/
def diagonalRawCarrier (p₂ : ℝ) (ell : ℝ → ℝ → ℂ) (r r' beta : ℝ) : ℂ :=
  ell (mixedAlpha p₂ r r') beta

/-- The coincident-row part of a raw coefficient, in the variables
`(alpha, beta)`. In position space this is the restriction to the diagonal
`n₀ = n₁`; in frequency space it is the average along the fibre
`r + r' - p₂ = alpha`, i.e. the orthogonal projection `I - Pi_3`. -/
def rawDiagonalPart (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) (alpha beta : ℝ) : ℂ :=
  Estimates.torusIntegral fun t => k t (alpha - t + p₂) beta

/-- `Pi_3` in frequency coordinates. -/
def rawOffDiagonalPart (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) (r r' beta : ℝ) : ℂ :=
  k r r' beta - diagonalRawCarrier p₂ (rawDiagonalPart p₂ k) r r' beta

/-- The Walsh coefficient of a two-row frequency function at a genuine
two-element row index. Reading the coefficient at a Finset index is exactly
the action of the degree-two projection `Pi_2`. -/
def twoRowFourierCoefficient (F : ℝ → ℝ → ℂ) (T : Type11Index) : ℂ :=
  Estimates.torusIntegral fun r =>
    Estimates.torusIntegral fun r' =>
      intCharacter (-type11RawIndex T 0) r *
        intCharacter (-type11RawIndex T 1) r' * F r r'

/-- The two-row symbol produced by (D2a) from a coincident-row carrier. -/
def diagonalTwoRowSymbol (ell : ℝ → ℝ → ℂ) (alpha : ℝ) : ℂ :=
  -Complex.I * (Real.sin alpha : ℂ) *
    Estimates.torusIntegral fun beta => ell alpha beta

/-! ## The two structural computations -/

/-- Averaging along the fibre is a left inverse of the diagonal embedding:
`(I - Pi_3)` is idempotent on coincident-row carriers. -/
@[simp] theorem rawDiagonalPart_diagonalRawCarrier (p₂ : ℝ) (ell : ℝ → ℝ → ℂ) :
    rawDiagonalPart p₂ (diagonalRawCarrier p₂ ell) = ell := by
  funext alpha beta
  rw [rawDiagonalPart]
  have : (fun t : ℝ => diagonalRawCarrier p₂ ell t (alpha - t + p₂) beta) =
      fun _ : ℝ => ell alpha beta := by
    funext t
    rw [diagonalRawCarrier, mixedAlpha]
    congr 1
    ring
  rw [this, torusIntegral_const]

/-- The raw coefficient splits as its `Pi_3` part plus its coincident-row
part. -/
theorem sub_rawOffDiagonalPart (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) (r r' beta : ℝ) :
    k r r' beta - rawOffDiagonalPart p₂ k r r' beta =
      diagonalRawCarrier p₂ (rawDiagonalPart p₂ k) r r' beta := by
  rw [rawOffDiagonalPart, sub_sub_cancel]

/-- (D2a) applied to a coincident-row carrier depends on the two row
frequencies only through `alpha`. -/
theorem rawD2StarTwoRow_diagonalRawCarrier (p₂ : ℝ) (ell : ℝ → ℝ → ℂ)
    (r r' : ℝ) :
    rawD2StarTwoRow p₂ (diagonalRawCarrier p₂ ell) r r' =
      diagonalTwoRowSymbol ell (mixedAlpha p₂ r r') := rfl

/-- (D2b) applied to a coincident-row carrier is the paper's `u(r,beta)`:
independent of the surviving row frequency, and equal to the mixed error of
`Manhattan.Glue.projectionErrorComponents`. -/
theorem rawD2StarMixed_diagonalRawCarrier (p₂ : ℝ) (ell : ℝ → ℝ → ℂ)
    (hper : ∀ beta, Function.Periodic (fun alpha => ell alpha beta)
      (2 * Real.pi)) (r beta : ℝ) :
    rawD2StarMixed (diagonalRawCarrier p₂ ell) r beta =
      projectionMixedError ell beta := by
  rw [rawD2StarMixed, projectionMixedError]
  congr 1
  have hshift : (fun r' : ℝ => diagonalRawCarrier p₂ ell r r' beta) =
      fun r' : ℝ => (fun alpha => ell alpha beta) (r' + (r - p₂)) := by
    funext r'
    rw [diagonalRawCarrier, mixedAlpha]
    congr 1
    ring
  rw [hshift, torusIntegral_comp_add_right (hper beta) (r - p₂)]

/-- The basic character computation on the coincident-row fibre: a function of
`alpha = r + r' - p_2` alone has a two-dimensional Fourier coefficient
supported on the diagonal of the two row frequencies. -/
theorem torusIntegral₂_character_comp_mixedAlpha (p₂ : ℝ) (m₀ m₁ : ℤ)
    (G : ℝ → ℂ) (hG : Function.Periodic G (2 * Real.pi)) :
    (Estimates.torusIntegral fun r : ℝ =>
        Estimates.torusIntegral fun r' : ℝ =>
          intCharacter (-m₀) r * intCharacter (-m₁) r' *
            G (mixedAlpha p₂ r r')) =
      if m₀ = m₁ then
        intCharacter (-m₁) p₂ *
          Estimates.torusIntegral (fun u : ℝ => intCharacter (-m₁) u * G u)
      else 0 := by
  set c₁ : ℂ :=
    Estimates.torusIntegral (fun u : ℝ => intCharacter (-m₁) u * G u) with hc₁
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun r' : ℝ =>
        intCharacter (-m₀) r * intCharacter (-m₁) r' *
          G (mixedAlpha p₂ r r')) =
        intCharacter (-m₀) r * (intCharacter (-m₁) (-(r - p₂)) * c₁) := by
    intro r
    have hrewrite : (fun r' : ℝ =>
        intCharacter (-m₀) r * intCharacter (-m₁) r' *
          G (mixedAlpha p₂ r r')) =
        fun r' : ℝ => intCharacter (-m₀) r *
          (intCharacter (-m₁) r' * G (mixedAlpha p₂ r r')) := by
      funext r'
      ring
    rw [hrewrite, torusIntegral_const_mul]
    congr 1
    have hHper : Function.Periodic (fun u : ℝ =>
        intCharacter (-m₁) (-(r - p₂)) * (intCharacter (-m₁) u * G u))
        (2 * Real.pi) := by
      intro u
      dsimp only
      rw [intCharacter_periodic (-m₁) u, hG u]
    have hshift : (fun r' : ℝ =>
        intCharacter (-m₁) r' * G (mixedAlpha p₂ r r')) =
        fun r' : ℝ => (fun u : ℝ =>
          intCharacter (-m₁) (-(r - p₂)) * (intCharacter (-m₁) u * G u))
            (r' + (r - p₂)) := by
      funext r'
      have hcancel :
          intCharacter (-m₁) (-(r - p₂)) * intCharacter (-m₁) (r' + (r - p₂)) =
            intCharacter (-m₁) r' := by
        rw [intCharacter_add_arg, ← mul_assoc, mul_comm
          (intCharacter (-m₁) (-(r - p₂))) (intCharacter (-m₁) r'),
          mul_assoc, ← intCharacter_add_arg]
        rw [show -(r - p₂) + (r - p₂) = 0 by ring, intCharacter_zero, mul_one]
      have halpha : mixedAlpha p₂ r r' = r' + (r - p₂) := by
        rw [mixedAlpha]; ring
      rw [halpha, ← hcancel]
      ring
    rw [hshift, torusIntegral_comp_add_right hHper (r - p₂),
      torusIntegral_const_mul, hc₁]
  rw [funext hinner]
  have houter : (fun r : ℝ =>
      intCharacter (-m₀) r * (intCharacter (-m₁) (-(r - p₂)) * c₁)) =
      fun r : ℝ => intCharacter (-m₀ + m₁) r *
        (intCharacter (-m₁) p₂ * c₁) := by
    funext r
    have hsplit : intCharacter (-m₁) (-(r - p₂)) =
        intCharacter (-m₁) (-r) * intCharacter (-m₁) p₂ := by
      rw [← intCharacter_add_arg]
      congr 1
      ring
    rw [hsplit, intCharacter_neg_arg, neg_neg, ← intCharacter_add_index]
    ring
  rw [houter, torusIntegral_mul_const, torusIntegral_intCharacter']
  by_cases hm : m₀ = m₁
  · subst hm
    rw [if_pos rfl, if_pos (by omega : -m₀ + m₀ = 0), one_mul]
  · rw [if_neg hm, if_neg (by omega : ¬(-m₀ + m₁ = 0)), zero_mul]

/-- Character orthogonality. A two-row frequency coefficient that depends on
the two row frequencies only through `alpha` has vanishing Walsh coefficient
at every genuine two-element row index. This is the paper's "`Pi_2` removes
it" (`manuscript.tex:1279-1281`). -/
theorem twoRowFourierCoefficient_comp_mixedAlpha (p₂ : ℝ) (G : ℝ → ℂ)
    (hG : Function.Periodic G (2 * Real.pi)) (T : Type11Index) :
    twoRowFourierCoefficient (fun r r' => G (mixedAlpha p₂ r r')) T = 0 := by
  rw [twoRowFourierCoefficient,
    torusIntegral₂_character_comp_mixedAlpha p₂ (type11RawIndex T 0)
      (type11RawIndex T 1) G hG,
    if_neg (type11RawIndex_ne T)]

/-! ## Closure properties of the bounded measurable classes -/

theorem TorusBoundedThree.integrable_row {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (r beta : ℝ) :
    Integrable (fun r' => k r r' beta) (volume.restrict Estimates.torus) := by
  have hmeas := hk.measurable_row r beta
  obtain ⟨-, C, hC⟩ := hk
  exact integrable_torus_of_bound hmeas.aestronglyMeasurable
    (fun r' => hC r r' beta)

theorem TorusBoundedThree.integrable_col {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (r r' : ℝ) :
    Integrable (fun beta => k r r' beta) (volume.restrict Estimates.torus) := by
  have hmeas := hk.measurable_col r r'
  obtain ⟨-, C, hC⟩ := hk
  exact integrable_torus_of_bound hmeas.aestronglyMeasurable
    (fun beta => hC r r' beta)

/-- The coincident-row part of a bounded measurable raw coefficient is again
bounded and measurable. -/
theorem TorusBoundedThree.rawDiagonalPart {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (p₂ : ℝ) :
    TorusBoundedTwo (Manhattan.Glue.rawDiagonalPart p₂ k) := by
  obtain ⟨hm, C, hC⟩ := hk
  constructor
  · have hcomp : Measurable fun w : (ℝ × ℝ) × ℝ =>
        k w.2 (w.1.1 - w.2 + p₂) w.1.2 :=
      hm.comp (measurable_snd.prodMk
        ((((measurable_fst.comp measurable_fst).sub measurable_snd).add
          measurable_const).prodMk (measurable_snd.comp measurable_fst)))
    exact (stronglyMeasurable_torusIntegral hcomp.stronglyMeasurable).measurable
  · exact ⟨C, fun alpha beta =>
      norm_torusIntegral_le_of_bound (fun t => hC t (alpha - t + p₂) beta)⟩

/-- The diagonal embedding of a bounded measurable carrier is bounded and
measurable. -/
theorem TorusBoundedTwo.diagonalRawCarrier {ell : ℝ → ℝ → ℂ}
    (hell : TorusBoundedTwo ell) (p₂ : ℝ) :
    TorusBoundedThree (Manhattan.Glue.diagonalRawCarrier p₂ ell) := by
  obtain ⟨hm, C, hC⟩ := hell
  refine ⟨?_, ⟨C, fun r r' beta => hC _ _⟩⟩
  exact hm.comp ((((measurable_fst.add
    (measurable_fst.comp measurable_snd)).sub measurable_const)).prodMk
      (measurable_snd.comp measurable_snd))

/-- The two-row lowering component of a bounded measurable raw coefficient is
bounded and measurable. -/
theorem TorusBoundedThree.rawD2StarTwoRow {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (p₂ : ℝ) :
    TorusBoundedTwo (Manhattan.Glue.rawD2StarTwoRow p₂ k) := by
  obtain ⟨hm, C, hC⟩ := hk
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  constructor
  · have hcomp : Measurable fun w : (ℝ × ℝ) × ℝ => k w.1.1 w.1.2 w.2 :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hint : Measurable fun z : ℝ × ℝ =>
        Estimates.torusIntegral fun beta => k z.1 z.2 beta :=
      (stronglyMeasurable_torusIntegral hcomp.stronglyMeasurable).measurable
    have hsin : Measurable fun z : ℝ × ℝ =>
        (-Complex.I * (Real.sin (mixedAlpha p₂ z.1 z.2) : ℂ)) := by
      unfold mixedAlpha
      fun_prop
    exact hsin.mul hint
  · refine ⟨C, fun r r' => ?_⟩
    rw [Manhattan.Glue.rawD2StarTwoRow, norm_mul, norm_mul, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.sin (mixedAlpha p₂ r r')| *
          ‖Estimates.torusIntegral fun beta => k r r' beta‖ ≤ 1 * C := by
        apply mul_le_mul (Real.abs_sin_le_one _)
          (norm_torusIntegral_le_of_bound (fun beta => hC r r' beta))
          (norm_nonneg _) zero_le_one
      _ = C := one_mul C

/-! ## Linearity of the lowering formulas -/

theorem rawD2StarMixed_sub {k k' : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (hk' : TorusBoundedThree k') (r beta : ℝ) :
    rawD2StarMixed (fun a b c => k a b c - k' a b c) r beta =
      rawD2StarMixed k r beta - rawD2StarMixed k' r beta := by
  rw [rawD2StarMixed, rawD2StarMixed, rawD2StarMixed,
    torusIntegral_sub (hk.integrable_row r beta) (hk'.integrable_row r beta),
    mul_sub]

theorem rawD2StarTwoRow_sub {k k' : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (hk' : TorusBoundedThree k') (p₂ r r' : ℝ) :
    rawD2StarTwoRow p₂ (fun a b c => k a b c - k' a b c) r r' =
      rawD2StarTwoRow p₂ k r r' - rawD2StarTwoRow p₂ k' r r' := by
  rw [rawD2StarTwoRow, rawD2StarTwoRow, rawD2StarTwoRow,
    torusIntegral_sub (hk.integrable_col r r') (hk'.integrable_col r r'),
    mul_sub]

theorem twoRowFourierCoefficient_sub {F F' : ℝ → ℝ → ℂ}
    (hF : TorusBoundedTwo F) (hF' : TorusBoundedTwo F') (T : Type11Index) :
    twoRowFourierCoefficient (fun r r' => F r r' - F' r r') T =
      twoRowFourierCoefficient F T - twoRowFourierCoefficient F' T := by
  obtain ⟨hm, C, hC⟩ := hF
  obtain ⟨hm', C', hC'⟩ := hF'
  set n₀ := type11RawIndex T 0
  set n₁ := type11RawIndex T 1
  have hkernel : ∀ (G : ℝ → ℝ → ℂ) (CG : ℝ)
      (hGm : Measurable fun z : ℝ × ℝ => G z.1 z.2)
      (hGC : ∀ x y, ‖G x y‖ ≤ CG),
      (∀ r, Integrable (fun r' => intCharacter (-n₀) r *
          intCharacter (-n₁) r' * G r r')
        (volume.restrict Estimates.torus)) ∧
      Integrable (fun r => Estimates.torusIntegral fun r' =>
          intCharacter (-n₀) r * intCharacter (-n₁) r' * G r r')
        (volume.restrict Estimates.torus) := by
    intro G CG hGm hGC
    have hCG : 0 ≤ CG := le_trans (norm_nonneg _) (hGC 0 0)
    have hbound : ∀ r r', ‖intCharacter (-n₀) r * intCharacter (-n₁) r' *
        G r r'‖ ≤ CG := by
      intro r r'
      rw [norm_mul, norm_mul, norm_intCharacter, norm_intCharacter, one_mul,
        one_mul]
      exact hGC r r'
    have hjoint : Measurable fun z : ℝ × ℝ =>
        intCharacter (-n₀) z.1 * intCharacter (-n₁) z.2 * G z.1 z.2 := by
      have h1 : Measurable fun z : ℝ × ℝ => intCharacter (-n₀) z.1 := by
        unfold intCharacter
        fun_prop
      have h2 : Measurable fun z : ℝ × ℝ => intCharacter (-n₁) z.2 := by
        unfold intCharacter
        fun_prop
      exact (h1.mul h2).mul hGm
    refine ⟨fun r => ?_, ?_⟩
    · exact integrable_torus_of_bound
        (hjoint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (fun r' => hbound r r')
    · refine integrable_torus_of_bound ?_ (fun r =>
        norm_torusIntegral_le_of_bound (fun r' => hbound r r'))
      exact ((stronglyMeasurable_torusIntegral
        hjoint.stronglyMeasurable).measurable).aestronglyMeasurable
  obtain ⟨hinnerF, houterF⟩ := hkernel F C hm hC
  obtain ⟨hinnerF', houterF'⟩ := hkernel F' C' hm' hC'
  rw [twoRowFourierCoefficient, twoRowFourierCoefficient,
    twoRowFourierCoefficient]
  rw [← torusIntegral_sub houterF houterF']
  congr 1
  funext r
  rw [← torusIntegral_sub (hinnerF r) (hinnerF' r)]
  congr 1
  funext r'
  ring

/-! ## Periodicity propagation -/

theorem rawDiagonalPart_periodic {k : ℝ → ℝ → ℝ → ℂ} (p₂ : ℝ)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (beta : ℝ) :
    Function.Periodic (fun alpha => rawDiagonalPart p₂ k alpha beta)
      (2 * Real.pi) := by
  intro alpha
  dsimp only
  rw [rawDiagonalPart, rawDiagonalPart]
  congr 1
  funext t
  rw [show alpha + 2 * Real.pi - t + p₂ = (alpha - t + p₂) + 2 * Real.pi by ring]
  exact hper t beta (alpha - t + p₂)

theorem diagonalTwoRowSymbol_periodic {ell : ℝ → ℝ → ℂ}
    (hper : ∀ beta, Function.Periodic (fun alpha => ell alpha beta)
      (2 * Real.pi)) :
    Function.Periodic (diagonalTwoRowSymbol ell) (2 * Real.pi) := by
  intro alpha
  rw [diagonalTwoRowSymbol, diagonalTwoRowSymbol, Real.sin_add_two_pi]
  congr 2
  funext beta
  exact hper beta alpha

/-! ## The concrete lowering input and the difference carrier -/

/-- Scaling a raw coefficient by a constant. -/
def scaleRaw (c : ℂ) (k : ℝ → ℝ → ℝ → ℂ) (r r' beta : ℝ) : ℂ :=
  c * k r r' beta

theorem torusBounded₃_scaleRaw {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (c : ℂ) : TorusBoundedThree (scaleRaw c k) := by
  obtain ⟨hm, C, hC⟩ := hk
  refine ⟨measurable_const.mul hm, ‖c‖ * C, fun r r' beta => ?_⟩
  rw [scaleRaw, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC r r' beta) (norm_nonneg c)

theorem scaleRaw_periodic {k : ℝ → ℝ → ℝ → ℂ}
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (c : ℂ) (r beta : ℝ) :
    Function.Periodic (fun r' => scaleRaw c k r r' beta) (2 * Real.pi) := by
  intro r'
  show c * k r (r' + 2 * Real.pi) beta = c * k r r' beta
  have h := hper r beta r'
  simp only at h
  rw [h]

@[simp] theorem rawDiagonalPart_scaleRaw (c : ℂ) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ) (alpha beta : ℝ) :
    rawDiagonalPart p₂ (scaleRaw c k) alpha beta =
      c * rawDiagonalPart p₂ k alpha beta := by
  rw [rawDiagonalPart, rawDiagonalPart, ← torusIntegral_const_mul]
  rfl

theorem projectionMixedError_const_mul (c : ℂ) (ell : ℝ → ℝ → ℂ) (beta : ℝ) :
    projectionMixedError (fun alpha beta => c * ell alpha beta) beta =
      c * projectionMixedError ell beta := by
  rw [projectionMixedError, projectionMixedError, torusIntegral_const_mul]
  ring

/-- CROSS-LANE INPUT (the formalization, concrete lowering formulas; the paper's
(D2a)--(D2b) at `manuscript.tex:827-834`). The concrete Finset operator
`D_2^*` evaluated on the projected coefficient `Pi_3 ktilde` is computed by the
paper's formulas in the shifted frequency variables, up to the two Finset
normalization constants `cTwoNorm` and `cMixNorm` of the type-`11` and
type-`12` sectors. the formalization proves this with `cTwoNorm = 1` and
`cMixNorm = sqrt 2` (`Manhattan.Glue.frequency_D2a`,
`Manhattan.Glue.frequency_D2b`); nothing below depends on their values.
Nothing else about the concrete operator is used here. -/
def ConcreteLoweringFormula (cTwoNorm cMixNorm : ℂ) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ)
    (concreteTwoRow : Type11Index → ℂ) (concreteMixed : ℝ → ℝ → ℂ) : Prop :=
  (∀ T : Type11Index, concreteTwoRow T =
      cTwoNorm * twoRowFourierCoefficient
        (rawD2StarTwoRow p₂ (rawOffDiagonalPart p₂ k)) T) ∧
    (∀ r beta : ℝ, concreteMixed r beta =
      cMixNorm * rawD2StarMixed (rawOffDiagonalPart p₂ k) r beta)

/-- The actual operator difference `Pi_2 Dtilde_2^* ktilde - D_2^* k` of
Lemma 5.3, packaged in the carrier of `Manhattan.Glue.ProjectionError`. -/
def rawProjectionDifference (cTwoNorm cMixNorm : ℂ) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ)
    (concreteTwoRow : Type11Index → ℂ) (concreteMixed : ℝ → ℝ → ℂ) :
    ProjectionErrorComponents where
  twoRow := fun T =>
    cTwoNorm * twoRowFourierCoefficient (rawD2StarTwoRow p₂ k) T -
      concreteTwoRow T
  mixed := fun r beta =>
    cMixNorm * rawD2StarMixed k r beta - concreteMixed r beta

theorem torusBounded₃_rawOffDiagonalPart {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (p₂ : ℝ) :
    TorusBoundedThree (rawOffDiagonalPart p₂ k) :=
  hk.sub ((hk.rawDiagonalPart p₂).diagonalRawCarrier p₂)

/-- **Discharge of the first interface.** The complete frequency-space
calculation identifies the raw/projected lowering difference with the carrier
`projectionErrorComponents` of the coincident-row part, rescaled by the mixed
Finset normalization. Only the concrete lowering formulas of the formalization are
imported. -/
theorem rawProjectionDifferenceIdentification_of_lowering
    {cTwoNorm cMixNorm : ℂ} {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    {concreteTwoRow : Type11Index → ℂ} {concreteMixed : ℝ → ℝ → ℂ}
    (hform : ConcreteLoweringFormula cTwoNorm cMixNorm p₂ k concreteTwoRow
      concreteMixed) :
    RawProjectionDifferenceIdentification
      (rawProjectionDifference cTwoNorm cMixNorm p₂ k concreteTwoRow
        concreteMixed)
      (rawDiagonalPart p₂ (scaleRaw cMixNorm k)) := by
  obtain ⟨hformTwo, hformMixed⟩ := hform
  set ell := rawDiagonalPart p₂ k with hell
  have hellPer : ∀ beta, Function.Periodic (fun alpha => ell alpha beta)
      (2 * Real.pi) := rawDiagonalPart_periodic p₂ hper
  have hoff : TorusBoundedThree (rawOffDiagonalPart p₂ k) :=
    torusBounded₃_rawOffDiagonalPart hk p₂
  have hsplit : (fun a b c => k a b c - rawOffDiagonalPart p₂ k a b c) =
      diagonalRawCarrier p₂ ell := by
    funext a b c
    exact sub_rawOffDiagonalPart p₂ k a b c
  rw [RawProjectionDifferenceIdentification, rawProjectionDifference,
    projectionErrorComponents]
  simp only [ProjectionErrorComponents.mk.injEq]
  constructor
  · funext T
    rw [hformTwo T, ← mul_sub,
      ← twoRowFourierCoefficient_sub (hk.rawD2StarTwoRow p₂)
        (hoff.rawD2StarTwoRow p₂) T]
    have hfun : (fun r r' => rawD2StarTwoRow p₂ k r r' -
        rawD2StarTwoRow p₂ (rawOffDiagonalPart p₂ k) r r') =
        fun r r' => diagonalTwoRowSymbol ell (mixedAlpha p₂ r r') := by
      funext r r'
      rw [← rawD2StarTwoRow_sub hk hoff p₂ r r', hsplit]
      exact rawD2StarTwoRow_diagonalRawCarrier p₂ ell r r'
    rw [hfun,
      twoRowFourierCoefficient_comp_mixedAlpha p₂ _
        (diagonalTwoRowSymbol_periodic hellPer) T, mul_zero]
    rfl
  · funext r beta
    rw [hformMixed r beta, ← mul_sub, ← rawD2StarMixed_sub hk hoff r beta,
      hsplit, rawD2StarMixed_diagonalRawCarrier p₂ ell hellPer r beta]
    rw [show rawDiagonalPart p₂ (scaleRaw cMixNorm k) =
        (fun alpha beta => cMixNorm * ell alpha beta) by
      funext alpha beta
      exact rawDiagonalPart_scaleRaw cMixNorm p₂ k alpha beta]
    rw [projectionMixedError_const_mul]

/-- **Lemma 5.3, qualitative clause, unconditional.** The raw/projected
lowering difference has no two-row component. -/
theorem rawProjectionDifference_twoRow_eq_zero
    {cTwoNorm cMixNorm : ℂ} {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    {concreteTwoRow : Type11Index → ℂ} {concreteMixed : ℝ → ℝ → ℂ}
    (hform : ConcreteLoweringFormula cTwoNorm cMixNorm p₂ k concreteTwoRow
      concreteMixed) :
    (rawProjectionDifference cTwoNorm cMixNorm p₂ k concreteTwoRow
      concreteMixed).twoRow = 0 :=
  rawProjectionDifference_onlyMixed _ _
    (rawProjectionDifferenceIdentification_of_lowering hk hper hform)

/-! ## The weighted contractivity (46) -/

theorem measurable_multiplier_comp {X : Type*} [MeasurableSpace X]
    (kappa : ℝ) (q : Estimates.Parameters) {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x : X =>
      Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency (f x) (g x)) := by
  simp only [Estimates.multiplier, Estimates.mixedTotalFrequency,
    Estimates.theta, Estimates.dispersion, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  fun_prop

/-- The raw multiplier quadratic form `⟨ktilde, M ktilde⟩` in the shifted
frequency variables (`manuscript.tex:983-987`). -/
def rawMultiplierEnergy (kappa : ℝ) (q : Estimates.Parameters) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ) : ℝ :=
  Estimates.torusIntegral fun beta =>
    Estimates.torusIntegral fun r =>
      Estimates.torusIntegral fun r' =>
        Estimates.multiplier kappa q
            (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
          ‖k r r' beta‖ ^ 2

/-- The integrand of the raw energy, written along the fibre `r + r' - p₂`. -/
def shiftedEnergyIntegrand (kappa : ℝ) (q : Estimates.Parameters) (p₂ : ℝ)
    (k : ℝ → ℝ → ℝ → ℂ) (beta alpha t : ℝ) : ℝ :=
  Estimates.multiplier kappa q (Estimates.mixedTotalFrequency beta alpha) *
    ‖k t (alpha - t + p₂) beta‖ ^ 2

section Energy

variable {kappa : ℝ} {q : Estimates.Parameters} {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}

private theorem multiplier_nonneg' (hkappa : 0 ≤ kappa) (hlambda : 0 ≤ q.lambda)
    (beta alpha : ℝ) :
    0 ≤ Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta alpha) :=
  Estimates.multiplier_nonneg hkappa hlambda _

private theorem measurable_shift (hk : TorusBoundedThree k) (p₂ alpha beta : ℝ) :
    Measurable fun t : ℝ => k t (alpha - t + p₂) beta :=
  hk.1.comp (measurable_id.prodMk
    (((measurable_const.sub measurable_id).add measurable_const).prodMk
      measurable_const))

/-- Fibrewise Cauchy--Schwarz: the coincident-row energy is dominated by the
average of the raw energy along the fibre. -/
private theorem diagonal_pointwise_le (hkappa : 0 ≤ kappa)
    (hlambda : 0 ≤ q.lambda) (hk : TorusBoundedThree k) (beta alpha : ℝ) :
    Estimates.multiplier kappa q (Estimates.mixedTotalFrequency beta alpha) *
        ‖rawDiagonalPart p₂ k alpha beta‖ ^ 2 ≤
      Estimates.torusIntegral
        (shiftedEnergyIntegrand kappa q p₂ k beta alpha) := by
  obtain ⟨C, hC⟩ := hk.2
  have hjensen := norm_torusIntegral_sq_le_of_bound
    (measurable_shift hk p₂ alpha beta) (fun t => hC t (alpha - t + p₂) beta)
  have hrw : Estimates.torusIntegral
      (shiftedEnergyIntegrand kappa q p₂ k beta alpha) =
      Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) *
        Estimates.torusIntegral
          (fun t : ℝ => ‖k t (alpha - t + p₂) beta‖ ^ 2) := by
    rw [← torusIntegral_real_const_mul]
    rfl
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hjensen
    (multiplier_nonneg' hkappa hlambda beta alpha)

private theorem norm_rawDiagonalPart_le {C : ℝ}
    (hC : ∀ r r' beta, ‖k r r' beta‖ ≤ C) (alpha beta : ℝ) :
    ‖rawDiagonalPart p₂ k alpha beta‖ ≤ C :=
  norm_torusIntegral_le_of_bound (fun t => hC t (alpha - t + p₂) beta)

private theorem energy_integrand_bound (hkappa : 0 ≤ kappa)
    (hlambda : 0 ≤ q.lambda) {C : ℝ} (hCnonneg : 0 ≤ C) {z : ℂ}
    (hz : ‖z‖ ≤ C) (beta alpha : ℝ) :
    ‖Estimates.multiplier kappa q (Estimates.mixedTotalFrequency beta alpha) *
        ‖z‖ ^ 2‖ ≤ kappa * (q.lambda + 8) * C ^ 2 := by
  have hnn := multiplier_nonneg' hkappa hlambda beta alpha
  have hCm : 0 ≤ kappa * (q.lambda + 8) :=
    le_trans hnn (multiplier_le hkappa _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (sq_nonneg _))]
  apply mul_le_mul (multiplier_le hkappa _) _ (sq_nonneg _) hCm
  nlinarith [norm_nonneg z]

/-- Weighted contractivity at one column frequency: the frequency-space form
of `int M |ell|^2 <= <ktilde, M ktilde>` (`manuscript.tex:1299-1302`), proved
by fibrewise Cauchy--Schwarz, Fubini, and translation invariance. -/
theorem diagonalMultiplierEnergy_slice_le (hkappa : 0 ≤ kappa)
    (hlambda : 0 ≤ q.lambda) (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (beta : ℝ) :
    (Estimates.torusIntegral fun alpha : ℝ =>
        Estimates.multiplier kappa q
            (Estimates.mixedTotalFrequency beta alpha) *
          ‖rawDiagonalPart p₂ k alpha beta‖ ^ 2) ≤
      Estimates.torusIntegral fun r : ℝ =>
        Estimates.torusIntegral fun r' : ℝ =>
          Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ r r')) *
            ‖k r r' beta‖ ^ 2 := by
  obtain ⟨C, hC⟩ := hk.2
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  have hFmeas : Measurable
      (Function.uncurry (shiftedEnergyIntegrand kappa q p₂ k beta)) := by
    have h1 : Measurable fun z : ℝ × ℝ =>
        Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta z.1) :=
      measurable_multiplier_comp kappa q measurable_const measurable_fst
    have h2 : Measurable fun z : ℝ × ℝ => k z.2 (z.1 - z.2 + p₂) beta :=
      hk.1.comp (measurable_snd.prodMk
        (((measurable_fst.sub measurable_snd).add measurable_const).prodMk
          measurable_const))
    exact h1.mul (h2.norm.pow_const 2)
  have hFbound : ∀ z : ℝ × ℝ,
      ‖Function.uncurry (shiftedEnergyIntegrand kappa q p₂ k beta) z‖ ≤
        kappa * (q.lambda + 8) * C ^ 2 := by
    rintro ⟨alpha, t⟩
    exact energy_integrand_bound hkappa hlambda hCnonneg
      (hC t (alpha - t + p₂) beta) beta alpha
  have hFint : Integrable
      (Function.uncurry (shiftedEnergyIntegrand kappa q p₂ k beta))
      ((volume.restrict Estimates.torus).prod
        (volume.restrict Estimates.torus)) :=
    integrable_prod_torus_of_bound hFmeas.aestronglyMeasurable hFbound
  have hstep1 :
      (Estimates.torusIntegral fun alpha : ℝ =>
          Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency beta alpha) *
            ‖rawDiagonalPart p₂ k alpha beta‖ ^ 2) ≤
        Estimates.torusIntegral fun alpha : ℝ =>
          Estimates.torusIntegral
            (shiftedEnergyIntegrand kappa q p₂ k beta alpha) := by
    apply torusIntegral_mono
    · refine integrable_torus_of_bound ?_
        (C := kappa * (q.lambda + 8) * C ^ 2) ?_
      · have h1 : Measurable fun alpha : ℝ =>
            Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency beta alpha) :=
          measurable_multiplier_comp kappa q measurable_const measurable_id
        have h2 : Measurable fun alpha : ℝ =>
            rawDiagonalPart p₂ k alpha beta :=
          (hk.rawDiagonalPart p₂).1.comp
            (measurable_id.prodMk measurable_const)
        exact ((h1.mul (h2.norm.pow_const 2))).aestronglyMeasurable
      · intro alpha
        exact energy_integrand_bound hkappa hlambda hCnonneg
          (norm_rawDiagonalPart_le hC alpha beta) beta alpha
    · have h := Integrable.smul ((2 * Real.pi)⁻¹) hFint.integral_prod_left
      simpa only [Estimates.torusIntegral, Function.uncurry_apply_pair]
        using h
    · intro alpha
      exact diagonal_pointwise_le hkappa hlambda hk beta alpha
  rw [torusIntegral_swap hFint] at hstep1
  refine hstep1.trans (le_of_eq ?_)
  congr 1
  funext t
  have hΨper : Function.Periodic
      (fun alpha : ℝ => shiftedEnergyIntegrand kappa q p₂ k beta alpha t)
      (2 * Real.pi) := by
    intro alpha
    show Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta (alpha + 2 * Real.pi)) *
        ‖k t (alpha + 2 * Real.pi - t + p₂) beta‖ ^ 2 =
      Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta alpha) *
        ‖k t (alpha - t + p₂) beta‖ ^ 2
    have hmul : Estimates.multiplier kappa q
        (Estimates.mixedTotalFrequency beta (alpha + 2 * Real.pi)) =
        Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) :=
      multiplier_periodic kappa q beta alpha
    rw [hmul]
    congr 2
    rw [show alpha + 2 * Real.pi - t + p₂ = (alpha - t + p₂) + 2 * Real.pi by
      ring]
    exact congrArg norm (hper t beta (alpha - t + p₂))
  rw [← torusIntegral_comp_add_right hΨper (t - p₂)]
  congr 1
  funext r'
  show Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta (r' + (t - p₂))) *
      ‖k t (r' + (t - p₂) - t + p₂) beta‖ ^ 2 =
    Estimates.multiplier kappa q
      (Estimates.mixedTotalFrequency beta (mixedAlpha p₂ t r')) *
      ‖k t r' beta‖ ^ 2
  rw [show r' + (t - p₂) - t + p₂ = r' by ring,
    show r' + (t - p₂) = mixedAlpha p₂ t r' by rw [mixedAlpha]; ring]

/-- **Discharge of the second interface.** The omitted diagonal coefficient
is the fibre average of the raw coefficient, that projection commutes with a
multiplier depending only on the total frequency, and the resulting
contraction is the paper's (46). -/
theorem diagonalMultiplierEnergy_le_rawMultiplierEnergy (hkappa : 0 ≤ kappa)
    (hlambda : 0 ≤ q.lambda) (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi)) :
    diagonalMultiplierEnergy kappa q (rawDiagonalPart p₂ k) ≤
      rawMultiplierEnergy kappa q p₂ k := by
  obtain ⟨C, hC⟩ := hk.2
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  rw [diagonalMultiplierEnergy, rawMultiplierEnergy]
  apply torusIntegral_mono
  · refine integrable_torus_of_bound ?_
      (C := kappa * (q.lambda + 8) * C ^ 2) ?_
    · have hjoint : Measurable fun z : ℝ × ℝ =>
          Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency z.1 z.2) *
            ‖rawDiagonalPart p₂ k z.2 z.1‖ ^ 2 :=
        (measurable_multiplier_comp kappa q measurable_fst measurable_snd).mul
          (((hk.rawDiagonalPart p₂).1.comp
            (measurable_snd.prodMk measurable_fst)).norm.pow_const 2)
      exact ((stronglyMeasurable_torusIntegral
        hjoint.stronglyMeasurable).measurable).aestronglyMeasurable
    · intro beta
      refine norm_torusIntegral_le_of_bound (fun alpha => ?_)
      exact energy_integrand_bound hkappa hlambda hCnonneg
        (norm_rawDiagonalPart_le hC alpha beta) beta alpha
  · refine integrable_torus_of_bound ?_
      (C := kappa * (q.lambda + 8) * C ^ 2) ?_
    · have hjoint : Measurable fun w : (ℝ × ℝ) × ℝ =>
          Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency w.1.1
                (mixedAlpha p₂ w.1.2 w.2)) *
            ‖k w.1.2 w.2 w.1.1‖ ^ 2 := by
        have h1 : Measurable fun w : (ℝ × ℝ) × ℝ =>
            Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency w.1.1
                (mixedAlpha p₂ w.1.2 w.2)) := by
          refine measurable_multiplier_comp kappa q
            (measurable_fst.comp measurable_fst) ?_
          unfold mixedAlpha
          fun_prop
        have h2 : Measurable fun w : (ℝ × ℝ) × ℝ => k w.1.2 w.2 w.1.1 :=
          hk.1.comp ((measurable_snd.comp measurable_fst).prodMk
            (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
        exact h1.mul (h2.norm.pow_const 2)
      exact ((stronglyMeasurable_torusIntegral
        ((stronglyMeasurable_torusIntegral
          hjoint.stronglyMeasurable).measurable).stronglyMeasurable
          ).measurable).aestronglyMeasurable
    · intro beta
      refine norm_torusIntegral_le_of_bound (fun r => ?_)
      refine norm_torusIntegral_le_of_bound (fun r' => ?_)
      exact energy_integrand_bound hkappa hlambda hCnonneg
        (hC r r' beta) beta (mixedAlpha p₂ r r')
  · intro beta
    exact diagonalMultiplierEnergy_slice_le hkappa hlambda hk hper beta

end Energy

/-! ## Finiteness of the projection-error integrals -/

section Finiteness

variable {kappa : ℝ} {q : Estimates.Parameters} {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}

private theorem measurable_projectionMixedError {ell : ℝ → ℝ → ℂ}
    (hell : TorusBoundedTwo ell) :
    Measurable fun beta : ℝ => projectionMixedError ell beta := by
  have h : Measurable fun beta : ℝ =>
      Estimates.torusIntegral fun alpha : ℝ => ell alpha beta := by
    refine (stronglyMeasurable_torusIntegral (F := fun w : ℝ × ℝ => ell w.2 w.1)
      ?_).measurable
    exact (hell.1.comp (measurable_snd.prodMk measurable_fst)).stronglyMeasurable
  have hsin : Measurable fun beta : ℝ =>
      (-Complex.I * (Real.sin beta : ℂ)) := by fun_prop
  exact hsin.mul h

private theorem norm_projectionMixedError_le {ell : ℝ → ℝ → ℂ} {C : ℝ}
    (hC : ∀ alpha beta, ‖ell alpha beta‖ ≤ C) (beta : ℝ) :
    ‖projectionMixedError ell beta‖ ≤ C := by
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  rw [projectionMixedError, norm_mul, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |Real.sin beta| *
        ‖Estimates.torusIntegral fun alpha : ℝ => ell alpha beta‖ ≤ 1 * C :=
      mul_le_mul (Real.abs_sin_le_one _)
        (norm_torusIntegral_le_of_bound (fun alpha => hC alpha beta))
        (norm_nonneg _) zero_le_one
    _ = C := one_mul C

private theorem mixedHMinusWeight_le (hlambda : 0 < q.lambda) (r beta : ℝ) :
    Estimates.mixedHMinusWeight q r beta ≤ q.lambda⁻¹ := by
  rw [Estimates.mixedHMinusWeight]
  have hpos : 0 < q.lambda + Estimates.dispersion r + Estimates.dispersion beta := by
    linarith [Estimates.dispersion_nonneg r, Estimates.dispersion_nonneg beta]
  refine (inv_le_inv₀ hpos hlambda).2 ?_
  linarith [Estimates.dispersion_nonneg r, Estimates.dispersion_nonneg beta]

/-- All four finiteness certificates required by
`Manhattan.Glue.ProjectionErrorIntegrable` hold for the coincident-row part of
a bounded measurable raw coefficient. -/
theorem projectionErrorIntegrable_rawDiagonalPart (hkappa : 0 ≤ kappa)
    (hlambda : 0 < q.lambda) (hk : TorusBoundedThree k) :
    ProjectionErrorIntegrable kappa q (rawDiagonalPart p₂ k) := by
  obtain ⟨C, hC⟩ := hk.2
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0 0)
  have hell : TorusBoundedTwo (rawDiagonalPart p₂ k) := hk.rawDiagonalPart p₂
  have hellC : ∀ alpha beta, ‖rawDiagonalPart p₂ k alpha beta‖ ≤ C :=
    fun alpha beta => norm_rawDiagonalPart_le hC alpha beta
  have hmultInner : ∀ beta : ℝ, Integrable (fun alpha : ℝ =>
      Estimates.multiplier kappa q
          (Estimates.mixedTotalFrequency beta alpha) *
        ‖rawDiagonalPart p₂ k alpha beta‖ ^ 2)
      (volume.restrict Estimates.torus) := by
    intro beta
    refine integrable_torus_of_bound ?_
      (C := kappa * (q.lambda + 8) * C ^ 2) ?_
    · have h1 : Measurable fun alpha : ℝ =>
          Estimates.multiplier kappa q
            (Estimates.mixedTotalFrequency beta alpha) :=
        measurable_multiplier_comp kappa q measurable_const measurable_id
      have h2 : Measurable fun alpha : ℝ => rawDiagonalPart p₂ k alpha beta :=
        hell.measurable_left beta
      exact (h1.mul (h2.norm.pow_const 2)).aestronglyMeasurable
    · intro alpha
      exact energy_integrand_bound hkappa hlambda.le hCnonneg
        (hellC alpha beta) beta alpha
  refine ⟨fun beta => hell.measurable_left beta, hmultInner, ?_, ?_⟩
  · refine integrable_torus_of_bound ?_ (C := q.lambda⁻¹ * C ^ 2) ?_
    · have hjoint : Measurable fun w : ℝ × ℝ =>
          Estimates.mixedHMinusWeight q w.2 w.1 *
            ‖projectionMixedError (rawDiagonalPart p₂ k) w.1‖ ^ 2 := by
        have h1 : Measurable fun w : ℝ × ℝ =>
            Estimates.mixedHMinusWeight q w.2 w.1 := by
          unfold Estimates.mixedHMinusWeight Estimates.dispersion
          fun_prop
        have h2 : Measurable fun w : ℝ × ℝ =>
            projectionMixedError (rawDiagonalPart p₂ k) w.1 :=
          (measurable_projectionMixedError hell).comp measurable_fst
        exact h1.mul (h2.norm.pow_const 2)
      exact ((stronglyMeasurable_torusIntegral
        hjoint.stronglyMeasurable).measurable).aestronglyMeasurable
    · intro beta
      refine norm_torusIntegral_le_of_bound (fun r => ?_)
      have hw : 0 ≤ Estimates.mixedHMinusWeight q r beta := by
        rw [Estimates.mixedHMinusWeight]
        apply inv_nonneg.mpr
        linarith [Estimates.dispersion_nonneg r,
          Estimates.dispersion_nonneg beta, hlambda.le]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
      apply mul_le_mul (mixedHMinusWeight_le hlambda r beta) _ (sq_nonneg _)
        (inv_nonneg.mpr hlambda.le)
      nlinarith [norm_nonneg (projectionMixedError (rawDiagonalPart p₂ k) beta),
        norm_projectionMixedError_le hellC beta]
  · refine integrable_torus_of_bound ?_
      (C := kappa * (q.lambda + 8) * C ^ 2) ?_
    · have hjoint : Measurable fun w : ℝ × ℝ =>
          Estimates.multiplier kappa q
              (Estimates.mixedTotalFrequency w.1 w.2) *
            ‖rawDiagonalPart p₂ k w.2 w.1‖ ^ 2 :=
        (measurable_multiplier_comp kappa q measurable_fst measurable_snd).mul
          (((hell.1.comp (measurable_snd.prodMk measurable_fst)).norm.pow_const 2))
      exact ((stronglyMeasurable_torusIntegral
        hjoint.stronglyMeasurable).measurable).aestronglyMeasurable
    · intro beta
      refine norm_torusIntegral_le_of_bound (fun alpha => ?_)
      exact energy_integrand_bound hkappa hlambda.le hCnonneg
        (hellC alpha beta) beta alpha

/-- **The second interface, discharged.** The weighted contractivity bridge
holds with the raw multiplier quadratic form on the right. -/
theorem rawProjectionEnergyBound_discharged (hlambda : 0 ≤ q.lambda)
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi)) :
    RawProjectionEnergyBound q (rawDiagonalPart p₂ k)
      (rawMultiplierEnergy 40 q p₂ k) :=
  diagonalMultiplierEnergy_le_rawMultiplierEnergy (by norm_num) hlambda hk hper

/-- **Lemma 5.3, unconditional.** The squared `H^-1` norm of the
raw/projected lowering difference is bounded by the raw multiplier quadratic
form, with constant one in the Finset normalization
(`manuscript.tex:1208-1219`). -/
theorem projectionErrorHMinusSq_le_rawMultiplierEnergy_unconditional
    (hlambda : 0 < q.lambda) (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi)) :
    projectionErrorHMinusSq q (rawDiagonalPart p₂ k) ≤
      rawMultiplierEnergy 40 q p₂ k :=
  projectionErrorHMinusSq_le_rawMultiplierEnergy hlambda _ _
    (projectionErrorIntegrable_rawDiagonalPart (by norm_num) hlambda hk)
    (rawProjectionEnergyBound_discharged hlambda.le hk hper)

end Finiteness

/-! ## Periodization

A formula written on `ℝ³` represents a function on the three-torus only after
its arguments are reduced to the fundamental domain. The reduction below
turns any bounded measurable formula into a genuine coefficient satisfying the
periodicity hypothesis used above, without changing its values on
`(-pi, pi]`. -/

/-- Reduction of a real number to the fundamental domain `(-pi, pi]`. -/
def torusWrap (x : ℝ) : ℝ :=
  x - 2 * Real.pi * ⌈(x - Real.pi) / (2 * Real.pi)⌉

theorem torusWrap_periodic : Function.Periodic torusWrap (2 * Real.pi) := by
  intro x
  have htwo : (2 * Real.pi) ≠ 0 := by positivity
  rw [torusWrap, torusWrap,
    show (x + 2 * Real.pi - Real.pi) / (2 * Real.pi) =
      (x - Real.pi) / (2 * Real.pi) + 1 by field_simp; ring,
    Int.ceil_add_one]
  push_cast
  ring

theorem torusWrap_measurable : Measurable torusWrap := by
  unfold torusWrap
  refine measurable_id.sub (measurable_const.mul ?_)
  have h1 : Measurable fun x : ℝ => (x - Real.pi) / (2 * Real.pi) := by
    fun_prop
  exact measurable_from_top.comp (Int.measurable_ceil.comp h1)

theorem torusWrap_eq_self {x : ℝ} (hx : x ∈ Estimates.torus) :
    torusWrap x = x := by
  obtain ⟨hlow, hhigh⟩ := hx
  have htwo : (0 : ℝ) < 2 * Real.pi := by positivity
  have hceil : ⌈(x - Real.pi) / (2 * Real.pi)⌉ = 0 := by
    rw [Int.ceil_eq_zero_iff, Set.mem_Ioc]
    constructor
    · rw [lt_div_iff₀ htwo]
      linarith
    · rw [div_le_iff₀ htwo]
      linarith
  rw [torusWrap, hceil]
  push_cast
  ring

/-- Any bounded measurable formula on `ℝ³` becomes a genuine raw coefficient
after reducing its row-frequency argument to the fundamental domain. -/
def periodizeRow (k : ℝ → ℝ → ℝ → ℂ) (r r' beta : ℝ) : ℂ :=
  k r (torusWrap r') beta

theorem periodizeRow_periodic (k : ℝ → ℝ → ℝ → ℂ) (r beta : ℝ) :
    Function.Periodic (fun r' => periodizeRow k r r' beta) (2 * Real.pi) := by
  intro r'
  show k r (torusWrap (r' + 2 * Real.pi)) beta = k r (torusWrap r') beta
  rw [torusWrap_periodic r']

theorem torusBounded₃_periodizeRow {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) : TorusBoundedThree (periodizeRow k) := by
  obtain ⟨hm, C, hC⟩ := hk
  refine ⟨?_, ⟨C, fun r r' beta => hC r (torusWrap r') beta⟩⟩
  exact hm.comp (measurable_fst.prodMk
    ((torusWrap_measurable.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

theorem periodizeRow_eq {k : ℝ → ℝ → ℝ → ℂ} {r' : ℝ}
    (hr' : r' ∈ Estimates.torus) (r beta : ℝ) :
    periodizeRow k r r' beta = k r r' beta := by
  rw [periodizeRow, torusWrap_eq_self hr']

/-! ## Lemma 5.3 -/

/-- The raw multiplier quadratic form is homogeneous of degree two. -/
theorem rawMultiplierEnergy_scaleRaw (c : ℂ) (kappa : ℝ)
    (q : Estimates.Parameters) (p₂ : ℝ) (k : ℝ → ℝ → ℝ → ℂ) :
    rawMultiplierEnergy kappa q p₂ (scaleRaw c k) =
      ‖c‖ ^ 2 * rawMultiplierEnergy kappa q p₂ k := by
  rw [rawMultiplierEnergy, rawMultiplierEnergy, ← torusIntegral_real_const_mul]
  congr 1
  funext beta
  rw [← torusIntegral_real_const_mul]
  congr 1
  funext r
  rw [← torusIntegral_real_const_mul]
  congr 1
  funext r'
  rw [scaleRaw, norm_mul, mul_pow]
  ring

/-- The mixed component of the actual difference is the mixed error of the
coincident-row part. -/
theorem rawProjectionDifference_mixed_eq
    {cTwoNorm cMixNorm : ℂ} {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    {concreteTwoRow : Type11Index → ℂ} {concreteMixed : ℝ → ℝ → ℂ}
    (hform : ConcreteLoweringFormula cTwoNorm cMixNorm p₂ k concreteTwoRow
      concreteMixed)
    (r beta : ℝ) :
    (rawProjectionDifference cTwoNorm cMixNorm p₂ k concreteTwoRow
        concreteMixed).mixed r beta =
      projectionMixedError (rawDiagonalPart p₂ (scaleRaw cMixNorm k)) beta := by
  have h := rawProjectionDifferenceIdentification_of_lowering hk hper hform
  rw [RawProjectionDifferenceIdentification] at h
  rw [h, projectionError_mixed_apply]

/-- **Lemma 5.3** (`manuscript.tex:1212-1219`), both clauses, unconditional
modulo the concrete lowering formula of the formalization. The universal constant is
the squared mixed Finset normalization: one for `cMixNorm = 1`, two for the
manuscript's `sqrt 2`. -/
theorem lemma_distinct_of_concreteLowering
    {cTwoNorm cMixNorm : ℂ} {q : Estimates.Parameters} {p₂ : ℝ}
    {k : ℝ → ℝ → ℝ → ℂ}
    (hlambda : 0 < q.lambda) (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    {concreteTwoRow : Type11Index → ℂ} {concreteMixed : ℝ → ℝ → ℂ}
    (hform : ConcreteLoweringFormula cTwoNorm cMixNorm p₂ k concreteTwoRow
      concreteMixed) :
    (rawProjectionDifference cTwoNorm cMixNorm p₂ k concreteTwoRow
        concreteMixed).twoRow = 0 ∧
      projectionErrorHMinusSq q
          (rawDiagonalPart p₂ (scaleRaw cMixNorm k)) ≤
        ‖cMixNorm‖ ^ 2 * rawMultiplierEnergy 40 q p₂ k := by
  refine ⟨rawProjectionDifference_twoRow_eq_zero hk hper hform, ?_⟩
  have h := projectionErrorHMinusSq_le_rawMultiplierEnergy_unconditional
    (p₂ := p₂) (k := scaleRaw cMixNorm k) hlambda
    (torusBounded₃_scaleRaw hk cMixNorm)
    (fun r beta => scaleRaw_periodic hper cMixNorm r beta)
  rwa [rawMultiplierEnergy_scaleRaw] at h

/-! ## Iterated normalized integrals of bounded measurable functions -/

/-- Measurability together with a uniform bound, in one variable. -/
def TorusBoundedOne (f : ℝ → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

theorem TorusBoundedOne.integrable {f : ℝ → ℂ} (hf : TorusBoundedOne f) :
    Integrable f (volume.restrict Estimates.torus) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact integrable_torus_of_bound hm.aestronglyMeasurable hC

theorem TorusBoundedTwo.integrable_right {f : ℝ → ℝ → ℂ} (hf : TorusBoundedTwo f)
    (x : ℝ) : Integrable (fun y => f x y) (volume.restrict Estimates.torus) := by
  have hmeas := hf.measurable_right x
  obtain ⟨-, C, hC⟩ := hf
  exact integrable_torus_of_bound hmeas.aestronglyMeasurable (fun y => hC x y)

theorem TorusBoundedTwo.integral_right {f : ℝ → ℝ → ℂ} (hf : TorusBoundedTwo f) :
    TorusBoundedOne fun x => Estimates.torusIntegral fun y => f x y := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨(stronglyMeasurable_torusIntegral
      (F := fun w : ℝ × ℝ => f w.1 w.2) hm.stronglyMeasurable).measurable,
    C, fun x => norm_torusIntegral_le_of_bound (fun y => hC x y)⟩

theorem TorusBoundedThree.integral_col {f : ℝ → ℝ → ℝ → ℂ}
    (hf : TorusBoundedThree f) :
    TorusBoundedTwo fun r r' => Estimates.torusIntegral fun b => f r r' b := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨?_, C, fun r r' => norm_torusIntegral_le_of_bound
    (fun b => hC r r' b)⟩
  have hcomp : Measurable fun w : (ℝ × ℝ) × ℝ => f w.1.1 w.1.2 w.2 :=
    hm.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (stronglyMeasurable_torusIntegral hcomp.stronglyMeasurable).measurable

theorem TorusBoundedTwo.sub {f g : ℝ → ℝ → ℂ} (hf : TorusBoundedTwo f)
    (hg : TorusBoundedTwo g) : TorusBoundedTwo fun x y => f x y - g x y := by
  obtain ⟨hm, C, hC⟩ := hf
  obtain ⟨hm', C', hC'⟩ := hg
  exact ⟨hm.sub hm', C + C', fun x y =>
    (norm_sub_le _ _).trans (add_le_add (hC x y) (hC' x y))⟩

/-- Subtraction passes through a triply iterated normalized integral. -/
theorem torusIntegral₃_sub {f g : ℝ → ℝ → ℝ → ℂ}
    (hf : TorusBoundedThree f) (hg : TorusBoundedThree g) :
    (Estimates.torusIntegral fun r : ℝ => Estimates.torusIntegral fun r' : ℝ =>
        Estimates.torusIntegral fun b : ℝ => f r r' b - g r r' b) =
      (Estimates.torusIntegral fun r : ℝ => Estimates.torusIntegral fun r' : ℝ =>
          Estimates.torusIntegral fun b : ℝ => f r r' b) -
        Estimates.torusIntegral fun r : ℝ => Estimates.torusIntegral fun r' : ℝ =>
          Estimates.torusIntegral fun b : ℝ => g r r' b := by
  have hfc := hf.integral_col
  have hgc := hg.integral_col
  rw [← torusIntegral_sub hfc.integral_right.integrable
    hgc.integral_right.integrable]
  congr 1
  funext r
  rw [← torusIntegral_sub (hfc.integrable_right r) (hgc.integrable_right r)]
  congr 1
  funext r'
  exact torusIntegral_sub (hf.integrable_col r r') (hg.integrable_col r r')

/-! ## `rawOffDiagonalPart` is exactly the projection `Pi_3`

The remaining two theorems justify the frequency-space model: the Fourier
coefficients of `rawOffDiagonalPart` vanish on the coincident-row diagonal and
agree with those of the raw coefficient off it. -/

/-- The three-torus Fourier coefficient of a raw type-`112` coefficient. -/
def rawFourierCoefficient (k : ℝ → ℝ → ℝ → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  Estimates.torusIntegral fun r : ℝ =>
    Estimates.torusIntegral fun r' : ℝ =>
      Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 0) r * intCharacter (-n 1) r' *
          intCharacter (-n 2) beta * k r r' beta

/-- The two-torus Fourier coefficient of a coincident-row carrier. -/
def carrierFourierCoefficient (ell : ℝ → ℝ → ℂ) (m n : ℤ) : ℂ :=
  Estimates.torusIntegral fun alpha : ℝ =>
    Estimates.torusIntegral fun beta : ℝ =>
      intCharacter (-m) alpha * intCharacter (-n) beta * ell alpha beta

theorem torusBounded₃_character_mul {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (n : Fin 3 → ℤ) :
    TorusBoundedThree fun r r' beta =>
      intCharacter (-n 0) r * intCharacter (-n 1) r' *
        intCharacter (-n 2) beta * k r r' beta := by
  obtain ⟨hm, C, hC⟩ := hk
  have hchar : ∀ j : ℤ, Measurable (intCharacter j) := by
    intro j
    unfold intCharacter
    fun_prop
  refine ⟨?_, C, fun r r' beta => ?_⟩
  · exact ((((hchar _).comp measurable_fst).mul
      ((hchar _).comp (measurable_fst.comp measurable_snd))).mul
        ((hchar _).comp (measurable_snd.comp measurable_snd))).mul hm
  · rw [norm_mul, norm_mul, norm_mul, norm_intCharacter, norm_intCharacter,
      norm_intCharacter, one_mul, one_mul, one_mul]
    exact hC r r' beta

/-- The diagonal embedding has Fourier coefficients supported on the
coincident-row diagonal: this is the paper's "in position space, `ell` is
supported where the two row indices coincide" (`manuscript.tex:1276-1278`). -/
theorem rawFourierCoefficient_diagonalRawCarrier (p₂ : ℝ) (ell : ℝ → ℝ → ℂ)
    (hper : ∀ beta, Function.Periodic (fun alpha => ell alpha beta)
      (2 * Real.pi)) (n : Fin 3 → ℤ) :
    rawFourierCoefficient (diagonalRawCarrier p₂ ell) n =
      if n 0 = n 1 then
        intCharacter (-n 1) p₂ * carrierFourierCoefficient ell (n 1) (n 2)
      else 0 := by
  set G : ℝ → ℂ := fun alpha =>
    Estimates.torusIntegral fun beta : ℝ =>
      intCharacter (-n 2) beta * ell alpha beta with hG
  have hGper : Function.Periodic G (2 * Real.pi) := by
    intro alpha
    show (Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 2) beta * ell (alpha + 2 * Real.pi) beta) =
      Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 2) beta * ell alpha beta
    congr 1
    funext beta
    have hell := hper beta alpha
    simp only at hell
    rw [hell]
  have hstep : rawFourierCoefficient (diagonalRawCarrier p₂ ell) n =
      Estimates.torusIntegral fun r : ℝ =>
        Estimates.torusIntegral fun r' : ℝ =>
          intCharacter (-n 0) r * intCharacter (-n 1) r' *
            G (mixedAlpha p₂ r r') := by
    rw [rawFourierCoefficient]
    congr 1
    funext r
    congr 1
    funext r'
    rw [hG]
    rw [← torusIntegral_const_mul]
    congr 1
    funext beta
    rw [diagonalRawCarrier]
    ring
  rw [hstep, torusIntegral₂_character_comp_mixedAlpha p₂ (n 0) (n 1) G hGper]
  by_cases hn : n 0 = n 1
  · rw [if_pos hn, if_pos hn]
    congr 1
    rw [carrierFourierCoefficient, hG]
    congr 1
    funext alpha
    rw [← torusIntegral_const_mul]
    congr 1
    funext beta
    ring
  · rw [if_neg hn, if_neg hn]

section RawFourier

variable {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}

/-- The column-transformed raw coefficient. -/
private def colTransform (n : ℤ) (k : ℝ → ℝ → ℝ → ℂ) (t r' : ℝ) : ℂ :=
  Estimates.torusIntegral fun beta : ℝ => intCharacter (-n) beta * k t r' beta

private theorem torusBounded₂_colTransform (n : ℤ) (hk : TorusBoundedThree k) :
    TorusBoundedTwo (colTransform n k) := by
  have hchar : Measurable (intCharacter (-n)) := by
    unfold intCharacter
    fun_prop
  obtain ⟨hm, C, hC⟩ := hk
  have hmul : TorusBoundedThree fun t r' beta => intCharacter (-n) beta * k t r' beta := by
    refine ⟨(hchar.comp (measurable_snd.comp measurable_snd)).mul hm, C,
      fun t r' beta => ?_⟩
    rw [norm_mul, norm_intCharacter, one_mul]
    exact hC t r' beta
  exact hmul.integral_col

private theorem colTransform_periodic (n : ℤ)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (t : ℝ) : Function.Periodic (colTransform n k t) (2 * Real.pi) := by
  intro r'
  show (Estimates.torusIntegral fun beta : ℝ =>
      intCharacter (-n) beta * k t (r' + 2 * Real.pi) beta) =
    Estimates.torusIntegral fun beta : ℝ =>
      intCharacter (-n) beta * k t r' beta
  congr 1
  funext beta
  have h := hper t beta r'
  simp only at h
  rw [h]

/-- The coincident-row part of a raw coefficient has exactly the raw Fourier
coefficients on the diagonal. Together with
`rawFourierCoefficient_diagonalRawCarrier` this identifies
`rawDiagonalPart` with `I - Pi_3` and `rawOffDiagonalPart` with `Pi_3`. -/
theorem carrierFourierCoefficient_rawDiagonalPart (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (m n : ℤ) :
    carrierFourierCoefficient (rawDiagonalPart p₂ k) m n =
      intCharacter m p₂ * rawFourierCoefficient k ![m, m, n] := by
  classical
  obtain ⟨hm, C, hC⟩ := hk
  have hk' : TorusBoundedThree k := ⟨hm, C, hC⟩
  have hchar : ∀ j : ℤ, Measurable (intCharacter j) := by
    intro j
    unfold intCharacter
    fun_prop
  -- the shifted coefficient and its column transform
  have hshiftBdd : TorusBoundedThree fun t alpha beta =>
      intCharacter (-n) beta * k t (alpha - t + p₂) beta := by
    refine ⟨(hchar (-n)).comp (measurable_snd.comp measurable_snd) |>.mul
      (hm.comp (measurable_fst.prodMk
        ((((measurable_fst.comp measurable_snd).sub measurable_fst).add
          measurable_const).prodMk (measurable_snd.comp measurable_snd)))),
      C, fun t alpha beta => ?_⟩
    rw [norm_mul, norm_intCharacter, one_mul]
    exact hC t (alpha - t + p₂) beta
  set W : ℝ → ℝ → ℂ := fun t alpha =>
    Estimates.torusIntegral fun beta : ℝ =>
      intCharacter (-n) beta * k t (alpha - t + p₂) beta with hW
  have hWBdd : TorusBoundedTwo W := hshiftBdd.integral_col
  -- step 1: exchange the column integral with the fibre average
  have hstep1 : carrierFourierCoefficient (rawDiagonalPart p₂ k) m n =
      Estimates.torusIntegral fun alpha : ℝ =>
        Estimates.torusIntegral fun t : ℝ =>
          intCharacter (-m) alpha * W t alpha := by
    rw [carrierFourierCoefficient]
    congr 1
    funext alpha
    have hinnerSwap :
        (Estimates.torusIntegral fun beta : ℝ =>
            Estimates.torusIntegral fun t : ℝ =>
              intCharacter (-m) alpha * intCharacter (-n) beta *
                k t (alpha - t + p₂) beta) =
          Estimates.torusIntegral fun t : ℝ =>
            Estimates.torusIntegral fun beta : ℝ =>
              intCharacter (-m) alpha * intCharacter (-n) beta *
                k t (alpha - t + p₂) beta := by
      refine torusIntegral_swap (integrable_prod_torus_of_bound (C := C) ?_ ?_)
      · refine Measurable.aestronglyMeasurable ?_
        exact (measurable_const.mul
          ((hchar (-n)).comp measurable_fst)).mul
            (hm.comp (measurable_snd.prodMk
              (((measurable_const.sub measurable_snd).add
                measurable_const).prodMk measurable_fst)))
      · rintro ⟨beta, t⟩
        rw [Function.uncurry_apply_pair, norm_mul, norm_mul,
          norm_intCharacter, norm_intCharacter, one_mul, one_mul]
        exact hC t (alpha - t + p₂) beta
    rw [show (fun beta : ℝ => intCharacter (-m) alpha * intCharacter (-n) beta *
        rawDiagonalPart p₂ k alpha beta) =
        fun beta : ℝ => Estimates.torusIntegral fun t : ℝ =>
          intCharacter (-m) alpha * intCharacter (-n) beta *
            k t (alpha - t + p₂) beta by
      funext beta
      rw [rawDiagonalPart, ← torusIntegral_const_mul]]
    rw [hinnerSwap]
    congr 1
    funext t
    rw [hW, ← torusIntegral_const_mul]
    congr 1
    funext beta
    ring
  -- step 2: Fubini in the fibre and the row frequency
  have hstep2 :
      (Estimates.torusIntegral fun alpha : ℝ =>
          Estimates.torusIntegral fun t : ℝ =>
            intCharacter (-m) alpha * W t alpha) =
        Estimates.torusIntegral fun t : ℝ =>
          Estimates.torusIntegral fun alpha : ℝ =>
            intCharacter (-m) alpha * W t alpha := by
    obtain ⟨hWm, CW, hCW⟩ := hWBdd
    refine torusIntegral_swap (integrable_prod_torus_of_bound (C := CW) ?_ ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact ((hchar (-m)).comp measurable_fst).mul
        (hWm.comp (measurable_snd.prodMk measurable_fst))
    · rintro ⟨alpha, t⟩
      rw [Function.uncurry_apply_pair, norm_mul, norm_intCharacter, one_mul]
      exact hCW t alpha
  -- step 3: translation invariance along the fibre
  have hstep3 : ∀ t : ℝ,
      (Estimates.torusIntegral fun alpha : ℝ =>
          intCharacter (-m) alpha * W t alpha) =
        intCharacter m p₂ * intCharacter (-m) t *
          Estimates.torusIntegral fun r' : ℝ =>
            intCharacter (-m) r' * colTransform n k t r' := by
    intro t
    have hWper : Function.Periodic (W t) (2 * Real.pi) := by
      intro alpha
      show (Estimates.torusIntegral fun beta : ℝ =>
          intCharacter (-n) beta * k t (alpha + 2 * Real.pi - t + p₂) beta) =
        Estimates.torusIntegral fun beta : ℝ =>
          intCharacter (-n) beta * k t (alpha - t + p₂) beta
      congr 1
      funext beta
      rw [show alpha + 2 * Real.pi - t + p₂ = (alpha - t + p₂) + 2 * Real.pi by
        ring]
      have h := hper t beta (alpha - t + p₂)
      simp only at h
      rw [h]
    have hΨper : Function.Periodic
        (fun alpha : ℝ => intCharacter (-m) alpha * W t alpha)
        (2 * Real.pi) := by
      intro alpha
      dsimp only
      rw [intCharacter_periodic (-m) alpha, hWper alpha]
    rw [← torusIntegral_comp_add_right hΨper (t - p₂)]
    have hval : ∀ r' : ℝ,
        intCharacter (-m) (r' + (t - p₂)) * W t (r' + (t - p₂)) =
          intCharacter m p₂ * intCharacter (-m) t *
            (intCharacter (-m) r' * colTransform n k t r') := by
      intro r'
      have hWval : W t (r' + (t - p₂)) = colTransform n k t r' := by
        show (Estimates.torusIntegral fun beta : ℝ =>
            intCharacter (-n) beta * k t (r' + (t - p₂) - t + p₂) beta) =
          Estimates.torusIntegral fun beta : ℝ =>
            intCharacter (-n) beta * k t r' beta
        rw [show r' + (t - p₂) - t + p₂ = r' by ring]
      have hchar' : intCharacter (-m) (r' + (t - p₂)) =
          intCharacter (-m) r' * (intCharacter (-m) t * intCharacter m p₂) := by
        rw [show r' + (t - p₂) = r' + (t + -p₂) by ring, intCharacter_add_arg,
          intCharacter_add_arg]
        congr 2
        rw [intCharacter_neg_arg, neg_neg]
      rw [hWval, hchar']
      ring
    have hfun : (fun r' : ℝ =>
        (fun alpha : ℝ => intCharacter (-m) alpha * W t alpha) (r' + (t - p₂))) =
        fun r' : ℝ => intCharacter m p₂ * intCharacter (-m) t *
          (intCharacter (-m) r' * colTransform n k t r') := funext hval
    rw [hfun]
    exact torusIntegral_const_mul _ _
  rw [hstep1, hstep2]
  rw [show (fun t : ℝ => Estimates.torusIntegral fun alpha : ℝ =>
      intCharacter (-m) alpha * W t alpha) =
      fun t : ℝ => intCharacter m p₂ *
        (intCharacter (-m) t *
          Estimates.torusIntegral fun r' : ℝ =>
            intCharacter (-m) r' * colTransform n k t r') by
    funext t
    rw [hstep3 t]
    ring]
  rw [torusIntegral_const_mul]
  congr 1
  rw [rawFourierCoefficient]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have hinner : ∀ t r' : ℝ,
      intCharacter (-m) t * (intCharacter (-m) r' * colTransform n k t r') =
        Estimates.torusIntegral fun beta : ℝ =>
          intCharacter (-m) t * intCharacter (-m) r' * intCharacter (-n) beta *
            k t r' beta := by
    intro t r'
    have hpull := torusIntegral_const_mul
      (intCharacter (-m) t * intCharacter (-m) r')
      (fun beta : ℝ => intCharacter (-n) beta * k t r' beta)
    rw [colTransform, ← mul_assoc, ← hpull]
    congr 1
    funext beta
    ring
  congr 1
  funext t
  rw [← torusIntegral_const_mul (intCharacter (-m) t)
    (fun r' : ℝ => intCharacter (-m) r' * colTransform n k t r')]
  congr 1
  funext r'
  exact hinner t r'

theorem rawFourierCoefficient_sub {f g : ℝ → ℝ → ℝ → ℂ}
    (hf : TorusBoundedThree f) (hg : TorusBoundedThree g) (n : Fin 3 → ℤ) :
    rawFourierCoefficient (fun r r' b => f r r' b - g r r' b) n =
      rawFourierCoefficient f n - rawFourierCoefficient g n := by
  rw [rawFourierCoefficient, rawFourierCoefficient, rawFourierCoefficient,
    ← torusIntegral₃_sub (torusBounded₃_character_mul hf n)
      (torusBounded₃_character_mul hg n)]
  congr 1
  funext r
  congr 1
  funext r'
  congr 1
  funext b
  ring

/-- **`rawOffDiagonalPart` is the projection `Pi_3`.** Its Fourier
coefficients vanish on the coincident-row diagonal and agree with those of the
raw coefficient off it. This is what makes `rawDiagonalPart` the paper's
`ell = (I - Pi_3) ktilde` rather than a definition by fiat
(`manuscript.tex:1275-1279`). -/
theorem rawFourierCoefficient_rawOffDiagonalPart {p₂ : ℝ} {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (n : Fin 3 → ℤ) :
    rawFourierCoefficient (rawOffDiagonalPart p₂ k) n =
      if n 0 = n 1 then 0 else rawFourierCoefficient k n := by
  have hdiag : TorusBoundedThree (diagonalRawCarrier p₂ (rawDiagonalPart p₂ k)) :=
    (hk.rawDiagonalPart p₂).diagonalRawCarrier p₂
  have hsplit : rawFourierCoefficient (rawOffDiagonalPart p₂ k) n =
      rawFourierCoefficient k n -
        rawFourierCoefficient
          (diagonalRawCarrier p₂ (rawDiagonalPart p₂ k)) n :=
    rawFourierCoefficient_sub hk hdiag n
  have hcarrier := rawFourierCoefficient_diagonalRawCarrier p₂
    (rawDiagonalPart p₂ k) (rawDiagonalPart_periodic p₂ hper) n
  rw [hsplit, hcarrier]
  by_cases hn : n 0 = n 1
  · rw [if_pos hn, if_pos hn,
      carrierFourierCoefficient_rawDiagonalPart hk hper (n 1) (n 2),
      ← mul_assoc, intCharacter_add_index, neg_add_cancel,
      intCharacter_index_zero, one_mul]
    have hvec : (![n 1, n 1, n 2] : Fin 3 → ℤ) = n := by
      funext i
      fin_cases i <;> simp [hn]
    rw [hvec, sub_self]
  · rw [if_neg hn, if_neg hn, sub_zero]

end RawFourier

end

end Manhattan.Glue
