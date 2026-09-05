import Manhattan.Glue.LoweringClosure
import Manhattan.Glue.ProjectionDischarge

/-!
# The bridge from the concrete lowering formulas to the projection discharge

The first projection-error interface is discharged
(`Manhattan.Glue.rawProjectionDifferenceIdentification_of_lowering`) modulo one
named hypothesis, `Manhattan.Glue.ConcreteLoweringFormula`, carrying the two
Finset normalization constants of the type-`11` and type-`12` sectors.  This
file instantiates that hypothesis from the concrete lowering formulas (D2a),
(D2b) of `Manhattan.Glue.ConcreteLoweringFourier`, with

* `cTwoNorm = 1`  (the type-`112` and type-`11` normalizations are both `sqrt 2`
  and cancel), and
* `cMixNorm = sqrt 2`  (the type-`12` normalization is one).

The raw frequency coefficient is the ordered kernel written in the manuscript's
shifted variables `r = p₂ + s`, `r' = p₂ + s'`, `beta = p₁ + u`
(`manuscript.tex:797-814`).  Since the kernel is diagonal-free in its two row
indices, the coincident-row projection `Pi_3` acts trivially on it, which is why
`rawOffDiagonalPart` disappears from the two clauses.

**Domain restriction of (D2b)**.  That diagonal-freeness is a
genuine restriction, not a convenience: `Manhattan.Glue.loweringCoefficient_mixedPair`
establishes (28) only for diagonal-free kernels, so everything this file derives
from it inherits the hypothesis.  The frequency-side identities
`Manhattan.Glue.frequency_D2a` and `Manhattan.Glue.frequency_D2b` are themselves
UNCONDITIONAL.  The paper's actual competitor is not diagonal-free, so nothing
here reaches it; the mixed identity for the competitor is
`Manhattan.Glue.mixedFourierCoefficient_correction`, packaged as
`Manhattan.Glue.concreteLoweringFormula_correction_certified`
(`Manhattan/Glue/CorrectionLowering.lean`), and Lemma 5.3 for the competitor is
`Manhattan.Glue.lemma_distinct_correction` there.  Consequently
`Manhattan.Glue.lemma_distinct_shiftedRawCoefficient` below is vacuous as a
rendering of Lemma 5.3 and must not be sealed as one; its honest content is that `Pi_3` acts trivially
on diagonal-free kernels.

The missing bookkeeping step named in is
`twoRowFourierCoefficient_orderedFreqTwo_shift`: the two-row Walsh coefficient
at a `Manhattan.Type11Index` of a shifted degree-two frequency function is the
ordered kernel read at the increasing pair of row indices, times the shift
phase.

Paper: `manuscript.tex:793-840`, `manuscript.tex:1208-1219`,
`manuscript.tex:1274-1303`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

local instance loweringBridgePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ## The two character families agree -/

theorem lineCharacter_eq_intCharacter (n : ℤ) (x : ℝ) :
    lineCharacter n x = intCharacter n x := by
  rw [lineCharacter, intCharacter]
  congr 1
  push_cast
  ring

@[simp] theorem norm_lineCharacter (n : ℤ) (x : ℝ) : ‖lineCharacter n x‖ = 1 := by
  rw [lineCharacter_eq_intCharacter, norm_intCharacter]

theorem lineCharacter_periodic (n : ℤ) :
    Function.Periodic (lineCharacter n) (2 * Real.pi) := by
  intro x
  rw [lineCharacter_eq_intCharacter, lineCharacter_eq_intCharacter]
  exact intCharacter_periodic n x

/-- The shift identity used by the coincident-row computation. -/
theorem intCharacter_sub_mul_intCharacter_sub (n m : ℤ) (t a alpha : ℝ) :
    intCharacter n (t - a) * intCharacter m (alpha - t) =
      intCharacter n (-a) * intCharacter m alpha * intCharacter (n - m) t := by
  rw [intCharacter, intCharacter, intCharacter, intCharacter, intCharacter,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The shift identity used by the Fourier-coefficient computation. -/
theorem intCharacter_neg_mul_intCharacter_sub (n m : ℤ) (r a : ℝ) :
    intCharacter (-n) r * intCharacter m (r - a) =
      intCharacter (-m) a * intCharacter (m - n) r := by
  rw [intCharacter, intCharacter, intCharacter, intCharacter,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrableOn_const_mul_intCharacter (c : ℂ) (n : ℤ) :
    IntegrableOn (fun x : ℝ => c * intCharacter n x) Estimates.torus := by
  rw [Estimates.torus]
  apply Continuous.integrableOn_Ioc
  unfold intCharacter
  fun_prop

/-! ## The ordered kernel as a raw frequency coefficient -/

/-- The ordered type-`112` kernel written in the manuscript's shifted frequency
variables `r = p₂ + s`, `r' = p₂ + s'`, `beta = p₁ + u`. -/
def shiftedRawCoefficient (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (r r' beta : ℝ) : ℂ :=
  orderedFreqThree k (r - p 1) (r' - p 1) (beta - p 0)

theorem orderedFreqThree_eq_sum (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' u : ℝ) :
    orderedFreqThree k s s' u =
      ∑ t ∈ k.support,
        k t * lineCharacter t.1 s * lineCharacter t.2.1 s' * lineCharacter t.2.2 u := by
  rw [orderedFreqThree, Finsupp.sum]

theorem norm_orderedFreqThree_le (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' u : ℝ) :
    ‖orderedFreqThree k s s' u‖ ≤ ∑ t ∈ k.support, ‖k t‖ := by
  rw [orderedFreqThree_eq_sum]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
  rw [norm_mul, norm_mul, norm_mul, norm_lineCharacter, norm_lineCharacter,
    norm_lineCharacter]
  ring

theorem continuous_orderedFreqThree (k : (ℤ × ℤ × ℤ) →₀ ℂ) :
    Continuous fun z : ℝ × ℝ × ℝ => orderedFreqThree k z.1 z.2.1 z.2.2 := by
  simp only [orderedFreqThree_eq_sum]
  refine continuous_finset_sum _ fun t _ => ?_
  unfold lineCharacter
  fun_prop

theorem orderedFreqThree_periodic_row (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s u : ℝ) :
    Function.Periodic (fun s' => orderedFreqThree k s s' u) (2 * Real.pi) := by
  intro s'
  simp only [orderedFreqThree_eq_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [lineCharacter_periodic t.2.1 s']

theorem orderedFreqThree_periodic_col (k : (ℤ × ℤ × ℤ) →₀ ℂ) (s s' : ℝ) :
    Function.Periodic (fun u => orderedFreqThree k s s' u) (2 * Real.pi) := by
  intro u
  simp only [orderedFreqThree_eq_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [lineCharacter_periodic t.2.2 u]

theorem torusBounded₃_shiftedRawCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) : TorusBoundedThree (shiftedRawCoefficient p k) := by
  refine ⟨?_, ∑ t ∈ k.support, ‖k t‖, fun r r' beta => ?_⟩
  · have hcont : Continuous fun z : ℝ × ℝ × ℝ =>
        shiftedRawCoefficient p k z.1 z.2.1 z.2.2 := by
      unfold shiftedRawCoefficient
      simp only [orderedFreqThree_eq_sum]
      refine continuous_finset_sum _ fun t _ => ?_
      unfold lineCharacter
      fun_prop
    exact hcont.measurable
  · exact norm_orderedFreqThree_le k _ _ _

theorem shiftedRawCoefficient_periodic (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (r beta : ℝ) :
    Function.Periodic (fun r' => shiftedRawCoefficient p k r r' beta)
      (2 * Real.pi) := by
  intro r'
  show orderedFreqThree k (r - p 1) (r' + 2 * Real.pi - p 1) (beta - p 0) =
    orderedFreqThree k (r - p 1) (r' - p 1) (beta - p 0)
  rw [show r' + 2 * Real.pi - p 1 = (r' - p 1) + 2 * Real.pi by ring]
  exact orderedFreqThree_periodic_row k (r - p 1) (beta - p 0) (r' - p 1)

/-! ## The coincident-row part of a diagonal-free kernel vanishes -/

/-- A kernel that vanishes on coincident row indices has no coincident-row
part: in the frequency picture the fibre average is zero.  This is the exact
statement that `Pi_3` acts as the identity on such a kernel. -/
theorem rawDiagonalPart_shiftedRawCoefficient (p : Fin 2 → ℝ)
    {k : (ℤ × ℤ × ℤ) →₀ ℂ} (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    rawDiagonalPart (p 1) (shiftedRawCoefficient p k) = 0 := by
  funext alpha beta
  rw [rawDiagonalPart]
  have hint : (fun t : ℝ => shiftedRawCoefficient p k t (alpha - t + p 1) beta) =
      fun t : ℝ => ∑ τ ∈ k.support,
        (k τ * intCharacter τ.1 (-(p 1)) * intCharacter τ.2.1 alpha *
            intCharacter τ.2.2 (beta - p 0)) *
          intCharacter (τ.1 - τ.2.1) t := by
    funext t
    rw [shiftedRawCoefficient,
      show alpha - t + p 1 - p 1 = alpha - t by ring, orderedFreqThree_eq_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lineCharacter_eq_intCharacter, lineCharacter_eq_intCharacter,
      lineCharacter_eq_intCharacter]
    rw [show k τ * intCharacter τ.1 (t - p 1) * intCharacter τ.2.1 (alpha - t) *
        intCharacter τ.2.2 (beta - p 0) =
        (k τ * intCharacter τ.2.2 (beta - p 0)) *
          (intCharacter τ.1 (t - p 1) * intCharacter τ.2.1 (alpha - t)) by ring,
      intCharacter_sub_mul_intCharacter_sub]
    ring
  rw [hint, torusIntegral_finset_sum _ _
    (fun τ _ => integrableOn_const_mul_intCharacter _ _)]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [torusIntegral_const_mul, torusIntegral_intCharacter']
  by_cases hτ : τ.1 - τ.2.1 = 0
  · have heq : τ.1 = τ.2.1 := by omega
    have hzero : k τ = 0 := by
      have : τ = (τ.1, τ.1, τ.2.2) := by
        rw [Prod.ext_iff, Prod.ext_iff]
        exact ⟨rfl, heq.symm, rfl⟩
      rw [this, hdiag]
    rw [hzero]
    simp
  · rw [if_neg hτ]
    simp

theorem rawOffDiagonalPart_shiftedRawCoefficient (p : Fin 2 → ℝ)
    {k : (ℤ × ℤ × ℤ) →₀ ℂ} (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    rawOffDiagonalPart (p 1) (shiftedRawCoefficient p k) =
      shiftedRawCoefficient p k := by
  funext r r' beta
  rw [rawOffDiagonalPart, diagonalRawCarrier,
    rawDiagonalPart_shiftedRawCoefficient p hdiag]
  simp

/-! ## (D2a) and (D2b) in the shifted raw variables -/

/-- The raw two-row lowering symbol of the shifted ordered kernel is the
shifted degree-two frequency function of the two-row lowered kernel.  This is
(D2a) after the change of variables `r = p₂ + s`, `r' = p₂ + s'`. -/
theorem rawD2StarTwoRow_shiftedRawCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (r r' : ℝ) :
    rawD2StarTwoRow (p 1) (shiftedRawCoefficient p k) r r' =
      orderedFreqTwo (twoRowLoweredKernel p k) (r - p 1) (r' - p 1) := by
  have hcol : (Estimates.torusIntegral fun beta =>
        shiftedRawCoefficient p k r r' beta) =
      Estimates.torusIntegral
        (fun u => orderedFreqThree k (r - p 1) (r' - p 1) u) := by
    have h := torusIntegral_comp_add_right
      (f := fun u => orderedFreqThree k (r - p 1) (r' - p 1) u)
      (orderedFreqThree_periodic_col k (r - p 1) (r' - p 1)) (-(p 0))
    simpa [shiftedRawCoefficient, sub_eq_add_neg] using h
  rw [frequency_D2a, rawD2StarTwoRow, mixedAlpha, hcol,
    show p 1 + (r - p 1) + (r' - p 1) = r + r' - p 1 from by ring]
  ring

/-- The raw mixed lowering symbol of the shifted ordered kernel, times the
type-`112` normalization `sqrt 2`, is the shifted degree-two frequency function
of the mixed lowered kernel.  This is (D2b) after the change of variables
`r = p₂ + s`, `beta = p₁ + u`; the `sqrt 2` is the ratio of the type-`112`
normalization to the type-`12` normalization. -/
theorem rawD2StarMixed_shiftedRawCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (r beta : ℝ) :
    ((Real.sqrt 2 : ℝ) : ℂ) *
        rawD2StarMixed (shiftedRawCoefficient p k) r beta =
      orderedFreqTwo (mixedLoweredKernel p k) (r - p 1) (beta - p 0) := by
  have hrow : (Estimates.torusIntegral fun r' =>
        shiftedRawCoefficient p k r r' beta) =
      Estimates.torusIntegral
        (fun s' => orderedFreqThree k (r - p 1) s' (beta - p 0)) := by
    have h := torusIntegral_comp_add_right
      (f := fun s' => orderedFreqThree k (r - p 1) s' (beta - p 0))
      (orderedFreqThree_periodic_row k (r - p 1) (beta - p 0)) (-(p 1))
    simpa [shiftedRawCoefficient, sub_eq_add_neg] using h
  rw [frequency_D2b, rawD2StarMixed, hrow,
    show p 0 + (beta - p 0) = beta from by ring]
  ring

/-! ## The two-row Walsh coefficient of a shifted degree-two symbol -/

/-- **The two-row bridge.**  Reading a
shifted degree-two frequency function at a genuine two-element row index is
reading its ordered kernel at the increasing pair of row indices, times the
phase of the frequency shift.  This is the passage from
`orderedFreqTwo` to the `Manhattan.Type11Index` Walsh coefficient. -/
theorem twoRowFourierCoefficient_orderedFreqTwo_shift (a : ℝ)
    (v : (ℤ × ℤ) →₀ ℂ) (T : Type11Index) :
    twoRowFourierCoefficient (fun r r' => orderedFreqTwo v (r - a) (r' - a)) T =
      intCharacter (-(type11RawIndex T 0 + type11RawIndex T 1)) a *
        v (type11RawIndex T 0, type11RawIndex T 1) := by
  set n₀ := type11RawIndex T 0 with hn₀
  set n₁ := type11RawIndex T 1 with hn₁
  have hsum : ∀ r r' : ℝ,
      intCharacter (-n₀) r * intCharacter (-n₁) r' *
          orderedFreqTwo v (r - a) (r' - a) =
        ∑ q ∈ v.support,
          (v q * intCharacter (-q.1) a * intCharacter (-q.2) a *
              intCharacter (q.1 - n₀) r) * intCharacter (q.2 - n₁) r' := by
    intro r r'
    rw [orderedFreqTwo, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lineCharacter_eq_intCharacter, lineCharacter_eq_intCharacter,
      show intCharacter (-n₀) r * intCharacter (-n₁) r' *
          (v q * intCharacter q.1 (r - a) * intCharacter q.2 (r' - a)) =
          v q * (intCharacter (-n₀) r * intCharacter q.1 (r - a)) *
            (intCharacter (-n₁) r' * intCharacter q.2 (r' - a)) from by ring,
      intCharacter_neg_mul_intCharacter_sub,
      intCharacter_neg_mul_intCharacter_sub]
    ring
  rw [twoRowFourierCoefficient]
  have hinner : ∀ r : ℝ, (Estimates.torusIntegral fun r' =>
        intCharacter (-n₀) r * intCharacter (-n₁) r' *
          orderedFreqTwo v (r - a) (r' - a)) =
      ∑ q ∈ v.support,
        (v q * intCharacter (-q.1) a * intCharacter (-q.2) a *
            (if q.2 - n₁ = 0 then 1 else 0)) * intCharacter (q.1 - n₀) r := by
    intro r
    rw [show (fun r' : ℝ => intCharacter (-n₀) r * intCharacter (-n₁) r' *
        orderedFreqTwo v (r - a) (r' - a)) =
        fun r' : ℝ => ∑ q ∈ v.support,
          (v q * intCharacter (-q.1) a * intCharacter (-q.2) a *
              intCharacter (q.1 - n₀) r) * intCharacter (q.2 - n₁) r' from
        funext fun r' => hsum r r',
      torusIntegral_finset_sum _ _
        (fun q _ => integrableOn_const_mul_intCharacter _ _)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [torusIntegral_const_mul, torusIntegral_intCharacter']
    ring
  rw [show (fun r : ℝ => Estimates.torusIntegral fun r' =>
      intCharacter (-n₀) r * intCharacter (-n₁) r' *
        orderedFreqTwo v (r - a) (r' - a)) =
      fun r : ℝ => ∑ q ∈ v.support,
        (v q * intCharacter (-q.1) a * intCharacter (-q.2) a *
            (if q.2 - n₁ = 0 then 1 else 0)) * intCharacter (q.1 - n₀) r from
      funext hinner,
    torusIntegral_finset_sum _ _
      (fun q _ => integrableOn_const_mul_intCharacter _ _)]
  have hchar : intCharacter (-n₀) a * intCharacter (-n₁) a =
      intCharacter (-(n₀ + n₁)) a := by
    rw [intCharacter_add_index]
    congr 1
    ring
  have hterm : ∀ q ∈ v.support,
      (Estimates.torusIntegral fun x : ℝ =>
        (v q * intCharacter (-q.1) a * intCharacter (-q.2) a *
            (if q.2 - n₁ = 0 then 1 else 0)) * intCharacter (q.1 - n₀) x) =
      if q = (n₀, n₁) then
        intCharacter (-(n₀ + n₁)) a * v (n₀, n₁) else 0 := by
    intro q _
    rw [torusIntegral_const_mul, torusIntegral_intCharacter']
    by_cases h₀ : q.1 - n₀ = 0
    · by_cases h₁ : q.2 - n₁ = 0
      · have e0 : q.1 = n₀ := by omega
        have e1 : q.2 = n₁ := by omega
        have hq : q = (n₀, n₁) := by
          rw [Prod.ext_iff]
          exact ⟨e0, e1⟩
        rw [if_pos h₀, if_pos h₁, if_pos hq, e0, e1,
          show v q = v (n₀, n₁) from by rw [hq]]
        linear_combination (v (n₀, n₁)) * hchar
      · rw [if_neg h₁, if_neg (fun hq : q = (n₀, n₁) => h₁ (by rw [hq]; simp))]
        ring
    · rw [if_neg h₀, if_neg (fun hq : q = (n₀, n₁) => h₀ (by rw [hq]; simp))]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' v.support (n₀, n₁)
    (fun _ => intCharacter (-(n₀ + n₁)) a * v (n₀, n₁))]
  by_cases hmem : (n₀, n₁) ∈ v.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem]
    ring

/-! ## Instantiation of `ConcreteLoweringFormula` -/

/-- The two-row Walsh coefficient of `D₂*` on the shifted ordered kernel. -/
def shiftedTwoRowCoefficient (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (T : Type11Index) : ℂ :=
  intCharacter (-(type11RawIndex T 0 + type11RawIndex T 1)) (p 1) *
    twoRowLoweredKernel p k (type11RawIndex T 0, type11RawIndex T 1)

/-- The mixed component of `D₂*` on the shifted ordered kernel. -/
def shiftedMixedCoefficient (p : Fin 2 → ℝ) (k : (ℤ × ℤ × ℤ) →₀ ℂ)
    (r beta : ℝ) : ℂ :=
  orderedFreqTwo (mixedLoweredKernel p k) (r - p 1) (beta - p 0)

/-- **The concrete lowering formula, instantiated.**  For a diagonal-free
ordered type-`112` kernel the shifted raw coefficient satisfies s
`ConcreteLoweringFormula` with `cTwoNorm = 1` and `cMixNorm = sqrt 2`. -/
theorem concreteLoweringFormula_shiftedRawCoefficient (p : Fin 2 → ℝ)
    {k : (ℤ × ℤ × ℤ) →₀ ℂ} (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    ConcreteLoweringFormula 1 ((Real.sqrt 2 : ℝ) : ℂ) (p 1)
      (shiftedRawCoefficient p k) (shiftedTwoRowCoefficient p k)
      (shiftedMixedCoefficient p k) := by
  constructor
  · intro T
    rw [one_mul, rawOffDiagonalPart_shiftedRawCoefficient p hdiag,
      show rawD2StarTwoRow (p 1) (shiftedRawCoefficient p k) =
        fun r r' => orderedFreqTwo (twoRowLoweredKernel p k) (r - p 1) (r' - p 1) from
        funext fun r => funext fun r' =>
          rawD2StarTwoRow_shiftedRawCoefficient p k r r',
      twoRowFourierCoefficient_orderedFreqTwo_shift, shiftedTwoRowCoefficient]
  · intro r beta
    rw [rawOffDiagonalPart_shiftedRawCoefficient p hdiag]
    exact (rawD2StarMixed_shiftedRawCoefficient p k r beta).symm

/-! ## The instantiating data is the concrete Walsh coefficient -/

/-- The two-row datum fed to `ConcreteLoweringFormula` is the genuine Walsh
coefficient of `D₂*` at the two-row Finset index, up to the shift phase and the
type-`11` Finset normalization `sqrt 2`.  Nothing is defined by fiat. -/
theorem shiftedTwoRowCoefficient_eq_loweringCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (T : Type11Index) :
    ((Real.sqrt 2 : ℝ) : ℂ) * shiftedTwoRowCoefficient p k T =
      intCharacter (-(type11RawIndex T 0 + type11RawIndex T 1)) (p 1) *
        loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k)) T.1 := by
  rw [← rowPairFinset_type11RawIndex T,
    loweringCoefficient_rowPair_eq_kernel p k hsymm (type11RawIndex_ne T),
    shiftedTwoRowCoefficient]
  ring

/-- The mixed datum fed to `ConcreteLoweringFormula` has the genuine Walsh
coefficients of `D₂*` at the mixed Finset indices as its Fourier coefficients:
`Manhattan.Glue.loweringCoefficient_mixedPair_eq_kernel` identifies
`mixedLoweredKernel` with those coefficients, and the type-`12` normalization is
one. -/
theorem mixedLoweredKernel_eq_loweringCoefficient (p : Fin 2 → ℝ)
    (k : (ℤ × ℤ × ℤ) →₀ ℂ) (hsymm : ∀ a b c : ℤ, k (b, a, c) = k (a, b, c))
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) (m n : ℤ) :
    mixedLoweredKernel p k (m, n) =
      loweringCoefficient p (walshSynthesis (type112FinsetCoefficient k))
        (mixedPairFinset (m, n)) :=
  (loweringCoefficient_mixedPair_eq_kernel p k hsymm hdiag m n).symm

/-! ## The two projection consequences, unconditional -/

/-- **Interface (a) of `Manhattan.Glue.ProjectionError`, unconditional.**  The
raw/projected lowering difference of the shifted ordered kernel is the
projection-error carrier of its coincident-row part. -/
theorem rawProjectionDifferenceIdentification_shiftedRawCoefficient
    (p : Fin 2 → ℝ) {k : (ℤ × ℤ × ℤ) →₀ ℂ} (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    RawProjectionDifferenceIdentification
      (rawProjectionDifference 1 ((Real.sqrt 2 : ℝ) : ℂ) (p 1)
        (shiftedRawCoefficient p k) (shiftedTwoRowCoefficient p k)
        (shiftedMixedCoefficient p k))
      (rawDiagonalPart (p 1)
        (scaleRaw ((Real.sqrt 2 : ℝ) : ℂ) (shiftedRawCoefficient p k))) :=
  rawProjectionDifferenceIdentification_of_lowering
    (torusBounded₃_shiftedRawCoefficient p k)
    (shiftedRawCoefficient_periodic p k)
    (concreteLoweringFormula_shiftedRawCoefficient p hdiag)

/-- **Π₃ acts trivially on diagonal-free kernels.**  NOT a rendering of Lemma 5.3
(`manuscript.tex:1212-1221`), despite the shape of the conclusion: the
hypothesis `hdiag` makes the statement vacuous as such.  Under `hdiag`,
`rawDiagonalPart_shiftedRawCoefficient` forces the coincident-row carrier to
zero, so the quantitative clause reads `0 ≤ 2 * energy` and the qualitative
clause is definitional.  Lemma 5.3 is precisely about a `k̃` WITH coincident
rows, so this must never be sealed or cited as Lemma 5.3.

Lemma 5.3 itself is `Manhattan.Glue.lemma_distinct_of_concreteLowering`, which
is not vacuous, and for the paper's actual competitor it is
`Manhattan.Glue.lemma_distinct_correction` and
`Manhattan.Glue.lemma_distinct_correction_sigmaEnergy`
(`Manhattan/Glue/CorrectionLowering.lean`), both with no diagonal-freeness
hypothesis.  The universal constant here is `‖sqrt 2‖² = 2`. -/
theorem lemma_distinct_shiftedRawCoefficient {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) {k : (ℤ × ℤ × ℤ) →₀ ℂ}
    (hdiag : ∀ a c : ℤ, k (a, a, c) = 0) :
    (rawProjectionDifference 1 ((Real.sqrt 2 : ℝ) : ℂ) (p 1)
        (shiftedRawCoefficient p k) (shiftedTwoRowCoefficient p k)
        (shiftedMixedCoefficient p k)).twoRow = 0 ∧
      projectionErrorHMinusSq q
          (rawDiagonalPart (p 1)
            (scaleRaw ((Real.sqrt 2 : ℝ) : ℂ) (shiftedRawCoefficient p k))) ≤
        ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 *
          rawMultiplierEnergy 40 q (p 1) (shiftedRawCoefficient p k) :=
  lemma_distinct_of_concreteLowering hlambda
    (torusBounded₃_shiftedRawCoefficient p k)
    (shiftedRawCoefficient_periodic p k)
    (concreteLoweringFormula_shiftedRawCoefficient p hdiag)

/-- The Lemma 5.3 constant of the manuscript, evaluated: `‖sqrt 2‖² = 2`. -/
theorem normSq_mixedNormalization : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

end

end Manhattan.Glue
