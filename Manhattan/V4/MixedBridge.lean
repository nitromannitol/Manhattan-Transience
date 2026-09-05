import Manhattan.V4.OperatorEstimate
import Manhattan.Glue.CorrectionLowering
import Manhattan.Glue.SummandThreeMixedFourier

/-!
# Version 4, the degree-two dual form at the parity kernel

`Manhattan.Glue.mixedFourierCoefficient_correction` identifies the raw mixed
lowering symbol with the genuine mixed Walsh coefficient of `D₂*`, but only for
the OLD competitor `Manhattan.Estimates.correctionCoefficient`.  This file
supplies the general raw-to-Walsh bridge and instantiates it at the Version 4
parity kernel `Manhattan.V4.parityKernel`.

The chain is

* `mFourierCoeff_rawL2` -- the missing `L²` Fourier bridge: the abstract
  `UnitAddTorus.mFourierCoeff` of `Manhattan.V4.rawL2` is the iterated
  normalized torus integral `Manhattan.Glue.rawFourierCoefficient` of the
  formula.  This is the general form of
  `Manhattan.Glue.mFourierCoeff_rawCorrection`, whose proof is the template.
* `type112CoefficientAt_rawShiftTwist_pinned` -- the index bookkeeping at a
  pinned mixed triple `(m, 0, j)`.  At `m = 0` that Finset has two elements, is
  not a type-`112` index, and the concrete `D₂*` reads it as zero; off `m = 0`
  the competitor stores the raw coefficient at the ordered representative
  `![min m 0, max m 0, j]`, which is why the **symmetry** hypothesis `hsymm` is
  needed (the correction had it from
  `Manhattan.Estimates.correctionCoefficient_swap`; the parity kernel has it
  from `Manhattan.V4.parityKernelReal_swap`).
* `mixedFourierCoefficient_rawOffDiagonalPart` -- **the bridge.**  Both sides
  drop the coincident-row term at `m = 0`: the concrete side because
  `Manhattan.Glue.type112DStarMixed_eq` reads its input at
  `tripleToFinset (m, 0, n ± 1)`, the raw side because
  `Manhattan.Glue.rawFourierCoefficient_rawOffDiagonalPart` kills the
  coincident-row Fourier coefficients of `Π₃`.  Off the diagonal the two sides
  agree up to the unimodular `(shift)` phase
  `e^{-i(m p₂ + n p₁)}`, and by nothing else.
* `mixedFourierCoefficient_parityKernel`, `type112DStarMixed_parityKernel` --
  the bridge at the Version 4 kernel, composed with (P2)
  `Manhattan.V4.rawD2StarMixed_offDiagonalPart`.
* `type12FreqFun_parityMixed`, `hMinusEnergy_parityMixed`,
  `hMinusEnergy_parityMixed_density` -- the degree-two dual form itself.

## The normalization, stated explicitly

`Manhattan.Glue.rawD2StarMixed` is `-i sin β ∫ k dm(r')`, with **no** `√2`;
the manuscript's (D2b) carries one.  The formalization follows
the Version 4 argument literally and puts the `(√2)⁻¹` **into the
kernel**: `Manhattan.V4.parityKernel = i sin β (v + v')/(√2 M)`.  This file
keeps that convention, so

    (D₂* Π₃ K)₁₂ = (√2)⁻¹ σ v     (`Manhattan.V4.rawD2StarMixed_offDiagonalPart`)
    ∫ M |K|²     = ∫ σ v²         (`Manhattan.V4.evenMajorantEnergy_parityKernel`)

and the mixed symbol carried by `Manhattan.V4.parityMixedSymbol` is
`(√2)⁻¹ σ v`, **not** `σ v`.  The square of that constant is the `2⁻¹` in
`hMinusEnergy_parityMixed_density`.  Both factors are exhibited as strict
inequalities in `Manhattan/V4/MixedBridgeWitnesses.lean`, so neither can be a
silently doubled or halved constant.

Paper: `manuscript.tex:793-840`, `manuscript.tex:1274-1303`.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Manhattan.V4

local instance (p : Prop) : Decidable p := Classical.propDecidable p

attribute [local instance] Real.fact_zero_lt_one

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The `L²` Fourier bridge for a general raw kernel -/

/-- **The Fourier bridge.**  The three-dimensional Fourier coefficients of a
bounded measurable raw kernel, taken on the abstract frequency torus where the
competitor's `ℓ²` coefficient lives, are the iterated normalized torus
integrals of the formula.  This is
`Manhattan.Glue.mFourierCoeff_rawCorrection` with the explicit correction
replaced by an arbitrary `Manhattan.Glue.TorusBoundedThree` kernel. -/
theorem mFourierCoeff_rawL2 {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k)
    (n : Manhattan.RawType112Index) :
    UnitAddTorus.mFourierCoeff ((rawL2 hk : UnitAddTorus (Fin 3) → ℂ)) n =
      Glue.rawFourierCoefficient k n := by
  classical
  set F : ℝ → ℝ → ℝ → ℂ := fun r r' b =>
    Glue.intCharacter (-n 0) r * Glue.intCharacter (-n 1) r' *
      Glue.intCharacter (-n 2) b * k r r' b with hFdef
  have hFB : Glue.TorusBoundedThree F := Glue.torusBounded₃_character_mul hk n
  have hcoeff : UnitAddTorus.mFourierCoeff ((rawL2 hk : UnitAddTorus (Fin 3) → ℂ)) n
      = ∫ x : UnitAddTorus (Fin 3),
          F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
            (Manhattan.unitTorusAngle (x 2)) := by
    rw [UnitAddTorus.mFourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [(rawTorusFun_memLp hk).coeFn_toLp] with x hx
    have hx' : (rawL2 hk : UnitAddTorus (Fin 3) → ℂ) x = rawTorusFun k x := hx
    rw [hx', smul_eq_mul, Glue.mFourier_eq_exp_angle, hFdef]
    show _ = Glue.intCharacter (-n 0) _ * Glue.intCharacter (-n 1) _ *
      Glue.intCharacter (-n 2) _ * _
    rw [rawTorusFun]
    congr 1
    rw [Glue.intCharacter, Glue.intCharacter, Glue.intCharacter, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [Fin.sum_univ_three]
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [hcoeff, Glue.integral_unitTorus_three_complex hFB]
  rfl

/-! ## The competitor coefficient at a pinned mixed index -/

/-- The projected raw coefficient at a Finset index: `Π₃` reads the raw Fourier
coefficient at the canonical ordered representative. -/
theorem rawType112Coefficients_apply {k : ℝ → ℝ → ℝ → ℂ} (hk : Glue.TorusBoundedThree k)
    (S : Manhattan.Type112Index) :
    rawType112Coefficients hk S =
      UnitAddTorus.mFourierCoeff ((rawL2 hk : UnitAddTorus (Fin 3) → ℂ))
        (Manhattan.type112RawIndex S) := by
  simp [rawType112Coefficients, UnitAddTorus.mFourierBasis_repr]

/-- **The competitor's degree-three coefficient at a pinned mixed index.**  Off
the coincident-row diagonal it is the raw Fourier coefficient carrying the
`(shift)` phase; on the diagonal `m = 0` the Finset index is not of type `112`
and the coefficient is read as zero.  The symmetry hypothesis is what lets the
ordered representative `![min m 0, max m 0, j]` be replaced by `![m, 0, j]`;
without it the two sides genuinely differ for `m > 0`. -/
theorem type112CoefficientAt_rawShiftTwist_pinned {k : ℝ → ℝ → ℝ → ℂ}
    (hk : Glue.TorusBoundedThree k) (hsymm : ∀ r r' b, k r r' b = k r' r b)
    (p₁ p₂ : ℝ) (m j : ℤ) :
    type112CoefficientAt
        (Manhattan.type112ShiftTwist p₁ p₂ (rawType112Coefficients hk))
        (Glue.tripleToFinset (m, 0, j)) =
      (if m = 0 then 0 else
        Complex.exp (Complex.I * (((m : ℝ) * p₂ + (j : ℝ) * p₁ : ℝ) : ℂ)) *
          Glue.rawFourierCoefficient k ![m, 0, j]) := by
  by_cases hm : m = 0
  · subst hm
    rw [type112CoefficientAt,
      dif_neg (Glue.not_isType112_tripleToFinset_diag 0 j), if_pos rfl]
  · have h112 : Manhattan.IsType112Index (Glue.tripleToFinset (m, 0, j)) :=
      Glue.isType112Index_tripleToFinset_pinned hm
    rw [type112CoefficientAt, dif_pos h112, if_neg hm,
      Manhattan.type112ShiftTwist_apply, rawType112Coefficients_apply,
      Glue.type112RawIndex_tripleToFinset_pinned hm h112,
      Manhattan.rawType112ShiftPhase_eq, mFourierCoeff_rawL2 hk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have hphase : ((min m 0 : ℤ) : ℝ) + ((max m 0 : ℤ) : ℝ) = (m : ℝ) := by
      push_cast
      rw [min_add_max]
      ring
    have hcoeff : Glue.rawFourierCoefficient k ![min m 0, max m 0, j] =
        Glue.rawFourierCoefficient k ![m, 0, j] := by
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le]
        exact Glue.rawFourierCoefficient_swap hk hsymm 0 m j
    rw [hcoeff, hphase]

/-! ## The bridge -/

/-- **The raw-to-Walsh mixed Fourier bridge.**  The `(m,n)` Fourier coefficient
of the raw mixed lowering symbol of `Π₃ k` is the genuine mixed Walsh
coefficient of `D₂* k_p`, read with the `(shift)` phase of
`manuscript.tex:791-800`.  This is
`Manhattan.Glue.mixedFourierCoefficient_correction` for an arbitrary bounded,
row-periodic, row-symmetric raw kernel, with
`Manhattan.shiftedCorrectionType112Coefficients` replaced by
`Manhattan.type112ShiftTwist ∘ Manhattan.V4.rawType112Coefficients`. -/
theorem mixedFourierCoefficient_rawOffDiagonalPart {k : ℝ → ℝ → ℝ → ℂ}
    (hk : Glue.TorusBoundedThree k)
    (hper : ∀ r beta, Function.Periodic (fun r' => k r r' beta) (2 * Real.pi))
    (hsymm : ∀ r r' b, k r r' b = k r' r b) (p : Fin 2 → ℝ) (m n : ℤ) :
    Glue.mixedFourierCoefficient
        (Glue.rawD2StarMixed (Glue.rawOffDiagonalPart (p 1) k)) m n =
      Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
        Manhattan.type112DStarMixed p
          (Manhattan.type112ShiftTwist (p 0) (p 1) (rawType112Coefficients hk))
          ⟨Glue.mixedPairFinset (m, n), Glue.isType12Index_mixedPairFinset m n⟩ := by
  have hoff : Glue.TorusBoundedThree (Glue.rawOffDiagonalPart (p 1) k) :=
    Glue.torusBounded₃_rawOffDiagonalPart hk (p 1)
  have hraw : ∀ j : ℤ,
      Glue.rawFourierCoefficient (Glue.rawOffDiagonalPart (p 1) k) ![m, 0, j] =
        (if m = 0 then 0 else Glue.rawFourierCoefficient k ![m, 0, j]) := by
    intro j
    rw [Glue.rawFourierCoefficient_rawOffDiagonalPart hk hper]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Glue.mixedFourierCoefficient_rawD2StarMixed hoff, hraw, hraw,
    Glue.type112DStarMixed_eq, type112CoefficientAt_rawShiftTwist_pinned hk hsymm,
    type112CoefficientAt_rawShiftTwist_pinned hk hsymm]
  by_cases hm : m = 0
  · simp only [if_pos hm]
    ring
  · simp only [if_neg hm]
    set A := Glue.rawFourierCoefficient k ![m, 0, n + 1] with hA
    set B := Glue.rawFourierCoefficient k ![m, 0, n - 1] with hB
    have hp1 : Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
        Complex.exp (-Complex.I * ((p 0 : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) = 1 := by
      have hcomb : Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
          Complex.exp (-Complex.I * ((p 0 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ((((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) =
          Complex.exp (Complex.I *
            (((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + -(p 0) +
              ((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0) : ℝ)) : ℂ)) := by
        rw [Glue.intCharacter, Glue.intCharacter, ← Complex.exp_add,
          ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hzero : ((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + -(p 0) +
          ((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0) : ℝ)) = 0 := by
        push_cast
        ring
      rw [hcomb, hzero]
      simp
    have hp2 : Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
        Complex.exp (Complex.I * ((p 0 : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) = 1 := by
      have hcomb : Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
          Complex.exp (Complex.I * ((p 0 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ((((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) =
          Complex.exp (Complex.I *
            (((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + p 0 +
              ((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0) : ℝ)) : ℂ)) := by
        rw [Glue.intCharacter, Glue.intCharacter, ← Complex.exp_add,
          ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hzero : ((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + p 0 +
          ((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0) : ℝ)) = 0 := by
        push_cast
        ring
      rw [hcomb, hzero]
      simp
    linear_combination (-(2 : ℂ)⁻¹ * A) * hp1 + ((2 : ℂ)⁻¹ * B) * hp2

/-! ## The V4 parity kernel -/

variable {kappa delta : ℝ}

theorem parityKernel_swap (v : ℝ → ℝ → ℝ) (r r' beta : ℝ) :
    parityKernel kappa delta v r r' beta = parityKernel kappa delta v r' r beta := by
  rw [parityKernel, parityKernel, parityKernelReal_swap]

/-- The mixed lowering symbol of the Version 4 competitor. -/
def parityMixedSymbol (kappa delta : ℝ) (v : ℝ → ℝ → ℝ) (r beta : ℝ) : ℂ :=
  (((Real.sqrt 2)⁻¹ * (paritySigma kappa delta r beta * v r beta) : ℝ) : ℂ)

theorem rawD2StarMixed_offDiagonalPart_eq (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (p₂ : ℝ) :
    Glue.rawD2StarMixed
        (Glue.rawOffDiagonalPart p₂ (parityKernel kappa delta v.toFun))
      = parityMixedSymbol kappa delta v.toFun := by
  funext r beta
  exact rawD2StarMixed_offDiagonalPart hkappa hdelta v p₂ r beta

/-- **The bridge at the Version 4 parity kernel.** -/
theorem mixedFourierCoefficient_parityKernel (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (p : Fin 2 → ℝ) (m n : ℤ) :
    Glue.mixedFourierCoefficient (parityMixedSymbol kappa delta v.toFun) m n =
      Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) *
        Manhattan.type112DStarMixed p
          (Manhattan.type112ShiftTwist (p 0) (p 1)
            (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))
          ⟨Glue.mixedPairFinset (m, n), Glue.isType12Index_mixedPairFinset m n⟩ := by
  rw [← rawD2StarMixed_offDiagonalPart_eq hkappa hdelta v (p 1)]
  exact mixedFourierCoefficient_rawOffDiagonalPart
    (torusBounded₃_parityKernel hkappa hdelta v)
    (fun r beta => parityKernel_periodic_row' v r beta)
    (fun r r' b => parityKernel_swap v.toFun r r' b) p m n

/-- **The genuine mixed Walsh coefficient of `D₂*` at the Version 4
competitor**, with the unimodular phase moved to the other side: it is the
`(m,n)` Fourier coefficient of `(√2)⁻¹ σ v`. -/
theorem type112DStarMixed_parityKernel (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (p : Fin 2 → ℝ) (m n : ℤ) :
    Manhattan.type112DStarMixed p
        (Manhattan.type112ShiftTwist (p 0) (p 1)
          (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))
        ⟨Glue.mixedPairFinset (m, n), Glue.isType12Index_mixedPairFinset m n⟩ =
      Glue.intCharacter m (p 1) * Glue.intCharacter n (p 0) *
        Glue.mixedFourierCoefficient (parityMixedSymbol kappa delta v.toFun) m n := by
  rw [mixedFourierCoefficient_parityKernel hkappa hdelta v p m n]
  have h1 : Glue.intCharacter m (p 1) * Glue.intCharacter (-m) (p 1) = 1 := by
    rw [Glue.intCharacter_add_index, add_neg_cancel, Glue.intCharacter_index_zero]
  have h2 : Glue.intCharacter n (p 0) * Glue.intCharacter (-n) (p 0) = 1 := by
    rw [Glue.intCharacter_add_index, add_neg_cancel, Glue.intCharacter_index_zero]
  set X := Manhattan.type112DStarMixed p
    (Manhattan.type112ShiftTwist (p 0) (p 1)
      (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))
    ⟨Glue.mixedPairFinset (m, n), Glue.isType12Index_mixedPairFinset m n⟩ with hX
  have hcollapse : Glue.intCharacter m (p 1) * Glue.intCharacter n (p 0) *
      (Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) * X) = X := by
    calc Glue.intCharacter m (p 1) * Glue.intCharacter n (p 0) *
        (Glue.intCharacter (-m) (p 1) * Glue.intCharacter (-n) (p 0) * X)
        = (Glue.intCharacter m (p 1) * Glue.intCharacter (-m) (p 1)) *
          ((Glue.intCharacter n (p 0) * Glue.intCharacter (-n) (p 0)) * X) := by ring
      _ = X := by rw [h1, h2, one_mul, one_mul]
  exact hcollapse.symm

/-! ## Passing to the shifted frequencies of `(shift)` -/

/-- Reading a doubly periodic mixed symbol at the shifted frequencies
`r = p₂ + s`, `beta = p₁ + u` multiplies its Fourier coefficients by the
unimodular shift phase. -/
theorem mixedFourierCoefficient_shift {F : ℝ → ℝ → ℂ}
    (hrow : ∀ beta, Function.Periodic (fun r => F r beta) (2 * Real.pi))
    (hcol : ∀ r, Function.Periodic (fun beta => F r beta) (2 * Real.pi))
    (c1 c2 : ℝ) (m n : ℤ) :
    Glue.mixedFourierCoefficient (fun s u => F (c1 + s) (c2 + u)) m n =
      Glue.intCharacter m c1 * Glue.intCharacter n c2 *
        Glue.mixedFourierCoefficient F m n := by
  have hem : Glue.intCharacter m c1 * Glue.intCharacter (-m) c1 = 1 := by
    rw [Glue.intCharacter_add_index, add_neg_cancel, Glue.intCharacter_index_zero]
  have hen : Glue.intCharacter n c2 * Glue.intCharacter (-n) c2 = 1 := by
    rw [Glue.intCharacter_add_index, add_neg_cancel, Glue.intCharacter_index_zero]
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun u => Glue.intCharacter (-n) u * F r (c2 + u))
        = Glue.intCharacter n c2 *
          Estimates.torusIntegral fun beta => Glue.intCharacter (-n) beta * F r beta := by
    intro r
    have hper : Function.Periodic
        (fun beta => Glue.intCharacter (-n) beta * F r beta) (2 * Real.pi) := by
      intro beta
      show Glue.intCharacter (-n) (beta + 2 * Real.pi) * F r (beta + 2 * Real.pi)
        = Glue.intCharacter (-n) beta * F r beta
      have h := hcol r beta
      simp only at h
      rw [Glue.intCharacter_periodic (-n) beta, h]
    have htr := Glue.torusIntegral_translate_periodic hper c2
    have hsplit : (Estimates.torusIntegral fun u =>
        Glue.intCharacter (-n) (c2 + u) * F r (c2 + u))
        = Glue.intCharacter (-n) c2 *
          Estimates.torusIntegral fun u => Glue.intCharacter (-n) u * F r (c2 + u) := by
      rw [← Glue.torusIntegral_const_mul]
      congr 1
      funext u
      rw [Glue.intCharacter_add_arg]
      ring
    rw [hsplit] at htr
    calc (Estimates.torusIntegral fun u => Glue.intCharacter (-n) u * F r (c2 + u))
        = Glue.intCharacter n c2 * (Glue.intCharacter (-n) c2 *
            Estimates.torusIntegral fun u => Glue.intCharacter (-n) u * F r (c2 + u)) := by
          rw [← mul_assoc, hen, one_mul]
      _ = _ := by rw [htr]
  have houter : Function.Periodic (fun r =>
      Glue.intCharacter (-m) r *
        Estimates.torusIntegral fun beta => Glue.intCharacter (-n) beta * F r beta)
      (2 * Real.pi) := by
    intro r
    show Glue.intCharacter (-m) (r + 2 * Real.pi) *
        (Estimates.torusIntegral fun beta =>
          Glue.intCharacter (-n) beta * F (r + 2 * Real.pi) beta)
      = Glue.intCharacter (-m) r *
        (Estimates.torusIntegral fun beta => Glue.intCharacter (-n) beta * F r beta)
    rw [Glue.intCharacter_periodic (-m) r]
    congr 2
    funext beta
    have h := hrow beta r
    simp only at h
    rw [h]
  rw [Glue.mixedFourierCoefficient, Glue.mixedFourierCoefficient]
  have hstep : ∀ s : ℝ,
      (Estimates.torusIntegral fun u =>
        Glue.intCharacter (-m) s * Glue.intCharacter (-n) u * F (c1 + s) (c2 + u))
        = Glue.intCharacter (-m) s * (Glue.intCharacter n c2 *
            Estimates.torusIntegral fun beta =>
              Glue.intCharacter (-n) beta * F (c1 + s) beta) := by
    intro s
    rw [← hinner (c1 + s), ← Glue.torusIntegral_const_mul]
    congr 1
    funext u
    ring
  simp only [hstep]
  have hpull : (Estimates.torusIntegral fun s =>
      Glue.intCharacter (-m) s * (Glue.intCharacter n c2 *
        Estimates.torusIntegral fun beta =>
          Glue.intCharacter (-n) beta * F (c1 + s) beta))
      = Glue.intCharacter n c2 * Estimates.torusIntegral fun s =>
          Glue.intCharacter (-m) s *
            Estimates.torusIntegral fun beta =>
              Glue.intCharacter (-n) beta * F (c1 + s) beta := by
    rw [← Glue.torusIntegral_const_mul]
    congr 1
    funext s
    ring
  rw [hpull]
  have htr := Glue.torusIntegral_translate_periodic houter c1
  have hsplit : (Estimates.torusIntegral fun s =>
      Glue.intCharacter (-m) (c1 + s) *
        Estimates.torusIntegral fun beta =>
          Glue.intCharacter (-n) beta * F (c1 + s) beta)
      = Glue.intCharacter (-m) c1 * Estimates.torusIntegral fun s =>
          Glue.intCharacter (-m) s *
            Estimates.torusIntegral fun beta =>
              Glue.intCharacter (-n) beta * F (c1 + s) beta := by
    rw [← Glue.torusIntegral_const_mul]
    congr 1
    funext s
    rw [Glue.intCharacter_add_arg]
    ring
  rw [hsplit] at htr
  calc Glue.intCharacter n c2 * (Estimates.torusIntegral fun s =>
        Glue.intCharacter (-m) s *
          (Estimates.torusIntegral fun beta =>
            Glue.intCharacter (-n) beta * F (c1 + s) beta))
      = Glue.intCharacter n c2 * (Glue.intCharacter m c1 *
          (Glue.intCharacter (-m) c1 * (Estimates.torusIntegral fun s =>
            Glue.intCharacter (-m) s *
              (Estimates.torusIntegral fun beta =>
                Glue.intCharacter (-n) beta * F (c1 + s) beta)))) := by
        rw [← mul_assoc (Glue.intCharacter m c1), hem, one_mul]
    _ = Glue.intCharacter m c1 * Glue.intCharacter n c2 *
          (Estimates.torusIntegral fun r => Glue.intCharacter (-m) r *
            (Estimates.torusIntegral fun beta =>
              Glue.intCharacter (-n) beta * F r beta)) := by
        rw [htr]; ring
    _ = Glue.intCharacter m c1 * Glue.intCharacter n c2 *
          (Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
            Glue.intCharacter (-m) r * Glue.intCharacter (-n) beta * F r beta) := by
        have hbody : ∀ r : ℝ,
            Glue.intCharacter (-m) r *
              (Estimates.torusIntegral fun beta => Glue.intCharacter (-n) beta * F r beta)
              = Estimates.torusIntegral fun beta =>
                  Glue.intCharacter (-m) r * Glue.intCharacter (-n) beta * F r beta := by
          intro r
          rw [← Glue.torusIntegral_const_mul]
          congr 1
          funext beta
          ring
        simp only [hbody]

/-! ## The degree-two dual form at the parity kernel -/

theorem parityJ_periodic_col (kappa delta r : ℝ) :
    Function.Periodic (fun beta => parityJ kappa delta r beta) (2 * Real.pi) := by
  intro beta
  show parityJ kappa delta r (beta + 2 * Real.pi) = parityJ kappa delta r beta
  unfold parityJ
  congr 1
  funext r'
  have h : evenMajorant kappa delta r r' (beta + 2 * Real.pi)
      = evenMajorant kappa delta r r' beta :=
    evenMajorant_periodic_col kappa delta r r' beta
  rw [h]

theorem paritySigma_periodic_col (kappa delta r : ℝ) :
    Function.Periodic (fun beta => paritySigma kappa delta r beta) (2 * Real.pi) := by
  intro beta
  show paritySigma kappa delta r (beta + 2 * Real.pi) = paritySigma kappa delta r beta
  have h : parityJ kappa delta r (beta + 2 * Real.pi) = parityJ kappa delta r beta :=
    parityJ_periodic_col kappa delta r beta
  rw [paritySigma, paritySigma, h, Real.sin_add_two_pi]

theorem paritySigma_le (hkappa : 0 < kappa) (hdelta : 0 < delta) (r beta : ℝ) :
    paritySigma kappa delta r beta ≤ (kappa * delta)⁻¹ := by
  have hJ := parityJ_le hkappa hdelta r beta
  have hJ0 := parityJ_nonneg hkappa hdelta r beta
  have hs : Real.sin beta ^ 2 ≤ 1 := by
    have := Real.abs_sin_le_one beta
    nlinarith [abs_nonneg (Real.sin beta), sq_abs (Real.sin beta)]
  have hs0 : (0:ℝ) ≤ Real.sin beta ^ 2 := sq_nonneg _
  rw [paritySigma]
  nlinarith

theorem parityMixedSymbol_periodic_row (v : ParityProfile) (beta : ℝ) :
    Function.Periodic (fun r => parityMixedSymbol kappa delta v.toFun r beta)
      (2 * Real.pi) := by
  intro r
  show parityMixedSymbol kappa delta v.toFun (r + 2 * Real.pi) beta
    = parityMixedSymbol kappa delta v.toFun r beta
  have hs : paritySigma kappa delta (r + 2 * Real.pi) beta
      = paritySigma kappa delta r beta := paritySigma_periodic_row kappa delta beta r
  have hv : v.toFun (r + 2 * Real.pi) beta = v.toFun r beta := v.periodic_row beta r
  rw [parityMixedSymbol, parityMixedSymbol, hs, hv]

theorem parityMixedSymbol_periodic_col (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    (r : ℝ) :
    Function.Periodic (fun beta => parityMixedSymbol kappa delta v.toFun r beta)
      (2 * Real.pi) := by
  intro beta
  show parityMixedSymbol kappa delta v.toFun r (beta + 2 * Real.pi)
    = parityMixedSymbol kappa delta v.toFun r beta
  have hs : paritySigma kappa delta r (beta + 2 * Real.pi)
      = paritySigma kappa delta r beta := paritySigma_periodic_col kappa delta r beta
  have hv := hvcol r beta
  simp only at hv
  rw [parityMixedSymbol, parityMixedSymbol, hs, hv]

theorem torusBounded₂_parityMixedSymbol (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) :
    Glue.TorusBoundedTwo (parityMixedSymbol kappa delta v.toFun) := by
  refine ⟨?_, (Real.sqrt 2)⁻¹ * ((kappa * delta)⁻¹ * v.bound), fun r beta => ?_⟩
  · unfold parityMixedSymbol
    exact Complex.measurable_ofReal.comp
      (measurable_const.mul ((paritySigma_measurable kappa delta).mul v.meas))
  · have hs0 := paritySigma_nonneg hkappa hdelta r beta
    have hsle := paritySigma_le hkappa hdelta r beta
    have hv := v.abs_le r beta
    have hvb := v.bound_nonneg
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hkd : (0:ℝ) < (kappa * delta)⁻¹ := by positivity
    rw [parityMixedSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_of_lt (by positivity : (0:ℝ) < (Real.sqrt 2)⁻¹)), abs_mul,
      abs_of_nonneg hs0]
    have hstep : paritySigma kappa delta r beta * |v.toFun r beta|
        ≤ (kappa * delta)⁻¹ * v.bound := by
      have h1 : paritySigma kappa delta r beta * |v.toFun r beta|
          ≤ (kappa * delta)⁻¹ * |v.toFun r beta| := by
        exact mul_le_mul_of_nonneg_right hsle (abs_nonneg _)
      have h2' : (kappa * delta)⁻¹ * |v.toFun r beta| ≤ (kappa * delta)⁻¹ * v.bound :=
        mul_le_mul_of_nonneg_left hv hkd.le
      linarith
    exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The shifted mixed symbol of the Version 4 competitor, as a bounded
two-variable carrier. -/
theorem torusBounded₂_parityShiftedSymbol (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile) (p : Fin 2 → ℝ) :
    Glue.TorusBoundedTwo fun s u =>
      parityMixedSymbol kappa delta v.toFun (p 1 + s) (p 0 + u) :=
  (torusBounded₂_parityMixedSymbol hkappa hdelta v).shift (p 1) (p 0)

/-- **The mixed degree-two frequency function of the Version 4 competitor.** -/
theorem type12FreqFun_parityMixed (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    (p : Fin 2 → ℝ) :
    Glue.type12FreqFun
        (Manhattan.type112DStarMixed p
          (Manhattan.type112ShiftTwist (p 0) (p 1)
            (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v))))
      = Glue.mixedAngleL2 (torusBounded₂_parityShiftedSymbol hkappa hdelta v p) := by
  refine Glue.type12FreqFun_eq_of_mFourierCoeff _ _ ?_ ?_
  · intro S
    have hS : S = ⟨Glue.mixedPairFinset
        (Glue.type12RawIndex S 0, Glue.type12RawIndex S 1),
        Glue.isType12Index_mixedPairFinset _ _⟩ :=
      Subtype.ext (Glue.mixedPairFinset_type12RawIndex S).symm
    rw [Glue.mFourierCoeff_mixedAngleL2]
    conv_rhs => rw [hS]
    rw [type112DStarMixed_parityKernel hkappa hdelta v p]
    exact mixedFourierCoefficient_shift
      (parityMixedSymbol_periodic_row v) (parityMixedSymbol_periodic_col v hvcol)
      (p 1) (p 0) (Glue.type12RawIndex S 0) (Glue.type12RawIndex S 1)
  · intro n hn
    obtain ⟨S, hS⟩ := Glue.type12RawIndex_surjective n
    exact absurd hS (hn S)

/-- **The degree-two dual form at the Version 4 parity kernel.** -/
theorem hMinusEnergy_parityMixed {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis
          (Manhattan.type112DStarMixed p
            (Manhattan.type112ShiftTwist (p 0) (p 1)
              (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))))
      = Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
          Estimates.mixedHMinusWeight q (p 1 + s) (p 0 + u) *
            ‖parityMixedSymbol kappa delta v.toFun (p 1 + s) (p 0 + u)‖ ^ 2 := by
  obtain ⟨hmeas, M, hM⟩ := torusBounded₂_parityShiftedSymbol hkappa hdelta v p
  refine Glue.hMinusEnergy_type12WalshSynthesis_torusIntegral hlam p _
    (fun s u => parityMixedSymbol kappa delta v.toFun (p 1 + s) (p 0 + u))
    hmeas hM ?_
  rw [type12FreqFun_parityMixed hkappa hdelta v hvcol p]
  exact Glue.coeFn_mixedAngleL2 (torusBounded₂_parityShiftedSymbol hkappa hdelta v p)

/-- The double translation of an iterated torus integral of a doubly periodic
real integrand. -/
theorem torusIntegral₂_shift {W : ℝ → ℝ → ℝ}
    (hrow : ∀ beta, Function.Periodic (fun r => W r beta) (2 * Real.pi))
    (hcol : ∀ r, Function.Periodic (fun beta => W r beta) (2 * Real.pi))
    (c1 c2 : ℝ) :
    (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u => W (c1 + s) (c2 + u))
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta => W r beta := by
  have hinner : ∀ s : ℝ,
      (Estimates.torusIntegral fun u => W (c1 + s) (c2 + u))
        = Estimates.torusIntegral fun beta => W (c1 + s) beta :=
    fun s => Glue.torusIntegral_translate_periodic (hcol (c1 + s)) c2
  simp only [hinner]
  have houter : Function.Periodic
      (fun r => Estimates.torusIntegral fun beta => W r beta) (2 * Real.pi) := by
    intro r
    show (Estimates.torusIntegral fun beta => W (r + 2 * Real.pi) beta)
      = Estimates.torusIntegral fun beta => W r beta
    congr 1
    funext beta
    have h := hrow beta r
    simp only at h
    exact h
  exact Glue.torusIntegral_translate_periodic houter c1

/-- **The degree-two dual form at the Version 4 parity kernel, as a density in
the unshifted frequencies.**  The dual energy of the mixed lowering vector is
exactly half of `∫∫ (sigma v)^2 / B`; the factor `1/2` is the square of the
`(sqrt 2)⁻¹` carried by `Manhattan.V4.parityKernel`. -/
theorem hMinusEnergy_parityMixed_density {q : Estimates.Parameters}
    (hlam : 0 < q.lambda) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (v : ParityProfile)
    (hvcol : ∀ r, Function.Periodic (fun beta => v.toFun r beta) (2 * Real.pi))
    (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type12WalshSynthesis
          (Manhattan.type112DStarMixed p
            (Manhattan.type112ShiftTwist (p 0) (p 1)
              (rawType112Coefficients (torusBounded₃_parityKernel hkappa hdelta v)))))
      = 2⁻¹ * Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
          (paritySigma kappa delta r beta * v.toFun r beta) ^ 2
            / Estimates.correctionB q r beta := by
  classical
  set W : ℝ → ℝ → ℝ := fun r beta =>
    Estimates.mixedHMinusWeight q r beta *
      ‖parityMixedSymbol kappa delta v.toFun r beta‖ ^ 2 with hW
  have hrow : ∀ beta : ℝ, Function.Periodic (fun r => W r beta) (2 * Real.pi) := by
    intro beta r
    have h1 : Estimates.mixedHMinusWeight q (r + 2 * Real.pi) beta
        = Estimates.mixedHMinusWeight q r beta :=
      Glue.mixedHMinusWeight_periodic_left q beta r
    have h2 : parityMixedSymbol kappa delta v.toFun (r + 2 * Real.pi) beta
        = parityMixedSymbol kappa delta v.toFun r beta :=
      parityMixedSymbol_periodic_row v beta r
    show W (r + 2 * Real.pi) beta = W r beta
    rw [hW]
    simp only
    rw [h1, h2]
  have hcol : ∀ r : ℝ, Function.Periodic (fun beta => W r beta) (2 * Real.pi) := by
    intro r beta
    have h1 : Estimates.mixedHMinusWeight q r (beta + 2 * Real.pi)
        = Estimates.mixedHMinusWeight q r beta :=
      Glue.mixedHMinusWeight_periodic_right q r beta
    have h2 : parityMixedSymbol kappa delta v.toFun r (beta + 2 * Real.pi)
        = parityMixedSymbol kappa delta v.toFun r beta :=
      parityMixedSymbol_periodic_col v hvcol r beta
    show W r (beta + 2 * Real.pi) = W r beta
    rw [hW]
    simp only
    rw [h1, h2]
  rw [hMinusEnergy_parityMixed hlam hkappa hdelta v hvcol p]
  have hshift : (Estimates.torusIntegral fun s => Estimates.torusIntegral fun u =>
      Estimates.mixedHMinusWeight q (p 1 + s) (p 0 + u) *
        ‖parityMixedSymbol kappa delta v.toFun (p 1 + s) (p 0 + u)‖ ^ 2)
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun beta =>
          W r beta := torusIntegral₂_shift hrow hcol (p 1) (p 0)
  rw [hshift]
  have hpoint : ∀ r beta : ℝ, W r beta =
      2⁻¹ * ((paritySigma kappa delta r beta * v.toFun r beta) ^ 2
        / Estimates.correctionB q r beta) := by
    intro r beta
    have hsq : (Real.sqrt 2)⁻¹ ^ 2 = 2⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hW]
    simp only [parityMixedSymbol, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Estimates.mixedHMinusWeight, Estimates.correctionB, mul_pow]
    rw [hsq]
    ring
  simp only [hpoint]
  have hpull : ∀ r : ℝ,
      (Estimates.torusIntegral fun beta =>
        2⁻¹ * ((paritySigma kappa delta r beta * v.toFun r beta) ^ 2
          / Estimates.correctionB q r beta))
        = 2⁻¹ * Estimates.torusIntegral fun beta =>
            (paritySigma kappa delta r beta * v.toFun r beta) ^ 2
              / Estimates.correctionB q r beta :=
    fun r => torusIntegral_real_smul 2⁻¹ _
  simp only [hpull]
  exact torusIntegral_real_smul 2⁻¹ _

/-! ## The weighted scalar completion the bridge forces

`Manhattan.V4.scalarCompletion_le` is stated with coefficient one on both the
degree-three density `sigma u^2` and the degree-two residual `(w - sigma u)^2/B`.
The bridge above shows that at the Version 4 kernel the mixed symbol is
`(sqrt 2)⁻¹ sigma v`, while (P4)
`Manhattan.V4.evenMajorantEnergy_parityKernel` gives `∫ M |K|^2 = ∫ sigma v^2`.
Writing `u = (sqrt 2)⁻¹ v` puts the residual in the shape `(w - sigma u)^2/B`
and turns the degree-three cost `C₃ ∫ M |K|^2` into `2 C₃ ∫ sigma u^2`: the
normalization cancels, but the **weight** `C = 2 C₃` does not.  These three
lemmas are the completion of the square at that weight.  With `C₃ = 9` of
`Manhattan.V4.operatorEstimate` the weight is `C = 18`. -/

/-- The exact algebraic identity behind the weighted scalar completion. -/
theorem weightedCompletion_sub_eq {B sigma w u C : ℝ} (hB : 0 < B)
    (hsigma : 0 ≤ sigma) (hC : 0 < C) :
    C * sigma * u ^ 2 + (w - sigma * u) ^ 2 / B - w ^ 2 / (B + sigma / C)
      = sigma * ((B * C + sigma) * u - w) ^ 2 / (B * (B * C + sigma)) := by
  have hD : 0 < B * C + sigma := by positivity
  have hd : B + sigma / C = (B * C + sigma) / C := by
    field_simp
  rw [hd]
  field_simp
  ring

/-- Pointwise form: `w²/(B + sigma/C)` is a lower bound for every `u`. -/
theorem weightedCompletion_le {B sigma w C : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma)
    (hC : 0 < C) (u : ℝ) :
    w ^ 2 / (B + sigma / C) ≤ C * sigma * u ^ 2 + (w - sigma * u) ^ 2 / B := by
  have hD : 0 < B * C + sigma := by positivity
  have h := weightedCompletion_sub_eq (B := B) (sigma := sigma) (w := w) (u := u)
    (C := C) hB hsigma hC
  have hnn : 0 ≤ sigma * ((B * C + sigma) * u - w) ^ 2 / (B * (B * C + sigma)) := by
    positivity
  linarith

/-- The minimizer `u = w/(BC + sigma)` attains the value. -/
theorem weightedCompletion_eq {B sigma w C : ℝ} (hB : 0 < B) (hsigma : 0 ≤ sigma)
    (hC : 0 < C) :
    C * sigma * (w / (B * C + sigma)) ^ 2
        + (w - sigma * (w / (B * C + sigma))) ^ 2 / B
      = w ^ 2 / (B + sigma / C) := by
  have hD : 0 < B * C + sigma := by positivity
  have h := weightedCompletion_sub_eq (B := B) (sigma := sigma) (w := w)
    (u := w / (B * C + sigma)) (C := C) hB hsigma hC
  have hz : (B * C + sigma) * (w / (B * C + sigma)) - w = 0 := by
    field_simp
    ring
  rw [hz] at h
  have hzero : sigma * (0 : ℝ) ^ 2 / (B * (B * C + sigma)) = 0 := by simp
  linarith

/-- At any weight `C ≥ 1` the weighted minimum is still controlled by the Move 1
density `w²/(B + sigma)`, at the cost of the factor `C`.  This is the only place
the weight leaves the argument, and it leaves it as an absolute constant. -/
theorem weightedCompletion_le_density {B sigma w C : ℝ} (hB : 0 < B)
    (hsigma : 0 ≤ sigma) (hC : 1 ≤ C) :
    w ^ 2 / (B + sigma / C) ≤ C * (w ^ 2 / (B + sigma)) := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hBs : 0 < B + sigma := by linarith
  have hBsC : 0 < B + sigma / C := by positivity
  have hkey : (B + sigma) ≤ C * (B + sigma / C) := by
    have : C * (B + sigma / C) = C * B + sigma := by
      field_simp
    rw [this]
    nlinarith
  have hw : 0 ≤ w ^ 2 := sq_nonneg w
  rw [div_le_iff₀ hBsC]
  rw [mul_comm C (w ^ 2 / (B + sigma)), mul_assoc]
  rw [div_mul_eq_mul_div, le_div_iff₀ hBs]
  nlinarith

end Manhattan.V4
