import Manhattan.Glue.SummandThree
import Manhattan.Glue.CubicDischargeProjection

/-!
# The concrete lowering formula for the actual correction

`Manhattan.Glue.lemma_distinct_of_concreteLowering` proves Lemma 5.3
(`manuscript.tex:1212-1219`) for any raw type-`112` coefficient that satisfies
the concrete lowering formula `Manhattan.Glue.ConcreteLoweringFormula`.  Its
only previous instantiation,
`Manhattan.Glue.lemma_distinct_shiftedRawCoefficient`, carries a
diagonal-freeness hypothesis under which the coincident-row carrier vanishes
identically, so it says nothing about the competitor.  This file supplies the
missing instance: the paper's explicit degree-three correction
`Manhattan.Estimates.correctionCoefficient`, periodized in its second row
frequency, satisfies the concrete lowering formula with both Finset
normalizations equal to one.

The two constants are `cTwoNorm = 1` and `cMixNorm = 1`.  The manuscript's
`k̃` carries `i sin β / √2`, and the tuple-space `√2` of
`Manhattan.Glue.rawD2StarMixed_shiftedRawCoefficient` is the ratio of the
type-`112` normalization to the type-`12` one.  The explicit formula
`Manhattan.Estimates.correctionCoefficient` carries `i sin β` with no `√2`, so
in these coordinates the mixed normalization is one; the computation below
proves it rather than assuming it.

Two things are established.

* The **two-row** clause: both the concrete two-row component of `D₂*` on the
  correction (`Manhattan.Glue.type112DStarTwoRow_correction`) and the raw
  two-row symbol (`Manhattan.Glue.rawD2StarTwoRow_correctionCoefficient`)
  vanish, because `k̃` is odd in the column frequency.
* The **mixed** identity, which is the actual computation.  The concrete
  operator reads its input at `tripleToFinset (m, 0, n ± 1)`, and at `m = 0`
  that Finset is not a type-`112` index, so the concrete `D₂*` drops exactly
  the coincident-row term that the raw `D̃₂*` keeps.  On the raw side the same
  term is dropped by `Manhattan.Glue.rawOffDiagonalPart`, whose Fourier
  coefficients vanish on the coincident-row diagonal
  (`Manhattan.Glue.rawFourierCoefficient_rawOffDiagonalPart`).  Off the
  diagonal the two sides agree up to the unimodular `(shift)` phase, exactly
  as in `Manhattan.Glue.twoRowFourierCoefficient_orderedFreqTwo_shift`.

Paper: `manuscript.tex:793-840`, `manuscript.tex:1212-1219`,
`manuscript.tex:1274-1303`.
-/

open MeasureTheory Set

namespace Manhattan.Glue

noncomputable section

local instance correctionLoweringPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Elementary facts about the integer characters -/

theorem measurable_intCharacter (i : ℤ) : Measurable (intCharacter i) := by
  unfold intCharacter
  fun_prop

theorem TorusBoundedOne.charMul {f : ℝ → ℂ} (hf : TorusBoundedOne f) (j : ℤ) :
    TorusBoundedOne fun x => intCharacter j x * f x := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨(measurable_intCharacter j).mul hm, C, fun x => ?_⟩
  rw [norm_mul, norm_intCharacter, one_mul]
  exact hC x

/-- The character identity behind (D2b): `e^{-inβ}(-i sin β)` is the average of
two neighbouring characters. -/
theorem intCharacter_mul_neg_I_sin (n : ℤ) (beta : ℝ) :
    intCharacter (-n) beta * (-Complex.I * (Real.sin beta : ℂ)) =
      (2 : ℂ)⁻¹ * (intCharacter (-(n + 1)) beta - intCharacter (-(n - 1)) beta) := by
  have h1 : intCharacter (-(n + 1)) beta =
      intCharacter (-n) beta * intCharacter (-1) beta := by
    rw [intCharacter_add_index]
    congr 1
    ring
  have h2 : intCharacter (-(n - 1)) beta =
      intCharacter (-n) beta * intCharacter 1 beta := by
    rw [intCharacter_add_index]
    congr 1
    ring
  have e1 : intCharacter (-1) beta = Complex.exp (-(beta : ℂ) * Complex.I) := by
    rw [intCharacter]
    congr 1
    push_cast
    ring
  have e2 : intCharacter 1 beta = Complex.exp ((beta : ℂ) * Complex.I) := by
    rw [intCharacter]
    congr 1
    push_cast
    ring
  have h3 : intCharacter (-1) beta - intCharacter 1 beta =
      -2 * Complex.I * (Real.sin beta : ℂ) := by
    rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg, Complex.ofReal_sin]
    ring
  rw [h1, h2, ← mul_sub, ← mul_assoc, mul_comm ((2 : ℂ)⁻¹), mul_assoc, h3]
  ring

/-! ## Periodization is invisible to the Fourier coefficients -/

/-- The complex form of `Manhattan.Glue.torusIntegral_congr_on`. -/
theorem torusIntegral_congr_on_torus {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E}
    (h : ∀ x ∈ Estimates.torus, f x = g x) :
    Estimates.torusIntegral f = Estimates.torusIntegral g := by
  unfold Estimates.torusIntegral
  congr 1
  refine setIntegral_congr_fun ?_ h
  rw [Estimates.torus]
  exact measurableSet_Ioc

/-- Reducing the second row frequency to the fundamental domain does not move
any three-dimensional Fourier coefficient. -/
theorem rawFourierCoefficient_periodizeRow (k : ℝ → ℝ → ℝ → ℂ) (n : Fin 3 → ℤ) :
    rawFourierCoefficient (periodizeRow k) n = rawFourierCoefficient k n := by
  unfold rawFourierCoefficient
  have h : ∀ r : ℝ,
      (Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 0) r * intCharacter (-n 1) r' *
          intCharacter (-n 2) beta * periodizeRow k r r' beta) =
      Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-n 0) r * intCharacter (-n 1) r' *
          intCharacter (-n 2) beta * k r r' beta := by
    intro r
    refine torusIntegral_congr_on_torus ?_
    intro r' hr'
    simp only [periodizeRow_eq hr']
  simp only [h]

/-! ## The mixed Fourier coefficient of the raw lowering symbol -/

/-- The two-torus Fourier coefficient of a mixed frequency symbol. -/
def mixedFourierCoefficient (F : ℝ → ℝ → ℂ) (m n : ℤ) : ℂ :=
  Estimates.torusIntegral fun r : ℝ => Estimates.torusIntegral fun beta : ℝ =>
    intCharacter (-m) r * intCharacter (-n) beta * F r beta

/-- The column-character transform of a bounded raw coefficient. -/
theorem torusBounded₃_colChar {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k) (j : ℤ) :
    TorusBoundedThree fun r r' b => intCharacter (-j) b * k r r' b := by
  obtain ⟨hm, C, hC⟩ := hk
  refine ⟨((measurable_intCharacter (-j)).comp
    (measurable_snd.comp measurable_snd)).mul hm, C, fun r r' b => ?_⟩
  rw [norm_mul, norm_intCharacter, one_mul]
  exact hC r r' b

/-- Fubini for a bounded raw coefficient against a column character. -/
theorem torusIntegral_colChar_swap {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (j : ℤ) (r : ℝ) :
    (Estimates.torusIntegral fun beta : ℝ => intCharacter (-j) beta *
        Estimates.torusIntegral fun r' : ℝ => k r r' beta) =
      Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-j) beta * k r r' beta := by
  obtain ⟨hm, C, hC⟩ := hk
  have hpull : ∀ beta : ℝ, (intCharacter (-j) beta *
      Estimates.torusIntegral fun r' : ℝ => k r r' beta) =
      Estimates.torusIntegral fun r' : ℝ => intCharacter (-j) beta * k r r' beta :=
    fun beta => (torusIntegral_const_mul _ _).symm
  simp only [hpull]
  refine torusIntegral_swap ?_
  refine integrable_prod_torus_of_bound (C := C) ?_ ?_
  · have hmeas : Measurable fun z : ℝ × ℝ =>
        intCharacter (-j) z.1 * k r z.2 z.1 :=
      ((measurable_intCharacter (-j)).comp measurable_fst).mul
        (hm.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
    exact hmeas.aestronglyMeasurable
  · intro z
    rw [Function.uncurry, norm_mul, norm_intCharacter, one_mul]
    exact hC r z.2 z.1

/-- The raw Fourier coefficient at a pinned second row index, before the outer
row integral. -/
def rawColumnTransform (k : ℝ → ℝ → ℝ → ℂ) (j : ℤ) (r : ℝ) : ℂ :=
  Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
    intCharacter (-j) beta * k r r' beta

theorem rawColumnTransform_apply (k : ℝ → ℝ → ℝ → ℂ) (j : ℤ) (r : ℝ) :
    rawColumnTransform k j r =
      Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-j) beta * k r r' beta := rfl

theorem torusBounded₁_rawColumnTransform {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (j m : ℤ) :
    TorusBoundedOne fun r => intCharacter (-m) r * rawColumnTransform k j r :=
  ((torusBounded₃_colChar hk j).integral_col.integral_right).charMul (-m)

theorem rawFourierCoefficient_pinned (k : ℝ → ℝ → ℝ → ℂ) (m j : ℤ) :
    rawFourierCoefficient k ![m, 0, j] =
      Estimates.torusIntegral fun r : ℝ =>
        intCharacter (-m) r * rawColumnTransform k j r := by
  rw [rawFourierCoefficient]
  have h : ∀ r : ℝ,
      (Estimates.torusIntegral fun r' : ℝ => Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-(![m, 0, j] 0)) r * intCharacter (-(![m, 0, j] 1)) r' *
          intCharacter (-(![m, 0, j] 2)) beta * k r r' beta) =
      intCharacter (-m) r * rawColumnTransform k j r := by
    intro r
    rw [rawColumnTransform_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, neg_zero, intCharacter_index_zero,
      mul_one]
    rw [← torusIntegral_const_mul]
    congr 1
    funext r'
    rw [← torusIntegral_const_mul]
    congr 1
    funext beta
    ring
  simp only [h]

/-- **(D2b) on Fourier coefficients.**  The mixed Fourier coefficient of the raw
mixed lowering symbol is one signed lattice step in the column index, with the
second row index of the input pinned to the origin.  This is the raw-side
counterpart of `Manhattan.Glue.type112DStarMixed_eq`. -/
theorem mixedFourierCoefficient_rawD2StarMixed {k : ℝ → ℝ → ℝ → ℂ}
    (hk : TorusBoundedThree k) (m n : ℤ) :
    mixedFourierCoefficient (rawD2StarMixed k) m n =
      (2 : ℂ)⁻¹ * (rawFourierCoefficient k ![m, 0, n + 1] -
        rawFourierCoefficient k ![m, 0, n - 1]) := by
  obtain ⟨hm, C, hC⟩ := hk
  have hk' : TorusBoundedThree k := ⟨hm, C, hC⟩
  have hrow : ∀ r : ℝ, TorusBoundedOne fun beta : ℝ =>
      Estimates.torusIntegral fun r' : ℝ => k r r' beta := by
    intro r
    have hB : TorusBoundedTwo fun beta r' : ℝ => k r r' beta :=
      ⟨hm.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)), C,
        fun beta r' => hC r r' beta⟩
    exact hB.integral_right
  have hinner : ∀ r : ℝ,
      (Estimates.torusIntegral fun beta : ℝ =>
        intCharacter (-m) r * intCharacter (-n) beta * rawD2StarMixed k r beta) =
      intCharacter (-m) r * ((2 : ℂ)⁻¹ *
        (rawColumnTransform k (n + 1) r - rawColumnTransform k (n - 1) r)) := by
    intro r
    have hstep : (fun beta : ℝ =>
        intCharacter (-m) r * intCharacter (-n) beta * rawD2StarMixed k r beta) =
        fun beta : ℝ => intCharacter (-m) r * ((2 : ℂ)⁻¹ *
          (intCharacter (-(n + 1)) beta *
              (Estimates.torusIntegral fun r' : ℝ => k r r' beta) -
            intCharacter (-(n - 1)) beta *
              (Estimates.torusIntegral fun r' : ℝ => k r r' beta))) := by
      funext beta
      rw [rawD2StarMixed]
      have hchar := intCharacter_mul_neg_I_sin n beta
      calc intCharacter (-m) r * intCharacter (-n) beta *
            (-Complex.I * (Real.sin beta : ℂ) *
              Estimates.torusIntegral fun r' : ℝ => k r r' beta)
          = intCharacter (-m) r *
              ((intCharacter (-n) beta * (-Complex.I * (Real.sin beta : ℂ))) *
                Estimates.torusIntegral fun r' : ℝ => k r r' beta) := by ring
        _ = _ := by rw [hchar]; ring
    rw [hstep, torusIntegral_const_mul, torusIntegral_const_mul]
    congr 2
    rw [torusIntegral_sub ((hrow r).charMul (-(n + 1))).integrable
        ((hrow r).charMul (-(n - 1))).integrable,
      torusIntegral_colChar_swap hk' (n + 1) r,
      torusIntegral_colChar_swap hk' (n - 1) r, rawColumnTransform_apply,
      rawColumnTransform_apply]
  rw [mixedFourierCoefficient]
  simp only [hinner]
  rw [rawFourierCoefficient_pinned, rawFourierCoefficient_pinned]
  have hsplit : (fun r : ℝ => intCharacter (-m) r * ((2 : ℂ)⁻¹ *
      (rawColumnTransform k (n + 1) r - rawColumnTransform k (n - 1) r))) =
      fun r : ℝ => (2 : ℂ)⁻¹ *
        (intCharacter (-m) r * rawColumnTransform k (n + 1) r -
          intCharacter (-m) r * rawColumnTransform k (n - 1) r) := by
    funext r
    ring
  rw [hsplit, torusIntegral_const_mul]
  congr 1
  exact torusIntegral_sub (torusBounded₁_rawColumnTransform hk' (n + 1) m).integrable
    (torusBounded₁_rawColumnTransform hk' (n - 1) m).integrable

/-- The row Fourier coefficients of a raw coefficient that is symmetric in its
two row frequencies are symmetric in the two row indices. -/
theorem rawFourierCoefficient_swap {k : ℝ → ℝ → ℝ → ℂ} (hk : TorusBoundedThree k)
    (hsymm : ∀ r r' b, k r r' b = k r' r b) (u v j : ℤ) :
    rawFourierCoefficient k ![u, v, j] = rawFourierCoefficient k ![v, u, j] := by
  obtain ⟨hgm, Cg, hCg⟩ := (torusBounded₃_colChar hk j).integral_col
  set g : ℝ → ℝ → ℂ := fun r r' =>
    Estimates.torusIntegral fun b : ℝ => intCharacter (-j) b * k r r' b with hgdef
  have hgsymm : ∀ r r' : ℝ, g r r' = g r' r := by
    intro r r'
    rw [hgdef]
    simp only
    congr 1
    funext b
    rw [hsymm]
  have hreduce : ∀ x y : ℤ, rawFourierCoefficient k ![x, y, j] =
      Estimates.torusIntegral fun r : ℝ => Estimates.torusIntegral fun r' : ℝ =>
        intCharacter (-x) r * intCharacter (-y) r' * g r r' := by
    intro x y
    rw [rawFourierCoefficient]
    have h : ∀ r r' : ℝ,
        (Estimates.torusIntegral fun b : ℝ =>
          intCharacter (-(![x, y, j] 0)) r * intCharacter (-(![x, y, j] 1)) r' *
            intCharacter (-(![x, y, j] 2)) b * k r r' b) =
        intCharacter (-x) r * intCharacter (-y) r' * g r r' := by
      intro r r'
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [hgdef]
      simp only
      rw [← torusIntegral_const_mul]
      congr 1
      funext b
      ring
    simp only [h]
  rw [hreduce u v, hreduce v u]
  have hFint : Integrable (Function.uncurry fun x y : ℝ =>
      intCharacter (-u) x * intCharacter (-v) y * g x y)
      ((volume.restrict Estimates.torus).prod (volume.restrict Estimates.torus)) := by
    refine integrable_prod_torus_of_bound (C := Cg) ?_ ?_
    · exact ((((measurable_intCharacter (-u)).comp measurable_fst).mul
        ((measurable_intCharacter (-v)).comp measurable_snd)).mul
          hgm).aestronglyMeasurable
    · intro z
      rw [Function.uncurry, norm_mul, norm_mul, norm_intCharacter,
        norm_intCharacter, one_mul, one_mul]
      exact hCg z.1 z.2
  rw [torusIntegral_swap hFint]
  have hbody : ∀ y : ℝ,
      (Estimates.torusIntegral fun x : ℝ =>
        intCharacter (-u) x * intCharacter (-v) y * g x y) =
      Estimates.torusIntegral fun r' : ℝ =>
        intCharacter (-v) y * intCharacter (-u) r' * g y r' := by
    intro y
    congr 1
    funext x
    rw [hgsymm y x]
    ring
  simp only [hbody]

/-! ## The three-dimensional Fourier coefficients of the correction -/

section TorusTransfer

attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] cubicUnitAddCircleMeasureSpace

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The complex form of `Manhattan.Glue.integral_unitTorus_three`. -/
theorem integral_unitTorus_three_complex {F : ℝ → ℝ → ℝ → ℂ}
    (hF : TorusBoundedThree F) :
    (∫ x : UnitAddTorus (Fin 3),
        F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
          (Manhattan.unitTorusAngle (x 2)))
      = Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
          Estimates.torusIntegral fun b => F r r' b := by
  obtain ⟨hm, C, hC⟩ := hF
  have hF' : TorusBoundedThree F := ⟨hm, C, hC⟩
  have hcol : TorusBoundedTwo fun r r' => Estimates.torusIntegral fun b => F r r' b :=
    hF'.integral_col
  have hout : TorusBoundedOne fun r => Estimates.torusIntegral fun r' =>
      Estimates.torusIntegral fun b => F r r' b := hcol.integral_right
  have h0 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 0) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 0)
  have h1 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 1) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 1)
  have h2 : Measurable fun x : UnitAddTorus (Fin 3) =>
      Manhattan.unitTorusAngle (x 2) :=
    Manhattan.unitTorusAngle_measurable.comp (measurable_pi_apply 2)
  have hcoord : Measurable fun x : UnitAddTorus (Fin 3) =>
      ((Manhattan.unitTorusAngle (x 0), Manhattan.unitTorusAngle (x 1),
        Manhattan.unitTorusAngle (x 2)) : ℝ × ℝ × ℝ) := h0.prodMk (h1.prodMk h2)
  have hmeasT : Measurable fun x : UnitAddTorus (Fin 3) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
        (Manhattan.unitTorusAngle (x 2)) := hm.comp hcoord
  have hint : Integrable fun x : UnitAddTorus (Fin 3) =>
      F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
        (Manhattan.unitTorusAngle (x 2)) :=
    Integrable.mono' (integrable_const C) hmeasT.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hC _ _ _)
  have key : ∀ L : ℂ →L[ℝ] ℝ,
      (∫ x : UnitAddTorus (Fin 3),
          L (F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
            (Manhattan.unitTorusAngle (x 2)))) =
        L (Estimates.torusIntegral fun r => Estimates.torusIntegral fun r' =>
            Estimates.torusIntegral fun b => F r r' b) := by
    intro L
    have hmeasL : Measurable fun z : ℝ × ℝ × ℝ => L (F z.1 z.2.1 z.2.2) :=
      L.continuous.measurable.comp hm
    have hbL : ∀ r r' b : ℝ, |L (F r r' b)| ≤ ‖L‖ * C := by
      intro r r' b
      have hh1 : ‖L (F r r' b)‖ ≤ ‖L‖ * ‖F r r' b‖ := L.le_opNorm _
      have hh2 : ‖L‖ * ‖F r r' b‖ ≤ ‖L‖ * C :=
        mul_le_mul_of_nonneg_left (hC r r' b) (norm_nonneg L)
      simpa [Real.norm_eq_abs] using hh1.trans hh2
    rw [integral_unitTorus_three (fun r r' b => L (F r r' b)) hmeasL hbL]
    have step1 : ∀ r r' : ℝ,
        (Estimates.torusIntegral fun b => L (F r r' b)) =
          L (Estimates.torusIntegral fun b => F r r' b) :=
      fun r r' => map_torusIntegral L (hF'.integrable_col r r')
    simp only [step1]
    have step2 : ∀ r : ℝ,
        (Estimates.torusIntegral fun r' =>
            L (Estimates.torusIntegral fun b => F r r' b)) =
          L (Estimates.torusIntegral fun r' =>
            Estimates.torusIntegral fun b => F r r' b) :=
      fun r => map_torusIntegral L (hcol.integrable_right r)
    simp only [step2]
    exact map_torusIntegral L hout.integrable
  apply Complex.ext
  · simpa using (Complex.reCLM.integral_comp_comm hint).symm.trans (key Complex.reCLM)
  · simpa using (Complex.imCLM.integral_comp_comm hint).symm.trans (key Complex.imCLM)

/-- **The Fourier bridge.**  The three-dimensional Fourier coefficients of the
raw correction, taken on the abstract frequency torus where the competitor's
`ℓ²` coefficient lives, are the iterated normalized torus integrals of the
explicit formula. -/
theorem mFourierCoeff_rawCorrection {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₂ : ℝ) (n : Manhattan.RawType112Index) :
    UnitAddTorus.mFourierCoeff
        ((Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
          UnitAddTorus (Fin 3) → ℂ)) n =
      rawFourierCoefficient (Estimates.correctionCoefficient 40 q a p₂) n := by
  classical
  set F : ℝ → ℝ → ℝ → ℂ := fun r r' b =>
    intCharacter (-n 0) r * intCharacter (-n 1) r' * intCharacter (-n 2) b *
      Estimates.correctionCoefficient 40 q a p₂ r r' b with hFdef
  have hFB : TorusBoundedThree F :=
    torusBounded₃_character_mul
      (torusBounded₃_correctionCoefficient (by norm_num) hlambda a p₂) n
  have hcoeff : UnitAddTorus.mFourierCoeff
      ((Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num) hlambda a p₂ :
        UnitAddTorus (Fin 3) → ℂ)) n
      = ∫ x : UnitAddTorus (Fin 3),
          F (Manhattan.unitTorusAngle (x 0)) (Manhattan.unitTorusAngle (x 1))
            (Manhattan.unitTorusAngle (x 2)) := by
    rw [UnitAddTorus.mFourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [(Manhattan.rawCorrectionFunction_memLp (kappa := 40)
      (by norm_num) hlambda a p₂).coeFn_toLp] with x hx
    have hx' : (Manhattan.rawCorrectionL2 (kappa := 40) (by norm_num)
        hlambda a p₂ : UnitAddTorus (Fin 3) → ℂ) x =
        Manhattan.rawCorrectionFunction 40 q a p₂ x := hx
    rw [hx', smul_eq_mul, mFourier_eq_exp_angle, hFdef]
    show _ = intCharacter (-n 0) _ * intCharacter (-n 1) _ *
      intCharacter (-n 2) _ * _
    rw [Manhattan.rawCorrectionFunction]
    congr 1
    rw [intCharacter, intCharacter, intCharacter, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    rw [Fin.sum_univ_three]
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [hcoeff, integral_unitTorus_three_complex hFB]
  rfl

end TorusTransfer

/-! ## The pinned mixed index -/

/-- A pinned mixed triple is a type-`112` index exactly when its free row index
is nonzero. -/
theorem isType112Index_tripleToFinset_pinned {m j : ℤ} (hm : m ≠ 0) :
    IsType112Index (tripleToFinset (m, 0, j)) := by
  have hlt : min m 0 < max m 0 := min_lt_max.mpr hm
  have h := Manhattan.orderedType112Lines_isType112
    ⟨![min m 0, max m 0, j], by simpa using hlt⟩
  have hset : Manhattan.orderedType112Lines
      ⟨![min m 0, max m 0, j], by simpa using hlt⟩ =
      tripleToFinset (m, 0, j) := by
    rw [Manhattan.orderedType112Lines]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rcases lt_or_gt_of_ne hm with hlt' | hgt'
    · rw [min_eq_left hlt'.le, max_eq_right hlt'.le]
      rfl
    · rw [min_eq_right hgt'.le, max_eq_left hgt'.le]
      ext l
      simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton]
      tauto
  rwa [hset] at h

/-- The canonical ordered coordinates of a pinned mixed triple. -/
theorem type112RawIndex_tripleToFinset_pinned {m j : ℤ} (hm : m ≠ 0)
    (h : IsType112Index (tripleToFinset (m, 0, j))) :
    Manhattan.type112RawIndex ⟨tripleToFinset (m, 0, j), h⟩ =
      ![min m 0, max m 0, j] := by
  have hlt : min m 0 < max m 0 := min_lt_max.mpr hm
  set n : Manhattan.OrderedType112Index :=
    ⟨![min m 0, max m 0, j], by simpa using hlt⟩ with hn
  have hset : Manhattan.orderedType112Lines n = tripleToFinset (m, 0, j) := by
    rw [hn, Manhattan.orderedType112Lines]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rcases lt_or_gt_of_ne hm with hlt' | hgt'
    · rw [min_eq_left hlt'.le, max_eq_right hlt'.le]
      rfl
    · rw [min_eq_right hgt'.le, max_eq_left hgt'.le]
      ext l
      simp only [tripleToFinset, Finset.mem_insert, Finset.mem_singleton]
      tauto
  have hequiv : Manhattan.orderedType112Equiv n = ⟨tripleToFinset (m, 0, j), h⟩ :=
    Subtype.ext hset
  rw [Manhattan.type112RawIndex, ← hequiv, Equiv.symm_apply_apply, hn]

/-! ## The competitor's coefficient at a pinned mixed index -/

/-- The competitor's degree-three coefficient at a pinned mixed index.  Off the
coincident-row diagonal it is the raw Fourier coefficient of the explicit
formula, carrying the `(shift)` phase; on the diagonal the Finset index is not
of type `112` and the coefficient is read as zero.  This is the concrete side of
the coincident-row drop. -/
theorem type112CoefficientAt_shiftedCorrection_pinned {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (m j : ℤ) :
    type112CoefficientAt
        (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
          (by norm_num) hlambda a p₁ p₂) (tripleToFinset (m, 0, j)) =
      (if m = 0 then 0 else
        Complex.exp (Complex.I * (((m : ℝ) * p₂ + (j : ℝ) * p₁ : ℝ) : ℂ)) *
          rawFourierCoefficient (Estimates.correctionCoefficient 40 q a p₂)
            ![m, 0, j]) := by
  by_cases hm : m = 0
  · subst hm
    rw [type112CoefficientAt, dif_neg (not_isType112_tripleToFinset_diag 0 j),
      if_pos rfl]
  · have h112 : IsType112Index (tripleToFinset (m, 0, j)) :=
      isType112Index_tripleToFinset_pinned hm
    rw [type112CoefficientAt, dif_pos h112, if_neg hm,
      Manhattan.shiftedCorrectionType112Coefficients_apply,
      Manhattan.correctionType112Coefficients_apply,
      type112RawIndex_tripleToFinset_pinned hm h112,
      Manhattan.rawType112ShiftPhase_eq, mFourierCoeff_rawCorrection hlambda a p₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have hphase : ((min m 0 : ℤ) : ℝ) + ((max m 0 : ℤ) : ℝ) = (m : ℝ) := by
      push_cast
      rw [min_add_max]
      ring
    have hcoeff : rawFourierCoefficient (Estimates.correctionCoefficient 40 q a p₂)
        ![min m 0, max m 0, j] =
        rawFourierCoefficient (Estimates.correctionCoefficient 40 q a p₂)
          ![m, 0, j] := by
      rcases lt_or_gt_of_ne hm with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le]
        exact rawFourierCoefficient_swap
          (torusBounded₃_correctionCoefficient (by norm_num) hlambda a p₂)
          (fun r r' b => Manhattan.correctionCoefficient_swap 40 q a p₂ r r' b) 0 m j
    rw [hcoeff, hphase]

/-! ## The mixed identity -/

/-- **The mixed identity for the actual correction.**  The `(m,n)` Fourier
coefficient of the raw mixed lowering symbol of `Pi_3 k̃` is the genuine mixed
Walsh coefficient of `D₂* k_p`, read with the `(shift)` phase of
`manuscript.tex:791-800`.  Both sides drop the coincident-row term at `m = 0`:
on the concrete side because `tripleToFinset (m, 0, j)` is then not a type-`112`
index, on the raw side because `Manhattan.Glue.rawOffDiagonalPart` kills the
diagonal Fourier coefficients. -/
theorem mixedFourierCoefficient_correction {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) (m n : ℤ) :
    mixedFourierCoefficient
        (rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))))) m n =
      intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
        Manhattan.type112DStarMixed p
          (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
            (by norm_num) hlambda a (p 0) (p 1))
          ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩ := by
  have hkB : TorusBoundedThree
      (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) :=
    torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num) hlambda a (p 1))
  have hper : ∀ r beta : ℝ, Function.Periodic
      (fun r' => periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))
        r r' beta) (2 * Real.pi) := fun r beta => periodizeRow_periodic _ r beta
  have hoff : TorusBoundedThree (rawOffDiagonalPart (p 1)
      (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) :=
    torusBounded₃_rawOffDiagonalPart hkB (p 1)
  have hraw : ∀ j : ℤ,
      rawFourierCoefficient (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) ![m, 0, j] =
        (if m = 0 then 0 else
          rawFourierCoefficient (Estimates.correctionCoefficient 40 q a (p 1))
            ![m, 0, j]) := by
    intro j
    rw [rawFourierCoefficient_rawOffDiagonalPart hkB hper]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases hm : m = 0
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm, rawFourierCoefficient_periodizeRow]
  rw [mixedFourierCoefficient_rawD2StarMixed hoff, hraw, hraw,
    type112DStarMixed_eq, type112CoefficientAt_shiftedCorrection_pinned,
    type112CoefficientAt_shiftedCorrection_pinned]
  by_cases hm : m = 0
  · simp only [if_pos hm]
    ring
  · simp only [if_neg hm]
    set A := rawFourierCoefficient (Estimates.correctionCoefficient 40 q a (p 1))
      ![m, 0, n + 1] with hA
    set B := rawFourierCoefficient (Estimates.correctionCoefficient 40 q a (p 1))
      ![m, 0, n - 1] with hB
    have hp1 : intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
        Complex.exp (-Complex.I * ((p 0 : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) = 1 := by
      have hcomb : intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
          Complex.exp (-Complex.I * ((p 0 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ((((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) =
          Complex.exp (Complex.I *
            (((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + -(p 0) +
              ((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0) : ℝ)) : ℂ)) := by
        rw [intCharacter, intCharacter, ← Complex.exp_add, ← Complex.exp_add,
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hzero : ((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + -(p 0) +
          ((m : ℝ) * p 1 + ((n + 1 : ℤ) : ℝ) * p 0) : ℝ)) = 0 := by
        push_cast
        ring
      rw [hcomb, hzero]
      simp
    have hp2 : intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
        Complex.exp (Complex.I * ((p 0 : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ((((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) = 1 := by
      have hcomb : intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
          Complex.exp (Complex.I * ((p 0 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ((((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0 : ℝ)) : ℂ)) =
          Complex.exp (Complex.I *
            (((((-m : ℤ) : ℝ) * p 1 + ((-n : ℤ) : ℝ) * p 0 + p 0 +
              ((m : ℝ) * p 1 + ((n - 1 : ℤ) : ℝ) * p 0) : ℝ)) : ℂ)) := by
        rw [intCharacter, intCharacter, ← Complex.exp_add, ← Complex.exp_add,
          ← Complex.exp_add]
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

/-! ## The two-row halves -/

/-- **The concrete two-row component of `D₂*k_p` vanishes**, for the
competitor's own coefficient carrying the `(shift)` phase.  This is
`Manhattan.Glue.type112DStarTwoRow_correction` transported through the
unimodular twist. -/
theorem type112DStarTwoRow_shiftedCorrection_apply {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (p : Fin 2 → ℝ) (T : Type11Index) :
    Manhattan.type112DStarTwoRow p
      (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
        (by norm_num) hlambda a p₁ p₂) T = 0 := by
  have hcol : ∀ m m' : ℤ, type112CoefficientAt
      (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
        (by norm_num) hlambda a p₁ p₂) (tripleToFinset (m, m', 0)) = 0 := by
    intro m m'
    rw [type112CoefficientAt]
    by_cases h : IsType112Index (tripleToFinset (m, m', 0))
    · rw [dif_pos h]
      exact Manhattan.type112ShiftTwist_eq_zero
        (correctionType112Coefficients_eq_zero_of_col hlambda a p₂
          (type112RawIndex_two_tripleToFinset h))
    · rw [dif_neg h]
  have hT := type112DStarTwoRow_eq p
    (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
      (by norm_num) hlambda a p₁ p₂) T
  simp only [hcol] at hT
  simpa using hT

theorem type112DStarTwoRow_shiftedCorrection {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a p₁ p₂ : ℝ) (p : Fin 2 → ℝ) :
    Manhattan.type112DStarTwoRow p
      (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
        (by norm_num) hlambda a p₁ p₂) = 0 := by
  apply lp.ext
  funext T
  simpa using type112DStarTwoRow_shiftedCorrection_apply hlambda a p₁ p₂ p T

/-- **The raw two-row symbol of `Pi_3 k̃` has no two-row Walsh coefficient.**
The raw symbol of `k̃` itself vanishes identically because `k̃` is odd in the
column frequency (`Manhattan.Glue.rawD2StarTwoRow_correctionCoefficient`), and
the coincident-row part it differs from is a function of `alpha` alone, which
the degree-two projection removes. -/
theorem twoRowFourierCoefficient_rawD2StarTwoRow_correction
    {q : Estimates.Parameters} (hlambda : 0 < q.lambda) (a p₂ : ℝ)
    (T : Type11Index) :
    twoRowFourierCoefficient (rawD2StarTwoRow p₂ (rawOffDiagonalPart p₂
      (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)))) T = 0 := by
  have hkB : TorusBoundedThree
      (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)) :=
    torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num) hlambda a p₂)
  have hper : ∀ r beta : ℝ, Function.Periodic
      (fun r' => periodizeRow (Estimates.correctionCoefficient 40 q a p₂)
        r r' beta) (2 * Real.pi) := fun r beta => periodizeRow_periodic _ r beta
  have hoff : TorusBoundedThree (rawOffDiagonalPart p₂
      (periodizeRow (Estimates.correctionCoefficient 40 q a p₂))) :=
    torusBounded₃_rawOffDiagonalPart hkB p₂
  have hzero : rawD2StarTwoRow p₂
      (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)) =
      fun _ _ => (0 : ℂ) := by
    funext r r'
    rw [rawD2StarTwoRow,
      show (Estimates.torusIntegral fun beta =>
          periodizeRow (Estimates.correctionCoefficient 40 q a p₂) r r' beta) = 0 from
        torusIntegral_correctionCoefficient_beta q a p₂ r (torusWrap r'), mul_zero]
  have hdiff := twoRowFourierCoefficient_sub (hkB.rawD2StarTwoRow p₂)
    (hoff.rawD2StarTwoRow p₂) T
  have hfun : (fun r r' => rawD2StarTwoRow p₂
        (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)) r r' -
      rawD2StarTwoRow p₂ (rawOffDiagonalPart p₂
        (periodizeRow (Estimates.correctionCoefficient 40 q a p₂))) r r') =
      fun r r' => diagonalTwoRowSymbol
        (rawDiagonalPart p₂ (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)))
        (mixedAlpha p₂ r r') := by
    funext r r'
    rw [← rawD2StarTwoRow_sub hkB hoff p₂ r r',
      show (fun x y z => periodizeRow (Estimates.correctionCoefficient 40 q a p₂) x y z -
          rawOffDiagonalPart p₂
            (periodizeRow (Estimates.correctionCoefficient 40 q a p₂)) x y z) =
        diagonalRawCarrier p₂ (rawDiagonalPart p₂
          (periodizeRow (Estimates.correctionCoefficient 40 q a p₂))) from
        funext fun x => funext fun y => funext fun z =>
          sub_rawOffDiagonalPart p₂ _ x y z]
    exact rawD2StarTwoRow_diagonalRawCarrier p₂ _ r r'
  rw [hfun, twoRowFourierCoefficient_comp_mixedAlpha p₂ _
      (diagonalTwoRowSymbol_periodic (rawDiagonalPart_periodic p₂ hper)) T,
    hzero, twoRowFourierCoefficient] at hdiff
  simp only [mul_zero, torusIntegral_const] at hdiff
  linear_combination hdiff

/-! ## The concrete lowering formula for the correction -/

/-- **The closing statement.**  The paper's explicit degree-three correction,
periodized in its second row frequency, satisfies the concrete lowering formula
of `Manhattan.Glue.ConcreteLoweringFormula` with both Finset normalizations
equal to one.

The two-row datum is the genuine concrete two-row component of `D₂*k_p`, which
is zero by `Manhattan.Glue.type112DStarTwoRow_shiftedCorrection`; the mixed
datum is the raw mixed symbol, whose Fourier coefficients are the genuine mixed
Walsh coefficients of `D₂*k_p` by
`Manhattan.Glue.mixedFourierCoefficient_correction`.  Nothing is defined by
fiat, and no diagonal-freeness hypothesis is used. -/
theorem concreteLoweringFormula_correction {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    ConcreteLoweringFormula 1 1 (p 1)
      (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) 0
      (rawD2StarMixed (rawOffDiagonalPart (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))))) := by
  constructor
  · intro T
    rw [Pi.zero_apply, one_mul,
      twoRowFourierCoefficient_rawD2StarTwoRow_correction hlambda a (p 1) T]
  · intro r beta
    rw [one_mul]

/-! ## Lemma 5.3 for the actual correction -/

/-- **Lemma 5.3** (`manuscript.tex:1212-1219`) for the competitor.  Both clauses,
with no diagonal-freeness hypothesis and with the universal constant
`‖1‖² = 1`: the raw/projected lowering difference of the paper's explicit
correction has no two-row component, and its coincident-row projection error is
bounded by the raw multiplier energy of the correction. -/
theorem lemma_distinct_correction {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    (rawProjectionDifference 1 1 (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) 0
        (rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))))).twoRow = 0 ∧
      projectionErrorHMinusSq q
          (rawDiagonalPart (p 1)
            (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) ≤
        rawMultiplierEnergy 40 q (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) := by
  have hkB : TorusBoundedThree
      (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) :=
    torusBounded₃_periodizeRow
      (torusBounded₃_correctionCoefficient (by norm_num) hlambda a (p 1))
  have hper : ∀ r beta : ℝ, Function.Periodic
      (fun r' => periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))
        r r' beta) (2 * Real.pi) := fun r beta => periodizeRow_periodic _ r beta
  obtain ⟨htwo, hquant⟩ := lemma_distinct_of_concreteLowering hlambda hkB hper
    (concreteLoweringFormula_correction hlambda a p)
  refine ⟨htwo, ?_⟩
  have hscale : rawDiagonalPart (p 1)
      (scaleRaw 1 (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) =
      rawDiagonalPart (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) := by
    funext alpha beta
    rw [rawDiagonalPart_scaleRaw, one_mul]
  rw [hscale, norm_one, one_pow, one_mul] at hquant
  exact hquant

/-- **Lemma 5.3 for the competitor, with the right-hand side evaluated.**  The
coincident-row projection error of the paper's explicit correction is at most
twice the scalar energy of (30), and the raw/projected lowering difference has
no two-row component. -/
theorem lemma_distinct_correction_sigmaEnergy {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (hK : 1 ≤ q.K) (hrho : 0 ≤ q.rho)
    (hrhopi : 3 * q.rho < Real.pi) {a : ℝ} (ha : 0 ≤ a) (p : Fin 2 → ℝ)
    (hp : |p 1| ≤ a) :
    (rawProjectionDifference 1 1 (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) 0
        (rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))))).twoRow = 0 ∧
      projectionErrorHMinusSq q
          (rawDiagonalPart (p 1)
            (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1)))) ≤
        2 * correctionSigmaEnergy q a :=
  ⟨(lemma_distinct_correction hlambda a p).1,
    projectionErrorHMinusSq_correction_le_two_correctionSigmaEnergy hlambda hK
      hrho hrhopi ha hp⟩

/-- **The instantiating data are the competitor's own Walsh coefficients.**  The
two Finset data fed to `Manhattan.Glue.ConcreteLoweringFormula` above are not
chosen by fiat: the two-row datum is the genuine two-row component of
`D₂*k_p`, and the Fourier coefficients of the mixed datum are the genuine mixed
Walsh coefficients of `D₂*k_p`, both read with the `(shift)` phase of
`manuscript.tex:791-800`.  This is the exact analogue of
`Manhattan.Glue.shiftedTwoRowCoefficient_eq_loweringCoefficient` and
`Manhattan.Glue.mixedLoweredKernel_eq_loweringCoefficient`, for the actual
correction.
-/
theorem concreteLoweringFormula_correction_certified {q : Estimates.Parameters}
    (hlambda : 0 < q.lambda) (a : ℝ) (p : Fin 2 → ℝ) :
    ConcreteLoweringFormula 1 1 (p 1)
        (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))) 0
        (rawD2StarMixed (rawOffDiagonalPart (p 1)
          (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))))) ∧
      (∀ T : Type11Index, (0 : Type11Index → ℂ) T =
          Manhattan.type112DStarTwoRow p
            (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
              (by norm_num) hlambda a (p 0) (p 1)) T) ∧
      (∀ m n : ℤ, mixedFourierCoefficient
          (rawD2StarMixed (rawOffDiagonalPart (p 1)
            (periodizeRow (Estimates.correctionCoefficient 40 q a (p 1))))) m n =
        intCharacter (-m) (p 1) * intCharacter (-n) (p 0) *
          Manhattan.type112DStarMixed p
            (Manhattan.shiftedCorrectionType112Coefficients (kappa := 40)
              (by norm_num) hlambda a (p 0) (p 1))
            ⟨mixedPairFinset (m, n), isType12Index_mixedPairFinset m n⟩) :=
  ⟨concreteLoweringFormula_correction hlambda a p,
    fun T => (type112DStarTwoRow_shiftedCorrection_apply hlambda a (p 0) (p 1) p T).symm,
    fun m n => mixedFourierCoefficient_correction hlambda a p m n⟩

end

end Manhattan.Glue
