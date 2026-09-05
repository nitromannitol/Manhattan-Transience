import Manhattan.Glue.Discharge
import Manhattan.Glue.CubicDischargeProjection
import Manhattan.Glue.Summands
import Manhattan.Glue.TransportDischarge

/-!
# Final assembly of the chain to Theorems 1.1 and 1.2

`Manhattan/Glue/Discharge.lean` reduces the whole formalization to the single
named statement `Manhattan.Glue.ConcreteSectorEnergyBound M`, which is the
paper's estimate (23) `E_p(f_p,k_p) ≤ C √L` for the four-sector form (22) at
the concrete competitor of `Glue/Correction.lean`, and
`Manhattan/Glue/Summands.lean` splits (23) into four summand statements, of
which the first is proved (`summandOneBound_proved`).

Lemma 5.2 does not deliver summands 2 and 4 separately: it bounds the sum
`⟨k,H₃k⟩ + ‖D₃k‖²_{-1}` by the single scalar core of
`manuscript.tex:1196-1205`. This file therefore

* names the two cubic quadratic forms in the shape `CubicWalshIntertwining`
  expects (`sectorHThreeForm`, `sectorDFourForm`) and identifies their sum, at
  the concrete competitor, with summands 2 and 4 of (22)
  (`sector_two_add_four_eq_cubic`, proved by `rfl` after one rewrite);
* groups those two summands (`SummandTwoFourBound`) and closes the group from
  the two operator-sector statements of `Glue/CubicDischarge.lean` plus
  Proposition 4.2 (`summandTwoFourBound_of_cubicSectors`);
* supplies Proposition 4.2 for the corrected competitor's parameters in the
  high-logarithmic regime (`support_of_logThreshold`,
  `exists_propositionFiveTwo_corrected`);
* assembles (23) from summand 1 (proved), the grouped cubic pair, and
  summand 3 (`exists_concreteSectorEnergyBound_of_two_four_three`);
* and derives the three headline conclusions from (23)
  (`proposition_frequency_v2_of_exists`, `theorem_1_2_proved_of_exists`,
  `theorem_1_1_proved_of_exists`), which are the bodies the sealing wave puts
  in place of the four registered `DRAFT_SORRY` nodes.

**What the chain still awaits.** ONE named statement, and nothing else:
`Manhattan.Glue.SummandThreeBound C₃`.

`ConcreteDThreeRaisingBound` is **no longer on the route to (23)**. The formalization
proved summand 4 outright (`Manhattan.Glue.summandFourBound_proved`) and with it
the grouped pair (`Manhattan.Glue.exists_summandTwoFourBound`), both in
`Manhattan/Glue/SummandFourAssembly.lean`, so the live route is
`summandTwoFourBound_of_summands` and the `summandTwoFourBound_of_cubicSectors`
route, whose degree-four hypothesis `ConcreteDThreeRaisingBound` was, is
obsolete. Summands 1 and 2 were already discharged outright
(`Manhattan.Glue.summandOneBound_proved`,
`Manhattan.Glue.summandTwoBound_proved`); summand 2 became available once the
`(shift)` phase `Manhattan.type112ShiftTwist` carried by the competitor turned
frozen momentum `![0, -p 1]` into the objective's momentum `p`
exactly (`Manhattan.Glue.hThreeForm_type112ShiftTwist_frozen`), which is what
`Manhattan.Glue.concreteHThreeQuadraticBound` records for the degree-three
companion `ConcreteHThreeQuadraticBound`.

Paper: `manuscript.tex:769-790` (the objective and (23)),
`manuscript.tex:1196-1205` (Lemma 5.2), `manuscript.tex:1137-1154` (the
substitution).
-/
noncomputable section

namespace Manhattan.Glue

open Manhattan.Estimates MeasureTheory
open scoped ENNReal

/-- Summand 2 of (22), `⟨k,H₃k⟩`, as a quadratic form on `WalshL2`. -/
def sectorHThreeForm (lambda : ℝ) (p : Fin 2 → ℝ) : WalshL2 → ℝ := fun x =>
  (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda x

/-- Summand 4 of (22), `‖D₃k‖²_{-1}`, as a quadratic form on `WalshL2`. -/
def sectorDFourForm {lambda : ℝ} (hlambda : 0 < lambda) (p : Fin 2 → ℝ) :
    WalshL2 → ℝ := fun x =>
  (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
    (walshSectorComponent (fun S => S.card = 4) (Manhattan.concreteFiberA p x))

/-- Sector projection is linear. -/
theorem walshSectorComponent_smul (P : Finset LineIndex → Prop) (z : ℂ)
    (x : WalshL2) :
    walshSectorComponent P (z • x) = z • walshSectorComponent P x := by
  have hana : Manhattan.walshSectorAnalysis P (z • x) =
      z • Manhattan.walshSectorAnalysis P x := by
    apply lp.ext
    funext S
    have hS : Manhattan.walshSectorAnalysis P (z • x) S =
        z * Manhattan.walshSectorAnalysis P x S := by
      rw [Manhattan.walshSectorAnalysis_apply,
        Manhattan.walshSectorAnalysis_apply, inner_smul_right]
    simpa using hS
  rw [walshSectorComponent, walshSectorComponent, hana, map_smul]

/-- Summand 2 is a quadratic form. -/
theorem sectorHThreeForm_smul (lambda : ℝ) (p : Fin 2 → ℝ) (z : ℂ)
    (x : WalshL2) :
    sectorHThreeForm lambda p (z • x) = ‖z‖ ^ 2 * sectorHThreeForm lambda p x :=
  hEnergy_smul _ lambda z x

/-- Summand 4 is a quadratic form. -/
theorem sectorDFourForm_smul {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (z : ℂ) (x : WalshL2) :
    sectorDFourForm hlambda p (z • x) = ‖z‖ ^ 2 * sectorDFourForm hlambda p x := by
  show (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
      hlambda (walshSectorComponent (fun S => S.card = 4)
        (Manhattan.concreteFiberA p (z • x))) = _
  rw [map_smul, walshSectorComponent_smul, hMinusEnergy_smul]
  rfl

/-- The manuscript's `sgn(sin p₁)` multiplier of `manuscript.tex:1138-1141`
does not increase summand 4: it is zero or unimodular. -/
theorem sectorDFourForm_ofReal_sign_smul_le {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (x : ℝ) (v : WalshL2) :
    sectorDFourForm hlambda p (((Real.sign x : ℝ) : ℂ) • v) ≤
      sectorDFourForm hlambda p v := by
  rw [sectorDFourForm_smul]
  have h1 := norm_ofReal_sign_sq_le_one x
  have h2 : 0 ≤ sectorDFourForm hlambda p v := hMinusEnergy_nonneg _ hlambda _
  nlinarith

theorem sector_four_residual_eq {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (d : LowDegreeCompetitorData) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlambda
        (walshSectorComponent (fun S => S.card = 4)
          (unnormalizedResidual p d.normalization (correctedRowVector d)
            (correctedMixedVector d))) =
      sectorDFourForm hlambda p (correctedMixedVector d) :=
  hMinusEnergy_sector_four_residual hlambda p d.normalization
    (correctedRowVector_mem d)


/-- The paper's summands 2 and 4 of (22), evaluated at the concrete
competitor, are exactly the two sector forms of Lemma 5.2 evaluated at the
projected correction `k_p`. -/
theorem sector_two_add_four_eq_cubic {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ (p 0) ≠ 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
          (correctedMixedVector
            (correctedLowDegreeData hlambda p hcert hnormalization)) +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (walshSectorComponent (fun S => S.card = 4)
            (unnormalizedResidual p
              (correctedLowDegreeData hlambda p hcert hnormalization).normalization
              (correctedRowVector
                (correctedLowDegreeData hlambda p hcert hnormalization))
              (correctedMixedVector
                (correctedLowDegreeData hlambda p hcert hnormalization)))) =
      ‖((Real.sign (Real.sin (p 0)) : ℝ) : ℂ)‖ ^ 2 *
        (sectorHThreeForm lambda p
          (shiftedCorrectionWalsh (kappa := 40) (by norm_num)
            (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
            hlambda |p 0| (p 0) (p 1)) +
        sectorDFourForm hlambda p
          (shiftedCorrectionWalsh (kappa := 40) (by norm_num)
            (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
            hlambda |p 0| (p 0) (p 1))) := by
  rw [sector_four_residual_eq hlambda p
    (correctedLowDegreeData hlambda p hcert hnormalization)]
  have hmix : correctedMixedVector
      (correctedLowDegreeData hlambda p hcert hnormalization) =
      ((Real.sign (Real.sin (p 0)) : ℝ) : ℂ) •
        shiftedCorrectionWalsh (kappa := 40) (by norm_num)
          (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
          hlambda |p 0| (p 0) (p 1) := by
    rw [correctedMixedVector_eq]
    exact correctedLowDegreeData_mixed_eq hlambda p hcert hnormalization
  rw [hmix]
  show sectorHThreeForm lambda p
      (((Real.sign (Real.sin (p 0)) : ℝ) : ℂ) • _) +
      sectorDFourForm hlambda p
        (((Real.sign (Real.sin (p 0)) : ℝ) : ℂ) • _) = _
  rw [sectorHThreeForm_smul, sectorDFourForm_smul]
  ring


/-- Summands 2 and 4 of (22) together, for the concrete competitor, from the
two operator-sector bounds of Lemma 5.2 and Proposition 4.2. -/
theorem sector_two_add_four_le_of_cubicSectors {lambda : ℝ}
    (hlambda : 0 < lambda) (p : Fin 2 → ℝ) {C : ℝ}
    (horder : |p 1| ≤ |p 0|)
    (hH : ConcreteHThreeQuadraticBound
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ hlambda
      |p 0| (p 0) (p 1) (sectorHThreeForm lambda p))
    (hD : ConcreteDThreeRaisingBound
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ hlambda
      |p 0| (p 0) (p 1) (sectorDFourForm hlambda p))
    (hfive : Estimates.PropositionFiveTwoIntegralBound 40 C
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ |p 0|)
    (hcert : Estimates.LemmaFourTwoIntegralCertificate
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ (p 0) (p 1))
    (hnormalization : Estimates.degreeOneNormalization
      ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ (p 0) ≠ 0) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
          (correctedMixedVector
            (correctedLowDegreeData hlambda p hcert hnormalization)) +
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
          hlambda (walshSectorComponent (fun S => S.card = 4)
            (unnormalizedResidual p
              (correctedLowDegreeData hlambda p hcert hnormalization).normalization
              (correctedRowVector
                (correctedLowDegreeData hlambda p hcert hnormalization))
              (correctedMixedVector
                (correctedLowDegreeData hlambda p hcert hnormalization)))) ≤
      2 * C * Real.sqrt
        ((⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ :
          Estimates.Parameters).scaleLog |p 0|) := by
  rw [sector_two_add_four_eq_cubic hlambda p hcert hnormalization]
  have hbase := correctionWalsh_cubicEnergy_le_sqrtScale_of_sectors
    (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
    hlambda correctedCompetitorK_one_le correctedCompetitorRho_nonneg
    correctedCompetitorRho_three_lt_pi (abs_nonneg _) horder
    (sectorHThreeForm lambda p) (sectorDFourForm hlambda p) hH hD hfive
  have hnn : 0 ≤ sectorHThreeForm lambda p
        (shiftedCorrectionWalsh (kappa := 40) (by norm_num)
          (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
          hlambda |p 0| (p 0) (p 1)) +
      sectorDFourForm hlambda p
        (shiftedCorrectionWalsh (kappa := 40) (by norm_num)
          (q := ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩)
          hlambda |p 0| (p 0) (p 1)) :=
    add_nonneg
      ((Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy_nonneg
        hlambda.le _)
      (hMinusEnergy_nonneg _ hlambda _)
  have hsign := norm_ofReal_sign_sq_le_one (Real.sin (p 0))
  nlinarith


/-- The four summands of (22) with the cubic pair grouped: summand 1
separately, summands 2 and 4 together (that is how Lemma 5.2 delivers them),
and summand 3 separately. -/
theorem concreteSectorEnergyBound_of_grouped_summands {C₁ C₂₄ C₃ : ℝ}
    (hC₁ : 0 ≤ C₁)
    (h : ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
      lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ,
        p 0 ∈ Manhattan.Estimates.torus →
        p 1 ∈ Manhattan.Estimates.torus →
        |p 1| ≤ |p 0| →
        0 < |p 0| →
        let q : Manhattan.Estimates.Parameters :=
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
        q.logThreshold < q.scaleLog |p 0| →
        ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q
            (p 0) (p 1))
          (hnormalization : Manhattan.Estimates.degreeOneNormalization q
            (p 0) ≠ 0),
          let d := correctedLowDegreeData hlambda p hcert hnormalization
          (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda (correctedRowVector d) ≤ C₁ ∧
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                  lambda (correctedMixedVector d) +
                (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
                    p).hMinusEnergy hlambda
                  (walshSectorComponent (fun S => S.card = 4)
                    (unnormalizedResidual p d.normalization
                      (correctedRowVector d) (correctedMixedVector d))) ≤
              C₂₄ * Real.sqrt (q.scaleLog |p 0|) ∧
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair
                p).hMinusEnergy hlambda
              (walshSectorComponent (fun S => S.card = 2)
                (unnormalizedResidual p d.normalization (correctedRowVector d)
                  (correctedMixedVector d))) ≤
              C₃ * Real.sqrt (q.scaleLog |p 0|)) :
    ConcreteSectorEnergyBound (C₁ + C₂₄ + C₃) := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization d
  obtain ⟨h1, h24, h3⟩ :=
    h hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization
  have hsqrt : 1 ≤ Real.sqrt (q.scaleLog |p 0|) :=
    Real.one_le_sqrt.mpr (one_le_scaleLog q |p 0|)
  have hC₁scale : C₁ ≤ C₁ * Real.sqrt (q.scaleLog |p 0|) :=
    le_mul_of_one_le_right hC₁ hsqrt
  show sectorObjective hlambda p d.normalization (correctedRowVector d)
      (correctedMixedVector d) ≤
    (C₁ + C₂₄ + C₃) * Real.sqrt (q.scaleLog |p 0|)
  rw [sectorObjective]
  nlinarith [h1, h24, h3, hC₁scale]

/-- `sectorHThreeForm` is `hThreeForm` at the same momentum. -/
theorem sectorHThreeForm_eq (lambda : ℝ) (p : Fin 2 → ℝ) :
    sectorHThreeForm lambda p = hThreeForm lambda p := rfl

/-- In the high-logarithmic regime the support interval is nonempty. -/
theorem support_of_logThreshold {q : Estimates.Parameters}
    (hK : 1 < q.K) (hr0 : 0 < q.r0) (hlambda : 0 < q.lambda) {a : ℝ} (ha : 0 ≤ a)
    (hlog : q.logThreshold < q.scaleLog a) :
    q.K * q.delta a < q.r0 := by
  have hdelta : 0 < q.delta a := by
    have : 0 < Real.sqrt q.lambda := Real.sqrt_pos.mpr hlambda
    rw [Estimates.Parameters.delta]; linarith
  have hlogK : 0 < Real.log q.K := Real.log_pos hK
  have hpos : 2 * Real.log q.K + 2 < Estimates.logPos (q.r0 / q.delta a) := by
    rw [Estimates.Parameters.logThreshold, Estimates.Parameters.scaleLog] at hlog
    linarith
  have hposPos : 0 < Estimates.logPos (q.r0 / q.delta a) := by linarith
  have hlogEq : Estimates.logPos (q.r0 / q.delta a) = Real.log (q.r0 / q.delta a) := by
    rw [Estimates.logPos, max_eq_right]
    by_contra hcon
    push_neg at hcon
    rw [Estimates.logPos, max_eq_left hcon.le] at hposPos
    exact lt_irrefl _ hposPos
  rw [hlogEq] at hpos
  have hratioPos : 0 < q.r0 / q.delta a := div_pos hr0 hdelta
  have hKlt : Real.log q.K < Real.log (q.r0 / q.delta a) := by linarith
  have hKpos : (0:ℝ) < q.K := by linarith
  have hlt := (Real.log_lt_log_iff hKpos hratioPos).mp hKlt
  calc q.K * q.delta a < (q.r0 / q.delta a) * q.delta a :=
        mul_lt_mul_of_pos_right hlt hdelta
    _ = q.r0 := by field_simp

/-- Summands 2 and 4 of (22) together. -/
def SummandTwoFourBound (C : ℝ) : Prop :=
  ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda,
    lambda ≤ 1 →
    ∀ p : Fin 2 → ℝ,
      p 0 ∈ Manhattan.Estimates.torus →
      p 1 ∈ Manhattan.Estimates.torus →
      |p 1| ≤ |p 0| →
      0 < |p 0| →
      let q : Manhattan.Estimates.Parameters :=
        ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
      q.logThreshold < q.scaleLog |p 0| →
      ∀ (hcert : Manhattan.Estimates.LemmaFourTwoIntegralCertificate q (p 0) (p 1))
        (hnormalization : Manhattan.Estimates.degreeOneNormalization q (p 0) ≠ 0),
        let d := correctedLowDegreeData hlambda p hcert hnormalization
        (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
              lambda (correctedMixedVector d) +
            (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
              hlambda
              (walshSectorComponent (fun S => S.card = 4)
                (unnormalizedResidual p d.normalization (correctedRowVector d)
                  (correctedMixedVector d))) ≤
          C * Real.sqrt (q.scaleLog |p 0|)

theorem summandTwoFourBound_of_summands {C₂ C₄ : ℝ}
    (h2 : SummandTwoBound C₂) (h4 : SummandFourBound C₄) :
    SummandTwoFourBound (C₂ + C₄) := by
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  have a2 := h2 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization
  have a4 := h4 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization
  have : (C₂ + C₄) * Real.sqrt (q.scaleLog |p 0|)
      = C₂ * Real.sqrt (q.scaleLog |p 0|) + C₄ * Real.sqrt (q.scaleLog |p 0|) := by ring
  dsimp only
  rw [this]
  exact add_le_add a2 a4


/-- Proposition 4.2 for the corrected competitor's parameters, uniformly. -/
theorem exists_propositionFiveTwo_corrected :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lambda : ℝ}, 0 < lambda → lambda ≤ 1 → ∀ a : ℝ, 0 ≤ a →
        let q : Manhattan.Estimates.Parameters :=
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
        q.logThreshold < q.scaleLog a →
        Manhattan.Estimates.PropositionFiveTwoIntegralBound 40 C q a := by
  obtain ⟨c, C, hc, hC, hall⟩ :=
    Manhattan.Estimates.propositionFiveTwoClaim_proved
      correctedCompetitorK correctedCompetitorRho
      (by simp [correctedCompetitorK])
      (by simp only [correctedCompetitorRho]; positivity)
      (by simp [correctedCompetitorRho])
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda hlambdaOne a ha
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog a → _
  intro hlog
  have hK : (1:ℝ) < q.K := by simp [q, correctedCompetitorK]
  have hr0 : 0 < q.r0 := by
    simp only [q, Manhattan.Estimates.Parameters.r0, correctedCompetitorK,
      correctedCompetitorRho]
    positivity
  have hsupport : q.K * q.delta a < q.r0 :=
    support_of_logThreshold hK hr0 hlambda ha hlog
  exact (hall lambda hlambda hlambdaOne a ha hsupport).2.2


/-- Summands 2 and 4 from the two operator-sector statements of Lemma 5.2,
stated at the frozen momentum `p` of the objective. -/
theorem summandTwoFourBound_of_cubicSectors
    (hH : ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda, lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ, |p 1| ≤ |p 0| →
        ConcreteHThreeQuadraticBound
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ hlambda
          |p 0| (p 0) (p 1) (sectorHThreeForm lambda p))
    (hD : ∀ {lambda : ℝ}, ∀ hlambda : 0 < lambda, lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ, |p 1| ≤ |p 0| →
        ConcreteDThreeRaisingBound
          ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩ hlambda
          |p 0| (p 0) (p 1) (sectorDFourForm hlambda p)) :
    ∃ C : ℝ, 0 ≤ C ∧ SummandTwoFourBound C := by
  obtain ⟨C, hC, hfive⟩ := exists_propositionFiveTwo_corrected
  refine ⟨2 * C, by linarith, ?_⟩
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  exact sector_two_add_four_le_of_cubicSectors hlambda p horder
    (hH hlambda hlambdaOne p horder) (hD hlambda hlambdaOne p horder)
    (hfive hlambda hlambdaOne |p 0| (abs_nonneg _) hlog) hcert hnormalization

/-- **(23) from what is left.** Summand 1 is already proved, so the
paper's estimate (23) follows from the grouped cubic pair and summand 3. -/
theorem exists_concreteSectorEnergyBound_of_two_four_three {C₂₄ C₃ : ℝ}
    (hC₂₄ : 0 ≤ C₂₄) (hC₃ : 0 ≤ C₃)
    (h24 : SummandTwoFourBound C₂₄) (h3 : SummandThreeBound C₃) :
    ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M := by
  obtain ⟨C₁, hC₁, h1⟩ := summandOneBound_proved
  refine ⟨C₁ + C₂₄ + C₃, by linarith, ?_⟩
  refine concreteSectorEnergyBound_of_grouped_summands hC₁ ?_
  intro lambda hlambda hlambdaOne p hp₀ hp₁ horder hpositive
  let q : Manhattan.Estimates.Parameters :=
    ⟨lambda, correctedCompetitorK, correctedCompetitorRho⟩
  change q.logThreshold < q.scaleLog |p 0| → _
  intro hlog hcert hnormalization
  exact ⟨h1 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization,
    h24 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization,
    h3 hlambda hlambdaOne p hp₀ hp₁ horder hpositive hlog hcert hnormalization⟩

/-! ### The three headline conclusions, from (23) -/

theorem proposition_frequency_v2_of_exists
    (h : ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M) :
    PropositionFrequencyClaim := by
  obtain ⟨M, hM, hb⟩ := h
  exact proposition_frequency_v2_of_sectorEnergy hM hb

theorem theorem_1_2_proved_of_exists
    (h : ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M) :
    Manhattan.AnnealedGreenBound := by
  obtain ⟨M, hM, hb⟩ := h
  exact theorem_1_2_proved_of_sectorEnergy hM hb

theorem theorem_1_1_proved_of_exists
    (h : ∃ M : ℝ, 0 ≤ M ∧ ConcreteSectorEnergyBound M) :
    ∀ᵐ omega ∂Manhattan.environmentLaw,
      ∀ x : Manhattan.Site, Manhattan.discreteGreen omega x < ∞ := by
  obtain ⟨M, hM, hb⟩ := h
  exact theorem_1_1_proved_of_sectorEnergy hM hb

end Manhattan.Glue
