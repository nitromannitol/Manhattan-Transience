import Manhattan.Estimates.Competitor
import Manhattan.Model.LowDegree

/-!
# Concrete low-degree competitor boundary

The degree-one and type-`(1,1,2)` coefficient spaces are synthesized into
the actual concrete Walsh fiber here.  The driftless branch is discharged
by `g=0`.  The remaining proposition-valued interface is deliberately the
paper-specific corrected energy estimate; it cannot be manufactured from
the scalar denominator statements alone.

Paper: `manuscript.tex:640-661`, `manuscript.tex:773-822`, and
`manuscript.tex:1120-1128`.
-/

noncomputable section

open MeasureTheory Set

namespace Manhattan.Glue

/-- Coefficient data for the concrete `g=(f+k)/b` construction. -/
structure LowDegreeCompetitorData where
  rowFrequency :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))
  mixedCoefficient : ℓ²(Type112Index, ℂ)
  normalization : ℝ
  normalization_ne : normalization ≠ 0

/-- The actual Walsh-space competitor synthesized from low-degree data. -/
noncomputable def LowDegreeCompetitorData.competitor
    (d : LowDegreeCompetitorData) : WalshL2 :=
  (((d.normalization : ℝ) : ℂ)⁻¹) •
    (degreeOneFrequencySynthesis Axis.horizontal d.rowFrequency +
      type112WalshSynthesis d.mixedCoefficient)

/-- The constructed degree-one part really lies in Walsh degree one. -/
theorem LowDegreeCompetitorData.row_mem_degree
    (d : LowDegreeCompetitorData) :
    degreeOneFrequencySynthesis Axis.horizontal d.rowFrequency ∈
      walshDegree 1 := by
  let c : RowLineCoefficient := fourierBasis.repr d.rowFrequency
  change axisDegreeOneSynthesis Axis.horizontal c ∈ walshDegree 1
  let V : ℤ → ℂ →ₗᵢ[ℂ] WalshL2 := fun k =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      ((orthonormal_walshL2.comp
        (fun m : ℤ => ({(Axis.horizontal, m)} : Finset LineIndex)) (by
          intro m n h
          simpa using h)).1 k)
  let U : Submodule ℂ WalshL2 := ⨆ k, LinearMap.range (V k).toLinearMap
  have hrange : axisDegreeOneSynthesis Axis.horizontal c ∈
      U.topologicalClosure := by
    have hrange' : axisDegreeOneSynthesis Axis.horizontal c ∈
        LinearMap.range
          (orthonormal_walshL2.comp
            (fun k : ℤ => ({(Axis.horizontal, k)} : Finset LineIndex)) (by
              intro k l h
              simpa using h)).orthogonalFamily.linearIsometry.toLinearMap := ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ walshDegree 1 := by
    refine iSup_le fun k => ?_
    rintro _ ⟨a, rfl⟩
    change a • walshL2 {(Axis.horizontal, k)} ∈ walshDegree 1
    exact (walshDegree 1).smul_mem a (by
      simpa using walshL2_mem_degree {(Axis.horizontal, k)})
  exact U.topologicalClosure_minimal hU
    (Submodule.isClosed_topologicalClosure _) hrange

/-- The constructed correction really lies in Walsh degree three. -/
theorem LowDegreeCompetitorData.mixed_mem_degree
    (d : LowDegreeCompetitorData) :
    type112WalshSynthesis d.mixedCoefficient ∈ walshDegree 3 :=
  type112WalshSynthesis_mem_degree d.mixedCoefficient

/-- The driftless majorant is nonnegative for positive `lambda`. -/
theorem driftlessMajorant_nonneg {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) :
    0 ≤ Operator.driftlessMajorant lambda p := by
  unfold Operator.driftlessMajorant
  exact one_div_nonneg.mpr
    (add_nonneg hlambda.le (operatorTheta_nonneg p))

/-- The `g=0` branch has exactly the driftless energy. -/
theorem concrete_driftless_competitor (lambda : ℝ) (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) :
    ∃ g : WalshL2,
      (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g +
          (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
            hlambda (walshL2 ∅ - concreteFiberA p g) ≤
        Operator.driftlessMajorant lambda p := by
  refine ⟨0, ?_⟩
  rw [map_zero, sub_zero, concrete_hMinusEnergy_empty hlambda p]
  simp [Operator.DissipativeSkewPair.hEnergy,
    Operator.DissipativeSkewPair.H]

/-- Exact cancellation of the constant Walsh component in the corrected
high-frequency branch.  It is a construction invariant, not a requirement
on the separate `g=0` branch. -/
def LowDegreeCompetitorData.CancelsAt (d : LowDegreeCompetitorData)
    (p : Fin 2 → ℝ) : Prop :=
  inner ℂ (walshL2 ∅)
    (walshL2 ∅ - concreteFiberA p d.competitor) = 0

/-- Requiring exact cancellation at every frequency is inconsistent: at
`p=0`, skew-adjointness and `A₀ 1=0` force the residual constant to equal
one. -/
theorem not_all_frequency_exactCancellation :
    ¬(∀ p : Fin 2 → ℝ, ∃ d : LowDegreeCompetitorData, d.CancelsAt p) := by
  intro h
  obtain ⟨d, hd⟩ := h 0
  rw [LowDegreeCompetitorData.CancelsAt,
    inner_empty_residual_zero_frequency] at hd
  norm_num at hd

/-- Retired interface.  It demands a *horizontal* degree-one plus type-(1,1,2)
competitor at every frequency, whereas the paper exchanges rows and columns
first (`manuscript.tex:1156`).  It is unsatisfiable: see
`Manhattan.Glue.not_correctedLowDegreeCertificate`.  New consumers must use
`CorrectedCompetitorCertificate` below. -/
def CorrectedLowDegreeCertificate (r0 C : ℝ) : Prop :=
  0 < r0 ∧ r0 < 1 ∧ 1 ≤ C ∧
    ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ,
        p 0 ∈ Estimates.torus → p 1 ∈ Estimates.torus →
          ∃ d : LowDegreeCompetitorData,
            (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
                  lambda d.competitor +
                (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                  hlambda (walshL2 ∅ - concreteFiberA p d.competitor) ≤
              C * Operator.correctedMajorant r0 lambda p

/-- A corrected low-degree certificate, together with the proved `g=0`
branch, yields W5B's torus-restricted operator claim. -/
theorem competitorBoundClaimV2_of_correctedLowDegreeCertificate
    {r0 C : ℝ} (h : CorrectedLowDegreeCertificate r0 C) :
    Operator.CompetitorBoundClaimV2 concreteFiberEnvironment (walshL2 ∅) := by
  refine Estimates.competitorBoundClaimV2_of_two_branches
    concreteFiberEnvironment (walshL2 ∅) r0 C h.1 h.2.1
      (zero_le_one.trans h.2.2.1) ?_ ?_
  · intro lambda hlambda _ p _ _
    obtain ⟨g, hg⟩ := concrete_driftless_competitor lambda hlambda p
    refine ⟨g, hg.trans ?_⟩
    exact (le_mul_of_one_le_left (driftlessMajorant_nonneg hlambda p)
      h.2.2.1)
  · intro lambda hlambda hlambdaOne p hp0 hp1
    obtain ⟨d, hd⟩ := h.2.2.2 lambda hlambda hlambdaOne p hp0 hp1
    exact ⟨d.competitor, hd⟩

/-- The corrected certificate: the competitor is an arbitrary Walsh vector,
exactly as in Proposition 2.2 and as the row/column exchange at
`manuscript.tex:1156` requires.  This is the version that is provable. -/
def CorrectedCompetitorCertificate (r0 C : ℝ) : Prop :=
  0 < r0 ∧ r0 < 1 ∧ 1 ≤ C ∧
    ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
      ∀ p : Fin 2 → ℝ,
        p 0 ∈ Estimates.torus → p 1 ∈ Estimates.torus →
          ∃ g : WalshL2,
            (concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda g +
                (concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
                  hlambda (walshL2 ∅ - concreteFiberA p g) ≤
              C * Operator.correctedMajorant r0 lambda p

/-- A corrected competitor certificate, together with the proved `g=0`
branch, yields W5B's torus-restricted operator claim. -/
theorem competitorBoundClaimV2_of_correctedCompetitorCertificate
    {r0 C : ℝ} (h : CorrectedCompetitorCertificate r0 C) :
    Operator.CompetitorBoundClaimV2 concreteFiberEnvironment (walshL2 ∅) := by
  refine Estimates.competitorBoundClaimV2_of_two_branches
    concreteFiberEnvironment (walshL2 ∅) r0 C h.1 h.2.1
      (zero_le_one.trans h.2.2.1) ?_ ?_
  · intro lambda hlambda _ p _ _
    obtain ⟨g, hg⟩ := concrete_driftless_competitor lambda hlambda p
    refine ⟨g, hg.trans ?_⟩
    exact (le_mul_of_one_le_left (driftlessMajorant_nonneg hlambda p)
      h.2.2.1)
  · intro lambda hlambda hlambdaOne p hp0 hp1
    exact h.2.2.2 lambda hlambda hlambdaOne p hp0 hp1

/-- Exact version-2 Proposition 2.2 conclusion from the corrected
certificate. -/
theorem proposition_frequency_of_correctedCompetitorCertificate
    {r0 C : ℝ} (h : CorrectedCompetitorCertificate r0 C) :
    ∃ D : Operator.FiberEnvironment WalshL2,
      D.shift = environmentShift ∧
      D.omega = originSignMultiplier ∧
      ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
        ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
          ∀ p : Fin 2 → ℝ,
            p 0 ∈ Estimates.torus → p 1 ∈ Estimates.torus →
            ∃ g : WalshL2,
              (D.dissipativeSkewPair p).hEnergy lambda g +
                  (D.dissipativeSkewPair p).hMinusEnergy
                    hlambda (walshL2 ∅ - D.fiberA p g) ≤
                C * Operator.frequencyMajorant r0 lambda p := by
  refine ⟨concreteFiberEnvironment, rfl, rfl, ?_⟩
  exact competitorBoundClaimV2_of_correctedCompetitorCertificate h

/-- Exact version-2 Proposition 2.2 conclusion, conditional only on the
paper-specific corrected low-degree certificate above. -/
theorem proposition_frequency_of_correctedLowDegreeCertificate
    {r0 C : ℝ} (h : CorrectedLowDegreeCertificate r0 C) :
    ∃ D : Operator.FiberEnvironment WalshL2,
      D.shift = environmentShift ∧
      D.omega = originSignMultiplier ∧
      ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
        ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 →
          ∀ p : Fin 2 → ℝ,
            p 0 ∈ Estimates.torus → p 1 ∈ Estimates.torus →
            ∃ g : WalshL2,
              (D.dissipativeSkewPair p).hEnergy lambda g +
                  (D.dissipativeSkewPair p).hMinusEnergy
                    hlambda (walshL2 ∅ - D.fiberA p g) ≤
                C * Operator.frequencyMajorant r0 lambda p := by
  refine ⟨concreteFiberEnvironment, rfl, rfl, ?_⟩
  exact competitorBoundClaimV2_of_correctedLowDegreeCertificate h

end Manhattan.Glue
