import Manhattan.V4.MixedSector
import Manhattan.Estimates.LineResolvent

/-!
# Version 4, Move 1: the two-row half of the degree-two sector (residue B-2)

(B-2) records the `2 s² J(μ)` summand of
estimate (4) as open.  `Manhattan.V4.rawD2StarTwoRow_offDiagonalPart`
gives `(D₂*k)₁₁ = 0`, so the two-row degree-two sector is carried entirely by the
raising half `D₁f_p`, and the sealed
`Manhattan.Glue.hMinusEnergy_twoRowRaiseCoeff_le` already bounds its dual energy
by `4 R(μ) s² ‖c‖²`, where `R(μ)` is the `α`-average of the two-row `H⁻¹`
weight.  What was missing is the evaluation of that average, and it is the
closed form of `Manhattan/Estimates/LineResolvent.lean`:

  `R(μ) = ∫ dm(α)/(μ + d(α)) = 1/√(μ(μ+2)) = J(μ)`,   `μ = λ + d(p₁)`.

So the constant is `4 s² J(μ)`, not the manuscript's `2 s² J(μ)`; the factor two
comes from the parallelogram bound across the two frequency slices inside the
sealed lemma and is absorbed into `C₁` in `Manhattan/V4/Move1.lean`.
-/

noncomputable section
open MeasureTheory

namespace Manhattan.V4

open Manhattan.Glue

/-- The `α`-average of the two-row `H⁻¹` weight is the closed form
`J(μ) = 1/√(μ(μ+2))` of `Manhattan/Estimates/LineResolvent.lean`. -/
theorem twoRowWeightAverage_eq {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p₁ : ℝ) :
    twoRowWeightAverage q p₁
      = (Real.sqrt ((q.lambda + Estimates.dispersion p₁)
          * (q.lambda + Estimates.dispersion p₁ + 2)))⁻¹ := by
  have hmu : 0 < q.lambda + Estimates.dispersion p₁ :=
    add_pos_of_pos_of_nonneg hlam (Estimates.dispersion_nonneg p₁)
  have h := Estimates.lineResolventIdentity_proved (q.lambda + Estimates.dispersion p₁) hmu
  rw [twoRowWeightAverage, ← h]
  congr 1

/-- The `ℓ²` norm of the shifted row Fourier coefficients is the torus mass of
the profile. -/
theorem norm_sq_rowCoefficient {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) (s : ℝ) :
    ‖fourierBasis.repr (rowTorusShift s (Manhattan.realTorusL2 f hf))‖ ^ 2
      = Estimates.torusIntegral (fun r => ‖f r‖ ^ 2) := by
  rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map, norm_sq_realTorusL2]

/-- **(B-2) The two-row half of the degree-two sector.**  The dual energy of the
two-row degree-two component of `D₁f_p` is at most `4 s² J(μ)` times the torus
mass of the row profile, `s = sin p₁`, `μ = λ + d(p₁)`,
`J(μ) = 1/√(μ(μ+2))`.  `rawD2StarTwoRow_offDiagonalPart` makes this
the whole two-row sector: the lowering half is identically zero. -/
theorem hMinusEnergy_twoRow_le {q : Estimates.Parameters} (hlam : 0 < q.lambda)
    (p : Fin 2 → ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy hlam
        (Manhattan.type11WalshSynthesis (Manhattan.type11WalshAnalysis
          (walshRaise p (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
            (fourierBasis.repr (rowTorusShift (p 1)
              (Manhattan.realTorusL2 f hf)))))))
      ≤ 4 * (Real.sin (p 0) ^ 2
            / Real.sqrt ((q.lambda + Estimates.dispersion (p 0))
              * (q.lambda + Estimates.dispersion (p 0) + 2)))
          * Estimates.torusIntegral (fun r => ‖f r‖ ^ 2) := by
  have h := hMinusEnergy_twoRowRaiseCoeff_le hlam p
    (fourierBasis.repr (rowTorusShift (p 1) (Manhattan.realTorusL2 f hf)))
  rw [twoRowWeightAverage_eq hlam (p 0)] at h
  rw [norm_sq_rowCoefficient hf (p 1)] at h
  refine h.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

end Manhattan.V4
