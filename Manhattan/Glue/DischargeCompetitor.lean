import Manhattan.Glue.Discharge
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The corrected low-degree certificate of `Glue/Competitor.lean`

`Manhattan.Glue.CorrectedLowDegreeCertificate` asks for a competitor of the
form `(f+k)/b` with `f` a *horizontal* degree-one function and `k` of type
`(1,1,2)` at **every** frequency of the torus.  The paper never asks for
that: at `manuscript.tex:1156` it exchanges rows and columns before running
the construction.

This file proves that the difference is real.  When `sin p₁ = 0` every such
competitor leaves the constant Walsh component untouched, so its objective is
at least the driftless majorant `1/(λ+θ(p))`, and at
`p=(0,s)`, `λ=s²`, `s` small this exceeds `C/(a²L^{3/2})`.  Hence
`CorrectedLowDegreeCertificate r0 C` is false for every `r0` and `C`.

The corrected interface, which is the one the paper actually states and the
one Proposition 2.2 consumes, quantifies over an arbitrary Walsh competitor;
it is discharged here from the single shared bound.

Paper: `manuscript.tex:640-661` and `manuscript.tex:1156`.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike

namespace Manhattan.Glue

section Young

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

open Manhattan.Operator

/-- Public form of the Young inequality for the dual energy: every test
vector gives a lower bound for `‖q‖²_{-1}`. -/
theorem young_hMinusEnergy (P : DissipativeSkewPair E) {lambda : ℝ}
    (hlambda : 0 < lambda) (q d : E) :
    2 * re ⟪q, d⟫_ℂ - P.hEnergy lambda d ≤ P.hMinusEnergy hlambda q := by
  let y := (P.hEquiv hlambda).symm q
  have hqy : P.H lambda y = q := P.H_apply_inverse hlambda q
  have hnonneg : 0 ≤ P.hEnergy lambda (y - d) :=
    P.hEnergy_nonneg hlambda.le (y - d)
  rw [DissipativeSkewPair.hEnergy] at hnonneg
  rw [DissipativeSkewPair.hEnergy, DissipativeSkewPair.hMinusEnergy]
  change 2 * re ⟪q, d⟫_ℂ - re ⟪P.H lambda d, d⟫_ℂ ≤ re ⟪q, y⟫_ℂ
  rw [← hqy]
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub] at hnonneg
  have hcross : re ⟪P.H lambda d, y⟫_ℂ = re ⟪P.H lambda y, d⟫_ℂ :=
    (P.re_inner_H_symm lambda d y).trans (inner_re_symm d (P.H lambda y))
  linarith

end Young

section ConstantResidual

/-- The degree-zero `H` energy is the driftless denominator. -/
theorem concrete_hEnergy_empty (lambda : ℝ) (p : Fin 2 → ℝ) :
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy lambda
        (Manhattan.walshL2 ∅) = lambda + Manhattan.Operator.theta p := by
  rw [Manhattan.Operator.DissipativeSkewPair.hEnergy, Manhattan.concreteH_empty,
    inner_smul_left, Manhattan.inner_walshL2, if_pos rfl]
  simp

/-- A residual whose constant Walsh component is one costs at least the
driftless majorant. -/
theorem driftlessMajorant_le_hMinusEnergy {lambda : ℝ} (hlambda : 0 < lambda)
    (p : Fin 2 → ℝ) (R : WalshL2)
    (hR : inner ℂ (Manhattan.walshL2 ∅) R = 1) :
    Manhattan.Operator.driftlessMajorant lambda p ≤
      (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hMinusEnergy
        hlambda R := by
  have hden : 0 < lambda + Manhattan.Operator.theta p :=
    add_pos_of_pos_of_nonneg hlambda (Manhattan.operatorTheta_nonneg p)
  set t : ℝ := (lambda + Manhattan.Operator.theta p)⁻¹ with ht
  have hyoung := young_hMinusEnergy
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p) hlambda R
    ((t : ℂ) • Manhattan.walshL2 ∅)
  have hRflip : inner ℂ R (Manhattan.walshL2 ∅) = (1 : ℂ) := by
    rw [← inner_conj_symm, hR, map_one]
  have h1 : re ⟪R, (t : ℂ) • Manhattan.walshL2 ∅⟫_ℂ = t := by
    rw [inner_smul_right, hRflip, mul_one]
    simp
  have h2 : (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
      lambda ((t : ℂ) • Manhattan.walshL2 ∅) =
      t ^ 2 * (lambda + Manhattan.Operator.theta p) := by
    rw [hEnergy_smul, concrete_hEnergy_empty]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at hyoung
  have hval : 2 * t - t ^ 2 * (lambda + Manhattan.Operator.theta p) =
      Manhattan.Operator.driftlessMajorant lambda p := by
    rw [Manhattan.Operator.driftlessMajorant, ht]
    field_simp
    norm_num
  rw [hval] at hyoung
  exact hyoung

/-- When `sin p₁ = 0` no horizontal low-degree competitor changes the
constant Walsh component. -/
theorem inner_empty_residual_of_sin_eq_zero (d : LowDegreeCompetitorData)
    (p : Fin 2 → ℝ) (hp : Real.sin (p 0) = 0) :
    inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p d.competitor) = 1 := by
  have hrow : inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.concreteFiberA p
        (Manhattan.degreeOneFrequencySynthesis Manhattan.Axis.horizontal
          d.rowFrequency)) = 0 := by
    change inner ℂ (Manhattan.walshL2 ∅)
      (Manhattan.concreteFiberA p
        (Manhattan.axisDegreeOneSynthesis Manhattan.Axis.horizontal
          (fourierBasis.repr d.rowFrequency))) = 0
    rw [Manhattan.inner_empty_concreteFiberA_axisDegreeOne, hp]
    simp
  rw [inner_sub_right, Manhattan.inner_walshL2, if_pos rfl,
    LowDegreeCompetitorData.competitor, map_smul, inner_smul_right, map_add,
    inner_add_right, hrow,
    Manhattan.inner_empty_concreteFiberA_type112 p d.mixedCoefficient]
  simp

end ConstantResidual

section Refutation

open Manhattan.Operator

/-- `Glue/Competitor.lean:117` is unsatisfiable.  At `p=(0,s)` with
`lambda=s²` every horizontal low-degree competitor leaves the constant Walsh
component intact, so its objective is at least `1/(lambda+theta(p))`, which is
larger than `C/(a²L^{3/2})` once `L` exceeds `(3C/2)^{2/3}`. -/
theorem not_correctedLowDegreeCertificate (r0 C : ℝ) :
    ¬ CorrectedLowDegreeCertificate r0 C := by
  rintro ⟨hr0, hr01, hC, hmain⟩
  have hexp : 0 < Real.exp (-(3 / 2 * C)) := Real.exp_pos _
  set s : ℝ := r0 * Real.exp (-(3 / 2 * C)) / 2 with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hexple : Real.exp (-(3 / 2 * C)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hshalf : s ≤ 1 / 2 := by rw [hsdef]; nlinarith
  have hspi : s ≤ Real.pi := by linarith [Real.pi_gt_three]
  set lam : ℝ := s ^ 2 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  have hlamle : lam ≤ 1 := by rw [hlamdef]; nlinarith
  set p : Fin 2 → ℝ := ![0, s] with hpdef
  have hp0 : p 0 = 0 := rfl
  have hp1 : p 1 = s := rfl
  have hmem0 : p 0 ∈ Manhattan.Estimates.torus := by
    rw [hp0]
    exact Set.mem_Ioc.mpr ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  have hmem1 : p 1 ∈ Manhattan.Estimates.torus := by
    rw [hp1]
    exact Set.mem_Ioc.mpr ⟨by linarith [Real.pi_pos], hspi⟩
  obtain ⟨d, hd⟩ := hmain lam hlampos hlamle p hmem0 hmem1
  have hsin : Real.sin (p 0) = 0 := by rw [hp0]; exact Real.sin_zero
  have hlower := driftlessMajorant_le_hMinusEnergy hlampos p
    (Manhattan.walshL2 ∅ - Manhattan.concreteFiberA p d.competitor)
    (inner_empty_residual_of_sin_eq_zero d p hsin)
  have hEnonneg :
      0 ≤ (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy
        lam d.competitor :=
    (Manhattan.concreteFiberEnvironment.dissipativeSkewPair p).hEnergy_nonneg
      hlampos.le _
  have hkey : driftlessMajorant lam p ≤ C * correctedMajorant r0 lam p := by
    linarith
  have hmax : maxFrequency p = s := by
    rw [maxFrequency, hp0, hp1, abs_zero, abs_of_pos hspos,
      max_eq_right hspos.le]
  have hmaxne : maxFrequency p ≠ 0 := by rw [hmax]; exact hspos.ne'
  have hsqrt : Real.sqrt lam = s := by rw [hlamdef]; exact Real.sqrt_sq hspos.le
  have hratio : r0 / (s + s) = Real.exp (3 / 2 * C) := by
    have h2s : s + s = r0 * Real.exp (-(3 / 2 * C)) := by rw [hsdef]; ring
    rw [h2s, Real.exp_neg]
    field_simp
  have hL : frequencyLogScale r0 lam p = 1 + 3 / 2 * C := by
    rw [frequencyLogScale, hsqrt, hmax, hratio, logPos, Real.log_exp,
      max_eq_left (by linarith)]
  set X : ℝ := (1 + 3 / 2 * C) ^ (3 / 2 : ℝ) with hXdef
  have hXge : 1 + 3 / 2 * C ≤ X := by
    rw [hXdef]
    calc
      1 + 3 / 2 * C = (1 + 3 / 2 * C) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + 3 / 2 * C) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hXpos : 0 < X := by linarith
  have hCM : correctedMajorant r0 lam p = 1 / (s ^ 2 * X) := by
    rw [correctedMajorant, if_neg hmaxne, hmax, hL, hXdef]
  have hDM : driftlessMajorant lam p = 1 / (lam + theta p) := rfl
  have htheta : theta p = 1 - Real.cos s := by
    rw [theta, Fin.sum_univ_two, hp0, hp1]
    simp [dispersion]
  have hthetale : theta p ≤ 1 / 2 * s ^ 2 := by
    rw [htheta]
    have h := Manhattan.Estimates.dispersion_le_half_mul_sq s
    rw [Manhattan.Estimates.dispersion] at h
    linarith
  have hthetanonneg : 0 ≤ theta p := Manhattan.operatorTheta_nonneg p
  have hden : 0 < lam + theta p := by linarith
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  rw [hDM, hCM] at hkey
  have hprod : s ^ 2 * X * (1 / (lam + theta p)) ≤
      s ^ 2 * X * (C * (1 / (s ^ 2 * X))) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hrhs : s ^ 2 * X * (C * (1 / (s ^ 2 * X))) = C := by
    field_simp
  have hlhs : s ^ 2 * X * (1 / (lam + theta p)) =
      s ^ 2 * X / (lam + theta p) := by ring
  rw [hrhs, hlhs, div_le_iff₀ hden] at hprod
  nlinarith [mul_le_mul_of_nonneg_left hXge hs2.le]

end Refutation

section Corrected

/-- Discharge of the corrected replacement for `Glue/Competitor.lean:117`. -/
theorem correctedCompetitorCertificate_of_sectorEnergy {M : ℝ} (hM : 0 ≤ M)
    (h : ConcreteSectorEnergyBound M) :
    ∃ r0 C : ℝ, CorrectedCompetitorCertificate r0 C := by
  obtain ⟨C, hC, hhoriz⟩ := correctedHorizontalEnergySupply_of_sectorEnergy hM h
  refine ⟨correctedCompetitorCutoff, C + correctedLowLogConstant + 1,
    correctedCompetitorCutoff_pos, correctedCompetitorCutoff_lt_one,
    by nlinarith [correctedLowLogConstant_nonneg], ?_⟩
  exact correctedCompetitor_all_frequencies_of_horizontal C hC hhoriz

end Corrected

end Manhattan.Glue
