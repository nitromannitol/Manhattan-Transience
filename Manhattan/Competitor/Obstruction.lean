import Manhattan.Model.FiberInstance
import Manhattan.Operator.Frequency

/-!
# Obstruction to the raw-frequency competitor claim

The paper states Proposition 2.2 for a torus frequency
`p ∈ (-π, π]²` (`manuscript.tex:640-660`).  The frozen Lean claim instead
quantifies over every raw real representative.  This module proves that the
resulting statement is false: the concrete fiber is `2π`-periodic, whereas
the raw `maxFrequency` appearing in the asserted upper bound is unbounded.

No analytic estimate is used in this counterexample.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike
open scoped BigOperators ComplexConjugate InnerProduct

namespace Manhattan.Competitor

private def periodicFrequency (n : ℕ) : Fin 2 → ℝ :=
  ![(n : ℝ) * (2 * Real.pi), 0]

private theorem environmentShift_empty (x : Operator.Lattice) :
    environmentShift x (walshL2 ∅) = walshL2 ∅ := by
  simp

private theorem periodicFrequency_phase (n : ℕ) (i : Fin 2) :
    Complex.exp (Complex.I * (periodicFrequency n i : ℂ)) = 1 := by
  fin_cases i
  · simpa [periodicFrequency, mul_assoc, mul_left_comm, mul_comm] using
      Complex.exp_nat_mul_two_pi_mul_I n
  · simp [periodicFrequency]

private theorem periodicFrequency_phase_neg (n : ℕ) (i : Fin 2) :
    Complex.exp (-(Complex.I * (periodicFrequency n i : ℂ))) = 1 := by
  rw [Complex.exp_neg, periodicFrequency_phase]
  simp

private theorem concreteFiberS_periodicFrequency_empty (n : ℕ) :
    concreteFiberS (periodicFrequency n) (walshL2 ∅) = 0 := by
  have hshift (i : Fin 2) :
      phasedShift (periodicFrequency n) i (walshL2 ∅) = walshL2 ∅ := by
    simp [phasedShift, periodicFrequency_phase]
  have hadjoint (i : Fin 2) :
      ((phasedShift (periodicFrequency n) i)†) (walshL2 ∅) = walshL2 ∅ := by
    rw [phasedShift_adjoint]
    simp [periodicFrequency_phase_neg]
  have hsummand (i : Fin 2) :
      fiberSymmetricTerm (periodicFrequency n) i (walshL2 ∅) = 0 := by
    simp only [fiberSymmetricTerm, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, hshift, hadjoint]
    module
  simp [concreteFiberS, hsummand]

private theorem concreteFiberA_periodicFrequency_empty (n : ℕ) :
    concreteFiberA (periodicFrequency n) (walshL2 ∅) = 0 := by
  have hshift (i : Fin 2) :
      phasedShift (periodicFrequency n) i (walshL2 ∅) = walshL2 ∅ := by
    simp [phasedShift, periodicFrequency_phase]
  have hadjoint (i : Fin 2) :
      ((phasedShift (periodicFrequency n) i)†) (walshL2 ∅) = walshL2 ∅ := by
    rw [phasedShift_adjoint]
    simp [periodicFrequency_phase_neg]
  have hsummand (i : Fin 2) :
      (originSignMultiplier i ∘L fiberSkewTerm (periodicFrequency n) i)
          (walshL2 ∅) = 0 := by
    rw [ContinuousLinearMap.comp_apply, fiberSkewTerm,
      ContinuousLinearMap.sub_apply, hshift, hadjoint, sub_self, map_zero]
  rw [concreteFiberA, Fin.sum_univ_two]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    hsummand, add_zero, smul_zero]

private theorem fiberS_eq_concrete {D : Operator.FiberEnvironment WalshL2}
    (hshift : D.shift = environmentShift) :
    D.fiberS = concreteFiberS := by
  funext p
  rw [D.fiberS_formula, concreteFiberS_formula, hshift]

private theorem fiberA_eq_concrete {D : Operator.FiberEnvironment WalshL2}
    (hshift : D.shift = environmentShift)
    (homega : D.omega = originSignMultiplier) :
    D.fiberA = concreteFiberA := by
  funext p
  rw [D.fiberA_formula, concreteFiberA_formula, hshift, homega]

private theorem constant_norm : ‖walshL2 (∅ : Finset LineIndex)‖ = 1 := by
  exact orthonormal_walshL2.1 ∅

private theorem objective_lower_at_periodicFrequency
    (D : Operator.FiberEnvironment WalshL2)
    (hshift : D.shift = environmentShift)
    (homega : D.omega = originSignMultiplier)
    (n : ℕ) (g : WalshL2) :
    (1 / 25 : ℝ) ≤
      (D.dissipativeSkewPair (periodicFrequency n)).hEnergy 1 g +
        (D.dissipativeSkewPair (periodicFrequency n)).hMinusEnergy
          (lambda := 1) (by norm_num)
          (walshL2 ∅ - D.fiberA (periodicFrequency n) g) := by
  let p := periodicFrequency n
  let P := D.dissipativeSkewPair p
  let V : WalshL2 := walshL2 ∅
  let q : WalshL2 := V - D.fiberA p g
  have hone : (0 : ℝ) < 1 := by norm_num
  let y : WalshL2 := (P.hEquiv hone).symm q
  have hAV : D.fiberA p V = 0 := by
    rw [fiberA_eq_concrete hshift homega]
    exact concreteFiberA_periodicFrequency_empty n
  have hinner : inner ℂ q V = 1 := by
    have hAg : inner ℂ (D.fiberA p g) V = 0 := by
      rw [← (D.fiberA p).adjoint_inner_right g V,
        D.fiberA_skewAdjoint, ContinuousLinearMap.neg_apply, hAV]
      simp
    dsimp [q]
    rw [inner_sub_left, hAg]
    simp [V, constant_norm]
  have hqnorm : 1 ≤ ‖q‖ := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) q V
    rw [hinner, norm_one, constant_norm, mul_one] at hcs
    exact hcs
  have hy_eq : P.H 1 y = q := P.H_apply_inverse hone q
  have hSnorm : ‖P.S‖ ≤ 4 := by
    exact D.fiberS_norm_le p
  have hq_le : ‖q‖ ≤ 5 * ‖y‖ := by
    calc
      ‖q‖ = ‖P.H 1 y‖ := by rw [hy_eq]
      _ = ‖y - P.S y‖ := by simp [Operator.DissipativeSkewPair.H]
      _ ≤ ‖y‖ + ‖P.S y‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + 4 * ‖y‖ := by
        gcongr
        exact (P.S.le_opNorm y).trans (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg y))
      _ = 5 * ‖y‖ := by ring
  have hynorm : (1 / 5 : ℝ) ≤ ‖y‖ := by linarith
  have hyenergy : (1 / 25 : ℝ) ≤ P.hEnergy 1 y := by
    calc
      (1 / 25 : ℝ) = (1 / 5 : ℝ) ^ 2 := by norm_num
      _ ≤ ‖y‖ ^ 2 := (sq_le_sq₀ (by norm_num) (norm_nonneg y)).2 hynorm
      _ = 1 * ‖y‖ ^ 2 := by ring
      _ ≤ P.hEnergy 1 y := P.hEnergy_lower 1 y
  have hminus : (1 / 25 : ℝ) ≤ P.hMinusEnergy hone q := by
    rw [Operator.DissipativeSkewPair.hMinusEnergy]
    change (1 / 25 : ℝ) ≤ re (inner ℂ q y)
    rw [← hy_eq]
    exact hyenergy
  have hg_nonneg : 0 ≤ P.hEnergy 1 g := P.hEnergy_nonneg (by norm_num) g
  change (1 / 25 : ℝ) ≤ P.hEnergy 1 g + P.hMinusEnergy hone q
  linarith

private theorem maxFrequency_periodicFrequency (n : ℕ) :
    Operator.maxFrequency (periodicFrequency n) = (n : ℝ) * (2 * Real.pi) := by
  have hnonneg : 0 ≤ (n : ℝ) * (2 * Real.pi) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (by norm_num) Real.pi_pos.le)
  change max |(n : ℝ) * (2 * Real.pi)| |0| = (n : ℝ) * (2 * Real.pi)
  rw [abs_of_nonneg hnonneg, abs_zero, max_eq_left hnonneg]

private theorem frequencyLogScale_periodicFrequency
    {r0 : ℝ} (hr0Pos : 0 < r0) (hr0 : r0 < 1) {n : ℕ} (hn : 0 < n) :
    Operator.frequencyLogScale r0 1 (periodicFrequency n) = 1 := by
  have ha_nonneg : 0 ≤ (n : ℝ) * (2 * Real.pi) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hden_pos : 0 < Real.sqrt (1 : ℝ) + (n : ℝ) * (2 * Real.pi) := by
    positivity
  have hratio : r0 / (Real.sqrt (1 : ℝ) + (n : ℝ) * (2 * Real.pi)) ≤ 1 := by
    apply (div_le_one hden_pos).2
    have hden_ge : 1 ≤ Real.sqrt (1 : ℝ) + (n : ℝ) * (2 * Real.pi) := by
      norm_num
      exact ha_nonneg
    exact hr0.le.trans hden_ge
  have hratio_nonneg :
      0 ≤ r0 / (Real.sqrt (1 : ℝ) + (n : ℝ) * (2 * Real.pi)) :=
    div_nonneg hr0Pos.le hden_pos.le
  have hlog : Real.log
      (r0 / (Real.sqrt (1 : ℝ) + (n : ℝ) * (2 * Real.pi))) ≤ 0 :=
    Real.log_nonpos hratio_nonneg hratio
  norm_num at hlog
  simp [Operator.frequencyLogScale, Operator.logPos,
    maxFrequency_periodicFrequency, hlog]

private theorem frequencyMajorant_periodicFrequency_le
    {r0 : ℝ} (hr0Pos : 0 < r0) (hr0 : r0 < 1) {n : ℕ} (hn : 0 < n) :
    Operator.frequencyMajorant r0 1 (periodicFrequency n) ≤
      1 / (((n : ℝ) * (2 * Real.pi)) ^ 2) := by
  refine (min_le_right _ _).trans_eq ?_
  rw [Operator.correctedMajorant, maxFrequency_periodicFrequency,
    frequencyLogScale_periodicFrequency hr0Pos hr0 hn]
  have hne : (n : ℝ) * (2 * Real.pi) ≠ 0 := by positivity
  simp [hne]

/-- The raw-frequency `CompetitorBoundClaim` cannot hold for any fiber whose
shift and sign fields are the concrete Manhattan environment fields.

The obstruction is the missing `p ∈ 𝕋²` restriction: at the representatives
`(2πn, 0)` the fiber operators agree with their value at zero, but the second
entry of `frequencyMajorant` tends to zero like `n⁻²`.
-/
theorem not_competitorBoundClaim_of_raw_frequency
    (D : Operator.FiberEnvironment WalshL2)
    (hshift : D.shift = environmentShift)
    (homega : D.omega = originSignMultiplier) :
    ¬ Operator.CompetitorBoundClaim D (walshL2 ∅) := by
  rintro ⟨r0, C, hr0, hr0One, hC, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (25 * C)
  have hnpos : 0 < n := by
    exact_mod_cast lt_of_le_of_lt (mul_nonneg (by norm_num) hC) hn
  let a : ℝ := (n : ℝ) * (2 * Real.pi)
  have ha_pos : 0 < a := by positivity
  have hCa : C / a ^ 2 < (1 / 25 : ℝ) := by
    rw [div_lt_iff₀ (sq_pos_of_pos ha_pos)]
    have hna : (n : ℝ) < a ^ 2 := by
      have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have htwoPi : (4 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
      have ha_ge : 4 * (n : ℝ) ≤ a := by
        dsimp [a]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left htwoPi (Nat.cast_nonneg n)
      nlinarith
    linarith
  obtain ⟨g, hg⟩ := hbound 1 (by norm_num) (by norm_num) (periodicFrequency n)
  have hmajorant := frequencyMajorant_periodicFrequency_le hr0 hr0One hnpos
  have hupper :
      (D.dissipativeSkewPair (periodicFrequency n)).hEnergy 1 g +
          (D.dissipativeSkewPair (periodicFrequency n)).hMinusEnergy
            (lambda := 1) (by norm_num)
            (walshL2 ∅ - D.fiberA (periodicFrequency n) g) ≤
        C / a ^ 2 := by
    refine hg.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hmajorant hC
    change C * Operator.frequencyMajorant r0 1 (periodicFrequency n) ≤ C / a ^ 2
    calc
      C * Operator.frequencyMajorant r0 1 (periodicFrequency n) ≤
          C * (1 / (((n : ℝ) * (2 * Real.pi)) ^ 2)) := hmul
      _ = C / a ^ 2 := by simp [a, div_eq_mul_inv]
  have hlower := objective_lower_at_periodicFrequency D hshift homega n g
  linarith

/-- Consequently, the current frozen Proposition 2.2 statement has no
witness.  A successor must restrict frequencies to torus representatives (or
make the radius periodic) before the analytic hypotheses can be used. -/
theorem not_proposition_frequency :
    ¬ (∃ D : Operator.FiberEnvironment WalshL2,
      D.shift = environmentShift ∧
      D.omega = originSignMultiplier ∧
      Operator.CompetitorBoundClaim D (walshL2 ∅)) := by
  rintro ⟨D, hshift, homega, hclaim⟩
  exact not_competitorBoundClaim_of_raw_frequency D hshift homega hclaim

end Manhattan.Competitor
