import Manhattan.Glue.SummandFourAssembly
import Manhattan.V4.OperatorEstimate

/-!
# Lemma 5.2 for every degree-three element

`lem:four` (`manuscript.tex:1200-1207`) states that there is a universal
constant `κ` such that, for the multiplier `M` of `eq:M` and every `k ∈ ℋ₃`,

  `⟨k, H₃ k⟩ + ‖D₃ k‖²_{H⁻¹} ≤ ⟨k, M k⟩`.

Every `k ∈ ℋ₃` is `homogeneousWalshSynthesis 3 g` for a square-summable
degree-three Walsh coefficient `g` (`Manhattan.Glue.walshDegree_eq_range`).
The multiplier `M` depends only on the total frequency, so its quadratic form
is the integral of `M(P)` against the squared modulus of the line-frequency
coefficient of `g`, summed over the axis patterns.

The two terms on the left are `Manhattan.Glue.sectorHThreeForm`, the `H`
energy, and `Manhattan.Glue.sectorDFourForm`, the `H⁻¹` energy of the
degree-four component of `A_p k`, which is `D₃ k`.

The lemma holds with `κ = 97`.  The `H₃` term costs `1`, because
`λ + θ(P) ≤ M(P)/κ`.  The degree-four term costs `8 · 12`: the factor `2`
splits the two raising directions, the factor `2` is the raising energy bound
of one direction (`Manhattan.Glue.tsum_integral_inv_symbolWeight_degreeRaiseDir_le`),
which holds at `κ = 12`, and the multiplier is linear in `κ`.  The paper's
proof bounds the square of the four-term sum of `eq:raise` by four times the
sum of squares and absorbs the finitely many terms by increasing `κ`; the
proof here organizes the same estimate by direction instead of by slot.
-/

open MeasureTheory UnitAddTorus
open Manhattan Manhattan.Glue

namespace Manhattan.Paper

/-- The `H₃` term of `lem:four` is bounded by the quadratic form of `M` at `κ = 1`. -/
theorem sectorHThreeForm_le_multiplierForm (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) (g : DegreeCoefficient 3) :
    sectorHThreeForm q.lambda p (homogeneousWalshSynthesis 3 g) ≤
      ∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier 1 q (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
  have hform : sectorHThreeForm q.lambda p (homogeneousWalshSynthesis 3 g) =
      ∑' σ : Fin 3 → Axis, ∫ t, symbolWeight 3 q.lambda p σ t *
        ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
    rw [← re_inner_coeffH_eq_integral 3 q.lambda p g, sectorHThreeForm_eq, hThreeForm,
      fiberH_homogeneousWalshSynthesis, (homogeneousWalshSynthesis 3).inner_map_map]
  rw [hform, tsum_fintype, tsum_fintype]
  refine Finset.sum_le_sum fun σ _ => integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards with t
    exact mul_nonneg (symbolWeight_pos 3 hlambda p σ t).le (sq_nonneg _)
  · exact integrable_multiplier_norm_sq zero_le_one hlambda.le 3 p σ _
  · filter_upwards with t
    exact mul_le_mul_of_nonneg_right (V4.symbolWeight_le_multiplier_one p σ t) (sq_nonneg _)

/-- The degree-four term of `lem:four` is bounded by eight times the quadratic
form of `M` at `κ = 12`. -/
theorem sectorDFourForm_le_multiplierForm (q : Estimates.Parameters)
    (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ) (g : DegreeCoefficient 3) :
    sectorDFourForm hlambda p (homogeneousWalshSynthesis 3 g) ≤
      8 * ∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier 12 q (totalFrequency 3 p σ t) *
        ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
        ∂(LineTorusMeasure 3) := by
  have hsplit := sectorDFourForm_le_dir_integrals hlambda p
    (homogeneousWalshSynthesis_mem_degree 3 g) (fun i => degreeRaiseDir p i g)
    (fun i => homogeneousWalshSynthesis_degreeRaiseDir p i g)
  have h0 := tsum_integral_inv_symbolWeight_degreeRaiseDir_le (le_refl (12 : ℝ)) hlambda p 0 g
  have h1 := tsum_integral_inv_symbolWeight_degreeRaiseDir_le (le_refl (12 : ℝ)) hlambda p 1 g
  linarith

/-- **`lem:four` in coefficients.**  For every square-summable degree-three
Walsh coefficient `g`, with `k = homogeneousWalshSynthesis 3 g`,
`⟨k, H₃ k⟩ + ‖D₃ k‖²_{H⁻¹} ≤ ⟨k, M k⟩` for the multiplier `M` of `eq:M` with
`κ = 97`, and the integrands of `⟨k, M k⟩` are integrable. -/
theorem lemma_four_coefficient (q : Estimates.Parameters) (hlambda : 0 < q.lambda)
    (p : Fin 2 → ℝ) (g : DegreeCoefficient 3) :
    (∀ σ : Fin 3 → Axis, Integrable (fun t =>
        Estimates.multiplier 97 q (totalFrequency 3 p σ t) *
          ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
        (LineTorusMeasure 3)) ∧
      sectorHThreeForm q.lambda p (homogeneousWalshSynthesis 3 g) +
          sectorDFourForm hlambda p (homogeneousWalshSynthesis 3 g) ≤
        ∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier 97 q (totalFrequency 3 p σ t) *
          ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
          ∂(LineTorusMeasure 3) := by
  refine ⟨fun σ => integrable_multiplier_norm_sq (by norm_num) hlambda.le 3 p σ _, ?_⟩
  have hH := sectorHThreeForm_le_multiplierForm q hlambda p g
  have hD := sectorDFourForm_le_multiplierForm q hlambda p g
  have e12 := tsum_integral_multiplier_eq_smul 12 q (LineTorusMeasure 3)
    (fun σ t => totalFrequency 3 p σ t)
    (fun σ t => ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
  have e97 := tsum_integral_multiplier_eq_smul 97 q (LineTorusMeasure 3)
    (fun σ t => totalFrequency 3 p σ t)
    (fun σ t => ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
  simp only at e12 e97
  rw [e12] at hD
  rw [e97]
  linarith

/-- **`lem:four`** (`manuscript.tex:1200-1207`).  There is a universal
constant `κ > 0` such that for every `λ > 0`, every `p`, and every `k ∈ ℋ₃`,
the degree-three coefficient `g` of `k` satisfies
`⟨k, H₃ k⟩ + ‖D₃ k‖²_{H⁻¹} ≤ ⟨k, M k⟩`, the right side being the quadratic
form of the multiplier `M` of `eq:M` with integrable integrands. -/
theorem lemma_four :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (q : Estimates.Parameters) (hlambda : 0 < q.lambda) (p : Fin 2 → ℝ),
      ∀ k ∈ Manhattan.walshDegree 3, ∃ g : DegreeCoefficient 3,
        homogeneousWalshSynthesis 3 g = k ∧
        (∀ σ : Fin 3 → Axis, Integrable (fun t =>
            Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
              ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2)
            (LineTorusMeasure 3)) ∧
        sectorHThreeForm q.lambda p k + sectorDFourForm hlambda p k ≤
          ∑' σ : Fin 3 → Axis, ∫ t, Estimates.multiplier kappa q (totalFrequency 3 p σ t) *
            ‖((lineIndexFourier 3 g) σ : UnitAddTorus (Fin 3) → ℂ) t‖ ^ 2
            ∂(LineTorusMeasure 3) := by
  refine ⟨97, by norm_num, fun q hlambda p k hk => ?_⟩
  have hk' : k ∈ (Manhattan.walshDegree 3 : Set WalshL2) := hk
  rw [walshDegree_eq_range] at hk'
  obtain ⟨g, rfl⟩ := hk'
  exact ⟨g, rfl, lemma_four_coefficient q hlambda p g⟩

end Manhattan.Paper
