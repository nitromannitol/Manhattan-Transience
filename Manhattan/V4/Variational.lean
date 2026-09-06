import Manhattan.Operator.Variational

/-!
# Version 4, Step 1: the variational bound by Cauchy-Schwarz

This file proves the competitor upper bound on the fixed-frequency resolvent
quadratic form by the two-line Cauchy-Schwarz argument of the Version 4
rewrite, replacing the appeal to Komorowski-Landim-Olla, Theorem 4.1.

The abstract setting is the one already fixed in
`Manhattan/Operator/Variational.lean`: a `DissipativeSkewPair` packages a
bounded self-adjoint `S` with `re ⟪S x, x⟫ ≤ 0` and a bounded skew-adjoint `A`;
`H lambda = lambda • I - S` satisfies `re ⟪H x, x⟫ ≥ lambda ‖x‖²`, so `H`,
`H + A` and `H - A` are all invertible by Lax-Milgram. Those facts are cited
from that file (`plus_bijective`, `minus_bijective`, `H_bijective`,
`hEquiv`, `minusEquiv`, `re_inner_A_self`, `re_inner_H_symm`) and are not
reproved here.

Writing `‖u‖₊² = re ⟪H u, u⟫ = hEnergy` and `‖u‖₋² = re ⟪u, H⁻¹ u⟫ =
hMinusEnergy`, and `r_lambda(V) = re ⟪V, (H - A)⁻¹ V⟫ = resolventQuadratic`,
the statement is

  `r_lambda(V) ≤ ‖g‖₊² + ‖V - A g‖₋²`   for every `g` with `re ⟪V, g⟫ = 0`.

The proof is:

* `z := (H - A)⁻¹ V`; since `re ⟪z, A z⟫ = 0`, `r_lambda(V) = ⟪z, H z⟫ = ‖z‖₊²`;
* `(H + A)* = H - A` together with `re ⟪V, g⟫ = 0` give
  `re ⟪z, (V - A g) - H g⟫ = ‖z‖₊²`;
* Young's inequality `2 re ⟪q, d⟫ - ‖d‖₊² ≤ ‖q‖₋²` (the `H`-weighted
  Cauchy-Schwarz, in the form that avoids square roots) gives
  `‖z‖₊² ≤ ‖(V - A g) - H g‖₋²`;
* expanding that dual norm, the cross term is `re ⟪V - A g, g⟫ =
  re ⟪V, g⟫ - re ⟪A g, g⟫ = 0`.

The hypothesis that the competitor lies in the Hilbert space (the `phi ∈ L²`
gap in the Version 4 argument) is carried here by the typing
`g : E`: no unbounded or merely formal competitor is allowed. A concrete part
instantiating `g` must therefore supply an honest membership proof.
-/

noncomputable section

open ComplexConjugate InnerProductSpace RCLike
open scoped ComplexConjugate InnerProduct

namespace Manhattan.V4

open Manhattan.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : DissipativeSkewPair E)

/-- `H⁻¹` inverts `H` on the left. -/
theorem hEquiv_symm_H {lambda : ℝ} (hlambda : 0 < lambda) (g : E) :
    (P.hEquiv hlambda).symm (P.H lambda g) = g :=
  (P.H_bijective hlambda).1 (P.H_apply_inverse hlambda (P.H lambda g))

/-- Young's inequality for the dual pair `‖·‖₊`, `‖·‖₋`: this is the weighted
Cauchy-Schwarz inequality `re ⟪q, d⟫ ≤ ‖q‖₋ ‖d‖₊` in the form that needs no
square roots. -/
theorem two_re_inner_sub_hEnergy_le {lambda : ℝ} (hlambda : 0 < lambda) (q d : E) :
    2 * re ⟪q, d⟫_ℂ - P.hEnergy lambda d ≤ P.hMinusEnergy hlambda q := by
  have hqy : P.H lambda ((P.hEquiv hlambda).symm q) = q := P.H_apply_inverse hlambda q
  have hnonneg : 0 ≤ P.hEnergy lambda ((P.hEquiv hlambda).symm q - d) :=
    P.hEnergy_nonneg hlambda.le _
  rw [DissipativeSkewPair.hEnergy] at hnonneg
  rw [DissipativeSkewPair.hEnergy, DissipativeSkewPair.hMinusEnergy]
  simp only [map_sub, inner_sub_left, inner_sub_right, map_sub, hqy] at hnonneg
  have hcross : re ⟪P.H lambda d, (P.hEquiv hlambda).symm q⟫_ℂ = re ⟪q, d⟫_ℂ := by
    rw [P.re_inner_H_symm lambda d ((P.hEquiv hlambda).symm q), hqy, inner_re_symm]
  rw [hcross] at hnonneg
  linarith

/-- The dual form is a quadratic form: the expansion of `‖q - H g‖₋²`. -/
theorem hMinusEnergy_sub_H {lambda : ℝ} (hlambda : 0 < lambda) (q g : E) :
    P.hMinusEnergy hlambda (q - P.H lambda g)
      = P.hMinusEnergy hlambda q - 2 * re ⟪q, g⟫_ℂ + P.hEnergy lambda g := by
  have hqy : P.H lambda ((P.hEquiv hlambda).symm q) = q := P.H_apply_inverse hlambda q
  rw [DissipativeSkewPair.hMinusEnergy, DissipativeSkewPair.hMinusEnergy,
    DissipativeSkewPair.hEnergy, map_sub, hEquiv_symm_H]
  have hcross :
      re ⟪P.H lambda g, (P.hEquiv hlambda).symm q⟫_ℂ = re ⟪q, g⟫_ℂ := by
    rw [P.re_inner_H_symm lambda g ((P.hEquiv hlambda).symm q), hqy, inner_re_symm]
  simp only [inner_sub_left, inner_sub_right, map_sub, hcross]
  ring

/-- **Version 4, Step 1.** For every competitor `g` in the Hilbert space with
`re ⟪V, g⟫ = 0`,

  `re ⟪V, (H - A)⁻¹ V⟫ ≤ ‖g‖₊² + ‖V - A g‖₋²`.

Proved by Cauchy-Schwarz, with no minimizer and no completing of the square. -/
theorem resolventQuadratic_le_cauchySchwarz {lambda : ℝ} (hlambda : 0 < lambda) (V g : E)
    (hg : re ⟪V, g⟫_ℂ = 0) :
    P.resolventQuadratic hlambda V
      ≤ P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g) := by
  set z := (P.minusEquiv hlambda).symm V with hzdef
  have hz : P.H lambda z - P.A z = V := P.minus_apply_inverse hlambda V
  -- (i) `re ⟪V, z⟫ = ⟪z, H z⟫`, since `re ⟪z, A z⟫ = 0`.
  have hstep1 : P.resolventQuadratic hlambda V = P.hEnergy lambda z := by
    rw [DissipativeSkewPair.resolventQuadratic, DissipativeSkewPair.hEnergy]
    show re ⟪V, z⟫_ℂ = re ⟪P.H lambda z, z⟫_ℂ
    rw [← hz, inner_sub_left, map_sub, P.re_inner_A_self, sub_zero]
  -- (ii) `(H + A)* = H - A` and mean zero.
  have hAskew : re ⟪z, P.A g⟫_ℂ = -re ⟪P.A z, g⟫_ℂ := by
    have h := congrArg re (P.A.adjoint_inner_left z g)
    rw [P.skewAdjoint_A] at h
    simp only [ContinuousLinearMap.neg_apply, inner_neg_left, map_neg] at h
    rw [inner_re_symm z (P.A g), inner_re_symm (P.A z) g]
    linarith
  have hHsymm : re ⟪z, P.H lambda g⟫_ℂ = re ⟪P.H lambda z, g⟫_ℂ :=
    (P.re_inner_H_symm lambda z g).symm
  have hVg : re ⟪P.H lambda z, g⟫_ℂ - re ⟪P.A z, g⟫_ℂ = 0 := by
    rw [← map_sub, ← inner_sub_left, hz]; exact hg
  have hstep2 : re ⟪z, (V - P.A g) - P.H lambda g⟫_ℂ = P.hEnergy lambda z := by
    simp only [inner_sub_right, map_sub]
    rw [hAskew, hHsymm]
    have hzV : re ⟪z, V⟫_ℂ = P.hEnergy lambda z := by
      rw [← hstep1, DissipativeSkewPair.resolventQuadratic, inner_re_symm]
    rw [hzV]
    linarith
  -- (iii) weighted Cauchy-Schwarz.
  have hstep3 : P.hEnergy lambda z ≤ P.hMinusEnergy hlambda ((V - P.A g) - P.H lambda g) := by
    have hY := two_re_inner_sub_hEnergy_le P hlambda ((V - P.A g) - P.H lambda g) z
    rw [inner_re_symm] at hY
    rw [hstep2] at hY
    linarith
  -- (iv) expand the dual norm; the cross term vanishes.
  have hcross : re ⟪V - P.A g, g⟫_ℂ = 0 := by
    rw [inner_sub_left, map_sub, P.re_inner_A_self, hg, sub_zero]
  rw [hMinusEnergy_sub_H P hlambda (V - P.A g) g, hcross] at hstep3
  rw [hstep1]
  linarith

/-- The driftless competitor `g = 0`, which needs no mean-zero hypothesis. -/
theorem resolventQuadratic_le_hMinusEnergy_cauchySchwarz {lambda : ℝ} (hlambda : 0 < lambda)
    (V : E) : P.resolventQuadratic hlambda V ≤ P.hMinusEnergy hlambda V := by
  simpa [DissipativeSkewPair.hEnergy, DissipativeSkewPair.hMinusEnergy] using
    resolventQuadratic_le_cauchySchwarz P hlambda V 0 (by simp)

/-- For the record: the Cauchy-Schwarz bound is a one-line consequence of the
completing-the-square bound `Manhattan.Operator.DissipativeSkewPair.resolventQuadratic_le`,
which holds for every `g` and therefore does not use the mean-zero hypothesis
at all. The completing-the-square statement is the stronger primitive; the
Cauchy-Schwarz proof above is the shorter route to it. -/
@[nolint unusedArguments]
theorem resolventQuadratic_le_cauchySchwarz_of_completingSquare {lambda : ℝ}
    (hlambda : 0 < lambda) (V g : E) (_hg : re ⟪V, g⟫_ℂ = 0) :
    P.resolventQuadratic hlambda V
      ≤ P.hEnergy lambda g + P.hMinusEnergy hlambda (V - P.A g) :=
  P.resolventQuadratic_le hlambda V g

end Manhattan.V4
