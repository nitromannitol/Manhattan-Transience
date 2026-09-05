import Manhattan.Operator.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fixed-frequency input and uniform assembly

This file separates the model-specific competitor estimate from its abstract
operator consequence.  The raw-frequency `CompetitorBoundClaim` is retained
only for the frozen version-1 record and its refutation; the live interface is
the torus-restricted `CompetitorBoundClaimV2`.  Once that interface is
supplied, the one-sided variational inequality gives the resolvent bound
without any further probabilistic input.

The final part records the three-region integration argument.  Its only
improper integral is evaluated exactly, rather than hidden in an `O(1)`.

Paper: `manuscript.tex:640-681`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Manhattan.Operator

/-- `d(s) = 1 - cos(s)` from Proposition 2.1. -/
def dispersion (s : ℝ) : ℝ := 1 - Real.cos s

/-- `theta(p) = d(p_1) + d(p_2)`. -/
def theta (p : Fin 2 → ℝ) : ℝ := ∑ i, dispersion (p i)

/-- The square radius `a(p)`. -/
def maxFrequency (p : Fin 2 → ℝ) : ℝ := max |p 0| |p 1|

/-- Positive part of the logarithm. -/
def logPos (x : ℝ) : ℝ := max (Real.log x) 0

/-- The logarithmic scale in Proposition 2.2. -/
def frequencyLogScale (r0 lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  1 + logPos (r0 / (Real.sqrt lambda + maxFrequency p))

/-- The first, driftless entry in (13). -/
def driftlessMajorant (lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  1 / (lambda + theta p)

/-- The second entry in (13).  At zero frequency it is replaced by the first
entry; this has exactly the same effect after taking the minimum as the
paper's convention that the second entry is `+infinity`. -/
def correctedMajorant (r0 lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  if maxFrequency p = 0 then driftlessMajorant lambda p
  else 1 / (maxFrequency p ^ 2 * frequencyLogScale r0 lambda p ^ (3 / 2 : ℝ))

/-- The real-valued version of the minimum in (13). -/
def frequencyMajorant (r0 lambda : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  min (driftlessMajorant lambda p) (correctedMajorant r0 lambda p)

/-- The paper's chosen representatives of the one-dimensional torus. -/
def frequencyTorus : Set ℝ := Set.Ioc (-Real.pi) Real.pi

/-- Retired version-1 interface for the model-specific content of Proposition
2.2.  New consumers must use `CompetitorBoundClaimV2`.

The concrete environment/Walsh parts must construct this value.  Keeping it
as proposition-valued data avoids postulating a theorem about arbitrary
unitary actions, for which the logarithmic estimate would be false. -/
def CompetitorBoundClaim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : FiberEnvironment E) (V : E) : Prop :=
  ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
    ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
      ∃ g : E,
        (D.dissipativeSkewPair p).hEnergy lambda g +
            (D.dissipativeSkewPair p).hMinusEnergy
              hlambda (V - D.fiberA p g) ≤
          C * frequencyMajorant r0 lambda p

/-- Retired raw-frequency consequence retained for its frozen version-1
wrapper.  `frequency_resolvent_le_of_competitor_v2` is the live theorem. -/
theorem frequency_resolvent_le_of_competitor {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : FiberEnvironment E) (V : E) (h : CompetitorBoundClaim D V) :
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        (D.dissipativeSkewPair p).resolventQuadratic
            hlambda V ≤
          C * frequencyMajorant r0 lambda p := by
  obtain ⟨r0, C, hr0, hr01, hC, hcompetitor⟩ := h
  refine ⟨r0, C, hr0, hr01, hC, ?_⟩
  intro lambda hlambda hlambda1 p
  obtain ⟨g, hg⟩ := hcompetitor lambda hlambda hlambda1 p
  exact ((D.dissipativeSkewPair p).resolventQuadratic_le hlambda V g).trans hg

/-- Version-2 successor to `CompetitorBoundClaim`, restricted to the torus
fundamental domain as in Proposition 2.2 (`manuscript.tex:644-661`). -/
def CompetitorBoundClaimV2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : FiberEnvironment E) (V : E) : Prop :=
  ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
    ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
      p 0 ∈ frequencyTorus → p 1 ∈ frequencyTorus →
      ∃ g : E,
        (D.dissipativeSkewPair p).hEnergy lambda g +
            (D.dissipativeSkewPair p).hMinusEnergy
              hlambda (V - D.fiberA p g) ≤
          C * frequencyMajorant r0 lambda p

/-- Torus-restricted version-2 successor of
`frequency_resolvent_le_of_competitor`. -/
theorem frequency_resolvent_le_of_competitor_v2 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D : FiberEnvironment E) (V : E) (h : CompetitorBoundClaimV2 D V) :
    ∃ r0 C : ℝ, 0 < r0 ∧ r0 < 1 ∧ 0 ≤ C ∧
      ∀ (lambda : ℝ), ∀ hlambda : 0 < lambda, lambda ≤ 1 → ∀ p : Fin 2 → ℝ,
        p 0 ∈ frequencyTorus → p 1 ∈ frequencyTorus →
        (D.dissipativeSkewPair p).resolventQuadratic hlambda V ≤
          C * frequencyMajorant r0 lambda p := by
  obtain ⟨r0, C, hr0, hr01, hC, hcompetitor⟩ := h
  refine ⟨r0, C, hr0, hr01, hC, ?_⟩
  intro lambda hlambda hlambda1 p hp0 hp1
  obtain ⟨g, hg⟩ := hcompetitor lambda hlambda hlambda1 p hp0 hp1
  exact ((D.dissipativeSkewPair p).resolventQuadratic_le hlambda V g).trans hg

/-- The logarithmic tail in the square-annulus calculation. -/
def logarithmicTail : ℝ := ∫ u : ℝ in Set.Ioi 1, u ^ (-3 / 2 : ℝ)

/-- Exact evaluation of the integral displayed at `manuscript.tex:675-677`. -/
theorem logarithmicTail_eq_two : logarithmicTail = 2 := by
  rw [logarithmicTail, integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- `-- INTERFACE`: the geometric output of splitting the normalized torus
into the small square, logarithmic square annuli, and the outer region.

`middleCoefficient` includes the harmless square-annulus Jacobian and the
constant in the frequency bound. -/
structure RegionalIntegralBounds (green : ℝ → ℝ) where
  smallBound : ℝ
  middleCoefficient : ℝ
  outerBound : ℝ
  small_nonneg : 0 ≤ smallBound
  middle_nonneg : 0 ≤ middleCoefficient
  outer_nonneg : 0 ≤ outerBound
  bound : ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 →
    green lambda ≤ smallBound + middleCoefficient * logarithmicTail + outerBound

/-- Uniform bound obtained from the three regions and the exact tail
integral.  This is the final analytic implication used for Theorem 1.2. -/
theorem uniform_green_bound_of_regional_bounds {green : ℝ → ℝ}
    (B : RegionalIntegralBounds green) {lambda : ℝ}
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    green lambda ≤ B.smallBound + 2 * B.middleCoefficient + B.outerBound := by
  rw [← logarithmicTail_eq_two]
  convert B.bound lambda hlambda hlambda1 using 1
  all_goals ring

end Manhattan.Operator
