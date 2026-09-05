import Manhattan.Walsh.Completeness
import Manhattan.Walsh.Fourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Complete homogeneous Walsh synthesis

This file upgrades the finite synthesis in `Coefficients.lean` to the complete
Finset-indexed Hilbert sums used by the competitor.  The index subtype carries
the homogeneous degree, so coincident line indices cannot occur.

Paper: `manuscript.tex:701-758`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Manhattan

noncomputable section

/-- Finite sets of line indices of homogeneous Walsh degree `n`. -/
abbrev WalshDegreeIndex (n : ℕ) := {S : Finset LineIndex // S.card = n}

/-- The homogeneous Walsh family, indexed only by `n`-element Finsets. -/
def homogeneousWalshFamily (n : ℕ) (S : WalshDegreeIndex n) : WalshL2 :=
  walshL2 S.1

/-- The homogeneous Walsh family is orthonormal. -/
theorem orthonormal_homogeneousWalshFamily (n : ℕ) :
    Orthonormal ℂ (homogeneousWalshFamily n) := by
  exact orthonormal_walshL2.comp Subtype.val Subtype.val_injective

/-- Complete synthesis of square-summable degree-`n` Finset coefficients.
This is the Finset form of (17): no factorial occurs because each unordered
set of distinct lines appears exactly once. -/
noncomputable def homogeneousWalshSynthesis (n : ℕ) :
    ℓ²(WalshDegreeIndex n, ℂ) →ₗᵢ[ℂ] WalshL2 :=
  (orthonormal_homogeneousWalshFamily n).orthogonalFamily.linearIsometry

/-- The complete homogeneous synthesis is an isometry. -/
@[simp] theorem norm_homogeneousWalshSynthesis (n : ℕ)
    (c : ℓ²(WalshDegreeIndex n, ℂ)) :
    ‖homogeneousWalshSynthesis n c‖ = ‖c‖ :=
  (homogeneousWalshSynthesis n).norm_map c

/-- A single homogeneous coefficient synthesizes to the corresponding Walsh
character. -/
@[simp] theorem homogeneousWalshSynthesis_single (n : ℕ)
    (S : WalshDegreeIndex n) (a : ℂ) :
    homogeneousWalshSynthesis n (lp.single 2 S a) = a • walshL2 S.1 := by
  rw [homogeneousWalshSynthesis,
    OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Every vector produced by homogeneous synthesis belongs to the closed
degree-`n` Walsh subspace. -/
theorem homogeneousWalshSynthesis_mem_degree (n : ℕ)
    (c : ℓ²(WalshDegreeIndex n, ℂ)) :
    homogeneousWalshSynthesis n c ∈ walshDegree n := by
  let V : WalshDegreeIndex n → ℂ →ₗᵢ[ℂ] WalshL2 := fun S =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      ((orthonormal_homogeneousWalshFamily n).1 S)
  let U : Submodule ℂ WalshL2 :=
    ⨆ S, LinearMap.range (V S).toLinearMap
  have hrange : homogeneousWalshSynthesis n c ∈ U.topologicalClosure := by
    have hrange' : homogeneousWalshSynthesis n c ∈
        LinearMap.range
          (orthonormal_homogeneousWalshFamily n).orthogonalFamily.linearIsometry.toLinearMap := by
      exact ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ walshDegree n := by
    refine iSup_le fun S => ?_
    rintro _ ⟨a, rfl⟩
    change a • walshL2 S.1 ∈ walshDegree n
    apply (walshDegree n).smul_mem
    simpa only [S.2] using walshL2_mem_degree S.1
  exact (U.topologicalClosure_minimal hU
    (Submodule.isClosed_topologicalClosure _)) hrange

/-- A three-line index of type `(1,1,2)`: two horizontal lines and one
vertical line.  Encoding the carrier as a Finset makes pairwise distinctness
part of the type, as the Finset convention requires. -/
def IsType112Index (S : Finset LineIndex) : Prop :=
  S.card = 3 ∧ (S.filter fun l => l.1 = Axis.horizontal).card = 2

/-- The genuine Finset carrier for the paper's degree-three correction. -/
abbrev Type112Index := {S : Finset LineIndex // IsType112Index S}

/-- The type-`(1,1,2)` Walsh family. -/
def type112WalshFamily (S : Type112Index) : WalshL2 := walshL2 S.1

/-- Type-`(1,1,2)` Walsh characters are orthonormal. -/
theorem orthonormal_type112WalshFamily :
    Orthonormal ℂ type112WalshFamily :=
  orthonormal_walshL2.comp Subtype.val Subtype.val_injective

/-- Complete synthesis of square-summable type-`(1,1,2)` coefficients. -/
noncomputable def type112WalshSynthesis :
    ℓ²(Type112Index, ℂ) →ₗᵢ[ℂ] WalshL2 :=
  orthonormal_type112WalshFamily.orthogonalFamily.linearIsometry

/-- The type-`(1,1,2)` synthesis is the exact no-factorial form of (17). -/
@[simp] theorem norm_type112WalshSynthesis (c : ℓ²(Type112Index, ℂ)) :
    ‖type112WalshSynthesis c‖ = ‖c‖ :=
  type112WalshSynthesis.norm_map c

/-- A singleton type-`(1,1,2)` coefficient maps to its Walsh character. -/
@[simp] theorem type112WalshSynthesis_single (S : Type112Index) (a : ℂ) :
    type112WalshSynthesis (lp.single 2 S a) = a • walshL2 S.1 := by
  rw [type112WalshSynthesis,
    OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Every synthesized type-`(1,1,2)` coefficient lies in Walsh degree three. -/
theorem type112WalshSynthesis_mem_degree (c : ℓ²(Type112Index, ℂ)) :
    type112WalshSynthesis c ∈ walshDegree 3 := by
  let V : Type112Index → ℂ →ₗᵢ[ℂ] WalshL2 := fun S =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      (orthonormal_type112WalshFamily.1 S)
  let U : Submodule ℂ WalshL2 :=
    ⨆ S, LinearMap.range (V S).toLinearMap
  have hrange : type112WalshSynthesis c ∈ U.topologicalClosure := by
    have hrange' : type112WalshSynthesis c ∈
        LinearMap.range
          orthonormal_type112WalshFamily.orthogonalFamily.linearIsometry.toLinearMap := by
      exact ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ walshDegree 3 := by
    refine iSup_le fun S => ?_
    rintro _ ⟨a, rfl⟩
    change a • walshL2 S.1 ∈ walshDegree 3
    apply (walshDegree 3).smul_mem
    have hcard : S.1.card = 3 := S.2.1
    simpa only [hcard] using walshL2_mem_degree S.1
  exact (U.topologicalClosure_minimal hU
    (Submodule.isClosed_topologicalClosure _)) hrange

/-- A Walsh character of any other degree is orthogonal to the complete
type-`(1,1,2)` synthesis. -/
theorem inner_type112WalshSynthesis_eq_zero (S : Finset LineIndex)
    (hS : S.card ≠ 3) (c : ℓ²(Type112Index, ℂ)) :
    inner ℂ (walshL2 S) (type112WalshSynthesis c) = 0 := by
  have hs : HasSum (fun T : Type112Index => c T • walshL2 T.1)
      (type112WalshSynthesis c) := by
    simpa only [type112WalshSynthesis, type112WalshFamily,
      LinearIsometry.toSpanSingleton_apply] using
      orthonormal_type112WalshFamily.orthogonalFamily.hasSum_linearIsometry c
  have hm := hs.mapL (innerSL ℂ (walshL2 S))
  have hz : HasSum (fun _ : Type112Index => (0 : ℂ)) 0 := hasSum_zero
  have hterm : ∀ T : Type112Index,
      inner ℂ (walshL2 S) (c T • walshL2 T.1) = 0 := by
    intro T
    rw [inner_smul_right, inner_walshL2, if_neg]
    · simp
    · intro hST
      apply hS
      rw [hST]
      exact T.2.1
  have hmzero : HasSum (fun _ : Type112Index => (0 : ℂ))
      (inner ℂ (walshL2 S) (type112WalshSynthesis c)) := by
    exact HasSum.congr_fun hm (fun T => by
      simpa only [innerSL_apply_apply] using (hterm T).symm)
  exact hmzero.unique hz

/-- The row sector used for the paper's degree-one coefficient. -/
abbrev RowLineCoefficient := ℓ²(ℤ, ℂ)

/-- Degree-one Walsh synthesis along lines parallel to `i`. -/
noncomputable def axisDegreeOneSynthesis (i : Axis) :
    RowLineCoefficient →ₗᵢ[ℂ] WalshL2 :=
  (orthonormal_walshL2.comp
    (fun k : ℤ => ({(i, k)} : Finset LineIndex)) (by
      intro k l h
      simpa using h)).orthogonalFamily.linearIsometry

@[simp] theorem norm_axisDegreeOneSynthesis (i : Axis) (c : RowLineCoefficient) :
    ‖axisDegreeOneSynthesis i c‖ = ‖c‖ :=
  (axisDegreeOneSynthesis i).norm_map c

@[simp] theorem axisDegreeOneSynthesis_single (i : Axis) (k : ℤ) (a : ℂ) :
    axisDegreeOneSynthesis i (lp.single 2 k a) = a • walshL2 {(i, k)} := by
  rw [axisDegreeOneSynthesis, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- Coefficient extraction from the complete degree-one synthesis. -/
theorem inner_axisDegreeOneSynthesis (i : Axis) (k : ℤ)
    (c : RowLineCoefficient) :
    inner ℂ (walshL2 {(i, k)}) (axisDegreeOneSynthesis i c) = c k := by
  rw [← one_smul ℂ (walshL2 {(i, k)}),
    ← axisDegreeOneSynthesis_single]
  rw [(axisDegreeOneSynthesis i).inner_map_map]
  rw [lp.inner_single_left]
  simp

/-- A line character on the other axis is orthogonal to the complete
degree-one synthesis. -/
theorem inner_axisDegreeOneSynthesis_of_ne (i j : Axis) (hij : j ≠ i)
    (l : ℤ) (c : RowLineCoefficient) :
    inner ℂ (walshL2 {(j, l)}) (axisDegreeOneSynthesis i c) = 0 := by
  let V : ℤ → ℂ →ₗᵢ[ℂ] WalshL2 := fun k =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      ((orthonormal_walshL2.comp
        (fun m : ℤ => ({(i, m)} : Finset LineIndex)) (by
          intro m n h
          simpa using h)).1 k)
  have hs : HasSum (fun k : ℤ => c k • walshL2 {(i, k)})
      (axisDegreeOneSynthesis i c) := by
    simpa only [axisDegreeOneSynthesis, V,
      LinearIsometry.toSpanSingleton_apply] using
      ((orthonormal_walshL2.comp
        (fun m : ℤ => ({(i, m)} : Finset LineIndex)) (by
          intro m n h
          simpa using h)).orthogonalFamily.hasSum_linearIsometry c)
  have hm := hs.mapL (innerSL ℂ (walshL2 {(j, l)}))
  have hz : HasSum (fun _ : ℤ => (0 : ℂ)) 0 := hasSum_zero
  apply hm.unique
  simpa [innerSL_apply_apply, inner_smul_right, inner_walshL2, hij] using hz

/-- Fourier-series synthesis followed by degree-one Walsh synthesis.  The
input is an honest `L²` frequency function on the paper's `2π`-torus. -/
noncomputable def degreeOneFrequencySynthesis (i : Axis) :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) →ₗᵢ[ℂ]
      WalshL2 :=
  (axisDegreeOneSynthesis i).comp
    (fourierBasis.repr :
      Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))
        ≃ₗᵢ[ℂ] RowLineCoefficient).toLinearIsometry

/-- Plancherel and (17) make the degree-one frequency synthesis isometric. -/
@[simp] theorem norm_degreeOneFrequencySynthesis (i : Axis)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod))) :
    ‖degreeOneFrequencySynthesis i f‖ = ‖f‖ := by
  simp [degreeOneFrequencySynthesis]

/-- A real-frequency representative on `(-π,π]`, bundled as an honest
element of the paper's normalized `L²` torus. -/
noncomputable def realTorusL2 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle torusPeriod)) :=
  by
    have hend : -Real.pi + torusPeriod = Real.pi := by
      rw [torusPeriod]
      ring
    have hf' : MemLp f 2
        (volume.restrict (Ioc (-Real.pi) (-Real.pi + torusPeriod))) := by
      rw [hend]
      exact hf
    exact (hf'.memLp_liftIoc (T := torusPeriod)
      (t := -Real.pi)).haarAddCircle.toLp
      (AddCircle.liftIoc torusPeriod (-Real.pi) f)

/-- The bundled torus vector has the advertised lifted representative. -/
theorem coeFn_realTorusL2 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    (realTorusL2 f hf : AddCircle torusPeriod → ℂ) =ᵐ[
        AddCircle.haarAddCircle]
      AddCircle.liftIoc torusPeriod (-Real.pi) f := by
  unfold realTorusL2
  dsimp only
  exact MemLp.coeFn_toLp _

/-- The zero Fourier coordinate of `realTorusL2` is the normalized integral
over the paper's fundamental domain. -/
theorem fourierBasis_repr_realTorusL2_zero (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    fourierBasis.repr (realTorusL2 f hf) 0 =
      (2 * Real.pi)⁻¹ * ∫ x in Ioc (-Real.pi) Real.pi, f x := by
  rw [fourierBasis_repr]
  have hcongr := congrFun (fourierCoeff_congr_ae
    (coeFn_realTorusL2 f hf)) 0
  rw [hcongr, fourierCoeff_liftIoc_eq,
    fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, torusPeriod]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  simp only [one_smul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  simp only [one_div, Complex.real_smul]

/-- The concrete degree-one competitor synthesized from a square-integrable
real-frequency coefficient. -/
noncomputable def degreeOneRealFrequencySynthesis (i : Axis) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) : WalshL2 :=
  degreeOneFrequencySynthesis i (realTorusL2 f hf)

theorem degreeOneRealFrequencySynthesis_mem_degree (i : Axis) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    degreeOneRealFrequencySynthesis i f hf ∈ walshDegree 1 := by
  let c : RowLineCoefficient := fourierBasis.repr (realTorusL2 f hf)
  change axisDegreeOneSynthesis i c ∈ walshDegree 1
  let V : ℤ → ℂ →ₗᵢ[ℂ] WalshL2 := fun k =>
    LinearIsometry.toSpanSingleton ℂ WalshL2
      ((orthonormal_walshL2.comp
        (fun m : ℤ => ({(i, m)} : Finset LineIndex)) (by
          intro m n h
          simpa using h)).1 k)
  let U : Submodule ℂ WalshL2 := ⨆ k, LinearMap.range (V k).toLinearMap
  have hrange : axisDegreeOneSynthesis i c ∈ U.topologicalClosure := by
    have hrange' : axisDegreeOneSynthesis i c ∈
        LinearMap.range
          (orthonormal_walshL2.comp
            (fun k : ℤ => ({(i, k)} : Finset LineIndex)) (by
              intro k l h
              simpa using h)).orthogonalFamily.linearIsometry.toLinearMap := ⟨c, rfl⟩
    rw [OrthogonalFamily.range_linearIsometry] at hrange'
    exact hrange'
  have hU : U ≤ walshDegree 1 := by
    refine iSup_le fun k => ?_
    rintro _ ⟨a, rfl⟩
    change a • walshL2 {(i, k)} ∈ walshDegree 1
    exact (walshDegree 1).smul_mem a (by simpa using walshL2_mem_degree {(i, k)})
  exact (U.topologicalClosure_minimal hU
    (Submodule.isClosed_topologicalClosure _)) hrange

end

end Manhattan
