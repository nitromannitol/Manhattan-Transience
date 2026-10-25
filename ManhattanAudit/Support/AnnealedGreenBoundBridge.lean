module

public import Mathlib
public import Manhattan.MainTheorems
public import ManhattanAudit.AnnealedGreenBound.SolutionBasic

@[expose] public section

/-!
# Bridge from the `AnnealedGreenBound` vocabulary to the repository

The challenge vocabulary (`ManhattanAudit/AnnealedGreenBound/SolutionBasic.lean`, a
verbatim copy of the vocabulary block of
`ManhattanAudit/AnnealedGreenBound/Challenge.lean`; namespace `ManhattanAudit`) is a
statement-level copy of the repository definitions.
Its two inductive types `Axis` and `Orientation` are new types, so this file
matches them constructor by constructor with the repository's, builds from
these a measurable equivalence of the environment spaces that carries the
vocabulary's product law to the repository's, and proves that the directed
edges, paths, `n`-step kernels, continuous-time kernels and annealed
continuous-time kernels agree along it.  The Poisson weights are
the same Mathlib expression on both sides and agree definitionally.

**It is imported by `ManhattanAudit/AnnealedGreenBound/Solution.lean` only.**  The
`Challenge` and `SolutionBasic` files stay Mathlib-only.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace ManhattanAudit.Bridge

/-- Match the independent copy of the two axes with the repository axes. -/
def axisEquiv : ManhattanAudit.Axis ≃ Manhattan.Axis where
  toFun
    | .horizontal => .horizontal
    | .vertical => .vertical
  invFun
    | .horizontal => .horizontal
    | .vertical => .vertical
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- Match the independent copy of the orientations with the repository copy. -/
def orientationEquiv : ManhattanAudit.Orientation ≃ Manhattan.Orientation where
  toFun
    | .negative => .negative
    | .positive => .positive
  invFun
    | .negative => .negative
    | .positive => .positive
  left_inv o := by cases o <;> rfl
  right_inv o := by cases o <;> rfl

def orientationMeasurableEquiv :
    ManhattanAudit.Orientation ≃ᵐ Manhattan.Orientation where
  toEquiv := orientationEquiv
  measurable_toFun := measurable_of_finite orientationEquiv
  measurable_invFun := measurable_of_finite orientationEquiv.symm

/-- Reindex the independent line set by the corresponding repository line set. -/
def lineIndexEquiv : ManhattanAudit.LineIndex ≃ Manhattan.LineIndex :=
  Equiv.prodCongr axisEquiv (Equiv.refl ℤ)

/-- The coordinatewise measurable equivalence between the two environment spaces. -/
def environmentMeasurableEquiv :
    ManhattanAudit.Environment ≃ᵐ Manhattan.Environment :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Manhattan.LineIndex => ManhattanAudit.Orientation) lineIndexEquiv).trans
    (MeasurableEquiv.piCongrRight
      (fun _ : Manhattan.LineIndex => orientationMeasurableEquiv))

theorem fairCoin_map :
    Measure.map orientationMeasurableEquiv ManhattanAudit.fairCoin =
      Manhattan.fairCoin := by
  apply Measure.ext_of_singleton
  intro o
  rw [Measure.map_apply orientationMeasurableEquiv.measurable
    (measurableSet_singleton o)]
  cases o with
  | negative =>
      have hpre :
          orientationMeasurableEquiv ⁻¹' {Manhattan.Orientation.negative} =
            {ManhattanAudit.Orientation.negative} := by
        ext o
        cases o <;> simp [orientationMeasurableEquiv, orientationEquiv]
      rw [hpre]
      change
        (ManhattanAudit.fairCoinPMF.toMeasure
          {ManhattanAudit.Orientation.negative}) =
        (Manhattan.fairCoinPMF.toMeasure {Manhattan.Orientation.negative})
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp only [ManhattanAudit.fairCoinPMF,
        Manhattan.fairCoinPMF, PMF.uniformOfFintype_apply]
      rw [Fintype.card_congr orientationEquiv]
  | positive =>
      have hpre :
          orientationMeasurableEquiv ⁻¹' {Manhattan.Orientation.positive} =
            {ManhattanAudit.Orientation.positive} := by
        ext o
        cases o <;> simp [orientationMeasurableEquiv, orientationEquiv]
      rw [hpre]
      change
        (ManhattanAudit.fairCoinPMF.toMeasure
          {ManhattanAudit.Orientation.positive}) =
        (Manhattan.fairCoinPMF.toMeasure {Manhattan.Orientation.positive})
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp only [ManhattanAudit.fairCoinPMF,
        Manhattan.fairCoinPMF, PMF.uniformOfFintype_apply]
      rw [Fintype.card_congr orientationEquiv]

theorem environmentMeasurableEquiv_map :
    Measure.map environmentMeasurableEquiv ManhattanAudit.environmentLaw =
      Manhattan.environmentLaw := by
  change Measure.map environmentMeasurableEquiv
      (Measure.infinitePi
        (fun _ : ManhattanAudit.LineIndex => ManhattanAudit.fairCoin)) =
    Measure.infinitePi (fun _ : Manhattan.LineIndex => Manhattan.fairCoin)
  rw [show (environmentMeasurableEquiv : ManhattanAudit.Environment → Manhattan.Environment) =
      (MeasurableEquiv.piCongrRight
        (fun _ : Manhattan.LineIndex => orientationMeasurableEquiv)) ∘
      (MeasurableEquiv.piCongrLeft
        (fun _ : Manhattan.LineIndex => ManhattanAudit.Orientation) lineIndexEquiv) by rfl]
  rw [← Measure.map_map
    (MeasurableEquiv.piCongrRight
      (fun _ : Manhattan.LineIndex => orientationMeasurableEquiv)).measurable
    (MeasurableEquiv.piCongrLeft
      (fun _ : Manhattan.LineIndex => ManhattanAudit.Orientation) lineIndexEquiv).measurable]
  rw [Measure.infinitePi_map_piCongrLeft
    (fun _ : Manhattan.LineIndex => ManhattanAudit.fairCoin) lineIndexEquiv]
  have hcoordinate :
      (MeasurableEquiv.piCongrRight
        (fun _ : Manhattan.LineIndex => orientationMeasurableEquiv) :
          (Manhattan.LineIndex → ManhattanAudit.Orientation) → Manhattan.Environment) =
        fun ω i => orientationMeasurableEquiv (ω i) := by
    funext ω i
    rfl
  rw [hcoordinate]
  rw [Measure.infinitePi_map_pi
    (fun _ : Manhattan.LineIndex => ManhattanAudit.fairCoin)
    (fun _ => orientationMeasurableEquiv.measurable)]
  simp only [fairCoin_map]

theorem measurePreserving_environmentMeasurableEquiv :
    MeasurePreserving environmentMeasurableEquiv ManhattanAudit.environmentLaw
      Manhattan.environmentLaw :=
  ⟨environmentMeasurableEquiv.measurable, environmentMeasurableEquiv_map⟩

@[simp] theorem environmentMeasurableEquiv_apply
    (ω : ManhattanAudit.Environment) (i : ManhattanAudit.Axis) (k : ℤ) :
    environmentMeasurableEquiv ω (axisEquiv i, k) = orientationEquiv (ω (i, k)) := by
  change orientationEquiv
      ((MeasurableEquiv.piCongrLeft
        (fun _ : Manhattan.LineIndex => ManhattanAudit.Orientation) lineIndexEquiv) ω
          (lineIndexEquiv (i, k))) = orientationEquiv (ω (i, k))
  rw [MeasurableEquiv.piCongrLeft_apply_apply]

@[simp] theorem orientation_sign_equiv (o : ManhattanAudit.Orientation) :
    (orientationEquiv o).sign = o.sign := by
  cases o <;> rfl

@[simp] theorem transverseCoordinate_axisEquiv
    (z : ManhattanAudit.Site) (i : ManhattanAudit.Axis) :
    Manhattan.transverseCoordinate z (axisEquiv i) = ManhattanAudit.transverseCoordinate z i := by
  cases i <;> rfl

@[simp] theorem basisStep_axisEquiv (i : ManhattanAudit.Axis) :
    Manhattan.basisStep (axisEquiv i) = ManhattanAudit.basisStep i := by
  cases i <;> rfl

theorem directedNeighbor_equiv
    (ω : ManhattanAudit.Environment) (z : ManhattanAudit.Site) (i : ManhattanAudit.Axis) :
    Manhattan.directedNeighbor (environmentMeasurableEquiv ω) z (axisEquiv i) =
      ManhattanAudit.directedNeighbor ω z i := by
  cases i <;>
    simp [Manhattan.directedNeighbor,
      ManhattanAudit.directedNeighbor,
      Manhattan.lineAt, ManhattanAudit.lineAt]

theorem followPath_equiv
    (ω : ManhattanAudit.Environment) (z : ManhattanAudit.Site) (path : List ManhattanAudit.Axis) :
    Manhattan.followPath (environmentMeasurableEquiv ω) z (path.map axisEquiv) =
      ManhattanAudit.followPath ω z path := by
  induction path generalizing z with
  | nil => rfl
  | cons i path ih =>
      simp only [List.map_cons, Manhattan.followPath_cons,
        ManhattanAudit.followPath]
      rw [directedNeighbor_equiv, ih]

/-- Coordinatewise transport of an `n`-step axis word. -/
def pathEquiv (n : ℕ) :
    (Fin n → ManhattanAudit.Axis) ≃ (Fin n → Manhattan.Axis) :=
  Equiv.piCongrRight (fun _ => axisEquiv)

theorem listOfFn_pathEquiv (n : ℕ) (path : Fin n → ManhattanAudit.Axis) :
    List.ofFn (pathEquiv n path) = (List.ofFn path).map axisEquiv := by
  have hpath : pathEquiv n path = fun i => axisEquiv (path i) := by
    funext i
    rfl
  rw [hpath]
  simp [Function.comp_def]

theorem nStepKernel_equiv
    (ω : ManhattanAudit.Environment) (n : ℕ) (z z' : ManhattanAudit.Site) :
    Manhattan.nStepKernel (environmentMeasurableEquiv ω) n z z' =
      ManhattanAudit.nStepKernel ω n z z' := by
  unfold Manhattan.nStepKernel ManhattanAudit.nStepKernel
  congr 1
  exact (Fintype.sum_equiv (pathEquiv n) _ _ fun path => by
    rw [listOfFn_pathEquiv, followPath_equiv]).symm

/-- The Poisson weights are the same expression on both sides. -/
theorem rateTwoPoissonWeight_eq (t : ℝ) (n : ℕ) :
    Manhattan.rateTwoPoissonWeight t n = ManhattanAudit.rateTwoPoissonWeight t n := rfl

/-- The continuous-time kernels agree along the environment equivalence. -/
theorem continuousKernel_eq (ω : ManhattanAudit.Environment) (t : ℝ)
    (z z' : ManhattanAudit.Site) :
    Manhattan.continuousKernel (environmentMeasurableEquiv ω) t z z' =
      ManhattanAudit.continuousKernel ω t z z' := by
  simp only [Manhattan.continuousKernel, ManhattanAudit.continuousKernel,
    nStepKernel_equiv, rateTwoPoissonWeight_eq]

/-- The annealed continuous-time kernels agree. -/
theorem annealedContinuousKernel_eq (t : ℝ) (z z' : ManhattanAudit.Site) :
    Manhattan.annealedContinuousKernel t z z' =
      ManhattanAudit.annealedContinuousKernel t z z' := by
  rw [Manhattan.annealedContinuousKernel, ManhattanAudit.annealedContinuousKernel,
    ← measurePreserving_environmentMeasurableEquiv.lintegral_comp_emb
      environmentMeasurableEquiv.measurableEmbedding]
  simp only [continuousKernel_eq]

end ManhattanAudit.Bridge
