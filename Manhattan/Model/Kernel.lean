import Manhattan.Model.Basic

/-!
# Quenched discrete-time kernels

The path-count definition below is the quenched probability of following a
word of independent axis choices, each chosen with probability `1/2`.

Paper: `manuscript.tex:176-190`.
-/

open scoped BigOperators ENNReal NNReal

namespace Manhattan

/-- Follow a finite word of horizontal/vertical choices in a fixed environment. -/
def followPath (ω : Environment) (z : Site) : List Axis → Site
  | [] => z
  | i :: path => followPath ω (directedNeighbor ω z i) path

@[simp] theorem followPath_nil (ω : Environment) (z : Site) : followPath ω z [] = z := rfl

@[simp] theorem followPath_cons (ω : Environment) (z : Site) (i : Axis) (path : List Axis) :
    followPath ω z (i :: path) = followPath ω (directedNeighbor ω z i) path := rfl

/-- Evaluation of a product coordinate chosen measurably from a countable
index set is measurable. -/
theorem measurable_environment_apply {f : Environment → LineIndex} (hf : Measurable f) :
    Measurable fun ω : Environment => ω (f ω) := by
  apply measurable_to_countable'
  intro o
  rw [show (fun ω : Environment => ω (f ω)) ⁻¹' {o} =
      ⋃ l : LineIndex, f ⁻¹' {l} ∩ (fun ω : Environment => ω l) ⁻¹' {o} by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨f ω, rfl, h⟩
    · rintro ⟨l, hl, hlo⟩
      simpa [hl] using hlo]
  exact MeasurableSet.iUnion fun l =>
    (hf (measurableSet_singleton l)).inter
      (measurable_pi_apply l (measurableSet_singleton o))

theorem measurable_directedNeighbor {f : Environment → Site} (hf : Measurable f) (i : Axis) :
    Measurable fun ω => directedNeighbor ω (f ω) i := by
  have hline : Measurable fun ω => lineAt (f ω) i :=
    (measurable_of_countable fun z : Site => lineAt z i).comp hf
  have horientation : Measurable fun ω : Environment => ω (lineAt (f ω) i) :=
    measurable_environment_apply hline
  exact hf.add (((measurable_of_finite Orientation.sign).comp horientation).smul measurable_const)

theorem measurable_followPath (z : Site) (path : List Axis) :
    Measurable fun ω => followPath ω z path := by
  induction path generalizing z with
  | nil => exact measurable_const
  | cons i path ih =>
      let f : Environment → Site := fun ω => directedNeighbor ω z i
      have hf : Measurable f := measurable_directedNeighbor measurable_const i
      have hpiece (y : Site) : MeasurableSet (f ⁻¹' {y}) := hf (measurableSet_singleton y)
      apply measurable_to_countable'
      intro y
      change MeasurableSet ((fun ω => followPath ω (f ω) path) ⁻¹' {y})
      rw [show (fun ω => followPath ω (f ω) path) ⁻¹' {y} =
          ⋃ z' : Site, f ⁻¹' {z'} ∩ (fun ω => followPath ω z' path) ⁻¹' {y} by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨f ω, rfl, h⟩
        · rintro ⟨z', hz', hpath⟩
          simpa [hz'] using hpath]
      exact MeasurableSet.iUnion fun z' =>
        (hpiece z').inter (ih z' (measurableSet_singleton y))

/-- Equation (1): the quenched one-step transition kernel. -/
noncomputable def oneStepKernel (ω : Environment) (z z' : Site) : ℝ≥0 :=
  (2 : ℝ≥0)⁻¹ * ∑ i : Axis, if z' = directedNeighbor ω z i then 1 else 0

/-- The quenched `n`-step transition kernel, as a finite path count. -/
noncomputable def nStepKernel (ω : Environment) (n : ℕ) (z z' : Site) : ℝ≥0 :=
  (2 : ℝ≥0)⁻¹ ^ n *
    ∑ path : Fin n → Axis,
      if followPath ω z (List.ofFn path) = z' then 1 else 0

theorem measurable_nStepKernel (n : ℕ) (z z' : Site) :
    Measurable fun ω => nStepKernel ω n z z' := by
  unfold nStepKernel
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro path _
  apply Measurable.ite
  · exact measurableSet_eq.preimage (measurable_followPath z (List.ofFn path))
  · exact measurable_const
  · exact measurable_const

@[simp] theorem nStepKernel_zero (ω : Environment) (z z' : Site) :
    nStepKernel ω 0 z z' = if z = z' then 1 else 0 := by
  simp [nStepKernel]

/-- Translation covariance of an entire directed path. -/
theorem followPath_translate (x z : Site) (ω : Environment) (path : List Axis) :
    followPath ω (x + z) path = x + followPath (translateEnvironment x ω) z path := by
  induction path generalizing z with
  | nil => simp
  | cons i path ih =>
      rw [followPath_cons, directedNeighbor_translate, ih, followPath_cons]

/-- Translation covariance of every quenched `n`-step kernel. -/
theorem nStepKernel_translate (x z z' : Site) (ω : Environment) (n : ℕ) :
    nStepKernel ω n (x + z) (x + z') =
      nStepKernel (translateEnvironment x ω) n z z' := by
  unfold nStepKernel
  congr 1
  apply Finset.sum_congr rfl
  intro path _
  rw [followPath_translate]
  by_cases hp : followPath (translateEnvironment x ω) z (List.ofFn path) = z'
  · simp [hp]
  · have hp' : x + followPath (translateEnvironment x ω) z (List.ofFn path) ≠ x + z' :=
      fun h => hp (add_left_cancel h)
    simp [hp, hp']

/-- The return-probability identity used at `manuscript.tex:694-696`. -/
theorem nStepKernel_return_translate (x : Site) (ω : Environment) (n : ℕ) :
    nStepKernel ω n x x = nStepKernel (translateEnvironment x ω) n 0 0 := by
  simpa using nStepKernel_translate x 0 0 ω n

/-- The rate-two jump generator, defined directly from its two rate-one jumps. -/
def jumpGenerator (ω : Environment) (h : Site → ℝ) (z : Site) : ℝ :=
  ∑ i : Axis, (h (directedNeighbor ω z i) - h z)

/-- The centered finite-difference expression displayed as equation (2). -/
noncomputable def centeredDriftGenerator (ω : Environment) (h : Site → ℝ) (z : Site) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ i : Axis,
      (h (z + basisStep i) + h (z - basisStep i) - 2 * h z) +
    (2 : ℝ)⁻¹ * ∑ i : Axis,
      (ω (lineAt z i)).sign * (h (z + basisStep i) - h (z - basisStep i))

/-- The generator of the Poisson-subordinated kernel is equation (2).
This is the elementary algebraic identification required by;
no continuous-time Markov-process theory enters the definition.
-/
theorem jumpGenerator_eq_centeredDriftGenerator
    (ω : Environment) (h : Site → ℝ) (z : Site) :
    jumpGenerator ω h z = centeredDriftGenerator ω h z := by
  classical
  have hsum (f : Axis → ℝ) : ∑ i : Axis, f i = f .horizontal + f .vertical := by
    rw [show Finset.univ = {.horizontal, .vertical} by decide]
    simp
  rw [jumpGenerator, centeredDriftGenerator, hsum, hsum, hsum]
  cases h₁ : ω (lineAt z .horizontal) <;>
    cases h₂ : ω (lineAt z .vertical) <;>
    rcases z with ⟨z₁, z₂⟩ <;>
    change ω (.horizontal, z₂) = _ at h₁ <;>
    change ω (.vertical, z₁) = _ at h₂ <;>
    simp [directedNeighbor, basisStep, Orientation.sign, h₁, h₂, lineAt,
      transverseCoordinate] <;> ring_nf

end Manhattan
