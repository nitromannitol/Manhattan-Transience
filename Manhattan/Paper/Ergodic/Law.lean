import Manhattan.Paper.Ergodic.Alternating

/-!
# The uniform law on the four alternating environments

This file builds the law of the remark and proves parts (ii), (iii) and (iv):
it is a probability measure carried by exactly four environments of mass `1/4`
each, it is stationary under the whole translation action, it is ergodic for
that action, and each one-point marginal is a fair sign. The last theorem of
the file records the paper's closing observation that ergodicity fails for the
even sublattice.

Paper: the remark before `\begin{problem}[Which orientations are transient]`.
-/

namespace Manhattan.Paper.Ergodic

open MeasureTheory
open scoped ENNReal symmDiff

/-! ### Two elementary sums -/

theorem sum_orientation {M : Type*} [AddCommMonoid M] (g : Orientation → M) :
    ∑ o : Orientation, g o = g .negative + g .positive := by
  rw [show (Finset.univ : Finset Orientation) = {Orientation.negative, Orientation.positive} by
      decide, Finset.sum_pair (by decide)]

theorem sum_signPair {M : Type*} [AddCommMonoid M] (f : Orientation × Orientation → M) :
    ∑ uv : Orientation × Orientation, f uv =
      f (.negative, .negative) + f (.negative, .positive) +
        (f (.positive, .negative) + f (.positive, .positive)) := by
  rw [Fintype.sum_prod_type, sum_orientation]
  rw [sum_orientation (fun v => f (.negative, v)), sum_orientation (fun v => f (.positive, v))]

theorem altEnv_eq_iff (uv uv' : Orientation × Orientation) :
    altEnv uv = altEnv uv' ↔ uv = uv' :=
  ⟨fun h => altEnv_injective h, fun h => h ▸ rfl⟩

/-! ### The law -/

/-- The uniform law on the four alternating environments. -/
noncomputable def ergodicLaw : Measure Environment :=
  (4 : ℝ≥0∞)⁻¹ • ∑ uv : Orientation × Orientation, Measure.dirac (altEnv uv)

theorem ergodicLaw_apply (s : Set Environment) :
    ergodicLaw s =
      (4 : ℝ≥0∞)⁻¹ * ∑ uv : Orientation × Orientation, s.indicator 1 (altEnv uv) := by
  simp only [ergodicLaw, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply,
    Measure.dirac_apply]

private theorem four_inv_mul_four : (4 : ℝ≥0∞)⁻¹ * 4 = 1 :=
  ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private theorem four_inv_mul_two : (4 : ℝ≥0∞)⁻¹ * 2 = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

instance : IsProbabilityMeasure ergodicLaw := by
  constructor
  rw [ergodicLaw_apply, sum_signPair]
  simp only [Set.indicator_univ, Pi.one_apply]
  rw [show (1 : ℝ≥0∞) + 1 + (1 + 1) = 4 by norm_num]
  exact four_inv_mul_four

/-! ### Four atoms of mass `1/4` -/

/-- Each of the four environments carries mass exactly `1/4`. -/
theorem ergodicLaw_singleton (uv : Orientation × Orientation) :
    ergodicLaw {altEnv uv} = (4 : ℝ≥0∞)⁻¹ := by
  classical
  rw [ergodicLaw_apply, sum_signPair]
  obtain ⟨u, v⟩ := uv
  cases u <;> cases v <;> simp [Set.mem_singleton_iff, altEnv_eq_iff]

/-- The support is genuinely four points. -/
theorem ncard_range_altEnv : (Set.range altEnv).ncard = 4 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ altEnv_injective, Set.ncard_univ,
    Nat.card_eq_fintype_card]
  decide

/-- The four environments carry all the mass. -/
theorem ergodicLaw_range : ergodicLaw (Set.range altEnv) = 1 := by
  classical
  rw [ergodicLaw_apply, sum_signPair]
  simp only [Set.indicator_apply, Set.mem_range, Pi.one_apply]
  rw [if_pos ⟨_, rfl⟩, if_pos ⟨_, rfl⟩, if_pos ⟨_, rfl⟩, if_pos ⟨_, rfl⟩,
    show (1 : ℝ≥0∞) + 1 + (1 + 1) = 4 by norm_num]
  exact four_inv_mul_four

/-! ### (ii) Stationarity -/

theorem translateEnvironment_leftInverse (x : Site) (ω : Environment) :
    translateEnvironment (-x) (translateEnvironment x ω) = ω := by
  rw [← translateEnvironment_add, add_neg_cancel, translateEnvironment_zero]

theorem shiftSigns_involutive (x : Site) : Function.Involutive (shiftSigns x) := by
  intro uv
  simp [shiftSigns]

/-- Part (ii): the law is invariant under every lattice translation. -/
theorem measurePreserving_translate (x : Site) :
    MeasurePreserving (translateEnvironment x) ergodicLaw ergodicLaw := by
  classical
  refine ⟨measurable_translateEnvironment x, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_translateEnvironment x) hs, ergodicLaw_apply,
    ergodicLaw_apply]
  congr 1
  have hpre : ∀ uv : Orientation × Orientation,
      (translateEnvironment x ⁻¹' s).indicator (1 : Environment → ℝ≥0∞) (altEnv uv) =
        s.indicator 1 (altEnv (shiftSigns x uv)) := by
    intro uv
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_preimage, translateEnvironment_altEnv, Pi.one_apply]
  simp only [hpre]
  exact Fintype.sum_equiv (shiftSigns_involutive x).toPerm
    (fun uv => s.indicator 1 (altEnv (shiftSigns x uv)))
    (fun uv => s.indicator 1 (altEnv uv)) fun _ => rfl

/-! ### (iv) Fair one-point marginals -/

/-- Part (iv): every one-point marginal is a fair sign. -/
theorem ergodicLaw_marginal (l : LineIndex) (o : Orientation) :
    ergodicLaw {ω : Environment | ω l = o} = (2 : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨i, k⟩ := l
  rw [ergodicLaw_apply, sum_signPair]
  by_cases hk : k % 2 = 0 <;> cases i <;> cases o <;>
    simp only [Set.mem_setOf_eq, Set.indicator_apply, altEnv_horizontal, altEnv_vertical,
      parityShift, hk, if_false, flipOrientation, Pi.one_apply, reduceCtorEq,
      if_pos, add_zero, zero_add] <;>
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num] <;>
    exact four_inv_mul_two

/-- Part (iv) in probability-measure form: the marginal law is the fair coin of
the model. -/
theorem ergodicLaw_map_eval (l : LineIndex) :
    Measure.map (fun ω : Environment => ω l) ergodicLaw = fairCoin := by
  refine Measure.ext_of_singleton fun o => ?_
  rw [Measure.map_apply (measurable_pi_apply l) (measurableSet_singleton o),
    show (fun ω : Environment => ω l) ⁻¹' {o} = {ω : Environment | ω l = o} from rfl,
    ergodicLaw_marginal, fairCoin,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton o), fairCoinPMF,
    PMF.uniformOfFintype_apply, show Fintype.card Orientation = 2 from rfl]
  norm_num

/-! ### (iii) Ergodicity for the full action -/

/-- Part (iii): every almost invariant set is null or conull. The proof uses
transitivity of the action on the four atoms. -/
theorem ergodicLaw_eq_zero_or_one_of_ae_invariant (s : Set Environment)
    (hinv : ∀ x : Site, ergodicLaw (s ∆ (translateEnvironment x ⁻¹' s)) = 0) :
    ergodicLaw s = 0 ∨ ergodicLaw s = 1 := by
  classical
  by_cases hmem : ∃ uv : Orientation × Orientation, altEnv uv ∈ s
  · right
    obtain ⟨uv, huv⟩ := hmem
    have hall : ∀ uv' : Orientation × Orientation, altEnv uv' ∈ s := by
      intro uv'
      by_contra hnot
      have hx : translateEnvironment (transitionSite uv uv') (altEnv uv) = altEnv uv' :=
        translate_transitive uv uv'
      have hin : altEnv uv ∈ s ∆ (translateEnvironment (transitionSite uv uv') ⁻¹' s) := by
        refine Set.mem_symmDiff.mpr (Or.inl ⟨huv, ?_⟩)
        simp only [Set.mem_preimage, hx]
        exact hnot
      have hle : ergodicLaw {altEnv uv} ≤
          ergodicLaw (s ∆ (translateEnvironment (transitionSite uv uv') ⁻¹' s)) :=
        measure_mono (Set.singleton_subset_iff.mpr hin)
      rw [ergodicLaw_singleton, hinv] at hle
      exact absurd (le_antisymm hle (zero_le _)) (by norm_num)
    rw [ergodicLaw_apply, sum_signPair]
    simp only [Set.indicator_apply, hall, if_pos, Pi.one_apply]
    rw [show (1 : ℝ≥0∞) + 1 + (1 + 1) = 4 by norm_num]
    exact four_inv_mul_four
  · left
    push_neg at hmem
    rw [ergodicLaw_apply, sum_signPair]
    simp only [Set.indicator_apply, hmem, if_neg, not_false_iff]
    simp

/-- Part (iii) for strictly invariant sets. -/
theorem ergodicLaw_eq_zero_or_one_of_invariant (s : Set Environment)
    (hinv : ∀ x : Site, translateEnvironment x ⁻¹' s = s) :
    ergodicLaw s = 0 ∨ ergodicLaw s = 1 := by
  refine ergodicLaw_eq_zero_or_one_of_ae_invariant s fun x => ?_
  rw [hinv x, symmDiff_self]
  simp

/-! ### Failure of ergodicity for the even sublattice -/

theorem preimage_singleton_translate_even (a b : ℤ) (uv : Orientation × Orientation) :
    translateEnvironment (2 * a, 2 * b) ⁻¹' {altEnv uv} = {altEnv uv} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    have hback := congrArg (translateEnvironment (-(2 * a, 2 * b))) h
    rw [translateEnvironment_leftInverse] at hback
    rw [hback, show (-(2 * a, 2 * b) : Site) = (2 * (-a), 2 * (-b)) by simp,
      translate_even]
  · rintro rfl
    exact translate_even a b uv

/-- The paper's closing remark: translations in `2ℤ²` fix every realization, so
the law is not ergodic for the even sublattice. The witness has mass `1/2`. -/
theorem not_ergodic_even_sublattice :
    ∃ s : Set Environment, MeasurableSet s ∧
      (∀ a b : ℤ, translateEnvironment (2 * a, 2 * b) ⁻¹' s = s) ∧
      ergodicLaw s = (2 : ℝ≥0∞)⁻¹ := by
  classical
  refine ⟨{altEnv (.positive, .positive)} ∪ {altEnv (.positive, .negative)},
    (measurableSet_singleton _).union (measurableSet_singleton _), ?_, ?_⟩
  · intro a b
    rw [Set.preimage_union, preimage_singleton_translate_even,
      preimage_singleton_translate_even]
  · rw [ergodicLaw_apply, sum_signPair]
    simp only [Set.indicator_apply, Set.mem_union, Set.mem_singleton_iff, Pi.one_apply,
      altEnv_eq_iff, Prod.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
      if_false, if_true, and_self, or_true, zero_add, add_zero]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
    exact four_inv_mul_two

end Manhattan.Paper.Ergodic
