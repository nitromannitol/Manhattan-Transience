import Manhattan.Glue.OrderedContractivity
import Manhattan.Walsh.Correction

/-!
# The ordered representative of a raw type-`(1,1,2)` coefficient

Paper: `manuscript.tex:1193-1198` (equation (46), `eq:contract`),
`manuscript.tex:1208-1219` (Lemma 5.3), `manuscript.tex:1045-1052`.

`Manhattan.type112DiagonalProjection` reads a raw coefficient indexed by
`RawType112Index = Fin 3 -> Z` (two row frequencies and one column frequency,
possibly coincident) at the strictly increasing representative of each Finset
type-`(1,1,2)` index, through `Manhattan.orderedType112Equiv`. Only the
*unweighted* contractivity of that passage was available
(`Manhattan.norm_type112DiagonalProjection_le`).

This file supplies the weighted statement. The passage is realised by the
orthogonal projection onto the coordinates with `n 0 < n 1`
(`Manhattan.Glue.rawOrderedProjection`), it is norm-preserving on that range,
and a multiplier in the total frequency `P` commutes with it because such a
multiplier is assembled from *simultaneous* translations of all line indices:
in these coordinates a simultaneous translation is a shift by a vector with
equal row entries, and such a shift preserves the strict order of the two row
indices.
-/

noncomputable section

namespace Manhattan.Glue

/-- The ordered off-diagonal coordinates of a raw type-`(1,1,2)` index. -/
def rawOrderedSet : Set RawType112Index := {n : RawType112Index | n 0 < n 1}

@[simp] theorem mem_rawOrderedSet (n : RawType112Index) :
    n ∈ rawOrderedSet ↔ n 0 < n 1 := Iff.rfl

/-- The orthogonal projection onto the ordered off-diagonal coordinates. This
is the frequency-free form of the paper's `Pi_3` together with the choice of
ordered representative. -/
def rawOrderedProjection : ℓ²(RawType112Index, ℂ) →L[ℂ] ℓ²(RawType112Index, ℂ) :=
  l2SupportProjection rawOrderedSet

@[simp] theorem rawOrderedProjection_apply (c : ℓ²(RawType112Index, ℂ))
    (n : RawType112Index) :
    rawOrderedProjection c n = rawOrderedSet.indicator (fun m => (c m : ℂ)) n := rfl

theorem rawOrderedProjection_idem (c : ℓ²(RawType112Index, ℂ)) :
    rawOrderedProjection (rawOrderedProjection c) = rawOrderedProjection c :=
  l2SupportProjection_idem _ c

theorem rawOrderedProjection_sym (c d : ℓ²(RawType112Index, ℂ)) :
    inner ℂ (rawOrderedProjection c) d = inner ℂ c (rawOrderedProjection d) :=
  l2SupportProjection_sym _ c d

/-! ### The projection realises `type112DiagonalProjection` -/

theorem type112RawIndex_orderedType112Equiv (m : OrderedType112Index) :
    type112RawIndex (orderedType112Equiv m) = m.1 := by
  rw [type112RawIndex, Equiv.symm_apply_apply]

/-- The passage to the ordered representative is norm-preserving on the range
of the projection: it loses exactly the coordinates the projection kills, and
nothing else. This refines `Manhattan.norm_type112DiagonalProjection_le` from
an inequality to an identity. -/
theorem norm_type112DiagonalProjection_eq (c : ℓ²(RawType112Index, ℂ)) :
    ‖type112DiagonalProjection c‖ = ‖rawOrderedProjection c‖ := by
  have hleft : ‖type112DiagonalProjection c‖ ^ 2
      = ∑' S : Type112Index, ‖c (type112RawIndex S)‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num) (type112DiagonalProjection c)
  have hright : ‖rawOrderedProjection c‖ ^ 2
      = ∑' n : RawType112Index,
        ‖rawOrderedSet.indicator (fun m => (c m : ℂ)) n‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num) (rawOrderedProjection c)
  have hind : (fun n : RawType112Index =>
        ‖rawOrderedSet.indicator (fun m => (c m : ℂ)) n‖ ^ 2)
      = rawOrderedSet.indicator (fun m => ‖c m‖ ^ 2) := by
    funext n
    by_cases h : n ∈ rawOrderedSet
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]
      norm_num
  have hreindex : (∑' S : Type112Index, ‖c (type112RawIndex S)‖ ^ 2)
      = ∑' m : OrderedType112Index, ‖c m.1‖ ^ 2 := by
    rw [← orderedType112Equiv.tsum_eq (fun S => ‖c (type112RawIndex S)‖ ^ 2)]
    exact tsum_congr fun m => by rw [type112RawIndex_orderedType112Equiv]
  have hsq : ‖type112DiagonalProjection c‖ ^ 2 = ‖rawOrderedProjection c‖ ^ 2 := by
    rw [hleft, hright, hreindex, hind]
    exact tsum_subtype rawOrderedSet fun m => ‖c m‖ ^ 2
  nlinarith [hsq, norm_nonneg (type112DiagonalProjection c),
    norm_nonneg (rawOrderedProjection c),
    sq_nonneg (‖type112DiagonalProjection c‖ - ‖rawOrderedProjection c‖),
    sq_nonneg (‖type112DiagonalProjection c‖ + ‖rawOrderedProjection c‖)]

/-! ### Simultaneous translations preserve the ordered representative

`Manhattan.Glue.lineShiftVector_axisVector` computes the shift a
lattice translation induces on the line frequencies: every horizontal line is
shifted by the same integer and every vertical line by the same integer. In
the coordinates `RawType112Index` of two rows and one column, a simultaneous
translation is therefore a shift by a vector `v` with `v 0 = v 1`, and such a
shift preserves the strict order of the two row indices. This is the paper's
"a multiplier in `P` is a combination of simultaneous translations of all line
indices, which preserve distinctness" (`manuscript.tex:1233-1235`), sharpened
from distinctness to the choice of ordered representative. -/

/-- The shift of raw type-`(1,1,2)` coordinates by an integer vector. -/
def rawType112Shift (v : RawType112Index) : RawType112Index ≃ RawType112Index :=
  Equiv.addRight v

@[simp] theorem rawType112Shift_apply (v n : RawType112Index) :
    rawType112Shift v n = n + v := rfl

/-- A simultaneous shift of the two row frequencies preserves the ordered
off-diagonal coordinates. -/
theorem rawType112Shift_mem_rawOrderedSet {v : RawType112Index} (hv : v 0 = v 1)
    (n : RawType112Index) :
    rawType112Shift v n ∈ rawOrderedSet ↔ n ∈ rawOrderedSet := by
  show (n + v) 0 < (n + v) 1 ↔ n 0 < n 1
  simp only [Pi.add_apply, hv]
  omega

/-- Simultaneous shifts commute with the projection onto the ordered
representatives. Every multiplier in the total frequency `P` is assembled from
such shifts, so every such multiplier satisfies the commutation hypothesis of
`Manhattan.Glue.re_inner_rawOrderedProjection_le`. -/
theorem rawOrderedProjection_comm_shift {v : RawType112Index} (hv : v 0 = v 1)
    (c : ℓ²(RawType112Index, ℂ)) :
    rawOrderedProjection (l2CongrLeft (rawType112Shift v) c)
      = l2CongrLeft (rawType112Shift v) (rawOrderedProjection c) :=
  l2SupportProjection_l2CongrLeft rawOrderedSet (rawType112Shift v)
    (rawType112Shift_mem_rawOrderedSet hv) c

/-! ### Equation (46) for the type-`(1,1,2)` ordered representative -/

/-- **The weighted contractivity (46) in the raw type-`(1,1,2)` picture.** Any
nonnegative operator commuting with the ordered-representative projection has
smaller energy after the passage to the ordered representative. With
`Manhattan.Glue.rawOrderedProjection_comm_shift` this applies to every
multiplier in the total frequency `P`, which is the weighted analogue of
`Manhattan.norm_type112DiagonalProjection_le`. -/
theorem re_inner_rawOrderedProjection_le
    (T : ℓ²(RawType112Index, ℂ) →L[ℂ] ℓ²(RawType112Index, ℂ))
    (hcomm : ∀ c, rawOrderedProjection (T c) = T (rawOrderedProjection c))
    (hpos : ∀ x : ℓ²(RawType112Index, ℂ), 0 ≤ RCLike.re (inner ℂ (T x) x))
    (c : ℓ²(RawType112Index, ℂ)) :
    RCLike.re (inner ℂ (T (rawOrderedProjection c)) (rawOrderedProjection c))
      ≤ RCLike.re (inner ℂ (T c) c) :=
  re_inner_le_of_commuting_projection T rawOrderedProjection
    rawOrderedProjection_idem rawOrderedProjection_sym hcomm hpos c

end Manhattan.Glue
