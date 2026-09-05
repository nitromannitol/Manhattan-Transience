import Manhattan.Walsh.LowDegreeSectors

/-!
# Ordered coordinates for the two-row Walsh sector

`Manhattan.Type11Index` is a two-element Finset of horizontal line indices.
The degree-two projection `Pi_2` of the paper is the passage from an ordered
pair of row frequencies to such a Finset, so the Fourier coefficient of a
two-row frequency function has to be read at the canonical increasing
representative.  This file supplies that representative, mirroring
`Manhattan.orderedType112Equiv` one degree lower.

Paper: `manuscript.tex:736-740` and `manuscript.tex:1274-1283`.
-/

namespace Manhattan.Glue

noncomputable section

local instance projectionDischargeIndexDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Ordered coordinates for two distinct row indices. -/
abbrev OrderedType11Index := {n : Fin 2 → ℤ // n 0 < n 1}

/-- The Finset of lines represented by ordered two-row coordinates. -/
def orderedType11Lines (n : OrderedType11Index) : Finset LineIndex :=
  {(Axis.horizontal, n.1 0), (Axis.horizontal, n.1 1)}

theorem orderedType11Lines_isType11 (n : OrderedType11Index) :
    IsType11Index (orderedType11Lines n) := by
  have hne : n.1 0 ≠ n.1 1 := ne_of_lt n.2
  constructor
  · simp [orderedType11Lines, hne]
  · intro l hl
    simp only [orderedType11Lines, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> rfl

/-- Ordered two-row coordinates as a genuine Finset index. -/
def orderedType11IndexToFinset (n : OrderedType11Index) : Type11Index :=
  ⟨orderedType11Lines n, orderedType11Lines_isType11 n⟩

theorem orderedType11IndexToFinset_injective :
    Function.Injective orderedType11IndexToFinset := by
  intro n m h
  apply Subtype.ext
  funext i
  have hsets : orderedType11Lines n = orderedType11Lines m :=
    congrArg Subtype.val h
  fin_cases i
  · change n.1 0 = m.1 0
    have hnmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, n.1 0) ∈ s) hsets
    have hmmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, m.1 0) ∈ s) hsets
    simp [orderedType11Lines] at hnmem hmmem
    have hn := n.2
    have hm := m.2
    omega
  · change n.1 1 = m.1 1
    have hnmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, n.1 1) ∈ s) hsets
    have hmmem := congrArg
      (fun s : Finset LineIndex => (Axis.horizontal, m.1 1) ∈ s) hsets
    simp [orderedType11Lines] at hnmem hmmem
    have hn := n.2
    have hm := m.2
    omega

theorem orderedType11IndexToFinset_surjective :
    Function.Surjective orderedType11IndexToFinset := by
  intro T
  obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp T.2.1
  have hx : x.1 = Axis.horizontal := T.2.2 x (by simp [hT])
  have hy : y.1 = Axis.horizontal := T.2.2 y (by simp [hT])
  rcases x with ⟨ix, k⟩
  rcases y with ⟨iy, l⟩
  change ix = Axis.horizontal at hx
  change iy = Axis.horizontal at hy
  subst ix
  subst iy
  have hkl : k ≠ l := by
    intro h
    exact hxy (by simp [h])
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · refine ⟨⟨![k, l], by simpa using hlt⟩, Subtype.ext ?_⟩
    change orderedType11Lines ⟨![k, l], by simpa using hlt⟩ = T.1
    simpa [orderedType11Lines] using hT.symm
  · refine ⟨⟨![l, k], by simpa using hgt⟩, Subtype.ext ?_⟩
    change orderedType11Lines ⟨![l, k], by simpa using hgt⟩ = T.1
    change ({(Axis.horizontal, l), (Axis.horizontal, k)} : Finset LineIndex) = T.1
    rw [Finset.pair_comm]
    exact hT.symm

/-- The canonical identification of ordered increasing row pairs with the
Finset-indexed two-row Walsh sector. -/
def orderedType11Equiv : OrderedType11Index ≃ Type11Index :=
  Equiv.ofBijective orderedType11IndexToFinset
    ⟨orderedType11IndexToFinset_injective,
      orderedType11IndexToFinset_surjective⟩

/-- The increasing pair of row frequencies carried by a two-row Walsh
index. -/
def type11RawIndex (T : Type11Index) : Fin 2 → ℤ :=
  (orderedType11Equiv.symm T).1

/-- The two row indices of a genuine two-row Walsh index are distinct: this
is exactly what `Pi_2` enforces. -/
theorem type11RawIndex_lt (T : Type11Index) :
    type11RawIndex T 0 < type11RawIndex T 1 :=
  (orderedType11Equiv.symm T).2

theorem type11RawIndex_ne (T : Type11Index) :
    type11RawIndex T 0 ≠ type11RawIndex T 1 :=
  ne_of_lt (type11RawIndex_lt T)

end

end Manhattan.Glue
