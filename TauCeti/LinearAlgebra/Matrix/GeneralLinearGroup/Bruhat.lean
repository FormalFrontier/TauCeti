/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Borel` and its normal form `TauCeti.GL2Borel.mk` are the subject of every statement
-- below, and this module re-exports the `GL` notation and the coercion of an element of `GL n R`
-- to a function on indices.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- `DoubleCoset.doubleCoset`, `DoubleCoset.mk` and `DoubleCoset.Quotient` occur in the statements
-- below.
public import Mathlib.GroupTheory.DoubleCoset
-- Non-public: the general double-coset identities — when two classes agree, and that the identity
-- double coset of a subgroup is the subgroup itself — are used only inside the proofs of the
-- double-coset results below, which are their specializations to the Borel subgroup of `GL₂`.
import TauCeti.GroupTheory.DoubleCoset.Identity
-- Non-public: the order of `GL₂` over a finite field is used only inside the proof of the size of
-- the big cell.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The Bruhat decomposition of `GL₂`

The **Bruhat decomposition** of `GL₂` says that the Borel subgroup `B` of invertible upper
triangular matrices has exactly two double cosets in `GL₂`: the group `GL₂` is the disjoint union
of `B` itself and the **big cell** `B w B`, where `w = !![0, 1; 1, 0]` is the Weyl element. In the
Weyl-group language this is `GL₂ = ⨆_{σ ∈ S₂} B σ B`, the rank-one case of the general
decomposition.

Everything is cut out by a single matrix entry. The lower-left entry of `b₁ w b₂`, for
`b₁ = !![a₁, c₁; 0, d₁]` and `b₂ = !![a₂, c₂; 0, d₂]`, is `d₁ a₂`, a product of two units; and
conversely, for an invertible `g = !![a, b; c, d]` whose lower-left entry `c` is a unit, the
column operation `v = !![1, -d; 0, c]` clears the lower-right entry of `g` and swapping the two
columns of `g v` then makes it upper triangular, so that

`g = (g v w) * w * v⁻¹`

exhibits `g` in the big cell. So membership in the big cell is exactly invertibility of the
lower-left entry
(`TauCeti.GL2Borel.mem_doubleCoset_weyl_iff`), while membership in `B` is exactly its vanishing
(`TauCeti.GL2Borel.mem_iff`). Over a commutative ring those two conditions need not exhaust `GL₂`,
so the decomposition itself is stated over a field, where a scalar is either zero or a unit; the
cell description and the factorization hold over any commutative ring.

The counting form `TauCeti.GL2Borel.card_doubleCosetQuotient_eq_two` is what the Mackey
irreducibility criterion `TauCeti.simple_indFDRep_iff_doubleCoset` consumes: the criterion
quantifies over `B \ GL₂ / B` and, with this file in hand, collapses to the single Mackey term at
the Weyl element.

## Main definitions

* `TauCeti.GL2WeylElement`: the Weyl element `!![0, 1; 1, 0]` of `GL₂`, the nontrivial permutation
  matrix.

## Main results

* `TauCeti.GL2Borel.mem_doubleCoset_weyl_iff`: an element of `GL₂` lies in the big cell `B w B`
  exactly when its lower-left entry is a unit, and `TauCeti.GL2Borel.doubleCoset_one_eq`: the
  other cell, the identity double coset, is `B` itself.
* `TauCeti.GL2Borel.union_doubleCoset_weyl_eq_univ` and
  `TauCeti.GL2Borel.disjoint_doubleCoset_weyl`: **the Bruhat decomposition**, `GL₂ = B ⊔ B w B`
  over a field.
* `TauCeti.GL2Borel.doubleCosetMk_eq_one_or_eq_weyl` and
  `TauCeti.GL2Borel.doubleCosetMk_eq_weyl_of_ne_one`: every double coset of `B` is the identity one
  or the Weyl one, so a double coset other than the identity one is the Weyl one.
* `TauCeti.GL2Borel.card_doubleCosetQuotient_eq_two`: `B` has exactly two double cosets in `GL₂`.
* `TauCeti.GL2Borel.closure_insert_gl2WeylElement_eq_top`: the Borel subgroup and the Weyl element
  generate `GL₂`.
* `TauCeti.GL2Borel.ncard_doubleCoset_weyl`: the big cell of `GL₂(𝔽_q)` has `q² (q - 1)²`
  elements.

## Implementation notes

The big cell is spelled as Mathlib's `DoubleCoset.doubleCoset (GL2WeylElement F) B B` rather than
as a new definition for `B * {w} * B`: the two are definitionally the same set, and using
Mathlib's spelling is what lets the results be read directly as statements about
`DoubleCoset.Quotient`, which is the form the Mackey criterion asks for.

The `GL2` prefix on `TauCeti.GL2WeylElement` follows the naming that
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` uses for this family of objects
(`GL2Borel`, `GL2PrincipalSeries`, `GL2Steinberg`, `GL2NonSplitTorus`), and matches
`TauCeti.GL2Borel` in the file this one builds on.

## References

This supplies the double-coset decomposition `B \ GL₂ / B` that the principal-series milestone of
Layer 9 ("the representation theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` needs: its target
`simple_GL2PrincipalSeries_iff`, the irreducibility of `Ind_B^{GL₂}(α ⊗ β)` for `α ≠ β`, is read
off the Mackey criterion, whose double-coset sum this decomposition evaluates. It is the rank-one
case of the Bruhat decomposition named in Layer 8 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`. See also W. Fulton and J. Harris,
*Representation Theory: A First Course*, GTM 129, §5.2, and J.-P. Serre, *Linear Representations
of Finite Groups*, GTM 42, §7.3.
-/

public section

namespace TauCeti

open Matrix

universe u

section Semiring

variable (R : Type u) [Semiring R]

/-- The **Weyl element** of `GL₂`: the permutation matrix `!![0, 1; 1, 0]` swapping the two basis
vectors. It is an involution, and together with the Borel subgroup it generates `GL₂`; its double
coset is the big cell of the Bruhat decomposition. -/
def GL2WeylElement : GL (Fin 2) R where
  val := !![0, 1; 1, 0]
  -- The matrix is its own inverse, so no invertibility side condition has to be discharged.
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The underlying matrix of the Weyl element. -/
@[simp]
theorem coe_gl2WeylElement :
    ((GL2WeylElement R : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; 1, 0] :=
  (rfl)

/-- The Weyl element is an involution. -/
@[simp]
theorem gl2WeylElement_mul_self : GL2WeylElement R * GL2WeylElement R = 1 :=
  Units.ext (GL2WeylElement R).val_inv

@[simp]
theorem gl2WeylElement_inv : (GL2WeylElement R)⁻¹ = GL2WeylElement R :=
  inv_eq_of_mul_eq_one_right (gl2WeylElement_mul_self R)

end Semiring

section CommRing

variable {R : Type u} [CommRing R]

/-- The Weyl element is not upper triangular: its lower-left entry is `1`. -/
theorem gl2WeylElement_notMem_gl2Borel [Nontrivial R] : GL2WeylElement R ∉ GL2Borel R := by
  rw [GL2Borel.mem_iff]
  simp

namespace GL2Borel

/-- **The big cell, entrywise.** Multiplying the Weyl element by upper-triangular matrices on both
sides produces the matrix `!![c₁ a₂, c₁ c₂ + a₁ d₂; d₁ a₂, d₁ c₂]`; the lower-left entry `d₁ a₂` is
the product of two units, which is the whole content of the Bruhat decomposition. -/
theorem coe_mk_mul_weyl_mul_mk (a₁ d₁ a₂ d₂ : Rˣ) (c₁ c₂ : R) :
    ((mk a₁ d₁ c₁ * GL2WeylElement R * mk a₂ d₂ c₂ : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      = !![c₁ * a₂, c₁ * c₂ + (a₁ : R) * d₂; (d₁ : R) * a₂, (d₁ : R) * c₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The lower-left entry detects the big cell, one direction**: every element of `B w B` has an
invertible lower-left entry.  The public interface is the two-way
`TauCeti.GL2Borel.mem_doubleCoset_weyl_iff`. -/
private theorem isUnit_apply_one_zero_of_mem_doubleCoset_weyl {g : GL (Fin 2) R}
    (hg : g ∈ DoubleCoset.doubleCoset (GL2WeylElement R) (GL2Borel R : Set (GL (Fin 2) R))
      (GL2Borel R : Set (GL (Fin 2) R))) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 1 0) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  obtain ⟨a₁, d₁, c₁, rfl⟩ := mem_iff_exists_mk.mp hx
  obtain ⟨a₂, d₂, c₂, rfl⟩ := mem_iff_exists_mk.mp hy
  rw [coe_mk_mul_weyl_mul_mk]
  simp

/-- **The Bruhat factorization.** An invertible matrix `g = !![a, b; c, d]` whose lower-left entry
`c` is a unit lies in the big cell: the column operation `v = !![1, -d; 0, c]` clears the
lower-right entry of `g`, and swapping the two columns of `g v` then makes it upper triangular, so
that `g = (g v w) w v⁻¹` exhibits `g` as an element of `B w B`. This is the only computation in the
file; everything else reads it off.  The public interface is the two-way
`TauCeti.GL2Borel.mem_doubleCoset_weyl_iff`. -/
private theorem mem_doubleCoset_weyl_of_isUnit_apply_one_zero {g : GL (Fin 2) R}
    (hg : IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 1 0)) :
    g ∈ DoubleCoset.doubleCoset (GL2WeylElement R) (GL2Borel R : Set (GL (Fin 2) R))
      (GL2Borel R : Set (GL (Fin 2) R)) := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨v, hv⟩ : ∃ v : GL (Fin 2) R,
      v = mk 1 c (-((g : Matrix (Fin 2) (Fin 2) R) 1 1)) := ⟨_, rfl⟩
  have hvmem : v ∈ GL2Borel R := hv ▸ mk_mem _ _ _
  -- The lower-left entry of `g v w` is the lower-right entry of `g v`, which the column operation
  -- was chosen to kill.
  have hb : g * v * GL2WeylElement R ∈ GL2Borel R := by
    rw [mem_iff, Units.val_mul, Units.val_mul, coe_gl2WeylElement, hv, coe_mk]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Units.val_one]
    linear_combination ((g : Matrix (Fin 2) (Fin 2) R) 1 1) * hc
  refine DoubleCoset.mem_doubleCoset.mpr ⟨_, hb, v⁻¹, inv_mem hvmem, ?_⟩
  rw [mul_assoc (g * v), gl2WeylElement_mul_self, mul_one, mul_assoc, mul_inv_cancel, mul_one]

/-- **The lower-left entry detects the big cell.** An element of `GL₂` lies in the double coset
`B w B` exactly when its lower-left entry is invertible — the condition complementary, over a
field, to the vanishing that defines `B`.

Not a `simp` lemma: `TauCeti.mem_doubleCoset_iff_mk_mem_orbit` is `simp` and rewrites any
double-coset membership into an orbit membership, so this left-hand side is not simp-normal. -/
theorem mem_doubleCoset_weyl_iff {g : GL (Fin 2) R} :
    g ∈ DoubleCoset.doubleCoset (GL2WeylElement R) (GL2Borel R : Set (GL (Fin 2) R))
        (GL2Borel R : Set (GL (Fin 2) R))
      ↔ IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 1 0) :=
  ⟨isUnit_apply_one_zero_of_mem_doubleCoset_weyl, mem_doubleCoset_weyl_of_isUnit_apply_one_zero⟩

/-- **The Weyl double coset, in the quotient**: an element of `GL₂` has the same double coset as
the Weyl element exactly when it lies in the big cell. This is
`TauCeti.doubleCosetMk_eq_mk_iff_mem` at the Weyl element. -/
@[simp]
theorem doubleCosetMk_eq_weyl_iff_mem {g : GL (Fin 2) R} :
    DoubleCoset.mk (GL2Borel R) (GL2Borel R) g
        = DoubleCoset.mk (GL2Borel R) (GL2Borel R) (GL2WeylElement R)
      ↔ g ∈ DoubleCoset.doubleCoset (GL2WeylElement R) (GL2Borel R : Set (GL (Fin 2) R))
          (GL2Borel R : Set (GL (Fin 2) R)) :=
  doubleCosetMk_eq_mk_iff_mem _ _ _ _

/-- The identity double coset of the Borel subgroup is the Borel subgroup. This is
`TauCeti.doubleCoset_one_self` for `H = B`. -/
theorem doubleCoset_one_eq :
    DoubleCoset.doubleCoset (1 : GL (Fin 2) R) (GL2Borel R : Set (GL (Fin 2) R))
        (GL2Borel R : Set (GL (Fin 2) R))
      = (GL2Borel R : Set (GL (Fin 2) R)) :=
  doubleCoset_one_self _

/-- The Weyl double coset is not the identity one: the Weyl element is not upper triangular. -/
theorem doubleCosetMk_weyl_ne_one [Nontrivial R] :
    DoubleCoset.mk (GL2Borel R) (GL2Borel R) (GL2WeylElement R)
      ≠ DoubleCoset.mk (GL2Borel R) (GL2Borel R) 1 := by
  rw [Ne, doubleCosetMk_eq_mk_one_iff_mem]
  exact gl2WeylElement_notMem_gl2Borel

end GL2Borel

end CommRing

section Field

variable (F : Type u) [Field F]

namespace GL2Borel

/-- **The Bruhat decomposition of `GL₂`, covering half**: every invertible `2 × 2` matrix over a
field is upper triangular or lies in the big cell `B w B`, according as its lower-left entry
vanishes or not. -/
theorem union_doubleCoset_weyl_eq_univ :
    (GL2Borel F : Set (GL (Fin 2) F)) ∪
        DoubleCoset.doubleCoset (GL2WeylElement F) (GL2Borel F : Set (GL (Fin 2) F))
          (GL2Borel F : Set (GL (Fin 2) F))
      = Set.univ := by
  ext g
  simp only [Set.mem_union, SetLike.mem_coe, mem_iff, mem_doubleCoset_weyl_iff, Set.mem_univ,
    iff_true, isUnit_iff_ne_zero]
  exact eq_or_ne _ _

/-- **The Bruhat decomposition of `GL₂`, disjointness half**: the Borel subgroup and the big cell
`B w B` are disjoint, the lower-left entry vanishing on the first and invertible on the second. -/
theorem disjoint_doubleCoset_weyl :
    Disjoint (GL2Borel F : Set (GL (Fin 2) F))
      (DoubleCoset.doubleCoset (GL2WeylElement F) (GL2Borel F : Set (GL (Fin 2) F))
        (GL2Borel F : Set (GL (Fin 2) F))) := by
  rw [Set.disjoint_left]
  intro g hg hg'
  rw [SetLike.mem_coe, mem_iff] at hg
  exact (mem_doubleCoset_weyl_iff.mp hg').ne_zero hg

variable {F}

/-- An element of `GL₂` outside the Borel subgroup lies in the big cell. -/
theorem mem_doubleCoset_weyl_of_notMem {g : GL (Fin 2) F} (hg : g ∉ GL2Borel F) :
    g ∈ DoubleCoset.doubleCoset (GL2WeylElement F) (GL2Borel F : Set (GL (Fin 2) F))
      (GL2Borel F : Set (GL (Fin 2) F)) := by
  rw [mem_iff, ← ne_eq, ← isUnit_iff_ne_zero] at hg
  exact mem_doubleCoset_weyl_iff.mpr hg

/-- **Bruhat, in the quotient.** Every double coset of the Borel subgroup in `GL₂` is either the
identity one or the one of the Weyl element. -/
theorem doubleCosetMk_eq_one_or_eq_weyl (g : GL (Fin 2) F) :
    DoubleCoset.mk (GL2Borel F) (GL2Borel F) g
        = DoubleCoset.mk (GL2Borel F) (GL2Borel F) 1 ∨
      DoubleCoset.mk (GL2Borel F) (GL2Borel F) g
        = DoubleCoset.mk (GL2Borel F) (GL2Borel F) (GL2WeylElement F) := by
  by_cases hg : g ∈ GL2Borel F
  · exact Or.inl ((doubleCosetMk_eq_mk_one_iff_mem (GL2Borel F) g).mpr hg)
  · exact Or.inr (doubleCosetMk_eq_weyl_iff_mem.mpr (mem_doubleCoset_weyl_of_notMem hg))

/-- **The form the Mackey criterion consumes**: a double coset of the Borel subgroup other than the
identity one is the Weyl one. -/
theorem doubleCosetMk_eq_weyl_of_ne_one {D : DoubleCoset.Quotient (GL2Borel F : Set (GL (Fin 2) F))
    (GL2Borel F : Set (GL (Fin 2) F))} (hD : D ≠ DoubleCoset.mk (GL2Borel F) (GL2Borel F) 1) :
    D = DoubleCoset.mk (GL2Borel F) (GL2Borel F) (GL2WeylElement F) := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep D
  exact (doubleCosetMk_eq_one_or_eq_weyl g).resolve_left hD

variable (F)

/-- **The Bruhat decomposition, counted**: the Borel subgroup of `GL₂` over a field has exactly two
double cosets, indexed by the Weyl group `S₂` of `GL₂`. This is the input to the Mackey
irreducibility criterion for the principal series. -/
theorem card_doubleCosetQuotient_eq_two :
    Nat.card (DoubleCoset.Quotient (GL2Borel F : Set (GL (Fin 2) F))
      (GL2Borel F : Set (GL (Fin 2) F))) = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨DoubleCoset.mk (GL2Borel F) (GL2Borel F) 1,
    DoubleCoset.mk (GL2Borel F) (GL2Borel F) (GL2WeylElement F),
    (doubleCosetMk_weyl_ne_one).symm, ?_⟩
  ext D
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  obtain ⟨g, rfl⟩ := Quotient.exists_rep D
  exact doubleCosetMk_eq_one_or_eq_weyl g

/-- **The Borel subgroup and the Weyl element generate `GL₂`.** Every element of `GL₂` is upper
triangular or a product `b₁ w b₂` of two upper-triangular matrices with the Weyl element, which is
the generation axiom of the `(B, N)`-pair of `GL₂`. -/
theorem closure_insert_gl2WeylElement_eq_top :
    Subgroup.closure (insert (GL2WeylElement F) (GL2Borel F : Set (GL (Fin 2) F))) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  by_cases hg : g ∈ GL2Borel F
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
  · obtain ⟨x, hx, y, hy, rfl⟩ :=
      DoubleCoset.mem_doubleCoset.mp (mem_doubleCoset_weyl_of_notMem hg)
    exact mul_mem
      (mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ hx))
        (Subgroup.subset_closure (Set.mem_insert _ _)))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ hy))

end GL2Borel

end Field

section FiniteField

variable (F : Type u) [Field F] [Fintype F]

namespace GL2Borel

/-- **The size of the big cell** of `GL₂(𝔽_q)` is `q² (q - 1)²`: what is left of the group after
the Borel subgroup, whose order is `q (q - 1)²`. Equivalently `|B w B| = |B|²/|T|` for the split
torus `T`, the two double cosets accounting for `q (q - 1)² (q + 1) = |GL₂(𝔽_q)|`. -/
theorem ncard_doubleCoset_weyl :
    (DoubleCoset.doubleCoset (GL2WeylElement F) (GL2Borel F : Set (GL (Fin 2) F))
        (GL2Borel F : Set (GL (Fin 2) F))).ncard
      = Fintype.card F ^ 2 * (Fintype.card F - 1) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 :=
    ⟨Fintype.card F - 1, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  -- The two cells partition `GL₂`, so their sizes add up to the order of the group.
  have hsum := congrArg Set.ncard (union_doubleCoset_weyl_eq_univ F)
  rw [Set.ncard_union_eq (disjoint_doubleCoset_weyl F) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_univ, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, card_eq,
    natCard_GL_fin_two, hm] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  rw [hm]
  simp only [Nat.add_sub_cancel]
  refine Nat.add_left_cancel (n := (m + 1) * m ^ 2) ?_
  rw [hsum]
  ring

end GL2Borel

end FiniteField

end TauCeti
