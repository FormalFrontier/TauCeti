/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootLength
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum

public section

/-!
# The rank-two type `B` root datum in explicit coordinates

`TauCeti.DynkinType.typeBSimplyConnectedRootDatum` is built uniformly in the rank, out of signed
basis vectors and a rotated product enumeration, so its public interface reads off the simple roots
and the simple coroots and nothing else. A consumer that has to check an equation on *every* root
of a fixed small rank cannot work with that: it needs a coordinate table, in the same shape as the
ones `TauCeti.DynkinType.g2Root` and `TauCeti.DynkinType.f4Root` carry for the two exceptional
types built directly from coordinates.

This file supplies the missing rank-two table. It names the eight roots of `B₂` by reflection words
in the two Bourbaki simple indices, and identifies their character and cocharacter coordinates.

## Coordinates

The character lattice is the weight lattice in the fundamental-weight basis and the cocharacter
lattice is the coroot lattice in the simple-coroot basis, so the coordinates of a root are its
Cartan integers against the two simple coroots and the coordinates of a coroot are its coefficients
on the two simple coroots. With `α₀` the long simple root and `α₁` the short one, the Cartan matrix
being `!![2, -2; -1, 2]` (`TauCeti.DynkinType.cartanMatrix_B_two_eq`), the enumeration is

```text
α₀,  α₁,  α₀ + α₁,  α₀ + 2 α₁,  -α₀,  -α₁,  -α₀ - α₁,  -α₀ - 2 α₁,
```

so that index `k + 4` is the negative of index `k`. The four positive roots come first, the two
simple ones first among them, matching the convention of
`TauCeti.DynkinType.typeBSimpleIndex`.

## Main definitions

* `TauCeti.DynkinType.b2Root` and `TauCeti.DynkinType.b2Coroot`: the coordinate tables.
* `TauCeti.DynkinType.b2Index`: the eight root indices of `typeBSimplyConnectedRootDatum 2`, as
  reflection words in the two simple indices, listed in the order above.
* `TauCeti.DynkinType.b2IndexEquiv`: the resulting reindexing `Fin 8 ≃ Fin (2 * 2 ^ 2)`.
* `TauCeti.DynkinType.b2Coeff`: the simple-root coordinates of the eight roots.
* `TauCeti.DynkinType.b2Length`: their squared lengths, normalised as
  `TauCeti.DynkinType.rootLength` normalises the simple ones.

## Main results

* `TauCeti.DynkinType.root_b2Index` and `TauCeti.DynkinType.coroot_b2Index`: the tables are the
  roots and the coroots of the pinned rank-two type `B` datum.
* `TauCeti.DynkinType.b2Index_bijective` and
  `TauCeti.DynkinType.range_root_typeBSimplyConnectedRootDatum_two`: the eight named indices are
  all of them, so the table is exhaustive.
* `TauCeti.DynkinType.pairing_b2Index`: every Cartan integer of the datum is a dot product of two
  table entries, hence a decidable computation.
* `TauCeti.DynkinType.b2Length_mul_b2Coroot`: the length table is the one forced by the simple
  lengths, `ℓ(β) β^∨ᵢ = cᵢ(β) ℓ(αᵢ)`, and `TauCeti.DynkinType.b2Length_castLE` matches it against
  `TauCeti.DynkinType.rootLength` on the two simple roots.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate II. The table is the rank-two input asked for by the "special isogenies in
characteristics two and three" bullet of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, whose `B₂` case is the one the pinned type `B` datum
could not be computed against.
-/

namespace TauCeti.DynkinType

open Function Set

/-- The eight roots of the pinned rank-two type `B` datum, in the fundamental-weight basis of the
character lattice, with the four positive roots first and the two simple ones first among them. -/
@[expose] def b2Root : Fin 8 → (Fin 2 → ℤ) :=
  ![![2, -2], ![-1, 2], ![1, 0], ![0, 2], ![-2, 2], ![1, -2], ![-1, 0], ![0, -2]]

/-- The eight coroots of the pinned rank-two type `B` datum, in the simple-coroot basis of the
cocharacter lattice, ordered compatibly with `TauCeti.DynkinType.b2Root`. -/
@[expose] def b2Coroot : Fin 8 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![2, 1], ![1, 1], ![-1, 0], ![0, -1], ![-2, -1], ![-1, -1]]

/-- The eight tabulated roots are pairwise distinct. -/
lemma b2Root_injective : Injective b2Root := by decide

/-- The eight tabulated coroots are pairwise distinct. -/
lemma b2Coroot_injective : Injective b2Coroot := by decide

/-- A root and the coroot listed beside it pair to `2`, as a root datum asks. -/
lemma b2Root_dotProduct_b2Coroot_self (k : Fin 8) : b2Root k ⬝ᵥ b2Coroot k = 2 := by
  decide +revert

/-- The last four roots are the negatives of the first four. -/
@[simp] lemma b2Root_add_four (k : Fin 8) : b2Root (k + 4) = -b2Root k := by decide +revert

/-- The last four coroots are the negatives of the first four. -/
@[simp] lemma b2Coroot_add_four (k : Fin 8) : b2Coroot (k + 4) = -b2Coroot k := by decide +revert

/-- The eight root indices of the pinned rank-two type `B` datum, named by reflection words in the
two Bourbaki simple indices and ordered as `TauCeti.DynkinType.b2Root` is. -/
@[expose] def b2Index : Fin 8 → Fin (2 * 2 ^ 2) :=
  ![typeBSimpleIndex 2 0, typeBSimpleIndex 2 1,
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 0)
      (typeBSimpleIndex 2 1),
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 1)
      (typeBSimpleIndex 2 0),
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 0)
      (typeBSimpleIndex 2 0),
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 1)
      (typeBSimpleIndex 2 1),
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 0)
      ((typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 1)
        (typeBSimpleIndex 2 1)),
    (typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 1)
      ((typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 0)
        (typeBSimpleIndex 2 0))]

/-- The first named index is the first Bourbaki simple root. -/
@[simp] lemma b2Index_zero : b2Index 0 = typeBSimpleIndex 2 0 := rfl

/-- The second named index is the second Bourbaki simple root. -/
@[simp] lemma b2Index_one : b2Index 1 = typeBSimpleIndex 2 1 := rfl

/-! ## Computing the table -/

private lemma b2_pairing (k l : Fin (2 * 2 ^ 2)) :
    (typeBSimplyConnectedRootDatum 2).pairing k l =
      (typeBSimplyConnectedRootDatum 2).root k ⬝ᵥ (typeBSimplyConnectedRootDatum 2).coroot l := by
  rw [← RootPairing.root_coroot_eq_pairing, toLinearMap_typeBSimplyConnectedRootDatum]

private lemma b2_root_reflectionPerm (i j : Fin (2 * 2 ^ 2)) :
    (typeBSimplyConnectedRootDatum 2).root
        ((typeBSimplyConnectedRootDatum 2).reflectionPerm i j) =
      (typeBSimplyConnectedRootDatum 2).root j -
        ((typeBSimplyConnectedRootDatum 2).root j ⬝ᵥ
            (typeBSimplyConnectedRootDatum 2).coroot i) •
              (typeBSimplyConnectedRootDatum 2).root i := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, b2_pairing]

private lemma b2_coroot_reflectionPerm (i j : Fin (2 * 2 ^ 2)) :
    (typeBSimplyConnectedRootDatum 2).coroot
        ((typeBSimplyConnectedRootDatum 2).reflectionPerm i j) =
      (typeBSimplyConnectedRootDatum 2).coroot j -
        ((typeBSimplyConnectedRootDatum 2).root i ⬝ᵥ
          (typeBSimplyConnectedRootDatum 2).coroot j) •
            (typeBSimplyConnectedRootDatum 2).coroot i := by
  rw [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_coroot, b2_pairing]

private lemma b2_simple_root (i : Fin 2) :
    (typeBSimplyConnectedRootDatum 2).root (typeBSimpleIndex 2 i) =
      b2Root (Fin.castLE (by omega) i) := by
  rw [root_typeBSimpleIndex]
  fin_cases i <;> decide

private lemma b2_simple_coroot (i : Fin 2) :
    (typeBSimplyConnectedRootDatum 2).coroot (typeBSimpleIndex 2 i) =
      b2Coroot (Fin.castLE (by omega) i) := by
  rw [coroot_typeBSimpleIndex]
  fin_cases i <;> decide

private lemma b2_reflectionPerm_simple (i : Fin 2) {j : Fin (2 * 2 ^ 2)} {k l : Fin 8}
    (hroot : (typeBSimplyConnectedRootDatum 2).root j = b2Root k)
    (hcoroot : (typeBSimplyConnectedRootDatum 2).coroot j = b2Coroot k)
    (hroot_reflection :
      b2Root k -
          (b2Root k ⬝ᵥ b2Coroot (Fin.castLE (by omega) i)) •
            b2Root (Fin.castLE (by omega) i) =
        b2Root l)
    (hcoroot_reflection :
      b2Coroot k -
          (b2Root (Fin.castLE (by omega) i) ⬝ᵥ b2Coroot k) •
            b2Coroot (Fin.castLE (by omega) i) =
        b2Coroot l) :
    (typeBSimplyConnectedRootDatum 2).root
          ((typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 i) j) =
        b2Root l ∧
      (typeBSimplyConnectedRootDatum 2).coroot
          ((typeBSimplyConnectedRootDatum 2).reflectionPerm (typeBSimpleIndex 2 i) j) =
        b2Coroot l := by
  constructor
  · rw [b2_root_reflectionPerm, hroot, b2_simple_root, b2_simple_coroot, hroot_reflection]
  · rw [b2_coroot_reflectionPerm, hcoroot, b2_simple_root, b2_simple_coroot,
      hcoroot_reflection]

private lemma b2_root_coroot_b2Index (k : Fin 8) :
    (typeBSimplyConnectedRootDatum 2).root (b2Index k) = b2Root k ∧
      (typeBSimplyConnectedRootDatum 2).coroot (b2Index k) = b2Coroot k := by
  fin_cases k
  · exact ⟨b2_simple_root 0, b2_simple_coroot 0⟩
  · exact ⟨b2_simple_root 1, b2_simple_coroot 1⟩
  · exact b2_reflectionPerm_simple 0 (b2_simple_root 1) (b2_simple_coroot 1)
      (by decide) (by decide)
  · exact b2_reflectionPerm_simple 1 (b2_simple_root 0) (b2_simple_coroot 0)
      (by decide) (by decide)
  · exact b2_reflectionPerm_simple 0 (b2_simple_root 0) (b2_simple_coroot 0)
      (by decide) (by decide)
  · exact b2_reflectionPerm_simple 1 (b2_simple_root 1) (b2_simple_coroot 1)
      (by decide) (by decide)
  · have h := b2_reflectionPerm_simple 1 (b2_simple_root 1) (b2_simple_coroot 1)
      (l := 5) (by decide) (by decide)
    exact b2_reflectionPerm_simple 0 h.1 h.2 (by decide) (by decide)
  · have h := b2_reflectionPerm_simple 0 (b2_simple_root 0) (b2_simple_coroot 0)
      (l := 4) (by decide) (by decide)
    exact b2_reflectionPerm_simple 1 h.1 h.2 (by decide) (by decide)

/-! ## The table is the datum -/

/-- **The eight named indices carry the tabulated roots.** -/
@[simp] theorem root_b2Index (k : Fin 8) :
    (typeBSimplyConnectedRootDatum 2).root (b2Index k) = b2Root k := by
  exact (b2_root_coroot_b2Index k).1

/-- **The eight named indices carry the tabulated coroots.** -/
@[simp] theorem coroot_b2Index (k : Fin 8) :
    (typeBSimplyConnectedRootDatum 2).coroot (b2Index k) = b2Coroot k := by
  exact (b2_root_coroot_b2Index k).2

/-- The eight reflection words name eight distinct root indices. -/
theorem b2Index_injective : Injective b2Index := fun k l h =>
  b2Root_injective (by rw [← root_b2Index, ← root_b2Index, h])

/-- **The eight reflection words exhaust the root indices.** The pinned rank-two type `B` datum has
`2 * 2 ^ 2 = 8` roots, so the injective list `TauCeti.DynkinType.b2Index` is all of them. -/
theorem b2Index_bijective : Bijective b2Index := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨b2Index_injective, rfl⟩

/-- The reindexing of the roots of the pinned rank-two type `B` datum by the coordinate table. -/
@[expose] noncomputable def b2IndexEquiv : Fin 8 ≃ Fin (2 * 2 ^ 2) :=
  Equiv.ofBijective b2Index b2Index_bijective

/-- The reindexing is the named list of indices. -/
@[simp] lemma b2IndexEquiv_apply (k : Fin 8) : b2IndexEquiv k = b2Index k := rfl

/-- **The tabulated roots are all the roots.** -/
theorem range_root_typeBSimplyConnectedRootDatum_two :
    range (typeBSimplyConnectedRootDatum 2).root = range b2Root := by
  rw [← b2Index_bijective.surjective.range_comp ⇑(typeBSimplyConnectedRootDatum 2).root]
  exact congrArg range (funext root_b2Index)

/-- **The tabulated coroots are all the coroots.** -/
theorem range_coroot_typeBSimplyConnectedRootDatum_two :
    range (typeBSimplyConnectedRootDatum 2).coroot = range b2Coroot := by
  rw [← b2Index_bijective.surjective.range_comp ⇑(typeBSimplyConnectedRootDatum 2).coroot]
  exact congrArg range (funext coroot_b2Index)

/-- **Every Cartan integer of the pinned rank-two type `B` datum is a dot product of table
entries**, hence a decidable computation. -/
@[simp] theorem pairing_b2Index (k l : Fin 8) :
    (typeBSimplyConnectedRootDatum 2).pairing (b2Index k) (b2Index l) =
      b2Root k ⬝ᵥ b2Coroot l := by
  rw [b2_pairing, root_b2Index, coroot_b2Index]

/-! ## Simple-root coordinates and lengths -/

/-- The simple-root coordinates of the eight roots of the pinned rank-two type `B` datum: the pair
`(c₀, c₁)` with `β = c₀ α₀ + c₁ α₁`. -/
@[expose] def b2Coeff : Fin 8 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, 2], ![-1, 0], ![0, -1], ![-1, -1], ![-1, -2]]

/-- **The coefficient table expands each root on the two simple roots.** -/
theorem b2Root_eq_smul_add_smul (k : Fin 8) :
    b2Root k = b2Coeff k 0 • b2Root 0 + b2Coeff k 1 • b2Root 1 := by decide +revert

private lemma b2_smul_add_smul_inj {a b a' b' : ℤ}
    (h : a • b2Root 0 + b • b2Root 1 = a' • b2Root 0 + b' • b2Root 1) : a = a' ∧ b = b' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [b2Root, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  omega

/-- The two simple roots are linearly independent, so the expansion above determines the
coefficients. -/
theorem eq_b2Coeff_of_root_eq {k : Fin 8} {c : Fin 2 → ℤ}
    (h : b2Root k = c 0 • b2Root 0 + c 1 • b2Root 1) : c = b2Coeff k := by
  obtain ⟨h0, h1⟩ := b2_smul_add_smul_inj (h.symm.trans (b2Root_eq_smul_add_smul k))
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The four positive roots come first: their simple-root coordinates are nonnegative. -/
theorem b2Coeff_nonneg (k : Fin 8) (hk : (k : ℕ) < 4) (i : Fin 2) : 0 ≤ b2Coeff k i := by
  decide +revert

/-- The four negative roots come last: their simple-root coordinates are nonpositive. -/
theorem b2Coeff_nonpos (k : Fin 8) (hk : 4 ≤ (k : ℕ)) (i : Fin 2) : b2Coeff k i ≤ 0 := by
  decide +revert

/-- The squared lengths of the eight roots of the pinned rank-two type `B` datum, normalised as
`TauCeti.DynkinType.rootLength` normalises the simple ones: `1` on the four short roots
`± α₁, ± (α₀ + α₁)` and `2` on the four long ones `± α₀, ± (α₀ + 2 α₁)`. -/
@[expose] def b2Length : Fin 8 → ℤ := ![2, 1, 1, 2, 2, 1, 1, 2]

/-- **The length table is the one forced by the simple lengths.** Writing `β = Σ cᵢ αᵢ` and
`β∨ = Σ dᵢ αᵢ∨`, the identity `β∨ = 2 β / (β, β)` reads `ℓ(β) dᵢ = cᵢ ℓ(αᵢ)` once both sides are
expanded on the simple coroots. -/
theorem b2Length_mul_b2Coroot (k : Fin 8) (i : Fin 2) :
    b2Length k * b2Coroot k i = b2Coeff k i * (B 2).rootLength i := by
  rw [rootLength_B]
  decide +revert

private lemma b2_exists_b2Coroot_ne_zero (k : Fin 8) : ∃ i, b2Coroot k i ≠ 0 := by decide +revert

/-- No coroot vanishes, so `TauCeti.DynkinType.b2Length_mul_b2Coroot` determines the length
table. -/
theorem eq_b2Length_of_mul_b2Coroot {k : Fin 8} {c : ℤ}
    (h : ∀ i, c * b2Coroot k i = b2Coeff k i * (B 2).rootLength i) : c = b2Length k := by
  obtain ⟨i, hi⟩ := b2_exists_b2Coroot_ne_zero k
  exact mul_right_cancel₀ hi ((h i).trans (b2Length_mul_b2Coroot k i).symm)

/-- On the two simple roots the length table is `TauCeti.DynkinType.rootLength`. -/
@[simp] theorem b2Length_castLE (i : Fin 2) :
    b2Length (Fin.castLE (by omega) i) = (B 2).rootLength i := by
  rw [rootLength_B]
  decide +revert

/-- A root and its negative have the same length. -/
@[simp] theorem b2Length_add_four (k : Fin 8) : b2Length (k + 4) = b2Length k := by
  decide +revert

/-- **The long simple roots are the ones of length two**, which is the convention
`TauCeti.DynkinType.rootLength` fixes and the one a length-exchanging map is pinned against. -/
theorem isLongSimpleRoot_iff_b2Length_eq_two (i : Fin 2) :
    (B 2).IsLongSimpleRoot i ↔ b2Length (Fin.castLE (by omega) i) = 2 := by
  rw [isLongSimpleRoot_B]
  fin_cases i
  · norm_num [b2Length]
  · norm_num [b2Length]
    decide

end TauCeti.DynkinType
