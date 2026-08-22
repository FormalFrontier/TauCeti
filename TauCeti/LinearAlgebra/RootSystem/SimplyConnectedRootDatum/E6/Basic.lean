/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `vecMul_dotProduct_comm` is used in the proof of `e6Root_dotProduct_e6Coroot_comm` below.
import TauCeti.LinearAlgebra.Matrix.Gram
-- The `DynkinType` API, `dotProductEquiv` and `RootPairing.Base` come with
-- `SimplyConnectedRootDatum.Basic`.
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic

public section

/-!
# The simply connected root datum of type `E₆`

This file constructs the pinned integral root datum of type `E₆` on the character and cocharacter
lattices `Fin 6 → ℤ`. The character lattice is written in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis, so that the `i`-th simple root is the `i`-th row of
the Bourbaki-numbered Cartan matrix `CartanMatrix.E 6` and the `i`-th simple coroot is the `i`-th
standard basis vector.

## The coordinates

A coroot is stored by its coordinates in the simple coroots, and the corresponding root by its
pairings against the simple coroots. Because `E₆` is simply laced, a root and its coroot have the
same simple-root coordinates, so a single stored vector determines both: if a coroot has
coordinates `c`, then the root has coordinates `⟨β, αⱼ^∨⟩ = ∑ i, cᵢ ⟨αᵢ, αⱼ^∨⟩`, that is, the
Cartan-matrix image of `c`. That relation is `TauCeti.DynkinType.e6Root_eq_mulVec`, and it is what
makes every later step structural rather than a second table: the root reflections are the image of
the coroot reflections under a linear map, and the pairing is symmetric because `CartanMatrix.E 6`
is.

The seventy-two roots — the count fixed by `TauCeti.DynkinType.numRoots` — are ordered with the six
simple roots first, in Bourbaki order, then the remaining thirty positive roots by height and then
lexicographically in their simple-root coordinates, and finally the thirty-six negative roots in
the matching order. The last positive root is therefore the highest root, whose simple-root
coordinates are the Bourbaki marks `(1, 2, 2, 3, 2, 1)`.

Only the coroots are asked to span their lattice, and only that half is recorded, in
`TauCeti.DynkinType.corootSpan_e6SimplyConnectedRootDatum_eq_top`. The roots span the root lattice,
which sits inside the weight lattice with index `3` — the determinant of `CartanMatrix.E 6` — so the
datum carries no `RootPairing.IsRootSystem` instance. That asymmetry is what "simply connected"
means here.

## Main definitions

* `TauCeti.DynkinType.e6Coroot` and `TauCeti.DynkinType.e6Root`: the coroot coordinate embedding and
  the root embedding derived from it by the Cartan-matrix map.
* `TauCeti.DynkinType.e6SimplyConnectedRootDatum`: the pinned root datum of type `E₆`.
* `TauCeti.DynkinType.e6SimpleIndex`: the first six root indices, the Bourbaki-numbered simple
  roots.
* `TauCeti.DynkinType.e6SimplyConnectedBase`: the base they form.

## Main results

* `TauCeti.DynkinType.e6Root_eq_mulVec`: the root coordinates are the Cartan-matrix image of the
  coroot coordinates.
* `TauCeti.DynkinType.root_e6SimpleIndex` and `TauCeti.DynkinType.coroot_e6SimpleIndex`: the `i`-th
  simple root is the `i`-th row of `CartanMatrix.E 6` and the `i`-th simple coroot is
  `Pi.single i 1`, which is what pins the two lattices as the weight and coroot lattices.
* `TauCeti.DynkinType.hasCartanType_e6SimplyConnectedRootDatum`: the pinned base has Cartan type
  `E6`.
* `TauCeti.DynkinType.corootSpan_e6SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate V, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `E₆` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open _root_.Matrix Module Set Submodule

namespace DynkinType

/-! ## The coordinate data -/

/-- The positive coroots of type `E₆` in the simple-coroot basis. -/
private def e6PositiveCoroot : Fin 36 → (Fin 6 → ℤ) := ![
    ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1], ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

/-- The coroots of type `E₆` in the simple-coroot basis. The first six are the standard basis
vectors, the first thirty-six are the positive coroots, and the last thirty-six are their
negatives. -/
def e6Coroot : Fin 72 ↪ (Fin 6 → ℤ) where
  toFun i := if h : (i : ℕ) < 36 then e6PositiveCoroot ⟨i, h⟩
    else -e6PositiveCoroot ⟨(i : ℕ) - 36, by omega⟩
  inj' := by decide +kernel

/-- The roots of type `E₆` in the fundamental-weight basis, ordered compatibly with
`TauCeti.DynkinType.e6Coroot`. They are derived from the coroot coordinates by the Cartan-matrix
map, and the first six are the rows of `CartanMatrix.E 6`. -/
def e6Root : Fin 72 ↪ (Fin 6 → ℤ) where
  toFun i := CartanMatrix.E 6 *ᵥ e6Coroot i
  inj' := (Matrix.mulVec_injective_of_det_ne_zero (by
    rw [CartanMatrix.E₆_det]
    norm_num)).comp e6Coroot.injective

/-! ## The three blocks of root indices -/

/-- The `i`-th simple root of type `E₆` sits at root index `i`, the Bourbaki node `i + 1`. -/
def e6SimpleIndex (i : Fin 6) : Fin 72 := ⟨i, by omega⟩

/-- The `i`-th positive root of type `E₆` sits at root index `i`. -/
def e6PositiveIndex (i : Fin 36) : Fin 72 := ⟨i, by omega⟩

/-- The negative of the `i`-th positive root of type `E₆` sits at root index `i + 36`. -/
def e6NegativeIndex (i : Fin 36) : Fin 72 := ⟨i + 36, by omega⟩

@[simp] lemma e6SimpleIndex_val (i : Fin 6) : (e6SimpleIndex i : ℕ) = i := (rfl)

@[simp] lemma e6PositiveIndex_val (i : Fin 36) : (e6PositiveIndex i : ℕ) = i := (rfl)

@[simp] lemma e6NegativeIndex_val (i : Fin 36) : (e6NegativeIndex i : ℕ) = (i : ℕ) + 36 := (rfl)

lemma e6SimpleIndex_injective : Function.Injective e6SimpleIndex :=
  fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)

/-! ## The Cartan matrix as the bridge between the two embeddings -/

/-- **The root coordinates are the Cartan-matrix image of the coroot coordinates.**
Writing a coroot as `β^∨ = ∑ i, cᵢ αᵢ^∨` in the simple coroots, the pairings of `β` against the
simple coroots are `⟨β, αⱼ^∨⟩ = ∑ i, cᵢ ⟨αᵢ, αⱼ^∨⟩`, which is the `j`-th entry of the
Cartan-matrix image of `c` because `CartanMatrix.E 6` is symmetric.

This is deliberately not a `simp` lemma: unfolding a root into the Cartan-matrix image of its
coroot is a change of representation, not a normal form, and it would take the left-hand sides of
the lemmas below out of normal form. -/
theorem e6Root_eq_mulVec (j : Fin 72) : e6Root j = CartanMatrix.E 6 *ᵥ e6Coroot j := by
  simp only [e6Root, Function.Embedding.coeFn_mk]

/-- **The simple coroots are the standard basis.** This is what pins the cocharacter lattice as the
coroot lattice, so that the datum is the simply connected one. -/
@[simp] theorem coroot_e6SimpleIndex (i : Fin 6) : e6Coroot (e6SimpleIndex i) = Pi.single i 1 := by
  decide +kernel +revert

/-- **The simple roots are the rows of the Cartan matrix.** In the fundamental-weight basis the
`i`-th simple root of the pinned type `E₆` datum is the `i`-th row of `CartanMatrix.E 6`, which is
what pins the character lattice as the weight lattice. -/
@[simp] theorem root_e6SimpleIndex (i : Fin 6) : e6Root (e6SimpleIndex i) = CartanMatrix.E 6 i := by
  rw [e6Root_eq_mulVec, coroot_e6SimpleIndex, Matrix.mulVec_single_one]
  exact funext ((CartanMatrix.E_isSymm 6).apply i)

/-- The pairing of the pinned tables is symmetric. This is the simply-laced feature of `E₆`: the
pairing is the symmetric bilinear form attached to `CartanMatrix.E 6`, read on the shared
simple-root coordinates of a root and its coroot. -/
theorem e6Root_dotProduct_e6Coroot_comm (i j : Fin 72) :
    e6Root i ⬝ᵥ e6Coroot j = e6Root j ⬝ᵥ e6Coroot i := by
  rw [e6Root_eq_mulVec, e6Root_eq_mulVec, ← vecMul_transpose, ← vecMul_transpose,
    (CartanMatrix.E_isSymm 6).eq]
  exact vecMul_dotProduct_comm (CartanMatrix.E_isSymm 6) _ _

/-- The second half of the table lists the negatives of the coroots in the first half. -/
@[simp] theorem e6Coroot_e6NegativeIndex (i : Fin 36) :
    e6Coroot (e6NegativeIndex i) = -e6Coroot (e6PositiveIndex i) := by
  decide +kernel +revert

/-- The second half of the table lists the negatives of the roots in the first half. -/
@[simp] theorem e6Root_e6NegativeIndex (i : Fin 36) :
    e6Root (e6NegativeIndex i) = -e6Root (e6PositiveIndex i) := by
  rw [e6Root_eq_mulVec, e6Root_eq_mulVec, e6Coroot_e6NegativeIndex, mulVec_neg]

/-- Each root pairs with its own coroot to `2`. -/
@[simp] theorem e6Root_dotProduct_e6Coroot_self (i : Fin 72) : e6Root i ⬝ᵥ e6Coroot i = 2 := by
  decide +kernel +revert

/-! ## The reflections -/

/-- The permutation table for reflection in each of the thirty-six positive `E₆` roots. Reflection
in the corresponding negative root is the same permutation. -/
private def e6ReflectionTable : Fin 36 → Fin 72 → Fin 72 := ![
  ![36, 1, 10, 3, 4, 5, 6, 7, 15, 9, 2, 11, 19, 13, 20, 8, 23, 17,
    24, 12, 14, 26, 27, 16, 18, 29, 21, 22, 31, 25, 30, 28, 32, 33, 34, 35,
    0, 37, 46, 39, 40, 41, 42, 43, 51, 45, 38, 47, 55, 49, 56, 44, 59, 53,
    60, 48, 50, 62, 63, 52, 54, 65, 57, 58, 67, 61, 66, 64, 68, 69, 70, 71],
  ![0, 37, 2, 9, 4, 5, 6, 13, 14, 3, 10, 17, 18, 7, 8, 20, 21, 11,
    12, 24, 15, 16, 22, 26, 19, 25, 23, 27, 28, 29, 30, 31, 32, 33, 35, 34,
    36, 1, 38, 45, 40, 41, 42, 49, 50, 39, 46, 53, 54, 43, 44, 56, 57, 47,
    48, 60, 51, 52, 58, 62, 55, 61, 59, 63, 64, 65, 66, 67, 68, 69, 71, 70],
  ![10, 1, 38, 8, 4, 5, 6, 12, 3, 14, 0, 16, 7, 18, 9, 15, 11, 21,
    13, 19, 20, 17, 22, 23, 24, 25, 26, 30, 28, 32, 27, 33, 29, 31, 34, 35,
    46, 37, 2, 44, 40, 41, 42, 48, 39, 50, 36, 52, 43, 54, 45, 51, 47, 57,
    49, 55, 56, 53, 58, 59, 60, 61, 62, 66, 64, 68, 63, 69, 65, 67, 70, 71],
  ![0, 9, 8, 39, 7, 5, 11, 4, 2, 1, 15, 6, 12, 13, 14, 10, 16, 17,
    22, 19, 20, 25, 18, 23, 27, 21, 29, 24, 28, 26, 30, 31, 32, 34, 33, 35,
    36, 45, 44, 3, 43, 41, 47, 40, 38, 37, 51, 42, 48, 49, 50, 46, 52, 53,
    58, 55, 56, 61, 54, 59, 63, 57, 65, 60, 64, 62, 66, 67, 68, 70, 69, 71],
  ![0, 1, 2, 7, 40, 6, 5, 3, 12, 13, 10, 11, 8, 9, 18, 19, 16, 17,
    14, 15, 24, 21, 22, 23, 20, 28, 26, 27, 25, 31, 30, 29, 33, 32, 34, 35,
    36, 37, 38, 43, 4, 42, 41, 39, 48, 49, 46, 47, 44, 45, 54, 55, 52, 53,
    50, 51, 60, 57, 58, 59, 56, 64, 62, 63, 61, 67, 66, 65, 69, 68, 70, 71],
  ![0, 1, 2, 3, 6, 41, 4, 11, 8, 9, 10, 7, 16, 17, 14, 15, 12, 13,
    21, 23, 20, 18, 25, 19, 26, 22, 24, 29, 28, 27, 32, 31, 30, 33, 34, 35,
    36, 37, 38, 39, 42, 5, 40, 47, 44, 45, 46, 43, 52, 53, 50, 51, 48, 49,
    57, 59, 56, 54, 61, 55, 62, 58, 60, 65, 64, 63, 68, 67, 66, 69, 70, 71],
  ![0, 1, 2, 11, 41, 40, 42, 7, 16, 17, 10, 3, 12, 13, 21, 23, 8, 9,
    18, 19, 26, 14, 28, 15, 24, 25, 20, 31, 22, 29, 33, 27, 32, 30, 34, 35,
    36, 37, 38, 47, 5, 4, 6, 43, 52, 53, 46, 39, 48, 49, 57, 59, 44, 45,
    54, 55, 62, 50, 64, 51, 60, 61, 56, 67, 58, 65, 69, 63, 68, 66, 70, 71],
  ![0, 13, 12, 40, 39, 11, 6, 43, 8, 9, 19, 5, 2, 1, 22, 15, 16, 17,
    18, 10, 27, 28, 14, 23, 24, 25, 31, 20, 21, 29, 30, 26, 34, 33, 32, 35,
    36, 49, 48, 4, 3, 47, 42, 7, 44, 45, 55, 41, 38, 37, 58, 51, 52, 53,
    54, 46, 63, 64, 50, 59, 60, 61, 67, 56, 57, 65, 66, 62, 70, 69, 68, 71],
  ![15, 14, 39, 38, 12, 5, 16, 7, 44, 9, 10, 11, 4, 22, 1, 0, 6, 25,
    18, 19, 20, 21, 13, 23, 30, 17, 32, 27, 28, 29, 24, 34, 26, 33, 31, 35,
    51, 50, 3, 2, 48, 41, 52, 43, 8, 45, 46, 47, 40, 58, 37, 36, 42, 61,
    54, 55, 56, 57, 49, 59, 66, 53, 68, 63, 64, 65, 60, 70, 62, 69, 67, 71],
  ![0, 39, 14, 37, 13, 5, 17, 7, 8, 45, 20, 11, 22, 4, 2, 15, 25, 6,
    18, 27, 10, 21, 12, 29, 24, 16, 26, 19, 28, 23, 30, 31, 32, 35, 34, 33,
    36, 3, 50, 1, 49, 41, 53, 43, 44, 9, 56, 47, 58, 40, 38, 51, 61, 42,
    54, 63, 46, 57, 48, 65, 60, 52, 62, 55, 64, 59, 66, 67, 68, 71, 70, 69],
  ![38, 1, 36, 15, 4, 5, 6, 19, 8, 20, 46, 23, 12, 24, 14, 3, 16, 26,
    18, 7, 9, 21, 30, 11, 13, 32, 17, 27, 33, 29, 22, 31, 25, 28, 34, 35,
    2, 37, 0, 51, 40, 41, 42, 55, 44, 56, 10, 59, 48, 60, 50, 39, 52, 62,
    54, 43, 45, 57, 66, 47, 49, 68, 53, 63, 69, 65, 58, 67, 61, 64, 70, 71],
  ![0, 17, 16, 42, 4, 43, 39, 41, 8, 9, 23, 47, 12, 13, 25, 15, 2, 1,
    28, 19, 29, 21, 22, 10, 31, 14, 26, 27, 18, 20, 34, 24, 32, 33, 30, 35,
    36, 53, 52, 6, 40, 7, 3, 5, 44, 45, 59, 11, 48, 49, 61, 51, 38, 37,
    64, 55, 65, 57, 58, 46, 67, 50, 62, 63, 54, 56, 70, 60, 68, 69, 66, 71],
  ![19, 18, 43, 3, 44, 16, 6, 38, 40, 22, 10, 11, 48, 13, 14, 15, 5, 28,
    1, 0, 30, 21, 9, 23, 24, 25, 33, 27, 17, 34, 20, 31, 32, 26, 29, 35,
    55, 54, 7, 39, 8, 52, 42, 2, 4, 58, 46, 47, 12, 49, 50, 51, 41, 64,
    37, 36, 66, 57, 45, 59, 60, 61, 69, 63, 53, 70, 56, 67, 68, 62, 65, 71],
  ![0, 43, 18, 3, 45, 17, 6, 37, 22, 40, 24, 11, 12, 49, 14, 27, 28, 5,
    2, 19, 20, 21, 8, 31, 10, 25, 26, 15, 16, 29, 30, 23, 35, 33, 34, 32,
    36, 7, 54, 39, 9, 53, 42, 1, 58, 4, 60, 47, 48, 13, 50, 63, 64, 41,
    38, 55, 56, 57, 44, 67, 46, 61, 62, 51, 52, 65, 66, 59, 71, 69, 70, 68],
  ![20, 44, 45, 3, 18, 5, 21, 22, 37, 38, 10, 25, 12, 13, 50, 15, 16, 17,
    4, 30, 0, 6, 7, 32, 24, 11, 26, 27, 28, 29, 19, 35, 23, 33, 34, 31,
    56, 8, 9, 39, 54, 41, 57, 58, 1, 2, 46, 61, 48, 49, 14, 51, 52, 53,
    40, 66, 36, 42, 43, 68, 60, 47, 62, 63, 64, 65, 55, 71, 59, 69, 70, 67],
  ![44, 20, 2, 46, 19, 5, 23, 7, 36, 9, 39, 11, 12, 27, 14, 51, 16, 29,
    30, 4, 1, 32, 22, 6, 24, 25, 26, 13, 34, 17, 18, 31, 21, 33, 28, 35,
    8, 56, 38, 10, 55, 41, 59, 43, 0, 45, 3, 47, 48, 63, 50, 15, 52, 65,
    66, 40, 37, 68, 58, 42, 60, 61, 62, 49, 70, 53, 54, 67, 57, 69, 64, 71],
  ![23, 21, 47, 3, 4, 48, 44, 7, 42, 25, 10, 38, 41, 28, 14, 15, 52, 17,
    18, 19, 32, 1, 22, 0, 33, 9, 26, 34, 13, 29, 30, 31, 20, 24, 27, 35,
    59, 57, 11, 39, 40, 12, 8, 43, 6, 61, 46, 2, 5, 64, 50, 51, 16, 53,
    54, 55, 68, 37, 58, 36, 69, 45, 62, 70, 49, 65, 66, 67, 56, 60, 63, 71],
  ![0, 47, 21, 3, 4, 49, 45, 7, 25, 42, 26, 37, 28, 41, 14, 29, 16, 53,
    18, 31, 20, 2, 22, 23, 24, 8, 10, 27, 12, 15, 35, 19, 32, 33, 34, 30,
    36, 11, 57, 39, 40, 13, 9, 43, 61, 6, 62, 1, 64, 5, 50, 65, 52, 17,
    54, 67, 56, 38, 58, 59, 60, 44, 46, 63, 48, 51, 71, 55, 68, 69, 70, 66],
  ![24, 48, 49, 22, 50, 21, 6, 7, 8, 9, 10, 28, 37, 38, 40, 30, 16, 17,
    54, 19, 20, 5, 3, 33, 0, 25, 26, 27, 11, 35, 15, 31, 32, 23, 34, 29,
    60, 12, 13, 58, 14, 57, 42, 43, 44, 45, 46, 64, 1, 2, 4, 66, 52, 53,
    18, 55, 56, 41, 39, 69, 36, 61, 62, 63, 47, 71, 51, 67, 68, 59, 70, 65],
  ![48, 24, 2, 3, 51, 23, 6, 46, 8, 27, 43, 11, 36, 13, 30, 40, 16, 31,
    18, 55, 20, 33, 22, 5, 1, 34, 26, 9, 28, 29, 14, 17, 32, 21, 25, 35,
    12, 60, 38, 39, 15, 59, 42, 10, 44, 63, 7, 47, 0, 49, 66, 4, 52, 67,
    54, 19, 56, 69, 58, 41, 37, 70, 62, 45, 64, 65, 50, 53, 68, 57, 61, 71],
  ![50, 51, 2, 3, 24, 5, 26, 27, 8, 46, 45, 29, 30, 13, 36, 37, 32, 17,
    18, 19, 56, 21, 22, 23, 4, 25, 6, 7, 35, 11, 12, 31, 16, 33, 34, 28,
    14, 15, 38, 39, 60, 41, 62, 63, 44, 10, 9, 65, 66, 49, 0, 1, 68, 53,
    54, 55, 20, 57, 58, 59, 40, 61, 42, 43, 71, 47, 48, 67, 52, 69, 70, 64],
  ![26, 52, 53, 25, 4, 54, 50, 28, 8, 9, 10, 11, 12, 13, 42, 32, 37, 38,
    41, 33, 20, 57, 22, 23, 24, 3, 0, 35, 7, 29, 30, 31, 15, 19, 34, 27,
    62, 16, 17, 61, 40, 18, 14, 64, 44, 45, 46, 47, 48, 49, 6, 68, 1, 2,
    5, 69, 56, 21, 58, 59, 60, 39, 36, 71, 43, 65, 66, 67, 51, 55, 70, 63],
  ![27, 1, 2, 54, 4, 25, 28, 50, 49, 48, 30, 11, 45, 44, 43, 15, 16, 17,
    39, 19, 20, 21, 58, 34, 24, 5, 35, 0, 6, 29, 10, 31, 32, 33, 23, 26,
    63, 37, 38, 18, 40, 61, 64, 14, 13, 12, 66, 47, 9, 8, 7, 51, 52, 53,
    3, 55, 56, 57, 22, 70, 60, 41, 71, 36, 42, 65, 46, 67, 68, 69, 59, 62],
  ![52, 26, 2, 3, 4, 55, 51, 7, 8, 29, 47, 46, 12, 31, 32, 42, 36, 17,
    33, 41, 20, 21, 34, 59, 24, 25, 1, 27, 28, 9, 30, 13, 14, 18, 22, 35,
    16, 62, 38, 39, 40, 19, 15, 43, 44, 65, 11, 10, 48, 67, 68, 6, 0, 53,
    69, 5, 56, 57, 70, 23, 60, 61, 37, 63, 64, 45, 66, 49, 50, 54, 58, 71],
  ![54, 55, 2, 27, 56, 26, 6, 7, 30, 9, 49, 31, 12, 46, 14, 15, 33, 17,
    36, 37, 40, 21, 22, 23, 60, 35, 5, 3, 28, 29, 8, 11, 32, 16, 34, 25,
    18, 19, 38, 63, 20, 62, 42, 43, 66, 45, 13, 67, 48, 10, 50, 51, 69, 53,
    0, 1, 4, 57, 58, 59, 24, 71, 41, 39, 64, 65, 44, 47, 68, 52, 70, 61],
  ![29, 1, 2, 57, 28, 58, 6, 7, 53, 52, 32, 50, 12, 13, 47, 15, 45, 44,
    18, 34, 20, 39, 41, 23, 35, 61, 26, 27, 4, 0, 30, 31, 10, 33, 19, 24,
    65, 37, 38, 21, 64, 22, 42, 43, 17, 16, 68, 14, 48, 49, 11, 51, 9, 8,
    54, 70, 56, 3, 5, 59, 71, 25, 62, 63, 40, 36, 66, 67, 46, 69, 55, 60],
  ![57, 59, 2, 29, 4, 60, 56, 31, 32, 9, 53, 11, 33, 13, 14, 15, 16, 46,
    18, 19, 42, 36, 35, 37, 41, 25, 62, 27, 28, 3, 30, 7, 8, 12, 34, 22,
    21, 23, 38, 65, 40, 24, 20, 67, 68, 45, 17, 47, 69, 49, 50, 51, 52, 10,
    54, 55, 6, 0, 71, 1, 5, 61, 26, 63, 64, 39, 66, 43, 44, 48, 70, 58],
  ![58, 1, 30, 60, 4, 29, 31, 56, 8, 55, 10, 11, 12, 51, 14, 49, 34, 17,
    18, 45, 43, 35, 36, 23, 39, 25, 26, 63, 28, 5, 2, 6, 32, 33, 16, 21,
    22, 37, 66, 24, 40, 65, 67, 20, 44, 19, 46, 47, 48, 15, 50, 13, 70, 53,
    54, 9, 7, 71, 0, 59, 3, 61, 62, 27, 64, 41, 38, 42, 68, 69, 52, 57],
  ![31, 1, 2, 3, 61, 5, 58, 57, 8, 9, 33, 54, 53, 52, 14, 34, 49, 48,
    47, 19, 35, 43, 42, 23, 24, 40, 26, 27, 64, 29, 30, 0, 32, 10, 15, 20,
    67, 37, 38, 39, 25, 41, 22, 21, 44, 45, 69, 18, 17, 16, 50, 70, 13, 12,
    11, 55, 71, 7, 6, 59, 60, 4, 62, 63, 28, 65, 66, 36, 68, 46, 51, 56],
  ![61, 1, 32, 62, 31, 63, 6, 7, 8, 59, 10, 56, 34, 13, 14, 53, 16, 51,
    35, 19, 47, 21, 22, 45, 24, 36, 39, 41, 28, 65, 30, 4, 2, 33, 12, 18,
    25, 37, 68, 26, 67, 27, 42, 43, 44, 23, 46, 20, 70, 49, 50, 17, 52, 15,
    71, 55, 11, 57, 58, 9, 60, 0, 3, 5, 64, 29, 66, 40, 38, 69, 48, 54],
  ![0, 1, 63, 3, 4, 32, 33, 7, 60, 9, 58, 34, 56, 13, 55, 54, 16, 35,
    51, 50, 48, 21, 46, 23, 44, 25, 26, 38, 28, 29, 66, 31, 5, 6, 11, 17,
    36, 37, 27, 39, 40, 68, 69, 43, 24, 45, 22, 70, 20, 49, 19, 18, 52, 71,
    15, 14, 12, 57, 10, 59, 8, 61, 62, 2, 64, 65, 30, 67, 41, 42, 47, 53],
  ![64, 1, 33, 3, 65, 5, 63, 62, 34, 9, 10, 60, 12, 59, 35, 15, 16, 55,
    18, 53, 20, 21, 22, 49, 47, 25, 43, 42, 36, 40, 30, 67, 32, 2, 8, 14,
    28, 37, 69, 39, 29, 41, 27, 26, 70, 45, 46, 24, 48, 23, 71, 51, 52, 19,
    54, 17, 56, 57, 58, 13, 11, 61, 7, 6, 0, 4, 66, 31, 68, 38, 44, 50],
  ![0, 1, 65, 3, 33, 66, 6, 34, 62, 9, 61, 11, 12, 35, 59, 57, 56, 17,
    18, 19, 52, 51, 22, 50, 24, 46, 44, 27, 28, 38, 41, 31, 68, 4, 7, 13,
    36, 37, 29, 39, 69, 30, 42, 70, 26, 45, 25, 47, 48, 71, 23, 21, 20, 53,
    54, 55, 16, 15, 58, 14, 60, 10, 8, 63, 64, 2, 5, 67, 32, 40, 43, 49],
  ![0, 1, 67, 34, 68, 5, 66, 7, 8, 35, 64, 11, 62, 13, 14, 15, 60, 17,
    59, 57, 20, 55, 22, 54, 52, 25, 48, 27, 46, 29, 42, 38, 40, 69, 3, 9,
    36, 37, 31, 70, 32, 41, 30, 43, 44, 71, 28, 47, 26, 49, 50, 51, 24, 53,
    23, 21, 56, 19, 58, 18, 16, 61, 12, 63, 10, 65, 6, 2, 4, 33, 39, 45],
  ![0, 35, 2, 69, 4, 5, 6, 68, 67, 9, 10, 66, 65, 13, 14, 64, 63, 17,
    18, 61, 20, 21, 59, 58, 24, 55, 26, 52, 51, 48, 47, 44, 43, 39, 70, 1,
    36, 71, 38, 33, 40, 41, 42, 32, 31, 45, 46, 30, 29, 49, 50, 28, 27, 53,
    54, 25, 56, 57, 23, 22, 60, 19, 62, 16, 15, 12, 11, 8, 7, 3, 34, 37],
  ![0, 70, 2, 3, 4, 5, 6, 7, 8, 69, 10, 11, 12, 68, 67, 15, 16, 66,
    65, 19, 64, 63, 62, 23, 61, 60, 58, 57, 56, 54, 53, 50, 49, 45, 37, 71,
    36, 34, 38, 39, 40, 41, 42, 43, 44, 33, 46, 47, 48, 32, 31, 51, 52, 30,
    29, 55, 28, 27, 26, 59, 25, 24, 22, 21, 20, 18, 17, 14, 13, 9, 1, 35]]

/-- Reflection in the root indexed by `i`, as an operation on root indices. Only the residue of `i`
modulo `36` is used, a positive root and its negative reflecting alike. -/
private def e6ReflectionIndex (i j : Fin 72) : Fin 72 :=
  e6ReflectionTable ⟨(i : ℕ) % 36, Nat.mod_lt _ (by omega)⟩ j

/-- The coroot reflection identity for a positive-root index and an arbitrary root index. -/
private abbrev e6ReflectionIndexCorootProp (i : Fin 36) (j : Fin 72) : Prop :=
  e6Coroot j - (e6Root (e6PositiveIndex i) ⬝ᵥ e6Coroot j) • e6Coroot (e6PositiveIndex i) =
    e6Coroot (e6ReflectionIndex (e6PositiveIndex i) j)

private lemma e6ReflectionIndex_coroot_pos_zero (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos_six (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i + 6, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos_twelve (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i + 12, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos_eighteen (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i + 18, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos_twenty_four (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i + 24, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos_thirty (i : Fin 6) (j : Fin 72) :
    e6ReflectionIndexCorootProp ⟨i + 30, by omega⟩ j := by
  fin_cases i <;> decide +kernel +revert

private lemma e6ReflectionIndex_coroot_pos (i : Fin 36) (j : Fin 72) :
    e6Coroot j - (e6Root (e6PositiveIndex i) ⬝ᵥ e6Coroot j) • e6Coroot (e6PositiveIndex i) =
      e6Coroot (e6ReflectionIndex (e6PositiveIndex i) j) := by
  change e6ReflectionIndexCorootProp i j
  rcases lt_or_ge (i : ℕ) 6 with hi | hi
  · let a : Fin 6 := ⟨i, hi⟩
    have hia : i = (⟨a, by omega⟩ : Fin 36) := Fin.ext rfl
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_zero a j
  rcases lt_or_ge (i : ℕ) 12 with hi' | hi'
  · let a : Fin 6 := ⟨(i : ℕ) - 6, by omega⟩
    have hia : i = (⟨a + 6, by omega⟩ : Fin 36) := Fin.ext (by simp [a]; omega)
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_six a j
  rcases lt_or_ge (i : ℕ) 18 with hi'' | hi''
  · let a : Fin 6 := ⟨(i : ℕ) - 12, by omega⟩
    have hia : i = (⟨a + 12, by omega⟩ : Fin 36) := Fin.ext (by simp [a]; omega)
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_twelve a j
  rcases lt_or_ge (i : ℕ) 24 with hi''' | hi'''
  · let a : Fin 6 := ⟨(i : ℕ) - 18, by omega⟩
    have hia : i = (⟨a + 18, by omega⟩ : Fin 36) := Fin.ext (by simp [a]; omega)
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_eighteen a j
  rcases lt_or_ge (i : ℕ) 30 with hi'''' | hi''''
  · let a : Fin 6 := ⟨(i : ℕ) - 24, by omega⟩
    have hia : i = (⟨a + 24, by omega⟩ : Fin 36) := Fin.ext (by simp [a]; omega)
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_twenty_four a j
  · let a : Fin 6 := ⟨(i : ℕ) - 30, by omega⟩
    have hia : i = (⟨a + 30, by omega⟩ : Fin 36) := Fin.ext (by simp [a]; omega)
    rw [hia]
    exact e6ReflectionIndex_coroot_pos_thirty a j

private lemma e6ReflectionIndex_e6NegativeIndex (i : Fin 36) (j : Fin 72) :
    e6ReflectionIndex (e6NegativeIndex i) j = e6ReflectionIndex (e6PositiveIndex i) j := by
  simp only [e6ReflectionIndex, e6NegativeIndex_val, e6PositiveIndex_val, Nat.add_mod_right]

private lemma e6ReflectionIndex_coroot (i j : Fin 72) :
    e6Coroot j - (e6Root i ⬝ᵥ e6Coroot j) • e6Coroot i = e6Coroot (e6ReflectionIndex i j) := by
  rcases lt_or_ge (i : ℕ) 36 with hi | hi
  · have hip : i = e6PositiveIndex ⟨i, hi⟩ := Fin.ext rfl
    rw [hip]
    exact e6ReflectionIndex_coroot_pos _ j
  · have hin : i = e6NegativeIndex ⟨(i : ℕ) - 36, by omega⟩ := Fin.ext (by simp; omega)
    rw [hin, e6Coroot_e6NegativeIndex, e6Root_e6NegativeIndex, e6ReflectionIndex_e6NegativeIndex]
    simpa using e6ReflectionIndex_coroot_pos _ j

/-- The root reflections are the image of the coroot reflections under the Cartan-matrix map, so
they need no second table. -/
private lemma e6ReflectionIndex_root (i j : Fin 72) :
    e6Root j - (e6Root j ⬝ᵥ e6Coroot i) • e6Root i = e6Root (e6ReflectionIndex i j) := by
  have h : CartanMatrix.E 6 *ᵥ (e6Coroot j - (e6Root i ⬝ᵥ e6Coroot j) • e6Coroot i) =
      CartanMatrix.E 6 *ᵥ e6Coroot (e6ReflectionIndex i j) :=
    congrArg _ (e6ReflectionIndex_coroot i j)
  rw [mulVec_sub, mulVec_smul] at h
  simp only [← e6Root_eq_mulVec] at h
  rw [e6Root_dotProduct_e6Coroot_comm j i]
  exact h

private lemma e6ReflectionIndex_involutive (i : Fin 72) :
    Function.Involutive (e6ReflectionIndex i) := by
  intro j
  apply e6Root.injective
  rw [← e6ReflectionIndex_root i (e6ReflectionIndex i j), ← e6ReflectionIndex_root i j]
  have hpair : (e6Root j - (e6Root j ⬝ᵥ e6Coroot i) • e6Root i) ⬝ᵥ e6Coroot i =
      -(e6Root j ⬝ᵥ e6Coroot i) := by
    rw [sub_dotProduct, smul_dotProduct, e6Root_dotProduct_e6Coroot_self]
    ring
  rw [hpair]
  simp

/-- Reflection in an `E₆` root as a permutation of the pinned root indices. -/
private def e6ReflectionPerm (i : Fin 72) : Fin 72 ≃ Fin 72 :=
  Function.Involutive.toPerm (e6ReflectionIndex i) (e6ReflectionIndex_involutive i)

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₆`.

Both lattices are `Fin 6 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `5` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e6SimpleIndex`. -/
def e6SimplyConnectedRootDatum : RootDatum (Fin 72) (Fin 6 → ℤ) (Fin 6 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 6)).toLinearMap
  root := e6Root
  coroot := e6Coroot
  root_coroot_two i := e6Root_dotProduct_e6Coroot_self i
  reflectionPerm := e6ReflectionPerm
  reflectionPerm_root i j := e6ReflectionIndex_root i j
  reflectionPerm_coroot i j := e6ReflectionIndex_coroot i j

/-- The root embedding of the pinned `E₆` datum is the explicit table `e6Root`. -/
@[simp] lemma e6SimplyConnectedRootDatum_root : e6SimplyConnectedRootDatum.root = e6Root := (rfl)

/-- The coroot embedding of the pinned `E₆` datum is the explicit table `e6Coroot`. -/
@[simp] lemma e6SimplyConnectedRootDatum_coroot :
    e6SimplyConnectedRootDatum.coroot = e6Coroot := (rfl)

/-- The perfect pairing of the pinned `E₆` datum is the dot product of coordinate vectors, the
fundamental-weight and simple-coroot bases being dual to one another. -/
@[simp] lemma e6SimplyConnectedRootDatum_toLinearMap (x y : Fin 6 → ℤ) :
    e6SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `E₆` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma e6SimplyConnectedRootDatum_pairing (i j : Fin 72) :
    e6SimplyConnectedRootDatum.pairing i j = e6Root i ⬝ᵥ e6Coroot j := (rfl)

/-- **The coroots of the pinned type `E₆` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. Its
counterpart for the roots is deliberately absent: they span the root lattice, which sits inside the
weight lattice with index `3` (Bourbaki, Plate V). -/
theorem corootSpan_e6SimplyConnectedRootDatum_eq_top :
    e6SimplyConnectedRootDatum.corootSpan ℤ = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun ℤ (Fin 6)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨e6SimpleIndex i, by rw [e6SimplyConnectedRootDatum_coroot, coroot_e6SimpleIndex]; simp⟩

/-! ## The pinned base -/

/-- The support of the pinned base of type `E₆`: the first six root indices. -/
private def e6SimpleSupport : Finset (Fin 72) :=
  simpleSupport e6SimpleIndex_injective

private lemma mem_e6SimpleSupport {k : Fin 72} : k ∈ e6SimpleSupport ↔ (k : ℕ) < 6 :=
  mem_simpleSupport_iff_lt e6SimpleIndex_injective (fun _ ↦ e6SimpleIndex_val _)

private lemma coe_e6SimpleSupport :
    (e6SimpleSupport : Set (Fin 72)) = range e6SimpleIndex :=
  coe_simpleSupport _

/-- The nonnegative simple-root coordinates of the `i`-th positive root of type `E₆`. Both lattices
carry them: the coroot is `∑ k, cₖ αₖ^∨` by the choice of basis, and the root is `∑ k, cₖ αₖ`
because the two tables differ by the linear map `e6Root_eq_mulVec`. -/
private def e6PositiveCoefficient (i : Fin 36) (k : Fin 6) : ℕ :=
  (e6Coroot (e6PositiveIndex i) k).toNat

private lemma e6Coroot_eq_sum (i : Fin 36) :
    ∑ k, e6PositiveCoefficient i k • e6Coroot (e6SimpleIndex k) =
      e6Coroot (e6PositiveIndex i) := by
  decide +kernel +revert

private lemma e6Root_eq_sum (i : Fin 36) :
    ∑ k, e6PositiveCoefficient i k • e6Root (e6SimpleIndex k) = e6Root (e6PositiveIndex i) := by
  have h := congrArg (CartanMatrix.E 6).mulVecLin (e6Coroot_eq_sum i)
  rw [map_sum] at h
  simpa only [map_nsmul, mulVecLin_apply, ← e6Root_eq_mulVec] using h

/-- Every root of type `E₆` is a nonnegative integer combination of the simple roots, or the
negative of one. The argument uses only the coefficient expansion of the positive half and the
negation symmetry of the table, so it serves the roots and the coroots alike. -/
private lemma mem_or_neg_mem_of_eq_sum (f : Fin 72 → (Fin 6 → ℤ))
    (hsum : ∀ i, ∑ k, e6PositiveCoefficient i k • f (e6SimpleIndex k) = f (e6PositiveIndex i))
    (hneg : ∀ i, f (e6NegativeIndex i) = -f (e6PositiveIndex i)) (i : Fin 72) :
    f i ∈ AddSubmonoid.closure (f '' (e6SimpleSupport : Set (Fin 72))) ∨
      -f i ∈ AddSubmonoid.closure (f '' (e6SimpleSupport : Set (Fin 72))) := by
  set C := AddSubmonoid.closure (f '' (e6SimpleSupport : Set (Fin 72))) with hC
  have hsimple (k : Fin 6) : f (e6SimpleIndex k) ∈ C :=
    AddSubmonoid.subset_closure ⟨e6SimpleIndex k, by rw [coe_e6SimpleSupport]; exact ⟨k, rfl⟩, rfl⟩
  have hpos (k : Fin 36) : f (e6PositiveIndex k) ∈ C := by
    rw [← hsum k]
    exact C.sum_mem fun j _ => C.nsmul_mem (hsimple j) _
  rcases lt_or_ge (i : ℕ) 36 with hi | hi
  · exact Or.inl (by simpa [e6PositiveIndex, Fin.ext_iff] using hpos ⟨i, hi⟩)
  · refine Or.inr ?_
    have hin : i = e6NegativeIndex ⟨(i : ℕ) - 36, by omega⟩ := Fin.ext (by simp; omega)
    rw [hin, hneg, neg_neg]
    exact hpos _

private lemma linearIndepOn_e6Root :
    LinearIndepOn ℤ e6Root (e6SimpleSupport : Set (Fin 72)) := by
  rw [coe_e6SimpleSupport, linearIndepOn_range_iff e6SimpleIndex_injective]
  have hcomp : e6Root ∘ e6SimpleIndex = fun i => CartanMatrix.E 6 i :=
    funext root_e6SimpleIndex
  rw [hcomp]
  exact Matrix.linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.E₆_det]; norm_num)

private lemma linearIndepOn_e6Coroot :
    LinearIndepOn ℤ e6Coroot (e6SimpleSupport : Set (Fin 72)) := by
  rw [coe_e6SimpleSupport, linearIndepOn_range_iff e6SimpleIndex_injective]
  have hcomp : e6Coroot ∘ e6SimpleIndex = fun i => (Pi.basisFun ℤ (Fin 6)) i :=
    funext fun i => by rw [Function.comp_apply, coroot_e6SimpleIndex]; simp
  rw [hcomp]
  exact (Pi.basisFun ℤ (Fin 6)).linearIndependent

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₆`. Its support
is the set of the first six root indices, carrying the simple roots in Bourbaki order. -/
def e6SimplyConnectedBase : e6SimplyConnectedRootDatum.Base where
  support := e6SimpleSupport
  linearIndepOn_root := linearIndepOn_e6Root
  linearIndepOn_coroot := linearIndepOn_e6Coroot
  root_mem_or_neg_mem :=
    mem_or_neg_mem_of_eq_sum e6Root e6Root_eq_sum e6Root_e6NegativeIndex
  coroot_mem_or_neg_mem :=
    mem_or_neg_mem_of_eq_sum e6Coroot e6Coroot_eq_sum e6Coroot_e6NegativeIndex

/-- Membership in the pinned base support is exactly membership among the first six root
indices. -/
@[simp] theorem mem_e6SimplyConnectedBase_support {k : Fin 72} :
    k ∈ e6SimplyConnectedBase.support ↔ (k : ℕ) < 6 :=
  mem_e6SimpleSupport

/-- **The Cartan integers at the first six root indices are Mathlib's Bourbaki-numbered `E₆`
matrix.** This pins the node order independently of the existential relabelling in
`TauCeti.HasCartanType`. -/
theorem pairing_e6SimpleIndex (i j : Fin 6) :
    e6SimplyConnectedRootDatum.pairing (e6SimpleIndex i) (e6SimpleIndex j) =
      CartanMatrix.E 6 i j := by
  rw [e6SimplyConnectedRootDatum_pairing, root_e6SimpleIndex, coroot_e6SimpleIndex,
    dotProduct_single, mul_one]

/-- Identify the support of the type-`E₆` base with its six Bourbaki-numbered nodes. -/
private def e6BaseEquiv : e6SimplyConnectedBase.support ≃ Fin 6 where
  toFun x := ⟨(x : Fin 72), mem_e6SimpleSupport.mp x.2⟩
  invFun i := ⟨e6SimpleIndex i, mem_e6SimpleSupport.mpr (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    simp
  right_inv i := by
    apply Fin.ext
    simp

/-- **The pinned datum of type `E₆` has Cartan type `E6`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.E 6`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_e6SimplyConnectedRootDatum :
    HasCartanType e6SimplyConnectedRootDatum e6SimplyConnectedBase E6 := by
  rw [hasCartanType_iff]
  refine ⟨e6BaseEquiv, fun i j => ?_⟩
  have hi : (i : Fin 72) = e6SimpleIndex (e6BaseEquiv i) := Fin.ext (by simp [e6BaseEquiv])
  have hj : (j : Fin 72) = e6SimpleIndex (e6BaseEquiv j) := Fin.ext (by simp [e6BaseEquiv])
  rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply, hi, hj, pairing_e6SimpleIndex,
    cartanMatrix_E6]
  rfl

end DynkinType

end TauCeti
