/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# The simply connected root datum of type F4

This file constructs the pinned integral root datum of type `F4` on the character and cocharacter
lattices `Fin 4 → ℤ`. The character lattice is written in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Thus the first four roots are the rows of the
Bourbaki-numbered Cartan matrix, while their coroots are the standard basis vectors.

The forty-eight roots are ordered with the four simple roots first, then the other twenty positive
roots, and finally their negatives in the same order. The coordinate tables make both the carrier
and every reflection explicit. The first two simple roots are long and the last two are short.

## Main definitions and results

* `TauCeti.DynkinType.f4SimplyConnectedRootDatum` is the pinned forty-eight-root datum.
* `TauCeti.DynkinType.f4SimplyConnectedBase` is its Bourbaki-numbered base.
* `TauCeti.DynkinType.f4SimplyConnectedRootDatum_pairing_eq_cartanMatrix_F4` pins the numbering.
* `TauCeti.DynkinType.hasCartanType_f4SimplyConnectedRootDatum` identifies its Cartan type.

## References

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VIII. In the standard orthonormal coordinates the long roots are `±eᵢ ± eⱼ`, while the short
roots are `±eᵢ` and `(±e₁ ± e₂ ± e₃ ± e₄) / 2`. This is the `F4` branch of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open _root_.Matrix Module Set Submodule

namespace DynkinType

/-- The roots of `F4` in the fundamental-weight basis, with the simple roots first and the
negative roots in the second half. -/
def f4Root : Fin 48 ↪ (Fin 4 → ℤ) where
  toFun := ![
    ![2, -1, 0, 0], ![-1, 2, -2, 0], ![0, -1, 2, -1], ![0, 0, -1, 2],
    ![0, -1, 1, 1], ![-1, 1, 0, -1], ![-1, 1, -1, 1], ![-1, 0, 2, -2],
    ![-1, 0, 1, 0], ![-1, 0, 0, 2], ![1, 1, -2, 0], ![1, 0, 0, -1],
    ![1, 0, -1, 1], ![1, -1, 2, -2], ![1, -1, 1, 0], ![1, -1, 0, 2],
    ![0, 1, 0, -2], ![0, 1, -1, 0], ![0, 1, -2, 2], ![0, 0, 1, -1],
    ![0, 0, 0, 1], ![0, -1, 2, 0], ![-1, 1, 0, 0], ![1, 0, 0, 0],
    ![-2, 1, 0, 0], ![1, -2, 2, 0], ![0, 1, -2, 1], ![0, 0, 1, -2],
    ![0, 1, -1, -1], ![1, -1, 0, 1], ![1, -1, 1, -1], ![1, 0, -2, 2],
    ![1, 0, -1, 0], ![1, 0, 0, -2], ![-1, -1, 2, 0], ![-1, 0, 0, 1],
    ![-1, 0, 1, -1], ![-1, 1, -2, 2], ![-1, 1, -1, 0], ![-1, 1, 0, -2],
    ![0, -1, 0, 2], ![0, -1, 1, 0], ![0, -1, 2, -2], ![0, 0, -1, 1],
    ![0, 0, 0, -1], ![0, 1, -2, 0], ![1, -1, 0, 0], ![-1, 0, 0, 0]]
  inj' := by decide

/-- The coroots of `F4` in the simple-coroot basis, ordered compatibly with `f4Root`. -/
def f4Coroot : Fin 48 ↪ (Fin 4 → ℤ) where
  toFun := ![
    ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![0, 0, 1, 1], ![0, 2, 1, 0], ![0, 2, 1, 1], ![0, 1, 1, 0],
    ![0, 2, 2, 1], ![0, 1, 1, 1], ![1, 1, 0, 0], ![2, 2, 1, 0],
    ![2, 2, 1, 1], ![1, 1, 1, 0], ![2, 2, 2, 1], ![1, 1, 1, 1],
    ![1, 2, 1, 0], ![2, 4, 2, 1], ![1, 2, 1, 1], ![2, 4, 3, 1],
    ![2, 4, 3, 2], ![1, 2, 2, 1], ![1, 3, 2, 1], ![2, 3, 2, 1],
    ![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1],
    ![0, 0, -1, -1], ![0, -2, -1, 0], ![0, -2, -1, -1], ![0, -1, -1, 0],
    ![0, -2, -2, -1], ![0, -1, -1, -1], ![-1, -1, 0, 0], ![-2, -2, -1, 0],
    ![-2, -2, -1, -1], ![-1, -1, -1, 0], ![-2, -2, -2, -1], ![-1, -1, -1, -1],
    ![-1, -2, -1, 0], ![-2, -4, -2, -1], ![-1, -2, -1, -1], ![-2, -4, -3, -1],
    ![-2, -4, -3, -2], ![-1, -2, -2, -1], ![-1, -3, -2, -1], ![-2, -3, -2, -1]]
  inj' := by decide

/-- The first-half index underlying a root, identifying a negative root with its positive
opposite. -/
private def f4PositiveIndex (i : Fin 48) : Fin 24 := ⟨i % 24, Nat.mod_lt _ (by omega)⟩

/-- The permutation table for reflection in each of the twenty-four positive `F4` roots. Reflection
in the corresponding negative root is the same permutation. -/
private def f4ReflectionTable : Fin 24 → Fin 48 → Fin 48 := ![
  ![24, 10, 2, 3, 4, 11, 12, 13, 14, 15, 1, 5, 6, 7, 8, 9,
    16, 17, 18, 19, 20, 21, 23, 22, 0, 34, 26, 27, 28, 35, 36, 37,
    38, 39, 25, 29, 30, 31, 32, 33, 40, 41, 42, 43, 44, 45, 47, 46],
  ![10, 25, 5, 3, 6, 2, 4, 7, 8, 9, 0, 11, 12, 16, 17, 18,
    13, 14, 15, 19, 20, 22, 21, 23, 34, 1, 29, 27, 30, 26, 28, 31,
    32, 33, 24, 35, 36, 40, 41, 42, 37, 38, 39, 43, 44, 46, 45, 47],
  ![0, 7, 26, 4, 3, 5, 8, 1, 6, 9, 13, 11, 14, 10, 12, 15,
    16, 19, 21, 17, 20, 18, 22, 23, 24, 31, 2, 28, 27, 29, 32, 25,
    30, 33, 37, 35, 38, 34, 36, 39, 40, 43, 45, 41, 44, 42, 46, 47],
  ![0, 1, 4, 27, 2, 6, 5, 9, 8, 7, 10, 12, 11, 15, 14, 13,
    18, 17, 16, 20, 19, 21, 22, 23, 24, 25, 28, 3, 26, 30, 29, 33,
    32, 31, 34, 36, 35, 39, 38, 37, 42, 41, 40, 44, 43, 45, 46, 47],
  ![0, 9, 27, 26, 28, 8, 6, 7, 5, 1, 15, 14, 12, 13, 11, 10,
    21, 20, 18, 19, 17, 16, 22, 23, 24, 33, 3, 2, 4, 32, 30, 31,
    29, 25, 39, 38, 36, 37, 35, 34, 45, 44, 42, 43, 41, 40, 46, 47],
  ![16, 31, 2, 6, 8, 29, 3, 25, 4, 9, 10, 11, 17, 13, 19, 22,
    0, 12, 18, 14, 20, 21, 15, 23, 40, 7, 26, 30, 32, 5, 27, 1,
    28, 33, 34, 35, 41, 37, 43, 46, 24, 36, 42, 38, 44, 45, 39, 47],
  ![18, 33, 8, 29, 4, 27, 30, 7, 2, 25, 10, 17, 12, 22, 20, 15,
    16, 11, 0, 19, 14, 21, 13, 23, 42, 9, 32, 5, 28, 3, 6, 31,
    26, 1, 34, 41, 36, 46, 44, 39, 40, 35, 24, 43, 38, 45, 37, 47],
  ![13, 1, 29, 8, 4, 26, 6, 31, 3, 9, 16, 11, 19, 0, 14, 21,
    10, 17, 22, 12, 20, 15, 18, 23, 37, 25, 5, 32, 28, 2, 30, 7,
    27, 33, 40, 35, 43, 24, 38, 45, 34, 41, 46, 36, 44, 39, 42, 47],
  ![21, 1, 30, 3, 29, 28, 26, 33, 32, 31, 22, 19, 20, 13, 14, 15,
    16, 17, 18, 11, 12, 0, 10, 23, 45, 25, 6, 27, 5, 4, 2, 9,
    8, 7, 46, 43, 44, 37, 38, 39, 40, 41, 42, 35, 36, 24, 34, 47],
  ![15, 1, 2, 32, 30, 5, 28, 7, 27, 33, 18, 20, 12, 21, 14, 0,
    22, 17, 10, 19, 11, 13, 16, 23, 39, 25, 26, 8, 6, 29, 4, 31,
    3, 9, 42, 44, 36, 45, 38, 24, 46, 41, 34, 43, 35, 37, 40, 47],
  ![25, 24, 11, 3, 12, 5, 6, 16, 17, 18, 34, 2, 4, 13, 14, 15,
    7, 8, 9, 19, 20, 23, 22, 21, 1, 0, 35, 27, 36, 29, 30, 40,
    41, 42, 10, 26, 28, 37, 38, 39, 31, 32, 33, 43, 44, 47, 46, 45],
  ![40, 1, 2, 12, 14, 5, 17, 7, 19, 23, 37, 35, 3, 34, 4, 15,
    24, 6, 18, 8, 20, 21, 22, 9, 16, 25, 26, 36, 38, 29, 41, 31,
    43, 47, 13, 11, 27, 10, 28, 39, 0, 30, 42, 32, 44, 45, 46, 33],
  ![42, 1, 14, 35, 4, 17, 6, 23, 20, 9, 39, 27, 36, 13, 2, 34,
    16, 5, 24, 19, 8, 21, 22, 7, 18, 25, 38, 11, 28, 41, 30, 47,
    44, 33, 15, 3, 12, 37, 26, 10, 40, 29, 0, 43, 32, 45, 46, 31],
  ![31, 16, 35, 14, 4, 5, 19, 24, 8, 21, 10, 26, 12, 37, 3, 15,
    1, 17, 23, 6, 20, 9, 22, 18, 7, 40, 11, 38, 28, 29, 43, 0,
    32, 45, 34, 2, 36, 13, 27, 39, 25, 41, 47, 30, 44, 33, 46, 42],
  ![45, 23, 36, 3, 35, 19, 20, 7, 8, 9, 10, 28, 26, 39, 38, 37,
    16, 17, 18, 5, 6, 24, 22, 1, 21, 47, 12, 27, 11, 43, 44, 31,
    32, 33, 34, 4, 2, 15, 14, 13, 40, 41, 42, 29, 30, 0, 46, 25],
  ![33, 18, 2, 38, 36, 20, 6, 21, 8, 24, 10, 11, 28, 13, 27, 39,
    23, 17, 1, 19, 5, 7, 22, 16, 9, 42, 26, 14, 12, 44, 30, 45,
    32, 0, 34, 35, 4, 37, 3, 15, 47, 41, 25, 43, 29, 31, 46, 40],
  ![0, 37, 2, 17, 19, 35, 6, 34, 8, 22, 31, 29, 12, 25, 14, 23,
    40, 3, 18, 4, 20, 21, 9, 15, 24, 13, 26, 41, 43, 11, 30, 10,
    32, 46, 7, 5, 36, 1, 38, 47, 16, 27, 42, 28, 44, 45, 33, 39],
  ![0, 47, 19, 3, 20, 36, 35, 7, 8, 9, 46, 30, 29, 13, 14, 15,
    42, 41, 40, 2, 4, 21, 34, 25, 24, 23, 43, 27, 44, 12, 11, 31,
    32, 33, 22, 6, 5, 37, 38, 39, 18, 17, 16, 26, 28, 45, 10, 1],
  ![0, 39, 20, 41, 4, 5, 36, 22, 8, 34, 33, 11, 30, 23, 14, 25,
    16, 27, 42, 19, 2, 21, 7, 13, 24, 15, 44, 17, 28, 29, 12, 46,
    32, 10, 9, 35, 6, 47, 38, 1, 40, 3, 18, 43, 26, 45, 31, 37],
  ![0, 1, 41, 20, 4, 38, 6, 47, 35, 9, 10, 32, 12, 46, 29, 15,
    45, 26, 18, 43, 3, 40, 37, 31, 24, 25, 17, 44, 28, 14, 30, 23,
    11, 33, 34, 8, 36, 22, 5, 39, 21, 2, 42, 19, 27, 16, 13, 7],
  ![0, 1, 2, 43, 41, 5, 38, 7, 36, 47, 10, 11, 32, 13, 30, 46,
    16, 28, 45, 27, 44, 42, 39, 33, 24, 25, 26, 19, 17, 29, 14, 31,
    12, 23, 34, 35, 8, 37, 6, 22, 40, 4, 21, 3, 20, 18, 15, 9],
  ![0, 22, 44, 3, 43, 5, 6, 39, 38, 37, 23, 11, 12, 33, 32, 31,
    16, 17, 18, 28, 26, 45, 1, 10, 24, 46, 20, 27, 19, 29, 30, 15,
    14, 13, 47, 35, 36, 9, 8, 7, 40, 41, 42, 4, 2, 21, 25, 34],
  ![23, 45, 2, 3, 4, 44, 43, 42, 41, 40, 10, 11, 12, 13, 14, 15,
    33, 32, 31, 30, 29, 25, 46, 0, 47, 21, 26, 27, 28, 20, 19, 18,
    17, 16, 34, 35, 36, 37, 38, 39, 9, 8, 7, 6, 5, 1, 22, 24],
  ![46, 1, 2, 3, 4, 5, 6, 7, 8, 9, 45, 44, 43, 42, 41, 40,
    39, 38, 37, 36, 35, 34, 24, 47, 22, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 0, 23]]

private def f4ReflectionIndex (i j : Fin 48) : Fin 48 := f4ReflectionTable (f4PositiveIndex i) j

private lemma f4ReflectionIndex_root_0 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 0) • f4Root 0 = f4Root (f4ReflectionIndex 0 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_1 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 1) • f4Root 1 = f4Root (f4ReflectionIndex 1 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_2 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 2) • f4Root 2 = f4Root (f4ReflectionIndex 2 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_3 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 3) • f4Root 3 = f4Root (f4ReflectionIndex 3 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_4 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 4) • f4Root 4 = f4Root (f4ReflectionIndex 4 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_5 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 5) • f4Root 5 = f4Root (f4ReflectionIndex 5 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_6 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 6) • f4Root 6 = f4Root (f4ReflectionIndex 6 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_7 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 7) • f4Root 7 = f4Root (f4ReflectionIndex 7 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_8 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 8) • f4Root 8 = f4Root (f4ReflectionIndex 8 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_9 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 9) • f4Root 9 = f4Root (f4ReflectionIndex 9 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_10 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 10) • f4Root 10 = f4Root (f4ReflectionIndex 10 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_11 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 11) • f4Root 11 = f4Root (f4ReflectionIndex 11 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_12 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 12) • f4Root 12 = f4Root (f4ReflectionIndex 12 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_13 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 13) • f4Root 13 = f4Root (f4ReflectionIndex 13 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_14 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 14) • f4Root 14 = f4Root (f4ReflectionIndex 14 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_15 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 15) • f4Root 15 = f4Root (f4ReflectionIndex 15 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_16 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 16) • f4Root 16 = f4Root (f4ReflectionIndex 16 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_17 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 17) • f4Root 17 = f4Root (f4ReflectionIndex 17 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_18 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 18) • f4Root 18 = f4Root (f4ReflectionIndex 18 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_19 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 19) • f4Root 19 = f4Root (f4ReflectionIndex 19 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_20 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 20) • f4Root 20 = f4Root (f4ReflectionIndex 20 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_21 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 21) • f4Root 21 = f4Root (f4ReflectionIndex 21 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_22 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 22) • f4Root 22 = f4Root (f4ReflectionIndex 22 j) := by
  decide +revert
private lemma f4ReflectionIndex_root_23 (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot 23) • f4Root 23 = f4Root (f4ReflectionIndex 23 j) := by
  decide +revert

private lemma f4ReflectionIndex_coroot_0 (j : Fin 48) :
    f4Coroot j - (f4Root 0 ⬝ᵥ f4Coroot j) • f4Coroot 0 = f4Coroot (f4ReflectionIndex 0 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_1 (j : Fin 48) :
    f4Coroot j - (f4Root 1 ⬝ᵥ f4Coroot j) • f4Coroot 1 = f4Coroot (f4ReflectionIndex 1 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_2 (j : Fin 48) :
    f4Coroot j - (f4Root 2 ⬝ᵥ f4Coroot j) • f4Coroot 2 = f4Coroot (f4ReflectionIndex 2 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_3 (j : Fin 48) :
    f4Coroot j - (f4Root 3 ⬝ᵥ f4Coroot j) • f4Coroot 3 = f4Coroot (f4ReflectionIndex 3 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_4 (j : Fin 48) :
    f4Coroot j - (f4Root 4 ⬝ᵥ f4Coroot j) • f4Coroot 4 = f4Coroot (f4ReflectionIndex 4 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_5 (j : Fin 48) :
    f4Coroot j - (f4Root 5 ⬝ᵥ f4Coroot j) • f4Coroot 5 = f4Coroot (f4ReflectionIndex 5 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_6 (j : Fin 48) :
    f4Coroot j - (f4Root 6 ⬝ᵥ f4Coroot j) • f4Coroot 6 = f4Coroot (f4ReflectionIndex 6 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_7 (j : Fin 48) :
    f4Coroot j - (f4Root 7 ⬝ᵥ f4Coroot j) • f4Coroot 7 = f4Coroot (f4ReflectionIndex 7 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_8 (j : Fin 48) :
    f4Coroot j - (f4Root 8 ⬝ᵥ f4Coroot j) • f4Coroot 8 = f4Coroot (f4ReflectionIndex 8 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_9 (j : Fin 48) :
    f4Coroot j - (f4Root 9 ⬝ᵥ f4Coroot j) • f4Coroot 9 = f4Coroot (f4ReflectionIndex 9 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_10 (j : Fin 48) :
    f4Coroot j - (f4Root 10 ⬝ᵥ f4Coroot j) • f4Coroot 10 = f4Coroot (f4ReflectionIndex 10 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_11 (j : Fin 48) :
    f4Coroot j - (f4Root 11 ⬝ᵥ f4Coroot j) • f4Coroot 11 = f4Coroot (f4ReflectionIndex 11 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_12 (j : Fin 48) :
    f4Coroot j - (f4Root 12 ⬝ᵥ f4Coroot j) • f4Coroot 12 = f4Coroot (f4ReflectionIndex 12 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_13 (j : Fin 48) :
    f4Coroot j - (f4Root 13 ⬝ᵥ f4Coroot j) • f4Coroot 13 = f4Coroot (f4ReflectionIndex 13 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_14 (j : Fin 48) :
    f4Coroot j - (f4Root 14 ⬝ᵥ f4Coroot j) • f4Coroot 14 = f4Coroot (f4ReflectionIndex 14 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_15 (j : Fin 48) :
    f4Coroot j - (f4Root 15 ⬝ᵥ f4Coroot j) • f4Coroot 15 = f4Coroot (f4ReflectionIndex 15 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_16 (j : Fin 48) :
    f4Coroot j - (f4Root 16 ⬝ᵥ f4Coroot j) • f4Coroot 16 = f4Coroot (f4ReflectionIndex 16 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_17 (j : Fin 48) :
    f4Coroot j - (f4Root 17 ⬝ᵥ f4Coroot j) • f4Coroot 17 = f4Coroot (f4ReflectionIndex 17 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_18 (j : Fin 48) :
    f4Coroot j - (f4Root 18 ⬝ᵥ f4Coroot j) • f4Coroot 18 = f4Coroot (f4ReflectionIndex 18 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_19 (j : Fin 48) :
    f4Coroot j - (f4Root 19 ⬝ᵥ f4Coroot j) • f4Coroot 19 = f4Coroot (f4ReflectionIndex 19 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_20 (j : Fin 48) :
    f4Coroot j - (f4Root 20 ⬝ᵥ f4Coroot j) • f4Coroot 20 = f4Coroot (f4ReflectionIndex 20 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_21 (j : Fin 48) :
    f4Coroot j - (f4Root 21 ⬝ᵥ f4Coroot j) • f4Coroot 21 = f4Coroot (f4ReflectionIndex 21 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_22 (j : Fin 48) :
    f4Coroot j - (f4Root 22 ⬝ᵥ f4Coroot j) • f4Coroot 22 = f4Coroot (f4ReflectionIndex 22 j) := by
  decide +revert
private lemma f4ReflectionIndex_coroot_23 (j : Fin 48) :
    f4Coroot j - (f4Root 23 ⬝ᵥ f4Coroot j) • f4Coroot 23 = f4Coroot (f4ReflectionIndex 23 j) := by
  decide +revert

private lemma f4ReflectionIndex_root_castAdd (i : Fin 24) (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot (Fin.castAdd 24 i)) • f4Root (Fin.castAdd 24 i) =
      f4Root (f4ReflectionIndex (Fin.castAdd 24 i) j) := by
  refine Fin.cases (f4ReflectionIndex_root_0 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_1 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_2 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_3 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_4 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_5 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_6 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_7 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_8 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_9 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_10 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_11 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_12 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_13 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_14 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_15 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_16 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_17 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_18 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_19 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_20 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_21 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_root_22 j) (fun i => ?_) i
  fin_cases i
  exact f4ReflectionIndex_root_23 j

private lemma f4ReflectionIndex_coroot_castAdd (i : Fin 24) (j : Fin 48) :
    f4Coroot j - (f4Root (Fin.castAdd 24 i) ⬝ᵥ f4Coroot j) •
        f4Coroot (Fin.castAdd 24 i) = f4Coroot (f4ReflectionIndex (Fin.castAdd 24 i) j) := by
  refine Fin.cases (f4ReflectionIndex_coroot_0 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_1 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_2 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_3 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_4 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_5 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_6 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_7 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_8 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_9 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_10 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_11 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_12 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_13 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_14 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_15 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_16 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_17 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_18 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_19 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_20 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_21 j) (fun i => ?_) i
  refine Fin.cases (f4ReflectionIndex_coroot_22 j) (fun i => ?_) i
  fin_cases i
  exact f4ReflectionIndex_coroot_23 j

private lemma f4Root_natAdd (i : Fin 24) :
    f4Root (Fin.addNat i 24) = -f4Root (Fin.castAdd 24 i) := by fin_cases i <;> decide

private lemma f4Coroot_natAdd (i : Fin 24) :
    f4Coroot (Fin.addNat i 24) = -f4Coroot (Fin.castAdd 24 i) := by fin_cases i <;> decide

private lemma f4ReflectionIndex_natAdd (i : Fin 24) (j : Fin 48) :
    f4ReflectionIndex (Fin.addNat i 24) j = f4ReflectionIndex (Fin.castAdd 24 i) j := by
  fin_cases i <;> rfl

private lemma f4ReflectionIndex_root (i j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot i) • f4Root i = f4Root (f4ReflectionIndex i j) := by
  by_cases hi : (i : ℕ) < 24
  · let k : Fin 24 := ⟨i, hi⟩
    have hik : i = Fin.castAdd 24 k := Fin.ext rfl
    rw [hik]
    exact f4ReflectionIndex_root_castAdd k j
  · let k : Fin 24 := ⟨(i : ℕ) - 24, by omega⟩
    have hik : i = Fin.addNat k 24 := by ext; simp [k]; omega
    rw [hik]
    simpa [f4Root_natAdd, f4Coroot_natAdd,
      f4ReflectionIndex_natAdd] using
      f4ReflectionIndex_root_castAdd k j

private lemma f4ReflectionIndex_coroot (i j : Fin 48) :
    f4Coroot j - (f4Root i ⬝ᵥ f4Coroot j) • f4Coroot i =
      f4Coroot (f4ReflectionIndex i j) := by
  by_cases hi : (i : ℕ) < 24
  · let k : Fin 24 := ⟨i, hi⟩
    have hik : i = Fin.castAdd 24 k := Fin.ext rfl
    rw [hik]
    exact f4ReflectionIndex_coroot_castAdd k j
  · let k : Fin 24 := ⟨(i : ℕ) - 24, by omega⟩
    have hik : i = Fin.addNat k 24 := by ext; simp [k]; omega
    rw [hik]
    simpa [f4Root_natAdd, f4Coroot_natAdd,
      f4ReflectionIndex_natAdd] using
      f4ReflectionIndex_coroot_castAdd k j

private lemma f4Root_coroot_two (i : Fin 48) : f4Root i ⬝ᵥ f4Coroot i = 2 := by
  fin_cases i <;> decide

private lemma f4ReflectionIndex_involutive (i : Fin 48) :
    Function.Involutive (f4ReflectionIndex i) := by
  intro j
  apply f4Root.injective
  rw [← f4ReflectionIndex_root i (f4ReflectionIndex i j), ← f4ReflectionIndex_root i j]
  have hpair :
      (f4Root j - (f4Root j ⬝ᵥ f4Coroot i) • f4Root i) ⬝ᵥ f4Coroot i =
        -(f4Root j ⬝ᵥ f4Coroot i) := by
    rw [sub_dotProduct, smul_dotProduct, f4Root_coroot_two]
    ring
  rw [hpair]
  simp

/-- Reflection in an `F4` root as a permutation of the pinned root indices. -/
private def f4ReflectionPerm (i : Fin 48) : Fin 48 ≃ Fin 48 :=
  Function.Involutive.toPerm (f4ReflectionIndex i) (f4ReflectionIndex_involutive i)

@[simp] private lemma f4ReflectionPerm_apply (i j : Fin 48) :
    f4ReflectionPerm i j = f4ReflectionIndex i j := rfl

/-- The pinned simply connected root datum of type `F4`.

Both lattices use `Fin 4 → ℤ`: fundamental weights on the root side and simple coroots on the
coroot side. Root indices `0` through `3` are the Bourbaki simple roots. -/
def f4SimplyConnectedRootDatum : RootDatum (Fin 48) (Fin 4 → ℤ) (Fin 4 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 4)).toLinearMap
  root := f4Root
  coroot := f4Coroot
  root_coroot_two := by
    intro i
    decide +revert
  reflectionPerm := f4ReflectionPerm
  reflectionPerm_root := by
    intro i j
    simpa [dotProductEquiv_apply_apply, f4ReflectionPerm_apply] using f4ReflectionIndex_root i j
  reflectionPerm_coroot := by
    intro i j
    simpa [dotProductEquiv_apply_apply, f4ReflectionPerm_apply] using f4ReflectionIndex_coroot i j

/-- The root embedding of the pinned `F4` datum is the explicit table `f4Root`. -/
@[simp] lemma f4SimplyConnectedRootDatum_root : f4SimplyConnectedRootDatum.root = f4Root := (rfl)

/-- The coroot embedding of the pinned `F4` datum is the explicit table `f4Coroot`. -/
@[simp] lemma f4SimplyConnectedRootDatum_coroot :
    f4SimplyConnectedRootDatum.coroot = f4Coroot := (rfl)

/-- The perfect pairing of the pinned `F4` datum is the standard dot product. -/
@[simp] lemma f4SimplyConnectedRootDatum_toLinearMap_apply (x y : Fin 4 → ℤ) :
    f4SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `F4` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma f4SimplyConnectedRootDatum_pairing (i j : Fin 48) :
    f4SimplyConnectedRootDatum.pairing i j = f4Root i ⬝ᵥ f4Coroot j := (rfl)

private lemma f4Root_23 : f4Root 23 = Pi.single 0 1 := by decide
private lemma f4Root_22_add_23 : f4Root 22 + f4Root 23 = Pi.single 1 1 := by decide
private lemma f4Root_19_add_20 : f4Root 19 + f4Root 20 = Pi.single 2 1 := by decide
private lemma f4Root_20 : f4Root 20 = Pi.single 3 1 := by decide
private lemma f4Coroot_0 : f4Coroot 0 = Pi.single 0 1 := by decide
private lemma f4Coroot_1 : f4Coroot 1 = Pi.single 1 1 := by decide
private lemma f4Coroot_2 : f4Coroot 2 = Pi.single 2 1 := by decide
private lemma f4Coroot_3 : f4Coroot 3 = Pi.single 3 1 := by decide

private lemma span_f4Root_eq_top : span ℤ (range f4Root) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  simp only [Pi.basisFun_apply]
  let S := span ℤ (range f4Root)
  have hr (j : Fin 48) : f4Root j ∈ S := subset_span ⟨j, rfl⟩
  fin_cases i
  · simpa only using (f4Root_23 ▸ hr 23)
  · simpa only using (f4Root_22_add_23 ▸ S.add_mem (hr 22) (hr 23))
  · simpa only using (f4Root_19_add_20 ▸ S.add_mem (hr 19) (hr 20))
  · simpa only using (f4Root_20 ▸ hr 20)

private lemma span_f4Coroot_eq_top : span ℤ (range f4Coroot) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  simp only [Pi.basisFun_apply]
  fin_cases i
  · simpa only using (f4Coroot_0 ▸ (subset_span ⟨0, rfl⟩))
  · simpa only using (f4Coroot_1 ▸ (subset_span ⟨1, rfl⟩))
  · simpa only using (f4Coroot_2 ▸ (subset_span ⟨2, rfl⟩))
  · simpa only using (f4Coroot_3 ▸ (subset_span ⟨3, rfl⟩))

/-- The pinned `F4` datum is a root system: its roots and coroots span the character and
cocharacter lattices. Coroot spanning is the simply connected lattice condition. -/
instance : f4SimplyConnectedRootDatum.IsRootSystem where
  span_root_eq_top := span_f4Root_eq_top
  span_coroot_eq_top := span_f4Coroot_eq_top

/-- The coefficients of the positive `F4` roots in the ordered simple-root basis. -/
private def f4RootCoefficients : Fin 24 → Fin 4 → ℕ := ![
  ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
  ![0, 0, 1, 1], ![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 2, 0],
  ![0, 1, 2, 1], ![0, 1, 2, 2], ![1, 1, 0, 0], ![1, 1, 1, 0],
  ![1, 1, 1, 1], ![1, 1, 2, 0], ![1, 1, 2, 1], ![1, 1, 2, 2],
  ![1, 2, 2, 0], ![1, 2, 2, 1], ![1, 2, 2, 2], ![1, 2, 3, 1],
  ![1, 2, 3, 2], ![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]]

/-- The coefficients of the positive `F4` coroots in the ordered simple-coroot basis. The
cocharacter lattice is written in that very basis, so these are the nonnegative coordinates of
`f4Coroot` itself. -/
private def f4CorootCoefficients (i : Fin 24) (k : Fin 4) : ℕ :=
  (f4Coroot (Fin.castAdd 24 i) k).toNat

private lemma f4Root_eq_sum (i : Fin 24) :
    ∑ k, f4RootCoefficients i k • f4Root (Fin.castAdd 44 k) =
      f4Root (Fin.castAdd 24 i) := by
  fin_cases i <;> decide

private lemma f4Coroot_eq_sum (i : Fin 24) :
    ∑ k, f4CorootCoefficients i k • f4Coroot (Fin.castAdd 44 k) =
      f4Coroot (Fin.castAdd 24 i) := by
  fin_cases i <;> decide

private lemma mem_or_neg_mem_of_coefficients (f : Fin 48 → (Fin 4 → ℤ))
    (c : Fin 24 → Fin 4 → ℕ)
    (hc : ∀ i, ∑ k, c i k • f (Fin.castAdd 44 k) = f (Fin.castAdd 24 i))
    (hneg : ∀ i, f (Fin.addNat i 24) = -f (Fin.castAdd 24 i)) (i : Fin 48) :
    f i ∈ AddSubmonoid.closure (f '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) ∨
      -f i ∈ AddSubmonoid.closure
        (f '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) := by
  let C := AddSubmonoid.closure (f '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48)))
  have hs (k : Fin 4) : f (Fin.castAdd 44 k) ∈ C :=
    AddSubmonoid.subset_closure ⟨Fin.castAdd 44 k, by fin_cases k <;> simp, rfl⟩
  have hsum (k : Fin 24) : f (Fin.castAdd 24 k) ∈ C := by
    rw [← hc k]
    simpa using C.sum_mem (t := Finset.univ) (fun j _ => C.nsmul_mem (hs j) _)
  by_cases hi : (i : ℕ) < 24
  · left
    let k : Fin 24 := ⟨i, hi⟩
    simpa [C, k] using hsum k
  · right
    let k : Fin 24 := ⟨(i : ℕ) - 24, by omega⟩
    have hik : i = Fin.addNat k 24 := by ext; simp [k]; omega
    rw [hik, hneg]
    simpa [C] using hsum k

private lemma f4Root_mem_or_neg_mem (i : Fin 48) :
    f4Root i ∈
        AddSubmonoid.closure (f4Root '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) ∨
      -f4Root i ∈
        AddSubmonoid.closure (f4Root '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) :=
  mem_or_neg_mem_of_coefficients f4Root f4RootCoefficients f4Root_eq_sum f4Root_natAdd i

private lemma f4Coroot_mem_or_neg_mem (i : Fin 48) :
    f4Coroot i ∈
        AddSubmonoid.closure (f4Coroot '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) ∨
      -f4Coroot i ∈ AddSubmonoid.closure
        (f4Coroot '' (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48))) :=
  mem_or_neg_mem_of_coefficients f4Coroot f4CorootCoefficients f4Coroot_eq_sum f4Coroot_natAdd i

private def f4SimpleIndex (i : Fin 4) : Fin 48 := Fin.castAdd 44 i

private lemma coe_f4Support :
    (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48)) = range f4SimpleIndex := by
  ext i
  fin_cases i <;> decide

private lemma linearIndepOn_f4Root :
    LinearIndepOn ℤ f4Root (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48)) := by
  have hinj : Function.Injective f4SimpleIndex := by
    intro i j h
    apply Fin.ext
    simpa only [f4SimpleIndex, Fin.val_castAdd] using congrArg Fin.val h
  rw [coe_f4Support, linearIndepOn_range_iff hinj]
  have hrows : LinearIndependent ℤ (CartanMatrix.F₄.row) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (A := CartanMatrix.F₄)
      (by rw [CartanMatrix.F₄_det]; norm_num)
  convert hrows using 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma linearIndepOn_f4Coroot :
    LinearIndepOn ℤ f4Coroot (↑({0, 1, 2, 3} : Finset (Fin 48)) : Set (Fin 48)) := by
  have hinj : Function.Injective f4SimpleIndex := by
    intro i j h
    apply Fin.ext
    simpa only [f4SimpleIndex, Fin.val_castAdd] using congrArg Fin.val h
  rw [coe_f4Support, linearIndepOn_range_iff hinj]
  have hid : LinearIndependent ℤ ((1 : Matrix (Fin 4) (Fin 4) ℤ).row) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (A := (1 : Matrix (Fin 4) (Fin 4) ℤ))
      (by simp)
  convert hid using 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The Bourbaki-numbered base of the pinned simply connected `F4` datum. Its support is the first
four root indices, with the two long simple roots followed by the two short simple roots. -/
def f4SimplyConnectedBase : f4SimplyConnectedRootDatum.Base where
  support := {0, 1, 2, 3}
  linearIndepOn_root := by simpa only [f4SimplyConnectedRootDatum_root] using linearIndepOn_f4Root
  linearIndepOn_coroot := by
    simpa only [f4SimplyConnectedRootDatum_coroot] using linearIndepOn_f4Coroot
  root_mem_or_neg_mem := f4Root_mem_or_neg_mem
  coroot_mem_or_neg_mem := f4Coroot_mem_or_neg_mem

@[simp] lemma f4SimplyConnectedBase_support :
    f4SimplyConnectedBase.support = {0, 1, 2, 3} := (rfl)

/-- The Cartan integers at the first four root indices are Mathlib's Bourbaki-numbered `F4`
matrix. This pins the node order independently of the existential relabelling in `HasCartanType`. -/
@[simp] theorem f4SimplyConnectedRootDatum_pairing_eq_cartanMatrix_F4 (i j : Fin 4) :
    f4Root (Fin.castAdd 44 i) ⬝ᵥ f4Coroot (Fin.castAdd 44 j) =
      CartanMatrix.F₄ i j := by
  fin_cases i <;> fin_cases j <;> decide

private def f4SimplyConnectedBaseEquiv : f4SimplyConnectedBase.support ≃ Fin 4 where
  toFun i := ⟨i, by
    have hi := i.property
    simp only [f4SimplyConnectedBase_support, Finset.mem_insert, Finset.mem_singleton] at hi
    omega⟩
  invFun i := ⟨Fin.castAdd 44 i, by fin_cases i <;> decide⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; simp
  right_inv i := by apply Fin.ext; simp

/-- The pinned simply connected `F4` datum has Cartan type `F4`. -/
theorem hasCartanType_f4SimplyConnectedRootDatum :
    HasCartanType f4SimplyConnectedRootDatum f4SimplyConnectedBase F4 := by
  rw [hasCartanType_iff]
  refine ⟨f4SimplyConnectedBaseEquiv, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [← (FaithfulSMul.algebraMap_injective ℤ ℤ).eq_iff]
    simp only [RootPairing.Base.algebraMap_cartanMatrixIn_apply,
      f4SimplyConnectedRootDatum_pairing, cartanMatrix_F4]
    decide

end DynkinType

end TauCeti
