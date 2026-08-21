/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic

public section

/-!
# The simply connected root datum of type F4

This file constructs the pinned integral root datum of type `F4` on the character and cocharacter
lattices `Fin 4 → ℤ`. The character lattice is written in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Thus the first four roots are the rows of the
Bourbaki-numbered Cartan matrix, while their coroots are the standard basis vectors.

The forty-eight roots are ordered with the four Bourbaki simple roots at indices `0` through `3`,
then at indices `4` through `23` the remaining twenty positive roots in increasing lexicographic
order of their tuple of simple-root coefficients — the order in which `f4RootCoefficients` lists
those tuples — and finally at index `i + 24` the negative of the root at index `i`. The coordinate
tables make both the carrier and every reflection explicit. The first two simple roots are long and
the last two are short.

## Main definitions and results

* `TauCeti.DynkinType.f4SimplyConnectedRootDatum` is the pinned forty-eight-root datum.
* `TauCeti.DynkinType.f4ReflectionIndex` is its explicit action on root indices.
* The `RootPairing.IsRootSystem` instance for `TauCeti.DynkinType.f4SimplyConnectedRootDatum` says
  that its roots span the character lattice and its coroots span the cocharacter lattice. The
  latter, `span_coroot_eq_top`, is the simply connected condition the file is named for: the datum
  has cocharacter lattice equal to the coroot lattice, so no central isogeny quotient of the simply
  connected form is taken.
* `TauCeti.DynkinType.f4SimplyConnectedBase` is its Bourbaki-numbered base.
* `TauCeti.DynkinType.f4SimplyConnectedRootDatum_pairing_eq_cartanMatrix_F₄` pins the numbering.
* `TauCeti.DynkinType.hasCartanType_f4SimplyConnectedRootDatum` identifies its Cartan type.

## References

The node numbering and the Cartan matrix follow Bourbaki, *Lie Groups and Lie Algebras,
Chapters 4--6*, Plate VIII. The coordinate tables here are not in Bourbaki's orthonormal model, in
which the long roots are `±eᵢ ± eⱼ` and the short roots are `±eᵢ` and `(±e₁ ± e₂ ± e₃ ± e₄) / 2`:
they are written in the fundamental-weight basis for the roots and the simple-coroot basis for the
coroots. This is the `F4` branch of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open _root_.Matrix Module Set Submodule

namespace DynkinType

/-- The roots of `F4` in the fundamental-weight basis, with the simple roots first and the
negative roots in the second half. -/
@[expose] def f4Root : Fin 48 ↪ (Fin 4 → ℤ) where
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
@[expose] def f4Coroot : Fin 48 ↪ (Fin 4 → ℤ) where
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

/-- The simple roots of `F4` sit at the first four indices, where they are the rows of Mathlib's
Bourbaki-numbered Cartan matrix. -/
@[simp] lemma f4Root_castAdd (i : Fin 4) : f4Root (Fin.castAdd 44 i) = CartanMatrix.F₄ i := by
  fin_cases i <;> decide

/-- The simple coroots of `F4` sit at the first four indices, where they are the standard basis of
the cocharacter lattice. -/
@[simp] lemma f4Coroot_castAdd (i : Fin 4) : f4Coroot (Fin.castAdd 44 i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- The root at index `i + 24` is the negative of the root at index `i`. -/
@[simp] lemma f4Root_addNat (i : Fin 24) :
    f4Root (Fin.addNat i 24) = -f4Root (Fin.castAdd 24 i) := by fin_cases i <;> decide

/-- The coroot at index `i + 24` is the negative of the coroot at index `i`. -/
@[simp] lemma f4Coroot_addNat (i : Fin 24) :
    f4Coroot (Fin.addNat i 24) = -f4Coroot (Fin.castAdd 24 i) := by fin_cases i <;> decide

/-- The first-half index underlying a root, identifying a negative root with its positive
opposite. -/
@[expose] def f4PositiveIndex (i : Fin 48) : Fin 24 := ⟨i % 24, Nat.mod_lt _ (by omega)⟩

/-- The first twenty-four indices are their own first-half index. -/
@[simp] lemma f4PositiveIndex_castAdd (i : Fin 24) : f4PositiveIndex (Fin.castAdd 24 i) = i :=
  Fin.ext (by simp only [f4PositiveIndex, Fin.val_castAdd, Nat.mod_eq_of_lt i.isLt])

/-- Adding twenty-four to a first-half index leaves the first-half index unchanged. -/
@[simp] lemma f4PositiveIndex_addNat (i : Fin 24) : f4PositiveIndex (Fin.addNat i 24) = i :=
  Fin.ext (by
    simp only [f4PositiveIndex, Fin.val_addNat, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt])

/-- The permutation table for reflection in each of the twenty-four positive `F4` roots. Reflection
in the corresponding negative root is the same permutation. -/
@[expose] def f4ReflectionTable : Fin 24 → Fin 48 → Fin 48 := ![
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

/-- The explicit action of the reflection in the root of index `i` on root indices: it sends the
index `j` to `f4ReflectionIndex i j`. -/
@[expose] def f4ReflectionIndex (i j : Fin 48) : Fin 48 := f4ReflectionTable (f4PositiveIndex i) j

/-- Reflection in one of the first twenty-four roots permutes root indices by the corresponding row
of `f4ReflectionTable`. -/
@[simp]
lemma f4ReflectionIndex_castAdd (i : Fin 24) (j : Fin 48) :
    f4ReflectionIndex (Fin.castAdd 24 i) j = f4ReflectionTable i j := by
  simp only [f4ReflectionIndex, f4PositiveIndex_castAdd]

private lemma f4ReflectionIndex_root_castAdd (i : Fin 24) (j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot (Fin.castAdd 24 i)) • f4Root (Fin.castAdd 24 i) =
      f4Root (f4ReflectionIndex (Fin.castAdd 24 i) j) := by
  decide +revert

private lemma f4ReflectionIndex_coroot_castAdd (i : Fin 24) (j : Fin 48) :
    f4Coroot j - (f4Root (Fin.castAdd 24 i) ⬝ᵥ f4Coroot j) • f4Coroot (Fin.castAdd 24 i) =
      f4Coroot (f4ReflectionIndex (Fin.castAdd 24 i) j) := by
  decide +revert

/-- Reflection in a negative root is the same permutation of root indices as reflection in its
positive opposite. -/
@[simp]
lemma f4ReflectionIndex_addNat (i : Fin 24) (j : Fin 48) :
    f4ReflectionIndex (Fin.addNat i 24) j = f4ReflectionIndex (Fin.castAdd 24 i) j := by
  simp only [f4ReflectionIndex, f4PositiveIndex_addNat, f4PositiveIndex_castAdd]

/-- Extend a reflection identity from the first twenty-four indices to all forty-eight, given that
passing to the negative index negates the vector and the reflection coefficient and leaves the
permutation of indices unchanged. -/
private lemma reflection_eq_of_castAdd {M : Type*} [AddCommGroup M] {f : Fin 48 → M}
    {c : Fin 48 → Fin 48 → ℤ} {σ : Fin 48 → Fin 48 → Fin 48}
    (hf : ∀ k : Fin 24, f (Fin.addNat k 24) = -f (Fin.castAdd 24 k))
    (hc : ∀ (k : Fin 24) (j : Fin 48), c (Fin.addNat k 24) j = -c (Fin.castAdd 24 k) j)
    (hσ : ∀ (k : Fin 24) (j : Fin 48), σ (Fin.addNat k 24) j = σ (Fin.castAdd 24 k) j)
    (h : ∀ (k : Fin 24) (j : Fin 48),
      f j - c (Fin.castAdd 24 k) j • f (Fin.castAdd 24 k) = f (σ (Fin.castAdd 24 k) j))
    (i j : Fin 48) : f j - c i j • f i = f (σ i j) := by
  induction i using Fin.addCases (m := 24) (n := 24) with
  | left k => exact h k j
  | right k =>
    rw [Fin.natAdd_eq_addNat, hf, hc, hσ, neg_smul, smul_neg, neg_neg]
    exact h k j

private lemma f4ReflectionIndex_root (i j : Fin 48) :
    f4Root j - (f4Root j ⬝ᵥ f4Coroot i) • f4Root i = f4Root (f4ReflectionIndex i j) :=
  reflection_eq_of_castAdd (f := ⇑f4Root) (c := fun i j => f4Root j ⬝ᵥ f4Coroot i)
    (σ := f4ReflectionIndex) f4Root_addNat
    (fun k j => by rw [f4Coroot_addNat, dotProduct_neg]) f4ReflectionIndex_addNat
    f4ReflectionIndex_root_castAdd i j

private lemma f4ReflectionIndex_coroot (i j : Fin 48) :
    f4Coroot j - (f4Root i ⬝ᵥ f4Coroot j) • f4Coroot i = f4Coroot (f4ReflectionIndex i j) :=
  reflection_eq_of_castAdd (f := ⇑f4Coroot) (c := fun i j => f4Root i ⬝ᵥ f4Coroot j)
    (σ := f4ReflectionIndex) f4Coroot_addNat
    (fun k j => by rw [f4Root_addNat, neg_dotProduct]) f4ReflectionIndex_addNat
    f4ReflectionIndex_coroot_castAdd i j

private lemma f4Root_coroot_two_castAdd (i : Fin 24) :
    f4Root (Fin.castAdd 24 i) ⬝ᵥ f4Coroot (Fin.castAdd 24 i) = 2 := by
  decide +revert

private lemma f4Root_coroot_two (i : Fin 48) : f4Root i ⬝ᵥ f4Coroot i = 2 := by
  induction i using Fin.addCases (m := 24) (n := 24) with
  | left k => exact f4Root_coroot_two_castAdd k
  | right k =>
    rw [Fin.natAdd_eq_addNat, f4Root_addNat, f4Coroot_addNat, neg_dotProduct_neg]
    exact f4Root_coroot_two_castAdd k

/-- The pinned simply connected root datum of type `F4`.

Both lattices use `Fin 4 → ℤ`: fundamental weights on the root side and simple coroots on the
coroot side. Root indices `0` through `3` are the Bourbaki simple roots. -/
noncomputable def f4SimplyConnectedRootDatum :
    RootDatum (Fin 48) (Fin 4 → ℤ) (Fin 4 → ℤ) :=
  RootPairing.mk' (dotProductEquiv ℤ (Fin 4)).toLinearMap f4Root f4Coroot
    f4Root_coroot_two
    (by
      rintro i x ⟨j, rfl⟩
      refine ⟨f4ReflectionIndex i j, ?_⟩
      simpa [preReflection_apply, dotProductEquiv_apply_apply] using
        (f4ReflectionIndex_root i j).symm)
    (by
      rintro i x ⟨j, rfl⟩
      refine ⟨f4ReflectionIndex i j, ?_⟩
      simpa [preReflection_apply, dotProductEquiv_apply_apply] using
        (f4ReflectionIndex_coroot i j).symm)

/-- The root embedding of the pinned `F4` datum is the explicit table `f4Root`. -/
@[simp] lemma f4SimplyConnectedRootDatum_root : f4SimplyConnectedRootDatum.root = f4Root := (rfl)

/-- The coroot embedding of the pinned `F4` datum is the explicit table `f4Coroot`. -/
@[simp] lemma f4SimplyConnectedRootDatum_coroot :
    f4SimplyConnectedRootDatum.coroot = f4Coroot := (rfl)

/-- The perfect pairing of the pinned `F4` datum is the standard dot product. -/
@[simp] lemma f4SimplyConnectedRootDatum_toLinearMap_apply_apply (x y : Fin 4 → ℤ) :
    f4SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y :=
  dotProductEquiv_apply_apply ℤ (Fin 4) x y

/-- Pairing a pinned `F4` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma f4SimplyConnectedRootDatum_pairing (i j : Fin 48) :
    f4SimplyConnectedRootDatum.pairing i j = f4Root i ⬝ᵥ f4Coroot j := by
  rw [← RootPairing.root_coroot_eq_pairing]
  simp

/-- Every Cartan integer between roots of the pinned type `F₄` datum has absolute value at most
two. -/
theorem abs_pairing_f4SimplyConnectedRootDatum_le_two (i j : Fin 48) :
    |f4SimplyConnectedRootDatum.pairing i j| ≤ 2 := by
  simp only [f4SimplyConnectedRootDatum_pairing]
  decide +revert

/-- Reflection in the root of index `i` permutes the root indices of the pinned `F4` datum by the
explicit table `f4ReflectionIndex i`. -/
@[simp] lemma f4SimplyConnectedRootDatum_reflectionPerm (i j : Fin 48) :
    f4SimplyConnectedRootDatum.reflectionPerm i j = f4ReflectionIndex i j := by
  refine f4Root.injective ?_
  have h := f4SimplyConnectedRootDatum.reflectionPerm_root i j
  simp only [f4SimplyConnectedRootDatum_root, f4SimplyConnectedRootDatum_coroot,
    f4SimplyConnectedRootDatum_toLinearMap_apply_apply] at h
  rw [← h]
  exact f4ReflectionIndex_root i j

private lemma f4Root_23 : f4Root 23 = Pi.single 0 1 := by decide
private lemma f4Root_22_add_23 : f4Root 22 + f4Root 23 = Pi.single 1 1 := by decide
private lemma f4Root_19_add_20 : f4Root 19 + f4Root 20 = Pi.single 2 1 := by decide
private lemma f4Root_20 : f4Root 20 = Pi.single 3 1 := by decide

private lemma span_eq_top_of_pi_single {f : Fin 48 → (Fin 4 → ℤ)}
    (h : ∀ k : Fin 4, Pi.single k 1 ∈ span ℤ (range f)) : span ℤ (range f) = ⊤ := by
  refine top_unique ?_
  rw [← (Pi.basisFun ℤ (Fin 4)).span_eq]
  refine span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  simpa only [Pi.basisFun_apply, SetLike.mem_coe] using h i

private lemma span_f4Root_eq_top : span ℤ (range f4Root) = ⊤ := by
  refine span_eq_top_of_pi_single fun k => ?_
  have hr (j : Fin 48) : f4Root j ∈ span ℤ (range ⇑f4Root) := subset_span ⟨j, rfl⟩
  fin_cases k
  · exact f4Root_23 ▸ hr 23
  · exact f4Root_22_add_23 ▸ (span ℤ (range ⇑f4Root)).add_mem (hr 22) (hr 23)
  · exact f4Root_19_add_20 ▸ (span ℤ (range ⇑f4Root)).add_mem (hr 19) (hr 20)
  · exact f4Root_20 ▸ hr 20

private lemma span_f4Coroot_eq_top : span ℤ (range f4Coroot) = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single (P := f4SimplyConnectedRootDatum) (e := Fin.castAdd 44)
    f4Coroot_castAdd

/-- The pinned `F4` datum is a root system: its roots and coroots span the character and
cocharacter lattices. Coroot spanning is the simply connected lattice condition. -/
instance : f4SimplyConnectedRootDatum.IsRootSystem where
  span_root_eq_top := span_f4Root_eq_top
  span_coroot_eq_top := span_f4Coroot_eq_top

/-- The support of the Bourbaki-numbered base of the pinned `F4` datum: the first four root
indices, which carry the simple roots. -/
def f4Support : Finset (Fin 48) := simpleSupport (Fin.castAdd_injective 4 44)

/-- The support of the base consists exactly of the four indices below `4`. -/
@[simp] lemma mem_f4Support {i : Fin 48} : i ∈ f4Support ↔ (i : ℕ) < 4 :=
  mem_simpleSupport_iff_lt (Fin.castAdd_injective 4 44) (fun _ ↦ Fin.val_castAdd 44 _)

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
    f4Root (Fin.castAdd 24 i) =
      ∑ k, f4RootCoefficients i k • f4Root (Fin.castAdd 44 k) := by
  fin_cases i <;> decide

private lemma f4Coroot_castAdd_nonneg (i : Fin 24) (k : Fin 4) :
    0 ≤ f4Coroot (Fin.castAdd 24 i) k := by decide +revert

private lemma f4Coroot_eq_sum (i : Fin 24) :
    f4Coroot (Fin.castAdd 24 i) =
      ∑ k, f4CorootCoefficients i k • f4Coroot (Fin.castAdd 44 k) := by
  have hk (k : Fin 4) : f4CorootCoefficients i k • f4Coroot (Fin.castAdd 44 k) =
      Pi.single k (f4Coroot (Fin.castAdd 24 i) k) := by
    rw [f4Coroot_castAdd, ← Pi.single_smul', nsmul_eq_mul, mul_one]
    simp only [f4CorootCoefficients, Int.toNat_of_nonneg (f4Coroot_castAdd_nonneg i k)]
  funext k
  rw [Finset.sum_apply]
  simp only [hk]
  exact (Fintype.sum_pi_single k _).symm

private def f4SignedCoefficients (c : Fin 24 → Fin 4 → ℕ) (i : Fin 48) : Fin 4 → ℤ :=
  Fin.addCases (fun i k => c i k) (fun i k => -(c i k : ℤ)) i

private lemma f4SignedCoefficients_nonneg_or_nonpos (c : Fin 24 → Fin 4 → ℕ) (i : Fin 48) :
    (∀ k, 0 ≤ f4SignedCoefficients c i k) ∨
      (∀ k, f4SignedCoefficients c i k ≤ 0) := by
  induction i using Fin.addCases (m := 24) (n := 24) with
  | left i =>
    refine Or.inl fun k => ?_
    simp only [f4SignedCoefficients, Fin.addCases_left]
    exact Int.natCast_nonneg _
  | right i =>
    refine Or.inr fun k => ?_
    simp only [f4SignedCoefficients, Fin.addCases_right]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)

private lemma f4Root_eq_signed_sum (i : Fin 48) :
    f4Root i = ∑ k, f4SignedCoefficients f4RootCoefficients i k •
      f4Root (Fin.castAdd 44 k) := by
  induction i using Fin.addCases (m := 24) (n := 24) with
  | left i => simpa [f4SignedCoefficients, ← natCast_zsmul] using f4Root_eq_sum i
  | right i =>
    simp only [f4SignedCoefficients, Fin.addCases_right]
    rw [Fin.natAdd_eq_addNat, f4Root_addNat, f4Root_eq_sum]
    simp

private lemma f4Coroot_eq_signed_sum (i : Fin 48) :
    f4Coroot i = ∑ k, f4SignedCoefficients f4CorootCoefficients i k •
      f4Coroot (Fin.castAdd 44 k) := by
  induction i using Fin.addCases (m := 24) (n := 24) with
  | left i => simpa [f4SignedCoefficients, ← natCast_zsmul] using f4Coroot_eq_sum i
  | right i =>
    simp only [f4SignedCoefficients, Fin.addCases_right]
    rw [Fin.natAdd_eq_addNat, f4Coroot_addNat, f4Coroot_eq_sum]
    simp

private lemma f4Root_mem_or_neg_mem (i : Fin 48) :
    f4Root i ∈
        AddSubmonoid.closure (f4Root '' (↑f4Support : Set (Fin 48))) ∨
      -f4Root i ∈
        AddSubmonoid.closure (f4Root '' (↑f4Support : Set (Fin 48))) := by
  rw [f4Support, image_simpleSupport, f4Root_eq_signed_sum i]
  exact sum_smul_mem_or_neg_mem_closure _ _
    (f4SignedCoefficients_nonneg_or_nonpos f4RootCoefficients i)

private lemma f4Coroot_mem_or_neg_mem (i : Fin 48) :
    f4Coroot i ∈
        AddSubmonoid.closure (f4Coroot '' (↑f4Support : Set (Fin 48))) ∨
      -f4Coroot i ∈ AddSubmonoid.closure
        (f4Coroot '' (↑f4Support : Set (Fin 48))) := by
  rw [f4Support, image_simpleSupport, f4Coroot_eq_signed_sum i]
  exact sum_smul_mem_or_neg_mem_closure _ _
    (f4SignedCoefficients_nonneg_or_nonpos f4CorootCoefficients i)

private lemma linearIndepOn_f4Root :
    LinearIndepOn ℤ f4Root (↑f4Support : Set (Fin 48)) :=
  linearIndepOn_simpleSupport _ _ <| by
    have hcomp : ⇑f4Root ∘ (Fin.castAdd 44 : Fin 4 → Fin 48) = fun i => CartanMatrix.F₄ i :=
      funext f4Root_castAdd
    rw [hcomp]
    exact Matrix.linearIndependent_rows_of_det_ne_zero (A := CartanMatrix.F₄)
      (by rw [CartanMatrix.F₄_det]; norm_num)

private lemma linearIndepOn_f4Coroot :
    LinearIndepOn ℤ f4Coroot (↑f4Support : Set (Fin 48)) :=
  linearIndepOn_simpleSupport _ _ <| by
    have hcomp : ⇑f4Coroot ∘ (Fin.castAdd 44 : Fin 4 → Fin 48) =
        fun i : Fin 4 => Pi.single i (1 : ℤ) := funext f4Coroot_castAdd
    rw [hcomp]
    exact Pi.linearIndependent_single_one (Fin 4) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected `F4` datum. Its support is the first
four root indices, with the two long simple roots followed by the two short simple roots. -/
def f4SimplyConnectedBase : f4SimplyConnectedRootDatum.Base where
  support := f4Support
  linearIndepOn_root := by simpa only [f4SimplyConnectedRootDatum_root] using linearIndepOn_f4Root
  linearIndepOn_coroot := by
    simpa only [f4SimplyConnectedRootDatum_coroot] using linearIndepOn_f4Coroot
  root_mem_or_neg_mem := f4Root_mem_or_neg_mem
  coroot_mem_or_neg_mem := f4Coroot_mem_or_neg_mem

@[simp] lemma f4SimplyConnectedBase_support :
    f4SimplyConnectedBase.support = f4Support := (rfl)

/-- The Cartan integers of the pinned datum at the first four root indices are Mathlib's
Bourbaki-numbered `F4` matrix. This pins the node order independently of the existential
relabelling in `HasCartanType`. -/
theorem f4SimplyConnectedRootDatum_pairing_eq_cartanMatrix_F₄ (i j : Fin 4) :
    f4SimplyConnectedRootDatum.pairing (Fin.castAdd 44 i) (Fin.castAdd 44 j) =
      CartanMatrix.F₄ i j := by
  rw [f4SimplyConnectedRootDatum_pairing, f4Root_castAdd, f4Coroot_castAdd, dotProduct_single_one]

/-- The pinned simply connected `F4` datum has Cartan type `F4`. Its Bourbaki-numbered base
realizes the standard Cartan matrix `CartanMatrix.F₄`, with the node numbering of
`TauCeti.DynkinType`. -/
theorem hasCartanType_f4SimplyConnectedRootDatum :
    HasCartanType f4SimplyConnectedRootDatum f4SimplyConnectedBase F4 :=
  hasCartanType_of_pairing_eq (Fin.castAdd_injective 4 44) rfl fun i j =>
    (f4SimplyConnectedRootDatum_pairing_eq_cartanMatrix_F₄ i j).trans (by simp)

end DynkinType

end TauCeti
