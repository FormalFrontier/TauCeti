/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Length

/-!
# The special length-exchanging map of the pinned type `F₄` root datum

In characteristic two, the Ree construction of the families `²F₄` and the Tits group uses a special
isogeny of the simply connected group of type `F₄`. At the root-datum level its character-lattice
map reverses the four Bourbaki nodes and multiplies in the long-root direction. In the
fundamental-weight coordinates of `TauCeti.DynkinType.f4Root`, that map is

```text
A = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 2, 0, 0; 2, 0, 0, 0].
```

This file computes the action of `A` on every root and of `Aᵀ` on every coroot. The induced
permutation of the forty-eight root indices exchanges long roots with short ones, preserves
positivity, and commutes with root negation. The rescaling exponent is the squared-length table
`TauCeti.DynkinType.f4Length`: it is `1` on short roots and `2` on long roots. Applying the data
twice multiplies both lattices by `2`, and the two exponents along each orbit multiply to `2`.

These equations are the explicit `F₄` input for the root-datum special-isogeny construction, the
last of the three beside the type `B₂` case of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/SpecialMap.lean` and the same-shape
`G₂` implementation proposed in
[Tau Ceti PR #4116](https://github.com/TauCetiProject/TauCeti/pull/4116).
They do not yet construct a group-scheme morphism; Layer 9 of the reductive-groups roadmap requires
that later lift, together with its action on root subgroups, before the Suzuki--Ree lane can use it.

## Main definitions

* `TauCeti.DynkinType.f4SpecialIsogenyMatrix`: the character-lattice matrix.
* `TauCeti.DynkinType.f4SpecialIsogenyIndex`: the induced permutation of the forty-eight root
  indices, and `TauCeti.DynkinType.f4SpecialIsogenyIndexEquiv` the same permutation as an
  `Equiv.Perm`.

The rescaling exponent needs no definition of its own here. The pinned `F₄` datum is tabulated on
its own root indices, so `TauCeti.DynkinType.f4Length` already is that exponent; the rank-two type
`B` datum is indexed uniformly in the rank instead, which is why its exponent carries a name of its
own.

## Main results

* `TauCeti.DynkinType.f4SpecialIsogenyMatrix_mulVec_root` and
  `TauCeti.DynkinType.f4SpecialIsogenyMatrix_transpose_mulVec_coroot`: the equations on the pinned
  datum.
* `TauCeti.DynkinType.f4SpecialIsogenyMatrix_mul_self` and its transpose counterpart: applying the
  lattice map twice is multiplication by `2`.
* `TauCeti.DynkinType.det_f4SpecialIsogenyMatrix`: the map has determinant `4`, so it is an
  isogeny and not a lattice automorphism.
* `TauCeti.DynkinType.f4Length_mul_f4Length_specialIsogenyIndex`: the two rescaling exponents on an
  orbit multiply to the defining characteristic.
* `TauCeti.DynkinType.f4SpecialIsogenyIndex_castAdd`: on the four simple roots the index
  permutation is `TauCeti.lengthPermF4`, the pinned length-exchanging permutation of the diagram.
* `TauCeti.DynkinType.f4Length_mul_pairing_f4SpecialIsogenyIndex`: the Cartan integers transform by
  the rule a special isogeny forces.

## References

The node numbering and coordinates follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VIII. The special-isogeny equations follow R. Steinberg, *Endomorphisms of Linear Algebraic
Groups*, §11; the Ree convention is also described in R. W. Carter, *Simple Groups of Lie Type*,
§§12.3--12.4. The exponent is `1` on long root subgroups and the characteristic on short root
subgroups when the group-scheme map is read contravariantly on its root datum. Here the lattice map
consequently rescales a root by its own squared length before exchanging its index.
-/

public section

namespace TauCeti.DynkinType

open Function

open scoped _root_.Matrix

/-! ## The lattice map and the root permutation -/

/-- The character-lattice matrix of the special length-exchanging map of the pinned `F₄` root
datum, in the fundamental-weight basis. -/
def f4SpecialIsogenyMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 2, 0, 0; 2, 0, 0, 0]

/-- The permutation of the forty-eight `F₄` roots induced by
`TauCeti.DynkinType.f4SpecialIsogenyMatrix`. It exchanges long roots with short roots and commutes
with root negation. -/
def f4SpecialIsogenyIndex : Fin 48 → Fin 48 :=
  ![3, 2, 1, 0, 10, 7, 13, 5, 16, 11, 4, 9,
    15, 6, 18, 12, 8, 21, 14, 22, 23, 17, 19, 20,
    27, 26, 25, 24, 34, 31, 37, 29, 40, 35, 28, 33,
    39, 30, 42, 36, 32, 45, 38, 46, 47, 41, 43, 44]

/-- The special root permutation is an involution. -/
theorem f4SpecialIsogenyIndex_involutive : Involutive f4SpecialIsogenyIndex := by
  intro i
  decide +revert

/-- The special permutation of the root indices of the pinned type `F₄` datum. -/
def f4SpecialIsogenyIndexEquiv : Equiv.Perm (Fin 48) :=
  f4SpecialIsogenyIndex_involutive.toPerm _

/-- The bundled special permutation acts by the tabulated one. -/
@[simp] theorem f4SpecialIsogenyIndexEquiv_apply (i : Fin 48) :
    f4SpecialIsogenyIndexEquiv i = f4SpecialIsogenyIndex i := by
  rw [f4SpecialIsogenyIndexEquiv, Involutive.coe_toPerm]

/-- The special root permutation commutes with passing to the negative root. -/
@[simp] theorem f4SpecialIsogenyIndex_add_twentyFour (i : Fin 48) :
    f4SpecialIsogenyIndex (i + 24) = f4SpecialIsogenyIndex i + 24 := by
  decide +revert

/-- The special root permutation preserves positivity: it maps the twenty-four positive roots,
which are the first twenty-four indices, among themselves. -/
@[simp] theorem f4SpecialIsogenyIndex_lt_twentyFour_iff (i : Fin 48) :
    (f4SpecialIsogenyIndex i : ℕ) < 24 ↔ (i : ℕ) < 24 := by
  decide +revert

private theorem f4SpecialIsogenyIndex_castAdd_rev (i : Fin 4) :
    f4SpecialIsogenyIndex (Fin.castAdd 44 i) = Fin.castAdd 44 i.rev := by
  decide +revert

/-- **On the four simple roots the special permutation is the pinned length-exchanging permutation
of the diagram**, namely reversal of the four-node chain. -/
@[simp] theorem f4SpecialIsogenyIndex_castAdd (i : Fin 4) :
    f4SpecialIsogenyIndex (Fin.castAdd 44 i) = Fin.castAdd 44 (lengthPermF4 i) := by
  rw [f4SpecialIsogenyIndex_castAdd_rev, lengthPermF4_apply]

/-! ## Action on the pinned root datum -/

private theorem f4SpecialIsogenyMatrix_mulVec_f4Root (i : Fin 48) :
    f4SpecialIsogenyMatrix *ᵥ f4Root i = f4Length i • f4Root (f4SpecialIsogenyIndex i) := by
  rw [f4Length_def]
  decide +revert

private theorem f4SpecialIsogenyMatrix_transpose_mulVec_f4Coroot (i : Fin 48) :
    f4SpecialIsogenyMatrixᵀ *ᵥ f4Coroot (f4SpecialIsogenyIndex i) = f4Length i • f4Coroot i := by
  rw [f4Length_def]
  decide +revert

/-- **The special matrix carries every root of the pinned datum to its indexed image with the
prescribed exponent.** -/
theorem f4SpecialIsogenyMatrix_mulVec_root (i : Fin 48) :
    f4SpecialIsogenyMatrix *ᵥ f4SimplyConnectedRootDatum.root i =
      f4Length i • f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv i) := by
  rw [f4SimplyConnectedRootDatum_root, f4SpecialIsogenyIndexEquiv_apply]
  exact f4SpecialIsogenyMatrix_mulVec_f4Root i

/-- **The transposed special matrix satisfies the contragredient equation on every coroot of the
pinned datum.** -/
theorem f4SpecialIsogenyMatrix_transpose_mulVec_coroot (i : Fin 48) :
    f4SpecialIsogenyMatrixᵀ *ᵥ f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv i) =
      f4Length i • f4SimplyConnectedRootDatum.coroot i := by
  rw [f4SimplyConnectedRootDatum_coroot, f4SpecialIsogenyIndexEquiv_apply]
  exact f4SpecialIsogenyMatrix_transpose_mulVec_f4Coroot i

/-- The square of the character-lattice special matrix is twice the identity matrix. -/
theorem f4SpecialIsogenyMatrix_mul_self :
    f4SpecialIsogenyMatrix * f4SpecialIsogenyMatrix =
      (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [f4SpecialIsogenyMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The square of the cocharacter-lattice special matrix is twice the identity matrix. -/
theorem f4SpecialIsogenyMatrix_transpose_mul_self :
    f4SpecialIsogenyMatrixᵀ * f4SpecialIsogenyMatrixᵀ =
      (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  rw [← Matrix.transpose_mul, f4SpecialIsogenyMatrix_mul_self, Matrix.transpose_smul,
    Matrix.transpose_one]

/-- Applying the character-lattice special map twice is multiplication by the characteristic
`2`. -/
theorem f4SpecialIsogenyMatrix_mulVec_self (x : Fin 4 → ℤ) :
    f4SpecialIsogenyMatrix *ᵥ (f4SpecialIsogenyMatrix *ᵥ x) = (2 : ℤ) • x := by
  rw [Matrix.mulVec_mulVec, f4SpecialIsogenyMatrix_mul_self, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Applying the cocharacter-lattice special map twice is multiplication by the characteristic
`2`. -/
theorem f4SpecialIsogenyMatrix_transpose_mulVec_self (x : Fin 4 → ℤ) :
    f4SpecialIsogenyMatrixᵀ *ᵥ (f4SpecialIsogenyMatrixᵀ *ᵥ x) = (2 : ℤ) • x := by
  rw [Matrix.mulVec_mulVec, f4SpecialIsogenyMatrix_transpose_mul_self, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- The square relation for the character-lattice map, as an equality of linear maps. -/
theorem f4SpecialIsogenyMatrix_mulVecLin_comp_self :
    f4SpecialIsogenyMatrix.mulVecLin ∘ₗ f4SpecialIsogenyMatrix.mulVecLin =
      (2 : ℤ) • (LinearMap.id : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)) := by
  rw [← Matrix.mulVecLin_mul, f4SpecialIsogenyMatrix_mul_self]
  ext x
  simp

/-- The square relation for the cocharacter-lattice map, as an equality of linear maps. -/
theorem f4SpecialIsogenyMatrix_transpose_mulVecLin_comp_self :
    f4SpecialIsogenyMatrixᵀ.mulVecLin ∘ₗ f4SpecialIsogenyMatrixᵀ.mulVecLin =
      (2 : ℤ) • (LinearMap.id : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)) := by
  rw [← Matrix.mulVecLin_mul, f4SpecialIsogenyMatrix_transpose_mul_self]
  ext x
  simp

/-- **The special map is an isogeny and not an automorphism of the character lattice**: its
determinant is `4`, the square of the characteristic, matching the two long simple directions in
which it multiplies. -/
@[simp] theorem det_f4SpecialIsogenyMatrix : f4SpecialIsogenyMatrix.det = 4 := by
  unfold f4SpecialIsogenyMatrix
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-! ## Length and exponent conventions -/

/-- The exponents at a root index and its image multiply to the characteristic `2`. -/
@[simp] theorem f4Length_mul_f4Length_specialIsogenyIndex (i : Fin 48) :
    f4Length i * f4Length (f4SpecialIsogenyIndex i) = 2 := by
  rw [f4Length_def]
  decide +revert

/-- **The special permutation exchanges long roots with short ones.** -/
@[simp] theorem f4Length_specialIsogenyIndex_eq_one_iff (i : Fin 48) :
    f4Length (f4SpecialIsogenyIndex i) = 1 ↔ f4Length i = 2 := by
  rw [f4Length_def]
  decide +revert

/-- **The special permutation sends a short root to a long root.** -/
@[simp] theorem f4Length_specialIsogenyIndex_eq_two_iff (i : Fin 48) :
    f4Length (f4SpecialIsogenyIndex i) = 2 ↔ f4Length i = 1 := by
  have h := (f4Length_specialIsogenyIndex_eq_one_iff (f4SpecialIsogenyIndex i)).symm
  rw [f4SpecialIsogenyIndex_involutive i] at h
  exact h

/-- **The Cartan integers transform by the rule a special isogeny forces.** Writing `α'` for the
image of a root `α` under the special permutation, pairing the root equation against the coroot
equation gives `ℓ(α) ⟨α', β'∨⟩ = ℓ(β) ⟨α, β∨⟩`. No diagram automorphism satisfies this, since the
two lengths differ. -/
theorem f4Length_mul_pairing_f4SpecialIsogenyIndex (i j : Fin 48) :
    f4Length i *
        f4SimplyConnectedRootDatum.pairing
          (f4SpecialIsogenyIndexEquiv i) (f4SpecialIsogenyIndexEquiv j) =
      f4Length j * f4SimplyConnectedRootDatum.pairing i j := by
  calc
    _ = (f4Length i • f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndexEquiv i)) ⬝ᵥ
          f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv j) := by
      rw [f4SimplyConnectedRootDatum_pairing, f4SimplyConnectedRootDatum_root,
        f4SimplyConnectedRootDatum_coroot, smul_dotProduct, smul_eq_mul]
    _ = (f4SpecialIsogenyMatrix *ᵥ f4SimplyConnectedRootDatum.root i) ⬝ᵥ
          f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv j) := by
      rw [f4SpecialIsogenyMatrix_mulVec_root]
    _ = f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv j) ⬝ᵥ
          (f4SpecialIsogenyMatrix *ᵥ f4SimplyConnectedRootDatum.root i) := dotProduct_comm _ _
    _ = f4SimplyConnectedRootDatum.root i ⬝ᵥ
          (f4SpecialIsogenyMatrixᵀ *ᵥ
            f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv j)) :=
      (Matrix.dotProduct_transpose_mulVec f4SpecialIsogenyMatrix
        (f4SimplyConnectedRootDatum.root i)
        (f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndexEquiv j))).symm
    _ = f4SimplyConnectedRootDatum.root i ⬝ᵥ
          (f4Length j • f4SimplyConnectedRootDatum.coroot j) := by
      rw [f4SpecialIsogenyMatrix_transpose_mulVec_coroot]
    _ = _ := by
      rw [dotProduct_smul, smul_eq_mul, f4SimplyConnectedRootDatum_pairing,
        f4SimplyConnectedRootDatum_root, f4SimplyConnectedRootDatum_coroot]

end TauCeti.DynkinType
