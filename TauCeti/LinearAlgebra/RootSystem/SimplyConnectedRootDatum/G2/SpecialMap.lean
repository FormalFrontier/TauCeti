/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialMap
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Length

/-!
# The special length-exchanging map of the pinned type `G₂` root datum

In characteristic three, the Ree construction uses a special isogeny of the simply connected group
of type `G₂`. At the root-datum level its character-lattice map exchanges the two Bourbaki nodes
and multiplies in the long-root direction. In the fundamental-weight coordinates of
`TauCeti.DynkinType.g2Root`, that map is

```text
A = !![0, 3; 1, 0].
```

This file computes the action of `A` on every root and of `Aᵀ` on every coroot. The induced root
permutation exchanges the two simple roots, exchanges the two remaining pairs of positive roots,
and commutes with root negation. The rescaling exponent is the existing squared-length table
`TauCeti.DynkinType.g2Length`: it is `1` on short roots and `3` on long roots. Applying the data
twice multiplies both lattices by `3`, and the two exponents along each orbit multiply to `3`.

These equations are the explicit `G₂` input for the root-datum special-isogeny construction, the
odd characteristic beside the type `B₂` case of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/SpecialMap.lean`. They do not yet
construct a group-scheme morphism; Layer 9 of the reductive-groups roadmap requires that later
lift, together with its action on root subgroups, before the Suzuki--Ree lane can use it.

## Main definitions

* `TauCeti.DynkinType.g2SpecialIsogenyMatrix`: the character-lattice matrix.
* `TauCeti.DynkinType.g2SpecialIsogenyIndex`: the induced permutation of the twelve root indices,
  and `TauCeti.DynkinType.g2SpecialIsogenyIndexEquiv` the same permutation as an `Equiv.Perm`.

The rescaling exponent needs no definition of its own here. The pinned `G₂` datum is tabulated on
its own root indices, so `TauCeti.DynkinType.g2Length` already is that exponent; the rank-two type
`B` datum is indexed uniformly in the rank instead, which is why its exponent carries a name of its
own.

## Main results

* `TauCeti.DynkinType.g2SpecialIsogenyMatrix_mulVec_root` and
  `TauCeti.DynkinType.g2SpecialIsogenyMatrix_transpose_mulVec_coroot`: the equations on the pinned
  datum.
* `TauCeti.DynkinType.g2SpecialIsogenyMatrix_mul_self`: the square of the lattice map is
  multiplication by `3`.
* `TauCeti.DynkinType.det_g2SpecialIsogenyMatrix`: the map has determinant `-3`, so it is an
  isogeny and not a lattice automorphism.
* `TauCeti.DynkinType.g2Length_mul_g2Length_g2SpecialIsogenyIndex`: the two rescaling exponents on
  an orbit multiply to the defining characteristic.
* `TauCeti.DynkinType.g2SpecialIsogenyIndex_castLE`: on the two simple roots the index permutation
  is `TauCeti.lengthPermRankTwo`, the pinned length-exchanging permutation of the diagram.
* `TauCeti.DynkinType.g2Length_mul_pairing_g2SpecialIsogenyIndexEquiv`: the Cartan integers
  transform by the rule a special isogeny forces.

## References

The node numbering and coordinates follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. The special-isogeny equations follow R. Steinberg, *Endomorphisms of Linear Algebraic
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

/-- The character-lattice matrix of the special length-exchanging map of the pinned `G₂` root
datum, in the fundamental-weight basis. -/
def g2SpecialIsogenyMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 3; 1, 0]

/-- The explicit entries of the character-lattice special-isogeny matrix. -/
theorem g2SpecialIsogenyMatrix_def : g2SpecialIsogenyMatrix = !![0, 3; 1, 0] := (rfl)

/-- The permutation of the twelve `G₂` roots induced by
`TauCeti.DynkinType.g2SpecialIsogenyMatrix`. It exchanges long roots with short roots and commutes
with root negation. -/
def g2SpecialIsogenyIndex : Fin 12 → Fin 12 :=
  ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9]

/-- The explicit values of the special permutation on the root indices. -/
theorem g2SpecialIsogenyIndex_def :
    g2SpecialIsogenyIndex = ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9] := (rfl)

/-- The special root permutation is an involution. -/
theorem g2SpecialIsogenyIndex_involutive : Involutive g2SpecialIsogenyIndex := by
  intro i
  fin_cases i <;> decide

/-- Applying the special root permutation twice fixes every root index. -/
@[simp] theorem g2SpecialIsogenyIndex_g2SpecialIsogenyIndex (i : Fin 12) :
    g2SpecialIsogenyIndex (g2SpecialIsogenyIndex i) = i :=
  g2SpecialIsogenyIndex_involutive i

/-- The special permutation of the root indices of the pinned type `G₂` datum. -/
def g2SpecialIsogenyIndexEquiv : Equiv.Perm (Fin 12) :=
  g2SpecialIsogenyIndex_involutive.toPerm _

@[simp] theorem g2SpecialIsogenyIndexEquiv_apply (i : Fin 12) :
    g2SpecialIsogenyIndexEquiv i = g2SpecialIsogenyIndex i := by
  rw [g2SpecialIsogenyIndexEquiv, Involutive.coe_toPerm]

/-- The special root permutation commutes with passing to the negative root. -/
@[simp] theorem g2SpecialIsogenyIndex_add_six (i : Fin 12) :
    g2SpecialIsogenyIndex (i + 6) = g2SpecialIsogenyIndex i + 6 := by
  decide +revert

/-- The special root permutation preserves positivity: it maps the six positive roots, which are
the first six indices, among themselves. -/
@[simp] theorem g2SpecialIsogenyIndex_lt_six_iff (i : Fin 12) :
    (g2SpecialIsogenyIndex i : ℕ) < 6 ↔ (i : ℕ) < 6 := by
  decide +revert

/-- **On the two simple roots the special permutation is the pinned length-exchanging permutation
of the diagram.** -/
@[simp] theorem g2SpecialIsogenyIndex_castLE (i : Fin 2) :
    g2SpecialIsogenyIndex (Fin.castLE (by omega) i) =
      Fin.castLE (by omega) (lengthPermRankTwo i) := by
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.castLE_zero, Fin.reduceCastLE,
      lengthPermRankTwo_apply_zero, lengthPermRankTwo_apply_one] <;>
    decide

/-! ## Action on the pinned root datum -/

-- These two equations cannot be simp lemmas: the whole-library simp set contains
-- `Matrix.mulVec_fin_two`, so the `simpNF` linter reduces their left-hand sides first.

/-- **The special matrix carries every tabulated root to its indexed image with the
prescribed exponent.** -/
theorem g2SpecialIsogenyMatrix_mulVec_g2Root (i : Fin 12) :
    g2SpecialIsogenyMatrix *ᵥ g2Root i = g2Length i • g2Root (g2SpecialIsogenyIndex i) := by
  rw [g2Root_apply, g2Root_apply, g2Length_apply]
  decide +revert

/-- **The transposed special matrix satisfies the contragredient equation on every tabulated
coroot.** -/
theorem g2SpecialIsogenyMatrix_transpose_mulVec_g2Coroot (i : Fin 12) :
    g2SpecialIsogenyMatrixᵀ *ᵥ g2Coroot (g2SpecialIsogenyIndex i) = g2Length i • g2Coroot i := by
  rw [g2Coroot_apply, g2Coroot_apply, g2Length_apply]
  decide +revert

/-- **The special matrix carries every root of the pinned datum to its indexed image with the
prescribed exponent.** -/
theorem g2SpecialIsogenyMatrix_mulVec_root (i : Fin 12) :
    g2SpecialIsogenyMatrix *ᵥ g2SimplyConnectedRootDatum.root i =
      g2Length i • g2SimplyConnectedRootDatum.root (g2SpecialIsogenyIndexEquiv i) := by
  rw [g2SimplyConnectedRootDatum_root, g2SpecialIsogenyIndexEquiv_apply]
  exact g2SpecialIsogenyMatrix_mulVec_g2Root i

/-- **The transposed special matrix satisfies the contragredient equation on every coroot of the
pinned datum.** -/
theorem g2SpecialIsogenyMatrix_transpose_mulVec_coroot (i : Fin 12) :
    g2SpecialIsogenyMatrixᵀ *ᵥ
        g2SimplyConnectedRootDatum.coroot (g2SpecialIsogenyIndexEquiv i) =
      g2Length i • g2SimplyConnectedRootDatum.coroot i := by
  rw [g2SimplyConnectedRootDatum_coroot, g2SpecialIsogenyIndexEquiv_apply]
  exact g2SpecialIsogenyMatrix_transpose_mulVec_g2Coroot i

/-- The square of the character-lattice special matrix is three times the identity matrix. -/
theorem g2SpecialIsogenyMatrix_mul_self :
    g2SpecialIsogenyMatrix * g2SpecialIsogenyMatrix =
      (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g2SpecialIsogenyMatrix_def, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **The special map is an isogeny and not an automorphism of the character lattice**: its
determinant is `-3`, of absolute value the characteristic. -/
@[simp] theorem det_g2SpecialIsogenyMatrix : g2SpecialIsogenyMatrix.det = -3 := by
  rw [g2SpecialIsogenyMatrix_def, Matrix.det_fin_two_of]
  ring

/-! ## Length and exponent conventions -/

/-- The exponents at a root index and its image multiply to the characteristic `3`. -/
@[simp] theorem g2Length_mul_g2Length_g2SpecialIsogenyIndex (i : Fin 12) :
    g2Length i * g2Length (g2SpecialIsogenyIndex i) = 3 := by
  rw [g2Length_apply, g2Length_apply]
  decide +revert

/-- **The special permutation exchanges long roots with short ones.** -/
@[simp] theorem g2Length_g2SpecialIsogenyIndex_eq_one_iff (i : Fin 12) :
    g2Length (g2SpecialIsogenyIndex i) = 1 ↔ g2Length i = 3 := by
  rw [g2Length_apply, g2Length_apply]
  decide +revert

/-- **The Cartan integers transform by the rule a special isogeny forces.** Writing `α'` for the
image of a root `α` under the special permutation, pairing the root equation against the coroot
equation gives `ℓ(α) ⟨α', β'∨⟩ = ℓ(β) ⟨α, β∨⟩`. No diagram automorphism satisfies this, since the
two lengths differ. -/
theorem g2Length_mul_pairing_g2SpecialIsogenyIndexEquiv (i j : Fin 12) :
    g2Length i *
        g2SimplyConnectedRootDatum.pairing
          (g2SpecialIsogenyIndexEquiv i) (g2SpecialIsogenyIndexEquiv j) =
      g2Length j * g2SimplyConnectedRootDatum.pairing i j := by
  simp only [g2SimplyConnectedRootDatum_pairing, g2SpecialIsogenyIndexEquiv_apply]
  exact mul_dotProduct_eq_of_mulVec_eq_smul g2SpecialIsogenyMatrix_mulVec_g2Root
    g2SpecialIsogenyMatrix_transpose_mulVec_g2Coroot i j

end TauCeti.DynkinType
