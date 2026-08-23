/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2

/-!
# The special isogenies of `G₂` in characteristic three and of `F₄` in characteristic two

The root data of `B₂` and `F₄` over a field of characteristic two, and that of `G₂` over a
field of characteristic three, admit an isogeny with themselves which exchanges the two root
lengths. These three types are the only ones: exchanging the two lengths identifies the root
system with its dual, and among the non-simply-laced irreducible types only `B₂`, `F₄` and `G₂`
are self-dual, the ratio of the two lengths then fixing the characteristic. The resulting
*special isogenies* of the pinned Chevalley groups are the ones whose odd powers cut out the
Suzuki and Ree groups. This file constructs the two whose underlying pinned root data
`TauCeti.DynkinType.g2SimplyConnectedRootDatum` and `TauCeti.DynkinType.f4SimplyConnectedRootDatum`
are already available in explicit coordinates.

## The construction

Both are instances of `TauCeti.RootPairingIsogeny.ofMatrix`, so all four pieces of data are
explicit integer tables and no carrier is chosen from an existence theorem. The character and
cocharacter lattices are `Fin t.rank → ℤ` in the fundamental-weight and simple-coroot bases, and
the whole isogeny is determined by the single matrix acting on the character lattice: the
cocharacter map is its transpose, and the index bijection and exponents are then forced.

That matrix is itself forced by the length-exchanging permutation `σ` of the Bourbaki-numbered
simple roots and by the normalised squared lengths `ℓ` of `TauCeti.DynkinType.rootLength`. Writing
`x` for a character in the fundamental-weight basis, it is

```text
(A x) i = ℓ (σ i) * x (σ i),
```

with `σ` the pinned `TauCeti.lengthPermRankTwo` for `G₂` and `TauCeti.lengthPermF4` for `F₄`. On
the simple roots this reads `A (α (σ i)) = ℓ (σ i) • α i`, which is the defining relation
`f (b α) = q α · α` of a special isogeny of root data, with the isogeny exponent `q` at a simple
root the *other* length; squaring it gives `A ^ 2 = p`, since `ℓ` takes the two values `1` and `p`
and `σ` exchanges them. `TauCeti.DynkinType.g2SpecialIsogeny_comp_self` and its `F₄` counterpart
are that square relation, in the form `τ ∘ τ = Frob_p` on root data.

The tables of `TauCeti.DynkinType.g2SpecialIsogenyIndex` and its `F₄` counterpart extend `σ` from
the simple roots to all twelve, respectively forty-eight, roots. They are not free choices either:
`A` is invertible over `ℚ`, so the index bijection and the exponents are determined by the matrix,
and the tables merely record the resulting values so that the defining equations reduce.

For `F₄` the tables and their equations are already those of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/F4/SpecialMap.lean`: the matrix is
`TauCeti.DynkinType.f4SpecialIsogenyMatrix`, the index bijection is
`TauCeti.DynkinType.f4SpecialIsogenyIndexEquiv`, and the exponent is the squared-length table
`TauCeti.DynkinType.f4Length`, so all this file adds there is the bundled isogeny and the relations
that are statements about it. Only the `G₂` matrix action, which no file yet tabulates, is set up
here, against `TauCeti.DynkinType.g2Root_specialIsogenyAction` and its coroot counterpart.

## Main definitions

* `TauCeti.DynkinType.g2SpecialIsogeny`: the special isogeny of the pinned `G₂` root datum,
  belonging to characteristic three.
* `TauCeti.DynkinType.f4SpecialIsogeny`: the special isogeny of the pinned `F₄` root datum,
  belonging to characteristic two.

## Main results

* `TauCeti.DynkinType.g2SpecialIsogeny_comp_self` and
  `TauCeti.DynkinType.f4SpecialIsogeny_comp_self`: composing the special isogeny with itself gives
  scaling by the characteristic, which is the root-datum form of `τ ^ 2 = Frob_p`.
* `TauCeti.DynkinType.g2SpecialIsogenyIndex_castAdd`: on the simple roots the index bijection
  is the pinned length-exchanging permutation, which for `F₄` is
  `TauCeti.DynkinType.f4SpecialIsogenyIndex_castAdd`.
* `TauCeti.DynkinType.g2SpecialIsogeny_weightMap_root_castAdd` and
  `TauCeti.DynkinType.f4SpecialIsogeny_weightMap_root_castAdd`: the defining relation on the simple
  roots, in the form the group-scheme isogeny is pinned by.
* `TauCeti.DynkinType.g2SpecialIsogenyExponent_castAdd`: on the simple roots the exponent is the
  normalised squared root length, which for `F₄` is `TauCeti.DynkinType.f4Length_castAdd`, and
  `TauCeti.DynkinType.g2SpecialIsogeny_exponent_castAdd_eq_one_iff` and its `F₄` counterpart read
  that off as `TauCeti.DynkinType.IsLongSimpleRoot`.
* `TauCeti.DynkinType.g2SpecialIsogenyExponent_mul_g2SpecialIsogenyExponent_index`: the exponents
  at a root and at its image multiply to the characteristic, which for `F₄` is
  `TauCeti.DynkinType.f4Length_mul_f4Length_specialIsogenyIndex`.

## Roadmap and references

This is the target "Special isogenies in characteristics two and three" of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, at the level of root data; the group-scheme isogeny
`τ` is built from it. Its consumer is milestone L2 of `TauCetiRoadmap/CFSGStatement/README.md`,
which selects `τ_X` for a `TauCeti.SuzukiReeIndex` and takes odd powers of it, and whose exponent
convention is stated against `TauCeti.DynkinType.IsLongSimpleRoot` and the length permutations
pinned in `TauCeti/LinearAlgebra/RootSystem/DiagramPermutations.lean`. The remaining case `B₂` is
not here: its pinned datum `TauCeti.DynkinType.typeBSimplyConnectedRootDatum` is built uniformly in
the rank through an enumeration whose rank-two specialisation needs its own coordinate work.

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* Schémas en groupes (SGA 3), Exposé XXI, 6.8, and Exposé XXII.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti.DynkinType

open _root_.Matrix

/-! ## `G₂` in characteristic three -/

/-- The character-lattice matrix of the special isogeny of `G₂`, in the fundamental-weight basis.
It sends `x` to `(3 * x 1, x 0)`, exchanging the two nodes and attaching the squared length of the
node it came from. -/
@[expose] def g2SpecialIsogenyMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 3; 1, 0]

/-- The action of the special isogeny of `G₂` on the twelve pinned root indices. -/
@[expose] def g2SpecialIsogenyIndex : Fin 12 → Fin 12 :=
  ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 8, 9]

/-- The scalar by which the special isogeny of `G₂` rescales each of the twelve pinned roots: `1`
at a short root and `3` at a long one. -/
@[expose] def g2SpecialIsogenyExponent : Fin 12 → ℤ :=
  ![1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3]

lemma g2SpecialIsogenyIndex_involutive : Function.Involutive g2SpecialIsogenyIndex :=
  fun i => by revert i; decide

private lemma g2SpecialIsogenyMatrix_mulVecLin_sq :
    g2SpecialIsogenyMatrix.mulVecLin ∘ₗ g2SpecialIsogenyMatrix.mulVecLin =
      (3 : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) := by
  refine LinearMap.ext fun x => funext fun i => ?_
  fin_cases i <;>
    simp [g2SpecialIsogenyMatrix, mulVec, dotProduct, Fin.sum_univ_succ]

private lemma g2SpecialIsogenyMatrix_transpose_mulVecLin_sq :
    g2SpecialIsogenyMatrixᵀ.mulVecLin ∘ₗ g2SpecialIsogenyMatrixᵀ.mulVecLin =
      (3 : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) := by
  refine LinearMap.ext fun x => funext fun i => ?_
  fin_cases i <;>
    simp [g2SpecialIsogenyMatrix, vecHead, vecTail, mul_comm]

/-- **The special isogeny of the pinned `G₂` root datum**, belonging to characteristic three. Its
character-lattice map is `TauCeti.DynkinType.g2SpecialIsogenyMatrix`; the map on cocharacters is
the transposed matrix, and the two are related by the dot-product pairing of the datum. -/
def g2SpecialIsogeny :
    RootPairingIsogeny g2SimplyConnectedRootDatum g2SimplyConnectedRootDatum :=
  RootPairingIsogeny.ofMatrix _ g2SimplyConnectedRootDatum_toLinearMap g2SpecialIsogenyMatrix
    (g2SpecialIsogenyIndex_involutive.toPerm _) g2SpecialIsogenyExponent
    (fun i => by revert i; decide)
    (by decide)
    (fun i => by
      simpa [g2SpecialIsogenyMatrix, g2SpecialIsogenyExponent, g2SpecialIsogenyIndex] using
        g2Root_specialIsogenyAction i)
    (fun i => by
      simpa [g2SpecialIsogenyMatrix, g2SpecialIsogenyExponent, g2SpecialIsogenyIndex] using
        g2Coroot_specialIsogenyAction i)

@[simp] lemma g2SpecialIsogeny_weightMap :
    g2SpecialIsogeny.weightMap = g2SpecialIsogenyMatrix.mulVecLin := by
  rw [g2SpecialIsogeny]
  simp

@[simp] lemma g2SpecialIsogeny_coweightMap :
    g2SpecialIsogeny.coweightMap = g2SpecialIsogenyMatrixᵀ.mulVecLin := by
  rw [g2SpecialIsogeny]
  simp

@[simp] lemma g2SpecialIsogeny_indexEquiv_apply (i : Fin 12) :
    g2SpecialIsogeny.indexEquiv i = g2SpecialIsogenyIndex i := by
  rw [g2SpecialIsogeny]
  simp

@[simp] lemma g2SpecialIsogeny_exponent (i : Fin 12) :
    g2SpecialIsogeny.exponent i = g2SpecialIsogenyExponent i := by
  rw [g2SpecialIsogeny]
  simp

/-- On the two simple roots, the index bijection of the special isogeny of `G₂` is the pinned
length-exchanging permutation. -/
@[simp] theorem g2SpecialIsogenyIndex_castAdd (i : Fin 2) :
    g2SpecialIsogenyIndex (Fin.castAdd 10 i) = Fin.castAdd 10 (lengthPermRankTwo i) := by
  simp only [lengthPermRankTwo_apply]
  revert i; decide

/-- On the two simple roots, the exponent of the special isogeny of `G₂` is the normalised squared
root length: `1` at the short node `0` and `3` at the long node `1`. -/
@[simp] theorem g2SpecialIsogenyExponent_castAdd (i : Fin 2) :
    g2SpecialIsogenyExponent (Fin.castAdd 10 i) = G2.rootLength i := by
  rw [rootLength_G2]
  revert i; decide

/-- The exponents of the special isogeny of `G₂` at a root and at its image multiply to the
characteristic. -/
@[simp] theorem g2SpecialIsogenyExponent_mul_g2SpecialIsogenyExponent_index (i : Fin 12) :
    g2SpecialIsogenyExponent i *
      g2SpecialIsogenyExponent (g2SpecialIsogenyIndex i) = 3 := by
  revert i; decide

/-- Every exponent of the special isogeny of `G₂` is `1` or the characteristic. -/
theorem g2SpecialIsogeny_exponent_eq_one_or_eq_three (i : Fin 12) :
    g2SpecialIsogeny.exponent i = 1 ∨ g2SpecialIsogeny.exponent i = 3 := by
  simp only [g2SpecialIsogeny_exponent]
  revert i; decide

/-- **The square of the special isogeny of `G₂` is scaling by three.** This is the root-datum form
of the relation `τ ^ 2 = Frob_p` that identifies the exceptional isogeny in characteristic `p`. -/
theorem g2SpecialIsogeny_comp_self :
    g2SpecialIsogeny.comp g2SpecialIsogeny =
      RootPairingIsogeny.smulId g2SimplyConnectedRootDatum 3 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_
  · simpa using g2SpecialIsogenyMatrix_mulVecLin_sq
  · simpa using g2SpecialIsogenyMatrix_transpose_mulVecLin_sq
  · ext i
    simpa only [RootPairingIsogeny.comp_indexEquiv, RootPairingIsogeny.smulId_indexEquiv,
      Equiv.trans_apply, Equiv.refl_apply, g2SpecialIsogeny_indexEquiv_apply] using
      congrArg Fin.val (g2SpecialIsogenyIndex_involutive i)
  · funext i
    simp only [RootPairingIsogeny.comp_exponent, RootPairingIsogeny.smulId_exponent]
    have hthree : ((3 : ℕ+) : ℤ) = 3 := by norm_num
    rw [hthree]
    simpa only [g2SpecialIsogeny_exponent, g2SpecialIsogeny_indexEquiv_apply] using
      g2SpecialIsogenyExponent_mul_g2SpecialIsogenyExponent_index i

/-- **The defining relation of the special isogeny of `G₂` on the simple roots.** The character
map carries the simple root at the length-exchanged node to the simple root at `i`, rescaled by
the squared length of that other node. This is the root-datum form of
`τ (x_α (t)) = x_{σ(α)} (t ^ q)` with `q = 1` at a long simple root and `q = 3` at a short one. -/
theorem g2SpecialIsogeny_weightMap_root_castAdd (i : Fin 2) :
    g2SpecialIsogeny.weightMap
        (g2SimplyConnectedRootDatum.root (Fin.castAdd 10 (lengthPermRankTwo i))) =
      G2.rootLength (lengthPermRankTwo i) • g2SimplyConnectedRootDatum.root (Fin.castAdd 10 i) := by
  rw [g2SpecialIsogeny.root_weightMap]
  simp only [g2SpecialIsogeny_exponent, g2SpecialIsogeny_indexEquiv_apply,
    g2SpecialIsogenyExponent_castAdd, g2SpecialIsogenyIndex_castAdd,
    lengthPermRankTwo_lengthPermRankTwo]
  simp only [Int.cast_id]

/-- The exponent of the special isogeny of `G₂` at a simple root is `1` exactly at the short
node, which is the convention that the exceptional isogeny raises a long root parameter to the
first power and a short one to the characteristic. -/
theorem g2SpecialIsogeny_exponent_castAdd_eq_one_iff (i : Fin 2) :
    g2SpecialIsogeny.exponent (Fin.castAdd 10 i) = 1 ↔ ¬ G2.IsLongSimpleRoot i := by
  rw [g2SpecialIsogeny_exponent]
  rw [g2SpecialIsogenyExponent_castAdd, rootLength_G2, isLongSimpleRoot_G2]
  fin_cases i <;> simp

/-! ## `F₄` in characteristic two -/

/-- **The special isogeny of the pinned `F₄` root datum**, belonging to characteristic two. Its
character-lattice map is `TauCeti.DynkinType.f4SpecialIsogenyMatrix`; the map on cocharacters is
the transposed matrix, and the two are related by the dot-product pairing of the datum. The
rescaling exponent needs no table of its own: the pinned datum is tabulated on its own root
indices, so the squared-length table `TauCeti.DynkinType.f4Length` already is it. -/
noncomputable def f4SpecialIsogeny :
    RootPairingIsogeny f4SimplyConnectedRootDatum f4SimplyConnectedRootDatum :=
  RootPairingIsogeny.ofMatrix _ f4SimplyConnectedRootDatum_toLinearMap_apply_apply
    f4SpecialIsogenyMatrix f4SpecialIsogenyIndexEquiv f4Length f4Length_pos
    (by rw [det_f4SpecialIsogenyMatrix]; norm_num)
    f4SpecialIsogenyMatrix_mulVec_root
    f4SpecialIsogenyMatrix_transpose_mulVec_coroot

@[simp] lemma f4SpecialIsogeny_weightMap :
    f4SpecialIsogeny.weightMap = f4SpecialIsogenyMatrix.mulVecLin := by
  rw [f4SpecialIsogeny]
  simp

@[simp] lemma f4SpecialIsogeny_coweightMap :
    f4SpecialIsogeny.coweightMap = f4SpecialIsogenyMatrixᵀ.mulVecLin := by
  rw [f4SpecialIsogeny]
  simp

@[simp] lemma f4SpecialIsogeny_indexEquiv_apply (i : Fin 48) :
    f4SpecialIsogeny.indexEquiv i = f4SpecialIsogenyIndex i := by
  rw [f4SpecialIsogeny]
  simp

@[simp] lemma f4SpecialIsogeny_exponent (i : Fin 48) :
    f4SpecialIsogeny.exponent i = f4Length i := by
  rw [f4SpecialIsogeny]
  simp

/-- **The square of the special isogeny of `F₄` is scaling by two.** This is the root-datum form of
the relation `τ ^ 2 = Frob_p` that identifies the exceptional isogeny in characteristic `p`. -/
theorem f4SpecialIsogeny_comp_self :
    f4SpecialIsogeny.comp f4SpecialIsogeny =
      RootPairingIsogeny.smulId f4SimplyConnectedRootDatum 2 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_
  · simpa using f4SpecialIsogenyMatrix_mulVecLin_comp_self
  · simpa using f4SpecialIsogenyMatrix_transpose_mulVecLin_comp_self
  · ext i
    simpa only [RootPairingIsogeny.comp_indexEquiv, RootPairingIsogeny.smulId_indexEquiv,
      Equiv.trans_apply, Equiv.refl_apply, f4SpecialIsogeny_indexEquiv_apply] using
      congrArg Fin.val (f4SpecialIsogenyIndex_involutive i)
  · funext i
    simp only [RootPairingIsogeny.comp_exponent, RootPairingIsogeny.smulId_exponent]
    have htwo : ((2 : ℕ+) : ℤ) = 2 := by norm_num
    rw [htwo]
    simpa only [f4SpecialIsogeny_exponent, f4SpecialIsogeny_indexEquiv_apply] using
      f4Length_mul_f4Length_specialIsogenyIndex i

/-- **The defining relation of the special isogeny of `F₄` on the simple roots.** The character
map carries the simple root at the length-exchanged node to the simple root at `i`, rescaled by
the squared length of that other node. This is the root-datum form of
`τ (x_α (t)) = x_{σ(α)} (t ^ q)` with `q = 1` at a long simple root and `q = 2` at a short one. -/
theorem f4SpecialIsogeny_weightMap_root_castAdd (i : Fin 4) :
    f4SpecialIsogeny.weightMap
        (f4SimplyConnectedRootDatum.root (Fin.castAdd 44 (lengthPermF4 i))) =
      F4.rootLength (lengthPermF4 i) • f4SimplyConnectedRootDatum.root (Fin.castAdd 44 i) := by
  rw [f4SpecialIsogeny.root_weightMap]
  simp only [f4SpecialIsogeny_exponent, f4SpecialIsogeny_indexEquiv_apply, f4Length_castAdd,
    f4SpecialIsogenyIndex_castAdd, lengthPermF4_lengthPermF4]
  simp only [Int.cast_id]

/-- The exponent of the special isogeny of `F₄` at a simple root is `1` exactly at a short node,
which is the convention that the exceptional isogeny raises a long root parameter to the first
power and a short one to the characteristic. -/
theorem f4SpecialIsogeny_exponent_castAdd_eq_one_iff (i : Fin 4) :
    f4SpecialIsogeny.exponent (Fin.castAdd 44 i) = 1 ↔ ¬ F4.IsLongSimpleRoot i := by
  rw [f4SpecialIsogeny_exponent]
  exact f4Length_castAdd_eq_one_iff i

end TauCeti.DynkinType
