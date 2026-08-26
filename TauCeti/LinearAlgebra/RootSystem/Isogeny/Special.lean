/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.SpecialMap

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

Both sets of tables and their matrix equations already exist:
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/G2/SpecialMap.lean` and
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/F4/SpecialMap.lean` supply the matrices
`TauCeti.DynkinType.g2SpecialIsogenyMatrix` and `TauCeti.DynkinType.f4SpecialIsogenyMatrix`, the
index bijections `TauCeti.DynkinType.g2SpecialIsogenyIndexEquiv` and
`TauCeti.DynkinType.f4SpecialIsogenyIndexEquiv`, and the squared-length tables
`TauCeti.DynkinType.g2Length` and `TauCeti.DynkinType.f4Length` that are the exponents. All this
file adds is the bundled isogeny in each case, and the relations that are statements about it.

## Main definitions

* `TauCeti.DynkinType.g2SpecialIsogeny`: the special isogeny of the pinned `G₂` root datum,
  belonging to characteristic three.
* `TauCeti.DynkinType.f4SpecialIsogeny`: the special isogeny of the pinned `F₄` root datum,
  belonging to characteristic two.

## Main results

* `TauCeti.DynkinType.g2SpecialIsogeny_comp_self` and
  `TauCeti.DynkinType.f4SpecialIsogeny_comp_self`: composing the special isogeny with itself gives
  scaling by the characteristic, which is the root-datum form of `τ ^ 2 = Frob_p`.
* `TauCeti.DynkinType.g2SpecialIsogeny_weightMap_root_castLE` and
  `TauCeti.DynkinType.f4SpecialIsogeny_weightMap_root_castAdd`: the defining relation on the simple
  roots, in the form the group-scheme isogeny is pinned by.
* `TauCeti.DynkinType.g2SpecialIsogeny_exponent_castLE_eq_one_iff` and its `F₄` counterpart:
  on the simple roots the exponent is `1` exactly at a short node, read off as
  `TauCeti.DynkinType.IsLongSimpleRoot`.

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

/-- The square of the transposed character-lattice special matrix of `G₂` is three times the
identity matrix. -/
private lemma g2SpecialIsogenyMatrix_transpose_mul_self :
    g2SpecialIsogenyMatrixᵀ * g2SpecialIsogenyMatrixᵀ =
      (3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [← transpose_mul, g2SpecialIsogenyMatrix_mul_self, transpose_smul, transpose_one]

private lemma g2SpecialIsogenyMatrix_mulVecLin_comp_self :
    g2SpecialIsogenyMatrix.mulVecLin ∘ₗ g2SpecialIsogenyMatrix.mulVecLin =
      (3 : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) := by
  rw [← Matrix.mulVecLin_mul, g2SpecialIsogenyMatrix_mul_self]
  ext x i
  simp

private lemma g2SpecialIsogenyMatrix_transpose_mulVecLin_comp_self :
    g2SpecialIsogenyMatrixᵀ.mulVecLin ∘ₗ g2SpecialIsogenyMatrixᵀ.mulVecLin =
      (3 : ℤ) • (LinearMap.id : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) := by
  rw [← Matrix.mulVecLin_mul, g2SpecialIsogenyMatrix_transpose_mul_self]
  ext x i
  simp

/-- **The special isogeny of the pinned `G₂` root datum**, belonging to characteristic three. Its
character-lattice map is `TauCeti.DynkinType.g2SpecialIsogenyMatrix`; the map on cocharacters is
the transposed matrix, and the two are related by the dot-product pairing of the datum. The
rescaling exponent needs no table of its own: the pinned datum is tabulated on its own root
indices, so the squared-length table `TauCeti.DynkinType.g2Length` already is it. -/
def g2SpecialIsogeny :
    RootPairingIsogeny g2SimplyConnectedRootDatum g2SimplyConnectedRootDatum :=
  RootPairingIsogeny.ofMatrix _ _ g2SimplyConnectedRootDatum_toLinearMap
    g2SimplyConnectedRootDatum_toLinearMap g2SpecialIsogenyMatrix g2SpecialIsogenyIndexEquiv
    g2Length g2Length_pos
    (by rw [det_g2SpecialIsogenyMatrix]; norm_num)
    g2SpecialIsogenyMatrix_mulVec_root
    g2SpecialIsogenyMatrix_transpose_mulVec_coroot

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
    g2SpecialIsogeny.exponent i = g2Length i := by
  rw [g2SpecialIsogeny]
  simp

/-- **The square of the special isogeny of `G₂` is scaling by three.** This is the root-datum form
of the relation `τ ^ 2 = Frob_p` that identifies the exceptional isogeny in characteristic `p`. -/
theorem g2SpecialIsogeny_comp_self :
    g2SpecialIsogeny.comp g2SpecialIsogeny =
      RootPairingIsogeny.smulId g2SimplyConnectedRootDatum 3 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_
  · simpa using g2SpecialIsogenyMatrix_mulVecLin_comp_self
  · simpa using g2SpecialIsogenyMatrix_transpose_mulVecLin_comp_self
  · ext i
    simpa only [RootPairingIsogeny.comp_indexEquiv, RootPairingIsogeny.smulId_indexEquiv,
      Equiv.trans_apply, Equiv.refl_apply, g2SpecialIsogeny_indexEquiv_apply] using
      congrArg Fin.val (g2SpecialIsogenyIndex_involutive i)
  · funext i
    simp only [RootPairingIsogeny.comp_exponent, RootPairingIsogeny.smulId_exponent]
    have hthree : ((3 : ℕ+) : ℤ) = 3 := by norm_num
    rw [hthree]
    simpa only [g2SpecialIsogeny_exponent, g2SpecialIsogeny_indexEquiv_apply] using
      g2Length_mul_g2Length_g2SpecialIsogenyIndex i

/-- **The defining relation of the special isogeny of `G₂` on the simple roots.** The character
map carries the simple root at the length-exchanged node to the simple root at `i`, rescaled by
the squared length of that other node. This is the root-datum form of
`τ (x_α (t)) = x_{σ(α)} (t ^ q)` with `q = 1` at a long simple root and `q = 3` at a short one. -/
theorem g2SpecialIsogeny_weightMap_root_castLE (i : Fin 2) :
    g2SpecialIsogeny.weightMap
        (g2SimplyConnectedRootDatum.root (Fin.castLE (by omega) (lengthPermRankTwo i))) =
      G2.rootLength (lengthPermRankTwo i) •
        g2SimplyConnectedRootDatum.root (Fin.castLE (by omega) i) := by
  rw [g2SpecialIsogeny.root_weightMap]
  simp only [g2SpecialIsogeny_exponent, g2SpecialIsogeny_indexEquiv_apply, g2Length_castLE,
    g2SpecialIsogenyIndex_castLE, lengthPermRankTwo_lengthPermRankTwo]
  simp only [Int.cast_id]

/-- The exponent of the special isogeny of `G₂` at a simple root is `1` exactly at the short
node, which is the convention that the exceptional isogeny raises a long root parameter to the
first power and a short one to the characteristic. -/
theorem g2SpecialIsogeny_exponent_castLE_eq_one_iff (i : Fin 2) :
    g2SpecialIsogeny.exponent (Fin.castLE (by omega) i) = 1 ↔ ¬ G2.IsLongSimpleRoot i := by
  rw [g2SpecialIsogeny_exponent]
  exact g2Length_castLE_eq_one_iff i

/-! ## `F₄` in characteristic two -/

/-- **The special isogeny of the pinned `F₄` root datum**, belonging to characteristic two. Its
character-lattice map is `TauCeti.DynkinType.f4SpecialIsogenyMatrix`; the map on cocharacters is
the transposed matrix, and the two are related by the dot-product pairing of the datum. The
rescaling exponent needs no table of its own: the pinned datum is tabulated on its own root
indices, so the squared-length table `TauCeti.DynkinType.f4Length` already is it. -/
noncomputable def f4SpecialIsogeny :
    RootPairingIsogeny f4SimplyConnectedRootDatum f4SimplyConnectedRootDatum :=
  RootPairingIsogeny.ofMatrix _ _ f4SimplyConnectedRootDatum_toLinearMap_apply_apply
    f4SimplyConnectedRootDatum_toLinearMap_apply_apply f4SpecialIsogenyMatrix
    f4SpecialIsogenyIndexEquiv f4Length f4Length_pos
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
