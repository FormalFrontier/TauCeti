/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.RootSystem.Hom

/-!
# Isogenies of root pairings

A morphism of root pairings carries each root to a root. An *isogeny* is allowed to rescale: it
carries each root to a positive integer multiple of a root, with the multiple depending on the
root. This is the notion of SGA III, Exposé XXI, 6.8, and it is what an isogeny of reductive group
schemes induces on root data; the special isogenies in characteristics two and three, which are not
isomorphisms, are the reason the notion is needed at all.

`TauCeti.RootPairingIsogeny P Q` carries the same data as Mathlib's `RootPairing.Hom P Q` — a
linear map of weight spaces, its transpose on coweight spaces, and a bijection of index sets —
together with a family `exponent : ι → R` of scalars, and it asks

```text
weightMap (P.root i) = exponent i • Q.root (indexEquiv i),
coweightMap (Q.coroot (indexEquiv i)) = exponent i • P.coroot i.
```

At `exponent = 1` these are exactly the two conditions defining a `RootPairing.Hom`, and
`TauCeti.RootPairingIsogeny.ofHom` records that. The transpose condition is stated as the
bilinear identity `Q.toLinearMap (weightMap x) y = P.toLinearMap x (coweightMap y)`, which is the
unfolded form of the corresponding `RootPairing.Hom` field.

The two conditions are not independent of the pairings: they force
`TauCeti.RootPairingIsogeny.exponent_mul_pairing`,

```text
exponent i * Q.pairing (indexEquiv i) (indexEquiv j) = exponent j * P.pairing i j,
```

so an isogeny with a nonconstant exponent transforms the Cartan matrix rather than preserving it.
That is exactly what a length-exchanging map of a doubly laced diagram does, and it is why
`RootPairing.Hom`, whose index bijection preserves all Cartan integers, cannot express one.

Isogenies compose, with exponents multiplying along the composite, and for each scalar `c` the
scaling `TauCeti.RootPairingIsogeny.smulId P c` is an isogeny of `P` with itself with constant
exponent `c`. At `c` a prime `p` the latter is the root-datum shadow of the `p`-power Frobenius
isogeny, which is what makes `f.comp f = smulId P p` the root-datum form of the relation
`τ ^ 2 = Frob_p` satisfied by a special isogeny.

## Main definitions

* `TauCeti.RootPairingIsogeny`: an isogeny of root pairings.
* `TauCeti.RootPairingIsogeny.comp`: the composite of two isogenies.
* `TauCeti.RootPairingIsogeny.smulId`: multiplication by a scalar, as an isogeny.
* `TauCeti.RootPairingIsogeny.ofMatrix`: an isogeny of a root datum on coordinate lattices,
  presented by an integer matrix.
* `TauCeti.RootPairingIsogeny.ofHom`: a morphism of root pairings is an isogeny with all
  exponents `1`.

## Main results

* `TauCeti.RootPairingIsogeny.exponent_mul_pairing`: the exponents intertwine the two Cartan
  matrices.

## References

* Schémas en groupes (SGA 3), Exposé XXI, 6.8.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.

This is a prerequisite for the target "Special isogenies in characteristics two and three" in
Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]

/-- An isogeny of root pairings: a pair of mutually transposed maps of weight and coweight spaces
and a bijection of index sets, carrying each root to a prescribed scalar multiple of a root and
each coroot to the same multiple of a coroot.

With all exponents equal to `1` this is a `RootPairing.Hom`; the extra generality is what an
isogeny of reductive group schemes that is not an isomorphism induces on root data. -/
@[ext]
structure RootPairingIsogeny (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) where
  /-- A linear map on weight space. -/
  weightMap : M →ₗ[R] M₂
  /-- A contravariant linear map on coweight space. -/
  coweightMap : N₂ →ₗ[R] N
  /-- A bijection on index sets. -/
  indexEquiv : ι ≃ ι₂
  /-- The scalar by which the root at each index is rescaled. -/
  exponent : ι → R
  weight_coweight_transpose : ∀ (x : M) (y : N₂),
    Q.toLinearMap (weightMap x) y = P.toLinearMap x (coweightMap y)
  root_weightMap : ∀ i, weightMap (P.root i) = exponent i • Q.root (indexEquiv i)
  coroot_coweightMap : ∀ i, coweightMap (Q.coroot (indexEquiv i)) = exponent i • P.coroot i

namespace RootPairingIsogeny

variable {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-- The exponents of an isogeny intertwine the Cartan matrices of its source and target. -/
theorem exponent_mul_pairing (f : RootPairingIsogeny P Q) (i j : ι) :
    f.exponent i * Q.pairing (f.indexEquiv i) (f.indexEquiv j) = f.exponent j * P.pairing i j := by
  have h : Q.toLinearMap (f.weightMap (P.root i)) (Q.coroot (f.indexEquiv j)) =
      P.toLinearMap (P.root i) (f.coweightMap (Q.coroot (f.indexEquiv j))) :=
    f.weight_coweight_transpose _ _
  rw [f.root_weightMap, f.coroot_coweightMap] at h
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    _root_.RootPairing.root_coroot_eq_pairing] using h

/-- Multiplication by a scalar, as an isogeny of a root pairing with itself. At a prime `p` this
is the isogeny of root data underlying the `p`-power Frobenius. -/
@[expose, simps]
def smulId (P : RootPairing ι R M N) (c : R) : RootPairingIsogeny P P where
  weightMap := c • LinearMap.id
  coweightMap := c • LinearMap.id
  indexEquiv := Equiv.refl ι
  exponent := fun _ => c
  weight_coweight_transpose x y := by
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
  root_weightMap i := by simp
  coroot_coweightMap i := by simp

/-- The composite of two isogenies, whose exponent at an index is the product of the exponent of
the first at that index and the exponent of the second at its image. -/
@[expose, simps]
def comp (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q) : RootPairingIsogeny P S where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  exponent := fun i => f.exponent i * g.exponent (f.indexEquiv i)
  weight_coweight_transpose x y := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, g.weight_coweight_transpose,
      f.weight_coweight_transpose]
  root_weightMap i := by
    rw [LinearMap.comp_apply, f.root_weightMap, map_smul, g.root_weightMap, smul_smul]
    rfl
  coroot_coweightMap i := by
    rw [LinearMap.comp_apply, show (f.indexEquiv.trans g.indexEquiv) i =
      g.indexEquiv (f.indexEquiv i) from rfl, g.coroot_coweightMap, map_smul,
      f.coroot_coweightMap, smul_smul, mul_comm]

section Coordinates

open Matrix

variable {n : ℕ}

/-- An isogeny of a root datum on the coordinate lattices `Fin n → ℤ` with the dot-product
pairing, presented by the integer matrix acting on the character lattice. The map on the
cocharacter lattice is the transposed matrix, which is what the transpose condition forces. -/
@[expose, simps]
def ofMatrix (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y) (A : Matrix (Fin n) (Fin n) ℤ)
    (e : Equiv.Perm ι) (c : ι → ℤ) (hroot : ∀ i, A *ᵥ P.root i = c i • P.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ P.coroot (e i) = c i • P.coroot i) :
    RootPairingIsogeny P P where
  weightMap := A.mulVecLin
  coweightMap := Aᵀ.mulVecLin
  indexEquiv := e
  exponent := c
  weight_coweight_transpose x y := by
    rw [hP, hP, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact (dotProduct_comm _ _).trans (dotProduct_transpose_mulVec A x y).symm
  root_weightMap := hroot
  coroot_coweightMap := hcoroot

end Coordinates

end RootPairingIsogeny

/-- A morphism of root pairings is an isogeny all of whose exponents are `1`. -/
@[expose, simps]
def RootPairingIsogeny.ofHom {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    (f : RootPairing.Hom P Q) : RootPairingIsogeny P Q where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  exponent := fun _ => 1
  weight_coweight_transpose x y := by
    simpa using congrArg (fun g : Module.Dual R M => g x)
      (_root_.RootPairing.Hom.weight_coweight_transpose_apply P Q y f)
  root_weightMap i := by simp [_root_.RootPairing.Hom.root_weightMap_apply P Q i f]
  coroot_coweightMap i := by simp [_root_.RootPairing.Hom.coroot_coweightMap_apply P Q _ f]

end TauCeti
