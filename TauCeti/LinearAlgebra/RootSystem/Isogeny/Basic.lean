/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.RootSystem.Hom

import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Isogenies of root pairings

A morphism of root pairings carries each root to a root. An *isogeny* is allowed to rescale: it
carries each root to a positive integer multiple of a root, with the multiple depending on the
root. This is the notion of SGA III, Exposé XXI, 6.8, and it is what an isogeny of reductive group
schemes induces on root data; the special isogenies in characteristics two and three, which are not
isomorphisms, are the reason the notion is needed at all.

`TauCeti.RootPairingIsogeny P Q` carries a linear map of weight spaces, its transpose on coweight
spaces, and a bijection of index sets, together with a family `exponent : ι → ℤ` of positive
integers, and it asks

```text
weightMap (P.root i) = exponent i • Q.root (indexEquiv i),
coweightMap (Q.coroot (indexEquiv i)) = exponent i • P.coroot i.
```

Both lattice maps are required to be injective with finite-index image. At `exponent = 1` the root
and coroot equations are those of a `RootPairing.Hom`,
`TauCeti.RootPairingIsogeny.toHom` performs that conversion, and
`TauCeti.RootPairingIsogeny.ofEquiv` turns a `RootPairing.Equiv` into an isogeny. The transpose
condition is stated as the
bilinear identity `Q.toLinearMap (weightMap x) y = P.toLinearMap x (coweightMap y)`, which is the
unfolded form of the corresponding `RootPairing.Hom` field.

The two conditions are not independent of the pairings: they force
`TauCeti.RootPairingIsogeny.exponent_mul_pairing`,

```text
exponent i * Q.pairing (indexEquiv i) (indexEquiv j) = exponent j * P.pairing i j,
```

so an isogeny with a nonconstant exponent transforms the Cartan matrix rather than preserving it.
That is exactly what a length-exchanging map of a non-simply-laced diagram does, and it is why
`RootPairing.Hom`, whose index bijection preserves all Cartan integers, cannot express one.

Isogenies compose, with exponents multiplying along the composite, and for each positive integer
`c` the scaling `TauCeti.RootPairingIsogeny.smulId P c` is an isogeny of a finite free
`ℤ`-root pairing `P` with itself with constant exponent `c`. At `c` a prime `p` the latter is the
root-datum shadow of the `p`-power Frobenius
isogeny, which is what makes `f * f = smulId P p` the root-datum form of the relation
`τ ^ 2 = Frob_p` satisfied by a special isogeny.

Composition makes the self-isogenies of `P` a monoid. This is the isogeny analogue of Mathlib's
`Monoid (RootPairing.Hom P P)` instance, with the additional exponent field accounted for.

## Main definitions

* `TauCeti.RootPairingIsogeny`: an isogeny of root pairings.
* `TauCeti.RootPairingIsogeny.comp`: the composite of two isogenies.
* `TauCeti.RootPairingIsogeny.smulId`: multiplication by a scalar, as an isogeny.
* the `Monoid` instance on `TauCeti.RootPairingIsogeny P P`, whose multiplication is composition.
* `TauCeti.RootPairingIsogeny.ofMatrix`: an isogeny between root data on coordinate lattices,
  presented by an integer matrix.
* `TauCeti.RootPairingIsogeny.toHom`: an isogeny with constant exponent `1` as a root-pairing
  morphism.
* `TauCeti.RootPairingIsogeny.ofEquiv`: an equivalence of root pairings is an isogeny with all
  exponents `1`.

## Main results

* `TauCeti.RootPairingIsogeny.exponent_mul_pairing`: the exponents intertwine the two Cartan
  matrices.
* `TauCeti.RootPairingIsogeny.pow_exponent`: the exponent of an iterate is the product along the
  corresponding orbit of indices.
* `TauCeti.RootPairingIsogeny.pow_two_mul_of_mul_self`: an isogeny squaring to a scaling has scalar
  even powers.

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
structure RootPairingIsogeny (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) : Type _ where
  /-- A linear map on weight space. -/
  weightMap : M →ₗ[R] M₂
  /-- A contravariant linear map on coweight space. -/
  coweightMap : N₂ →ₗ[R] N
  /-- A bijection on index sets. -/
  indexEquiv : ι ≃ ι₂
  /-- The positive integer by which the root at each index is rescaled. -/
  exponent : ι → ℤ
  /-- Every root-rescaling exponent is positive. -/
  exponent_pos : ∀ i, 0 < exponent i
  /-- The map on the weight lattice is injective. -/
  weightMap_injective : Function.Injective weightMap
  /-- The contravariant map on the coweight lattice is injective. -/
  coweightMap_injective : Function.Injective coweightMap
  /-- The image in the target weight lattice has finite index. -/
  weightMap_finiteIndex : weightMap.range.toAddSubgroup.FiniteIndex
  /-- The image in the source coweight lattice has finite index. -/
  coweightMap_finiteIndex : coweightMap.range.toAddSubgroup.FiniteIndex
  /-- The weight and coweight maps are transposes with respect to the two root pairings. -/
  weight_coweight_transpose : ∀ (x : M) (y : N₂),
    Q.toLinearMap (weightMap x) y = P.toLinearMap x (coweightMap y)
  /-- The weight map sends each root to its prescribed positive integral multiple. -/
  root_weightMap : ∀ i, weightMap (P.root i) = (exponent i : R) • Q.root (indexEquiv i)
  /-- The coweight map sends each corresponding coroot to the same integral multiple. -/
  coroot_coweightMap : ∀ i,
    coweightMap (Q.coroot (indexEquiv i)) = (exponent i : R) • P.coroot i

attribute [simp] RootPairingIsogeny.root_weightMap RootPairingIsogeny.coroot_coweightMap

namespace RootPairingIsogeny

variable {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-- An isogeny whose exponents are all `1`, as a morphism of root pairings. -/
def toHom (f : RootPairingIsogeny P Q) (h : ∀ i, f.exponent i = 1) : RootPairing.Hom P Q where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  weight_coweight_transpose := by
    ext y x
    exact f.weight_coweight_transpose x y
  root_weightMap := by
    ext i
    simp [f.root_weightMap, h i]
  coroot_coweightMap := by
    ext i
    simpa [h] using f.coroot_coweightMap (f.indexEquiv.symm i)

@[simp] theorem toHom_weightMap (f : RootPairingIsogeny P Q) (h : ∀ i, f.exponent i = 1) :
    (toHom f h).weightMap = f.weightMap := by
  rw [toHom]

@[simp] theorem toHom_coweightMap (f : RootPairingIsogeny P Q) (h : ∀ i, f.exponent i = 1) :
    (toHom f h).coweightMap = f.coweightMap := by
  rw [toHom]

@[simp] theorem toHom_indexEquiv (f : RootPairingIsogeny P Q) (h : ∀ i, f.exponent i = 1) :
    (toHom f h).indexEquiv = f.indexEquiv := by
  rw [toHom]

/-- The exponents of an isogeny intertwine the Cartan matrices of its source and target. -/
theorem exponent_mul_pairing (f : RootPairingIsogeny P Q) (i j : ι) :
    (f.exponent i : R) * Q.pairing (f.indexEquiv i) (f.indexEquiv j) =
      (f.exponent j : R) * P.pairing i j := by
  have h : Q.toLinearMap (f.weightMap (P.root i)) (Q.coroot (f.indexEquiv j)) =
      P.toLinearMap (P.root i) (f.coweightMap (Q.coroot (f.indexEquiv j))) :=
    f.weight_coweight_transpose _ _
  rw [f.root_weightMap, f.coroot_coweightMap] at h
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    _root_.RootPairing.root_coroot_eq_pairing] using h

/-- Multiplication by a positive integer, as an isogeny of a finite free `ℤ`-root pairing with
itself. At a prime `p` this is the isogeny of root data underlying the `p`-power Frobenius. -/
def smulId [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (P : RootPairing ι ℤ M N) (c : ℕ+) : RootPairingIsogeny P P where
  weightMap := (c : ℕ) • LinearMap.id
  coweightMap := (c : ℕ) • LinearMap.id
  indexEquiv := Equiv.refl ι
  exponent := fun _ => c
  exponent_pos _ := by exact_mod_cast c.pos
  weightMap_injective :=
    AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree c.ne_zero
  coweightMap_injective :=
    AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree c.ne_zero
  weightMap_finiteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    -- The scalar linear map and `nsmulAddMonoidHom` have definitionally equal ranges; this
    -- reshaping is needed to apply Mathlib's index formula for multiplication by `c`.
    change (nsmulAddMonoidHom (α := M) c).range.index ≠ 0
    rw [AddSubgroup.index_range_nsmul]
    exact pow_ne_zero _ c.ne_zero
  coweightMap_finiteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    -- As above, expose the additive range expected by `index_range_nsmul`.
    change (nsmulAddMonoidHom (α := N) c).range.index ≠ 0
    rw [AddSubgroup.index_range_nsmul]
    exact pow_ne_zero _ c.ne_zero
  weight_coweight_transpose x y := by
    simp
  root_weightMap i := by simp
  coroot_coweightMap i := by simp

@[simp] theorem smulId_weightMap [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : RootPairing ι ℤ M N) (c : ℕ+) :
    (smulId P c).weightMap = (c : ℕ) • LinearMap.id := by
  rw [smulId]

@[simp] theorem smulId_coweightMap [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : RootPairing ι ℤ M N) (c : ℕ+) :
    (smulId P c).coweightMap = (c : ℕ) • LinearMap.id := by
  rw [smulId]

@[simp] theorem smulId_indexEquiv [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : RootPairing ι ℤ M N) (c : ℕ+) :
    (smulId P c).indexEquiv = Equiv.refl ι := by
  rw [smulId]

@[simp] theorem smulId_exponent [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ N] [Module.Finite ℤ N] (P : RootPairing ι ℤ M N) (c : ℕ+) (i : ι) :
    (smulId P c).exponent i = c := by
  rw [smulId]

/-- The composite of two linear maps with finite-index images again has finite-index image. -/
private lemma finiteIndex_range_comp (g : M₂ →ₗ[R] M₃) (f : M →ₗ[R] M₂)
    (hf : f.range.toAddSubgroup.FiniteIndex)
    (hgf : g.range.toAddSubgroup.FiniteIndex) : (g ∘ₗ f).range.toAddSubgroup.FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff]
  let A := (g ∘ₗ f).range.toAddSubgroup
  let B := g.range.toAddSubgroup
  have hAB : A ≤ B := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨f y, hy⟩
  rw [← AddSubgroup.relIndex_mul_index hAB]
  apply mul_ne_zero
  · have hA : A = f.range.toAddSubgroup.map g.toAddMonoidHom := by
      ext x
      simp only [A, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨f y, ⟨y, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, rfl⟩
    have hB : B = (⊤ : AddSubgroup M₂).map g.toAddMonoidHom := by
      ext x
      -- Membership in the range of `g` is definitionally the displayed existential for the
      -- image of the top subgroup.
      change (∃ y, g y = x) ↔ ∃ y, y ∈ (⊤ : AddSubgroup M₂) ∧ g y = x
      simp
    rw [hA, hB, AddSubgroup.relIndex_map_map, top_sup_eq, AddSubgroup.relIndex_top_right]
    let _ : f.range.toAddSubgroup.FiniteIndex := hf
    exact (AddSubgroup.finiteIndex_of_le le_sup_left).index_ne_zero
  · exact hgf.index_ne_zero

/-- The composite of two isogenies, whose exponent at an index is the product of the exponent of
the first at that index and the exponent of the second at its image. -/
def comp (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q) :
    RootPairingIsogeny P S where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  exponent := fun i => f.exponent i * g.exponent (f.indexEquiv i)
  exponent_pos i := mul_pos (f.exponent_pos i) (g.exponent_pos (f.indexEquiv i))
  weightMap_injective := g.weightMap_injective.comp f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective.comp g.coweightMap_injective
  weightMap_finiteIndex := finiteIndex_range_comp g.weightMap f.weightMap
    f.weightMap_finiteIndex g.weightMap_finiteIndex
  coweightMap_finiteIndex := finiteIndex_range_comp f.coweightMap g.coweightMap
    g.coweightMap_finiteIndex f.coweightMap_finiteIndex
  weight_coweight_transpose x y := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, g.weight_coweight_transpose,
      f.weight_coweight_transpose]
  root_weightMap i := by
    rw [LinearMap.comp_apply, f.root_weightMap, map_smul, g.root_weightMap, smul_smul]
    simp only [Int.cast_mul, Equiv.trans_apply]
  coroot_coweightMap i := by
    rw [LinearMap.comp_apply, Equiv.trans_apply, g.coroot_coweightMap, map_smul,
      f.coroot_coweightMap, smul_smul, mul_comm, Int.cast_mul]

@[simp] theorem comp_weightMap (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q) :
    (comp g f).weightMap = g.weightMap ∘ₗ f.weightMap := by
  rw [comp]

@[simp] theorem comp_coweightMap (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q) :
    (comp g f).coweightMap = f.coweightMap ∘ₗ g.coweightMap := by
  rw [comp]

@[simp] theorem comp_indexEquiv (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q) :
    (comp g f).indexEquiv = f.indexEquiv.trans g.indexEquiv := by
  rw [comp]

@[simp] theorem comp_exponent (g : RootPairingIsogeny Q S) (f : RootPairingIsogeny P Q)
    (i : ι) : (comp g f).exponent i = f.exponent i * g.exponent (f.indexEquiv i) := by
  rw [comp]

section Coordinates

open Matrix

variable {n : ℕ}

private lemma matrix_mulVecLin_finiteIndex_of_det_ne_zero
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.FiniteIndex := by
  let d := A.det.natAbs
  have hd : d ≠ 0 := Int.natAbs_ne_zero.mpr hA
  have hdFinite : (nsmulAddMonoidHom (α := Fin n → ℤ) d).range.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, AddSubgroup.index_range_nsmul]
    exact pow_ne_zero _ hd
  apply @AddSubgroup.finiteIndex_of_le (Fin n → ℤ) _ _ _ hdFinite
  rintro _ ⟨x, rfl⟩
  rcases le_total 0 A.det with hdet | hdet
  · refine ⟨Matrix.cramer A x, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_cramer]
    exact congrArg (· • x) (Int.natAbs_of_nonneg hdet).symm
  · refine ⟨-Matrix.cramer A x, ?_⟩
    -- The range goal unfolds scalar multiplication by `d : ℕ` to `d`-fold addition, whereas
    -- Cramer's rule is stated using the corresponding integer scalar action.
    change A.mulVecLin (-Matrix.cramer A x) = d • x
    rw [map_neg, Matrix.mulVecLin_apply, Matrix.mulVec_cramer, ← neg_smul]
    exact congrArg (· • x) (Int.ofNat_natAbs_of_nonpos hdet).symm

/-- An isogeny between root data on the coordinate lattices `Fin n → ℤ` with the
dot-product pairing, presented by the integer matrix acting on the character lattice. The map on
the cocharacter lattice is the transposed matrix, which is what the transpose condition forces.
Nonvanishing of the determinant supplies injectivity and finite-index image for both maps. -/
def ofMatrix (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (Q : RootDatum ι₂ (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y)
    (hQ : ∀ x y : Fin n → ℤ, Q.toLinearMap x y = x ⬝ᵥ y)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : ι ≃ ι₂) (c : ι → ℤ) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hroot : ∀ i, A *ᵥ P.root i = c i • Q.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ Q.coroot (e i) = c i • P.coroot i) :
    RootPairingIsogeny P Q where
  weightMap := A.mulVecLin
  coweightMap := Aᵀ.mulVecLin
  indexEquiv := e
  exponent := c
  exponent_pos := hc
  weightMap_injective := Matrix.mulVec_injective_of_det_ne_zero hA
  coweightMap_injective := Matrix.mulVec_injective_of_det_ne_zero (by simpa using hA)
  weightMap_finiteIndex := matrix_mulVecLin_finiteIndex_of_det_ne_zero A hA
  coweightMap_finiteIndex := matrix_mulVecLin_finiteIndex_of_det_ne_zero Aᵀ (by simpa using hA)
  weight_coweight_transpose x y := by
    rw [hQ, hP, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact (dotProduct_comm _ _).trans (dotProduct_transpose_mulVec A x y).symm
  root_weightMap := hroot
  coroot_coweightMap := hcoroot

@[simp] theorem ofMatrix_weightMap (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (Q : RootDatum ι₂ (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y)
    (hQ : ∀ x y : Fin n → ℤ, Q.toLinearMap x y = x ⬝ᵥ y)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : ι ≃ ι₂) (c : ι → ℤ) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hroot : ∀ i, A *ᵥ P.root i = c i • Q.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ Q.coroot (e i) = c i • P.coroot i) :
    (ofMatrix P Q hP hQ A e c hc hA hroot hcoroot).weightMap = A.mulVecLin := by
  rw [ofMatrix]

@[simp] theorem ofMatrix_coweightMap (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (Q : RootDatum ι₂ (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y)
    (hQ : ∀ x y : Fin n → ℤ, Q.toLinearMap x y = x ⬝ᵥ y)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : ι ≃ ι₂) (c : ι → ℤ) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hroot : ∀ i, A *ᵥ P.root i = c i • Q.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ Q.coroot (e i) = c i • P.coroot i) :
    (ofMatrix P Q hP hQ A e c hc hA hroot hcoroot).coweightMap = Aᵀ.mulVecLin := by
  rw [ofMatrix]

@[simp] theorem ofMatrix_indexEquiv (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (Q : RootDatum ι₂ (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y)
    (hQ : ∀ x y : Fin n → ℤ, Q.toLinearMap x y = x ⬝ᵥ y)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : ι ≃ ι₂) (c : ι → ℤ) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hroot : ∀ i, A *ᵥ P.root i = c i • Q.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ Q.coroot (e i) = c i • P.coroot i) :
    (ofMatrix P Q hP hQ A e c hc hA hroot hcoroot).indexEquiv = e := by
  rw [ofMatrix]

@[simp] theorem ofMatrix_exponent (P : RootDatum ι (Fin n → ℤ) (Fin n → ℤ))
    (Q : RootDatum ι₂ (Fin n → ℤ) (Fin n → ℤ))
    (hP : ∀ x y : Fin n → ℤ, P.toLinearMap x y = x ⬝ᵥ y)
    (hQ : ∀ x y : Fin n → ℤ, Q.toLinearMap x y = x ⬝ᵥ y)
    (A : Matrix (Fin n) (Fin n) ℤ) (e : ι ≃ ι₂) (c : ι → ℤ) (hc : ∀ i, 0 < c i)
    (hA : A.det ≠ 0)
    (hroot : ∀ i, A *ᵥ P.root i = c i • Q.root (e i))
    (hcoroot : ∀ i, Aᵀ *ᵥ Q.coroot (e i) = c i • P.coroot i) (i : ι) :
    (ofMatrix P Q hP hQ A e c hc hA hroot hcoroot).exponent i = c i := by
  rw [ofMatrix]

end Coordinates

end RootPairingIsogeny

/-- An equivalence of root pairings is an isogeny all of whose exponents are `1`. -/
def RootPairingIsogeny.ofEquiv {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    (f : RootPairing.Equiv P Q) : RootPairingIsogeny P Q where
  weightMap := f.toHom.weightMap
  coweightMap := f.toHom.coweightMap
  indexEquiv := f.toHom.indexEquiv
  exponent := fun _ => 1
  exponent_pos _ := by norm_num
  weightMap_injective := f.bijective_weightMap.injective
  coweightMap_injective := f.bijective_coweightMap.injective
  weightMap_finiteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    have hr : f.toHom.weightMap.range = ⊤ :=
      LinearMap.range_eq_top.mpr f.bijective_weightMap.surjective
    rw [hr, Submodule.top_toAddSubgroup, AddSubgroup.index_top]
    exact one_ne_zero
  coweightMap_finiteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    have hr : f.toHom.coweightMap.range = ⊤ :=
      LinearMap.range_eq_top.mpr f.bijective_coweightMap.surjective
    rw [hr, Submodule.top_toAddSubgroup, AddSubgroup.index_top]
    exact one_ne_zero
  weight_coweight_transpose x y := by
    simpa using congrArg (fun g : Module.Dual R M => g x)
      (_root_.RootPairing.Hom.weight_coweight_transpose_apply P Q y f.toHom)
  root_weightMap i := by simp [_root_.RootPairing.Hom.root_weightMap_apply P Q i f.toHom]
  coroot_coweightMap i := by
    simp [_root_.RootPairing.Hom.coroot_coweightMap_apply P Q _ f.toHom]

@[simp] theorem RootPairingIsogeny.ofEquiv_weightMap
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} (f : RootPairing.Equiv P Q) :
    (RootPairingIsogeny.ofEquiv f).weightMap = f.toHom.weightMap := by
  rw [RootPairingIsogeny.ofEquiv]

@[simp] theorem RootPairingIsogeny.ofEquiv_coweightMap
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} (f : RootPairing.Equiv P Q) :
    (RootPairingIsogeny.ofEquiv f).coweightMap = f.toHom.coweightMap := by
  rw [RootPairingIsogeny.ofEquiv]

@[simp] theorem RootPairingIsogeny.ofEquiv_indexEquiv
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} (f : RootPairing.Equiv P Q) :
    (RootPairingIsogeny.ofEquiv f).indexEquiv = f.toHom.indexEquiv := by
  rw [RootPairingIsogeny.ofEquiv]

@[simp] theorem RootPairingIsogeny.ofEquiv_exponent
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} (f : RootPairing.Equiv P Q) (i : ι) :
    (RootPairingIsogeny.ofEquiv f).exponent i = 1 := by
  rw [RootPairingIsogeny.ofEquiv]

namespace RootPairingIsogeny

variable {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-- The identity isogeny of a root pairing. -/
def id (P : RootPairing ι R M N) : RootPairingIsogeny P P :=
  ofEquiv (RootPairing.Equiv.id P)

@[simp] theorem id_weightMap (P : RootPairing ι R M N) :
    (id P).weightMap = LinearMap.id := by
  rw [id, ofEquiv]
  rfl

@[simp] theorem id_coweightMap (P : RootPairing ι R M N) :
    (id P).coweightMap = LinearMap.id := by
  rw [id, ofEquiv]
  rfl

@[simp] theorem id_indexEquiv (P : RootPairing ι R M N) :
    (id P).indexEquiv = Equiv.refl ι := by
  rw [id, ofEquiv]
  rfl

@[simp] theorem id_exponent (P : RootPairing ι R M N) (i : ι) :
    (id P).exponent i = 1 := by
  rw [id, ofEquiv]

/-- Composing an isogeny on the left with the identity isogeny does not change it. -/
@[simp] theorem comp_id (f : RootPairingIsogeny P Q) : comp (id Q) f = f := by
  ext <;> simp [comp, id, ofEquiv]

/-- Composing an isogeny on the right with the identity isogeny does not change it. -/
@[simp] theorem id_comp (f : RootPairingIsogeny P Q) : comp f (id P) = f := by
  ext <;> simp [comp, id, ofEquiv]

variable {ι₄ M₄ N₄ : Type*} [AddCommGroup M₄] [Module R M₄]
  [AddCommGroup N₄] [Module R N₄]
  {T : RootPairing ι₄ R M₄ N₄}

/-- Composition of root-pairing isogenies is associative. -/
@[simp] theorem comp_assoc (h : RootPairingIsogeny S T) (g : RootPairingIsogeny Q S)
    (f : RootPairingIsogeny P Q) : comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp [comp, mul_assoc]

/-! ### Iterates of a self-isogeny -/

section Iterate

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- Composition of isogenies of a root pairing with itself, with the identity isogeny as unit.
Multiplication is `TauCeti.RootPairingIsogeny.comp`, in the same order as for endomorphisms of a
module: `f * g` applies `g` first. -/
instance : Monoid (RootPairingIsogeny P P) where
  mul := comp
  one := id P
  mul_assoc := comp_assoc
  one_mul := comp_id
  mul_one := id_comp

/-- The product in the monoid of self-isogenies is composition. -/
theorem mul_def (f g : RootPairingIsogeny P P) : f * g = comp f g := rfl

/-- The unit of the monoid of self-isogenies is the identity isogeny. -/
theorem one_def : (1 : RootPairingIsogeny P P) = id P := rfl

/-- The character-lattice map of a product is the composite of the two character-lattice maps. -/
@[simp] theorem mul_weightMap (f g : RootPairingIsogeny P P) :
    (f * g).weightMap = f.weightMap ∘ₗ g.weightMap := by
  rw [mul_def, comp_weightMap]

/-- The cocharacter map of a composite is the composite in the opposite order: an isogeny is
contravariant on coweight space. -/
@[simp] theorem mul_coweightMap (f g : RootPairingIsogeny P P) :
    (f * g).coweightMap = g.coweightMap ∘ₗ f.coweightMap := by
  rw [mul_def, comp_coweightMap]

/-- The index bijection of a product is the product of the two index bijections, as
permutations. -/
@[simp] theorem mul_indexEquiv (f g : RootPairingIsogeny P P) :
    (f * g).indexEquiv = f.indexEquiv * g.indexEquiv := by
  rw [mul_def, comp_indexEquiv, Equiv.Perm.mul_def]

/-- The exponent of `f * g` at `i` is the exponent of `g` at `i`, times the exponent of `f` at
`g.indexEquiv i`. -/
@[simp] theorem mul_exponent (f g : RootPairingIsogeny P P) (i : ι) :
    (f * g).exponent i = g.exponent i * f.exponent (g.indexEquiv i) := by
  rw [mul_def, comp_exponent]

/-- The identity isogeny is the identity on the character lattice. -/
@[simp] theorem one_weightMap : (1 : RootPairingIsogeny P P).weightMap = LinearMap.id := by
  rw [one_def, id_weightMap]

/-- The identity isogeny is the identity on the cocharacter lattice. -/
@[simp] theorem one_coweightMap : (1 : RootPairingIsogeny P P).coweightMap = LinearMap.id := by
  rw [one_def, id_coweightMap]

/-- The identity isogeny fixes every index. -/
@[simp] theorem one_indexEquiv : (1 : RootPairingIsogeny P P).indexEquiv = Equiv.refl ι := by
  rw [one_def, id_indexEquiv]

/-- The identity isogeny rescales no root. -/
@[simp] theorem one_exponent (i : ι) : (1 : RootPairingIsogeny P P).exponent i = 1 := by
  rw [one_def, id_exponent]

/-- The character-lattice map of an iterate is the iterate of the character-lattice map. -/
@[simp] theorem pow_weightMap (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).weightMap = f.weightMap ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => rw [pow_succ, mul_weightMap, ih, pow_succ, Module.End.mul_eq_comp]

/-- The cocharacter map of an iterate is the iterate of the cocharacter map. Composition reverses
the order, but a power of an endomorphism commutes with itself, so no reversal is visible. -/
@[simp] theorem pow_coweightMap (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).coweightMap = f.coweightMap ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => rw [pow_succ, mul_coweightMap, ih, pow_succ', Module.End.mul_eq_comp]

/-- The index bijection of an iterate is the iterate of the index bijection. -/
theorem pow_indexEquiv (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).indexEquiv = f.indexEquiv ^ k := by
  induction k with
  | zero => simp [Equiv.Perm.one_def]
  | succ k ih => rw [pow_succ, mul_indexEquiv, ih, pow_succ]

/-- **The exponent of an iterate accumulates along the forward orbit of the index bijection.**
Unlike the other three fields the exponent is not multiplicative: the exponent of a composite at
an index is the product of the exponents met at the successive images of that index. -/
theorem pow_exponent (f : RootPairingIsogeny P P) (k : ℕ) (i : ι) :
    (f ^ k).exponent i = ∏ j ∈ Finset.range k, f.exponent ((f.indexEquiv ^ j) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_exponent, ih, pow_indexEquiv, Finset.prod_range_succ]

end Iterate

/-! ### Iterates of a square root of a scaling -/

section Scaling

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
  {P : RootPairing ι ℤ M N}

/-- Scaling by one is the identity isogeny. -/
@[simp] theorem smulId_one : smulId P 1 = 1 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_ <;> ext <;> simp

/-- The product of two scalings is the scaling by the product. -/
@[simp] theorem smulId_mul_smulId (c d : ℕ+) : smulId P c * smulId P d = smulId P (c * d) := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_
  · ext x
    simp [mul_smul]
  · ext x
    rw [mul_comm c d]
    simp [mul_smul]
  · ext i
    simp
  · funext i
    simp only [mul_exponent, smulId_exponent, smulId_indexEquiv]
    push_cast
    ring

/-- Iterating a scaling raises the scalar to the corresponding power. -/
@[simp] theorem smulId_pow (c : ℕ+) (k : ℕ) : smulId P c ^ k = smulId P (c ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, smulId_mul_smulId, pow_succ]

variable {f : RootPairingIsogeny P P} {c : ℕ+}

/-- **An isogeny that squares to a scaling has scalar even powers.** The special isogenies in
characteristics two and three are square roots of the Frobenius scaling in this sense, and this is
what makes an odd power of one of them differ from a Frobenius by a single further application. -/
theorem pow_two_mul_of_mul_self (hf : f * f = smulId P c) (m : ℕ) :
    f ^ (2 * m) = smulId P (c ^ m) := by
  rw [pow_mul, pow_two, hf, smulId_pow]

/-- **Every power of an isogeny that squares to a scaling again squares to a scaling.** -/
theorem pow_mul_pow_of_mul_self (hf : f * f = smulId P c) (k : ℕ) :
    f ^ k * f ^ k = smulId P (c ^ k) := by
  rw [← pow_add, ← two_mul, pow_two_mul_of_mul_self hf]

/-- An odd power is a scaling composed with the original isogeny. -/
theorem pow_two_mul_add_one_of_mul_self (hf : f * f = smulId P c) (m : ℕ) :
    f ^ (2 * m + 1) = smulId P (c ^ m) * f := by
  rw [pow_succ, pow_two_mul_of_mul_self hf]

/-- An odd power of an isogeny that squares to a scaling acts on indices exactly as the isogeny
itself does. -/
theorem pow_odd_indexEquiv_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).indexEquiv = f.indexEquiv := by
  rw [pow_two_mul_add_one_of_mul_self hf, mul_indexEquiv, smulId_indexEquiv,
    ← Equiv.Perm.one_def, one_mul]

/-- **The exponent of an odd power of an isogeny that squares to scaling by `c`.** It is the
exponent of the isogeny itself, multiplied by `c ^ m`. -/
theorem pow_odd_exponent_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ) (i : ι) :
    (f ^ (2 * m + 1)).exponent i = f.exponent i * (c : ℤ) ^ m := by
  rw [pow_two_mul_add_one_of_mul_self hf, mul_exponent, smulId_exponent]
  push_cast
  ring

/-- The character-lattice map of an odd power is that of the isogeny itself, scaled by `c ^ m`. -/
theorem pow_odd_weightMap_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).weightMap = ((c : ℕ) ^ m) • f.weightMap := by
  rw [pow_two_mul_add_one_of_mul_self hf, mul_weightMap, smulId_weightMap,
    LinearMap.smul_comp, LinearMap.id_comp, PNat.pow_coe]

/-- The cocharacter map of an odd power is that of the isogeny itself, scaled by `c ^ m`. -/
theorem pow_odd_coweightMap_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).coweightMap = ((c : ℕ) ^ m) • f.coweightMap := by
  rw [pow_two_mul_add_one_of_mul_self hf, mul_coweightMap, smulId_coweightMap]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, PNat.pow_coe]
  exact map_nsmul f.coweightMap _ x

/-- The action of an odd power on a root, in terms of the original isogeny. -/
theorem root_weightMap_pow_odd_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ) (i : ι) :
    (f ^ (2 * m + 1)).weightMap (P.root i) =
      (f.exponent i * (c : ℤ) ^ m) • P.root (f.indexEquiv i) := by
  rw [(f ^ (2 * m + 1)).root_weightMap, pow_odd_exponent_of_mul_self_eq_smulId hf,
    pow_odd_indexEquiv_of_mul_self_eq_smulId hf]
  simp only [Int.cast_id]

/-- The action of an odd power on a coroot, in terms of the original isogeny. -/
theorem coroot_coweightMap_pow_odd_of_mul_self_eq_smulId (hf : f * f = smulId P c) (m : ℕ)
    (i : ι) :
    (f ^ (2 * m + 1)).coweightMap (P.coroot (f.indexEquiv i)) =
      (f.exponent i * (c : ℤ) ^ m) • P.coroot i := by
  rw [← pow_odd_indexEquiv_of_mul_self_eq_smulId hf,
    (f ^ (2 * m + 1)).coroot_coweightMap, pow_odd_exponent_of_mul_self_eq_smulId hf]
  simp only [Int.cast_id]

/-- **The two exponents of a power at an index and at its image multiply to `c ^ k`.** -/
theorem pow_exponent_mul_exponent_indexEquiv_of_mul_self_eq_smulId
    (hf : f * f = smulId P c) (k : ℕ) (i : ι) :
    (f ^ k).exponent i * (f ^ k).exponent ((f ^ k).indexEquiv i) = (c : ℤ) ^ k := by
  have h := congrArg (fun g : RootPairingIsogeny P P => g.exponent i) (pow_mul_pow_of_mul_self hf k)
  simpa using h

end Scaling

end RootPairingIsogeny

end TauCeti
