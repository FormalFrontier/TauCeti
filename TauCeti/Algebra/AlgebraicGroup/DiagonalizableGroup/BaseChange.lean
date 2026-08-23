/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.Bialgebra.MonoidAlgebra.BaseChange

/-!
# Base change of diagonalizable-group points

For a commutative group `G`, the diagonalizable group `D(G)` over `k` is represented by the
Hopf algebra `k[G]`. The imported `TauCeti.MonoidAlgebra.scalarTensorBialgEquiv` identifies its
base change `K ⊗[k] k[G]` with `K[G]` as a bialgebra. This file records the corresponding
calculation on functors of points: if `A` is a commutative `K`-algebra, then the `A`-valued
points of the base-changed Hopf algebra are still the character group `G →* Aˣ`.

The construction is the composition of two existing Tau Ceti equivalences:
`AlgHom.baseChangePointsMulEquiv`, which identifies points of `K ⊗[k] k[G]` with
`k`-algebra maps out of `k[G]`, and `DiagonalizableGroup.pointsMulEquiv`, which identifies
those maps with characters. The lemmas here spell out the values on the group-like generators
`1 ⊗ single g 1`, the inverse map, and compatibility with the contravariant functoriality
in `G`.

This advances the ReductiveGroups roadmap, Layer 0 ("Base change. `K ⊗[k] A` as a Hopf
algebra over `K`") and Layer 4 ("Diagonalizable groups and groups of multiplicative type:
`M ↦ D(M) = Spec k[M]`").

## Main declarations

* `TauCeti.DiagonalizableGroup.baseChangePointsMulEquiv`: the multiplicative equivalence
  from base-changed points of `D(G)` to the character group `G →* Aˣ`.
* `TauCeti.DiagonalizableGroup.baseChangeCoordinateRingIso`: base change of the finite-type
  coordinate Hopf algebra of `D(G)` is the corresponding coordinate Hopf algebra over the new
  base.
* `TauCeti.DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso`: the same isomorphism read in
  `CommHopfAlgCat`.
* `TauCeti.DiagonalizableGroup.baseChangePointsMulEquiv_apply_coe`: the equivalence reads a
  point by evaluating it on `1 ⊗ single g 1`.
* `TauCeti.DiagonalizableGroup.baseChangePointsMulEquiv_mapDomain_scalarTensorBialgEquiv`:
  the coordinate-ring and points-level base-change equivalences agree.
* `TauCeti.DiagonalizableGroup.baseChangePointsMulEquiv_mapDomain`: under a homomorphism
  `G →* G'`, the base-changed points map is precomposition of characters.

## References

The group-algebra Hopf structure and `MonoidAlgebra.mapDomainBialgHom` are Mathlib's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` and
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`. The base-change equivalence and the
diagonalizable-group points calculation are Tau Ceti's
`TauCeti.AlgHom.baseChangePointsMulEquiv` and
`TauCeti.DiagonalizableGroup.pointsMulEquiv`.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w w'

namespace DiagonalizableGroup

variable {k : Type u} {K : Type v} {A : Type w} {G : Type w'}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable [CommGroup G]

/-- **The coordinate Hopf algebra of a finite-type diagonalizable group commutes with base
change.** This is the bundled form of `MonoidAlgebra.scalarTensorBialgEquiv` for a finitely
generated commutative group `G`:

```text
K ⊗[k] k[G] ≅ K[G].
```

It is an abbreviation so that `MonoidAlgebra.scalarTensorBialgEquiv_tmul` and
`MonoidAlgebra.scalarTensorBialgEquiv_symm_single` apply directly to its forward and inverse maps,
without duplicating their statements at this bundling layer.
-/
noncomputable abbrev baseChangeCoordinateRingIso
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K]
    (G : FGCommGrpCat.{u}) :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (coordinateRing k G) ≅
      coordinateRing K G :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.isoMk (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k K (G := G))

/-- The `CommHopfAlgCat`-level form of `baseChangeCoordinateRingIso`, obtained by forgetting the
finite-type property. It is the isomorphism `K ⊗[k] k[G] ≅ K[G]` of commutative Hopf algebras. -/
noncomputable abbrev baseChangeCoordinateHopfAlgebraIso
    (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K]
    (G : FGCommGrpCat.{u}) :
    CommHopfAlgCat.baseChange (K := K) (coordinateRing k G).obj ≅
      (coordinateRing K G).obj :=
  (ObjectProperty.ι _).mapIso (baseChangeCoordinateRingIso k K G)

/-- The `A`-points of the base change `K ⊗[k] k[G]` of the diagonalizable group `D(G)` are
the character group `G →* Aˣ`.

The source is the convolution group of `K`-algebra maps out of the base-changed Hopf algebra.
The target is the ordinary pointwise-multiplication group of characters. -/
@[expose] noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] MonoidAlgebra k G →ₐ[K] A) ≃* (G →* Aˣ) :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := MonoidAlgebra k G) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (A := A) (G := G))

/-- Applying `baseChangePointsMulEquiv` first restricts a base-changed point along
`g ↦ 1 ⊗ single g 1`, then reads off its character. -/
@[simp]
theorem baseChangePointsMulEquiv_apply
    (f : WithConv (K ⊗[k] MonoidAlgebra k G →ₐ[K] A)) :
    baseChangePointsMulEquiv f =
      charOfPoint
        (((AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
          (A := MonoidAlgebra k G) (R := A)).symm f).ofConv) :=
  rfl

/-- The base-changed diagonalizable-points equivalence reads a point by evaluating it on the
base-changed group-like element `1 ⊗ single g 1`. -/
@[simp]
theorem baseChangePointsMulEquiv_apply_coe
    (f : WithConv (K ⊗[k] MonoidAlgebra k G →ₐ[K] A)) (g : G) :
    (baseChangePointsMulEquiv f g : A) =
      f.ofConv (1 ⊗ₜ[k] MonoidAlgebra.single g (1 : k)) := by
  rw [baseChangePointsMulEquiv_apply, charOfPoint_apply_coe,
    AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed diagonalizable-points equivalence extends a character after
base change. On a pure tensor it sends `s ⊗ single g r` to `s • (r • χ g)`. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_single (χ : G →* Aˣ) (s : K)
    (g : G) (r : k) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G)).symm χ).ofConv
        (s ⊗ₜ[k] MonoidAlgebra.single g r) =
      s • (r • (χ g : A)) := by
  simp [baseChangePointsMulEquiv, DiagonalizableGroup.pointsMulEquiv_symm_apply,
    DiagonalizableGroup.point_single]

/-- The inverse base-changed diagonalizable-points equivalence takes `1 ⊗ single g 1` to the
value of the character at `g`. -/
theorem baseChangePointsMulEquiv_symm_apply_single_one (χ : G →* Aˣ) (g : G) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G)).symm χ).ofConv
        (1 ⊗ₜ[k] MonoidAlgebra.single g (1 : k)) =
      (χ g : A) := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_single]
  simp

/-- The coordinate-ring and functor-of-points base-change identifications agree. A point of
`K[G]`, restricted along `K ⊗[k] k[G] ≃ₐc[K] K[G]`, gives the same character under
`baseChangePointsMulEquiv` as it does under the ordinary `pointsMulEquiv` over `K`. -/
theorem baseChangePointsMulEquiv_mapDomain_scalarTensorBialgEquiv
    (f : WithConv (MonoidAlgebra K G →ₐ[K] A)) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G)
        (AlgHom.mapDomain (A := A)
          (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k K (G := G) :
            K ⊗[k] MonoidAlgebra k G →ₐc[K] MonoidAlgebra K G) f) =
      pointsMulEquiv (R := K) (A := A) (G := G) f := by
  ext g
  simp

section MapDomain

variable {G' : Type*} [CommGroup G']

/-- Under base change, the points map induced contravariantly by `φ : G →* G'` is
precomposition of characters by `φ`. -/
theorem baseChangePointsMulEquiv_mapDomain (φ : G →* G')
    (f : WithConv (K ⊗[k] MonoidAlgebra k G' →ₐ[K] A)) :
    baseChangePointsMulEquiv
        (AlgHom.mapDomain (A := A)
          (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K)
            (MonoidAlgebra.mapDomainBialgHom k φ)) f) =
      (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G') f).comp φ := by
  ext g
  simp only [baseChangePointsMulEquiv_apply_coe, MonoidHom.comp_apply,
    AlgHom.mapDomain_apply_apply, _root_.Bialgebra.TensorProduct.map_tmul,
    _root_.BialgHom.id_apply, MonoidAlgebra.mapDomainBialgHom,
    _root_.BialgHom.ofAlgHom_apply, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single]

/-- Mapping the base-changed point attached to a character is precomposition of that character
by the homomorphism of character groups. -/
theorem mapDomain_baseChangePointsMulEquiv_symm_apply (φ : G →* G') (χ : G' →* Aˣ) :
    AlgHom.mapDomain (A := A)
        (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K)
          (MonoidAlgebra.mapDomainBialgHom k φ))
        ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G')).symm χ) =
      (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G)).symm (χ.comp φ) := by
  apply (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (G := G)).injective
  rw [baseChangePointsMulEquiv_mapDomain]
  simp

end MapDomain

end DiagonalizableGroup

end TauCeti
