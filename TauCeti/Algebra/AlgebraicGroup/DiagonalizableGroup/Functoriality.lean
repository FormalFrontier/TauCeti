/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Functoriality of the diagonalizable group in the abelian group

`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic` computes the functor of points of the
diagonalizable group `D(G) = Spec R[G]`: for every commutative `R`-algebra `A`, the
convolution group of `R`-algebra maps `R[G] →ₐ[R] A` is the character group `G →* Aˣ`. This
file records the remaining variance, making `D` into a **contravariant functor** on commutative
groups: a group homomorphism `φ : G →* G'` induces a homomorphism of group functors
`D(φ) : D(G') → D(G)`, and under the character identification this is just **precomposition**
`χ ↦ χ ∘ φ` of characters.

Concretely `φ` induces, by `MonoidAlgebra.mapDomainBialgHom`, the bialgebra map
`R[G] →ₐc[R] R[G']`, which `TauCeti.AlgHom.mapDomain` turns into a monoid homomorphism
`WithConv (R[G'] →ₐ[R] A) →* WithConv (R[G] →ₐ[R] A)` of convolution groups. The headline
calculation `pointsMulEquiv_pointsMap` says this monoid homomorphism is intertwined by
`pointsMulEquiv` with precomposition by `φ` on character groups, so the contravariant functor
`G ↦ D(G)` agrees on points with the contravariant functor `G ↦ (G →* Aˣ)`. This is the
on-points half of the roadmap's anti-equivalence `M ↦ D(M)`.

This advances the reductive-groups roadmap (Layer 4, "diagonalizable groups and groups of
multiplicative type: the anti-equivalence `M ↦ D(M)`"), building on the diagonalizable-group
worked example and the coordinate-Hopf-algebra functoriality `AlgHom.mapDomain`.

## Main declarations

* `TauCeti.DiagonalizableGroup.pointsMap`: the homomorphism of convolution groups of points
  induced by a group homomorphism `φ : G →* G'`, contravariantly.
* `TauCeti.DiagonalizableGroup.pointsMap_id`, `TauCeti.DiagonalizableGroup.pointsMap_comp`:
  the contravariant functoriality of `pointsMap`.
* `TauCeti.DiagonalizableGroup.mapValue_pointsMap`: `pointsMap` is natural in the value
  algebra, commuting with `AlgHom.mapValue`.
* `TauCeti.DiagonalizableGroup.charOfPoint_comp`: reading off the character of a precomposed
  point is precomposition of the character by `φ`.
* `TauCeti.DiagonalizableGroup.pointsMulEquiv_pointsMap`: the points homomorphism is
  intertwined by `pointsMulEquiv` with precomposition of characters by `φ`.

## References

The group-algebra bialgebra functoriality `MonoidAlgebra.mapDomainBialgHom` is Mathlib's
(`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`). The convolution-group functoriality in the
coordinate Hopf algebra is Tau Ceti's `TauCeti.AlgHom.mapDomain`
(`TauCeti.Algebra.AlgebraicGroup.Hopf.Map`). This realizes the diagonalizable-group
functoriality of the Tau Ceti reductive-groups roadmap (Layer 4).
-/

public section

open WithConv

namespace TauCeti

universe u v w w' w''

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w} {G' : Type w'} {G'' : Type w''}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [CommGroup G] [CommGroup G'] [CommGroup G'']

/-- **The diagonalizable group is contravariant in the abelian group.** A group homomorphism
`φ : G →* G'` induces, by pre-composition with the bialgebra map `R[G] →ₐc[R] R[G']`, a
homomorphism of convolution groups of points `D(G')(A) → D(G)(A)`. -/
@[expose] noncomputable def pointsMap (φ : G →* G') :
    WithConv (MonoidAlgebra R G' →ₐ[R] A) →* WithConv (MonoidAlgebra R G →ₐ[R] A) :=
  AlgHom.mapDomain (MonoidAlgebra.mapDomainBialgHom R φ)

/-- `pointsMap φ` acts by pre-composition with the induced bialgebra map. -/
@[simp]
theorem pointsMap_apply (φ : G →* G') (f : WithConv (MonoidAlgebra R G' →ₐ[R] A)) :
    pointsMap (A := A) φ f =
      toConv (f.ofConv.comp
        (MonoidAlgebra.mapDomainBialgHom R φ : MonoidAlgebra R G →ₐ[R] MonoidAlgebra R G')) :=
  rfl

/-- Pre-composition by the identity homomorphism is the identity on points. -/
@[simp]
theorem pointsMap_id :
    (pointsMap (MonoidHom.id G) :
        WithConv (MonoidAlgebra R G →ₐ[R] A) →* WithConv (MonoidAlgebra R G →ₐ[R] A)) =
      MonoidHom.id _ := by
  rw [pointsMap, MonoidAlgebra.mapDomainBialgHom_id, AlgHom.mapDomain_id]

/-- **Contravariant functoriality.** Pre-composition by a composite homomorphism is the
composite of the induced points homomorphisms, in the opposite order. -/
theorem pointsMap_comp (φ : G →* G') (ψ : G' →* G'') :
    (pointsMap (A := A) (ψ.comp φ) :
        WithConv (MonoidAlgebra R G'' →ₐ[R] A) →* WithConv (MonoidAlgebra R G →ₐ[R] A)) =
      (pointsMap (R := R) (A := A) φ).comp (pointsMap (R := R) (A := A) ψ) := by
  rw [pointsMap, pointsMap, pointsMap, MonoidAlgebra.mapDomainBialgHom_comp,
    AlgHom.mapDomain_comp]

/-- **Naturality in the value algebra.** The contravariant points homomorphism `pointsMap φ`
commutes with the value-algebra functoriality `AlgHom.mapValue χ`: pre-composition by the
induced bialgebra map and post-composition by `χ : A →ₐ[R] B` may be applied in either order.
This makes `pointsMap φ` a natural transformation of functors of points. -/
theorem mapValue_pointsMap {B : Type*} [CommSemiring B] [Algebra R B] (φ : G →* G')
    (χ : A →ₐ[R] B) :
    (pointsMap (A := B) φ).comp (AlgHom.mapValue (H := MonoidAlgebra R G') χ) =
      (AlgHom.mapValue (H := MonoidAlgebra R G) χ).comp (pointsMap (A := A) φ) := by
  rw [pointsMap, pointsMap]
  exact AlgHom.mapValue_mapDomain (MonoidAlgebra.mapDomainBialgHom R φ) χ

/-- Reading off the character of a point pre-composed by the induced bialgebra map is the
character of the original point pre-composed by `φ`. -/
@[simp]
theorem charOfPoint_comp (φ : G →* G') (f : MonoidAlgebra R G' →ₐ[R] A) :
    charOfPoint (f.comp
        (MonoidAlgebra.mapDomainBialgHom R φ : MonoidAlgebra R G →ₐ[R] MonoidAlgebra R G')) =
      (charOfPoint f).comp φ := by
  ext g
  rw [charOfPoint_apply_coe, AlgHom.comp_apply, MonoidHom.comp_apply, charOfPoint_apply_coe,
    BialgHom.coe_toAlgHom (MonoidAlgebra.mapDomainBialgHom R φ),
    MonoidAlgebra.mapDomainBialgHom, _root_.BialgHom.ofAlgHom_apply,
    MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

/-- **The points homomorphism is precomposition of characters.** Under the identification of
points of `D(G)` with characters of `G`, the homomorphism `pointsMap φ` induced by
`φ : G →* G'` is intertwined with precomposition `χ ↦ χ ∘ φ` of characters. -/
theorem pointsMulEquiv_pointsMap (φ : G →* G') (f : WithConv (MonoidAlgebra R G' →ₐ[R] A)) :
    pointsMulEquiv (pointsMap (A := A) φ f) = (pointsMulEquiv f).comp φ := by
  rw [pointsMap_apply, pointsMulEquiv_apply, ofConv_toConv, pointsMulEquiv_apply, charOfPoint_comp]

/-- If `φ` is surjective, then the induced contravariant map on diagonalizable-group points is
injective. Under the character identification this is injectivity of precomposition by a
surjective homomorphism. -/
theorem pointsMap_injective (φ : G →* G') (hφ : Function.Surjective φ) :
    Function.Injective (pointsMap (R := R) (A := A) φ) := by
  intro f g hfg
  apply (pointsMulEquiv (R := R) (A := A) (G := G')).injective
  have hchar : (pointsMulEquiv f).comp φ = (pointsMulEquiv g).comp φ := by
    rw [← pointsMulEquiv_pointsMap, ← pointsMulEquiv_pointsMap, hfg]
  exact DFunLike.coe_injective
    (hφ.injective_comp_right (funext fun x => DFunLike.congr_fun hchar x))

/-- Mapping the point attached to a character is precomposition of that character by `φ`. -/
theorem pointsMap_pointsMulEquiv_symm_apply (φ : G →* G') (χ : G' →* Aˣ) :
    pointsMap (R := R) (A := A) φ ((pointsMulEquiv (R := R) (A := A) (G := G')).symm χ) =
      (pointsMulEquiv (R := R) (A := A) (G := G)).symm (χ.comp φ) := by
  apply (pointsMulEquiv (R := R) (A := A) (G := G)).injective
  rw [pointsMulEquiv_pointsMap]
  rw [(pointsMulEquiv (R := R) (A := A) (G := G')).apply_symm_apply χ]
  exact ((pointsMulEquiv (R := R) (A := A) (G := G)).apply_symm_apply (χ.comp φ)).symm

end DiagonalizableGroup

end TauCeti
