/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# Root subgroups on points of the toral Kostant closure

The toral Kostant closure has a coordinate Hopf algebra obtained by quotienting the coordinate
algebra of `GLₙ`, and each represented root subgroup factors through this quotient. This file
records the resulting map on algebra-valued points. Thus, for every commutative ring `A` and root
index `i`, it supplies the intrinsic homomorphism

```text
𝔾ₐ(A) → kostantToralGroupScheme(A).
```

Composing this homomorphism with the quotient-points inclusion recovers the previously constructed
matrix-valued root subgroup. The construction is natural in `A`; in particular, iterated
Frobenius raises its root parameter to the corresponding prime-power exponent. These are the
point-level root-subgroup and field-endomorphism interfaces required when the generic Kostant
carrier is specialized to a pinned Chevalley--Demazure group.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralPoints`: the intrinsic root-subgroup
  homomorphism on algebra-valued points of the toral closure.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralParam`: the same homomorphism with
  its parameter read directly in the value ring.
* `TauCeti.UniversalEnvelopingAlgebra.mapPoints_kostantRootSubgroupToralParam`: base-change
  naturality of the parametrized root subgroup.
* `mapPoints_iterateFrobeniusValueHom_kostantRootSubgroupToralParam`:
  iterated Frobenius raises the root parameter to its `p ^ m`-th power.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

This advances the “Chevalley--Demazure construction” and “points over an algebraically closed
field” targets in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. The resulting intrinsic
root-subgroup map and Frobenius law are inputs to milestones L0 and L1 of the CFSGStatement
roadmap.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

/-- The `i`th represented root subgroup on algebra-valued points of the toral Kostant closure.

Its coordinate morphism is `kostantRootSubgroupToralCoordinateMap`; contravariance of the functor
of points turns that morphism into a homomorphism from the additive-group points to the intrinsic
points of the quotient coordinate Hopf algebra. -/
noncomputable def kostantRootSubgroupToralPoints (i : I) (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A →*
      HopfAlgebra.points
        (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) A :=
  ((CommHopfAlgCat.mapPointsFunctor
    (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i)).app A).hom

private theorem kostantRootSubgroupToralPoints_apply_def (i : I) (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A q =
      (CommHopfAlgCat.mapPointsFunctor
        (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i)).app A q :=
  rfl

/-- The intrinsic root-subgroup point map is precomposition by its factored coordinate map. -/
theorem kostantRootSubgroupToralPoints_apply (i : I) (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A q =
      (CommHopfAlgCat.mapPointsFunctor
        (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i)).app A q :=
  kostantRootSubgroupToralPoints_apply_def e h ρ M hM hnil b wt i A q

/-- Including an intrinsic toral-closure root point into the ambient general linear group recovers
the original represented root-subgroup point. -/
theorem quotientPointsHom_kostantRootSubgroupToralPoints (i : I) (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) A
        (kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A q) =
      (CommHopfAlgCat.mapPointsFunctor
        (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b)).app A q := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
    kostantRootSubgroupToralPoints_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply_apply]
  change q.ofConv
      (((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ≫
          kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i).hom) x) = _
  rw [mkQuotient_comp_kostantRootSubgroupToralCoordinateMap]

/-- In general-linear coordinates, the intrinsic root point is the divided-power exponential
matrix previously attached to the represented Kostant root subgroup. -/
theorem pointsMulEquiv_quotientPointsHom_kostantRootSubgroupToralPoints
    (i : I) (A : Type v) [CommRing A]
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) (CommAlgCat.of ℤ A)) :
    GeneralLinear.pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt) (CommAlgCat.of ℤ A)
          (kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i
            (CommAlgCat.of ℤ A) q)) =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q := by
  rw [quotientPointsHom_kostantRootSubgroupToralPoints,
    CommHopfAlgCat.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply]
  exact pointsMulEquiv_kostantRootSubgroupCoordinateMap
    e h ρ M hM i (hnil i) b A q

/-- The intrinsic toral-closure root subgroup with its parameter read in the value ring through
the canonical identification `𝔾ₐ(A) ≃ A⁺`. -/
noncomputable def kostantRootSubgroupToralParam (i : I) (A : CommAlgCat.{v} ℤ) :
    Multiplicative A →*
      HopfAlgebra.points
        (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) A :=
  (kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A).comp
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom

private theorem kostantRootSubgroupToralParam_apply_def (i : I) (A : CommAlgCat.{v} ℤ)
    (t : Multiplicative A) :
    kostantRootSubgroupToralParam e h ρ M hM hnil b wt i A t =
      kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) :=
  rfl

/-- The parametrized intrinsic root subgroup is the point map evaluated on the corresponding
point of `𝔾ₐ`. -/
theorem kostantRootSubgroupToralParam_apply (i : I) (A : CommAlgCat.{v} ℤ)
    (t : Multiplicative A) :
    kostantRootSubgroupToralParam e h ρ M hM hnil b wt i A t =
      kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) :=
  kostantRootSubgroupToralParam_apply_def e h ρ M hM hnil b wt i A t

/-- The intrinsic root-subgroup point map is natural in the value algebra. -/
theorem mapPoints_kostantRootSubgroupToralPoints
    (i : I) {A B : CommAlgCat.{v} ℤ} (φ : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    HopfAlgebra.mapPoints φ
        (kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i A q) =
      kostantRootSubgroupToralPoints e h ρ M hM hnil b wt i B
        (HopfAlgebra.mapPoints φ q) := by
  rw [kostantRootSubgroupToralPoints_apply, kostantRootSubgroupToralPoints_apply]
  exact CommHopfAlgCat.mapPointsFunctor_naturality_apply
    (kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i) φ q

/-- Base change sends the intrinsic root element with parameter `t` to the root element whose
parameter is the image of `t`. -/
theorem mapPoints_kostantRootSubgroupToralParam
    (i : I) {A B : CommAlgCat.{v} ℤ} (φ : A ⟶ B) (t : Multiplicative A) :
    HopfAlgebra.mapPoints φ
        (kostantRootSubgroupToralParam e h ρ M hM hnil b wt i A t) =
      kostantRootSubgroupToralParam e h ρ M hM hnil b wt i B
        (Multiplicative.ofAdd (φ.hom (Multiplicative.toAdd t))) := by
  rw [kostantRootSubgroupToralParam_apply, kostantRootSubgroupToralParam_apply,
    mapPoints_kostantRootSubgroupToralPoints]
  congr 1
  exact AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply φ.hom t

/-- Iterated Frobenius preserves each intrinsic root subgroup and raises its parameter to the
`p ^ m`-th power. Over an algebraic closure of `𝔽_p`, this is the root-subgroup compatibility of
the standard `q`-power Frobenius. -/
theorem mapPoints_iterateFrobeniusValueHom_kostantRootSubgroupToralParam
    (i : I) (p m : ℕ) (A : CommAlgCat.{v} ℤ) [ExpChar A p]
    (t : Multiplicative A) :
    HopfAlgebra.mapPoints (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
        (iterateFrobeniusValueHom p m A)
        (kostantRootSubgroupToralParam e h ρ M hM hnil b wt i A t) =
      kostantRootSubgroupToralParam e h ρ M hM hnil b wt i A
        (Multiplicative.ofAdd (Multiplicative.toAdd t ^ p ^ m)) := by
  rw [mapPoints_kostantRootSubgroupToralParam, iterateFrobeniusValueHom_apply]

end TauCeti.UniversalEnvelopingAlgebra
