/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem

/-!
# Root subgroups on points of toral-subsystem carriers

A toral-subsystem carrier has a coordinate Hopf algebra obtained by quotienting the coordinate
algebra of `GLₙ`, and each selected represented root subgroup factors through this quotient. This
file records the resulting map on algebra-valued points. Thus, for every commutative ring `A` and
selected root index `i : S`, it supplies the intrinsic homomorphism

```text
𝔾ₐ(A) → kostantToralSubsystemGroupScheme(S)(A).
```

Composing this homomorphism with the quotient-points inclusion recovers the previously constructed
matrix-valued root subgroup. The construction is natural in `A`; in particular, iterated
Frobenius raises its root parameter to the corresponding prime-power exponent. These are the
point-level root-subgroup and field-endomorphism interfaces required when the generic Kostant
carrier is specialized to a pinned Chevalley--Demazure group.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralSubsystemPoints`: the intrinsic
  root-subgroup homomorphism on algebra-valued points of a toral-subsystem carrier.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralSubsystemParam`: the same
  homomorphism with its parameter read directly in the value ring.
* `TauCeti.UniversalEnvelopingAlgebra.mapPoints_kostantRootSubgroupToralSubsystemParam`: base-change
  naturality of the parametrized root subgroup.
* `mapPoints_iterateFrobeniusValueHom_kostantRootSubgroupToralSubsystemParam`:
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
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I)
variable (hnil : ∀ i ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

/-- A selected represented root subgroup on algebra-valued points of a toral-subsystem carrier.

Contravariance of the functor of points turns its factored coordinate morphism into a homomorphism
from the additive-group points to the intrinsic points of the quotient coordinate Hopf algebra. -/
noncomputable def kostantRootSubgroupToralSubsystemPoints (i : S) (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A →*
      HopfAlgebra.points
        (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) A :=
  ((CommHopfAlgCat.mapPointsFunctor
    (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i)).app A).hom

/-- The intrinsic root-subgroup point map is precomposition by its factored coordinate map. -/
@[simp]
theorem kostantRootSubgroupToralSubsystemPoints_apply (i : S) (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i A q =
      (CommHopfAlgCat.mapPointsFunctor
        (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i)).app A q :=
  (rfl)

/-- Including an intrinsic toral-closure root point into the ambient general linear group recovers
the original represented root-subgroup point. -/
@[simp]
theorem quotientPointsHom_kostantRootSubgroupToralSubsystemPoints
    (i : S) (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) A
        (kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i A q) =
      (CommHopfAlgCat.mapPointsFunctor
        (kostantRootSubgroupCoordinateMap e h ρ M hM i.1 (hnil i.1 i.2) b)).app A q := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply,
    kostantRootSubgroupToralSubsystemPoints_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply_apply]
  -- Evaluating the point and removing `WithConv` leaves categorical composition, whose
  -- underlying algebra homomorphism is definitionally `AlgHom.comp`.
  change q.ofConv
      (((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) ≫
          kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i).hom) x) = _
  rw [mkQuotient_comp_kostantRootSubgroupToralSubsystemCoordinateMap]

/-- In general-linear coordinates, the intrinsic root point is the divided-power exponential
matrix previously attached to the represented Kostant root subgroup.

This is not a simp lemma because `GeneralLinear.pointsMulEquiv_apply` first normalizes its
left-hand side to `GeneralLinear.pointToGeneralLinear`; use it explicitly when that matrix form is
needed. -/
theorem pointsMulEquiv_quotientPointsHom_kostantRootSubgroupToralSubsystemPoints
    (i : S) (A : Type v) [CommRing A]
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) (CommAlgCat.of ℤ A)) :
    GeneralLinear.pointsMulEquiv n
        (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) (CommAlgCat.of ℤ A)
          (kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i
            (CommAlgCat.of ℤ A) q)) =
      kostantRootSubgroupMatrix e h ρ M hM i.1 (hnil i.1 i.2) b q := by
  rw [quotientPointsHom_kostantRootSubgroupToralSubsystemPoints,
    CommHopfAlgCat.mapPointsFunctor_app_apply, GeneralLinear.pointsMulEquiv_apply]
  exact pointsMulEquiv_kostantRootSubgroupCoordinateMap
    e h ρ M hM i.1 (hnil i.1 i.2) b A q

/-- The intrinsic toral-closure root subgroup with its parameter read in the value ring through
the canonical identification `𝔾ₐ(A) ≃ A⁺`. -/
noncomputable def kostantRootSubgroupToralSubsystemParam (i : S) (A : CommAlgCat.{v} ℤ) :
    Multiplicative A →*
      HopfAlgebra.points
        (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) A :=
  (kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i A).comp
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom

/-- The parametrized intrinsic root subgroup is the point map evaluated on the corresponding
point of `𝔾ₐ`. -/
@[simp]
theorem kostantRootSubgroupToralSubsystemParam_apply (i : S) (A : CommAlgCat.{v} ℤ)
    (t : Multiplicative A) :
    kostantRootSubgroupToralSubsystemParam e h ρ M hM b wt S hnil i A t =
      kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i A
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) :=
  (rfl)

/-- The intrinsic root-subgroup point map is natural in the value algebra. -/
@[simp]
theorem mapPoints_kostantRootSubgroupToralSubsystemPoints
    (i : S) {A B : CommAlgCat.{v} ℤ} (φ : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) A) :
    HopfAlgebra.mapPoints φ
        (kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i A q) =
      kostantRootSubgroupToralSubsystemPoints e h ρ M hM b wt S hnil i B
        (HopfAlgebra.mapPoints φ q) := by
  rw [kostantRootSubgroupToralSubsystemPoints_apply,
    kostantRootSubgroupToralSubsystemPoints_apply]
  exact CommHopfAlgCat.mapPointsFunctor_naturality_apply
    (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i) φ q

/-- Base change sends the intrinsic root element with parameter `t` to the root element whose
parameter is the image of `t`. -/
@[simp]
theorem mapPoints_kostantRootSubgroupToralSubsystemParam
    (i : S) {A B : CommAlgCat.{v} ℤ} (φ : A ⟶ B) (t : Multiplicative A) :
    HopfAlgebra.mapPoints φ
        (kostantRootSubgroupToralSubsystemParam e h ρ M hM b wt S hnil i A t) =
      kostantRootSubgroupToralSubsystemParam e h ρ M hM b wt S hnil i B
        (Multiplicative.ofAdd (φ.hom (Multiplicative.toAdd t))) := by
  rw [kostantRootSubgroupToralSubsystemParam_apply,
    kostantRootSubgroupToralSubsystemParam_apply,
    mapPoints_kostantRootSubgroupToralSubsystemPoints]
  congr 1
  exact AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply φ.hom t

/-- Iterated Frobenius preserves each intrinsic root subgroup and raises its parameter to the
`p ^ m`-th power. Over an algebraic closure of `𝔽_p`, this is the root-subgroup compatibility of
the standard `q`-power Frobenius. The general simp lemma
`mapPoints_kostantRootSubgroupToralSubsystemParam` already normalizes this specialization. -/
theorem mapPoints_iterateFrobeniusValueHom_kostantRootSubgroupToralSubsystemParam
    (i : S) (p m : ℕ) (A : CommAlgCat.{v} ℤ) [ExpChar A p]
    (t : Multiplicative A) :
    HopfAlgebra.mapPoints (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil))
        (iterateFrobeniusValueHom p m A)
        (kostantRootSubgroupToralSubsystemParam e h ρ M hM b wt S hnil i A t) =
      kostantRootSubgroupToralSubsystemParam e h ρ M hM b wt S hnil i A
        (Multiplicative.ofAdd (Multiplicative.toAdd t ^ p ^ m)) := by
  rw [mapPoints_kostantRootSubgroupToralSubsystemParam, iterateFrobeniusValueHom_apply]

end TauCeti.UniversalEnvelopingAlgebra
