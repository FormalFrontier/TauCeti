/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeightTorus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.BaseChange

/-!
# Base-changed toral Kostant subsystem carriers inside the general linear group

The toral Kostant subsystem carrier over `ℤ` attached to a set `S` is the closed subgroup scheme
of `GLₙ` generated jointly by the represented root subgroups indexed by `S` and a represented
split torus. Base change first presents it inside the scalar extension `A ⊗[ℤ] O(GLₙ/ℤ)`. This
file transports that presentation across the canonical Hopf-algebra isomorphism

```text
A ⊗[ℤ] O(GLₙ/ℤ) ≅ O(GLₙ/A),
```

so the carrier is cut out directly inside `GLₙ` over `A`. The root-subgroup parameter algebra and
the split-torus coordinate algebra are transported at the same time. Consequently the factored
maps have target `O(𝔾ₐ/A)` and `O(T/A)`, rather than scalar extensions of the corresponding
coordinate algebras over `ℤ`. The `Presentation` in the names records exactly this: these objects
live in the coordinate algebras built directly over `A`, whereas the
`kostantToralSubsystemBaseChange*` family of `ToralClosure/BaseChange.lean` lives in the scalar
extensions of the integral ones.

Everything here is a transport of the integral data, not a fresh construction over `A`. In
particular the transported root-subgroup and split-torus maps are not identified with maps
constructed directly over `A`: for the torus such an identification would need base-change
compatibility of `GeneralLinear.diagonalTorusCoordinateMap`, which is a separate step, and on the
root-subgroup side no over-`A` construction exists yet.

The transported ideal need not be the largest Hopf ideal killed by the root subgroups and torus
after base change: new equations may appear over a non-flat base. The proved comparison therefore
has the honest direction only. The closed subgroup generated over `A` by the transported root and
torus maps lies in the base change of the integral toral-subsystem carrier; equality is not
asserted.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralSubsystemBaseChangePresentationIdeal`: the
  transported defining ideal in `O(GLₙ/A)`.
* `kostantToralSubsystemBaseChangePresentationIso`: its quotient is the base change of the
  integral toral-subsystem coordinate ring.
* `kostantRootSubgroupBaseChangePresentationCoordinateMap` and
  `kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap`: the transported base
  change of a root subgroup and its factorization through the transported toral carrier.
* `kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap`: the factorization of
  `GeneralLinear.weightTorusBaseChangeCoordinateMap` through the transported carrier.
* `kostantToralSubsystemBaseChangePresentationIdeal_le_commonKernelHopfIdeal`: the
  generated-over-`A` carrier is a closed subgroup of the transported integral carrier.

## References

This is the base-change compatibility of the explicit Chevalley--Demazure construction; see
R. W. Carter, *Simple Groups of Lie Type*, §4.4, and B. Conrad, *Reductive Group Schemes*, §1.
It advances Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. The resulting carrier over the
prime field and its algebraic closure is consumed by milestone L0 of the CFSGStatement roadmap.

The formal inputs are Tau Ceti's own coordinate base-change isomorphisms
`GeneralLinear.coordinateHopfAlgebraBaseChangeIso`,
`AdditiveGroup.coordinateHopfAlgebraBaseChangeIso`, and
`DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso`, together with the Hopf-ideal quotient
API of `CommHopfAlgCat` and the sibling
`Kostant/RootSubgroup/Scheme/ToralClosure/BaseChange.lean`, whose declaration structure this file
mirrors. Mathlib supplies the lower-level inputs those isomorphisms rest on
(`MvPolynomial.algebraTensorAlgEquiv`, `IsLocalization.Away.tensorProductEquivTMulRight`,
`MonoidAlgebra.scalarTensorEquiv`) and the category `CommHopfAlgCat` itself.
-/

public section

open CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

/-- The base change of the `i`th integral root-subgroup coordinate map, transported into the
coordinate Hopf algebras built directly over `A`. -/
noncomputable def kostantRootSubgroupBaseChangePresentationCoordinateMap (i : I)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (A : Type*) [CommRing A] :
    GeneralLinear.coordinateHopfAlgebra A n ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
    CommHopfAlgCat.baseChangeMap
      (kostantRootSubgroupCoordinateMap e h ρ M hM i hi b) ≫
    (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom

omit [Finite κ] in
/-- The transported base-changed root-subgroup map is the stated composite of the two coordinate
base-change isomorphisms with the scalar extension of the map over `ℤ`. -/
theorem kostantRootSubgroupBaseChangePresentationCoordinateMap_def (i : I)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (A : Type*) [CommRing A] :
    kostantRootSubgroupBaseChangePresentationCoordinateMap e h ρ M hM i hi b A =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (kostantRootSubgroupCoordinateMap e h ρ M hM i hi b) ≫
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom := by
  unfold kostantRootSubgroupBaseChangePresentationCoordinateMap
  rfl

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I)
variable (hnil : ∀ i ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (A : Type*) [CommRing A]

/-- The Hopf ideal of `O(GLₙ/A)` presenting the base change of the toral Kostant subsystem
carrier: the inverse image of the base-changed defining ideal under the general-linear coordinate
base-change isomorphism. -/
noncomputable def kostantToralSubsystemBaseChangePresentationIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A n) :=
  (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A).comap
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom.hom
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom).2

/-- Membership in the defining ideal over `A` is membership of the transported element in the
base-changed integral defining ideal. -/
@[simp]
theorem mem_kostantToralSubsystemBaseChangePresentationIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A n} :
    x ∈ kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv.hom x ∈
        kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A :=
  HopfIdeal.mem_comap

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the defining ideal over `A`. -/
theorem map_tmul_mem_kostantToralSubsystemBaseChangePresentationIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ n}
    (hy : y ∈ kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).hom.hom (s ⊗ₜ[ℤ] y) ∈
      kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A := by
  rw [mem_kostantToralSubsystemBaseChangePresentationIdeal_iff,
    CommHopfAlgCat.inv_hom_apply, kostantToralSubsystemBaseChangeIdeal_def]
  exact CommHopfAlgCat.tmul_mem_baseChangeHopfIdeal s hy

/-- Transporting the presentation from the scalar extension of `O(GLₙ/ℤ)` to `O(GLₙ/A)` gives
isomorphic quotient Hopf algebras. -/
private noncomputable def kostantToralSubsystemBaseChangePresentationQuotientIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≅
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) :=
  CommHopfAlgCat.quotientIsoOfIso
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A)

@[simp]
private theorem mkQuotient_comp_kostantToralSubsystemBaseChangePresentationQuotientIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≫
        (kostantToralSubsystemBaseChangePresentationQuotientIso
          e h ρ M hM b wt S hnil A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) :=
  CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A)

/-- The toral carrier presented inside `GLₙ` over `A` is the base change of the toral-subsystem
carrier over `ℤ`. -/
noncomputable def kostantToralSubsystemBaseChangePresentationIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) :=
  kostantToralSubsystemBaseChangePresentationQuotientIso e h ρ M hM b wt S hnil A ≪≫
    kostantToralSubsystemBaseChangeIso e h ρ M hM b wt S hnil A

/-- The base-change identification of the toral-subsystem carrier is compatible with the quotient
maps. -/
@[simp]
theorem mkQuotient_comp_kostantToralSubsystemBaseChangePresentationIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≫
        (kostantToralSubsystemBaseChangePresentationIso e h ρ M hM b wt S hnil A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
            (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) := by
  rw [kostantToralSubsystemBaseChangePresentationIso, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangePresentationQuotientIso_hom, Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangeIso_hom]

/-- The transported base change of the `i`th root-subgroup coordinate map, factored through the
transported toral carrier. -/
noncomputable def kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap (i : S) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  (kostantToralSubsystemBaseChangePresentationQuotientIso e h ρ M hM b wt S hnil A).hom ≫
    kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap e h ρ M hM b wt S hnil A i ≫
    (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom

/-- The factored root-subgroup map recovers the transported base change of the `i`th integral
root-subgroup coordinate map. -/
@[simp]
theorem mkQuotient_comp_kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap
    (i : S) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≫
        kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap
          e h ρ M hM b wt S hnil A i =
      kostantRootSubgroupBaseChangePresentationCoordinateMap e h ρ M hM i.1
        (hnil i.1 i.2) b A := by
  rw [kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangePresentationQuotientIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap,
    kostantRootSubgroupBaseChangePresentationCoordinateMap]

/-- The transported base change of the weight-torus coordinate map, factored through the
transported toral carrier. -/
noncomputable def kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj :=
  (kostantToralSubsystemBaseChangePresentationQuotientIso e h ρ M hM b wt S hnil A).hom ≫
    kostantWeightTorusToralSubsystemBaseChangeCoordinateMap e h ρ M hM b wt S hnil A ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso ℤ A
      (SplitTorus.characterGroup κ)).hom

/-- The factored weight-torus map recovers `GeneralLinear.weightTorusBaseChangeCoordinateMap`. -/
@[simp]
theorem mkQuotient_comp_kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A) ≫
        kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap
          e h ρ M hM b wt S hnil A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A wt := by
  rw [kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangePresentationQuotientIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantWeightTorusToralSubsystemBaseChangeCoordinateMap,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_def]

/-- Every transported root-subgroup map kills the defining ideal over `A`. -/
theorem kostantToralSubsystemBaseChangePresentationIdeal_toIdeal_le_root_ker (i : S) :
    (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A).toIdeal ≤
      RingHom.ker
        (kostantRootSubgroupBaseChangePresentationCoordinateMap
          e h ρ M hM i.1 (hnil i.1 i.2) b A).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
    (mkQuotient_comp_kostantRootSubgroupToralSubsystemBaseChangePresentationCoordinateMap
      e h ρ M hM b wt S hnil A i)

/-- The transported weight-torus map kills the defining ideal over `A`. -/
theorem kostantToralSubsystemBaseChangePresentationIdeal_toIdeal_le_torus_ker :
    (kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A).toIdeal ≤
      RingHom.ker
        (GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A
          wt).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
    (mkQuotient_comp_kostantWeightTorusToralSubsystemBaseChangePresentationCoordinateMap
      e h ρ M hM b wt S hnil A)

/-- The closed subgroup of `GLₙ/A` generated by the transported root subgroups and split torus
lies in the transported base change of the integral toral-subsystem carrier.

The reverse inclusion is deliberately not claimed: a Hopf ideal killed by all generators after
base change need not descend to an integral Hopf ideal. -/
theorem kostantToralSubsystemBaseChangePresentationIdeal_le_commonKernelHopfIdeal :
    let K : Sum S Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ => (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj
    kostantToralSubsystemBaseChangePresentationIdeal e h ρ M hM b wt S hnil A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | Sum.inl i => kostantRootSubgroupBaseChangePresentationCoordinateMap
              e h ρ M hM i.1 (hnil i.1 i.2) b A
          | Sum.inr _ => GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A wt) := by
  dsimp only
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (i | _)
  · exact kostantToralSubsystemBaseChangePresentationIdeal_toIdeal_le_root_ker
      e h ρ M hM b wt S hnil A i
  · exact kostantToralSubsystemBaseChangePresentationIdeal_toIdeal_le_torus_ker
      e h ρ M hM b wt S hnil A

end TauCeti.UniversalEnvelopingAlgebra
