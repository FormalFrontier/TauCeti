/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.BaseChange

/-!
# The base-changed toral Kostant closure inside the general linear group

The toral Kostant closure over `ℤ` is the closed subgroup scheme of `GLₙ` generated jointly by
represented root subgroups and a represented split torus. Base change first presents it inside
the scalar extension `A ⊗[ℤ] O(GLₙ/ℤ)`. This file transports that presentation across the
canonical Hopf-algebra isomorphism

```text
A ⊗[ℤ] O(GLₙ/ℤ) ≅ O(GLₙ/A),
```

so the carrier is cut out directly inside `GLₙ` over `A`. The root-subgroup parameter algebra and
the split-torus coordinate algebra are transported at the same time. Consequently the factored
maps have target `O(𝔾ₐ/A)` and `O(T/A)`, rather than scalar extensions of the corresponding
coordinate algebras over `ℤ`. The `Presentation` in the names records exactly this: these objects
live in the coordinate algebras built directly over `A`, whereas the `kostantToralBaseChange*`
family of `ToralClosure/BaseChange.lean` lives in the scalar extensions of the integral ones.

Everything here is a transport of the integral data, not a fresh construction over `A`. The
underlying bialgebra morphism of the transported split-torus map is identified with
`GeneralLinear.weightTorusCoordinateBialgHom`, constructed directly over `A`; this formulation
also covers value rings in a larger universe than the integral torus index. On the root-subgroup
side no over-`A` construction exists yet.

The transported ideal need not be the largest Hopf ideal killed by the root subgroups and torus
after base change: new equations may appear over a non-flat base. The proved comparison therefore
has the honest direction only. The closed subgroup generated over `A` by the transported root and
torus maps lies in the base change of the integral toral carrier; equality is not asserted.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangePresentationIdeal`: the transported
  defining ideal in `O(GLₙ/A)`.
* `kostantToralBaseChangePresentationIso`: its quotient is the base change of the integral toral
  coordinate ring.
* `kostantRootSubgroupBaseChangePresentationCoordinateMap` and
  `kostantRootSubgroupToralBaseChangePresentationCoordinateMap`: the transported base change of a
  root subgroup and its factorization through the transported toral carrier.
* `kostantWeightTorusToralBaseChangePresentationCoordinateMap`: the factorization of the
  transported weight-torus coordinate map through the transported carrier.
* `kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal`: the generated-over-`A`
  carrier is a closed subgroup of the transported integral carrier.
* `kostantToralBaseChangePresentationIsoOfEq`,
  `kostantRootSubgroupToralCoordinateMapOfEq` and `kostantWeightTorusToralCoordinateMapOfEq`:
  the same identification and integral generator maps, read through a named spelling `J` of the
  integral defining ideal. A carrier that names its own defining ideal specializes these rather
  than replaying the equality transport.
* `hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op` and
  `hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op`: those integral generator maps
  represent the carrier's root-subgroup and weight-torus morphisms.

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
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (A : Type*) [CommRing A]

/-- The Hopf ideal of `O(GLₙ/A)` presenting the base change of the toral Kostant closure: the
inverse image of the base-changed defining ideal under the general-linear coordinate
base-change isomorphism. -/
noncomputable def kostantToralBaseChangePresentationIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A n) :=
  (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A).comapOfSurjective
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom.hom
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm.hom).2

/-- Membership in the defining ideal over `A` is membership of the transported element in the
base-changed integral defining ideal. -/
@[simp]
theorem mem_kostantToralBaseChangePresentationIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A n} :
    x ∈ kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv.hom x ∈
        kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A :=
  HopfIdeal.mem_comapOfSurjective

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the defining ideal over `A`. -/
theorem map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ n}
    (hy : y ∈ kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).hom.hom (s ⊗ₜ[ℤ] y) ∈
      kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A := by
  rw [mem_kostantToralBaseChangePresentationIdeal_iff,
    CommHopfAlgCat.inv_hom_apply, kostantToralBaseChangeIdeal_def]
  exact CommHopfAlgCat.tmul_mem_baseChangeHopfIdeal s hy

/-- Transporting the presentation from the scalar extension of `O(GLₙ/ℤ)` to `O(GLₙ/A)` gives
isomorphic quotient Hopf algebras. -/
private noncomputable def kostantToralBaseChangePresentationQuotientIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≅
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  CommHopfAlgCat.quotientIsoOfIso
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

@[simp]
private theorem mkQuotient_comp_kostantToralBaseChangePresentationQuotientIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≫
        (kostantToralBaseChangePresentationQuotientIso
          e h ρ M hM hnil b wt A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A) :=
  CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).symm
    (kostantToralBaseChangeIdeal e h ρ M hM hnil b wt A)

/-- The toral carrier presented inside `GLₙ` over `A` is the base change of the toral carrier
over `ℤ`. -/
noncomputable def kostantToralBaseChangePresentationIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) :=
  kostantToralBaseChangePresentationQuotientIso e h ρ M hM hnil b wt A ≪≫
    kostantToralBaseChangeIso e h ρ M hM hnil b wt A

/-- The base-change identification of the toral carrier is compatible with the quotient maps. -/
@[simp]
theorem mkQuotient_comp_kostantToralBaseChangePresentationIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≫
        (kostantToralBaseChangePresentationIso e h ρ M hM hnil b wt A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
            (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) := by
  rw [kostantToralBaseChangePresentationIso, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_kostantToralBaseChangePresentationQuotientIso_hom, Category.assoc,
    mkQuotient_comp_kostantToralBaseChangeIso_hom]

/-- The base change of the `i`th integral root-subgroup coordinate map, transported into the
coordinate Hopf algebras built directly over `A`. -/
noncomputable def kostantRootSubgroupBaseChangePresentationCoordinateMap (i : I) :
    GeneralLinear.coordinateHopfAlgebra A n ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
    CommHopfAlgCat.baseChangeMap
      (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
    (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom

omit [Finite κ] in
/-- The transported base-changed root-subgroup map is the stated composite of the two coordinate
base-change isomorphisms with the scalar extension of the map over `ℤ`. -/
theorem kostantRootSubgroupBaseChangePresentationCoordinateMap_def (i : I) :
    kostantRootSubgroupBaseChangePresentationCoordinateMap e h ρ M hM hnil b A i =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b) ≫
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom := by
  unfold kostantRootSubgroupBaseChangePresentationCoordinateMap
  rfl

/-- The transported base change of the `i`th root-subgroup coordinate map, factored through the
transported toral carrier. -/
noncomputable def kostantRootSubgroupToralBaseChangePresentationCoordinateMap (i : I) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  (kostantToralBaseChangePresentationQuotientIso e h ρ M hM hnil b wt A).hom ≫
    kostantRootSubgroupToralBaseChangeCoordinateMap e h ρ M hM hnil b wt A i ≫
    (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom

/-- The factored root-subgroup map recovers the transported base change of the `i`th integral
root-subgroup coordinate map. -/
@[simp]
theorem mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap (i : I) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≫
        kostantRootSubgroupToralBaseChangePresentationCoordinateMap
          e h ρ M hM hnil b wt A i =
      kostantRootSubgroupBaseChangePresentationCoordinateMap e h ρ M hM hnil b A i := by
  rw [kostantRootSubgroupToralBaseChangePresentationCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralBaseChangePresentationQuotientIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantRootSubgroupToralBaseChangeCoordinateMap,
    kostantRootSubgroupBaseChangePresentationCoordinateMap]

/-- The transported base change of the weight-torus coordinate map, factored through the
transported toral carrier. -/
noncomputable def kostantWeightTorusToralBaseChangePresentationCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ⟶
      (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj :=
  (kostantToralBaseChangePresentationQuotientIso e h ρ M hM hnil b wt A).hom ≫
    kostantWeightTorusToralBaseChangeCoordinateMap e h ρ M hM hnil b wt A ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso ℤ A
      (SplitTorus.characterGroup κ)).hom

/-- The factored weight-torus map recovers `GeneralLinear.weightTorusBaseChangeCoordinateMap`. -/
@[simp]
theorem mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≫
        kostantWeightTorusToralBaseChangePresentationCoordinateMap e h ρ M hM hnil b wt A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A wt := by
  rw [kostantWeightTorusToralBaseChangePresentationCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralBaseChangePresentationQuotientIso_hom, Category.assoc,
    ← Category.assoc (CommHopfAlgCat.mkQuotient _ _),
    mkQuotient_comp_kostantWeightTorusToralBaseChangeCoordinateMap,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_def]

/-- Every transported root-subgroup map kills the defining ideal over `A`. -/
theorem kostantToralBaseChangePresentationIdeal_toIdeal_le_root_ker (i : I) :
    (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A).toIdeal ≤
      RingHom.ker
        (kostantRootSubgroupBaseChangePresentationCoordinateMap
          e h ρ M hM hnil b A i).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
    (mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
      e h ρ M hM hnil b wt A i)

/-- The transported weight-torus map kills the defining ideal over `A`. -/
theorem kostantToralBaseChangePresentationIdeal_toIdeal_le_torus_ker :
    (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A).toIdeal ≤
      RingHom.ker
        (GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A
          wt).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp
    (mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
      e h ρ M hM hnil b wt A)

/-- The closed subgroup of `GLₙ/A` generated by the transported root subgroups and split torus
lies in the transported base change of the integral toral carrier.

The reverse inclusion is deliberately not claimed: a Hopf ideal killed by all generators after
base change need not descend to an integral Hopf ideal. -/
theorem kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal :
    let K : Sum I Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ => (DiagonalizableGroup.coordinateRing A (SplitTorus.characterGroup κ)).obj
    kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | Sum.inl i => kostantRootSubgroupBaseChangePresentationCoordinateMap
              e h ρ M hM hnil b A i
          | Sum.inr _ => GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A wt) := by
  dsimp only
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (i | _)
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_root_ker
      e h ρ M hM hnil b wt A i
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_torus_ker
      e h ρ M hM hnil b wt A

/-! ## Transport along a named spelling of the integral defining ideal

A carrier constructed as a toral Kostant closure names its own integral defining ideal `J` and
records the equality `J = kostantToralDefiningIdeal e h ρ M hM hnil b wt`. The declarations below
re-express the base-change presentation and the two integral generator maps in terms of `J`, so a
specialization does not replay the equality transport itself. -/

variable {J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n)}

/-- The base-change identification of the toral carrier, with the integral quotient expressed
using a named spelling `J` of the defining ideal. -/
noncomputable def kostantToralBaseChangePresentationIsoOfEq
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A n)
        (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J) :=
  kostantToralBaseChangePresentationIso e h ρ M hM hnil b wt A ≪≫
    (CommHopfAlgCat.baseChangeFunctor (K := A)).mapIso
      (eqToIso (congrArg
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)) hJ.symm))

/-- The transported identification is compatible with the quotient maps. -/
@[simp]
theorem mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
          (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A) ≫
        (kostantToralBaseChangePresentationIsoOfEq e h ρ M hM hnil b wt A hJ).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J) := by
  rw [kostantToralBaseChangePresentationIsoOfEq, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_kostantToralBaseChangePresentationIso_hom, Category.assoc,
    Functor.mapIso_hom, eqToIso.hom, ← CommHopfAlgCat.baseChangeFunctor_map,
    ← Functor.map_comp, CommHopfAlgCat.mkQuotient_comp_eqToHom hJ]

/-- The integral `i`th root-subgroup coordinate map, with source expressed using a named spelling
`J` of the defining ideal. -/
noncomputable def kostantRootSubgroupToralCoordinateMapOfEq
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) (i : I) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  eqToHom (congrArg (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)) hJ) ≫
    kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i

/-- The transported factored root-subgroup map recovers the represented root-subgroup coordinate
map. -/
@[simp]
theorem mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) (i : I) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J ≫
        kostantRootSubgroupToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ i =
      kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b := by
  rw [kostantRootSubgroupToralCoordinateMapOfEq, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_eqToHom hJ.symm,
    mkQuotient_comp_kostantRootSubgroupToralCoordinateMap]

/-- The integral weight-torus coordinate map, with source expressed using a named spelling `J` of
the defining ideal. -/
noncomputable def kostantWeightTorusToralCoordinateMapOfEq
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J ⟶
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj :=
  eqToHom (congrArg (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)) hJ) ≫
    kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt

/-- The transported factored weight-torus map recovers the weight-torus coordinate map. -/
@[simp]
theorem mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J ≫
        kostantWeightTorusToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ =
      GeneralLinear.weightTorusCoordinateMap wt := by
  rw [kostantWeightTorusToralCoordinateMapOfEq, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_eqToHom hJ.symm,
    mkQuotient_comp_kostantWeightTorusToralCoordinateMap]

/-- The spectrum of the integral factored `i`th root-subgroup coordinate map is the represented
root-subgroup morphism into the toral carrier, transported to the named spelling `J`. -/
-- Not a `simp` lemma: `simp` rewrites `hopfSpec` to `algSpec.mapGrp` composed with the
-- Hopf-algebra/cogroup equivalence, so no equation whose sides mention `hopfSpec.map` has a
-- left-hand side in `simp` normal form. The sibling `kostantRootSubgroupToToral_def` is stated
-- without the attribute for the same reason.
theorem hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) (i : I) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (kostantRootSubgroupToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ i).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        kostantRootSubgroupToToral e h ρ M hM hnil b wt i ≫
          eqToHom (congrArg
            (CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra ℤ n)) hJ.symm) := by
  subst hJ
  simp [kostantRootSubgroupToralCoordinateMapOfEq, kostantRootSubgroupToToral_def]

/-- The spectrum of the integral factored weight-torus coordinate map is the represented
weight-torus morphism into the toral carrier, transported to the named spelling `J`. -/
theorem hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (kostantWeightTorusToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ).op =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup κ)).symm ≫
        kostantWeightTorusToToral e h ρ M hM hnil b wt ≫
          eqToHom (congrArg
            (CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra ℤ n)) hJ.symm) := by
  subst hJ
  simp [kostantWeightTorusToralCoordinateMapOfEq, kostantWeightTorusToToral_def]

/-- Under the transported identification, the factored `i`th root-subgroup map over `A` is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem kostantToralBaseChangePresentationIsoOfEq_hom_comp_rootSubgroupBaseChangeMap
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) (i : I) :
    (kostantToralBaseChangePresentationIsoOfEq e h ρ M hM hnil b wt A hJ).hom ≫
          CommHopfAlgCat.baseChangeMap
            (kostantRootSubgroupToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ i) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      kostantRootSubgroupToralBaseChangePresentationCoordinateMap e h ρ M hM hnil b wt A i := by
  let _ : Epi (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
      (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
    (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A))).1
  rw [← Category.assoc, mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J)),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq,
    CommHopfAlgCat.baseChangeFunctor_map,
    mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap]
  simpa only [_root_.CommHopfAlgCat.isoMk_hom] using
    (kostantRootSubgroupBaseChangePresentationCoordinateMap_def e h ρ M hM hnil b A i).symm

/-- Under the transported identification, the factored weight-torus map over `A` is the scalar
extension of its integral coordinate map. -/
-- The bialgebra equivalence is coerced by name: writing `↑` leaves the source of the coercion a
-- metavariable, and the coordinate ring of the character group only matches the monoid algebra
-- the equivalence is stated for after unfolding, which the coercion elaborator does not do.
@[simp]
theorem kostantToralBaseChangePresentationIsoOfEq_hom_comp_weightTorusBaseChangeMap
    (hJ : J = kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    (kostantToralBaseChangePresentationIsoOfEq e h ρ M hM hnil b wt A hJ).hom ≫
          CommHopfAlgCat.baseChangeMap
            (kostantWeightTorusToralCoordinateMapOfEq e h ρ M hM hnil b wt hJ) ≫
        (_root_.CommHopfAlgCat.ofHom
          (BialgHomClass.toBialgHom
            (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
              (G := SplitTorus.characterGroup κ)))) =
      kostantWeightTorusToralBaseChangePresentationCoordinateMap e h ρ M hM hnil b wt A := by
  let _ : Epi (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
      (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A n)
    (kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A))).1
  rw [← Category.assoc, mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n) J)),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq,
    CommHopfAlgCat.baseChangeFunctor_map,
    mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap]
  simpa only [Functor.mapIso_hom, ObjectProperty.isoMk_hom, _root_.CommHopfAlgCat.isoMk_hom,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom] using
    (GeneralLinear.weightTorusBaseChangeCoordinateMap_def ℤ A wt).symm

end TauCeti.UniversalEnvelopingAlgebra
