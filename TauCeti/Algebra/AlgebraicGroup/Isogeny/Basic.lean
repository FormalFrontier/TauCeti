/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FaithfullyFlatPoints
public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Coordinate

/-!
# Isogenies of affine group schemes

A morphism `f : H ⟶ K` of commutative Hopf algebras represents, contravariantly, a
morphism `Spec K ⟶ Spec H` of affine group schemes. We call this morphism an isogeny when
its coordinate map is finite and faithfully flat. These two conditions respectively say that
the group-scheme morphism is finite and faithfully flat (hence fpqc-surjective). A central
isogeny is an isogeny whose scheme-theoretic kernel is central.

The definitions are stated over an arbitrary commutative base ring. Over a field, for affine
algebraic groups of finite type, this is the coordinate-algebra form of the usual finite
surjective group morphism. Keeping faithful flatness explicit avoids replacing scheme-theoretic
surjectivity by a weaker statement about points over the base field.

## Main declarations

* `TauCeti.CommHopfAlgCat.IsIsogeny`: a finite faithfully flat coordinate morphism.
* `TauCeti.CommHopfAlgCat.IsCentralIsogeny`: an isogeny with central kernel Hopf ideal.
* `TauCeti.CommHopfAlgCat.isIsogeny_iff_isIsogeny_hopfSpec_map`: the coordinate and
  group-scheme definitions agree over a commutative ring.
* `TauCeti.CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map`: the analogous
  bridge for central isogenies.
* `TauCeti.CommHopfAlgCat.IsIsogeny.mapPointsFunctor_app_surjective`: an isogeny is
  surjective on points over algebraically closed fields.
* `TauCeti.CommHopfAlgCat.IsIsogeny.isIso_iff_surjective`: an isogeny is an isomorphism
  exactly when its coordinate map is surjective.
* `TauCeti.CommHopfAlgCat.isCentralIsogeny_of_isIso`: every isomorphism is a central
  isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 2.20 and §23.

The isogeny and central-kernel interfaces and their proof organization are adapted from the prior
formalizations in `TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic` and
`TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Coordinate`.

This supplies the central-isogeny interface requested in Layer 6, "Reductive and semisimple
groups", of `TauCetiRoadmap/ReductiveGroups/README.md`. It builds on the existing
scheme-theoretic kernel and central Hopf-ideal APIs.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]
variable {H K L : _root_.CommHopfAlgCat.{v} R}

/-- A morphism of affine group schemes is an **isogeny** when its coordinate morphism is
finite and faithfully flat.

For `f : H ⟶ K`, this predicate concerns the contravariant group-scheme morphism
`Spec K ⟶ Spec H`. Finiteness is therefore finiteness of `K` as an `H`-module through
`f`, while faithful flatness is the scheme-theoretic surjectivity condition. -/
def IsIsogeny (f : H ⟶ K) : Prop :=
  f.hom.toAlgHom.Finite ∧ f.hom.toAlgHom.toRingHom.FaithfullyFlat

/-- A **central isogeny** is an isogeny whose scheme-theoretic kernel is central. The kernel
is represented by the quotient of `K` by `kernelHopfIdeal f`, so centrality is imposed on
that Hopf ideal. -/
def IsCentralIsogeny (f : H ⟶ K) : Prop :=
  IsIsogeny f ∧ (kernelHopfIdeal f).IsCentral

/-- Restatement of the coordinate-algebra conditions defining a central isogeny. -/
theorem isCentralIsogeny_iff (f : H ⟶ K) :
    IsCentralIsogeny f ↔
      f.hom.toAlgHom.Finite ∧ f.hom.toAlgHom.toRingHom.FaithfullyFlat ∧
        (kernelHopfIdeal f).IsCentral := by
  rw [IsCentralIsogeny, IsIsogeny, and_assoc]

-- This isolates the definitional computation of Mathlib's bundled `hopfSpec` functor at the
-- morphism-property boundary where the source and target schemes are propositionally aligned.
private lemma isogeny_conditions_hopfSpec_map_iff
    {H₀ K₀ : _root_.CommHopfAlgCat.{u} R} (f : H₀ ⟶ K₀) :
    f.hom.toAlgHom.Finite ∧ f.hom.toAlgHom.toRingHom.FaithfullyFlat ↔
      AlgebraicGeometry.IsFinite
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op).hom.hom.left ∧
        AlgebraicGeometry.Flat
            ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op).hom.hom.left ∧
          AlgebraicGeometry.Surjective
            ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map f.op).hom.hom.left := by
  change f.hom.toAlgHom.Finite ∧ f.hom.toAlgHom.toRingHom.FaithfullyFlat ↔
    AlgebraicGeometry.IsFinite
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ∧
    AlgebraicGeometry.Flat
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ∧
    AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
  rw [AlgebraicGeometry.IsFinite.SpecMap_iff,
    AlgebraicGeometry.flat_and_surjective_SpecMap_iff]
  rfl

section Ring

variable {k : Type u} [CommRing k] {H₀ K₀ : _root_.CommHopfAlgCat.{u} k}

/-- The coordinate-algebra definition of an isogeny agrees with the group-scheme definition
after applying the contravariant Hopf spectrum functor. -/
theorem isIsogeny_iff_isIsogeny_hopfSpec_map (f : H₀ ⟶ K₀) :
    IsIsogeny f ↔
      GroupScheme.IsIsogeny
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map f.op) := by
  rw [IsIsogeny, GroupScheme.isIsogeny_iff]
  exact isogeny_conditions_hopfSpec_map_iff f

/-- The coordinate-algebra definition of a central isogeny agrees with the group-scheme
definition after applying the contravariant Hopf spectrum functor. -/
theorem isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map (f : H₀ ⟶ K₀) :
    IsCentralIsogeny f ↔
      GroupScheme.IsCentralIsogeny
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map f.op) := by
  rw [IsCentralIsogeny, GroupScheme.isCentralIsogeny_hopfSpec_map_iff,
    isIsogeny_iff_isIsogeny_hopfSpec_map]

end Ring

namespace IsIsogeny

variable {f : H ⟶ K}

/-- The coordinate algebra of the source of an isogeny is finite over that of the target. -/
theorem finite (hf : IsIsogeny f) : f.hom.toAlgHom.Finite :=
  hf.1

/-- The coordinate map of an isogeny is faithfully flat. -/
theorem faithfullyFlat (hf : IsIsogeny f) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat :=
  hf.2

/-- The coordinate map of an isogeny is injective. -/
theorem injective (hf : IsIsogeny f) : Function.Injective f.hom :=
  hf.faithfullyFlat.injective

/-- An isogeny is an isomorphism exactly when its coordinate map is surjective. -/
theorem isIso_iff_surjective (hf : IsIsogeny f) :
    IsIso f ↔ Function.Surjective f.hom := by
  constructor
  · intro
    exact (ConcreteCategory.bijective_of_isIso f).2
  · intro hsurjective
    let hbijective : Function.Bijective f.hom := ⟨hf.injective, hsurjective⟩
    let e := BialgEquiv.ofBijective f.hom hbijective
    have he : (CommHopfAlgCat.isoMk e).hom = f := by
      rw [CommHopfAlgCat.isoMk_hom]
      apply CommHopfAlgCat.hom_ext
      apply BialgHom.ext
      intro x
      exact congrFun (BialgEquiv.coe_ofBijective f.hom hbijective) x
    rw [← he]
    infer_instance

/-- A finite coordinate morphism is in particular of finite type. -/
theorem finiteType (hf : IsIsogeny f) : f.hom.toAlgHom.FiniteType :=
  hf.finite.finiteType

/-- A composite of isogenies is an isogeny. -/
theorem comp {f : H ⟶ K} {g : K ⟶ L} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) := by
  rw [IsIsogeny, _root_.CommHopfAlgCat.hom_comp]
  exact ⟨AlgHom.Finite.comp hg.finite hf.finite,
    RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.faithfullyFlat
      hg.faithfullyFlat⟩

end IsIsogeny

namespace IsCentralIsogeny

variable {f : H ⟶ K}

/-- Forgetting centrality from a central isogeny gives an isogeny. -/
theorem isIsogeny (hf : IsCentralIsogeny f) : IsIsogeny f :=
  hf.1

/-- The kernel Hopf ideal of a central isogeny is central. -/
theorem isCentral_kernelHopfIdeal (hf : IsCentralIsogeny f) :
    (kernelHopfIdeal f).IsCentral :=
  hf.2

/-- The kernel Hopf ideal of a central isogeny is normal. -/
theorem isNormal_kernelHopfIdeal (hf : IsCentralIsogeny f) :
    (kernelHopfIdeal f).IsNormal :=
  hf.isCentral_kernelHopfIdeal.isNormal

/-- The coordinate ring of the kernel of a central isogeny is cocommutative. Equivalently,
the kernel group scheme is commutative. -/
theorem isCocomm_quotient_kernelHopfIdeal (hf : IsCentralIsogeny f) :
    _root_.Coalgebra.IsCocomm R (quotient K (kernelHopfIdeal f)) :=
  hf.isCentral_kernelHopfIdeal.isCocomm_quotient

/-- A central isogeny is finite on coordinate algebras. -/
theorem finite (hf : IsCentralIsogeny f) : f.hom.toAlgHom.Finite :=
  hf.isIsogeny.finite

/-- A central isogeny is faithfully flat on coordinate algebras. -/
theorem faithfullyFlat (hf : IsCentralIsogeny f) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat :=
  hf.isIsogeny.faithfullyFlat

/-- The coordinate map of a central isogeny is injective. -/
theorem injective (hf : IsCentralIsogeny f) : Function.Injective f.hom :=
  hf.isIsogeny.injective

end IsCentralIsogeny

/-- The identity morphism is an isogeny. -/
@[simp]
theorem isIsogeny_id (H : _root_.CommHopfAlgCat.{v} R) : IsIsogeny (𝟙 H) := by
  rw [IsIsogeny, _root_.CommHopfAlgCat.hom_id]
  exact ⟨AlgHom.Finite.id R H, Module.FaithfullyFlat.self H⟩

/-- A bijective coordinate morphism is an isogeny. -/
theorem isIsogeny_of_bijective (f : H ⟶ K) (hf : Function.Bijective f.hom) :
    IsIsogeny f :=
  ⟨AlgHom.Finite.of_surjective f.hom.toAlgHom hf.2,
    RingHom.FaithfullyFlat.of_bijective hf⟩

/-- A bijective coordinate morphism is a central isogeny. Its kernel Hopf ideal is the
augmentation ideal, hence cuts out the trivial central subgroup. -/
theorem isCentralIsogeny_of_bijective (f : H ⟶ K) (hf : Function.Bijective f.hom) :
    IsCentralIsogeny f := by
  refine ⟨isIsogeny_of_bijective f hf, ?_⟩
  rw [kernelHopfIdeal_eq_augmentation_of_surjective f hf.2]
  exact isCentral_augmentation K

-- These lemmas isolate the definitional identification of `unitBialgHom` with `algebraMap`.
private lemma unitBialgHom_finite (K : _root_.CommHopfAlgCat.{u} R) [Module.Finite R K] :
    (Bialgebra.unitBialgHom R K).toAlgHom.Finite := by
  change (algebraMap R K).Finite
  exact RingHom.finite_algebraMap.mpr inferInstance

private lemma unitBialgHom_faithfullyFlat (K : _root_.CommHopfAlgCat.{u} R)
    [Module.FaithfullyFlat R K] :
    (Bialgebra.unitBialgHom R K).toAlgHom.toRingHom.FaithfullyFlat := by
  change (algebraMap R K).FaithfullyFlat
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- The structure morphism from a finite faithfully flat commutative affine group scheme to the
trivial group is a central isogeny. Its kernel is the whole source group, so nontrivial choices of
`K` give central isogenies with nontrivial kernel. -/
theorem isCentralIsogeny_unit_of_isCocomm (K : _root_.CommHopfAlgCat.{u} R)
    [Module.Finite R K] [Module.FaithfullyFlat R K] [Coalgebra.IsCocomm R K] :
    IsCentralIsogeny
      (CommHopfAlgCat.ofHom (Bialgebra.unitBialgHom R K)) := by
  exact ⟨⟨unitBialgHom_finite K, unitBialgHom_faithfullyFlat K⟩,
    (HopfIdeal.isCentral_bot_iff_isCocomm.mpr inferInstance).mono bot_le⟩

/-- Every categorical isomorphism of commutative Hopf algebras is an isogeny. -/
theorem isIsogeny_of_isIso (f : H ⟶ K) [IsIso f] : IsIsogeny f :=
  isIsogeny_of_bijective f (ConcreteCategory.bijective_of_isIso f)

/-- Every categorical isomorphism of commutative Hopf algebras is a central isogeny. -/
theorem isCentralIsogeny_of_isIso (f : H ⟶ K) [IsIso f] : IsCentralIsogeny f :=
  isCentralIsogeny_of_bijective f (ConcreteCategory.bijective_of_isIso f)

/-- The identity morphism is a central isogeny. -/
@[simp]
theorem isCentralIsogeny_id (H : _root_.CommHopfAlgCat.{v} R) :
    IsCentralIsogeny (𝟙 H) :=
  isCentralIsogeny_of_isIso (𝟙 H)

/-- An isogeny is surjective on points valued in an algebraically closed field. -/
theorem IsIsogeny.mapPointsFunctor_app_surjective (hf : IsIsogeny f)
    (F : Type w) [Field F] [Algebra R F] [IsAlgClosed F] :
    Function.Surjective ((mapPointsFunctor f).app (CommAlgCat.of R F)) :=
  mapPointsFunctor_app_surjective_of_faithfullyFlat F f hf.finiteType hf.faithfullyFlat

end TauCeti.CommHopfAlgCat
