/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# The conjugation equations of the Geck carrier, against its named root datum

For a valid Dynkin type `t`, `TauCeti.DynkinType.geckGroupScheme t` is the explicit Kostant
toral-closure carrier built from Geck's integral coordinate lattice. Its split weight torus
conjugates the parameter of the numbered raising subgroup at node `i` through the character
`t.rootGeneratorWeight ht (.inl i)`, which was constructed as a Bourbaki row of `t.cartanMatrix`.
This file restates those conjugation equations with that character read instead as a simple root
of `TauCeti.DynkinType.simplyConnectedRootDatum t`.

The distinction is important to the downstream finite-group construction. Its ambient carrier is
indexed by a Dynkin type and must use the root datum supplied by the root-systems roadmap; equality
with a Cartan-matrix row is not by itself an interface connecting the two constructions. The
substitution itself is `TauCeti.DynkinType.rootGeneratorWeight_inl_eq_root_simpleIndex` and its
lowering counterpart, proved with the Kostant form in
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/KostantForm.lean`; the results below are
the carrier's conjugation equations that consume it.

The existing Geck lattice has full character lattice exactly in types `E₈`, `F₄`, and `G₂`.
Thus the equations below supply this named-root form of the pinning interface for those three
carriers. They are stated uniformly because the conjugation equations are valid for every Dynkin
type, including the other types whose full-weight admissible lattices remain to be constructed.
Each equation says only how the torus rescales a subgroup parameter: nothing here asserts
reductivity, maximality of the torus, or that these numbered subgroups exhaust the root subgroups
of a root datum carried by the group scheme; those are separate Layer 9 targets.

## Main results

* `TauCeti.DynkinType.geckTorusPoints_conj_geckRootSubgroupParam_root_simpleIndex` and its
  negative-root counterpart: the pointwise conjugation equations, with the conjugating character
  read as a named simple root.
* `TauCeti.DynkinType.geckWeightTorus_conj_geckRootSubgroup_root_simpleIndex` and its
  negative-root counterpart: the corresponding equations on scheme-valued points.
* `TauCeti.DynkinType.geckWeightTorusPoints_conj_geckRootSubgroupPoints_root_simpleIndex` and its
  negative-root counterpart: the corresponding equations inside the matrix point group, where the
  represented torus and the represented root subgroups are group homomorphisms.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--IX.

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone `L0` of
`TauCetiRoadmap/CFSGStatement/README.md`, which requires each Lie-type carrier to be traceable to
`DynkinType.simplyConnectedRootDatum` through `ValidLieTypeIndex.dynkinType`.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

universe v

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! None of the restatements below is a `simp` lemma, at any of the three tiers. Their right-hand
sides are not `simp`-normal: `TauCeti.DynkinType.root_simpleIndex` rewrites a named simple root
back to its Bourbaki row of `t.cartanMatrix`, which is also what
`TauCeti.DynkinType.rootGeneratorWeight_inl` produces from the character on the left. This is the
policy recorded in `TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/KostantForm.lean`
beside the substitution these restatements perform: both forms are already `simp`-normal, so
orienting the identification either way would undo an existing rule. They are stated to be used by
`exact` and `rw`, as `TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` uses them. -/

/-! ## The pointwise conjugation equations -/

/-- **The pointwise conjugation equation of the Geck carrier at a named simple root.** A split-torus
point `s` conjugates the raising-subgroup element of parameter `u` at node `i` into the one of
parameter `α_i(s)u`, where `α_i` is the corresponding simple root of the pinned simply connected
datum. -/
theorem geckTorusPoints_conj_geckRootSubgroupParam_root_simpleIndex (i : Fin t.rank)
    (A : CommAlgCat.{v} ℤ) (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckTorusPoints ht A s * t.geckRootSubgroupParam ht (.inl i) A u *
        (t.geckTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupParam ht (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]
  exact t.geckTorusPoints_conj_geckRootSubgroupParam ht (.inl i) A s u

/-- **The pointwise conjugation equation of the Geck carrier at the negative of a named simple
root.** -/
theorem geckTorusPoints_conj_geckRootSubgroupParam_neg_root_simpleIndex (i : Fin t.rank)
    (A : CommAlgCat.{v} ℤ) (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckTorusPoints ht A s * t.geckRootSubgroupParam ht (.inr i) A u *
        (t.geckTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupParam ht (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← t.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i]
  exact t.geckTorusPoints_conj_geckRootSubgroupParam ht (.inr i) A s u

/-! ## The scheme-level conjugation equations -/

/-- **The scheme-level conjugation equation of the Geck carrier at a named simple root.** -/
theorem geckWeightTorus_conj_geckRootSubgroup_root_simpleIndex (i : Fin t.rank)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin t.rank)).X)
    (u : A) :
    (s ≫ (t.geckWeightTorus ht).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (t.geckRootSubgroup ht (.inl i)).hom.hom) *
        (s ≫ (t.geckWeightTorus ht).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) * u)) ≫
        (t.geckRootSubgroup ht (.inl i)).hom.hom := by
  rw [← t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]
  exact t.geckWeightTorus_conj_geckRootSubgroup ht (.inl i) A s u

/-- **The scheme-level conjugation equation of the Geck carrier at the negative of a named simple
root.** -/
theorem geckWeightTorus_conj_geckRootSubgroup_neg_root_simpleIndex (i : Fin t.rank)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin t.rank)).X)
    (u : A) :
    (s ≫ (t.geckWeightTorus ht).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (t.geckRootSubgroup ht (.inr i)).hom.hom) *
        (s ≫ (t.geckWeightTorus ht).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (-(t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) * u)) ≫
        (t.geckRootSubgroup ht (.inr i)).hom.hom := by
  rw [← t.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i]
  exact t.geckWeightTorus_conj_geckRootSubgroup ht (.inr i) A s u

/-! ## The conjugation equations inside the matrix point group -/

/-- **The pinning equation in the point group of the Geck carrier, at a named simple root.**
Conjugating the numbered raising subgroup at node `i` by a represented weight-torus point rescales
its parameter by `α_i(s)`, where `α_i` is the simple root of the pinned simply connected datum with
the same Bourbaki node number.

This is the form in which a consumer working with the matrix points rather than with the group
scheme uses the pinning: `TauCeti.DynkinType.geckWeightTorusPoints` and
`TauCeti.DynkinType.geckRootSubgroupPoints` are group homomorphisms into
`TauCeti.DynkinType.geckPoints`, so both sides are elements of one group. -/
theorem geckWeightTorusPoints_conj_geckRootSubgroupPoints_root_simpleIndex (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckWeightTorusPoints ht A s * t.geckRootSubgroupPoints ht (.inl i) A u *
        (t.geckWeightTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupPoints ht (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]
  exact t.geckWeightTorusPoints_conj_geckRootSubgroupPoints ht (.inl i) A s u

/-- **The pinning equation in the point group of the Geck carrier, at the negative of a named
simple root.** -/
theorem geckWeightTorusPoints_conj_geckRootSubgroupPoints_neg_root_simpleIndex (i : Fin t.rank)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckWeightTorusPoints ht A s * t.geckRootSubgroupPoints ht (.inr i) A u *
        (t.geckWeightTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupPoints ht (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← t.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i]
  exact t.geckWeightTorusPoints_conj_geckRootSubgroupPoints ht (.inr i) A s u

end

end TauCeti.DynkinType
