/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Basic

/-!
# The Kostant toral-closure group scheme of the pinned Geck lattice

`TauCeti.DynkinType.lieAlgebra` is the split Lie algebra of a valid Dynkin type, realized by Geck's
construction as explicit matrices acting on the coordinate space `GeckIndex → ℚ`, and
`TauCeti.DynkinType.geckCoordinateLattice` is the `ℤ`-lattice of integral coordinate vectors in
that space, preserved by the whole simple-generator Kostant form. This file feeds that pinned data
into the Kostant toral-closure construction and so produces, for every valid Dynkin type, an
explicit affine group scheme over `ℤ`: the smallest closed subgroup scheme of `GLₙ` containing the
divided-power exponential root subgroups of the numbered Chevalley generators together with the
weight torus of the Geck coordinate weights.

The lattice, weights, and nilpotent root vectors are read off the Bourbaki-numbered pinned data, so
the carrier traces back to explicit matrices. The ambient coordinate ordering is the arbitrary
`Fintype.equivFin` reindexing of `GeckIndex`, and hence is pinned only up to that permutation. The
size of the ambient general linear group is
`TauCeti.DynkinType.geckDim_eq_rank_add_numRoots`, namely `rank + numRoots`. In the classical
construction Geck's module is the adjoint module and its weights are the roots, so this carrier is
expected to be the adjoint form; those identifications are not formalized here. The simply
connected carrier required by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` needs instead an admissible lattice whose weights generate
the full weight lattice. That lattice, the Borel, root subgroups for nonsimple roots, the Chevalley
commutator relations, and the root-datum properties that turn a carrier into a pinned split
reductive group scheme are the Layer 9 work that remains; the functoriality of `geckPoints` in the
value ring is supplied by
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor`.

This construction supplies part of the interface that Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md` asks for: the closed immersion into `GLₙ`, the root
subgroup morphisms `x_{±α_i} : 𝔾ₐ → G` of the numbered simple raising and lowering generators
and the weight-torus morphism `T → G` that factor through it, the group of `A`-valued points for
every commutative ring `A`, and the pinning equation
`s x_i(u) s⁻¹ = x_i(α_i(s) u)` expressing the torus action on a root subgroup through the Bourbaki
row of the Cartan matrix. No reductivity, maximality of the torus, finiteness, or root-datum
statement is asserted.

## Main definitions

* `TauCeti.DynkinType.geckDefiningIdeal` and `TauCeti.DynkinType.geckGroupScheme`: the defining
  Hopf ideal and the resulting affine group scheme over `ℤ`.
* `TauCeti.DynkinType.geckGroupSchemeι`: its closed immersion into `GLₙ`.
* `TauCeti.DynkinType.geckRootSubgroup` and `TauCeti.DynkinType.geckWeightTorus`: the root subgroup
  and weight-torus morphisms into the carrier.
* `TauCeti.DynkinType.geckPoints`: the `A`-valued points of the carrier, as matrices.
* `TauCeti.DynkinType.geckRootSubgroupPoints` and
  `TauCeti.DynkinType.geckWeightTorusPoints`: the numbered root subgroups and represented weight
  torus inside the point group.

## Main results

* `TauCeti.DynkinType.geckRootSubgroup_comp_ι` and `TauCeti.DynkinType.geckWeightTorus_comp_ι`:
  both families recover their represented morphisms into `GLₙ`.
* `TauCeti.DynkinType.geckWeightTorus_conj_geckRootSubgroup`: the scheme-level pinning equation.
* `TauCeti.DynkinType.isClosedImmersion_geckWeightTorus` and
  `TauCeti.DynkinType.geckTorusPoints_injective`: weights generating the character lattice embed
  the weight torus in the carrier, on schemes and on points.
* `TauCeti.DynkinType.geckGroupScheme_hom_ext`: morphisms from the carrier into affine group
  schemes represented by commutative Hopf algebras are determined by their composites with the
  root subgroups and weight torus.
* `TauCeti.DynkinType.geckTorusPoints_conj_geckRootSubgroupParam`: the pinning equation, with the
  root of a raising generator the corresponding pinned Cartan-matrix row and that of a lowering
  generator its negative.
* `TauCeti.DynkinType.geckWeightTorusPoints_conj_geckRootSubgroupPoints`: the same pinning equation
  inside the points of the carrier.
* `TauCeti.DynkinType.map_geckElementarySubgroup_conj_geckTorusPoints`: the torus normalizes the
  elementary group.
* `TauCeti.DynkinType.map_geckTorusSubsystemSubgroup_le_geckPoints`: the pointwise group generated
  by the torus and a chosen set of numbered root subgroups lies in the points of the carrier.
* `TauCeti.DynkinType.geckPoints_def`: the points are the matrices cut out by the defining ideal.
* `TauCeti.DynkinType.geckPoints_mk_geckTorusMatrix`: the weight-torus matrix and the diagonal
  matrix of the weight characters are the same point.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This advances "The Chevalley--Demazure construction", "Root subgroup maps" and "Points over an
algebraically closed field" in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose
consumer is the pinned ambient group of milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

universe v

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads them.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-! ## The group scheme -/

/-- **The defining Hopf ideal of the Geck carrier of a valid Dynkin type**: the largest Hopf
ideal of the coordinate algebra of `GLₙ` killed by every numbered Kostant root subgroup and by the
weight torus of the Geck lattice. -/
def geckDefiningIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)

/-- The defining ideal of the Geck carrier is the Kostant toral defining ideal of the pinned
Geck data. -/
theorem geckDefiningIdeal_def :
    t.geckDefiningIdeal ht =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) := (rfl)

/-- **The Kostant toral-closure group scheme of the pinned Geck lattice**: the smallest closed
subgroup scheme of `GLₙ` over `ℤ`, with `n = rank + numRoots`, containing every divided-power
exponential root subgroup of a numbered Chevalley generator and the weight torus of the Geck
coordinates.

Every ingredient is explicit pinned data, so no carrier is chosen from an existence theorem.
Reductivity, and the identification of its root datum, are not claimed. -/
def geckGroupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)

/-- The Geck carrier is the Kostant toral-closure group scheme of the pinned Geck data. -/
theorem geckGroupScheme_def :
    t.geckGroupScheme ht =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) := (rfl)

/-- The Geck carrier is a closed subgroup scheme of `GLₙ`. -/
def geckGroupSchemeι :
    t.geckGroupScheme ht ⟶ GeneralLinear.groupScheme ℤ (t.geckDim ht) :=
  eqToHom (t.geckGroupScheme_def ht) ≫
    TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)

/-- The carrier inclusion is the Kostant toral-closure inclusion for the pinned Geck data. -/
theorem geckGroupSchemeι_def :
    t.geckGroupSchemeι ht =
      eqToHom (t.geckGroupScheme_def ht) ≫
        TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (t.isNilpotent_geckRepresentation_rootGenerator ht)
          (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) := (rfl)

/-- The inclusion of the Geck carrier into `GLₙ` is a closed immersion. -/
instance isClosedImmersion_geckGroupSchemeι :
    IsClosedImmersion (t.geckGroupSchemeι ht).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι _ _ _ _ _ _ _ _

/-- **The `i`-th root subgroup of the Geck carrier**, the divided-power exponential of the
numbered raising or lowering generator, factored through the carrier. -/
def geckRootSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    AdditiveGroup.groupScheme ℤ ⟶ t.geckGroupScheme ht :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i ≫
      eqToHom (t.geckGroupScheme_def ht).symm

/-- A pinned root-subgroup morphism is the corresponding Kostant toral-closure morphism. -/
theorem geckRootSubgroup_def (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckRootSubgroup ht i =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i ≫
          eqToHom (t.geckGroupScheme_def ht).symm := (rfl)

/-- Including a root subgroup of the Geck carrier into `GLₙ` recovers the represented Kostant
root subgroup of the corresponding numbered generator. -/
@[simp]
theorem geckRootSubgroup_comp_ι (i : Fin t.rank ⊕ Fin t.rank) :
    t.geckRootSubgroup ht i ≫ t.geckGroupSchemeι ht =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
        (t.isNilpotent_geckRepresentation_rootGenerator ht i) (t.geckCoordinateBasisFin ht) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι _ _ _ _ _ _ _ _ i

/-- **The represented weight torus of the Geck lattice, factored through the carrier.** This is a
weight-torus morphism into the carrier; it is not asserted to be a monomorphism. -/
def geckWeightTorus :
    SplitTorus.groupScheme ℤ (Fin t.rank) ⟶ t.geckGroupScheme ht :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) ≫
      eqToHom (t.geckGroupScheme_def ht).symm

/-- The pinned weight-torus morphism is the Kostant toral-closure weight-torus morphism. -/
theorem geckWeightTorus_def :
    t.geckWeightTorus ht =
      TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) ≫
          eqToHom (t.geckGroupScheme_def ht).symm := (rfl)

/-- Including the weight-torus morphism into `GLₙ` recovers the diagonal weight torus of the Geck
lattice. -/
@[simp]
theorem geckWeightTorus_comp_ι :
    t.geckWeightTorus ht ≫ t.geckGroupSchemeι ht =
      GeneralLinear.weightTorus (R := ℤ) (t.geckWeightFin ht) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι _ _ _ _ _ _ _ _

/-- **Weights generating the character lattice embed the weight torus as a closed subgroup scheme
of the Geck carrier.** The hypothesis fails in general, since the Geck weights generate only the
root lattice; the types where it holds are settled in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.FullWeight`. -/
theorem isClosedImmersion_geckWeightTorus
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) :
    IsClosedImmersion (t.geckWeightTorus ht).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral
    _ _ _ _ _ _ _ _ hwt

/-- **The intrinsic pinning equation for the Geck carrier.** On points over a commutative ring,
conjugation by a weight-torus point rescales the parameter of a numbered root subgroup by the
corresponding root character. -/
@[simp]
theorem geckWeightTorus_conj_geckRootSubgroup (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin t.rank)).X)
    (u : A) :
    (s ≫ (t.geckWeightTorus ht).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (t.geckRootSubgroup ht i).hom.hom) *
        (s ≫ (t.geckWeightTorus ht).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (t.rootGeneratorWeight ht i) : A) * u)) ≫
        (t.geckRootSubgroup ht i).hom.hom := by
  have h :=
    UniversalEnvelopingAlgebra.kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
        (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
        (t.geckCoordinateLattice ht).toAddSubgroup
        (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
        (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
        (t.isCartanWeightVector_geckCoordinateBasisFin ht)
        (t.isNilpotent_geckRepresentation_rootGenerator ht) A
        (fun j => t.lie_lieBasis_h_rootGenerator ht i j) s u
  have h' := congrArg
    (fun q => q ≫ (eqToHom (t.geckGroupScheme_def ht).symm).hom.hom) h
  simpa only [geckWeightTorus_def, geckRootSubgroup_def, Grp.comp', Mon.comp_hom',
    Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] using h'

/-- **Rigidity of the Geck carrier.** Two homomorphisms from the carrier into an affine group
scheme represented by a commutative Hopf algebra are equal if they agree on every numbered root
subgroup and on the represented weight torus. -/
@[ext]
theorem geckGroupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (φ ψ : t.geckGroupScheme ht ⟶
      (hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ i, t.geckRootSubgroup ht i ≫ φ = t.geckRootSubgroup ht i ≫ ψ)
    (htorus : t.geckWeightTorus ht ≫ φ = t.geckWeightTorus ht ≫ ψ) :
    φ = ψ := by
  apply (cancel_epi (eqToHom (t.geckGroupScheme_def ht).symm)).1
  apply TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (eqToHom (t.geckGroupScheme_def ht).symm ≫ φ)
    (eqToHom (t.geckGroupScheme_def ht).symm ≫ ψ)
  · intro i
    simpa only [geckRootSubgroup_def, Category.assoc] using hroot i
  · simpa only [geckWeightTorus_def, Category.assoc] using htorus

/-! ## Pinned pointwise subgroups -/

/-- The represented Geck weight torus on points of a value algebra. -/
abbrev geckTorusPoints (A : CommAlgCat.{v} ℤ) :
    (Fin t.rank → Aˣ) →* LinearMap.GeneralLinearGroup A
      (A ⊗[ℤ] (t.geckCoordinateLattice ht).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints
    (t.geckCoordinateLattice ht).toAddSubgroup (t.geckCoordinateBasisFin ht)
    (t.geckWeightFin ht) A

/-- **Weights generating the character lattice make the Geck weight torus injective on points**,
over every value algebra. This is the point-level counterpart of
`TauCeti.DynkinType.isClosedImmersion_geckWeightTorus`, proved from the same hypothesis rather
than transported across it: the identification of `Fin t.rank → Aˣ` with the scheme-theoretic
`A`-points of the split torus, and the compatibility of `geckTorusPoints` with `geckWeightTorus`,
are not established here. -/
theorem geckTorusPoints_injective (A : CommAlgCat.{v} ℤ)
    (hwt : Submodule.span ℤ (Set.range (t.geckWeightFin ht)) = ⊤) :
    Function.Injective (t.geckTorusPoints ht A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_injective _ _ _ hwt

/-- The parametrized root subgroup for a numbered Geck root generator. -/
abbrev geckRootSubgroupParam (i : Fin t.rank ⊕ Fin t.rank) (A : CommAlgCat.{v} ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A
      (A ⊗[ℤ] (t.geckCoordinateLattice ht).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
    (t.isNilpotent_geckRepresentation_rootGenerator ht i) A

/-- The elementary subgroup generated by all numbered Geck root subgroups. -/
abbrev geckElementarySubgroup (A : CommAlgCat.{v} ℤ) :
    Subgroup (LinearMap.GeneralLinearGroup A
      (A ⊗[ℤ] (t.geckCoordinateLattice ht).toAddSubgroup)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantElementarySubgroup
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht) A

/-- The subgroup generated by the represented Geck weight torus and a chosen set of numbered root
subgroups. -/
abbrev geckTorusSubsystemSubgroup (S : Set (Fin t.rank ⊕ Fin t.rank))
    (A : CommAlgCat.{v} ℤ) :
    Subgroup (LinearMap.GeneralLinearGroup A
      (A ⊗[ℤ] (t.geckCoordinateLattice ht).toAddSubgroup)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusSubsystemSubgroup
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) S A

/-! ## The pinning equation -/

/-- **The pinning equation for the Geck carrier of a valid Dynkin type.** A torus point `s`
conjugates the root-subgroup element of parameter `u` into the one of parameter `α_i(s) u`, where
`α_i` is the `i`-th Bourbaki row of the Cartan matrix on a raising generator and its negative on a
lowering one.

This is the equation against which the numbered conventions of downstream Steinberg maps are
stated. -/
theorem geckTorusPoints_conj_geckRootSubgroupParam (i : Fin t.rank ⊕ Fin t.rank)
    (A : CommAlgCat.{v} ℤ) (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckTorusPoints ht A s * t.geckRootSubgroupParam ht i A u *
        (t.geckTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupParam ht i A
        (Multiplicative.ofAdd ((torusCharacter s (t.rootGeneratorWeight ht i) : A) *
          Multiplicative.toAdd u)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam
    _ _ _ _ _ _ _ (t.isCartanWeightVector_geckCoordinateBasisFin ht)
    (fun j => t.lie_lieBasis_h_rootGenerator ht i j) _ A s u

/-- **The represented weight torus normalizes the elementary group.** Conjugation by a torus point
rescales the parameter of each numbered root subgroup by the value of its root, so it preserves
the group the root subgroups generate. -/
theorem map_geckElementarySubgroup_conj_geckTorusPoints
    (A : CommAlgCat.{v} ℤ) (s : Fin t.rank → Aˣ) :
    Subgroup.map (MulAut.conj (t.geckTorusPoints ht A s)).toMonoidHom
        (t.geckElementarySubgroup ht A) = t.geckElementarySubgroup ht A :=
  TauCeti.UniversalEnvelopingAlgebra.map_kostantElementarySubgroup_conj_kostantTorusPoints
    _ _ _ _ _ _ _ (t.isCartanWeightVector_geckCoordinateBasisFin ht) (t.rootGeneratorWeight ht)
    (t.lie_lieBasis_h_rootGenerator ht) _ A s

/-! ## The points of the carrier -/

/-- A numbered Geck root subgroup written in the finite coordinate basis. -/
abbrev geckRootSubgroupMatrix {A : Type v} [CommRing A]
    (i : Fin t.rank ⊕ Fin t.rank) :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) i
    (t.isNilpotent_geckRepresentation_rootGenerator ht i) (t.geckCoordinateBasisFin ht)

/-- The represented Geck weight torus written in the finite coordinate basis. -/
abbrev geckTorusMatrix {A : Type v} [CommRing A] :
    (Fin t.rank → Aˣ) →* Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
    (t.geckCoordinateLattice ht).toAddSubgroup (t.geckCoordinateBasisFin ht)
    (t.geckWeightFin ht)

/-- **The `A`-valued points of the Geck carrier of a valid Dynkin type**, as a subgroup of
`GLₙ(A)` through the Hopf-ideal quotient presentation and the Geck coordinate basis. -/
def geckPoints (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

/-- **The points of the Geck carrier are cut out by its defining Hopf ideal.** This is the
form in which the `q`-power Frobenius of
`TauCeti/Algebra/AlgebraicGroup/Frobenius/GeneralLinear.lean` acts on them. -/
theorem geckPoints_def (A : Type v) [CommRing A] :
    t.geckPoints ht A =
      GeneralLinear.hopfIdealPointsSubgroup (t.geckDim ht) (t.geckDefiningIdeal ht) A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def _ _ _ _ _ _ _ _ A

/-- A matrix is a point of the Geck carrier exactly when the associated convolution point
kills its defining Hopf ideal. -/
@[simp]
theorem mem_geckPoints_iff (A : Type v) [CommRing A]
    (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
    g ∈ t.geckPoints ht A ↔
      ∀ x ∈ t.geckDefiningIdeal ht,
        ((GeneralLinear.pointsMulEquiv (R := ℤ) (t.geckDim ht)).symm g).ofConv x = 0 :=
  TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-- Every matrix in a numbered Geck root subgroup is a point of the carrier. -/
theorem geckRootSubgroupMatrix_mem_geckPoints (A : Type v) [CommRing A]
    (i : Fin t.rank ⊕ Fin t.rank)
    (q : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ)
      (CommAlgCat.of ℤ A)) :
    t.geckRootSubgroupMatrix ht i q ∈ t.geckPoints ht A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantGeneratedPointsSubgroup_le_toralPoints
    _ _ _ _ _ _ _ _ A
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_mem_generatedPoints
      _ _ _ _ _ _ _ A i q)

/-- Every represented Geck weight-torus matrix is a point of the carrier. -/
theorem geckTorusMatrix_mem_geckPoints (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.geckTorusMatrix ht s ∈ t.geckPoints ht A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_mem_toralPoints
    _ _ _ _ _ _ _ _ A s

/-- **The parametrized numbered root subgroup inside the Geck carrier points.** The parameter is
read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def geckRootSubgroupPoints (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] : Multiplicative A →* t.geckPoints ht A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i A

/-- A parametrized Geck root-subgroup point has the represented root-subgroup matrix as its
underlying general-linear element. -/
@[simp]
theorem coe_geckRootSubgroupPoints (i : Fin t.rank ⊕ Fin t.rank)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    (t.geckRootSubgroupPoints ht i A u :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      t.geckRootSubgroupMatrix ht i
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) :=
  TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i A u

/-- **The represented weight torus inside the Geck carrier points.** -/
noncomputable def geckWeightTorusPoints (A : Type v) [CommRing A] :
    (Fin t.rank → Aˣ) →* t.geckPoints ht A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

/-- A represented Geck weight-torus point has the weight-torus matrix as its underlying
general-linear element. -/
@[simp]
theorem coe_geckWeightTorusPoints (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    (t.geckWeightTorusPoints ht A s :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) = t.geckTorusMatrix ht s :=
  TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A s

/-- **The pinning equation inside the points of the Geck carrier.** Conjugation by a represented
weight-torus point rescales a numbered root-subgroup parameter by the corresponding root
character. -/
@[simp]
theorem geckWeightTorusPoints_conj_geckRootSubgroupPoints
    (i : Fin t.rank ⊕ Fin t.rank) (A : Type v) [CommRing A]
    (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckWeightTorusPoints ht A s * t.geckRootSubgroupPoints ht i A u *
        (t.geckWeightTorusPoints ht A s)⁻¹ =
      t.geckRootSubgroupPoints ht i A
        (Multiplicative.ofAdd
          ((torusCharacter s (t.rootGeneratorWeight ht i) : A) * Multiplicative.toAdd u)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (t.isCartanWeightVector_geckCoordinateBasisFin ht)
    (fun j => t.lie_lieBasis_h_rootGenerator ht i j) A s u

/-- **The two representations of a weight-torus point of the carrier agree**: writing the point
through `TauCeti.DynkinType.geckTorusMatrix` and writing it as the diagonal matrix of the weight
characters give the same element of `TauCeti.DynkinType.geckPoints`. Both occur in the pinning
equations, which state the parameter of a torus point in the second form and its value in the
first. -/
theorem geckPoints_mk_geckTorusMatrix (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    (⟨t.geckTorusMatrix ht s, t.geckTorusMatrix_mem_geckPoints ht A s⟩ : t.geckPoints ht A) =
      ⟨diagGL fun i => torusCharacter s (t.geckWeightFin ht i), by
        simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
          t.geckTorusMatrix_mem_geckPoints ht A s⟩ :=
  Subtype.ext (TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply _ _ _ s)

/-- **A pointwise torus-subsystem group lies in the points of the carrier.** The subgroup of
`Aut_A(A ⊗ M)` generated by the torus and a chosen set of numbered root subgroups, written in
the Geck coordinate basis, is contained in the `A`-valued points of the group scheme. -/
theorem map_geckTorusSubsystemSubgroup_le_geckPoints
    (S : Set (Fin t.rank ⊕ Fin t.rank)) (A : Type v) [CommRing A] :
    (t.geckTorusSubsystemSubgroup ht S (CommAlgCat.of ℤ A)).map
        (Units.map (LinearMap.toMatrixAlgEquiv
          ((t.geckCoordinateBasisFin ht).baseChange A)).toMulEquiv) ≤
      t.geckPoints ht A :=
  TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusSubsystemSubgroup_le_toralPoints
    _ _ _ _ _ _ _ _ S A

end

end TauCeti.DynkinType
