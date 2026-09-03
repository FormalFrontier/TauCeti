/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The three families on a type-`D` diagram, and the candidate group of `Dₙ(q)`

Three classification-list families are built on the diagram `Dₙ`: the untwisted `Dₙ(q)`, the
graph-twisted `²Dₙ(q)`, and, at rank four, the triality-twisted `³D₄(q)`. They share a diagram, so
they share a carrier, and `TauCeti.TypeDDiagramLieIndex` is the subtype that collects exactly them.
This file attaches to such an index the group of algebraic-closure-valued points of Tau Ceti's
explicit full-weight type-`D` spin Chevalley carrier at the index's own rank,
`TauCeti.TypeDSpinCarrier.points`, together with that group's Bourbaki-numbered simple root
subgroups and its `q`-power Frobenius; and it then runs the milestone L3 recipe on the untwisted
branch, where the Frobenius *is* the Steinberg map.

The rank is available because it is at least four on this subtype, by
`TauCeti.TypeDDiagramLieIndex.four_le_rank`, which is exactly the hypothesis the carrier takes: the
carrier is built from the type-`Dₙ` Serre presentation, whose diagram is `A₁ × A₁` at rank two and
`A₃` at rank three, so it is offered only in the range where `Dₙ` is a valid Dynkin type.

The spin carrier rather than the Geck carrier is used because the Geck carrier is built from the
adjoint representation, so its weights span the whole character lattice exactly in the types `E₈`,
`F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`. A type-`D` diagram is not
one of those, by `TauCeti.LieTypeIndex.not_hasUnimodularDiagram_of_hasTypeDDiagram`, and the full
spin representation is what sees both spinor cosets of the type-`D` root lattice; its weights span
that lattice, by `TauCeti.TypeDSpinCarrier.span_range_basisWeight_eq_top`.

## Why only one of the three branches gets a candidate group

The three families differ exactly in the endomorphism whose fixed points milestone L3 takes. On
the untwisted branch that endomorphism is the `q`-power Frobenius outright, which is what milestone
L1's table asks of an untwisted family and what
`TauCeti.TypeDLieIndex.diagramPerm_toGraphTwistedIndex` checks: the diagram permutation the index
carries is trivial. So `TauCeti.TypeDLieIndex.steinberg` is the shared Frobenius, and the recipe

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d])
```

runs on this branch, on the spin carrier.

On the two twisted branches the Steinberg map is `γ ∘ Frob_q` for a nontrivial diagram
permutation, the fork exchange on `²Dₙ(q)` and triality on `³D₄(q)`. The graph factor `γ` is
point-level data that the carrier does not yet carry, and its pinning equation
`γ (x_{α_i}(t)) = x_{α_{σ i}}(t)` is stated against the numbered root subgroups on matrix points.
Neither twisted Steinberg map is formed until that factor exists, and hence no candidate group is
formed on those two branches either; the Frobenius supplied here is the factor they will compose
with, on the very carrier their fixed points will be taken in.

Nothing here asserts that the spin carrier is reductive, that its weight torus is maximal, or that
any group below is finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeDDiagramLieIndex.AmbientGroup`: the algebraic-closure-valued points of the
  full-weight type-`D` spin carrier at the rank the index names, the group inside which the
  classification recipe is run on the untwisted branch below.
* `TauCeti.TypeDDiagramLieIndex.simpleRootSubgroup`: the positive simple-root subgroup at a
  Bourbaki node.
* `TauCeti.TypeDDiagramLieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character of that
  subgroup is the corresponding simple root of the root datum of the Dynkin type the index names.
* `TauCeti.TypeDDiagramLieIndex.frobenius`, `TauCeti.TypeDDiagramLieIndex.coe_frobenius_apply` and
  `TauCeti.TypeDDiagramLieIndex.frobenius_simpleRootSubgroup`: the `q`-power Frobenius, its
  entrywise description, and its pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)`.
* `TauCeti.TypeDDiagramLieIndex.mem_fixedSubgroup_frobenius_iff`: its fixed points are the points
  whose matrix entries lie in the field of definition `𝔽_q`.
* `TauCeti.TypeDLieIndex.steinberg` and `TauCeti.TypeDLieIndex.Group`: the milestone L1 Steinberg
  endomorphism of the untwisted branch and the milestone L3 quotient formed from it, both on the
  spin carrier rather than on the pinned group milestone L0 asks for.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV, for the numbering of the
  `Dₙ` diagram that the index's rank and diagram permutation are read in.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Steinberg map with its pinned equation, and the fixed-point recipe, all taken on a
  validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the three
type-`D` branches, and the spin carrier is not offered as a substitute for that pinned group.** The
pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets
of `TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds;
none of them is proved of `TauCeti.TypeDSpinCarrier.groupScheme` here or in the files this one
imports. What this file supplies is the branches' explicit carrier, its numbered root characters
read in the type-`Dₙ` root datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1
asks of an ordinary Frobenius factor, and, on the untwisted branch, the milestone L3 recipe run on
that Frobenius, each in the shape those milestones state it; they transfer to the L0 carrier along
that Layer 9 identification, and not before. The counterparts on the branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
-/

public section

namespace TauCeti

namespace TypeDDiagramLieIndex

noncomputable section

variable (d : TypeDDiagramLieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated index on a type-`D` diagram**: the points
of the explicit full-weight type-`Dₙ` spin Chevalley carrier, at the rank the index names, over the
algebraic closure of its prime field.

It is infinite, and it is the same group for the untwisted, graph-twisted and triality-twisted
families of a given rank and field order, those three differing only in the Steinberg map taken of
it. No finiteness, reductivity, pinning or maximality statement is attached to it, and it is not
claimed to be the pinned `Dₙ` group scheme's points that milestone L0 asks for, that identification
being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type :=
  TypeDSpinCarrier.points d.1.rank d.four_le_rank d.1.Closure

/-- Milestone L3 runs its recipe inside this group, so it carries a group structure; the carrier
being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `Dₙ` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type and the carrier's own rank. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.four_le_rank (.inl i) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`,
whose definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` is the normal form the pinned
equations of this file are stated against, and unfolding to
`TauCeti.TypeDSpinCarrier.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.four_le_rank (.inl i) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`Dₙ` root datum.** The
character by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i` is
the `i`-th simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the
index names, in the same Bourbaki numbering. This is the sense in which the spin carrier serves
that diagram; it is not a claim that the carrier is the pinned group of the diagram, no pinning
being constructed for it.

The character itself is `TauCeti.TypeDStd.rootGeneratorWeight`, which
`TauCeti.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` exhibits as the one conjugation
by the carrier's split torus rescales the parameter by. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeDStd.rootGeneratorWeight d.1.rank (.inl i) j =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`D` Cartan matrix, the carrier's by the upstream
  -- `TypeDStd.rootGeneratorWeight_inl` and the datum's by the uniform
  -- `DynkinType.root_simpleIndex`, leaving the stated index transport
  -- `dynkinType_cartanMatrix_apply` between them.
  rw [TypeDStd.rootGeneratorWeight_inl]
  simp only [DynkinType.root_simpleIndex]
  rw [d.dynkinType_cartanMatrix_apply]

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of an index on a type-`D`
diagram**, for `q` the field order the index records. On the untwisted family `Dₙ(q)` it is the
Steinberg map itself, by `TauCeti.TypeDLieIndex.steinberg_def`. On the two twisted families it is
not: there the Steinberg map is `γ ∘ Frob_q` for a nontrivial diagram permutation, and this is the
factor that composite composes with. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic d.1.fieldExponent
    d.1.Closure

/-- The Frobenius of an index on a type-`D` diagram is the carrier's Frobenius at the exponent the
index records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.TypeDSpinCarrier.frobenius` would keep them from firing. -/
theorem frobenius_def :
    d.frobenius =
      TypeDSpinCarrier.frobenius d.1.rank d.four_le_rank d.1.characteristic d.1.fieldExponent
        d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup)
    (r c : Fin (TypeDSpinCarrier.dimension d.1.rank)) :
    ((d.frobenius g :
        Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact TypeDSpinCarrier.coe_frobenius_apply _ _ _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation milestone L1
asks of an ordinary Frobenius factor. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, TypeDSpinCarrier.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius fixed points are the points
of the spin carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, TypeDSpinCarrier.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end TypeDDiagramLieIndex

namespace TypeDLieIndex

noncomputable section

variable (d : TypeDLieIndex)

/-! ## The Steinberg endomorphism of the untwisted family -/

/-- **The milestone L1 Steinberg endomorphism of a validated untwisted type-`D` index, formed on
the spin carrier**: the `q`-power Frobenius of the ambient group, `q` being the field order the
index records. The family is untwisted, so no diagram automorphism and no half-Frobenius enters;
`diagramPerm_toGraphTwistedIndex` is the check that its diagram permutation is trivial.

It is the Steinberg map of `Dₙ(q)` on the pinned carrier milestone L0 asks for only along the
Layer 9 identification of the two carriers described in the module docstring, and not before. -/
def steinberg :
    d.toTypeDDiagramLieIndex.AmbientGroup →* d.toTypeDDiagramLieIndex.AmbientGroup :=
  d.toTypeDDiagramLieIndex.frobenius

/-- The Steinberg map of an untwisted type-`D` index is the Frobenius that all three families on a
type-`D` diagram share. This is its unfolding lemma; the definition itself stays sealed, and it is
through this equation that the ambient-group API of `TauCeti.TypeDDiagramLieIndex` reaches the
Steinberg map. -/
theorem steinberg_def : d.steinberg = d.toTypeDDiagramLieIndex.frobenius := (rfl)

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families, on this branch. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.toTypeDDiagramLieIndex.simpleRootSubgroup i u) =
      d.toTypeDDiagramLieIndex.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def]
  exact d.toTypeDDiagramLieIndex.frobenius_simpleRootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition**, so the group `H_d` that the milestone L3 recipe is run on
below is the group of points of the spin carrier whose entries lie in `𝔽_q`. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.toTypeDDiagramLieIndex.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) :
        Matrix (Fin (TypeDSpinCarrier.dimension d.1.rank))
          (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [steinberg_def]
  exact d.toTypeDDiagramLieIndex.mem_fixedSubgroup_frobenius_iff g

/-! ## The milestone L3 quotient -/

/-- **The milestone L3 quotient on the type-`Dₙ` spin carrier**: the derived subgroup of the fixed
points of the Steinberg map above, modulo the centre of that derived subgroup.

This is the shape milestone L3 asks of the untwisted family `Dₙ(q)`, formed on the spin carrier
rather than on the pinned simply connected Chevalley--Demazure group scheme that milestone L0 asks
for. It becomes the candidate simple group of that family along the Layer 9 identification of the
two carriers described in the module docstring, and not before; it is not offered as that candidate
here. Nothing below asserts that it is finite, perfect, or simple. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeDLieIndex

end TauCeti
