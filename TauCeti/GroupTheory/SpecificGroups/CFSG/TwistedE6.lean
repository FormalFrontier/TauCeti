/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The graph-twisted family `²E₆(q)` on the doubled minuscule carrier

The classification list carries two families on the `E₆` diagram: the untwisted `E₆(q)`, whose
Steinberg map is the `q`-power Frobenius, and the graph-twisted `²E₆(q)`, whose Steinberg map is
that Frobenius composed with the order-two symmetry `γ₂` of the diagram. They are built on
different carriers, and that is forced rather than chosen: the `E₆` diagram symmetry exchanges the
minuscule representation `V(ϖ₁)` with its contragredient `V(ϖ₆)` rather than preserving either, so
it does not act on the `27`-dimensional carrier `TauCeti.E6Minuscule.groupScheme` that
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` runs the recipe on. The graph-stable carrier
is `TauCeti.E6DoubledMinuscule.groupScheme`, built on `V(ϖ₁) ⊕ V(ϖ₆)` inside `GL₅₄` over `ℤ`.

This file attaches that carrier to a validated `²E₆` index. It supplies the group of
algebraic-closure-valued points and the Bourbaki-numbered simple root subgroups, identifies the
character of those subgroups with the corresponding simple root of the `E₆` root datum, records
that the involution of the fifty-four doubled coordinates realizes on the doubled weight family the
diagram permutation the index itself carries, and builds the `q`-power Frobenius factor `Frob_q` of
the branch's Steinberg map, with the pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)` on the numbered
simple-root subgroups and the description of the points it fixes as those all of whose `54 × 54`
matrix entries lie in the field of definition `𝔽_q`.

The Steinberg map itself is *not* here, and no fixed-point subgroup of it is formed. That map is
the composite `γ₂ ∘ Frob_q`, whose other factor `γ₂` is the automorphism of the carrier that the
coordinate involution induces; constructing it consumes exactly the weight equivariance recorded
below. In particular `TauCeti.TypeTwistedE6LieIndex.frobenius` is not that map: the twisted branch
is precisely the one on which the Steinberg map and its Frobenius factor differ.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the pinned simply connected Chevalley--Demazure group scheme of type `E₆`, or that any group
mentioned is finite, perfect, or simple.

## Main declarations

* `TauCeti.TypeTwistedE6LieIndex.AmbientGroup`: the algebraic-closure-valued points of the doubled
  minuscule carrier, the group the classification recipe for `²E₆(q)` will be run inside.
* `TauCeti.TypeTwistedE6LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.
* `TauCeti.TypeTwistedE6LieIndex.frobenius`: the `q`-power Frobenius factor of the branch's
  Steinberg map, at the field order the index records.

## Main results

* `TauCeti.TypeTwistedE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex`: the character of that
  subgroup is the corresponding simple root of
  `TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`.
* `TauCeti.TypeTwistedE6LieIndex.frobenius_simpleRootSubgroup`: the pinned equation
  `Frob_q (x_i(u)) = x_i(u ^ q)` on the numbered simple-root subgroups.
* `TauCeti.TypeTwistedE6LieIndex.mem_fixedSubgroup_frobenius_iff`: a point is fixed by `Frob_q`
  exactly when all entries of its `54 × 54` matrix lie in the field of definition.
* `TauCeti.TypeTwistedE6LieIndex.e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm`:
  the coordinate involution of the doubled index set is equivariant for the diagram permutation
  that the index itself carries, read in the index's copy `Fin d.1.rank` of the Bourbaki index
  type.
* `TauCeti.TypeTwistedE6LieIndex.e6DoubledMinusculeGraphPerm_pow_twistOrder`: the twist order the
  index records annihilates that involution.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2 and 13, for the graph automorphism of `E₆` and
  the twisted family it defines.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the Steinberg endomorphisms of the graph-twisted families.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V, for the numbering of the
  `E₆` diagram that the root subgroups below are indexed by.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group and the numbered simple root
  subgroup, taken on a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0, and the doubled
minuscule carrier is not offered as a substitute for that pinned group.** The pinned group scheme,
its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.E6DoubledMinuscule.groupScheme` here or in the files this one
imports. What this file supplies is the `²E₆` branch's explicit carrier, its numbered root
characters read in the `E₆` root datum, the diagram-symmetry data that a graph automorphism's
equation `γ (x_α(t)) = x_{γ α}(t)` will be proved from, and the `q`-power Frobenius `Frob_q`
together with its own pinned equation `Frob_q (x_α(t)) = x_α(t ^ q)`; they transfer to the points
of the pinned group along an identification of it with this carrier, and not before. The
counterparts on the branches already assembled
are `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`, and the branch that likewise stops short
of a Steinberg map is `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`.
-/

public section

namespace TauCeti

namespace TypeTwistedE6LieIndex

open DynkinType

noncomputable section

variable (d : TypeTwistedE6LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated `²E₆` index**: the points of the explicit
full-weight graph-stable type-`E₆` doubled minuscule Chevalley carrier over the algebraic closure
of its prime field. No finiteness, reductivity, pinning or maximality statement is attached to it,
and it is not claimed to be the pinned `E₆` group scheme's points that milestone L0 asks for, that
identification being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type := E6DoubledMinuscule.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `E₆` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  E6DoubledMinuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`. It
is deliberately not a `simp` lemma: the pinned equations `γ₂ (x_i(u)) = x_{σ i}(u)` and
`Frob_q (x_i(u)) = x_i(u ^ q)` of this branch's Steinberg map will be stated against
`simpleRootSubgroup` itself, and unfolding to `TauCeti.E6DoubledMinuscule.rootSubgroupPoints` would
keep them from firing, as it does on the branches already assembled. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      E6DoubledMinuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `E₆` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, pinned by
`TauCeti.E6DoubledMinuscule.weightTorus_conj_rootSubgroup`, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`, in the same Bourbaki numbering.

The characters themselves are shared with the `27`-dimensional carrier, `TauCeti.E6Minuscule`
having defined them from the `E₆` Cartan matrix alone, so this is the same identification the
untwisted branch records in `TauCeti.TypeE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex`, on
the index subtype of this branch. It is not a claim that the doubled carrier is the pinned group of
that diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i : Fin d.1.rank) :
    E6Minuscule.rootGeneratorWeight (.inl (finCongr d.rank_eq_six i)) =
      (E6.simplyConnectedRootDatum valid_E6).root
        (E6.simpleIndex valid_E6 (finCongr d.rank_eq_six i)) := by
  -- The uniform `root_simpleIndex` is instantiated by hand rather than rewritten with: its index
  -- argument lives in `Fin E6.rank`, which is only definitionally the `Fin 6` the carrier uses.
  have h := root_simpleIndex E6 valid_E6 (finCongr d.rank_eq_six i)
  rw [E6Minuscule.rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex, root_e6SimpleIndex, h,
    cartanMatrix_E6]

/-! ## The diagram symmetry on the carrier's coordinates -/

/-- **The coordinate involution of the doubled index set realizes the diagram permutation that the
index carries.** `TauCeti.DynkinType.e6DoubledMinusculeGraphPerm` exchanges the two minuscule
summands, and this is the equivariance `wt (π x) (σ i) = wt x i` of the doubled weight family for
it, with `σ` read as `TauCeti.GraphTwistedIndex.diagramPerm` of this index rather than as
`TauCeti.graphPermE6` directly. That equivariance is the hypothesis under which a numbered
permutation of the coordinates extends to an automorphism of a Kostant toral-closure carrier, so
stating it against the index's own permutation is what will make the resulting automorphism the
`γ₂` of milestone L1's table rather than an unrelated symmetry.

The minuscule weight family alone admits no such equivariance, by
`TauCeti.DynkinType.e6MinusculeWeight_comp_graphPermE6_notMem_range`; that is why this branch is
built on the doubled carrier. -/
theorem e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm_diagramPerm
    (x : Fin 27 ⊕ Fin 27) (i : Fin d.1.rank) :
    e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm x)
        (finCongr d.rank_eq_six (d.toGraphTwistedIndex.diagramPerm i)) =
      e6DoubledMinusculeWeight x (finCongr d.rank_eq_six i) := by
  -- A `finCongr` round trip preserves the underlying natural number on the nose, so the two
  -- casts cancel by `Fin.ext` rather than by an `Equiv.apply_symm_apply` rewrite, which would
  -- have to be aimed at the inner occurrence.
  have hcast (j : Fin 6) : finCongr d.rank_eq_six (finCongr d.rank_eq_six.symm j) = j :=
    Fin.ext rfl
  have hinv (j : Fin 6) : graphPermE6 (graphPermE6 j) = j := by
    rw [← Equiv.Perm.mul_apply, ← pow_two, graphPermE6_sq, Equiv.Perm.one_apply]
  rw [diagramPerm_toGraphTwistedIndex, hcast,
    e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm, hinv]

/-- **The twist order of the index annihilates the coordinate involution.** Together with
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder` on the diagram side, this is the pair of
order relations from which the graph automorphism of the carrier inherits `γ₂ ^ 2 = 1`, the
relation milestone L1 requires of the `²E₆` branch. -/
theorem e6DoubledMinusculeGraphPerm_pow_twistOrder :
    e6DoubledMinusculeGraphPerm ^ d.toGraphTwistedIndex.twistOrder = 1 := by
  rw [d.twistOrder_toGraphTwistedIndex, pow_two]
  exact Equiv.ext e6DoubledMinusculeGraphPerm_apply_apply

/-! ## The Frobenius factor of the Steinberg map -/

/-- **The `q`-power Frobenius endomorphism of the ambient group of a validated `²E₆` index**, `q`
being the field order the index records.

It is *not* the Steinberg map of the family, which for a graph-twisted family is `γ₂ ∘ Frob_q`.
On this branch the two genuinely differ: the composite acts on the simple-root subgroups through
the diagram permutation the index carries, which is `TauCeti.graphPermE6` by
`TauCeti.TypeTwistedE6LieIndex.diagramPerm_toGraphTwistedIndex` and has order two by
`TauCeti.orderOf_graphPermE6`. This is the right-hand factor of that composite, and the subgroup of
points it fixes, characterized below, is correspondingly the untwisted one and not the fixed
subgroup of the composite. -/
def frobenius : d.AmbientGroup →* d.AmbientGroup :=
  E6DoubledMinuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius of a `²E₆` index is the doubled minuscule carrier's Frobenius at the
characteristic and the exponent the index records. -/
-- Not `@[simp]`: `frobenius_simpleRootSubgroup` and `coe_frobenius_apply` are the normal forms the
-- pinned equations of this file are stated against, and unfolding to
-- `TauCeti.E6DoubledMinuscule.frobenius` would keep them from firing, as it does on the branches
-- already assembled.
theorem frobenius_def :
    d.frobenius = E6DoubledMinuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Frobenius acts on the ambient group by raising each entry of the `54 × 54` matrix of a
point to the `q`-th power. This is the coefficient-level form from which the commutation of
`Frob_q` with a coordinate symmetry of the carrier is read. -/
@[simp]
theorem coe_frobenius_apply (g : d.AmbientGroup) (r c : Fin 54) :
    ((d.frobenius g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [frobenius_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E6DoubledMinuscule.coe_frobenius_apply _ _ _ g r c

/-- **The Frobenius fixes the Bourbaki numbering of a simple-root subgroup and raises its parameter
to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. The diagram permutation of the
twisted family enters through the other factor `γ₂` of the Steinberg map, and not through this
one. -/
@[simp]
theorem frobenius_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.frobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [frobenius_def, simpleRootSubgroup_def, E6DoubledMinuscule.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Frobenius exactly when every entry of its
`54 × 54` matrix lies in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the Frobenius-fixed subgroup is therefore the group of points of the doubled minuscule
carrier with coordinates in `𝔽_q`. It is not the group of points fixed by the twisted composite
`γ₂ ∘ Frob_q`, which is the one the classification recipe for this branch is run inside. -/
-- Not `@[simp]`, as for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`:
-- `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites the
-- left-hand side to `d.frobenius g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
-- rejects the annotation.
theorem mem_fixedSubgroup_frobenius_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 54) d.1.Closure) :
        Matrix (Fin 54) (Fin 54) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def, E6DoubledMinuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end TypeTwistedE6LieIndex

end TauCeti
