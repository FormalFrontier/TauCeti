/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The untwisted family `E₆(q)` on the minuscule carrier

The untwisted exceptional family `E₆(q)` is built on the `E₆` diagram, and Tau Ceti's explicit
full-weight Chevalley carrier for that diagram is `TauCeti.E6Minuscule.groupScheme`, the Kostant
toral closure of the `27`-dimensional minuscule representation inside `GL₂₇` over `ℤ`. This file
runs the classification recipe on it: for a validated `E₆` index it supplies the group of
algebraic-closure-valued points of that carrier, its Bourbaki-numbered simple root subgroups, the
Steinberg endomorphism milestone L1 prescribes for an untwisted family, and the candidate group
milestone L3 builds from it,

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d]).
```

The Steinberg map is the `q`-power Frobenius outright. That is what L1's table asks of an untwisted
family, and `TauCeti.TypeE6LieIndex.diagramPerm_toGraphTwistedIndex` is the check that the diagram
permutation this index carries is indeed trivial: the nontrivial symmetry of the `E₆` diagram
belongs to `²E₆(q)`, a different constructor.

The graph-twisted family `²E₆(q)` is therefore *not* built here, although it is the other
classification-list family on this diagram. Its Steinberg map composes the Frobenius with the order
two graph automorphism `γ₂`, which does not act on this carrier at all: the diagram automorphism of
`E₆` exchanges the minuscule representation with its contragredient rather than preserving either,
so a carrier realizing it has to carry both, as
`TauCeti/Algebra/Lie/E6/DoubledMinuscule/Basic.lean` records. Assembling that carrier and that
automorphism is separate work, and this file adds no index subtype for `²E₆(q)`.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the pinned simply connected Chevalley--Demazure group scheme of type `E₆`, or that any group below
is finite, perfect, or simple. What is proved of the carrier against the `E₆` diagram is the
identification of numbered root characters,
`TauCeti.TypeE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex`.

## Main declarations

* `TauCeti.TypeE6LieIndex.AmbientGroup`: the algebraic-closure-valued points of the minuscule
  carrier, the group the recipe is run inside.
* `TauCeti.TypeE6LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node, with
  `TauCeti.TypeE6LieIndex.rootGeneratorWeight_eq_root_simpleIndex` identifying the character of
  that subgroup with the corresponding simple root of the `E₆` root datum.
* `TauCeti.TypeE6LieIndex.steinberg`: the Steinberg endomorphism of the family, together with its
  pinned equation `Frob_q (x_i(u)) = x_i(u ^ q)` and the description
  `TauCeti.TypeE6LieIndex.mem_fixedSubgroup_steinberg_iff` of the group `H_d` it fixes.
* `TauCeti.TypeE6LieIndex.Group`: the classification candidate `[H_d, H_d] / Z([H_d, H_d])`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V, for the numbering of the
  `E₆` diagram that the root subgroups below are indexed by.
* The target signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Steinberg map with its pinned equation, and the fixed-point candidate, all taken
  on a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0, and the minuscule
carrier is not offered as a substitute for that pinned group.** The pinned group scheme, its
pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.E6Minuscule.groupScheme` here or in the files this one imports. What
this file supplies is the branch's explicit carrier, its numbered root characters read in the `E₆`
root datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of an ordinary
Frobenius, and the milestone L3 recipe run on it, each in the shape those milestones state it; they
transfer to the L0 carrier along that Layer 9 identification, and not before. The counterparts on
the other branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
-/

public section

namespace TauCeti

namespace TypeE6LieIndex

open DynkinType

noncomputable section

variable (d : TypeE6LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated `E₆` index**: the points of the explicit
full-weight type-`E₆` minuscule Chevalley carrier over the algebraic closure of its prime field. No
finiteness, reductivity, pinning or maximality statement is attached to it, and it is not claimed
to be the pinned `E₆` group scheme's points that milestone L0 asks for, that identification being
the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type := E6Minuscule.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `E₆` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  E6Minuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`. It
is not a `simp` lemma: `steinberg_simpleRootSubgroup` is the normal form the pinned equations of
this file are stated against, and unfolding to `TauCeti.E6Minuscule.rootSubgroupPoints` would keep
it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      E6Minuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_six i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the `E₆` root datum.** The character by
which the carrier's split torus rescales the parameter of `simpleRootSubgroup i` is the `i`-th
simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at `E₆`, in the same Bourbaki
numbering. This is the sense in which the minuscule carrier serves the diagram that the index
names; it is not a claim that the carrier is the pinned group of that diagram, no pinning being
constructed for it. -/
theorem rootGeneratorWeight_eq_root_simpleIndex (i : Fin d.1.rank) :
    E6Minuscule.rootGeneratorWeight (.inl (finCongr d.rank_eq_six i)) =
      (E6.simplyConnectedRootDatum valid_E6).root
        (E6.simpleIndex valid_E6 (finCongr d.rank_eq_six i)) := by
  -- The uniform `root_simpleIndex` is instantiated by hand rather than rewritten with: its index
  -- argument lives in `Fin E6.rank`, which is only definitionally the `Fin 6` the carrier uses.
  have h := root_simpleIndex E6 valid_E6 (finCongr d.rank_eq_six i)
  rw [E6Minuscule.rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex, root_e6SimpleIndex, h,
    cartanMatrix_E6]

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated `E₆` index**: the `q`-power Frobenius of the
ambient group, `q` being the field order the index records. The family is untwisted, so no diagram
automorphism and no half-Frobenius enters; `diagramPerm_toGraphTwistedIndex` is the check that its
diagram permutation is trivial. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  E6Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of an `E₆` index is the carrier's Frobenius at the exponent the index
records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` and `coe_steinberg_apply`
are the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.E6Minuscule.frobenius` would keep them from firing. -/
theorem steinberg_def :
    d.steinberg = E6Minuscule.frobenius d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : d.AmbientGroup) (r c : Fin 27) :
    ((d.steinberg g : Matrix.GeneralLinearGroup (Fin 27) d.1.Closure) :
        Matrix (Fin 27) (Fin 27) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup (Fin 27) d.1.Closure) :
        Matrix (Fin 27) (Fin 27) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [steinberg_def, d.1.fieldOrder_eq_characteristic_pow]
  exact E6Minuscule.coe_frobenius_apply _ _ _ g r c

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, simpleRootSubgroup_def, E6Minuscule.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the group `H_d` that the milestone L3 recipe is run on below is therefore the group of
points of the minuscule carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp`
lemma: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.steinberg g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup (Fin 27) d.1.Closure) :
        Matrix (Fin 27) (Fin 27) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def, E6Minuscule.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The classification candidate -/

/-- **The candidate simple group of the untwisted family `E₆(q)`**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the milestone L3 recipe on the `E₆` branch, run on the minuscule carrier. Nothing below
asserts that it is finite, perfect, or simple, nor that the carrier is the one milestone L0 asks
for. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeE6LieIndex

end TauCeti
