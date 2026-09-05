/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

/-!
# The untwisted family `Cₙ(q)` on the standard symplectic carrier

The type-`C` branch of the classification list is built on the type-`C` diagram of rank `n`, and
Tau Ceti's explicit full-weight Chevalley carrier for that diagram is `TauCeti.SpStd.groupScheme`,
the Kostant toral closure of the standard representation of `sp_(2n)` inside `GL_(2n)` over `ℤ`.
This file attaches that carrier to a validated type-`C` index and runs the classification recipe on
it: the group of algebraic-closure-valued points of the carrier at the index's rank, its
Bourbaki-numbered simple root subgroups, the reading of their root characters in the type-`C` root
datum the index names, the Steinberg endomorphism of the family, and the candidate group

```text
H_d = fixedSubgroup d.steinberg,        d.Group = [H_d, H_d] / Z([H_d, H_d]).
```

The Steinberg map is the `q`-power Frobenius outright, `q` being the field order the index records.
That is what an untwisted family asks for, and `TauCeti.TypeCLieIndex.diagramPerm_eq_one` is the
check that the diagram permutation this index carries is indeed trivial: the type-`C` diagram has
no symmetry to twist by, its last node carrying a root of a different length from the others, so
`Cₙ(q)` is the only classification-list family on it.

The carrier is indexed by `n` in the spelling `C (n + 1)`, so a validated index of rank `r` uses
the carrier at `TauCeti.TypeCLieIndex.carrierRank`, which is `r - 1`. That subtraction is harmless
because `TauCeti.TypeCLieIndex.three_le_rank` bounds the rank below by three:
`TauCeti.TypeCLieIndex.carrierRank_add_one` recovers `r`, and every numbered object below is indexed
by `Fin d.1.rank`, the upstream Bourbaki index type of the index's own Dynkin type, rather than by a
node of the carrier. The two numberings agree node for node, so
`TauCeti.TypeCLieIndex.carrierNode` is the rank identification and nothing more; that is what
`TauCeti.TypeCLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex` records, reading the
character of the `i`-th raising subgroup as the `i`-th simple root of the type-`C` root datum the
index names.

The rank-two member of the same carrier family is *not* reached from here. `TauCeti.DynkinType.C 2`
is not a valid Dynkin type, the rank-two root system being carried by `B 2`, and correspondingly a
validated type-`C` index has rank at least three. The rank-two carrier serves the Suzuki family
instead, in `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB2.lean`, where the node correspondence
acquires the swap of the two Bourbaki nodes.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the symplectic group scheme or the pinned simply connected Chevalley--Demazure group scheme of type
`Cₙ`, or that its point group is finite.

## Main declarations

* `TauCeti.TypeCLieIndex.AmbientGroup`: the algebraic-closure-valued points of the standard
  symplectic carrier at the index's rank.
* `TauCeti.TypeCLieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node, with
  `TauCeti.TypeCLieIndex.rootGeneratorWeight_carrierNode_eq_root_simpleIndex` identifying the
  character of that subgroup with the corresponding simple root of the type-`C` root datum.
* `TauCeti.TypeCLieIndex.steinberg`: the Steinberg endomorphism of the family, with
  `TauCeti.TypeCLieIndex.coe_steinberg_apply` its entrywise description,
  `TauCeti.TypeCLieIndex.steinberg_simpleRootSubgroup` its pinned equation
  `Frob_q (x_i(u)) = x_i(u ^ q)`, and
  `TauCeti.TypeCLieIndex.mem_fixedSubgroup_steinberg_iff` describing the points it fixes as those
  whose matrix entries lie in the field of definition `𝔽_q`.
* `TauCeti.TypeCLieIndex.Group`: the candidate group of `Cₙ(q)`, the derived subgroup of those
  fixed points modulo its centre.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17, for
  the Steinberg endomorphism and its fixed points.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III, for the numbering of the
  type-`C` diagram that the root subgroups below are indexed by.
* The signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Steinberg map with its pinned equation, and the fixed-point candidate, all taken on
  a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the `C` branch,
and the standard symplectic carrier is not offered as a substitute for that pinned group.** The
pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.SpStd.groupScheme` here or in the files this one imports. What this
file supplies is the branch's explicit carrier, its numbered root characters read in the type-`C`
root datum, the equation `Frob_q (x_i(u)) = x_i(u ^ q)` that milestone L1 asks of an ordinary
Frobenius, and the milestone L3 recipe run on it, each in the shape those milestones state it; they
transfer to the L0 carrier along that Layer 9 identification, and not before. The counterparts on
the branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeD.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
-/

public section

namespace TauCeti

namespace TypeCLieIndex

variable (d : TypeCLieIndex)

noncomputable section

/-! ## The carrier rank and the node correspondence -/

/-- **The rank parameter of the standard symplectic carrier serving a validated type-`C` index.**
`TauCeti.SpStd.groupScheme n` is the carrier of type `C (n + 1)`, so the carrier serving an index
of rank `r` is the one at `r - 1`. The subtraction never truncates, `r` being at least three by
`TauCeti.TypeCLieIndex.three_le_rank`; `TauCeti.TypeCLieIndex.carrierRank_add_one` is the
identification that recovers `r`. -/
def carrierRank : ℕ := d.1.rank - 1

/-- The carrier rank of a validated type-`C` index is one less than its rank. It is oriented
towards `TauCeti.ValidLieTypeIndex.rank`, so that `simp` normalizes the successor of the carrier
rank to the rank the index's own Bourbaki index type is built on. -/
@[simp]
theorem carrierRank_add_one : d.carrierRank + 1 = d.1.rank := by
  have := d.three_le_rank
  -- The body is unexposed, so the subtraction has to be unfolded before `omega` sees it.
  rw [carrierRank]
  omega

/-- **The carrier node numbered by a Bourbaki node of the index's diagram.** Unlike the rank-two
correspondence of the Suzuki family, this is the rank identification and nothing else: the standard
symplectic carrier at `TauCeti.TypeCLieIndex.carrierRank` numbers its generators by the Bourbaki
numbering of the type-`C` diagram that the index names, node for node. -/
abbrev carrierNode (i : Fin d.1.rank) : Fin (d.carrierRank + 1) :=
  Fin.cast d.carrierRank_add_one.symm i

/-- **The node correspondence transports the type-`C` Cartan matrix.** The entry at a pair of
carrier nodes is the entry at the pair of Bourbaki nodes they number: `carrierNode` moves no node
value, only the rank its index type is built on, and `TauCeti.TypeCLieIndex.carrierRank_add_one`
identifies the two ranks. -/
theorem cartanMatrix_C_carrierNode (i j : Fin d.1.rank) :
    CartanMatrix.C (d.carrierRank + 1) (d.carrierNode i) (d.carrierNode j) =
      CartanMatrix.C d.1.rank i j := by
  have hrank : d.1.rank - 1 = d.carrierRank := by
    have := d.carrierRank_add_one
    omega
  -- Both sides are the same table of conditions on the two node values, which `carrierNode` leaves
  -- unchanged, and on the last node, where the two spellings of the rank agree by `hrank`.
  simp only [CartanMatrix.C, Matrix.of_apply, carrierNode, Fin.ext_iff, Fin.val_cast,
    Nat.add_sub_cancel, hrank]

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated type-`C` index**: the points of the
explicit full-weight standard symplectic Chevalley carrier at the index's rank, over the algebraic
closure of its prime field. No finiteness, reductivity, pinning or maximality statement is attached
to it, and it is not claimed to be the pinned type-`Cₙ` group scheme's points that milestone L0 asks
for, that identification being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type := SpStd.points d.carrierRank d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the type-`C` diagram. It
is the carrier's numbered raising subgroup at the node that `carrierNode` names. -/
def simpleRootSubgroup (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.AmbientGroup :=
  SpStd.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`, whose definition itself stays sealed. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      SpStd.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`C` root datum.** The character
by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read in the
same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the index names. This is the sense
in which the standard symplectic carrier serves that diagram; it is not a claim that the carrier is
the pinned group of the diagram, no pinning being constructed for it. -/
theorem rootGeneratorWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    SpStd.rootGeneratorWeight d.carrierRank (.inl (d.carrierNode i)) (d.carrierNode j) =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`C` Cartan matrix, the carrier's by the upstream
  -- `SpStd.rootGeneratorWeight_inl` and the datum's by the uniform `DynkinType.root_simpleIndex`,
  -- which is the same route the upstream identification takes past the dependent root index. The
  -- two index transports that remain are then the stated equations `cartanMatrix_C_carrierNode`
  -- and `dynkinType_cartanMatrix_apply`, so no dependent conversion is left to the elaborator.
  rw [SpStd.rootGeneratorWeight_inl]
  simp only [DynkinType.root_simpleIndex]
  rw [d.dynkinType_cartanMatrix_apply, d.cartanMatrix_C_carrierNode]

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated type-`C` index**: the `q`-power Frobenius of the
ambient group, `q` being the field order the index records. The family is untwisted, so no diagram
automorphism and no half-Frobenius enters; `TauCeti.TypeCLieIndex.diagramPerm_eq_one` is the check
that its diagram permutation is trivial. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of a type-`C` index is the carrier's Frobenius at the exponent the index
records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` and `coe_steinberg_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.SpStd.frobenius` would keep them from firing. -/
theorem steinberg_def :
    d.steinberg = SpStd.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : d.AmbientGroup)
    (r c : Fin (d.carrierRank + 1 + (d.carrierRank + 1))) :
    ((d.steinberg g :
        Matrix.GeneralLinearGroup (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) :
        Matrix (Fin (d.carrierRank + 1 + (d.carrierRank + 1)))
          (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) r c =
      ((g :
        Matrix.GeneralLinearGroup (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) :
        Matrix (Fin (d.carrierRank + 1 + (d.carrierRank + 1)))
          (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [steinberg_def, d.1.fieldOrder_eq_characteristic_pow]
  exact SpStd.coe_frobenius_apply _ _ _ _ g r c

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation
milestone L1 asks of the untwisted families. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, simpleRootSubgroup_def, SpStd.frobenius_rootSubgroupPoints,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`,
the copy of the field of `q` elements inside the algebraic closure, the group `H_d` that the
milestone L3 recipe is run on below is therefore the group of points of the standard symplectic
carrier whose entries lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.steinberg g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g :
          Matrix.GeneralLinearGroup (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) :
        Matrix (Fin (d.carrierRank + 1 + (d.carrierRank + 1)))
          (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def, SpStd.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The classification candidate -/

/-- **The candidate simple group of the untwisted family `Cₙ(q)`**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the milestone L3 recipe on the `C` branch, run on the standard symplectic carrier. Nothing
below asserts that it is finite, perfect, or simple, nor that the carrier is the one milestone L0
asks for. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeCLieIndex

end TauCeti
