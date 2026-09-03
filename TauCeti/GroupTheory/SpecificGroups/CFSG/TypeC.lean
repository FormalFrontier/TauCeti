/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The standard symplectic carrier of a validated type-`C` index

The type-`C` branch of the classification list is built on the type-`C` diagram of rank `n`, and
Tau Ceti's explicit full-weight Chevalley carrier for that diagram is `TauCeti.SpStd.groupScheme`,
the Kostant toral closure of the standard representation of `sp_(2n)` inside `GL_(2n)` over `ℤ`.
This file attaches that carrier to a validated type-`C` index: the group of algebraic-closure-valued
points of the carrier at the index's rank, its Bourbaki-numbered simple root subgroups, and the
reading of their root characters in the type-`C` root datum the index names.

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

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III, for the numbering of the
  type-`C` diagram that the root subgroups below are indexed by.
* The signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group and the numbered simple root
  subgroup, both taken on a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the `C` branch,
and the standard symplectic carrier is not offered as a substitute for that pinned group.** The
pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets of
`TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds; none
of them is proved of `TauCeti.SpStd.groupScheme` here or in the files this one imports. What this
file supplies is the material that identification will be made against on the `C` branch: the
branch's explicit carrier, its numbered simple root subgroups, and their root characters read as the
simple roots of the type-`C` root datum. The milestone L1 Steinberg map of the untwisted family
`Cₙ(q)` and the milestone L3 quotient built from it are *not* stated here; they wait on L0's pinned
carrier for this branch.
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

end

end TypeCLieIndex

end TauCeti
