/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.RootDatum
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Index

/-!
# The exceptional family `E₇(q)` on the minuscule carrier

The classification list carries a single family on the `E₇` diagram, the untwisted `E₇(q)`, cut out
of the index datatype by `TauCeti.TypeE7LieIndex`. Tau Ceti's explicit full-weight Chevalley
carrier for that diagram is `TauCeti.E7Minuscule.groupScheme`, the Kostant toral closure of the
`56`-dimensional minuscule representation `V(ϖ₇)` inside `GL₅₆` over `ℤ`.

This file attaches that carrier to such an index: the group of points over the algebraic closure of
the index's prime field, the simple root subgroups numbered by the Bourbaki nodes of the `E₇`
diagram, the explicit unipotent matrix each of them is, and the pinning equation that reads their
characters as the simple roots of `TauCeti.DynkinType.simplyConnectedRootDatum` at `E₇`.

The minuscule representation rather than the adjoint one is what makes the carrier's character
lattice the full weight lattice of the `E₇` root datum, which contains the root lattice with index
two; the adjoint carrier spans the character lattice exactly in the types `E₈`, `F₄` and `G₂`,
where the two lattices coincide.

No Steinberg endomorphism is formed here, and no group of fixed points. Nothing below asserts that
the carrier is reductive, that its weight torus is maximal, that it is the pinned simply connected
Chevalley--Demazure group scheme of type `E₇`, or that any group named is finite, perfect or
simple; none of those is proved of `TauCeti.E7Minuscule.groupScheme` here or in the files this one
imports, and the carrier is not offered as a substitute for the pinned group of the diagram. What
is proved of the carrier against the `E₇` diagram is the pinning equation
`TauCeti.TypeE7LieIndex.weightTorusPoints_conj_simpleRootSubgroup`.

## Main declarations

* `TauCeti.TypeE7LieIndex.AmbientGroup`: the algebraic-closure-valued points of the minuscule
  carrier, the group inside which the family's finite group will be cut out.
* `TauCeti.TypeE7LieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node.

## Main results

* `TauCeti.TypeE7LieIndex.coe_simpleRootSubgroup`: a simple-root point is the explicit unipotent
  matrix `1 + u Eᵢ` in the minuscule basis.
* `TauCeti.TypeE7LieIndex.weightTorusPoints_conj_simpleRootSubgroup`: the weight torus rescales
  the parameter of the subgroup at node `i` by the `i`-th simple root of the uniform pinned `E₇`
  datum, in the same Bourbaki numbering.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14, for the fixed-point construction of the
  exceptional families and their carriers.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI, for the numbering of the
  `E₇` diagram that the root subgroups below are indexed by.
-/

public section

namespace TauCeti

namespace TypeE7LieIndex

open DynkinType

noncomputable section

variable (d : TypeE7LieIndex)

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group this file attaches to a validated `E₇` index**: the points of the explicit
full-weight type-`E₇` minuscule Chevalley carrier over the algebraic closure of its prime field.
No finiteness, reductivity, pinning or maximality statement is attached to it, and it is not
claimed to be the points of the pinned simply connected `E₇` group scheme. -/
abbrev AmbientGroup : Type := E7Minuscule.points d.1.Closure

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `E₇` diagram. It is
the carrier's numbered raising subgroup at the same node, the index type `Fin d.1.rank` being the
upstream Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  E7Minuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_seven i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding node.
This is the equation through which the upstream root-subgroup API reaches `simpleRootSubgroup`. It
is not a `simp` lemma: `coe_simpleRootSubgroup` and
`weightTorusPoints_conj_simpleRootSubgroup` are the normal forms the equations of this file are
stated against, and unfolding to `TauCeti.E7Minuscule.rootSubgroupPoints` would keep them from
firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      E7Minuscule.rootSubgroupPoints (.inl (finCongr d.rank_eq_seven i)) d.1.Closure :=
  (rfl)

/-- **A simple-root point is an explicit unipotent matrix.** At the Bourbaki-numbered node `i` and
parameter `u` it is `1 + u Eᵢ`, where `Eᵢ` is the integral raising matrix of the minuscule basis,
read in the algebraic closure. This is the sense in which the carrier of the family is explicit
data rather than a group produced by an existence theorem. -/
@[simp]
theorem coe_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    ((d.simpleRootSubgroup i u : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) :
        Matrix (Fin 56) (Fin 56) d.1.Closure) =
      1 + Multiplicative.toAdd u •
        (E7Minuscule.raisingMatrix (finCongr d.rank_eq_seven i)).map
          (Int.cast : ℤ → d.1.Closure) := by
  rw [simpleRootSubgroup_def]
  exact E7Minuscule.coe_rootSubgroupPoints_inl _ _ _

/-- **The simple-root subgroups sit at the simple roots of the `E₇` root datum.** A point `s` of
the carrier's rank-seven split weight torus conjugates the subgroup at node `i` to itself,
rescaling its parameter by the value at `s` of the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at `E₇`, in the same Bourbaki numbering. This is the
sense in which the minuscule carrier serves the diagram that the index names; it is not a claim
that the carrier is the pinned group of that diagram, no pinning being constructed for it.

The torus is indexed by the carrier's own `Fin 7`, which `finCongr d.rank_eq_seven` identifies
with the index's copy `Fin d.1.rank` of the Bourbaki index type. -/
theorem weightTorusPoints_conj_simpleRootSubgroup (i : Fin d.1.rank)
    (s : Fin 7 → d.1.Closureˣ) (u : Multiplicative d.1.Closure) :
    E7Minuscule.weightTorusPoints d.1.Closure s * d.simpleRootSubgroup i u *
        (E7Minuscule.weightTorusPoints d.1.Closure s)⁻¹ =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd
          ((torusCharacter s
              ((E7.simplyConnectedRootDatum DynkinType.valid_E7).root
                (E7.simpleIndex DynkinType.valid_E7 (finCongr d.rank_eq_seven i))) :
                  d.1.Closure) *
            Multiplicative.toAdd u)) := by
  rw [simpleRootSubgroup_def]
  exact E7Minuscule.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex
    DynkinType.valid_E7 _ _ s u

end

end TypeE7LieIndex

end TauCeti
