/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Frobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The candidate group of the untwisted family `Bₙ(q)`

The classification list carries the untwisted odd orthogonal family named `Bₙ(q)` for `n ≥ 2`,
whose matrix name in Gorenstein--Lyons--Solomon is `Ω_{2n+1}(q)`. This file runs the fixed-point
recipe of Chevalley and Steinberg on a validated index of that family: inside the group of
algebraic-closure-valued points of an explicit full-weight Chevalley carrier of type `Bₙ`, take
the fixed points of the `q`-power Frobenius, then the derived subgroup of those fixed points, then
the quotient by its centre.

The carrier used is Tau Ceti's explicit type-`B` spin carrier `TauCeti.TypeBSpinCarrier`, the
Kostant toral closure of the `2ⁿ`-dimensional spin representation of `so_(2n+1)` inside `GL_(2ⁿ)`
over `ℤ`. The spin representation rather than the adjoint one is what makes the character lattice
of this carrier the full weight lattice of the `Bₙ` root datum, that lattice containing the root
lattice with index two; the adjoint representation sees only the root lattice, and its span is the
whole character lattice exactly in the types `E₈`, `F₄` and `G₂`, by
`TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`. The spin weights do span, by
`TauCeti.TypeBSpinCarrier.span_range_basisWeight_eq_top`.

The carrier is indexed by `n` in the spelling `B (n + 1)`, so a validated index of rank `r` uses
the carrier at `TauCeti.TypeBLieIndex.carrierRank`, which is `r - 1`. That subtraction is harmless
because `TauCeti.TypeBLieIndex.two_le_rank` bounds the rank below by two:
`TauCeti.TypeBLieIndex.carrierRank_add_one` recovers `r`, and every numbered object below is indexed
by `Fin d.1.rank`, the Bourbaki index type of the index's own Dynkin type, rather than by a node of
the carrier. The two numberings agree node for node, so `TauCeti.TypeBLieIndex.carrierNode` is the
rank identification and nothing more; that is what
`TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex` records, reading the character of
the `i`-th raising subgroup as the `i`-th simple root of the type-`Bₙ` root datum the index names.

The family is untwisted: the `Bₙ` diagram has no symmetry to twist by, its two extreme nodes
carrying different root lengths, so the Steinberg endomorphism is the `q`-power Frobenius outright
and no diagram automorphism and no half-Frobenius enters. The Suzuki family `²B₂(2^(2m+1))` shares
the rank-two diagram but not that Steinberg map, and it is not an index of the subtype used here;
it is served in `TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB/Two.lean`, on the rank-two symplectic
carrier that the exceptional isogeny of characteristic two acts on. The rank-two members of the
present family are also collected there, by `TauCeti.TypeB2LieIndex`: that subtype cuts the
untwisted family out of the pair sharing the `B₂` diagram, where this one cuts the untwisted family
out of the whole list, at every rank the family has.

Nothing here asserts that the carrier is reductive, that its weight torus is maximal, that it is
the spin group scheme or the pinned simply connected Chevalley--Demazure group scheme of type `Bₙ`,
or that any group below is finite, perfect, or simple. In particular, the group constructed here is
identified with the finite simple group `Bₙ(q)` only along an identification of this carrier with
that pinned group scheme, which is proved neither here nor in the files this one imports.

## Main declarations

* `TauCeti.LieTypeIndex.IsTypeB` and `TauCeti.TypeBLieIndex`: the constructor selector of the
  family and the subtype of validated indices it cuts out, on which everything below is stated.
* `TauCeti.TypeBLieIndex.AmbientGroup`: the algebraic-closure-valued points of the full-weight
  type-`B` spin carrier at the rank the index names.
* `TauCeti.TypeBLieIndex.simpleRootSubgroup`: its positive simple-root subgroup at a
  Bourbaki-numbered node, with
  `TauCeti.TypeBLieIndex.rootWeight_carrierNode_eq_root_simpleIndex` identifying the character of
  that subgroup with the corresponding simple root of the type-`Bₙ` root datum.
* `TauCeti.TypeBLieIndex.steinberg`, with `TauCeti.TypeBLieIndex.steinberg_simpleRootSubgroup` and
  `TauCeti.TypeBLieIndex.mem_fixedSubgroup_steinberg_iff`: the Steinberg endomorphism of the
  family, its equation `Frob_q (x_i(u)) = x_i(u ^ q)` on the numbered simple-root subgroups, and
  the description of its fixed points as the carrier points with entries in `𝔽_q`.
* `TauCeti.TypeBLieIndex.Group`: the derived subgroup of those fixed points, modulo its centre.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17, for
  the Frobenius endomorphism and its fixed points.
* D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 1, §2.2, for the small-parameter exclusions that the validated index carries.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II, for the numbering of the
  `Bₙ` diagram that the root subgroups below are indexed by.
* The signatures realized here follow the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`: the ambient group, the numbered simple root
  subgroup, the Steinberg map with its pinned equation, and the fixed-point recipe, all taken on a
  validated-index subtype.
-/

public section

namespace TauCeti

/-! ## The validated indices of the family -/

namespace LieTypeIndex

/-- Whether a Lie-type index belongs to the untwisted family `B_r(q)`.

This is a constructor selector, not a mathematical property of a group. It is false on the Suzuki
family `²B₂(2^(2m+1))`, which shares the `B₂` diagram but takes an odd power of a half-Frobenius
for its Steinberg map. The rank, field, and preferred-representative restrictions come from the
enclosing `TauCeti.ValidLieTypeIndex`. -/
abbrev IsTypeB : LieTypeIndex → Prop
  | .B _ _ => True
  | _ => False

instance : DecidablePred IsTypeB := fun d => by
  cases d <;> infer_instance

end LieTypeIndex

/-- A validated index in the untwisted type-`B` family `B_r(q)`.

In particular, its rank is at least two, and neither `B₂(2)`, whose recipe does not produce a
simple group, nor `B₂(3)`, which the list carries as `²A₃(2)`, is an index of this subtype. The
Suzuki family `²B₂(2^(2m+1))`, which shares the `B₂` diagram, is not of this subtype either. -/
abbrev TypeBLieIndex : Type _ := {d : ValidLieTypeIndex // d.1.IsTypeB}

namespace TypeBLieIndex

open LieTypeIndex (inStandardRange_iff valid_iff)

/-- Introduce a valid type-`B` index. -/
abbrev ofB (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.B rank q).Valid) :
    TypeBLieIndex :=
  ⟨⟨.B rank q, hvalid⟩, trivial⟩

/-- Every type-B index is an introduction form `ofB rank q hvalid`. -/
theorem exists_eq_ofB (d : TypeBLieIndex) :
    ∃ (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.B rank q).Valid),
      d = ofB rank q hvalid := by
  obtain ⟨⟨d, hvalid⟩, hB⟩ := d
  revert hvalid hB
  cases d
  case B rank q => exact fun hvalid _ => ⟨rank, q, hvalid, rfl⟩
  all_goals exact fun _ hB => False.elim hB

/-- **The Cartan matrix of the diagram a validated type-`B` index names**, entry by entry: it is
the type-`B` Cartan matrix at the index's rank. This is the projection of the introduction form
`TauCeti.TypeBLieIndex.ofB` through `TauCeti.DynkinType.cartanMatrix_B`, stated on entries rather
than on matrices because the rank occurs in the index types of the two nodes. -/
theorem dynkinType_cartanMatrix_apply (d : TypeBLieIndex) (i j : Fin d.1.rank) :
    d.1.dynkinType.cartanMatrix i j = CartanMatrix.B d.1.rank i j := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofB
  exact congrFun₂ (DynkinType.cartanMatrix_B rank) i j

/-- The rank of a validated type-`B` index is at least two: the `B₁` diagram is `A₁`, and the
double edge that names the family appears from rank two on. -/
theorem two_le_rank (d : TypeBLieIndex) : 2 ≤ d.1.rank := by
  obtain ⟨rank, q, hvalid, rfl⟩ := d.exists_eq_ofB
  simpa only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
    LieTypeIndex.dynkinType_B, DynkinType.rank_B] using
      ((inStandardRange_iff _).mp ((valid_iff _).mp hvalid).1).1

variable (d : TypeBLieIndex)

noncomputable section

/-! ## The carrier rank and the node correspondence -/

/-- **The rank parameter of the type-`B` spin carrier serving a validated type-`B` index.**
`TauCeti.TypeBSpinCarrier.groupScheme n` is the carrier of type `B (n + 1)`, so the carrier serving
an index of rank `r` is the one at `r - 1`. The subtraction never truncates, `r` being at least two
by `TauCeti.TypeBLieIndex.two_le_rank`; `TauCeti.TypeBLieIndex.carrierRank_add_one` is the
identification that recovers `r`. -/
def carrierRank : ℕ := d.1.rank - 1

/-- The carrier rank of a validated type-`B` index is one less than its rank. It is oriented
towards `TauCeti.ValidLieTypeIndex.rank`, so that `simp` normalizes the successor of the carrier
rank to the rank the index's own Bourbaki index type is built on. -/
@[simp]
theorem carrierRank_add_one : d.carrierRank + 1 = d.1.rank := by
  have := d.two_le_rank
  -- The body is unexposed, so the subtraction has to be unfolded before `omega` sees it.
  rw [carrierRank]
  omega

/-- **The carrier node numbered by a Bourbaki node of the index's diagram.** The type-`B` spin
carrier at `TauCeti.TypeBLieIndex.carrierRank` numbers its generators by the Bourbaki numbering of
the type-`B` diagram that the index names, node for node, so this is the rank identification and
nothing else. -/
abbrev carrierNode (i : Fin d.1.rank) : Fin (d.carrierRank + 1) :=
  Fin.cast d.carrierRank_add_one.symm i

/-- **The node correspondence transports the type-`B` Cartan matrix.** The entry at a pair of
carrier nodes is the entry at the pair of Bourbaki nodes they number: `carrierNode` moves no node
value, only the rank its index type is built on, and `TauCeti.TypeBLieIndex.carrierRank_add_one`
identifies the two ranks. -/
theorem cartanMatrix_B_carrierNode (i j : Fin d.1.rank) :
    CartanMatrix.B (d.carrierRank + 1) (d.carrierNode i) (d.carrierNode j) =
      CartanMatrix.B d.1.rank i j := by
  have hrank : d.1.rank - 1 = d.carrierRank := by
    have := d.carrierRank_add_one
    omega
  -- Both sides are the same table of conditions on the two node values, which `carrierNode` leaves
  -- unchanged, and on the last node, where the two spellings of the rank agree by `hrank`.
  simp only [CartanMatrix.B, Matrix.of_apply, carrierNode, Fin.ext_iff, Fin.val_cast,
    Nat.add_sub_cancel, hrank]

/-- The Dynkin type of the carrier serving a validated type-`B` index is valid, its rank being at
least two. This is the hypothesis under which the upstream carrier reads its root characters in the
simply connected root datum. -/
theorem valid_B_carrierRank_add_one : (DynkinType.B (d.carrierRank + 1)).Valid := by
  rw [DynkinType.valid_B, d.carrierRank_add_one]
  exact d.two_le_rank

/-! ## The ambient group and its simple root subgroups -/

/-- **The ambient group of a validated type-`B` index**: the points of the explicit full-weight
type-`Bₙ` spin Chevalley carrier, at the rank the index names, over the algebraic closure of its
prime field.

It is infinite, and no finiteness, reductivity, pinning or maximality statement is attached to it;
in particular it is not claimed to be the points of the pinned simply connected
Chevalley--Demazure group scheme of type `Bₙ`. -/
abbrev AmbientGroup : Type := TypeBSpinCarrier.points d.carrierRank d.1.Closure

/-- The classification recipe is run inside this group, so it carries a group structure; the
carrier being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

/-- The positive simple-root subgroup at the Bourbaki-numbered node `i` of the `Bₙ` diagram. It is
the carrier's numbered raising subgroup at the node that `carrierNode` names, the index type
`Fin d.1.rank` being the Bourbaki index type of the index's own Dynkin type. -/
def simpleRootSubgroup (i : Fin d.1.rank) : Multiplicative d.1.Closure →* d.AmbientGroup :=
  TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure

/-- The simple-root subgroup is the carrier's numbered raising subgroup at the corresponding
carrier node. This is the equation through which the upstream root-subgroup API reaches
`simpleRootSubgroup`, whose definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` is the normal form the pinned
equations of this file are stated against, and unfolding to
`TauCeti.TypeBSpinCarrier.rootSubgroupPoints` would keep it from firing. -/
theorem simpleRootSubgroup_def (i : Fin d.1.rank) :
    d.simpleRootSubgroup i =
      TypeBSpinCarrier.rootSubgroupPoints d.carrierRank (.inl (d.carrierNode i)) d.1.Closure :=
  (rfl)

/-- **The simple-root subgroups sit at the simple roots of the type-`Bₙ` root datum.** The
character by which the carrier's split torus rescales the parameter of `simpleRootSubgroup i`, read
in the same node correspondence, is the `i`-th simple root of
`TauCeti.DynkinType.simplyConnectedRootDatum` at the Dynkin type the index names. This is the sense
in which the spin carrier serves that diagram; it is not a claim that the carrier is the pinned
group of the diagram, no pinning being constructed for it.

The character itself is `TauCeti.TypeBSpinCarrier.rootWeight`, which
`TauCeti.TypeBSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` exhibits as the one
conjugation by the carrier's split torus rescales the parameter by. -/
theorem rootWeight_carrierNode_eq_root_simpleIndex (i j : Fin d.1.rank) :
    TypeBSpinCarrier.rootWeight d.carrierRank (.inl (d.carrierNode i)) (d.carrierNode j) =
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
        (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) j := by
  -- Both sides are read as entries of the type-`B` Cartan matrix: the carrier's by the upstream
  -- identification of its root weights with the simple roots of the carrier's own datum, and the
  -- index's by the uniform `DynkinType.root_simpleIndex`. The two index transports that remain
  -- are then the stated equations `cartanMatrix_B_carrierNode` and `dynkinType_cartanMatrix_apply`.
  rw [TypeBSpinCarrier.rootWeight_inl_eq_root_simpleIndex d.carrierRank
      d.valid_B_carrierRank_add_one,
    congrFun (DynkinType.root_simpleIndex (DynkinType.B (d.carrierRank + 1))
      d.valid_B_carrierRank_add_one (d.carrierNode i)) (d.carrierNode j),
    DynkinType.cartanMatrix_B, d.cartanMatrix_B_carrierNode]
  simp only [DynkinType.root_simpleIndex]
  exact (d.dynkinType_cartanMatrix_apply i j).symm

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of a validated type-`B` index**: the `q`-power Frobenius of the
ambient group, `q` being the field order the index records. The family is untwisted, the `Bₙ`
diagram having no symmetry to twist by, so no diagram automorphism and no half-Frobenius enters;
`TauCeti.GraphTwistedIndex.diagramPerm_B` is the check that its diagram permutation is trivial. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of a type-`B` index is the carrier's Frobenius at the exponent the index
records. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_simpleRootSubgroup` and `coe_steinberg_apply` are
the normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.TypeBSpinCarrier.frobenius` would keep them from firing. -/
theorem steinberg_def :
    d.steinberg =
      TypeBSpinCarrier.frobenius d.carrierRank d.1.characteristic d.1.fieldExponent d.1.Closure :=
  (rfl)

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : d.AmbientGroup)
    (r c : Fin (TypeBSpinCarrier.dimension d.carrierRank)) :
    ((d.steinberg g :
        Matrix.GeneralLinearGroup (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
        Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
          (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [steinberg_def, d.1.fieldOrder_eq_characteristic_pow]
  exact TypeBSpinCarrier.coe_frobenius_apply _ _ _ _ g r c

/-- **The Steinberg map fixes the Bourbaki numbering of a simple-root subgroup and raises its
parameter to the `q`-th power**, that is, `Frob_q (x_i(u)) = x_i(u ^ q)`. This is the equation an
ordinary Frobenius Steinberg map is pinned by. -/
@[simp]
theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup i
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, simpleRootSubgroup_def, TypeBSpinCarrier.frobenius_rootSubgroupPoints,
    ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`,
the copy of the field of `q` elements inside the algebraic closure, the group whose derived
subgroup the recipe below takes is therefore the group of points of the spin carrier whose entries
lie in `𝔽_q`.

As for `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`, this is not a `simp` lemma:
`TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the identity, so `simp` rewrites its
left-hand side to `d.steinberg g = g` through `MonoidHom.mem_eqLocus`, and the `simpNF` linter
rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : d.AmbientGroup) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
            (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) :
          Matrix (Fin (TypeBSpinCarrier.dimension d.carrierRank))
            (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) r c ∈ d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def, TypeBSpinCarrier.frobenius_eq_self_iff]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-! ## The classification candidate -/

/-- **The candidate simple group of the untwisted family `Bₙ(q)`**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

Nothing below asserts that it is finite, perfect, or simple, nor that the carrier it is formed in
is the pinned simply connected Chevalley--Demazure group scheme of type `Bₙ`. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- The classification list asks every branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end TypeBLieIndex

end TauCeti
