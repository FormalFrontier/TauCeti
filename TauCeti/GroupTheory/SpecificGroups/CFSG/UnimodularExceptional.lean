/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Torus

/-!
# The Lie-type candidates `E₈(q)`, `F₄(q)` and `G₂(q)`

The pinned Geck carrier `TauCeti.DynkinType.geckGroupScheme` is built from the adjoint
representation, so the characters occurring in it generate the root lattice and not, in general,
the whole character lattice of the pinned torus. It is therefore the adjoint form of a
Chevalley--Demazure group, whereas the CFSG recipe has to be run in the simply connected form.
The two forms agree exactly where the root lattice is the whole weight lattice, which by
`TauCeti.DynkinType.span_range_geckWeight_eq_top_iff` happens exactly in the types `E₈`, `F₄`
and `G₂`.

This file therefore singles out `TauCeti.LieTypeIndex.IsUnimodularExceptional`, the three
untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)`, and carries them through the whole CFSG recipe:
the pinned ambient group, its numbered root subgroups, the untwisted Steinberg map, the group it
fixes, and the derived subgroup of that group modulo its centre.

Three exclusions inside those Dynkin types are what makes the predicate list index constructors
rather than Dynkin types. The Ree families `²F₄(2^(2m+1))` and `²G₂(3^(2m+1))` and the Tits index
also have underlying Dynkin type `F₄` or `G₂`, and their Steinberg map is an odd power of a
half-Frobenius rather than the Frobenius, so the pinned ambient group is not enough to place them
here. The predicate is therefore exactly "the underlying diagram is one of the three unimodular
types, and the Steinberg map is not a half-Frobenius power", which is
`TauCeti.LieTypeIndex.isUnimodularExceptional_iff_not_usesHalfFrobenius_and_dynkinType`.

Nothing here asserts that the constructed group is finite, perfect, or simple, that the ambient
carrier is reductive, or that its weight torus is maximal; those are outside this roadmap. The
`Aₙ`, `²Aₙ`, `Bₙ`, `Cₙ`, `Dₙ`, `²Dₙ`, `E₆`, `²E₆`, `E₇` and `³D₄` families need a carrier built
from a full-weight representation of their own, and the Suzuki--Ree families need the
half-Frobenius, so this file covers three of the seventeen Lie-type constructors of
`TauCeti.LieTypeIndex` and no more.

## Main definitions

* `TauCeti.LieTypeIndex.IsUnimodularExceptional`: the three untwisted unimodular exceptional
  families, and `TauCeti.UnimodularExceptionalIndex`, the corresponding subtype of valid indices,
  whose three branches are `TauCeti.UnimodularExceptionalIndex.e8`, `f4` and `g2`.
* `TauCeti.UnimodularExceptionalIndex.AmbientGroup`: the pinned ambient group, the points of the
  Geck carrier of the underlying Dynkin type over the algebraic closure of the prime field.
* `TauCeti.UnimodularExceptionalIndex.rootSubgroup`: the numbered root subgroups of that group.
* `TauCeti.UnimodularExceptionalIndex.steinberg`: the Steinberg endomorphism, the `q`-power
  Frobenius.
* `TauCeti.UnimodularExceptionalIndex.Group`: the candidate simple group, the derived subgroup of
  the fixed points of the Steinberg map modulo the centre of that derived subgroup.

## Main results

* `TauCeti.LieTypeIndex.isUnimodularExceptional_iff_not_usesHalfFrobenius_and_dynkinType` and
  `TauCeti.LieTypeIndex.exists_eq_of_isUnimodularExceptional`: the predicate is the conjunction
  described above, and the three families exhaust it.
* `TauCeti.UnimodularExceptionalIndex.span_range_geckWeight_eq_top`: the Geck weights of such an
  index span the whole character lattice, so its Geck carrier is the simply connected form.
* `TauCeti.UnimodularExceptionalIndex.isClosedImmersion_geckWeightTorus`: consequently the pinned
  split torus is a closed subgroup scheme of the ambient carrier.
* `TauCeti.UnimodularExceptionalIndex.steinberg_rootSubgroup`: the Steinberg map raises the
  parameter of every numbered root subgroup to the `q`-th power, which is the equation milestone
  L1 asks of the untwisted branches.
* `TauCeti.UnimodularExceptionalIndex.mem_fixedSubgroup_steinberg_iff`: the fixed points of the
  Steinberg map are the points of the carrier whose matrix entries lie in the field of definition
  `𝔽_q` recorded by `TauCeti.ValidLieTypeIndex.fixedField`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates VII--IX, for the unimodularity
  of the `E₈`, `F₄` and `G₂` Cartan matrices.

## Roadmap

This supplies the milestone L0, L1 and L3 constructions of
`TauCetiRoadmap/CFSGStatement/README.md` on the `E₈`, `F₄` and `G₂` branches: `AmbientGroup` and
`rootSubgroup` are the L0 pinned ambient group and root subgroups, `steinberg` is the L1 map
`Frob_q` with its simple-root-subgroup equation, and `Group` is the L3 composite
`[H_d, H_d] / Z([H_d, H_d])`. It consumes the pinned Chevalley--Demazure carrier of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md` rather than restating it, so what that layer still
owes -- the reductivity of the carrier and the identification of its root datum with
`TauCeti.DynkinType.simplyConnectedRootDatum` -- is still owed after this file, for these
branches as for every other.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace LieTypeIndex

/-- The three untwisted families whose underlying Dynkin diagram has unimodular Cartan matrix:
`E₈(q)`, `F₄(q)` and `G₂(q)`. These are exactly the CFSG indices whose pinned adjoint Geck carrier
is already the simply connected form. -/
def IsUnimodularExceptional : LieTypeIndex → Prop
  | .E8 _ | .F4 _ | .G2 _ => True
  | _ => False

/-- Characterization of the untwisted unimodular exceptional families. -/
@[simp] theorem isUnimodularExceptional_iff (d : LieTypeIndex) : d.IsUnimodularExceptional ↔
    match d with
    | .E8 _ | .F4 _ | .G2 _ => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred IsUnimodularExceptional := fun d => by
  cases d <;> rw [isUnimodularExceptional_iff] <;> infer_instance

/-- The `E₈(q)` family is unimodular exceptional. -/
theorem isUnimodularExceptional_E8 (q : PrimePower) : (E8 q).IsUnimodularExceptional := trivial

/-- The `F₄(q)` family is unimodular exceptional. -/
theorem isUnimodularExceptional_F4 (q : PrimePower) : (F4 q).IsUnimodularExceptional := trivial

/-- The `G₂(q)` family is unimodular exceptional. -/
theorem isUnimodularExceptional_G2 (q : PrimePower) : (G2 q).IsUnimodularExceptional := trivial

/-- **The untwisted unimodular exceptional families are exactly the indices whose underlying
diagram is `E₈`, `F₄` or `G₂` and whose Steinberg map is not a half-Frobenius power.** The second
condition is not automatic: the Ree families `²F₄` and `²G₂` and the Tits index have underlying
diagram `F₄` or `G₂` as well. -/
theorem isUnimodularExceptional_iff_not_usesHalfFrobenius_and_dynkinType (d : LieTypeIndex) :
    d.IsUnimodularExceptional ↔
      ¬d.UsesHalfFrobenius ∧
        (d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2) := by
  cases d <;> simp

/-- An unimodular exceptional index does not use a half-Frobenius. -/
theorem not_usesHalfFrobenius_of_isUnimodularExceptional {d : LieTypeIndex}
    (hd : d.IsUnimodularExceptional) : ¬d.UsesHalfFrobenius :=
  ((isUnimodularExceptional_iff_not_usesHalfFrobenius_and_dynkinType d).mp hd).1

/-- The underlying Dynkin type of an unimodular exceptional index is `E₈`, `F₄` or `G₂`. -/
theorem dynkinType_of_isUnimodularExceptional {d : LieTypeIndex}
    (hd : d.IsUnimodularExceptional) :
    d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2 :=
  ((isUnimodularExceptional_iff_not_usesHalfFrobenius_and_dynkinType d).mp hd).2

/-- **An unimodular exceptional index is one of `E₈(q)`, `F₄(q)` and `G₂(q)`.** -/
theorem exists_eq_of_isUnimodularExceptional {d : LieTypeIndex}
    (hd : d.IsUnimodularExceptional) : ∃ q : PrimePower, d = .E8 q ∨ d = .F4 q ∨ d = .G2 q := by
  cases d <;> simp_all

end LieTypeIndex

/-- A valid CFSG index in one of the three untwisted families `E₈(q)`, `F₄(q)`, `G₂(q)`. Like
`TauCeti.GraphTwistedIndex` and `TauCeti.SuzukiReeIndex` this is a subtype of
`TauCeti.ValidLieTypeIndex`, so no branch of it is a value invented to fill a hole. -/
abbrev UnimodularExceptionalIndex : Type :=
  {d : ValidLieTypeIndex // d.1.IsUnimodularExceptional}

namespace UnimodularExceptionalIndex

noncomputable section

variable (d : UnimodularExceptionalIndex)

/-- The index `E₈(q)`. -/
abbrev e8 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨⟨.E8 q, by simp⟩, by simp⟩

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨⟨.F4 q, by simp⟩, by simp⟩

/-- The index `G₂(q)`, for `q` at least three: `G₂(2)` is excluded from the classification list,
its recipe producing a group already named `²A₂(3)`. -/
abbrev g2 (q : PrimePower) (hq : 3 ≤ q.card) : UnimodularExceptionalIndex :=
  ⟨⟨.G2 q, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq, not_false⟩⟩, by simp⟩

/-- The underlying untwisted Dynkin diagram of an unimodular exceptional index. -/
abbrev dynkinType : DynkinType := d.1.dynkinType

/-- That diagram is a valid Dynkin type, so the pinned Geck carrier of the root-systems roadmap is
available for it. -/
theorem dynkinType_valid : d.dynkinType.Valid := d.1.dynkinType_valid

/-- The underlying Dynkin type of an unimodular exceptional index is one of the three unimodular
exceptional types. -/
theorem dynkinType_eq_E8_or_eq_F4_or_eq_G2 :
    d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2 :=
  LieTypeIndex.dynkinType_of_isUnimodularExceptional d.2

/-- **The Geck weights of an unimodular exceptional index span the whole character lattice.** This
is what makes its adjoint Geck carrier the simply connected form, and hence the ambient group the
CFSG recipe asks for. -/
theorem span_range_geckWeight_eq_top :
    Submodule.span ℤ (Set.range (d.dynkinType.geckWeight d.dynkinType_valid)) = ⊤ :=
  (DynkinType.span_range_geckWeight_eq_top_iff _ d.dynkinType_valid).mpr
    d.dynkinType_eq_E8_or_eq_F4_or_eq_G2

/-- **The pinned split torus is a closed subgroup scheme of the ambient carrier.** This is the
torus half of the pinning, and it is exactly what the full character span of
`TauCeti.UnimodularExceptionalIndex.span_range_geckWeight_eq_top` buys. -/
theorem isClosedImmersion_geckWeightTorus :
    IsClosedImmersion (d.dynkinType.geckWeightTorus d.dynkinType_valid).hom.hom.left :=
  DynkinType.isClosedImmersion_geckWeightTorus_of_span_eq_top _ d.dynkinType_valid
    d.span_range_geckWeight_eq_top

/-! ## The ambient group and its root subgroups -/

/-- **The pinned ambient group of an unimodular exceptional index**: the points of the pinned Geck
carrier of its underlying Dynkin type over the algebraic closure of its prime field. It is
generally infinite; no finiteness, reductivity or maximality statement is attached to it. -/
abbrev ambientPoints :
    Subgroup (Matrix.GeneralLinearGroup
      (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :=
  d.dynkinType.geckPoints d.dynkinType_valid d.1.Closure

/-- The ambient group as a type, with the group structure it inherits as a subgroup of
`GLₙ` over the algebraic closure. -/
abbrev AmbientGroup : Type := ↥d.ambientPoints

/-- **The numbered root subgroups of the ambient group.** The left summand indexes the raising
generators and the right summand the lowering generators of the pinned Bourbaki numbering, so
`rootSubgroup d (.inl i)` is the simple root subgroup `x_{α_i}`. -/
def rootSubgroup (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank) :
    Multiplicative d.1.Closure →* AmbientGroup d :=
  MonoidHom.codRestrict
    ((d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i).comp
      (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.1.Closure)).symm.toMonoidHom)
    d.ambientPoints fun _ =>
      d.dynkinType.geckRootSubgroupMatrix_mem_geckPoints d.dynkinType_valid d.1.Closure i _

/-- The general linear matrix underlying a root-subgroup point is the represented Geck
root-subgroup matrix of the same parameter. -/
@[simp]
theorem coe_rootSubgroup (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank)
    (u : Multiplicative d.1.Closure) :
    (d.rootSubgroup i u : Matrix.GeneralLinearGroup
        (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) =
      d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.1.Closure)).symm u) := by
  rw [rootSubgroup]
  rfl

/-! ## The Steinberg endomorphism -/

/-- **The Steinberg endomorphism of an unimodular exceptional index**: the `q`-power Frobenius of
the ambient group, where `q` is the field order recorded by the index. The three families this
covers are untwisted, so no diagram automorphism and no half-Frobenius enters. -/
def steinberg : AmbientGroup d →* AmbientGroup d :=
  d.dynkinType.geckFrobenius d.dynkinType_valid d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map is the Frobenius of the pinned Geck carrier at the exponent recorded by the
index. This is its unfolding lemma; the definition itself stays sealed. -/
theorem steinberg_def : d.steinberg =
    d.dynkinType.geckFrobenius d.dynkinType_valid d.1.characteristic d.1.fieldExponent
      d.1.Closure := by
  rw [steinberg]

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : AmbientGroup d)
    (r c : Fin (d.dynkinType.geckDim d.dynkinType_valid)) :
    ((d.steinberg g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [d.1.fieldOrder_eq_characteristic_pow]
  exact d.dynkinType.coe_geckFrobenius_apply d.dynkinType_valid _ _ _ g r c

/-- **The Steinberg map raises the parameter of every numbered root subgroup to the `q`-th
power.** On a simple root subgroup this is the equation `Frob_q (x_α(t)) = x_α(t ^ q)` that
milestone L1 requires of the untwisted families. -/
@[simp]
theorem steinberg_rootSubgroup (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.rootSubgroup i u) =
      d.rootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [d.1.fieldOrder_eq_characteristic_pow]
  exact d.dynkinType.geckFrobenius_geckRootSubgroupMatrix d.dynkinType_valid
    d.1.characteristic d.1.fieldExponent d.1.Closure i u

/-! ## The fixed points and the candidate group -/

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`,
the copy of the field of `q` elements inside the algebraic closure, the fixed group `H_d` of
milestone L3 is therefore the group of points of the pinned carrier whose entries lie in `𝔽_q`.

This is deliberately not a `simp` lemma: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the
identity, so `simp` rewrites its left-hand side to `d.steinberg g = g` through the Mathlib
`simp` lemma `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : AmbientGroup d) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix (Fin (d.dynkinType.geckDim d.dynkinType_valid))
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) r c ∈
        d.1.fixedField := by
  rw [mem_fixedSubgroup, steinberg_def,
    d.dynkinType.geckFrobenius_eq_self_iff d.dynkinType_valid _ _ _ g]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

/-- **The candidate simple group of an unimodular exceptional index**: the derived subgroup of the
fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the CFSG recipe on the `E₈`, `F₄` and `G₂` branches. Nothing below asserts that it is
finite, perfect, or simple. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end UnimodularExceptionalIndex

end TauCeti
