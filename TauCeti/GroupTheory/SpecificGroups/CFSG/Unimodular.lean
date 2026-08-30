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
# The Lie-type indices whose Dynkin diagram is unimodular

The pinned Geck carrier `TauCeti.DynkinType.geckGroupScheme` is built from the adjoint
representation, so the characters occurring in it generate the root lattice and not, in general,
the whole character lattice of the pinned torus. It is therefore the adjoint form of a
Chevalley--Demazure group, whereas the CFSG recipe has to be run in the simply connected form.
The two forms agree exactly where the root lattice is the whole weight lattice, which by
`TauCeti.DynkinType.span_range_geckWeight_eq_top_iff` happens exactly in the types `E₈`, `F₄`
and `G₂`.

This file therefore singles out `TauCeti.LieTypeIndex.HasUnimodularDiagram`, the indices whose
underlying diagram is one of those three, and gives them the pinned ambient group and numbered root
subgroups that milestone L0 asks for. Six of the seventeen Lie-type constructors qualify, and they
are of two kinds:

```text
E₈(q),  F₄(q),  G₂(q),        ²G₂(3^(2m+1)),  ²F₄(2^(2m+1)),  ²F₄(2)'.
```

The three on the left are untwisted, and their Steinberg map is the `q`-power Frobenius
`TauCeti.UnimodularLieIndex.frobenius`; they are collected as
`TauCeti.UnimodularExceptionalIndex` and carried through the rest of the recipe here. The three on
the right take an odd power of a half-Frobenius instead, so their Steinberg map is not built in
this file; what they gain here is the ambient group it will be an endomorphism of, and the
Frobenius its square is to be compared with.

The predicate is about the diagram alone, so it says nothing about which Steinberg map an index
takes. That is exactly why it is the right hypothesis for the carrier: `²F₄(2^(2m+1))` and
`²F₄(2)'` live inside the points of the same pinned group scheme as `F₄(q)`, and `²G₂(3^(2m+1))`
inside the same one as `G₂(q)`, whatever endomorphism is later taken of them. The Suzuki family
`²B₂(2^(2m+1))` does *not* appear: its underlying diagram is `B₂`, whose Cartan matrix has
determinant two, so the Geck carrier is not its simply connected form and a full-weight carrier of
its own is still owed.

Nothing here asserts that a constructed group is finite, perfect, or simple, that the ambient
carrier is reductive, or that its weight torus is maximal; those are outside this roadmap. The
`Aₙ`, `²Aₙ`, `Bₙ`, `Cₙ`, `Dₙ`, `²Dₙ`, `E₆`, `²E₆`, `E₇`, `³D₄` and `²B₂` families need a carrier
built from a full-weight representation of their own, so this file covers six of the seventeen
Lie-type constructors of `TauCeti.LieTypeIndex` and no more.

## Main definitions

* `TauCeti.LieTypeIndex.HasUnimodularDiagram`: the indices whose underlying Dynkin diagram has
  unimodular Cartan matrix, and `TauCeti.UnimodularLieIndex`, the corresponding subtype of valid
  indices, whose six branches are `TauCeti.UnimodularLieIndex.e8`, `f4`, `g2`, `reeG2`, `reeF4`
  and `tits`.
* `TauCeti.UnimodularLieIndex.AmbientGroup`: the pinned ambient group, the points of the Geck
  carrier of the underlying Dynkin type over the algebraic closure of the prime field.
* `TauCeti.UnimodularLieIndex.rootSubgroup`: the numbered root subgroups of that group.
* `TauCeti.UnimodularLieIndex.frobenius`: the `q`-power Frobenius of the ambient group, for `q`
  the field order recorded by the index.
* `TauCeti.UnimodularExceptionalIndex`: the unimodular indices whose Steinberg map is not a
  half-Frobenius power, that is `E₈(q)`, `F₄(q)` and `G₂(q)`, with
  `TauCeti.UnimodularExceptionalIndex.steinberg` their Steinberg map and
  `TauCeti.UnimodularExceptionalIndex.Group` the candidate simple group, the derived subgroup of
  the fixed points of that map modulo the centre of that derived subgroup.

## Main results

* `TauCeti.LieTypeIndex.hasUnimodularDiagram_iff_dynkinType` and
  `TauCeti.LieTypeIndex.exists_eq_of_hasUnimodularDiagram`: the predicate says exactly that the
  underlying diagram is `E₈`, `F₄` or `G₂`, and the six families above exhaust it.
* `TauCeti.UnimodularLieIndex.span_range_geckWeight_eq_top`: the Geck weights of such an index
  span the whole character lattice, so its Geck carrier is the simply connected form.
* `TauCeti.UnimodularLieIndex.isClosedImmersion_geckWeightTorus`: consequently the pinned split
  torus is a closed subgroup scheme of the ambient carrier.
* `TauCeti.UnimodularLieIndex.frobenius_rootSubgroup`: the Frobenius raises the parameter of every
  numbered root subgroup to the `q`-th power. On the untwisted branches this is
  `TauCeti.UnimodularExceptionalIndex.steinberg_rootSubgroup`, the equation milestone L1 asks of
  them.
* `TauCeti.UnimodularLieIndex.mem_fixedSubgroup_frobenius_iff`: the fixed points of the Frobenius
  are the points of the carrier whose matrix entries lie in the field of definition `𝔽_q` recorded
  by `TauCeti.ValidLieTypeIndex.fixedField`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates VII--IX, for the unimodularity
  of the `E₈`, `F₄` and `G₂` Cartan matrices.

## Roadmap

This supplies the milestone L0 construction of `TauCetiRoadmap/CFSGStatement/README.md` on the six
branches above -- `AmbientGroup` and `rootSubgroup` are its pinned ambient group and root
subgroups -- and the milestone L1 and L3 constructions on the three untwisted ones, where
`steinberg` is the map `Frob_q` with its simple-root-subgroup equation and `Group` is the composite
`[H_d, H_d] / Z([H_d, H_d])`. What the `²G₂`, `²F₄` and Tits branches still lack is their Steinberg
map: it is an odd power of the special isogeny `τ` of milestone L2, and `τ` itself is a Layer 9
target of `TauCetiRoadmap/ReductiveGroups/README.md` that this roadmap consumes rather than builds.
The relation `τ ^ 2 = Frob_p` that L2 records will be read against `frobenius` here. It consumes
the pinned Chevalley--Demazure carrier of that same Layer 9 rather than restating it, so what the
layer still owes -- the reductivity of the carrier and the identification of its root datum with
`TauCeti.DynkinType.simplyConnectedRootDatum` -- is still owed after this file, for these branches
as for every other.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace LieTypeIndex

/-- The Lie-type families whose underlying Dynkin diagram has unimodular Cartan matrix, namely
`E₈`, `F₄` and `G₂`. These are exactly the CFSG indices whose pinned adjoint Geck carrier is
already the simply connected form.

Both the untwisted families `E₈(q)`, `F₄(q)`, `G₂(q)` and the Ree families `²G₂(3^(2m+1))`,
`²F₄(2^(2m+1))` together with the Tits index are included: the predicate constrains the diagram
and not the Steinberg map, which is what makes it the hypothesis the ambient carrier needs. -/
def HasUnimodularDiagram : LieTypeIndex → Prop
  | .E8 _ | .F4 _ | .G2 _ | .reeG2 _ | .reeF4 _ | .tits => True
  | _ => False

/-- Characterization of the families with unimodular diagram. -/
@[simp] theorem hasUnimodularDiagram_iff (d : LieTypeIndex) : d.HasUnimodularDiagram ↔
    match d with
    | .E8 _ | .F4 _ | .G2 _ | .reeG2 _ | .reeF4 _ | .tits => True
    | _ => False :=
  Iff.rfl

instance : DecidablePred HasUnimodularDiagram := fun d => by
  cases d <;> rw [hasUnimodularDiagram_iff] <;> infer_instance

/-- **An index has unimodular diagram exactly when its underlying Dynkin type is `E₈`, `F₄` or
`G₂`.** The Suzuki family is the one Suzuki--Ree constructor left out, its diagram being `B₂`. -/
theorem hasUnimodularDiagram_iff_dynkinType (d : LieTypeIndex) :
    d.HasUnimodularDiagram ↔
      (d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2) := by
  cases d <;> simp

/-- **The six families with unimodular diagram.** -/
theorem exists_eq_of_hasUnimodularDiagram {d : LieTypeIndex} (hd : d.HasUnimodularDiagram) :
    (∃ q : PrimePower, d = .E8 q ∨ d = .F4 q ∨ d = .G2 q) ∨
      (∃ m : ℕ, d = .reeG2 m ∨ d = .reeF4 m) ∨ d = .tits := by
  cases d <;> simp_all

/-- **The three untwisted families with unimodular diagram.** Removing the Suzuki--Ree
constructors from the previous list leaves `E₈(q)`, `F₄(q)` and `G₂(q)`. -/
theorem exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius {d : LieTypeIndex}
    (hd : d.HasUnimodularDiagram) (hf : ¬d.UsesHalfFrobenius) :
    ∃ q : PrimePower, d = .E8 q ∨ d = .F4 q ∨ d = .G2 q := by
  cases d <;> simp_all

end LieTypeIndex

/-- A valid CFSG index whose underlying Dynkin diagram has unimodular Cartan matrix. Like
`TauCeti.GraphTwistedIndex` and `TauCeti.SuzukiReeIndex` this is a subtype of
`TauCeti.ValidLieTypeIndex`, so no branch of it is a value invented to fill a hole. -/
abbrev UnimodularLieIndex : Type :=
  {d : ValidLieTypeIndex // d.1.HasUnimodularDiagram}

namespace UnimodularLieIndex

noncomputable section

variable (d : UnimodularLieIndex)

/-- The index `E₈(q)`. -/
abbrev e8 (q : PrimePower) : UnimodularLieIndex :=
  ⟨⟨.E8 q, by simp⟩, by simp⟩

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularLieIndex :=
  ⟨⟨.F4 q, by simp⟩, by simp⟩

/-- The index `G₂(q)`, for `q` at least three: `G₂(2)` is excluded from the classification list,
its recipe producing a group already named `²A₂(3)`. -/
abbrev g2 (q : PrimePower) (hq : 3 ≤ q.card) : UnimodularLieIndex :=
  ⟨⟨.G2 q, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq, not_false⟩⟩, by simp⟩

/-- The Ree index `²G₂(3^(2m+1))`, for `m` at least one: `²G₂(3)` is excluded from the
classification list, its recipe producing a group already named `A₁(8)`. -/
abbrev reeG2 (m : ℕ) (hm : 1 ≤ m) : UnimodularLieIndex :=
  ⟨⟨.reeG2 m, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩⟩, by simp⟩

/-- The Ree index `²F₄(2^(2m+1))`, for `m` at least one: at `m = 0` the recipe returns the Tits
group `²F₄(2)'`, which the classification list carries under the separate name `tits`. -/
abbrev reeF4 (m : ℕ) (hm : 1 ≤ m) : UnimodularLieIndex :=
  ⟨⟨.reeF4 m, by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩⟩, by simp⟩

/-- The Tits index `²F₄(2)'`. -/
abbrev tits : UnimodularLieIndex :=
  ⟨⟨.tits, by simp⟩, by simp⟩

/-- The underlying untwisted Dynkin diagram of an index with unimodular diagram. -/
abbrev dynkinType : DynkinType := d.1.dynkinType

/-- That diagram is a valid Dynkin type, so the pinned Geck carrier of the root-systems roadmap is
available for it. -/
theorem dynkinType_valid : d.dynkinType.Valid := d.1.dynkinType_valid

/-- The underlying Dynkin type of an index with unimodular diagram is one of the three unimodular
types. -/
theorem dynkinType_eq_E8_or_eq_F4_or_eq_G2 :
    d.dynkinType = .E8 ∨ d.dynkinType = .F4 ∨ d.dynkinType = .G2 :=
  (LieTypeIndex.hasUnimodularDiagram_iff_dynkinType d.1.1).mp d.2

/-- **The Geck weights of an index with unimodular diagram span the whole character lattice.** This
is what makes its adjoint Geck carrier the simply connected form, and hence the ambient group the
CFSG recipe asks for. -/
theorem span_range_geckWeight_eq_top :
    Submodule.span ℤ (Set.range (d.dynkinType.geckWeight d.dynkinType_valid)) = ⊤ :=
  (DynkinType.span_range_geckWeight_eq_top_iff _ d.dynkinType_valid).mpr
    d.dynkinType_eq_E8_or_eq_F4_or_eq_G2

/-- **The pinned split torus is a closed subgroup scheme of the ambient carrier.** This is the
torus half of the pinning, and it is exactly what the full character span of
`TauCeti.UnimodularLieIndex.span_range_geckWeight_eq_top` buys. -/
theorem isClosedImmersion_geckWeightTorus :
    IsClosedImmersion (d.dynkinType.geckWeightTorus d.dynkinType_valid).hom.hom.left :=
  DynkinType.isClosedImmersion_geckWeightTorus_of_span_eq_top _ d.dynkinType_valid
    d.span_range_geckWeight_eq_top

/-! ## The ambient group and its root subgroups -/

/-- **The pinned ambient group of an index with unimodular diagram**: the points of the pinned Geck
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

/-! ## The Frobenius endomorphism -/

/-- **The `q`-power Frobenius endomorphism of the ambient group**, for `q` the field order recorded
by the index.

On the three untwisted branches this is the Steinberg map
`TauCeti.UnimodularExceptionalIndex.steinberg`. On the `²G₂`, `²F₄` and Tits branches it is not:
their Steinberg map is an odd power of a half-Frobenius, and this map is the square of it. -/
def frobenius : AmbientGroup d →* AmbientGroup d :=
  d.dynkinType.geckFrobenius d.dynkinType_valid d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Frobenius is that of the pinned Geck carrier at the exponent recorded by the index. This is
its unfolding lemma; the definition itself stays sealed. -/
theorem frobenius_def : d.frobenius =
    d.dynkinType.geckFrobenius d.dynkinType_valid d.1.characteristic d.1.fieldExponent
      d.1.Closure := by
  rw [frobenius]

/-- The Frobenius acts on the ambient group by raising every matrix entry to the `q`-th power. -/
@[simp]
theorem coe_frobenius_apply (g : AmbientGroup d)
    (r c : Fin (d.dynkinType.geckDim d.dynkinType_valid)) :
    ((d.frobenius g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c ^ d.1.fieldOrder := by
  rw [d.1.fieldOrder_eq_characteristic_pow]
  exact d.dynkinType.coe_geckFrobenius_apply d.dynkinType_valid _ _ _ g r c

/-- **The Frobenius raises the parameter of every numbered root subgroup to the `q`-th power.** On
a simple root subgroup this is the equation `Frob_q (x_α(t)) = x_α(t ^ q)` that milestone L1
requires of the untwisted families. -/
@[simp]
theorem frobenius_rootSubgroup (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank)
    (u : Multiplicative d.1.Closure) :
    d.frobenius (d.rootSubgroup i u) =
      d.rootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [d.1.fieldOrder_eq_characteristic_pow]
  exact d.dynkinType.geckFrobenius_geckRootSubgroupMatrix d.dynkinType_valid
    d.1.characteristic d.1.fieldExponent d.1.Closure i u

/-- **A point of the ambient group is fixed by the Frobenius exactly when all of its matrix entries
lie in the field of definition.** Writing `𝔽_q` for `TauCeti.ValidLieTypeIndex.fixedField`, the copy
of the field of `q` elements inside the algebraic closure, the Frobenius-fixed group is therefore
the group of points of the pinned carrier whose entries lie in `𝔽_q`.

This is deliberately not a `simp` lemma: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus` against the
identity, so `simp` rewrites its left-hand side to `d.frobenius g = g` through the Mathlib `simp`
lemma `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects the annotation. -/
theorem mem_fixedSubgroup_frobenius_iff (g : AmbientGroup d) :
    g ∈ fixedSubgroup d.frobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) :
        Matrix (Fin (d.dynkinType.geckDim d.dynkinType_valid))
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.1.Closure) r c ∈
        d.1.fixedField := by
  rw [mem_fixedSubgroup, frobenius_def,
    d.dynkinType.geckFrobenius_eq_self_iff d.dynkinType_valid _ _ _ g]
  simp only [mem_frobeniusFixedSubring, ValidLieTypeIndex.mem_fixedField,
    d.1.fieldOrder_eq_characteristic_pow]

end

end UnimodularLieIndex

/-! ## The untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)` -/

/-- An index with unimodular diagram whose Steinberg map is not an odd power of a half-Frobenius.
By `TauCeti.LieTypeIndex.exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius` these are
exactly the three untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)`; the condition removes the Ree
families `²G₂(3^(2m+1))` and `²F₄(2^(2m+1))` and the Tits index, which share their diagrams. -/
abbrev UnimodularExceptionalIndex : Type :=
  {d : UnimodularLieIndex // ¬d.1.1.UsesHalfFrobenius}

namespace UnimodularExceptionalIndex

noncomputable section

variable (d : UnimodularExceptionalIndex)

/-- The index `E₈(q)`. -/
abbrev e8 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.e8 q, by simp⟩

/-- The index `F₄(q)`. -/
abbrev f4 (q : PrimePower) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.f4 q, by simp⟩

/-- The index `G₂(q)`, for `q` at least three. -/
abbrev g2 (q : PrimePower) (hq : 3 ≤ q.card) : UnimodularExceptionalIndex :=
  ⟨UnimodularLieIndex.g2 q hq, by simp⟩

/-- **The Steinberg endomorphism of an untwisted unimodular exceptional index**: the `q`-power
Frobenius of the ambient group, where `q` is the field order recorded by the index. The three
families this covers are untwisted, so no diagram automorphism and no half-Frobenius enters. -/
def steinberg : UnimodularLieIndex.AmbientGroup d.1 →* UnimodularLieIndex.AmbientGroup d.1 :=
  d.1.frobenius

/-- The Steinberg map of an untwisted unimodular exceptional index is the Frobenius of its ambient
group. This is its unfolding lemma; the definition itself stays sealed.

It is deliberately not a `simp` lemma: `steinberg_rootSubgroup` and `coe_steinberg_apply` are the
normal forms the pinned equations of this file are stated against, and unfolding to
`TauCeti.UnimodularLieIndex.frobenius` would keep them from firing. -/
theorem steinberg_eq_frobenius : d.steinberg = d.1.frobenius := by
  rw [steinberg]

/-- The Steinberg map acts on the ambient group by raising every matrix entry to the `q`-th
power. -/
@[simp]
theorem coe_steinberg_apply (g : UnimodularLieIndex.AmbientGroup d.1)
    (r c : Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) :
    ((d.steinberg g : Matrix.GeneralLinearGroup
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix _ _ d.1.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix _ _ d.1.1.Closure) r c ^ d.1.1.fieldOrder := by
  rw [steinberg_eq_frobenius]
  exact d.1.coe_frobenius_apply g r c

/-- **The Steinberg map raises the parameter of every numbered root subgroup to the `q`-th
power.** On a simple root subgroup this is the equation `Frob_q (x_α(t)) = x_α(t ^ q)` that
milestone L1 requires of the untwisted families. -/
@[simp]
theorem steinberg_rootSubgroup (i : Fin d.1.dynkinType.rank ⊕ Fin d.1.dynkinType.rank)
    (u : Multiplicative d.1.1.Closure) :
    d.steinberg (d.1.rootSubgroup i u) =
      d.1.rootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.1.fieldOrder)) := by
  rw [steinberg_eq_frobenius]
  exact d.1.frobenius_rootSubgroup i u

/-- **A point of the ambient group is fixed by the Steinberg map exactly when all of its matrix
entries lie in the field of definition.** Writing `𝔽_q` for
`TauCeti.ValidLieTypeIndex.fixedField`, the copy of the field of `q` elements inside the algebraic
closure, the fixed group `H_d` of milestone L3 is therefore the group of points of the pinned
carrier whose entries lie in `𝔽_q`.

As for `TauCeti.UnimodularLieIndex.mem_fixedSubgroup_frobenius_iff`, this is not a `simp` lemma:
`simp` rewrites its left-hand side through `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects
the annotation. -/
theorem mem_fixedSubgroup_steinberg_iff (g : UnimodularLieIndex.AmbientGroup d.1) :
    g ∈ fixedSubgroup d.steinberg ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.1.Closure) :
        Matrix (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid))
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.1.Closure) r c ∈
        d.1.1.fixedField := by
  rw [steinberg_eq_frobenius]
  exact d.1.mem_fixedSubgroup_frobenius_iff g

/-- **The candidate simple group of an untwisted unimodular exceptional index**: the derived
subgroup of the fixed points of its Steinberg map, modulo the centre of that derived subgroup.

This is the CFSG recipe on the `E₈`, `F₄` and `G₂` branches. Nothing below asserts that it is
finite, perfect, or simple. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

/-- Milestone L3 asks every valid branch to carry a group instance; the quotient construction
supplies it. -/
example : _root_.Group d.Group := inferInstance

end

end UnimodularExceptionalIndex

end TauCeti
