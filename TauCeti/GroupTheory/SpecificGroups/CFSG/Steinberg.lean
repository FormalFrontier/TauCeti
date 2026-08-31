/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.RootDatumAutomorphism
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.TwistedFrobenius

/-!
# The graph-twisted Steinberg map of a Lie-type index

The Steinberg endomorphism of a family on the classification list that is not of Suzuki--Ree type
is `γ ∘ Frob_q`, the `q`-power Frobenius composed with the graph automorphism realizing the pinned
diagram permutation `TauCeti.GraphTwistedIndex.diagramPerm`. This file builds that composite on the
Geck carrier, for every `TauCeti.GraphTwistedIndex`, and proves there the equations milestone L1
asks of it.

Both factors are already available on the carrier. The Frobenius is
`TauCeti.ValidLieTypeIndex.geckFrobenius`, and the graph factor is the automorphism of the points
of the pinned Geck carrier attached to a symmetry of its numbered Dynkin diagram,
`TauCeti.DynkinType.geckGraphAutPoints`, whose input is exactly
`TauCeti.GraphTwistedIndex.diagramPerm_mem_diagramSymmetry`. The only step taken here is to read
one as the other, exactly as `TauCeti/GroupTheory/SpecificGroups/CFSG/RootDatumAutomorphism.lean`
does for the root-datum shadow of the same map.

## What the equations say

The permutation attached to an index moves the *raising and lowering generators together*, through
`TauCeti.DynkinType.diagramRootGeneratorPerm`, so the pinning equation reads

```text
γ (x_i(u)) = x_{σ i}(u),        F (x_i(u)) = x_{σ i}(u ^ q)
```

on the Bourbaki-numbered root subgroups of the carrier, with the parameter untouched by `γ`. This
is milestone L1's `γ (x_α(t)) = x_{γ α}(t)` on the simple root subgroups, and its composite with
the Frobenius; nothing is claimed about a non-simple root, where the corresponding equation carries
the signs `ε_α = ±1` the roadmap warns of. The other two relations L1 requires are the order
relation `TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`, which is `γ ^ 2 = 1` on `²Aₙ`,
`²Dₙ` and `²E₆` and `γ ^ 3 = 1` on `³D₄`, and the commutation of `γ` with `Frob_q`,
`TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`, which is what lets the composite be
taken in either order and what makes its twist-order iterate the Frobenius `Frob_(q ^ e)` of the
larger field, `TauCeti.GraphTwistedIndex.geckSteinberg_iterate_twistOrder_eq_geckFrobenius`.

## The carrier

Every name here carries the `geck` prefix, for the reason
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` gives: Geck's module is the adjoint
module, so the characters occurring in it generate the root lattice and not, in general, the whole
character lattice of the pinned torus, and this carrier is therefore **not** the pinned simply
connected Chevalley--Demazure group that milestone L0 asks for. The three diagrams `Aₙ`, `Dₙ` and
`E₆` carrying the four genuinely twisted families are not among the unimodular ones, so unlike the
untwisted `E₈`, `F₄` and `G₂` of `TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean` these
branches cannot drop the prefix: the names `TauCeti.ValidLieTypeIndex.steinberg` and
`TauCeti.ValidLieTypeIndex.Group` are left free for the L0 carrier, no fixed-point subgroup of
`geckSteinberg` is formed, and nothing below asserts that the carrier is reductive or that any
group is finite, perfect or simple.

On the three unimodular untwisted branches this construction agrees with the Steinberg map already
built there, which is `TauCeti.UnimodularExceptionalIndex.steinberg_eq_geckSteinberg`. It is *not*
compared with `TauCeti.TypeALieIndex.steinberg`, which is the same recipe on a different carrier,
the explicit type-`A` special linear one of
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`: relating two carriers of one diagram needs
the isomorphism theorem for pinned groups, a Layer 9 target of
`TauCetiRoadmap/ReductiveGroups/README.md`, and asserting the two agree without it is exactly what
the `geck` prefix exists to prevent.

## Main definitions

* `TauCeti.GraphTwistedIndex.geckGraphAut`: the graph automorphism of the Geck point group of a
  graph-twisted index.
* `TauCeti.GraphTwistedIndex.geckSteinberg`: its Steinberg map `γ ∘ Frob_q` on that group.

## Main results

* `TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup`: the pinning equations on the numbered
  root subgroups.
* `TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`: the order relation of the graph factor.
* `TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_comp`: the two factors commute, so the
  composite may be taken in either order.
* `TauCeti.GraphTwistedIndex.geckSteinberg_iterate_twistOrder_eq_geckFrobenius` and
  `TauCeti.GraphTwistedIndex.coe_geckSteinberg_iterate_twistOrder_apply`: iterating the Steinberg
  map to the twist order gives the Frobenius of the field of that degree.
* `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one`: on an untwisted
  family the Steinberg map is the Frobenius itself.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs Amer. Math. Soc. **80** (1968),
  §11.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, for the carrier.

## Roadmap

This is the group-level half of milestone L1, "ordinary and graph Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose table sets the Steinberg map of `²A`, `²D` and
`²E₆` to `γ₂ ∘ Frob_q` with `γ₂ ^ 2 = 1`, that of `³D₄` to `γ₃ ∘ Frob_q` with `γ₃ ^ 3 = 1`, and
that of the nine untwisted families to `Frob_q`, and which requires in each case that `γ` commute
with `Frob_q`. The diagram-permutation half is
`TauCeti/GroupTheory/SpecificGroups/CFSG/GraphTwisted.lean` and the root-datum shadow of the whole
composite is `TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Steinberg.lean`. What L1 still lacks
after this file is the same construction on the L0 carrier, which waits on the identification of
that carrier with this one, a Layer 9 target of `TauCetiRoadmap/ReductiveGroups/README.md` that
this roadmap consumes rather than builds.
-/

public section

namespace TauCeti

namespace GraphTwistedIndex

noncomputable section

variable (d : GraphTwistedIndex)

/-! ## The graph automorphism -/

/-- **The graph automorphism of the Geck point group of a graph-twisted index**: the automorphism
of the points of the pinned Geck carrier realizing the index's pinned diagram permutation. It is
the identity on the nine untwisted families, where that permutation is the identity.

Every carrier attached to an index in this directory is a group of points, so this is
`TauCeti.DynkinType.geckGraphAutPoints` and not the automorphism
`TauCeti.DynkinType.geckGraphAut` of the group scheme itself; the two are compared upstream. -/
def geckGraphAut : MulAut (ValidLieTypeIndex.GeckGroup d.1) :=
  d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.Closure

/-- The graph automorphism is that of the pinned Geck carrier at the index's diagram permutation.
This is its unfolding lemma; the definition itself stays sealed. -/
theorem geckGraphAut_def : d.geckGraphAut =
    d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
      d.1.Closure := by
  rw [geckGraphAut]

/-- **The graph automorphism renumbers the root subgroups by the diagram permutation**, leaving
their additive parameter alone. On a raising index this is the equation `γ (x_α(t)) = x_{γ α}(t)`
that milestone L1 asks of the graph-twisted families on the simple root subgroups, proved here on
the Geck carrier. -/
@[simp]
theorem geckGraphAut_geckRootSubgroup (i : Fin d.1.dynkinType.rank ⊕ Fin d.1.dynkinType.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckGraphAut (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i) u := by
  rw [geckGraphAut_def, d.1.geckRootSubgroup_apply i u, d.1.geckRootSubgroup_apply _ u]
  exact d.1.dynkinType.geckGraphAutPoints_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure i u

/-- **The order relation of the graph automorphism.** This is `γ ^ 2 = 1` for `²Aₙ`, `²Dₙ` and
`²E₆`, `γ ^ 3 = 1` for `³D₄`, and the trivial relation on an untwisted family, all read off the
twist order recorded by the index. -/
@[simp]
theorem geckGraphAut_pow_twistOrder : d.geckGraphAut ^ d.twistOrder = 1 := by
  rw [geckGraphAut_def]
  exact DynkinType.geckGraphAutPoints_pow_eq_one d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure d.diagramPerm_pow_twistOrder

/-- **On an untwisted family the graph automorphism is the identity.** -/
theorem geckGraphAut_eq_one_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckGraphAut = 1 := by
  rw [geckGraphAut_def, ← pow_one (DynkinType.geckGraphAutPoints _ _ _)]
  exact DynkinType.geckGraphAutPoints_pow_eq_one d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure (by rw [pow_one, h])

/-- **The graph automorphism commutes with the Frobenius.** This is the second relation milestone
L1 requires of a graph-twisted Steinberg map, read on the Geck point group. -/
theorem geckGraphAut_comp_geckFrobenius :
    d.geckGraphAut.toMonoidHom.comp d.1.geckFrobenius =
      d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [geckGraphAut_def, d.1.geckFrobenius_def]
  exact DynkinType.geckGraphAutPoints_comp_geckFrobenius d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure

/-! ## The Steinberg map -/

/-- **The Steinberg endomorphism of a graph-twisted index on its Geck point group**: the `q`-power
Frobenius followed by the graph automorphism, for `q` the field order recorded by the index. The
two factors commute, so the composite is the same in either order. -/
def geckSteinberg : ValidLieTypeIndex.GeckGroup d.1 →* ValidLieTypeIndex.GeckGroup d.1 :=
  d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map is the graph-twisted Frobenius of the pinned Geck carrier at the diagram
permutation and field exponent recorded by the index. This is its unfolding lemma; the definition
itself stays sealed. -/
theorem geckSteinberg_def : d.geckSteinberg =
    d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
      d.1.characteristic d.1.fieldExponent d.1.Closure := by
  rw [geckSteinberg]

/-- **The Steinberg map applies the Frobenius first and then the graph automorphism.** -/
theorem geckSteinberg_apply (g : ValidLieTypeIndex.GeckGroup d.1) :
    d.geckSteinberg g = d.geckGraphAut (d.1.geckFrobenius g) := by
  rw [geckSteinberg_def, geckGraphAut_def, d.1.geckFrobenius_def]
  exact DynkinType.geckTwistedFrobenius_apply d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure g

/-- **The Steinberg map is the composite in either order**, the two factors commuting by
`TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`. -/
theorem geckSteinberg_eq_geckFrobenius_comp :
    d.geckSteinberg = d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [← d.geckGraphAut_comp_geckFrobenius]
  exact MonoidHom.ext d.geckSteinberg_apply

/-- **The Steinberg map raises the parameter of every numbered root subgroup to the `q`-th power
and renumbers it by the diagram permutation.** On a raising index this is the equation
`γ ∘ Frob_q (x_α(t)) = x_{γ α}(t ^ q)` that milestone L1 asks of the graph-twisted families on the
simple root subgroups, proved here on the Geck carrier. -/
@[simp]
theorem geckSteinberg_geckRootSubgroup (i : Fin d.1.dynkinType.rank ⊕ Fin d.1.dynkinType.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckSteinberg (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [geckSteinberg_apply, d.1.geckFrobenius_geckRootSubgroup, geckGraphAut_geckRootSubgroup]

/-- The two factors of the Steinberg map commute, pointwise. -/
private theorem geckGraphAut_geckFrobenius (x : ValidLieTypeIndex.GeckGroup d.1) :
    d.geckGraphAut (d.1.geckFrobenius x) = d.1.geckFrobenius (d.geckGraphAut x) :=
  DFunLike.congr_fun d.geckGraphAut_comp_geckFrobenius x

/-- The Frobenius commutes with every power of the graph automorphism. -/
private theorem geckFrobenius_geckGraphAut_pow (n : ℕ) (x : ValidLieTypeIndex.GeckGroup d.1) :
    d.1.geckFrobenius ((d.geckGraphAut ^ n) x) = (d.geckGraphAut ^ n) (d.1.geckFrobenius x) := by
  induction n generalizing x with
  | zero => rw [pow_zero, MulAut.one_apply, MulAut.one_apply]
  | succ n ih => rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, geckGraphAut_geckFrobenius]

/-- The `n`-th iterate of the Steinberg map is the `n`-th power of the graph automorphism after the
Frobenius at `n` times the field exponent. -/
private theorem geckSteinberg_iterate (n : ℕ) (g : ValidLieTypeIndex.GeckGroup d.1) :
    d.geckSteinberg^[n] g =
      (d.geckGraphAut ^ n) (d.1.dynkinType.geckFrobenius d.1.dynkinType_valid d.1.characteristic
        (n * d.1.fieldExponent) d.1.Closure g) := by
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, pow_zero, MulAut.one_apply, Nat.zero_mul,
        DynkinType.geckFrobenius_zero, MonoidHom.id_apply]
  | succ n ih =>
      have hadd : d.1.dynkinType.geckFrobenius d.1.dynkinType_valid d.1.characteristic
            ((n + 1) * d.1.fieldExponent) d.1.Closure =
          d.1.geckFrobenius.comp (d.1.dynkinType.geckFrobenius d.1.dynkinType_valid
            d.1.characteristic (n * d.1.fieldExponent) d.1.Closure) := by
        rw [d.1.geckFrobenius_def, ← DynkinType.geckFrobenius_add, Nat.succ_mul, Nat.add_comm]
      rw [Function.iterate_succ_apply', ih, geckSteinberg_apply, geckFrobenius_geckGraphAut_pow,
        ← MulAut.mul_apply, ← pow_succ', hadd, MonoidHom.comp_apply]

/-- **Iterating the Steinberg map to the twist order gives the Frobenius of the field of that
degree.** The graph factor is annihilated by the twist order and commutes with the Frobenius, so
each of the `e` factors contributes its own `q` and the iterate is `Frob_(q ^ e)`, the Frobenius at
field exponent `e * k` for `q = p ^ k`. This is the defining property of a Steinberg endomorphism
in Steinberg's sense, on this carrier; the corresponding statement on the pinned root datum is
`TauCeti.GraphTwistedIndex.datumSteinberg_pow_twistOrder_eq_smulId`. -/
theorem geckSteinberg_iterate_twistOrder_eq_geckFrobenius :
    d.geckSteinberg^[d.twistOrder] =
      ⇑(d.1.dynkinType.geckFrobenius d.1.dynkinType_valid d.1.characteristic
        (d.twistOrder * d.1.fieldExponent) d.1.Closure) :=
  funext fun g => by
    rw [d.geckSteinberg_iterate d.twistOrder g, d.geckGraphAut_pow_twistOrder, MulAut.one_apply]

/-- **Entrywise, iterating the Steinberg map to the twist order raises every matrix entry to the
`q ^ e`-th power**, for `e` the twist order. It is the reading of
`TauCeti.GraphTwistedIndex.geckSteinberg_iterate_twistOrder_eq_geckFrobenius` which exhibits the
field of the iterate as `𝔽_(q ^ e)`: the twisted families are the ones whose Steinberg map is not
itself a Frobenius, but a power of which is. -/
theorem coe_geckSteinberg_iterate_twistOrder_apply (g : ValidLieTypeIndex.GeckGroup d.1)
    (r c : Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) :
    ((d.geckSteinberg^[d.twistOrder] g : Matrix.GeneralLinearGroup
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) :
        Matrix _ _ d.1.Closure) r c ^ d.1.fieldOrder ^ d.twistOrder := by
  rw [congrFun d.geckSteinberg_iterate_twistOrder_eq_geckFrobenius g,
    DynkinType.coe_geckFrobenius_apply,
    d.1.fieldOrder_eq_characteristic_pow, ← pow_mul, Nat.mul_comm]

/-- **On an untwisted family the Steinberg map is the Frobenius itself.** -/
theorem geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckSteinberg = d.1.geckFrobenius :=
  MonoidHom.ext fun g => by
    rw [geckSteinberg_apply, d.geckGraphAut_eq_one_of_diagramPerm_eq_one h, MulAut.one_apply]

/-- **The Steinberg map is the Frobenius whenever the family name carries no superscript**, the
twist order of a graph-twisted index being the order of its diagram permutation. -/
theorem geckSteinberg_eq_geckFrobenius_of_twistOrder_eq_one (h : d.twistOrder = 1) :
    d.geckSteinberg = d.1.geckFrobenius :=
  d.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one
    (orderOf_eq_one_iff.mp ((orderOf_diagramPerm d).trans h))

end

end GraphTwistedIndex

/-! ## The untwisted unimodular exceptional branches -/

namespace UnimodularExceptionalIndex

/-- An untwisted unimodular exceptional index, regarded as a graph-twisted index. The condition
cutting `TauCeti.UnimodularExceptionalIndex` out of `TauCeti.UnimodularLieIndex` is exactly the one
cutting `TauCeti.GraphTwistedIndex` out of `TauCeti.ValidLieTypeIndex`, so `E₈(q)`, `F₄(q)` and
`G₂(q)` carry a diagram permutation, which is the identity. -/
abbrev toGraphTwistedIndex (d : UnimodularExceptionalIndex) : GraphTwistedIndex := ⟨d.1.1, d.2⟩

/-- The diagram permutation of an untwisted unimodular exceptional index is the identity: `E₈`,
`F₄` and `G₂` have no nontrivial diagram symmetry. -/
@[simp]
theorem diagramPerm_toGraphTwistedIndex (d : UnimodularExceptionalIndex) :
    d.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨⟨⟨e, hv⟩, hu⟩, hh⟩ := d
  -- every constructor is either not unimodular, or a half-Frobenius one, or one of the three
  -- untwisted families the pinned table already assigns the identity permutation to
  cases e <;> first
    | (exfalso; rw [LieTypeIndex.hasUnimodularDiagram_iff] at hu; exact hu)
    | exact absurd ((LieTypeIndex.usesHalfFrobenius_iff _).mpr trivial) hh
    | exact GraphTwistedIndex.diagramPerm_E8 hv
    | exact GraphTwistedIndex.diagramPerm_F4 hv
    | exact GraphTwistedIndex.diagramPerm_G2 hv

/-- **The Steinberg map of an untwisted unimodular exceptional index is its graph-twisted Steinberg
map.** The two constructions are stated on different subtypes, `E₈(q)`, `F₄(q)` and `G₂(q)` lying in
both; on that overlap the diagram permutation is the identity and they agree. -/
theorem steinberg_eq_geckSteinberg (d : UnimodularExceptionalIndex) :
    d.steinberg = d.toGraphTwistedIndex.geckSteinberg := by
  rw [d.steinberg_eq_geckFrobenius,
    d.toGraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one
      d.diagramPerm_toGraphTwistedIndex]

end UnimodularExceptionalIndex

end TauCeti
