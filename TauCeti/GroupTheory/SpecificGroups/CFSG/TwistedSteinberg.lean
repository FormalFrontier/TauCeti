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
# The graph-twisted Steinberg map of a Lie-type index, on the Geck carrier

The Steinberg endomorphism of a finite group of Lie type that is not of Suzuki--Ree type is
`γ ∘ Frob_q`, the field Frobenius composed with the graph automorphism realizing the index's pinned
diagram permutation. `TauCeti.ValidLieTypeIndex.geckFrobenius` already supplies the second factor on
the points of the pinned Geck carrier, for every valid index. This file supplies the first factor
and the composite, for every `TauCeti.GraphTwistedIndex`, and proves the equations milestone L1
requires of them.

Both halves already exist upstream and are joined here rather than rebuilt.
`TauCeti.DynkinType.geckGraphAutPoints` turns a symmetry of the Bourbaki-numbered Cartan matrix into
an automorphism of the carrier's points, and
`TauCeti.GraphTwistedIndex.diagramPerm_mem_diagramSymmetry` reads the index's own pinned diagram
permutation as such a symmetry; `TauCeti.DynkinType.geckTwistedFrobenius` is the composite of that
automorphism with the Frobenius. The assignment is total on `TauCeti.GraphTwistedIndex` and defined
nowhere else, so no diagram automorphism is invented for a family whose Steinberg map is an odd
power of a half-Frobenius.

## What milestone L1 asks for, and what is proved here

The roadmap's table sets the Steinberg map of the nine untwisted families to `Frob_q` and that of
`²Aₙ(q)`, `²Dₙ(q)`, `²E₆(q)` and `³D₄(q)` to `γ ∘ Frob_q`, with the required relations
`γ ^ 2 = 1` on `²Aₙ`, `²Dₙ` and `²E₆` and `γ ^ 3 = 1` on `³D₄`, that is `γ ^ n = 1` for `n` the
superscript printed in the family name, and that `γ` commutes with `Frob_q`, and with the defining
equation `γ (x_α(t)) = x_{γ α}(t)` on the simple root subgroups. All four are below:
`TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`,
`TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`,
`TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup_inl`, and, for the composite,
`TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup_inl`. The equation on the simple root
subgroups is deliberately not strengthened to arbitrary roots: on a general root it carries signs
forced by the Chevalley structure constants, and a pinning normalizes only the simple ones.

The numbering is the pinned Bourbaki one throughout. A Geck root subgroup is indexed by
`Fin d.1.rank ⊕ Fin d.1.rank`, the left summand carrying the raising generators `x_{α_i}` and the
right the lowering generators `x_{-α_i}`, and the graph automorphism moves both halves by the same
node permutation, `TauCeti.DynkinType.diagramRootGeneratorPerm`.

## Which carrier this is, and which it is not

The names carry the `geck` prefix for the reason
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` gives: Geck's module is the adjoint
module, so its weights generate the root lattice and not, in general, the whole character lattice of
the pinned torus, and the identification of this carrier with the pinned simply connected
Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` is Layer 9 work of
`TauCetiRoadmap/ReductiveGroups/README.md`. So `TauCeti.ValidLieTypeIndex.AmbientGroup`,
`TauCeti.ValidLieTypeIndex.steinberg` and `TauCeti.GraphTwistedIndex.graphAut` are left free, no
declaration below asserts that this carrier is reductive or simply connected, and no fixed-point
subgroup, derived subgroup or central quotient is formed here. The one place where the lattice
condition does hold is `TauCeti.UnimodularLieIndex`, and there the composite is already
`TauCeti.UnimodularExceptionalIndex.steinberg`: the three unimodular diagrams `E₈`, `F₄` and `G₂`
have no nontrivial symmetry, so the graph factor is trivial on every unimodular graph-twisted index,
which is `TauCeti.UnimodularExceptionalIndex.geckSteinberg_toGraphTwistedIndex` below.

## Main definitions

* `TauCeti.GraphTwistedIndex.geckGraphAut`: the graph automorphism of the Geck point group
  realizing the index's pinned diagram permutation.
* `TauCeti.GraphTwistedIndex.geckSteinberg`: the graph-twisted Steinberg map `γ ∘ Frob_q` of the
  Geck point group.

## Main results

* `TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup` and
  `TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup_inl`: the graph automorphism renumbers
  the root subgroups without touching their parameter, which on a raising generator is milestone
  L1's `γ (x_{α_i}(t)) = x_{α_{σ i}}(t)`.
* `TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`: `γ ^ 2 = 1` on `²Aₙ`, `²Dₙ` and `²E₆`
  and `γ ^ 3 = 1` on `³D₄`, read off the twist order recorded by the index.
* `TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`: `γ` commutes with `Frob_q`, so the
  Steinberg map is the composite in either order.
* `TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup_inl`: the Steinberg map renumbers a
  root subgroup by the diagram permutation and raises its parameter to the `q`-th power.
* `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one`: on an index
  with trivial diagram permutation, that is on the nine untwisted families, it is the Frobenius
  itself.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the graph automorphisms and the twisted Steinberg endomorphisms.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs Amer. Math. Soc. **80** (1968),
  §11.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*, Proc. Amer. Math.
  Soc. **145** (2017), 3233--3247, for the matrix realization this carrier is built from.

## Roadmap

This is the group layer of milestone L1, "ordinary and graph Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose completion evidence is that "the
simple-root-subgroup equations and the order relations are proved". Its root-datum layer is
`TauCeti.GraphTwistedIndex.datumSteinberg`, which records the same conventions on the pinned simply
connected root datum and states nothing about a group; the module docstring of
`TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Assembly.lean` observes that the group-level
composite "already exists in another form" upstream, "for a diagram symmetry and a field order
handed to it", and this file is the selection of those two arguments for each index. As with
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`, the equations are proved here in the
shape milestone L1 needs them, on a carrier whose identification with the L0 one is owed by Layer 9
of `TauCetiRoadmap/ReductiveGroups/README.md`; they transfer to the L0 carrier along that
identification, and not before. Nothing here touches the Suzuki--Ree and Tits branches, whose
Steinberg map is the odd half-Frobenius power of milestone L2.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

/-- A Geck root-subgroup point, written as an explicit element of the subgroup of `GLₙ` the carrier
cuts out. This is the shape in which the pinned equations are stated upstream, and the only thing
the proofs below need beyond those equations. -/
private theorem geckRootSubgroup_eq (d : ValidLieTypeIndex)
    (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank) (u : Multiplicative d.Closure) :
    d.geckRootSubgroup i u =
      ⟨d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm u),
        d.dynkinType.geckRootSubgroupMatrix_mem_geckPoints d.dynkinType_valid d.Closure i _⟩ :=
  Subtype.ext (d.coe_geckRootSubgroup i u)

end ValidLieTypeIndex

namespace GraphTwistedIndex

noncomputable section

variable (d : GraphTwistedIndex)

/-! ## The graph automorphism on points -/

/-- **The graph automorphism of the Geck point group of a graph-twisted index**: the automorphism
realizing its pinned diagram permutation, obtained by reading that permutation as a symmetry of the
Bourbaki-numbered Cartan matrix. It is the identity on an untwisted family, where the permutation
is the identity. -/
def geckGraphAut :
    ValidLieTypeIndex.GeckGroup d.1 ≃* ValidLieTypeIndex.GeckGroup d.1 :=
  d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.Closure

/-- **The defining equation of the graph automorphism.** The body of `geckGraphAut` is not exposed,
so this is what lets a consumer rewrite it into `TauCeti.DynkinType.geckGraphAutPoints` and then
apply the general lemmas about that construction at `σ = d.diagramPerm`. -/
theorem geckGraphAut_def : d.geckGraphAut =
    d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
      d.1.Closure := by
  rw [geckGraphAut]

/-- **The graph automorphism renumbers the Geck root subgroups and leaves their parameter alone.**
The same node permutation acts on the raising and on the lowering generators, through
`TauCeti.DynkinType.diagramRootGeneratorPerm`. -/
@[simp]
theorem geckGraphAut_geckRootSubgroup (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckGraphAut (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i) u := by
  rw [geckGraphAut_def, ValidLieTypeIndex.geckRootSubgroup_eq,
    ValidLieTypeIndex.geckRootSubgroup_eq]
  exact d.1.dynkinType.geckGraphAutPoints_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure i u

/-- **`γ (x_{α_i}(t)) = x_{α_{σ i}}(t)` on the Bourbaki-numbered simple root subgroups.** This is
the equation that pins the graph automorphism in milestone L1, and it must not be strengthened to
arbitrary roots: there the equation reads `γ (x_α(t)) = x_{γ α}(ε_α t)` with signs `ε_α = ±1` forced
by the Chevalley structure constants. -/
theorem geckGraphAut_geckRootSubgroup_inl (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.geckGraphAut (d.1.geckRootSubgroup (Sum.inl i) u) =
      d.1.geckRootSubgroup (Sum.inl (d.diagramPerm i)) u := by
  rw [geckGraphAut_geckRootSubgroup, DynkinType.diagramRootGeneratorPerm_apply_inl]

/-- The same equation on the lowering generators `x_{-α_i}`, which the graph automorphism moves by
the same node permutation. -/
theorem geckGraphAut_geckRootSubgroup_inr (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.geckGraphAut (d.1.geckRootSubgroup (Sum.inr i) u) =
      d.1.geckRootSubgroup (Sum.inr (d.diagramPerm i)) u := by
  rw [geckGraphAut_geckRootSubgroup, DynkinType.diagramRootGeneratorPerm_apply_inr]

/-- **The order relation of the graph automorphism.** This is `γ ^ 2 = 1` for `²Aₙ`, `²Dₙ` and
`²E₆`, `γ ^ 3 = 1` for `³D₄`, and the trivial relation on an untwisted family, all read off the
twist order recorded by the index. It is the image on points of
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder`, and the group-layer counterpart of
`TauCeti.GraphTwistedIndex.datumGraphAut_pow_twistOrder`. -/
@[simp]
theorem geckGraphAut_pow_twistOrder : d.geckGraphAut ^ d.twistOrder = 1 :=
  d.1.dynkinType.geckGraphAutPoints_pow_eq_one d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure d.diagramPerm_pow_twistOrder

/-- **An index with trivial diagram permutation has trivial graph automorphism**, so on the nine
untwisted families the graph factor of the Steinberg map contributes nothing. -/
theorem geckGraphAut_eq_one_of_diagramPerm_eq_one (h : d.diagramPerm = 1) : d.geckGraphAut = 1 := by
  -- the diagram permutation appears only in the type of the symmetry proof, so substituting it
  -- reduces the claim to the identity symmetry, whose proof is irrelevant.
  have key : ∀ (sigma : Equiv.Perm (Fin d.1.rank))
      (hsigma : sigma ∈ d.1.dynkinType.diagramSymmetry), sigma = 1 →
      d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid hsigma d.1.Closure = 1 := by
    rintro sigma hsigma rfl
    exact d.1.dynkinType.geckGraphAutPoints_one d.1.dynkinType_valid d.1.Closure
  rw [geckGraphAut_def]
  exact key _ d.diagramPerm_mem_diagramSymmetry h

/-! ## The graph-twisted Steinberg map -/

/-- **The graph-twisted Steinberg map of a graph-twisted index, on its Geck point group**: the
`q`-power Frobenius followed by the graph automorphism realizing the index's pinned diagram
permutation, where `q` is the field order recorded by the index. The two factors commute, so the
composite in the other order is the same map. On the nine untwisted families the graph automorphism
is trivial and this is the Frobenius itself. -/
def geckSteinberg :
    ValidLieTypeIndex.GeckGroup d.1 →* ValidLieTypeIndex.GeckGroup d.1 :=
  d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.characteristic d.1.fieldExponent d.1.Closure

/-- **The defining equation of the graph-twisted Steinberg map.** The body of `geckSteinberg` is not
exposed, so this is what lets a consumer rewrite it into
`TauCeti.DynkinType.geckTwistedFrobenius` and reach the general lemmas about that construction,
among them its action on the pinned weight torus. -/
theorem geckSteinberg_def : d.geckSteinberg =
    d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
      d.1.characteristic d.1.fieldExponent d.1.Closure := by
  rw [geckSteinberg]

/-- The Steinberg map applies the Frobenius first and then the graph automorphism. -/
theorem geckSteinberg_apply (g : ValidLieTypeIndex.GeckGroup d.1) :
    d.geckSteinberg g = d.geckGraphAut (d.1.geckFrobenius g) := by
  rw [geckSteinberg_def, geckGraphAut_def, ValidLieTypeIndex.geckFrobenius_def]
  exact d.1.dynkinType.geckTwistedFrobenius_apply d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure g

/-- **The graph automorphism commutes with the Frobenius.** This is the second relation milestone
L1 requires of a graph-twisted Steinberg map, read on the points of the Geck carrier: it holds
because the graph automorphism is conjugation by a permutation matrix, whose entries any ring map
fixes, so it is natural in the value ring. -/
theorem geckGraphAut_comp_geckFrobenius :
    d.geckGraphAut.toMonoidHom.comp d.1.geckFrobenius =
      d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [geckGraphAut_def, ValidLieTypeIndex.geckFrobenius_def]
  exact d.1.dynkinType.geckGraphAutPoints_comp_geckFrobenius d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map is the graph automorphism after the Frobenius. -/
theorem geckSteinberg_eq_geckGraphAut_comp :
    d.geckSteinberg = d.geckGraphAut.toMonoidHom.comp d.1.geckFrobenius :=
  MonoidHom.ext fun g => d.geckSteinberg_apply g

/-- The Steinberg map is the Frobenius after the graph automorphism: the same composite in the
other order, by `TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`. -/
theorem geckSteinberg_eq_geckFrobenius_comp :
    d.geckSteinberg = d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [geckSteinberg_eq_geckGraphAut_comp, geckGraphAut_comp_geckFrobenius]

/-- **The Steinberg map renumbers a Geck root subgroup by the diagram permutation and raises its
parameter to the `q`-th power.** The same node permutation acts on the raising and on the lowering
generators. -/
@[simp]
theorem geckSteinberg_geckRootSubgroup (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckSteinberg (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [d.1.fieldOrder_eq_characteristic_pow, geckSteinberg_def,
    ValidLieTypeIndex.geckRootSubgroup_eq, ValidLieTypeIndex.geckRootSubgroup_eq]
  exact d.1.dynkinType.geckTwistedFrobenius_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure i u

/-- **`F (x_{α_i}(t)) = x_{α_{σ i}}(t ^ q)` on the Bourbaki-numbered simple root subgroups**, the
defining equation of a graph-twisted Steinberg map. On an untwisted family `σ` is the identity and
this is the equation `Frob_q (x_α(t)) = x_α(t ^ q)` of the untwisted lane. -/
theorem geckSteinberg_geckRootSubgroup_inl (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.geckSteinberg (d.1.geckRootSubgroup (Sum.inl i) u) =
      d.1.geckRootSubgroup (Sum.inl (d.diagramPerm i))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [geckSteinberg_geckRootSubgroup, DynkinType.diagramRootGeneratorPerm_apply_inl]

/-- The same equation on the lowering generators `x_{-α_i}`. -/
theorem geckSteinberg_geckRootSubgroup_inr (i : Fin d.1.rank) (u : Multiplicative d.1.Closure) :
    d.geckSteinberg (d.1.geckRootSubgroup (Sum.inr i) u) =
      d.1.geckRootSubgroup (Sum.inr (d.diagramPerm i))
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [geckSteinberg_geckRootSubgroup, DynkinType.diagramRootGeneratorPerm_apply_inr]

/-- **An index with trivial diagram permutation has the plain Frobenius as its Steinberg map.**
This is the degeneration of `γ ∘ Frob_q` on the nine untwisted families, where the roadmap's table
prescribes `Frob_q`. -/
theorem geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckSteinberg = d.1.geckFrobenius := by
  rw [geckSteinberg_eq_geckGraphAut_comp, geckGraphAut_eq_one_of_diagramPerm_eq_one d h]
  exact MonoidHom.ext fun _ => rfl

end

end GraphTwistedIndex

/-! ## The unimodular exceptional families -/

namespace UnimodularExceptionalIndex

variable (e : UnimodularExceptionalIndex)

/-- An index with unimodular diagram whose Steinberg map is not a half-Frobenius power, regarded as
an ordinary-or-graph-twisted index. The three families this covers, `E₈(q)`, `F₄(q)` and `G₂(q)`,
carry a diagram permutation, namely the identity. -/
abbrev toGraphTwistedIndex : GraphTwistedIndex := ⟨e.1.1, e.2⟩

/-- **The three unimodular exceptional diagrams have no nontrivial symmetry.** The `E₈` and `F₄`
diagrams are asymmetric, and the length-exchanging symmetry of `G₂` is not an automorphism of its
Cartan matrix; it enters the classification only through the half-Frobenius of `²G₂`, whose index is
excluded from this subtype. -/
@[simp]
theorem diagramPerm_toGraphTwistedIndex : e.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨⟨⟨d, hd⟩, hu⟩, hf⟩ := e
  obtain ⟨q, rfl | rfl | rfl⟩ :=
    LieTypeIndex.exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius hu hf
  exacts [GraphTwistedIndex.diagramPerm_E8 hd, GraphTwistedIndex.diagramPerm_F4 hd,
    GraphTwistedIndex.diagramPerm_G2 hd]

/-- **The uniform graph-twisted Steinberg map agrees with the one already attached to `E₈(q)`,
`F₄(q)` and `G₂(q)`.** Those three branches are untwisted, so
`TauCeti.UnimodularExceptionalIndex.steinberg`, which is the plain Frobenius, is the value of
`TauCeti.GraphTwistedIndex.geckSteinberg` there and not a second construction. -/
theorem geckSteinberg_toGraphTwistedIndex :
    e.toGraphTwistedIndex.geckSteinberg = e.steinberg := by
  rw [GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one _
      e.diagramPerm_toGraphTwistedIndex,
    steinberg_eq_geckFrobenius]

end UnimodularExceptionalIndex

end TauCeti
