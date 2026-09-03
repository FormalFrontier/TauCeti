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
# The ordinary Steinberg map of a Lie-type index on the Geck carrier

Thirteen of the seventeen Lie-type constructors take an *ordinary* Steinberg endomorphism, the
field Frobenius composed with a graph automorphism of the pinned ambient group; the remaining four
take an odd power of a half-Frobenius instead. `TauCeti.GraphTwistedIndex` is exactly the subtype
of the first thirteen, and `TauCeti.GraphTwistedIndex.diagramPerm` already attaches to each of them
the permutation `σ` of the Bourbaki-numbered simple roots that its graph automorphism realizes.
This file realizes that permutation on the carrier: it produces the graph automorphism
`TauCeti.GraphTwistedIndex.geckGraphAut` of the Geck point group of the index and composes it with
the `q`-power Frobenius, giving `TauCeti.GraphTwistedIndex.geckSteinberg`.

Both halves already exist and are joined rather than rebuilt. On the diagram side,
`TauCeti.GraphTwistedIndex.diagramPerm_mem_diagramSymmetry` reads `σ` as a symmetry of the
Bourbaki-numbered Cartan matrix; on the carrier side, that is exactly what
`TauCeti.DynkinType.geckGraphAutPoints` and `TauCeti.DynkinType.geckTwistedFrobenius` consume. The
work here is the assignment of one to the other, and the resulting equations in the shape milestone
L1 states them, on the numbered root subgroups of `TauCeti.ValidLieTypeIndex.geckRootSubgroup`:

```text
γ (x_i(u)) = x_{σ i}(u),        F (x_i(u)) = x_{σ i}(u ^ q),
```

together with the two relations that milestone requires of the graph factor, namely that `γ`
commutes with the Frobenius and that the twist order recorded by the index annihilates it,
`γ ^ 2 = 1` on `²Aₙ`, `²Dₙ` and `²E₆` and `γ ^ 3 = 1` on `³D₄`.

The nine untwisted families are indices of this subtype too, with `σ = 1`, so the construction is
total on the thirteen ordinary constructors and degenerates to the plain Frobenius exactly where
the printed family name carries no superscript. On the three untwisted families whose diagram is
unimodular that degeneration is
`TauCeti.UnimodularExceptionalIndex.steinberg_eq_geckSteinberg`, which identifies the map built
here with the Steinberg map those three branches already carry, so the uniform map extends the
special case rather than competing with it.

The `geck` prefix is the same disclaimer it carries in
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean`. Geck's module is the adjoint module, so
outside the `E₈`, `F₄` and `G₂` diagrams the characters occurring in the carrier generate the root
lattice and not the whole character lattice of the pinned torus, and the carrier is therefore not
yet the simply connected group that milestone L0 asks for. No declaration below asserts that it is,
nor that any group here is finite, perfect or simple, and no fixed-point subgroup is formed on a
branch whose carrier has not been identified.

## Main definitions

* `TauCeti.GraphTwistedIndex.geckGraphAut`: the graph automorphism of the Geck point group of an
  ordinary Lie-type index, realizing its pinned diagram permutation.
* `TauCeti.GraphTwistedIndex.geckSteinberg`: the ordinary Steinberg map `γ ∘ Frob_q` of that index
  on the same carrier.
* `TauCeti.UnimodularExceptionalIndex.toGraphTwistedIndex`: the three untwisted unimodular
  families `E₈(q)`, `F₄(q)` and `G₂(q)` as ordinary indices.

## Main results

* `TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup`: the graph automorphism renumbers the
  root subgroups by the diagram permutation and leaves their parameters alone.
* `TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`: the twist order of the index annihilates
  the graph automorphism.
* `TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`: the graph automorphism commutes with
  the Frobenius, so `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckGraphAut_comp` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_comp` are the same map.
* `TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup`: the Steinberg map raises the
  parameter of every numbered root subgroup to the `q`-th power and renumbers it by the diagram
  permutation.
* `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one`: on an untwisted
  family it is the Frobenius.
* `TauCeti.UnimodularExceptionalIndex.steinberg_eq_geckSteinberg`: it agrees with the Steinberg map
  already attached to `E₈(q)`, `F₄(q)` and `G₂(q)`.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the graph-twisted Steinberg endomorphisms and their conventions.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs Amer. Math. Soc. **80** (1968),
  §11.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, for the matrix realization of the carrier.

## Roadmap

This is the carrier layer of milestone L1, "ordinary and graph Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose completion condition is that "the simple-root-
subgroup equations and the order relations are proved". Those equations and relations are proved
here for all thirteen ordinary indices at once, in the shape the milestone states them and against
the diagram permutations that `TauCeti/GroupTheory/SpecificGroups/CFSG/GraphTwisted.lean` pins.

It does not close L1, and it does not close milestone L0: the carrier is the Geck one, whose
identification with the pinned simply connected Chevalley--Demazure group of
`TauCeti.DynkinType.simplyConnectedRootDatum` is a Layer 9 target of
`TauCetiRoadmap/ReductiveGroups/README.md` that this roadmap consumes rather than proves. This file
stands to `TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Steinberg.lean` as
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` stands to
`TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Frobenius.lean`: the same map one layer up, on
points instead of on the root datum.
-/

public section

namespace TauCeti

namespace GraphTwistedIndex

noncomputable section

variable (d : GraphTwistedIndex)

/-! ## The graph automorphism of the Geck point group -/

/-- **The graph automorphism of the Geck point group of an ordinary Lie-type index**: the
automorphism of the carrier realizing the index's pinned diagram permutation, namely conjugation by
the matrix of the induced permutation of the Geck coordinates. It is the identity on the nine
untwisted families, where that permutation is the identity.

It is an automorphism of the Geck carrier, which is not claimed to be the pinned simply connected
Chevalley--Demazure group that milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for. -/
def geckGraphAut : MulAut (ValidLieTypeIndex.GeckGroup d.1) :=
  d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.Closure

/-- The graph automorphism of an index is that of the pinned Geck carrier at the index's own
diagram permutation. This is its unfolding lemma; the definition itself stays sealed. -/
theorem geckGraphAut_def : d.geckGraphAut =
    d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
      d.1.Closure := by
  rw [geckGraphAut]

/-- The graph automorphism acts on the Geck point group by conjugation by the matrix of the pinned
coordinate permutation. -/
@[simp]
theorem coe_geckGraphAut (g : ValidLieTypeIndex.GeckGroup d.1) :
    (d.geckGraphAut g : Matrix.GeneralLinearGroup
        (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) =
      d.1.dynkinType.geckGraphAutMatrix d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
          d.1.Closure * g *
        (d.1.dynkinType.geckGraphAutMatrix d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
          d.1.Closure)⁻¹ := by
  rw [geckGraphAut_def]
  exact d.1.dynkinType.coe_geckGraphAutPoints d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure g

/-- **The graph automorphism renumbers the root subgroups by the diagram permutation and leaves
their parameters alone.** On a simple root subgroup this is the equation `γ (x_α(t)) = x_{γ α}(t)`
that milestone L1 asks of the graph factor of a graph-twisted Steinberg map, proved here on the
Geck carrier. The same node permutation acts on the raising and on the lowering generators. -/
@[simp]
theorem geckGraphAut_geckRootSubgroup (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckGraphAut (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i) u := by
  -- Both sides are read through `ValidLieTypeIndex.coe_geckRootSubgroup`, since the body of
  -- `ValidLieTypeIndex.geckRootSubgroup` is not exposed.
  have h := congrArg Subtype.val (d.1.dynkinType.geckGraphAutPoints_geckRootSubgroupMatrix
    d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry d.1.Closure i u)
  rw [DynkinType.coe_geckGraphAutPoints] at h
  refine Subtype.ext ?_
  rw [coe_geckGraphAut, ValidLieTypeIndex.coe_geckRootSubgroup,
    ValidLieTypeIndex.coe_geckRootSubgroup]
  exact h

/-- **The twist order recorded by an index annihilates its graph automorphism.** This is `γ ^ 2 = 1`
for `²Aₙ`, `²Dₙ` and `²E₆`, `γ ^ 3 = 1` for `³D₄`, and the trivial relation on an untwisted family,
which is the order relation milestone L1 requires of the graph factor. -/
@[simp]
theorem geckGraphAut_pow_twistOrder : d.geckGraphAut ^ d.twistOrder = 1 := by
  rw [geckGraphAut_def]
  exact DynkinType.geckGraphAutPoints_pow_eq_one d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure d.diagramPerm_pow_twistOrder

/-- **An index whose diagram permutation is trivial has trivial graph automorphism**, which is the
case of the nine untwisted families. -/
theorem geckGraphAut_eq_one_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckGraphAut = 1 := by
  -- The diagram permutation occurs in the type of the membership proof, so it is generalized
  -- before being rewritten to the identity; the two membership proofs then agree by proof
  -- irrelevance.
  have key : ∀ σ : Equiv.Perm (Fin d.1.rank), σ = 1 →
      ∀ hσ : σ ∈ d.1.dynkinType.diagramSymmetry,
        d.1.dynkinType.geckGraphAutPoints d.1.dynkinType_valid hσ d.1.Closure = 1 := by
    rintro σ rfl hσ
    exact DynkinType.geckGraphAutPoints_one d.1.dynkinType_valid d.1.Closure
  rw [geckGraphAut_def]
  exact key _ h d.diagramPerm_mem_diagramSymmetry

/-! ## The ordinary Steinberg map -/

/-- **The ordinary Steinberg map of a Lie-type index on its Geck point group**: the pinned graph
automorphism after the `q`-power Frobenius, for `q` the field order recorded by the index. It is
defined on the thirteen constructors whose Steinberg map is not an odd power of a half-Frobenius,
and the four that are excluded are not indices of this subtype, so no value is invented for
them. -/
def geckSteinberg :
    ValidLieTypeIndex.GeckGroup d.1 →* ValidLieTypeIndex.GeckGroup d.1 :=
  d.1.dynkinType.geckTwistedFrobenius d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.1.characteristic d.1.fieldExponent d.1.Closure

/-- The Steinberg map of an index is the graph-twisted Frobenius of the pinned Geck carrier at the
index's own diagram permutation and field exponent. This is its unfolding lemma; the definition
itself stays sealed. -/
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
L1 requires of a graph-twisted Steinberg map, read on the Geck point group. -/
theorem geckGraphAut_comp_geckFrobenius :
    d.geckGraphAut.toMonoidHom.comp d.1.geckFrobenius =
      d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [geckGraphAut_def, ValidLieTypeIndex.geckFrobenius_def]
  exact d.1.dynkinType.geckGraphAutPoints_comp_geckFrobenius d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure

/-- **The defining factorization of the Steinberg map**, the graph automorphism after the
Frobenius. -/
theorem geckSteinberg_eq_geckGraphAut_comp :
    d.geckSteinberg = d.geckGraphAut.toMonoidHom.comp d.1.geckFrobenius :=
  MonoidHom.ext fun g => d.geckSteinberg_apply g

/-- **The Steinberg map is the same composite in the other order**, since its two factors
commute. -/
theorem geckSteinberg_eq_geckFrobenius_comp :
    d.geckSteinberg = d.1.geckFrobenius.comp d.geckGraphAut.toMonoidHom := by
  rw [geckSteinberg_eq_geckGraphAut_comp, geckGraphAut_comp_geckFrobenius]

/-- **The Steinberg map raises the parameter of every numbered root subgroup to the `q`-th power
and renumbers it by the diagram permutation.** On a simple root subgroup this is the equation
`F (x_{α_i}(t)) = x_{α_{σ i}}(t ^ q)` that milestone L1 asks of an ordinary Steinberg map, proved
here on the Geck carrier for all thirteen ordinary families at once. -/
@[simp]
theorem geckSteinberg_geckRootSubgroup (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.geckSteinberg (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup (DynkinType.diagramRootGeneratorPerm d.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [geckSteinberg_apply, ValidLieTypeIndex.geckFrobenius_geckRootSubgroup,
    geckGraphAut_geckRootSubgroup]

/-- **On a family whose diagram permutation is trivial the Steinberg map is the plain Frobenius.**
Those are the nine untwisted constructors, where the printed family name carries no superscript. -/
theorem geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckSteinberg = d.1.geckFrobenius := by
  refine MonoidHom.ext fun g => ?_
  rw [geckSteinberg_apply, geckGraphAut_eq_one_of_diagramPerm_eq_one d h, MulAut.one_apply]

end

end GraphTwistedIndex

/-! ## The three untwisted unimodular families -/

namespace UnimodularExceptionalIndex

variable (d : UnimodularExceptionalIndex)

/-- An index with unimodular diagram whose Steinberg map is not a half-Frobenius power, regarded as
an ordinary index. These are the three untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)`, none of
which carries a diagram symmetry. -/
abbrev toGraphTwistedIndex : GraphTwistedIndex := ⟨d.1.1, d.2⟩

/-- The diagram permutation of an untwisted unimodular exceptional index is the identity: the
`E₈`, `F₄` and `G₂` diagrams have no nontrivial symmetry, and none of the three families is
twisted. -/
theorem diagramPerm_toGraphTwistedIndex : d.toGraphTwistedIndex.diagramPerm = 1 := by
  obtain ⟨⟨⟨e, hv⟩, hu⟩, hf⟩ := d
  obtain ⟨q, rfl | rfl | rfl⟩ :=
    LieTypeIndex.exists_eq_of_hasUnimodularDiagram_of_not_usesHalfFrobenius hu hf
  · exact GraphTwistedIndex.diagramPerm_E8 hv
  · exact GraphTwistedIndex.diagramPerm_F4 hv
  · exact GraphTwistedIndex.diagramPerm_G2 hv

/-- **The Steinberg map already attached to `E₈(q)`, `F₄(q)` and `G₂(q)` is the ordinary Steinberg
map of the same index.** The uniform construction of this file therefore extends the untwisted
special case of `TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean` rather than competing
with it. -/
theorem steinberg_eq_geckSteinberg :
    d.steinberg = d.toGraphTwistedIndex.geckSteinberg := by
  rw [steinberg_eq_geckFrobenius,
    GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one _
      d.diagramPerm_toGraphTwistedIndex]

end UnimodularExceptionalIndex

end TauCeti
