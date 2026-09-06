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

Those relations are then read on the Steinberg map itself. Because the two factors commute, its
`m`-th power in the endomorphism monoid of the carrier separates as `γ ^ m ∘ Frob_(q ^ m)`, so at
`m` the twist order `e` the graph factor disappears and

```text
F ^ e = Frob_(q ^ e).
```

That is the group-of-points analogue of the power relation which defines a Steinberg endomorphism,
namely that some positive iterate is a Frobenius; calling `F` a Steinberg endomorphism in
Steinberg's sense would need this carrier identified with the pinned simply connected group, which
is not done here. The relation places the subgroup of the carrier fixed by `F` inside the
subgroup fixed by `Frob_(q ^ e)`, whose points have their entries in the degree-`e` extension
`𝔽_(q ^ e)` of the field of definition. Only that inequality of subgroups is proved: no reverse
inequality is stated, and nothing below compares the two in size. In the other direction, what is
proved is that a point fixed by both factors is fixed by the composite. On the nine untwisted
families the twist order is `1`, and there the Steinberg map is the Frobenius outright, by
`geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one`.

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
yet the pinned simply connected Chevalley--Demazure group of
`TauCeti.DynkinType.simplyConnectedRootDatum`. No declaration below asserts that it is, nor that
any group here is finite, perfect or simple. In particular the fixed subgroups below are named as
the fixed points of the maps built here; that they are the group of rational points of a family of
the classification list needs that same identification, and no declaration below anticipates it.
For the three untwisted unimodular families, where the carrier does have full character span, the
group so obtained is `TauCeti.UnimodularExceptionalIndex.Group`.

This file stands to `TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Steinberg.lean` as
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean` stands to
`TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Frobenius.lean`: the same map one layer up, on
points instead of on the root datum.

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
* `TauCeti.GraphTwistedIndex.geckGraphAut_pow_geckRootSubgroup`: its `m`-th power renumbers them by
  `σ ^ m`.
* `TauCeti.GraphTwistedIndex.geckGraphAut_geckWeightTorus`: it relabels the coordinates of a
  weight-torus point by the inverse of that permutation.
* `TauCeti.GraphTwistedIndex.geckGraphAut_pow_twistOrder`: the twist order of the index annihilates
  the graph automorphism.
* `TauCeti.GraphTwistedIndex.geckGraphAut_comp_geckFrobenius`: the graph automorphism commutes with
  the Frobenius, so `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckGraphAut_comp` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_comp` are the same map.
* `TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup`: the Steinberg map raises the
  parameter of every numbered root subgroup to the `q`-th power and renumbers it by the diagram
  permutation.
* `TauCeti.GraphTwistedIndex.geckSteinberg_geckWeightTorus`: it raises every coordinate of a
  weight-torus point to the `q`-th power and relabels them by the inverse of that permutation.
* `TauCeti.GraphTwistedIndex.geckWeightTorus_mem_fixedSubgroup_geckSteinberg`: a weight-torus point
  satisfying the resulting twisted equations `s_{σ⁻¹ k} ^ q = s_k` is fixed by the Steinberg map.
* `TauCeti.GraphTwistedIndex.geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one`: on an untwisted
  family it is the Frobenius.
* `TauCeti.GraphTwistedIndex.geckSteinberg_pow_eq_geckGraphAut_pow_comp`,
  `TauCeti.GraphTwistedIndex.geckSteinberg_pow_eq_geckFrobenius_pow_comp` and
  `TauCeti.GraphTwistedIndex.geckSteinberg_pow_geckRootSubgroup`: a power separates, in either
  order, into a power of the graph automorphism and an iterate of the Frobenius, and so renumbers a
  root subgroup by `σ ^ m` and raises its parameter to the `q ^ m`-th power.
* `TauCeti.GraphTwistedIndex.geckSteinberg_pow_twistOrder_eq_geckFrobenius_pow`: the order
  relation `F ^ e = Frob_(q ^ e)` on the Steinberg map itself.
* `TauCeti.GraphTwistedIndex.mem_fixedSubgroup_geckSteinberg_iff`: a point is Steinberg-fixed
  exactly when its entrywise Frobenius image is its conjugate by the matrix of the pinned
  coordinate permutation.
* `TauCeti.GraphTwistedIndex.fixedSubgroup_geckSteinberg_le_fixedSubgroup_geckFrobenius_pow` and
  `TauCeti.GraphTwistedIndex.mem_frobeniusFixedSubfield_of_mem_fixedSubgroup_geckSteinberg`: the
  Steinberg-fixed points lie among the points over `𝔽_(q ^ e)`, entrywise.
* `TauCeti.GraphTwistedIndex.fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_geckSteinberg`: a
  point fixed by both factors is Steinberg-fixed.
* `TauCeti.UnimodularExceptionalIndex.steinberg_eq_geckSteinberg`: it agrees with the Steinberg map
  already attached to `E₈(q)`, `F₄(q)` and `G₂(q)`.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15 and
  1.17, for the graph-twisted Steinberg endomorphisms and their conventions.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs Amer. Math. Soc. **80** (1968),
  §11.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, for the matrix realization of the carrier.
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
  rw [geckGraphAut_def]
  simp only [ValidLieTypeIndex.geckRootSubgroup_eq_mk]
  exact d.1.dynkinType.geckGraphAutPoints_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure i u

/-- **The graph automorphism relabels the coordinates of a weight-torus point** by the inverse of
the diagram permutation, leaving the torus itself invariant. This is the torus half of the pinning
equation that `TauCeti.GraphTwistedIndex.geckGraphAut_geckRootSubgroup` states on root
subgroups. -/
@[simp]
theorem geckGraphAut_geckWeightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.geckGraphAut (d.1.geckWeightTorus s) =
      d.1.geckWeightTorus fun k => s (d.diagramPerm⁻¹ k) := by
  rw [geckGraphAut_def, ValidLieTypeIndex.geckWeightTorus_def]
  exact d.1.dynkinType.geckGraphAutPoints_geckWeightTorusPoints d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure s

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

/-- **The Steinberg map raises every coordinate of a weight-torus point to the `q`-th power and
relabels them by the inverse of the diagram permutation.** This is the equation the map satisfies
on the second half of the pinned data, beside
`TauCeti.GraphTwistedIndex.geckSteinberg_geckRootSubgroup` on the root subgroups. -/
@[simp]
theorem geckSteinberg_geckWeightTorus (s : Fin d.1.rank → d.1.Closureˣ) :
    d.geckSteinberg (d.1.geckWeightTorus s) =
      d.1.geckWeightTorus fun k => s (d.diagramPerm⁻¹ k) ^ d.1.fieldOrder := by
  rw [geckSteinberg_apply, ValidLieTypeIndex.geckFrobenius_geckWeightTorus,
    geckGraphAut_geckWeightTorus]
  exact congrArg _ (funext fun k => Pi.pow_apply s d.1.fieldOrder _)

/-- **A weight-torus point satisfying the twisted equations of an index is fixed by its Steinberg
map.** On an untwisted family, where the diagram permutation is the identity, the condition says
that every coordinate lies in the field of definition `𝔽_q`; on a graph-twisted family it couples
instead the coordinates that the permutation exchanges. -/
theorem geckWeightTorus_mem_fixedSubgroup_geckSteinberg (s : Fin d.1.rank → d.1.Closureˣ)
    (hs : ∀ k, s (d.diagramPerm⁻¹ k) ^ d.1.fieldOrder = s k) :
    d.1.geckWeightTorus s ∈ fixedSubgroup d.geckSteinberg := by
  rw [mem_fixedSubgroup, geckSteinberg_geckWeightTorus]
  exact congrArg _ (funext hs)

/-- **On a family whose diagram permutation is trivial the Steinberg map is the plain Frobenius.**
Those are the nine untwisted constructors, where the printed family name carries no superscript. -/
theorem geckSteinberg_eq_geckFrobenius_of_diagramPerm_eq_one (h : d.diagramPerm = 1) :
    d.geckSteinberg = d.1.geckFrobenius := by
  refine MonoidHom.ext fun g => ?_
  rw [geckSteinberg_apply, geckGraphAut_eq_one_of_diagramPerm_eq_one d h, MulAut.one_apply]

/-! ## The powers of the Steinberg map

The iterates of the Steinberg map are its powers in the endomorphism monoid of the carrier, as they
are at the layer below in `TauCeti.DynkinType.geckTwistedFrobenius_pow`. -/

-- `Monoid.End` is definitionally a bundled `MonoidHom`, and the `show` in each statement below
-- picks its composition monoid structure before the power is elaborated.

/-- **The `m`-th power of the graph automorphism renumbers the root subgroups by the `m`-th power
of the diagram permutation**, again leaving their parameters alone. -/
@[simp]
theorem geckGraphAut_pow_geckRootSubgroup (m : ℕ) (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    (d.geckGraphAut ^ m) (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup ((DynkinType.diagramRootGeneratorPerm d.diagramPerm ^ m) i) u := by
  rw [geckGraphAut_def]
  simp only [ValidLieTypeIndex.geckRootSubgroup_eq_mk]
  exact d.1.dynkinType.geckGraphAutPoints_pow_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.Closure m i u

/-- **The powers of the ordinary Steinberg map separate into a power of the graph automorphism and
an iterate of the Frobenius**: `(γ ∘ Frob_q) ^ m = γ ^ m ∘ Frob_(q ^ m)`. The separation is exactly
the commutation `geckGraphAut_comp_geckFrobenius` of the two factors; without it a power would only
be an alternating word in them. -/
theorem geckSteinberg_pow_eq_geckGraphAut_pow_comp (m : ℕ) :
    (show Monoid.End _ from d.geckSteinberg) ^ m =
      (d.geckGraphAut ^ m).toMonoidHom.comp
        ((show Monoid.End _ from d.1.geckFrobenius) ^ m) := by
  rw [ValidLieTypeIndex.geckFrobenius_pow, geckSteinberg_def, geckGraphAut_def]
  exact DynkinType.geckTwistedFrobenius_pow d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure m

/-- **The powers of the ordinary Steinberg map separate in the other order too**, since its two
factors commute: `(γ ∘ Frob_q) ^ m = Frob_(q ^ m) ∘ γ ^ m`. This is the power form of
`geckSteinberg_eq_geckFrobenius_comp`. -/
theorem geckSteinberg_pow_eq_geckFrobenius_pow_comp (m : ℕ) :
    (show Monoid.End _ from d.geckSteinberg) ^ m =
      ((show Monoid.End _ from d.1.geckFrobenius) ^ m).comp
        (d.geckGraphAut ^ m).toMonoidHom := by
  rw [ValidLieTypeIndex.geckFrobenius_pow, geckSteinberg_def, geckGraphAut_def]
  exact DynkinType.geckTwistedFrobenius_pow_eq_geckFrobenius_comp d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure m

/-- **The order relation of the ordinary Steinberg map**: raising `γ ∘ Frob_q` to the twist order
`e` recorded by the index returns the plain Frobenius `Frob_(q ^ e)`.

This is the annihilation `γ ^ 2 = 1`, `γ ^ 3 = 1` of the graph factor read on the Steinberg map
itself, and it is the group-layer counterpart of
`TauCeti.GraphTwistedIndex.datumSteinberg_pow_twistOrder_eq_smulId`. It is the group-of-points
analogue of the power relation which defines a Steinberg endomorphism, some positive iterate being
a Frobenius; that this carrier is the group on which Steinberg's definition is read needs its
identification with the pinned simply connected group, and is not claimed here. On an untwisted
family the twist order is `1` and the relation is `pow_one` on both sides. -/
@[simp]
theorem geckSteinberg_pow_twistOrder_eq_geckFrobenius_pow :
    (show Monoid.End _ from d.geckSteinberg) ^ d.twistOrder =
      (show Monoid.End _ from d.1.geckFrobenius) ^ d.twistOrder := by
  rw [ValidLieTypeIndex.geckFrobenius_pow, geckSteinberg_def]
  exact DynkinType.geckTwistedFrobenius_pow_eq_geckFrobenius d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure
    d.diagramPerm_pow_twistOrder

/-- **The `m`-th power of the Steinberg map renumbers a root subgroup by the `m`-th power of the
diagram permutation and raises its parameter to the `q ^ m`-th power.** At the twist order the
renumbering disappears, which is `geckSteinberg_pow_twistOrder_eq_geckFrobenius_pow` read on the
root subgroups. -/
@[simp]
theorem geckSteinberg_pow_geckRootSubgroup (m : ℕ) (i : Fin d.1.rank ⊕ Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    ((show Monoid.End _ from d.geckSteinberg) ^ m) (d.1.geckRootSubgroup i u) =
      d.1.geckRootSubgroup ((DynkinType.diagramRootGeneratorPerm d.diagramPerm ^ m) i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder ^ m)) := by
  rw [geckSteinberg_def, d.1.fieldOrder_eq_characteristic_pow, ← pow_mul]
  simp only [ValidLieTypeIndex.geckRootSubgroup_eq_mk]
  exact DynkinType.geckTwistedFrobenius_pow_geckRootSubgroupMatrix d.1.dynkinType_valid
    d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent d.1.Closure m i u

/-! ## The fixed points of the Steinberg map -/

/-- **A point of the Geck point group is fixed by the Steinberg map exactly when its entrywise
`q`-power Frobenius image is its conjugate by the matrix of the pinned coordinate permutation.**
This is the graph-twisted form of the descent condition that
`TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff` records on the nine untwisted
families, where the matrix is the identity and the condition is that every entry lies in `𝔽_q`. -/
-- As for that lemma, this is not a `simp` lemma: `TauCeti.fixedSubgroup` is `MonoidHom.eqLocus`
-- against the identity, so `simp` rewrites its left-hand side to `d.geckSteinberg g = g` through
-- the Mathlib `simp` lemma `MonoidHom.mem_eqLocus`, and the `simpNF` linter rejects the annotation.
theorem mem_fixedSubgroup_geckSteinberg_iff (g : ValidLieTypeIndex.GeckGroup d.1) :
    g ∈ fixedSubgroup d.geckSteinberg ↔
      Matrix.GeneralLinearGroup.map
          (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)
          (g : Matrix.GeneralLinearGroup
            (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) =
        (d.1.dynkinType.geckGraphAutMatrix d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry d.1.Closure)⁻¹ *
          (g : Matrix.GeneralLinearGroup
            (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) *
          d.1.dynkinType.geckGraphAutMatrix d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry d.1.Closure := by
  rw [mem_fixedSubgroup, geckSteinberg_def,
    d.1.dynkinType.geckTwistedFrobenius_eq_self_iff d.1.dynkinType_valid
      d.diagramPerm_mem_diagramSymmetry _ _ _ g]

/-- **The Steinberg-fixed points are fixed by the twist-order iterate of the Frobenius.** For a
graph-twisted family this is the containment of the points fixed by `F` in the points fixed by
`Frob_(q ^ e)`, those whose entries lie in the degree-`e` extension of the field of definition. No
reverse inequality is stated. -/
theorem fixedSubgroup_geckSteinberg_le_fixedSubgroup_geckFrobenius_pow :
    fixedSubgroup d.geckSteinberg ≤
      fixedSubgroup ((show Monoid.End _ from d.1.geckFrobenius) ^ d.twistOrder) := by
  rw [geckSteinberg_def, ValidLieTypeIndex.geckFrobenius_pow]
  exact DynkinType.fixedSubgroup_geckTwistedFrobenius_le_fixedSubgroup_geckFrobenius
    d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent
    d.1.Closure d.diagramPerm_pow_twistOrder

/-- **The matrix entries of a Steinberg-fixed point lie in the degree-`e` extension of the field of
definition**, `e` being the twist order recorded by the index: `𝔽_q` itself on the nine untwisted
families, `𝔽_(q ^ 2)` on `²Aₙ`, `²Dₙ` and `²E₆`, and `𝔽_(q ^ 3)` on `³D₄`. The degree-`e` extension
is the field over which the ambient untwisted group of a graph-twisted family is defined, in the
small-field GLS/ATLAS convention on `q` that the index records. -/
theorem mem_frobeniusFixedSubfield_of_mem_fixedSubgroup_geckSteinberg
    {g : ValidLieTypeIndex.GeckGroup d.1} (hg : g ∈ fixedSubgroup d.geckSteinberg)
    (r c : Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) :
    ((g : Matrix.GeneralLinearGroup
        (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) :
      Matrix (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid))
        (Fin (d.1.dynkinType.geckDim d.1.dynkinType_valid)) d.1.Closure) r c ∈
      frobeniusFixedSubfield d.1.Closure d.1.characteristic
        (d.1.fieldExponent * d.twistOrder) :=
  (ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_pow_iff _ _ _).mp
    (d.fixedSubgroup_geckSteinberg_le_fixedSubgroup_geckFrobenius_pow hg) r c

/-- **A point fixed by both the Frobenius and the graph automorphism is fixed by the Steinberg
map.** No converse is stated: a point fixed by the composite is not shown to be fixed by either
factor. -/
theorem fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_geckSteinberg :
    fixedSubgroup d.1.geckFrobenius ⊓ fixedSubgroup d.geckGraphAut.toMonoidHom ≤
      fixedSubgroup d.geckSteinberg := by
  rw [geckSteinberg_def, ValidLieTypeIndex.geckFrobenius_def, geckGraphAut_def]
  exact DynkinType.fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_geckTwistedFrobenius
    d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry d.1.characteristic d.1.fieldExponent
    d.1.Closure

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
