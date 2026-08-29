/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.RootDatumAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic

/-!
# The root-datum Steinberg map of a graph-twisted index

The Steinberg endomorphism attached to a Lie-type index that is not of Suzuki--Ree type is
`γ ∘ Frob_q`, the `q`-power Frobenius of the pinned Chevalley--Demazure group followed by the graph
automorphism realizing the pinned diagram permutation. This file builds the shadow that composite
casts on the pinned simply connected root datum, where both factors are already available:
`TauCeti.RootPairingIsogeny.smulId` at the Frobenius parameter is the root-datum image of `Frob_q`,
and `TauCeti.GraphTwistedIndex.datumGraphAut` is the root-datum image of `γ`.

Two things are worth being precise about. First, this is the root-datum layer and not the group
layer: nothing here mentions a group scheme, its points, or a finite group, and the equations below
are the root-datum images of the equations milestone L1 states about root subgroups, not those
equations themselves. Second, the composite is *defined* in the order `γ ∘ Frob_q` and then proved
to agree with `Frob_q ∘ γ`. That agreement,
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_comp`,
is the root-datum form of the relation "`γ` commutes with `Frob_q`" which L1 requires of the
graph-twisted families, and it comes from the general naturality of scaling among isogenies,
`TauCeti.RootPairingIsogeny.comp_smulId`, at the endo-isogenies of a single datum.

## The orientation of the graph factor

The shadow is read covariantly on the character lattice: the weight map of `datumSteinberg` carries
the root at each index to `q` times the root at the image of that index under the index's *own*
diagram permutation `TauCeti.GraphTwistedIndex.diagramPerm`, which is
`TauCeti.GraphTwistedIndex.datumSteinberg_root_simpleIndex` and is the root-datum image of the
equation `γ (x_α(t)) = x_{γ α}(t)` that milestone L1 pins on the simple root subgroups. That
reading is not chosen here but inherited: `TauCeti.DynkinType.diagramAut` sends a node permutation
`σ` to the datum automorphism whose root enumeration moves by `σ` and not by `σ⁻¹`, which is
`TauCeti.DynkinType.diagramRootPerm_simpleIndex`, and
`TauCeti.GraphTwistedIndex.datumGraphAut` is that automorphism at `σ = d.diagramPerm`.

Reading a group endomorphism through its pullback on characters instead would replace `σ` by `σ⁻¹`
throughout, and the commutation above does not make the two readings agree: it is about the order
of the two factors, not about the orientation of the graph factor, and it holds under either
reading. They differ only on `³D₄`, the one family whose diagram permutation has order greater than
two, where they name the two trialities, and even there the choice is not observable downstream:
an order-two symmetry of the `D₄` diagram conjugates one three-cycle to the other and commutes with
the scaling, so it conjugates one composite to the other.

The construction is faithful in the sense that matters for the classification list: by
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff` the Steinberg map of an index
degenerates to its Frobenius exactly on the nine untwisted families, so `²Aₙ(q)`, `²Dₙ(q)`,
`²E₆(q)` and `³D₄(q)` receive maps that no untwisted index receives.

## Main definitions

* `TauCeti.ValidLieTypeIndex.datumFrobenius`: multiplication by the Frobenius parameter, as an
  isogeny of the pinned simply connected root datum; the root-datum shadow of `Frob_q`.
* `TauCeti.GraphTwistedIndex.datumSteinberg`: the root-datum shadow of the Steinberg map
  `γ ∘ Frob_q`.

## Main results

* `TauCeti.RootPairingIsogeny.comp_smulId` (in the isogeny file): every isogeny intertwines scaling
  on its source with scaling on its target, which is the general form of the required relation.
* `TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_comp`: `γ ∘ Frob_q = Frob_q ∘ γ`.
* `TauCeti.GraphTwistedIndex.datumSteinberg_root` and
  `TauCeti.GraphTwistedIndex.datumSteinberg_root_simpleIndex`: the Steinberg map multiplies the
  root at each index by `q` and moves it along `TauCeti.DynkinType.diagramRootPerm`, which on a
  Bourbaki-numbered simple root is the index's own pinned diagram permutation.
* `TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff` and
  `TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff_twistOrder`: it is the plain
  Frobenius exactly on the untwisted families, equivalently exactly when the twist order is one.

## Roadmap

This is the root-datum layer of milestone L1, "ordinary and graph Steinberg maps", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose table sets the Steinberg map of the untwisted
families to `Frob_q` and that of `²A`, `²D`, `²E₆` and `³D₄` to `γ ∘ Frob_q`, with required
relations `γ ^ 2 = 1`, `γ ^ 3 = 1` and "`γ` commutes with `Frob_q`". The order relations are
already `TauCeti.GraphTwistedIndex.datumGraphAut_pow_twistOrder`; the commutation is proved here.
What remains of L1 after this file is the group layer: `TauCeti.ValidLieTypeIndex.steinberg` and the
equations `γ (x_α(t)) = x_{γ α}(t)` and `Frob_q (x_α(t)) = x_α(t ^ q)` on the root subgroups of the
pinned ambient group, which wait on the carriers of milestone L0. This file stands to the
graph-twisted families as `TauCeti/GroupTheory/SpecificGroups/CFSG/RootDatumAutomorphism.lean`
stands to the graph automorphism alone.

The conventions follow R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80
(1968), §11, and R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.17.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

variable (d : ValidLieTypeIndex)

noncomputable section

/-- **The root-datum shadow of the `q`-power Frobenius** of a valid Lie-type index: multiplication
by the Frobenius parameter on the pinned simply connected root datum. A Frobenius isogeny of a split
group scheme fixes the root datum and multiplies its characters by `q`, so no diagram data enters
here; the twisting of a family is carried entirely by the graph automorphism it is composed with. -/
def datumFrobenius :
    RootPairingIsogeny (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid)
      (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid) :=
  RootPairingIsogeny.smulId _ d.1.fieldOrderPNat

/-- The Frobenius shadow acts on the character lattice as multiplication by `q`. -/
@[simp] theorem datumFrobenius_weightMap :
    d.datumFrobenius.weightMap = d.fieldOrder • LinearMap.id := by
  rw [datumFrobenius, RootPairingIsogeny.smulId_weightMap, LieTypeIndex.coe_fieldOrderPNat]

/-- The Frobenius shadow acts on the cocharacter lattice as multiplication by `q`. -/
@[simp] theorem datumFrobenius_coweightMap :
    d.datumFrobenius.coweightMap = d.fieldOrder • LinearMap.id := by
  rw [datumFrobenius, RootPairingIsogeny.smulId_coweightMap, LieTypeIndex.coe_fieldOrderPNat]

/-- The Frobenius shadow fixes the root enumeration: it rescales the roots and does not move
them. -/
@[simp] theorem datumFrobenius_indexEquiv :
    d.datumFrobenius.indexEquiv = Equiv.refl (Fin d.dynkinType.numRoots) := by
  rw [datumFrobenius, RootPairingIsogeny.smulId_indexEquiv]

/-- The Frobenius shadow rescales every root by `q`. -/
@[simp] theorem datumFrobenius_exponent (k : Fin d.dynkinType.numRoots) :
    d.datumFrobenius.exponent k = (d.fieldOrder : ℤ) := by
  rw [datumFrobenius, RootPairingIsogeny.smulId_exponent, LieTypeIndex.coe_fieldOrderPNat]

end

end ValidLieTypeIndex

namespace GraphTwistedIndex

variable (d : GraphTwistedIndex)

noncomputable section

/-- **The root-datum Steinberg map of a graph-twisted index**: the root-datum shadow of
`γ ∘ Frob_q`, the pinned graph automorphism after the `q`-power Frobenius. The graph factor is
`TauCeti.GraphTwistedIndex.datumGraphAut` itself and not its inverse, so the root enumeration moves
by the index's own diagram permutation; the module docstring records that orientation convention
and what changes under the opposite one. On the nine untwisted families the graph automorphism is
trivial and this is the Frobenius itself, by
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff`. -/
def datumSteinberg :
    RootPairingIsogeny (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid)
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid) :=
  (RootPairingIsogeny.ofEquiv d.datumGraphAut).comp d.1.datumFrobenius

/-- **The graph automorphism commutes with the Frobenius.** This is the second relation milestone
L1 requires of a graph-twisted Steinberg map, read on the pinned root datum: the composite is the
same whichever order the two factors are taken in. -/
theorem datumSteinberg_eq_datumFrobenius_comp :
    d.datumSteinberg =
      d.1.datumFrobenius.comp (RootPairingIsogeny.ofEquiv d.datumGraphAut) := by
  rw [datumSteinberg, ValidLieTypeIndex.datumFrobenius]
  exact RootPairingIsogeny.comp_smulId (RootPairingIsogeny.ofEquiv d.datumGraphAut) _

/-- The Steinberg map acts on the character lattice as multiplication by `q` followed by the weight
map of the graph automorphism. -/
@[simp] theorem datumSteinberg_weightMap :
    d.datumSteinberg.weightMap =
      d.datumGraphAut.toHom.weightMap ∘ₗ (d.1.fieldOrder • LinearMap.id) := by
  rw [datumSteinberg, RootPairingIsogeny.comp_weightMap,
    RootPairingIsogeny.ofEquiv_weightMap, ValidLieTypeIndex.datumFrobenius_weightMap]

/-- The Steinberg map acts on the cocharacter lattice as the coweight map of the graph automorphism
followed by multiplication by `q`. -/
@[simp] theorem datumSteinberg_coweightMap :
    d.datumSteinberg.coweightMap =
      (d.1.fieldOrder • LinearMap.id) ∘ₗ d.datumGraphAut.toHom.coweightMap := by
  rw [datumSteinberg, RootPairingIsogeny.comp_coweightMap,
    RootPairingIsogeny.ofEquiv_coweightMap, ValidLieTypeIndex.datumFrobenius_coweightMap]

/-- The Steinberg map permutes the pinned root enumeration by the permutation
`TauCeti.DynkinType.diagramRootPerm` that the index's diagram permutation induces. -/
@[simp] theorem datumSteinberg_indexEquiv :
    d.datumSteinberg.indexEquiv =
      DynkinType.diagramRootPerm d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry := by
  rw [datumSteinberg, RootPairingIsogeny.comp_indexEquiv, RootPairingIsogeny.ofEquiv_indexEquiv,
    ValidLieTypeIndex.datumFrobenius_indexEquiv, Equiv.refl_trans,
    datumGraphAut_eq_diagramAut]
  exact DynkinType.diagramAut_indexEquiv _ _

/-- Every root is rescaled by the Frobenius parameter, uniformly: the graph automorphism moves
roots without rescaling them, so the composite has the constant exponent of the Frobenius. -/
@[simp] theorem datumSteinberg_exponent (k : Fin d.1.dynkinType.numRoots) :
    d.datumSteinberg.exponent k = (d.1.fieldOrder : ℤ) := by
  rw [datumSteinberg, RootPairingIsogeny.comp_exponent,
    ValidLieTypeIndex.datumFrobenius_exponent, RootPairingIsogeny.ofEquiv_exponent, mul_one]

/-- **The Steinberg map on roots**: it sends the root at `k` to `q` times the root at the image of
`k` under the induced permutation of the root enumeration. This is the root-datum shadow of
`γ (Frob_q (x_α(t))) = x_{γ α}(t ^ q)`. -/
theorem datumSteinberg_root (k : Fin d.1.dynkinType.numRoots) :
    d.datumSteinberg.weightMap
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root k) =
      (d.1.fieldOrder : ℤ) •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (DynkinType.diagramRootPerm d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry k) := by
  rw [d.datumSteinberg.root_weightMap, datumSteinberg_exponent, datumSteinberg_indexEquiv,
    Int.cast_id]

/-- **The Steinberg map on the Bourbaki-numbered simple roots**, where the induced permutation of
the root enumeration is the index's own pinned diagram permutation. This is the form in which
milestone L1 states the graph-twisted convention. -/
theorem datumSteinberg_root_simpleIndex (i : Fin d.1.rank) :
    d.datumSteinberg.weightMap
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) =
      (d.1.fieldOrder : ℤ) •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm i)) := by
  rw [datumSteinberg_root, DynkinType.diagramRootPerm_simpleIndex]

/-- **The Steinberg map on coroots**, the transpose statement of
`TauCeti.GraphTwistedIndex.datumSteinberg_root`. -/
theorem datumSteinberg_coroot (k : Fin d.1.dynkinType.numRoots) :
    d.datumSteinberg.coweightMap
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).coroot
          (DynkinType.diagramRootPerm d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry k)) =
      (d.1.fieldOrder : ℤ) •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).coroot k := by
  have h := d.datumSteinberg.coroot_coweightMap k
  rwa [datumSteinberg_exponent, datumSteinberg_indexEquiv, Int.cast_id] at h

/-- **The Steinberg map is the plain Frobenius exactly on the untwisted families.** The forward
direction is what makes the four graph-twisted families genuinely twisted: no untwisted index
receives the same root-datum map. -/
theorem datumSteinberg_eq_datumFrobenius_iff :
    d.datumSteinberg = d.1.datumFrobenius ↔ d.diagramPerm = 1 := by
  have hgraph : d.datumGraphAut = 1 ↔ d.diagramPerm = 1 := by
    rw [datumGraphAut_eq_diagramAut]
    exact DynkinType.diagramAut_eq_one_iff _ _
  rw [← hgraph]
  constructor
  · intro h
    -- Read the equality in the commuted order, where the Frobenius factor is outermost and its
    -- injectivity on the character lattice cancels it.
    rw [datumSteinberg_eq_datumFrobenius_comp] at h
    have hw := congrArg RootPairingIsogeny.weightMap h
    rw [RootPairingIsogeny.comp_weightMap, RootPairingIsogeny.ofEquiv_weightMap] at hw
    -- Multiplication by `q` is injective on the character lattice, so it cancels.
    have hx : ∀ x, d.datumGraphAut.toHom.weightMap x = x := fun x =>
      d.1.datumFrobenius.weightMap_injective (by simpa using LinearMap.congr_fun hw x)
    -- An automorphism of a root pairing is determined by its weight map.
    apply RootPairing.Equiv.weightHom_injective
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid)
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext fun x => ?_
    simpa using hx x
  · intro h
    have hone : RootPairingIsogeny.ofEquiv d.datumGraphAut =
        RootPairingIsogeny.id
          (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid) := by
      rw [h]
      ext <;> simp
    rw [datumSteinberg, hone, RootPairingIsogeny.comp_id]

/-- **The Steinberg map is the plain Frobenius exactly when the family name carries no
superscript**, since the twist order of a graph-twisted index is the order of its diagram
permutation. -/
theorem datumSteinberg_eq_datumFrobenius_iff_twistOrder :
    d.datumSteinberg = d.1.datumFrobenius ↔ d.twistOrder = 1 := by
  rw [datumSteinberg_eq_datumFrobenius_iff, ← orderOf_diagramPerm d, orderOf_eq_one_iff]

end

end GraphTwistedIndex

end TauCeti
