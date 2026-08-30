/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Datum.Frobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.RootDatumAutomorphism
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic

/-!
# The root-datum Steinberg map of a graph-twisted index

The Steinberg endomorphism attached to a Lie-type index that is not of Suzuki--Ree type is
`γ ∘ Frob_q`, the `q`-power Frobenius of the pinned Chevalley--Demazure group followed by the graph
automorphism realizing the pinned diagram permutation. This file builds the shadow that composite
casts on the pinned simply connected root datum, where both factors are already available:
`TauCeti.ValidLieTypeIndex.datumFrobenius` is the isogeny induced by `Frob_q`, and the isogeny
induced by `γ` is built from `TauCeti.GraphTwistedIndex.datumGraphAut⁻¹`, for the reason the next
section gives.

Two things are worth being precise about. First, this is the root-datum layer and not the group
layer: nothing here mentions a group scheme, its points, or a finite group, and the equations below
record on the root datum what milestone L1 states about root subgroups, rather than being those
equations themselves. Second, the composite is *defined* in the order `γ ∘ Frob_q` and then proved
to agree with `Frob_q ∘ γ`. That agreement,
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_comp`, is the root-datum form of the
relation "`γ` commutes with `Frob_q`" which L1 requires of the graph-twisted families, and it comes
from the general naturality of scaling among isogenies,
`TauCeti.RootPairingIsogeny.comp_smulId`, at the endo-isogenies of a single datum.

## The orientation of the graph factor

A `TauCeti.RootPairingIsogeny` carries its two lattice maps in the directions a homomorphism of
group schemes carries characters and cocharacters: `weightMap` is the pullback `χ ↦ χ ∘ f` and
`coweightMap`, its transpose, is the pushforward. So the isogeny induced by a pinned automorphism
`γ` acting on root subgroups by `γ (x_{α_i}(t)) = x_{α_{σ i}}(t)` moves the root enumeration by
`σ⁻¹` and not by `σ`: the displayed equation gives `α_{σ i} ∘ γ = α_i` on the pinned torus, so `γ`
pulls `α_i` back to `α_{σ⁻¹ i}`.

`TauCeti.DynkinType.diagramAut` is oriented the other way in `σ`. It is a homomorphism in the node
permutation, `TauCeti.DynkinType.diagramAutHom`, and its root enumeration moves by `σ`, which is
`TauCeti.DynkinType.diagramRootPerm_simpleIndex`. Passing to pullbacks is an antihomomorphism, so
the two orientations differ by an inverse, and `TauCeti.GraphTwistedIndex.datumGraphAut` is the
inverse of the isogeny the pinned `γ` induces. The graph factor here is therefore
`datumGraphAut⁻¹`, and `TauCeti.GraphTwistedIndex.datumSteinberg_root_weightMap_simpleIndex`
carries the root at a Bourbaki-numbered simple index to `q` times the root at the image of that
index under `σ⁻¹`, which is what the pullback of `γ ∘ Frob_q` does.

Taking the inverse costs nothing that `datumGraphAut` was carrying. Its order relation
`TauCeti.GraphTwistedIndex.datumGraphAut_pow_twistOrder` is the `γ ^ 2 = 1` and `γ ^ 3 = 1` of
milestone L1, and an inverse has the same order, so the graph factor used here satisfies it too.
The distinction is invisible on `²Aₙ`, `²Dₙ` and `²E₆`, whose diagram permutation is an involution,
and is visible only on `³D₄`, where the two orientations name the two trialities.

The construction separates the families in the way the classification list needs: by
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff` the Steinberg map of an index
degenerates to its Frobenius exactly on the nine untwisted families, so `²Aₙ(q)`, `²Dₙ(q)`,
`²E₆(q)` and `³D₄(q)` receive maps that no untwisted index receives.

## Main definitions

* `TauCeti.GraphTwistedIndex.datumSteinberg`: the root-datum shadow of the Steinberg map
  `γ ∘ Frob_q`.

## Main results

* `TauCeti.RootPairingIsogeny.comp_smulId` and
  `TauCeti.RootPairingIsogeny.comp_ofEquiv_smulId_eq_iff` (in the isogeny file): every isogeny
  intertwines scaling on its source with scaling on its target, which is the general form of the
  required relation, and an automorphism factor survives that scaling unless it is trivial.
* `TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_comp`: `γ ∘ Frob_q = Frob_q ∘ γ`.
* `TauCeti.GraphTwistedIndex.datumSteinberg_root_weightMap` and
  `TauCeti.GraphTwistedIndex.datumSteinberg_root_weightMap_simpleIndex`: the Steinberg map
  multiplies the root at each index by `q` and moves it along the inverse of
  `TauCeti.DynkinType.diagramRootPerm`, which on a Bourbaki-numbered simple root is the inverse of
  the index's own pinned diagram permutation.
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
pinned ambient group, which wait on the carriers of milestone L0. Nothing in this file consumes an
L0 carrier: it is convention material of the kind milestone I0 pins ahead of L0, of which the
roadmap says that the pinned diagram permutations "carry the conventions of L1 and L2 and need
nothing from Layer 9, so they land here rather than waiting on L0". This file stands to the
graph-twisted families as `TauCeti/GroupTheory/SpecificGroups/CFSG/RootDatumAutomorphism.lean`
stands to the graph automorphism alone.

The conventions follow R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80
(1968), §11, and R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.17.
-/

public section

namespace TauCeti

namespace GraphTwistedIndex

variable (d : GraphTwistedIndex)

noncomputable section

/-- **The root-datum Steinberg map of a graph-twisted index**: the isogeny induced by
`γ ∘ Frob_q`, the pinned graph automorphism after the `q`-power Frobenius. The graph factor is
`TauCeti.GraphTwistedIndex.datumGraphAut⁻¹` and not `datumGraphAut` itself, because an isogeny
carries its weight map contravariantly, as the pullback on characters, while `datumGraphAut` is
covariant in the diagram permutation; the module docstring sets that out. On the nine untwisted
families the graph automorphism is trivial and this is the Frobenius itself, by
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_iff`. -/
def datumSteinberg :
    RootPairingIsogeny (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid)
      (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid) :=
  (RootPairingIsogeny.ofEquiv d.datumGraphAut⁻¹).comp d.1.datumFrobenius

/-- **The defining equation of the root-datum Steinberg map.** The body of `datumSteinberg` is not
exposed, so this is what exhibits it as the graph automorphism after the Frobenius, in that order;
`TauCeti.GraphTwistedIndex.datumSteinberg_eq_datumFrobenius_comp` is the same map in the other
order. -/
theorem datumSteinberg_def : d.datumSteinberg =
    (RootPairingIsogeny.ofEquiv d.datumGraphAut⁻¹).comp d.1.datumFrobenius := by
  rw [datumSteinberg]

/-- **The graph automorphism commutes with the Frobenius.** This is the second relation milestone
L1 requires of a graph-twisted Steinberg map, read on the pinned root datum: the composite is the
same whichever order the two factors are taken in. -/
theorem datumSteinberg_eq_datumFrobenius_comp :
    d.datumSteinberg =
      d.1.datumFrobenius.comp (RootPairingIsogeny.ofEquiv d.datumGraphAut⁻¹) := by
  rw [datumSteinberg_def, ValidLieTypeIndex.datumFrobenius_def]
  exact RootPairingIsogeny.comp_smulId (RootPairingIsogeny.ofEquiv d.datumGraphAut⁻¹) _

/-- The Steinberg map acts on the character lattice as multiplication by `q` followed by the weight
map of the graph automorphism. -/
@[simp] theorem datumSteinberg_weightMap :
    d.datumSteinberg.weightMap =
      (d.datumGraphAut⁻¹).toHom.weightMap ∘ₗ (d.1.fieldOrder • LinearMap.id) := by
  rw [datumSteinberg_def, RootPairingIsogeny.comp_weightMap,
    RootPairingIsogeny.ofEquiv_weightMap, ValidLieTypeIndex.datumFrobenius_weightMap]

/-- The Steinberg map acts on the cocharacter lattice as the coweight map of the graph automorphism
followed by multiplication by `q`. -/
@[simp] theorem datumSteinberg_coweightMap :
    d.datumSteinberg.coweightMap =
      (d.1.fieldOrder • LinearMap.id) ∘ₗ (d.datumGraphAut⁻¹).toHom.coweightMap := by
  rw [datumSteinberg_def, RootPairingIsogeny.comp_coweightMap,
    RootPairingIsogeny.ofEquiv_coweightMap, ValidLieTypeIndex.datumFrobenius_coweightMap]

/-- The Steinberg map permutes the pinned root enumeration by the inverse of the permutation
`TauCeti.DynkinType.diagramRootPerm` that the index's diagram permutation induces, the inverse being
the pullback orientation the module docstring fixes. -/
@[simp] theorem datumSteinberg_indexEquiv :
    d.datumSteinberg.indexEquiv =
      (DynkinType.diagramRootPerm d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)⁻¹ := by
  rw [datumSteinberg_def, RootPairingIsogeny.comp_indexEquiv, RootPairingIsogeny.ofEquiv_indexEquiv,
    ValidLieTypeIndex.datumFrobenius_indexEquiv, Equiv.refl_trans,
    datumGraphAut_def]
  simp only [RootPairing.Equiv.indexEquiv_inv, RootPairing.Equiv.indexHom_apply,
    DynkinType.diagramAut_indexEquiv]

/-- Every root is rescaled by the Frobenius parameter, uniformly: the graph automorphism moves
roots without rescaling them, so the composite has the constant exponent of the Frobenius. -/
@[simp] theorem datumSteinberg_exponent (k : Fin d.1.dynkinType.numRoots) :
    d.datumSteinberg.exponent k = (d.1.fieldOrder : ℤ) := by
  rw [datumSteinberg_def, RootPairingIsogeny.comp_exponent,
    ValidLieTypeIndex.datumFrobenius_exponent, RootPairingIsogeny.ofEquiv_exponent, mul_one]

/-- **The Steinberg map on roots**: it sends the root at `k` to `q` times the root at the image of
`k` under the induced permutation of the root enumeration. That permutation is the motion of the
pinned root indices under the pullback of `γ ∘ Frob_q`, which is why the inverse appears. -/
theorem datumSteinberg_root_weightMap (k : Fin d.1.dynkinType.numRoots) :
    d.datumSteinberg.weightMap
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root k) =
      (d.1.fieldOrder : ℤ) •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          ((DynkinType.diagramRootPerm d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry)⁻¹ k) := by
  rw [d.datumSteinberg.root_weightMap, datumSteinberg_exponent, datumSteinberg_indexEquiv,
    Int.cast_id]

/-- **The Steinberg map on the Bourbaki-numbered simple roots**, where the induced permutation of
the root enumeration is the inverse of the index's own pinned diagram permutation. Milestone L1
states the graph-twisted convention as the motion `α_i ↦ α_{σ i}` of the pinned simple root
subgroups; pulling back along `γ` turns that into `σ⁻¹` here. -/
theorem datumSteinberg_root_weightMap_simpleIndex (i : Fin d.1.rank) :
    d.datumSteinberg.weightMap
        ((d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i)) =
      (d.1.fieldOrder : ℤ) •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root
          (d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm⁻¹ i)) := by
  have h : (DynkinType.diagramRootPerm d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry)⁻¹
      (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) =
      d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm⁻¹ i) := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, DynkinType.diagramRootPerm_simpleIndex,
      Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rw [datumSteinberg_root_weightMap, h]

/-- **The Steinberg map is the plain Frobenius exactly on the untwisted families.** The forward
direction is what makes the four graph-twisted families genuinely twisted: no untwisted index
receives the same root-datum map. -/
@[simp] theorem datumSteinberg_eq_datumFrobenius_iff :
    d.datumSteinberg = d.1.datumFrobenius ↔ d.diagramPerm = 1 := by
  rw [datumSteinberg_def, ValidLieTypeIndex.datumFrobenius_def,
    RootPairingIsogeny.comp_ofEquiv_smulId_eq_iff, inv_eq_one, datumGraphAut_def]
  exact DynkinType.diagramAut_eq_one_iff _ _

/-- **The Steinberg map is the plain Frobenius exactly when the family name carries no
superscript**, since the twist order of a graph-twisted index is the order of its diagram
permutation. -/
theorem datumSteinberg_eq_datumFrobenius_iff_twistOrder :
    d.datumSteinberg = d.1.datumFrobenius ↔ d.twistOrder = 1 := by
  rw [datumSteinberg_eq_datumFrobenius_iff, ← orderOf_diagramPerm d, orderOf_eq_one_iff]

end

end GraphTwistedIndex

end TauCeti
