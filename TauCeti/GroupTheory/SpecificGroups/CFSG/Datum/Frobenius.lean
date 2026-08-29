/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The root-datum Frobenius of a valid Lie-type index

The Steinberg endomorphism of every family on the CFSG list is built from the `q`-power Frobenius
of the pinned Chevalley--Demazure group scheme, where `q` is the Frobenius parameter
`TauCeti.LieTypeIndex.fieldOrder` recorded by the index. This file builds the shadow that Frobenius
casts on the pinned simply connected root datum: a Frobenius isogeny of a split group scheme fixes
the root datum and multiplies its characters by `q`, so the shadow is multiplication by `q`,
`TauCeti.RootPairingIsogeny.smulId` at the positive natural
`TauCeti.LieTypeIndex.fieldOrderPNat`.

No diagram data enters here, and nothing about a twist: the map is available for every valid index,
exactly as the field-level `TauCeti.ValidLieTypeIndex.frobeniusEquiv` is, and the twisting of a
family is carried entirely by whatever the Frobenius shadow is composed with. For the graph-twisted
families that partner is the root-datum graph automorphism, and the composite is
`TauCeti.GraphTwistedIndex.datumSteinberg` in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Datum/Steinberg.lean`.

This is the root-datum layer and not the group layer: nothing here mentions a group scheme, its
points, or a finite group.

## Main definitions

* `TauCeti.ValidLieTypeIndex.datumFrobenius`: multiplication by the Frobenius parameter, as an
  isogeny of the pinned simply connected root datum; the root-datum shadow of `Frob_q`.

## Main results

* `TauCeti.ValidLieTypeIndex.datumFrobenius_weightMap`,
  `TauCeti.ValidLieTypeIndex.datumFrobenius_coweightMap`,
  `TauCeti.ValidLieTypeIndex.datumFrobenius_indexEquiv` and
  `TauCeti.ValidLieTypeIndex.datumFrobenius_exponent`: it multiplies both lattices by `q`, fixes
  the root enumeration, and rescales every root by `q`.

## Roadmap

This is the root-datum layer of the `Frob_q` of milestone L1, "ordinary and graph Steinberg maps",
of `TauCetiRoadmap/CFSGStatement/README.md`, whose table sets the Steinberg map of the untwisted
families to `Frob_q`. The field-level half is
`TauCeti.ValidLieTypeIndex.frobeniusEquiv` in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Frobenius.lean`; the endomorphism of points that L1 asks
for waits on the carriers of milestone L0.

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

/-- **The defining equation of the root-datum Frobenius.** The body of `datumFrobenius` is not
exposed, so this is what lets a consumer rewrite it into `TauCeti.RootPairingIsogeny.smulId` and
then apply the general lemmas about scaling at `c = d.fieldOrderPNat`. -/
theorem datumFrobenius_def : d.datumFrobenius =
    RootPairingIsogeny.smulId (d.dynkinType.simplyConnectedRootDatum d.dynkinType_valid)
      d.1.fieldOrderPNat := by
  rw [datumFrobenius]

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

end TauCeti
