/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SuzukiRee
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
public import TauCeti.LinearAlgebra.RootSystem.SpecialNodePermutations

/-!
# The special isogeny selected by a Suzuki--Ree index

The Steinberg endomorphism of a Suzuki or Ree group is an odd power of the exceptional isogeny of
its pinned ambient group. That isogeny exists only for `B₂` and `F₄` in characteristic two and for
`G₂` in characteristic three, and this file selects it, on root data, for every
`TauCeti.SuzukiReeIndex`: the Suzuki family takes the special isogeny of the pinned `B₂` datum, the
Ree `G₂` family that of `G₂`, and the Ree `F₄` family together with the Tits index that of `F₄`.

The point of selecting it here rather than downstream is that the selection carries a convention,
and the convention has to be checked against the one the CFSG roadmap fixes. Its exponent
assignment attaches `1` to a long simple root and the defining characteristic to a short one,
which is a genuine choice: the opposite assignment also squares to the prime-field Frobenius. The
upstream isogenies are pinned instead by squared root lengths, and
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny_exponent_simpleIndex` and
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny_weightMap_root_simpleIndex` are the statements that
the two agree. In the form the second one takes,

```text
τ (root (σ i)) = exponent i • root i,
```

the character map is the pullback along the group-scheme isogeny, so the exponent is indexed by
the node `i` whose root subgroup is being raised to a power and not by its image `σ i`; this is
the root-datum shadow of `τ (x_{α_i}(t)) = x_{α_{σ i}}(t ^ exponent i)`.

The permutation of nodes is checked in the same way.
`TauCeti.SuzukiReeIndex.isSpecialNodePerm_lengthPerm` reads the length permutation the index
carries as a `TauCeti.DynkinType.IsSpecialNodePerm`, which is the uniform root-level notion, and
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny_indexEquiv_simpleIndex` says the upstream isogeny
permutes the simple-root indices by exactly that permutation. Since a special node permutation is
unique when it exists (`TauCeti.DynkinType.IsSpecialNodePerm.unique`), no second convention can
sneak in.

Nothing here is a group. The lift of these three isogenies from root data to the pinned
Chevalley--Demazure group schemes, and hence the finite groups themselves, are separate work.

## Main definitions

* `TauCeti.SuzukiReeIndex.datumSpecialIsogeny`: the special isogeny of the pinned simply connected
  root datum of the underlying untwisted Dynkin type of a Suzuki--Ree index.

## Main results

* `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_weightMap_suzuki` and its fifteen siblings: the
  branch equations naming the selected isogeny on each of the four half-Frobenius families.
* `TauCeti.SuzukiReeIndex.isSpecialNodePerm_lengthPerm`: the pinned length permutation of an index
  is the special node permutation of its Dynkin type.
* `TauCeti.SuzukiReeIndex.rootLength_eq_characteristic_of_isLongSimpleRoot` and
  `TauCeti.SuzukiReeIndex.rootLength_eq_one_of_not_isLongSimpleRoot`: the two squared root lengths
  of such an index are its defining characteristic and one.
* `TauCeti.SuzukiReeIndex.rootLength_lengthPerm`: the squared length of the length-exchanged node
  is the roadmap's exponent, so the two conventions are the same one.
* `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_indexEquiv_simpleIndex` and
  `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_exponent_simpleIndex`: the selected isogeny permutes
  the simple-root indices by the pinned length permutation, with the pinned exponents.
* `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_weightMap_root_simpleIndex` and
  `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_coweightMap_coroot_simpleIndex`: the defining
  relation of the exceptional isogeny on the simple roots and on the simple coroots, in the
  exponent convention of the CFSG roadmap.
* `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_comp_self`: its square is scaling by the defining
  characteristic, which is the root-datum form of `τ ^ 2 = Frob_p`.

## Roadmap and references

This is the selection half of milestone L2 of `TauCetiRoadmap/CFSGStatement/README.md`, which owns
"selecting `τ_X` for a given `SuzukiReeIndex`, checking that the upstream isogeny is the one this
roadmap's conventions describe, and taking the odd power" and states its exponent convention
against `TauCeti.DynkinType.IsLongSimpleRoot`. The isogeny selected here is the root-datum
half of the target "Special isogenies in characteristics two and three" of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, which owns the isogeny itself. This file is to L2 what
`TauCeti/GroupTheory/SpecificGroups/CFSG/RootDatumAutomorphism.lean` is to L1.

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti

/-! ## Transport along an equality of root pairings

The special isogenies are constructed on the pinned data of the family modules, while a
Suzuki--Ree index names its datum through `TauCeti.DynkinType.simplyConnectedRootDatum`. The two
are equal, by the branch equations of that dispatcher, but not syntactically so; the transport
below reads one as the other. None of the four pieces of data of an isogeny has a type mentioning
the root pairing, so the transport moves only its three proof obligations and leaves the data
alone. -/

/-- An isogeny of a root pairing with itself, read as one of an equal root pairing with itself. -/
private def congrIsogeny {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P Q : RootPairing ι R M N} (h : P = Q)
    (f : RootPairingIsogeny Q Q) : RootPairingIsogeny P P where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  exponent := f.exponent
  exponent_pos := f.exponent_pos
  weightMap_injective := f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective
  weightMap_finiteIndex := f.weightMap_finiteIndex
  coweightMap_finiteIndex := f.coweightMap_finiteIndex
  weight_coweight_transpose := by subst h; exact f.weight_coweight_transpose
  root_weightMap := by subst h; exact f.root_weightMap
  coroot_coweightMap := by subst h; exact f.coroot_coweightMap

/-- A square relation transports along an equality of root pairings. -/
private theorem congrIsogeny_comp_self {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    {P Q : RootDatum ι M N} (h : P = Q) (f : RootPairingIsogeny Q Q)
    (c : ℕ+) (hf : f.comp f = RootPairingIsogeny.smulId Q c) :
    (congrIsogeny h f).comp (congrIsogeny h f) = RootPairingIsogeny.smulId P c := by
  subst h
  exact hf

namespace SuzukiReeIndex

open DynkinType

/-! ## The selected isogeny -/

/-- **The special isogeny of the pinned simply connected root datum selected by a Suzuki--Ree
index**: the exceptional isogeny of `B₂` in characteristic two for the Suzuki family, of `G₂` in
characteristic three for the Ree `G₂` family, and of `F₄` in characteristic two for the Ree `F₄`
family and the Tits index.

The sixteen branch equations below name the selected isogeny on each family, field by field, so no
consumer needs this body. -/
noncomputable def datumSpecialIsogeny (e : SuzukiReeIndex) :
    RootPairingIsogeny (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid)
      (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid) :=
  match e with
  | ⟨⟨.A _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedA _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.B _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.C _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.D _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedD _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E7 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E8 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.F4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.G2 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedE6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.suzuki _, _⟩, _⟩ => congrIsogeny (simplyConnectedRootDatum_B 2 _) b2SpecialIsogeny
  | ⟨⟨.reeG2 _, _⟩, _⟩ => congrIsogeny (simplyConnectedRootDatum_G2 _) g2SpecialIsogeny
  | ⟨⟨.reeF4 _, _⟩, _⟩ => congrIsogeny (simplyConnectedRootDatum_F4 _) f4SpecialIsogeny
  | ⟨⟨.tits, _⟩, _⟩ => congrIsogeny (simplyConnectedRootDatum_F4 _) f4SpecialIsogeny

/-! ### Branch equations

The four pieces of data of an isogeny are recorded one family at a time. Together they determine
the selected isogeny, since `TauCeti.RootPairingIsogeny` is extensional in exactly these four
fields. -/

section Branches

variable (m : ℕ)

/-- The character map of the isogeny selected by a Suzuki index is that of the `B₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_weightMap_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    (datumSpecialIsogeny ⟨⟨.suzuki m, hv⟩, by simp⟩).weightMap = b2SpecialIsogeny.weightMap :=
  (rfl)

/-- The cocharacter map of the isogeny selected by a Suzuki index is that of the `B₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_coweightMap_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    (datumSpecialIsogeny ⟨⟨.suzuki m, hv⟩, by simp⟩).coweightMap = b2SpecialIsogeny.coweightMap :=
  (rfl)

/-- The root permutation of the isogeny selected by a Suzuki index is that of the `B₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_indexEquiv_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    (datumSpecialIsogeny ⟨⟨.suzuki m, hv⟩, by simp⟩).indexEquiv = b2SpecialIsogeny.indexEquiv :=
  (rfl)

/-- The rescaling exponents of the isogeny selected by a Suzuki index are those of the `B₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_exponent_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    (datumSpecialIsogeny ⟨⟨.suzuki m, hv⟩, by simp⟩).exponent = b2SpecialIsogeny.exponent :=
  (rfl)

/-- The character map of the isogeny selected by a Ree `G₂` index is that of the `G₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_weightMap_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeG2 m, hv⟩, by simp⟩).weightMap = g2SpecialIsogeny.weightMap :=
  (rfl)

/-- The cocharacter map of the isogeny selected by a Ree `G₂` index is that of the `G₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_coweightMap_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeG2 m, hv⟩, by simp⟩).coweightMap = g2SpecialIsogeny.coweightMap :=
  (rfl)

/-- The root permutation of the isogeny selected by a Ree `G₂` index is that of the `G₂` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_indexEquiv_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeG2 m, hv⟩, by simp⟩).indexEquiv = g2SpecialIsogeny.indexEquiv :=
  (rfl)

/-- The rescaling exponents of the isogeny selected by a Ree `G₂` index are those of the `G₂`
special isogeny. -/
@[simp] theorem datumSpecialIsogeny_exponent_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeG2 m, hv⟩, by simp⟩).exponent = g2SpecialIsogeny.exponent :=
  (rfl)

/-- The character map of the isogeny selected by a Ree `F₄` index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_weightMap_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeF4 m, hv⟩, by simp⟩).weightMap = f4SpecialIsogeny.weightMap :=
  (rfl)

/-- The cocharacter map of the isogeny selected by a Ree `F₄` index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_coweightMap_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeF4 m, hv⟩, by simp⟩).coweightMap = f4SpecialIsogeny.coweightMap :=
  (rfl)

/-- The root permutation of the isogeny selected by a Ree `F₄` index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_indexEquiv_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeF4 m, hv⟩, by simp⟩).indexEquiv = f4SpecialIsogeny.indexEquiv :=
  (rfl)

/-- The rescaling exponents of the isogeny selected by a Ree `F₄` index are those of the `F₄`
special isogeny. -/
@[simp] theorem datumSpecialIsogeny_exponent_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    (datumSpecialIsogeny ⟨⟨.reeF4 m, hv⟩, by simp⟩).exponent = f4SpecialIsogeny.exponent :=
  (rfl)

/-- The character map of the isogeny selected by the Tits index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_weightMap_tits :
    (datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩).weightMap = f4SpecialIsogeny.weightMap :=
  (rfl)

/-- The cocharacter map of the isogeny selected by the Tits index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_coweightMap_tits :
    (datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩).coweightMap = f4SpecialIsogeny.coweightMap :=
  (rfl)

/-- The root permutation of the isogeny selected by the Tits index is that of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_indexEquiv_tits :
    (datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩).indexEquiv = f4SpecialIsogeny.indexEquiv :=
  (rfl)

/-- The rescaling exponents of the isogeny selected by the Tits index are those of the `F₄` special
isogeny. -/
@[simp] theorem datumSpecialIsogeny_exponent_tits :
    (datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩).exponent = f4SpecialIsogeny.exponent :=
  (rfl)

end Branches

/-! ## The length permutation and the root-length convention -/

/-- **The pinned length permutation of a Suzuki--Ree index is the special node permutation of its
Dynkin type.** Both defining conditions are already proved of it: it exchanges long and short
simple roots and transposes the Cartan matrix. Since a special node permutation is unique
(`TauCeti.DynkinType.IsSpecialNodePerm.unique`), this leaves no room for a competing
length-exchanging convention. -/
theorem isSpecialNodePerm_lengthPerm (e : SuzukiReeIndex) :
    e.1.dynkinType.IsSpecialNodePerm e.lengthPerm where
  isLongSimpleRoot_apply := e.isLongSimpleRoot_lengthPerm
  cartanMatrix_apply := e.cartanMatrix_lengthPerm

-- Transporting a length statement along an equality of Dynkin types, rather than rewriting the
-- type of the node index that the statement depends on.
private theorem rootLength_of_eq {t u : DynkinType} (h : t = u) (c : ℤ)
    (hu : ∀ j : Fin u.rank, u.rootLength j = if u.IsLongSimpleRoot j then c else 1)
    (i : Fin t.rank) : t.rootLength i = if t.IsLongSimpleRoot i then c else 1 := by
  subst h
  exact hu i

-- The two squared lengths of a Suzuki--Ree index are `1` and its defining characteristic: two for
-- `B₂` and `F₄`, three for `G₂`, taken at the long simple roots. The two named readings below are
-- the interface; this combined form exists to case on the family once rather than twice.
private theorem rootLength_eq_ite (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.1.dynkinType.rootLength i =
      if e.1.dynkinType.IsLongSimpleRoot i then (e.1.characteristic : ℤ) else 1 := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    simp only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_suzuki,
      Nat.cast_ofNat]
    refine rootLength_of_eq (LieTypeIndex.dynkinType_suzuki _) 2 ?_ i
    simp only [rootLength_B, isLongSimpleRoot_B]
    decide
  case reeG2 =>
    simp only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_reeG2,
      Nat.cast_ofNat]
    refine rootLength_of_eq (LieTypeIndex.dynkinType_reeG2 _) 3 ?_ i
    simp only [rootLength_G2, isLongSimpleRoot_G2]
    decide
  case reeF4 =>
    simp only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_reeF4,
      Nat.cast_ofNat]
    refine rootLength_of_eq (LieTypeIndex.dynkinType_reeF4 _) 2 ?_ i
    simp only [rootLength_F4, isLongSimpleRoot_F4]
    decide
  case tits =>
    simp only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_tits, Nat.cast_ofNat]
    refine rootLength_of_eq LieTypeIndex.dynkinType_tits 2 ?_ i
    simp only [rootLength_F4, isLongSimpleRoot_F4]
    decide

/-- A long simple root of a Suzuki--Ree index has squared length the defining characteristic: two
for `B₂` and `F₄`, three for `G₂`. -/
@[simp] theorem rootLength_eq_characteristic_of_isLongSimpleRoot (e : SuzukiReeIndex)
    (i : Fin e.1.rank) (hi : e.1.dynkinType.IsLongSimpleRoot i) :
    e.1.dynkinType.rootLength i = (e.1.characteristic : ℤ) := by
  simp [rootLength_eq_ite, hi]

/-- A short simple root of a Suzuki--Ree index has squared length one: the normalisation of
`TauCeti.DynkinType.rootLength` makes the shorter of the two lengths `1`. -/
@[simp] theorem rootLength_eq_one_of_not_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : ¬ e.1.dynkinType.IsLongSimpleRoot i) : e.1.dynkinType.rootLength i = 1 := by
  simp [rootLength_eq_ite, hi]

/-- **The exponent convention of the CFSG roadmap is the root-length convention of the
root-systems roadmap.** The squared length of the node paired with `i` by the length permutation
is the exponent the exceptional isogeny attaches to the root subgroup of `i`: it is `1` when `i`
is long, because the paired node is then short, and the defining characteristic when `i` is
short. -/
@[simp] theorem rootLength_lengthPerm (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.1.dynkinType.rootLength (e.lengthPerm i) = (e.exponent i : ℤ) := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · rw [exponent_of_isLongSimpleRoot e i hi, Nat.cast_one]
    exact rootLength_eq_one_of_not_isLongSimpleRoot e _
      fun hc => (isLongSimpleRoot_lengthPerm e i).mp hc hi
  · rw [exponent_of_not_isLongSimpleRoot e i hi]
    exact rootLength_eq_characteristic_of_isLongSimpleRoot e _
      ((isLongSimpleRoot_lengthPerm e i).mpr hi)

/-! ## The selected isogeny on the simple roots -/

-- The private lemmas below are the branch content of the uniform statements that follow. Each is
-- stated on one concrete pinned datum, where no index type depends on a Dynkin type variable, and
-- the uniform statement then closes each branch by rewriting to it. They are proved by chaining
-- equations in term mode rather than by `rw`, because rewriting a simple-root index under the
-- isogeny would abstract a term whose type is `Fin t.numRoots` on one side and the family
-- module's own literal count on the other.

-- The `G₂` root enumeration names its simple indices by `Fin.castLE`, while the uniform
-- `simpleIndex` dispatcher names them by `Fin.castAdd`. `Fin.castAdd` is `Fin.castLE` at a
-- particular inequality proof, so the two are the same index and only the syntax differs.
private theorem castAdd_eq_castLE_g2 (i : Fin 2) :
    (Fin.castAdd 10 i : Fin 12) = Fin.castLE (by omega) i :=
  rfl

private theorem b2SpecialIsogeny_indexEquiv_simpleIndex (ht : (B 2).Valid)
    (i : Fin (B 2).rank) :
    b2SpecialIsogeny.indexEquiv ((B 2).simpleIndex ht i) =
      (B 2).simpleIndex ht (lengthPermRankTwo i) :=
  (congrArg (⇑b2SpecialIsogeny.indexEquiv) (simpleIndex_B 2 ht i)).trans
    (((b2SpecialIsogeny_indexEquiv_apply _).trans
        (b2SpecialIsogenyIndexEquiv_typeBSimpleIndex i)).trans
      (simpleIndex_B 2 ht (lengthPermRankTwo i)).symm)

private theorem g2SpecialIsogeny_indexEquiv_simpleIndex (ht : G2.Valid) (i : Fin G2.rank) :
    g2SpecialIsogeny.indexEquiv (G2.simpleIndex ht i) =
      G2.simpleIndex ht (lengthPermRankTwo i) :=
  (congrArg (⇑g2SpecialIsogeny.indexEquiv)
      ((simpleIndex_G2 ht i).trans (castAdd_eq_castLE_g2 i))).trans
    (((g2SpecialIsogeny_indexEquiv_apply _).trans (g2SpecialIsogenyIndex_castLE i)).trans
      (((castAdd_eq_castLE_g2 (lengthPermRankTwo i)).symm).trans
        (simpleIndex_G2 ht (lengthPermRankTwo i)).symm))

private theorem f4SpecialIsogeny_indexEquiv_simpleIndex (ht : F4.Valid) (i : Fin F4.rank) :
    f4SpecialIsogeny.indexEquiv (F4.simpleIndex ht i) = F4.simpleIndex ht (lengthPermF4 i) :=
  (congrArg (⇑f4SpecialIsogeny.indexEquiv) (simpleIndex_F4 ht i)).trans
    (((f4SpecialIsogeny_indexEquiv_apply _).trans (f4SpecialIsogenyIndex_castAdd i)).trans
      (simpleIndex_F4 ht (lengthPermF4 i)).symm)

private theorem b2SpecialIsogeny_exponent_simpleIndex (ht : (B 2).Valid) (i : Fin (B 2).rank) :
    b2SpecialIsogeny.exponent ((B 2).simpleIndex ht i) = (B 2).rootLength i :=
  (congrArg b2SpecialIsogeny.exponent (simpleIndex_B 2 ht i)).trans
    ((b2SpecialIsogeny_exponent _).trans (b2SpecialIsogenyExponent_typeBSimpleIndex i))

private theorem g2SpecialIsogeny_exponent_simpleIndex (ht : G2.Valid) (i : Fin G2.rank) :
    g2SpecialIsogeny.exponent (G2.simpleIndex ht i) = G2.rootLength i :=
  (congrArg g2SpecialIsogeny.exponent
      ((simpleIndex_G2 ht i).trans (castAdd_eq_castLE_g2 i))).trans
    ((g2SpecialIsogeny_exponent _).trans (g2Length_castLE i))

private theorem f4SpecialIsogeny_exponent_simpleIndex (ht : F4.Valid) (i : Fin F4.rank) :
    f4SpecialIsogeny.exponent (F4.simpleIndex ht i) = F4.rootLength i :=
  (congrArg f4SpecialIsogeny.exponent (simpleIndex_F4 ht i)).trans
    ((f4SpecialIsogeny_exponent _).trans (f4Length_castAdd i))

/-- **The selected isogeny permutes the simple-root indices by the pinned length permutation.**
This is the check that the node convention of the upstream isogeny is the one
`TauCeti.SuzukiReeIndex.lengthPerm` fixes. -/
@[simp] theorem datumSpecialIsogeny_indexEquiv_simpleIndex (e : SuzukiReeIndex)
    (i : Fin e.1.rank) :
    e.datumSpecialIsogeny.indexEquiv (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) =
      e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i) := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    rw [datumSpecialIsogeny_indexEquiv_suzuki, lengthPerm_suzuki]
    exact b2SpecialIsogeny_indexEquiv_simpleIndex _ i
  case reeG2 =>
    rw [datumSpecialIsogeny_indexEquiv_reeG2, lengthPerm_reeG2]
    exact g2SpecialIsogeny_indexEquiv_simpleIndex _ i
  case reeF4 =>
    rw [datumSpecialIsogeny_indexEquiv_reeF4, lengthPerm_reeF4]
    exact f4SpecialIsogeny_indexEquiv_simpleIndex _ i
  case tits =>
    rw [datumSpecialIsogeny_indexEquiv_tits, lengthPerm_tits]
    exact f4SpecialIsogeny_indexEquiv_simpleIndex _ i

/-- **The exponent of the selected isogeny at a simple-root index is the squared length of that
node.** The isogeny's `exponent` field is indexed by the source of its character map, which is the
image node of the group-scheme isogeny; combined with
`TauCeti.SuzukiReeIndex.rootLength_lengthPerm` this is the roadmap's assignment of `1` to a long
simple root and the characteristic to a short one. -/
@[simp] theorem datumSpecialIsogeny_exponent_simpleIndex (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.datumSpecialIsogeny.exponent (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) =
      e.1.dynkinType.rootLength i := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    rw [datumSpecialIsogeny_exponent_suzuki]
    exact b2SpecialIsogeny_exponent_simpleIndex _ i
  case reeG2 =>
    rw [datumSpecialIsogeny_exponent_reeG2]
    exact g2SpecialIsogeny_exponent_simpleIndex _ i
  case reeF4 =>
    rw [datumSpecialIsogeny_exponent_reeF4]
    exact f4SpecialIsogeny_exponent_simpleIndex _ i
  case tits =>
    rw [datumSpecialIsogeny_exponent_tits]
    exact f4SpecialIsogeny_exponent_simpleIndex _ i

/-- **The defining relation of the exceptional isogeny on the simple roots, in the exponent
convention of the CFSG roadmap.** The character map carries the simple root at the
length-exchanged node to the simple root at `i`, rescaled by `TauCeti.SuzukiReeIndex.exponent i`,
which is `1` at a long node and the defining characteristic at a short one.

The character map is the pullback along the group-scheme isogeny, so this is the root-datum shadow
of `τ (x_{α_i}(t)) = x_{α_{σ i}}(t ^ exponent i)`, with the exponent indexed by `i` rather than by
its image. -/
theorem datumSpecialIsogeny_weightMap_root_simpleIndex (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.datumSpecialIsogeny.weightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i))) =
      (e.exponent i : ℤ) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) := by
  rw [e.datumSpecialIsogeny.root_weightMap, datumSpecialIsogeny_indexEquiv_simpleIndex,
    lengthPerm_lengthPerm, datumSpecialIsogeny_exponent_simpleIndex, rootLength_lengthPerm]
  simp only [Int.cast_id]

/-- **The defining relation of the exceptional isogeny on the simple coroots.** Dually to
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny_weightMap_root_simpleIndex`, the cocharacter map runs
the other way, so it carries the simple coroot at `i` to the one at the length-exchanged node,
rescaled by the same `TauCeti.SuzukiReeIndex.exponent i`. -/
theorem datumSpecialIsogeny_coweightMap_coroot_simpleIndex (e : SuzukiReeIndex)
    (i : Fin e.1.rank) :
    e.datumSpecialIsogeny.coweightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i)) =
      (e.exponent i : ℤ) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i)) := by
  have h := e.datumSpecialIsogeny.coroot_coweightMap
    (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i))
  rw [datumSpecialIsogeny_indexEquiv_simpleIndex, lengthPerm_lengthPerm] at h
  rw [h, datumSpecialIsogeny_exponent_simpleIndex, rootLength_lengthPerm]
  simp only [Int.cast_id]

/-! ## The square relation -/

/-- **The square of the selected isogeny is scaling by the defining characteristic.** This is the
root-datum form of `τ ^ 2 = Frob_p`, uniformly over the four half-Frobenius families; the odd
powers of `τ` that cut out the Suzuki, Ree and Tits groups are read off it. -/
@[simp] theorem datumSpecialIsogeny_comp_self (e : SuzukiReeIndex) :
    e.datumSpecialIsogeny.comp e.datumSpecialIsogeny =
      RootPairingIsogeny.smulId _ ⟨e.1.characteristic, e.1.characteristic_prime.pos⟩ := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    have hc : (2 : ℕ+) = ⟨ValidLieTypeIndex.characteristic ⟨_, hvalid⟩,
        (ValidLieTypeIndex.characteristic_prime _).pos⟩ := by
      refine PNat.coe_injective ?_
      simp [ValidLieTypeIndex.characteristic]
    exact congrIsogeny_comp_self (simplyConnectedRootDatum_B 2 _) b2SpecialIsogeny _
      (hc ▸ b2SpecialIsogeny_comp_self)
  case reeG2 =>
    have hc : (3 : ℕ+) = ⟨ValidLieTypeIndex.characteristic ⟨_, hvalid⟩,
        (ValidLieTypeIndex.characteristic_prime _).pos⟩ := by
      refine PNat.coe_injective ?_
      simp [ValidLieTypeIndex.characteristic]
    exact congrIsogeny_comp_self (simplyConnectedRootDatum_G2 _) g2SpecialIsogeny _
      (hc ▸ g2SpecialIsogeny_comp_self)
  case reeF4 =>
    have hc : (2 : ℕ+) = ⟨ValidLieTypeIndex.characteristic ⟨_, hvalid⟩,
        (ValidLieTypeIndex.characteristic_prime _).pos⟩ := by
      refine PNat.coe_injective ?_
      simp [ValidLieTypeIndex.characteristic]
    exact congrIsogeny_comp_self (simplyConnectedRootDatum_F4 _) f4SpecialIsogeny _
      (hc ▸ f4SpecialIsogeny_comp_self)
  case tits =>
    have hc : (2 : ℕ+) = ⟨ValidLieTypeIndex.characteristic ⟨_, hvalid⟩,
        (ValidLieTypeIndex.characteristic_prime _).pos⟩ := by
      refine PNat.coe_injective ?_
      simp [ValidLieTypeIndex.characteristic]
    exact congrIsogeny_comp_self (simplyConnectedRootDatum_F4 _) f4SpecialIsogeny _
      (hc ▸ f4SpecialIsogeny_comp_self)

end SuzukiReeIndex

end TauCeti
