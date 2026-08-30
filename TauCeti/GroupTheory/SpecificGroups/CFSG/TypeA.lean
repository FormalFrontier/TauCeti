/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius
public import TauCeti.GroupTheory.FixedPointCandidate
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The type-A finite-group candidates

This file carries the type-`A` families through the complete construction prescribed by the
CFSG-statement roadmap. A `TauCeti.TypeAIndex` packages an ordinary or graph-twisted type-`A`
index together with its validity proof; invalid ranks and excluded small parameters therefore
cannot reach any carrier-valued definition. Its ambient group is the algebraic-closure-valued
point group of the explicit full-weight type-`A` Chevalley carrier
`TauCeti.SlStd.groupScheme`.

The Steinberg map is the `q`-power Frobenius on an untwisted index and the pinned graph
automorphism composed with that Frobenius on a twisted index. The equation on every numbered
simple-root subgroup is recorded against the identity or Bourbaki-node reversal, respectively.
Finally `TauCeti.TypeAIndex.Group` applies the uniform fixed-points, derived-subgroup, and
central-quotient recipe:

```text
H = fixedSubgroup steinberg,        Group = [H, H] / Z([H, H]).
```

Thus both type-`A` branches now name honest group types built from explicit data. Nothing here
asserts that these groups are finite or simple. The remaining Lie families still need their own
explicit carriers before `TauCeti.CFSGIndex.Group` can be assembled.

## Main declarations

* `TauCeti.TypeAIndex`: the valid untwisted and graph-twisted type-`A` indices.
* `TauCeti.TypeAIndex.AmbientGroup`: points of the explicit type-`A` carrier over the algebraic
  closure attached to the index.
* `TauCeti.TypeAIndex.steinberg`: ordinary or graph-twisted Frobenius on those points.
* `TauCeti.TypeAIndex.simpleRootSubgroup` and `steinberg_simpleRootSubgroup`: the pinned simple-root
  subgroups and the Steinberg equation on them.
* `TauCeti.TypeAIndex.FixedPoints` and `TauCeti.TypeAIndex.Group`: the fixed group and its derived
  central quotient.

## References

The construction follows R. W. Carter, *Simple Groups of Lie Type*, Chapters 2 and 14, and
R. Steinberg, *Endomorphisms of Linear Algebraic Groups*, Memoirs AMS **80** (1968), Section 11.
It is the type-`A` slice of milestones L0--L3 in
`TauCetiRoadmap/CFSGStatement/README.md`. The explicit carrier, its root subgroups, Frobenius, and
graph automorphism are the corresponding Layer 9 outputs of
`TauCetiRoadmap/ReductiveGroups/README.md` already available in Tau Ceti.
-/

public section

namespace TauCeti

/-! ## Valid type-A indices -/

/-- A valid untwisted or graph-twisted type-`A` index. The validity proof is part of each
constructor, so every carrier below is indexed by the roadmap's validity predicate. -/
inductive TypeAIndex : Type
  | ofA (rank : ℕ) (q : PrimePower) (hvalid : (LieTypeIndex.A rank q).Valid)
  | ofTwistedA (rank : ℕ) (q : PrimePower)
      (hvalid : (LieTypeIndex.twistedA rank q).Valid)

namespace TypeAIndex

/-- The valid Lie-type index underlying a type-`A` index. -/
abbrev validIndex : TypeAIndex → ValidLieTypeIndex
  | .ofA rank q hvalid => ⟨LieTypeIndex.A rank q, hvalid⟩
  | .ofTwistedA rank q hvalid => ⟨LieTypeIndex.twistedA rank q, hvalid⟩

/-- The rank of a type-`A` index, read from its pinned Dynkin type. -/
abbrev rank : TypeAIndex → ℕ
  | .ofA rank _ _ | .ofTwistedA rank _ _ => rank

/-- The characteristic of a type-`A` index. -/
abbrev characteristic (d : TypeAIndex) : ℕ := d.validIndex.characteristic

/-- The Frobenius exponent of a type-`A` index. -/
abbrev fieldExponent (d : TypeAIndex) : ℕ := d.validIndex.fieldExponent

/-- The Frobenius parameter of a type-`A` index. -/
abbrev fieldOrder (d : TypeAIndex) : ℕ := d.validIndex.fieldOrder

/-- The algebraic closure of the prime field attached to a type-`A` index. -/
abbrev Closure (d : TypeAIndex) : Type := d.validIndex.Closure

/-- The exponential characteristic structure on the algebraic closure attached to a type-`A`
index. -/
noncomputable instance expChar (d : TypeAIndex) : ExpChar d.Closure d.characteristic :=
  inferInstanceAs (ExpChar d.validIndex.Closure d.validIndex.characteristic)

/-! ## The explicit carrier and its pinned maps -/

/-- **The ambient group of a type-`A` index:** the algebraic-closure-valued points of the explicit
full-weight type-`A` Chevalley carrier. -/
noncomputable abbrev AmbientGroup (d : TypeAIndex) : Type :=
  SlStd.points d.rank d.Closure

/-- The `q`-power Frobenius endomorphism of the explicit type-`A` ambient group. -/
@[expose] noncomputable def frobenius (d : TypeAIndex) : d.AmbientGroup →* d.AmbientGroup :=
  SlStd.frobenius d.rank d.characteristic d.fieldExponent d.Closure

/-- The specified power of the characteristic Frobenius on a type-`A` ambient group. -/
@[expose] noncomputable def frobeniusPower (d : TypeAIndex) (exponent : ℕ) :
    d.AmbientGroup →* d.AmbientGroup :=
  SlStd.frobenius d.rank d.characteristic exponent d.Closure

/-- Graph reversal composed with the `q`-power Frobenius on a type-`A` ambient group. This map is
selected as the Steinberg map precisely on the graph-twisted branch. -/
@[expose] noncomputable def twistedFrobenius (d : TypeAIndex) :
    d.AmbientGroup →* d.AmbientGroup :=
  SlStd.twistedFrobenius d.rank d.characteristic d.fieldExponent d.Closure

/-- The diagram permutation used by a type-`A` Steinberg map: the identity on an ordinary index
and reversal of the Bourbaki nodes on a graph-twisted index. -/
@[expose] def diagramPerm : (d : TypeAIndex) → Equiv.Perm (Fin d.rank)
  | .ofA _ _ _ => 1
  | .ofTwistedA _ _ _ => Fin.revPerm

/-- An ordinary type-`A` index has the identity diagram permutation. -/
@[simp]
theorem diagramPerm_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).diagramPerm = 1 := rfl

/-- A graph-twisted type-`A` index reverses the Bourbaki nodes. -/
@[simp]
theorem diagramPerm_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).diagramPerm = Fin.revPerm := rfl

/-- **The Steinberg endomorphism of an explicit type-`A` ambient group.** It is ordinary
Frobenius on `A_r(q)` and graph reversal composed with Frobenius on `²A_r(q)`. -/
@[expose] noncomputable def steinberg : (d : TypeAIndex) →
    d.AmbientGroup →* d.AmbientGroup
  | .ofA rank q hvalid => (ofA rank q hvalid).frobenius
  | .ofTwistedA rank q hvalid => (ofTwistedA rank q hvalid).twistedFrobenius

/-- On an ordinary type-`A` index the Steinberg map is the carrier Frobenius. -/
@[simp]
theorem steinberg_ofA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.A rank q).Valid) :
    (ofA rank q hvalid).steinberg = (ofA rank q hvalid).frobenius := by
  apply MonoidHom.ext
  intro g
  rfl

/-- On a graph-twisted type-`A` index the Steinberg map is graph reversal composed with the carrier
Frobenius. -/
@[simp]
theorem steinberg_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).steinberg =
      (ofTwistedA rank q hvalid).twistedFrobenius := rfl

/-- Applying the graph-twisted type-`A` Steinberg map twice is the
`p ^ (2 * fieldExponent)`-power Frobenius. -/
theorem steinberg_comp_self_ofTwistedA (rank : ℕ) (q : PrimePower)
    (hvalid : (LieTypeIndex.twistedA rank q).Valid) :
    (ofTwistedA rank q hvalid).steinberg.comp (ofTwistedA rank q hvalid).steinberg =
      (ofTwistedA rank q hvalid).frobeniusPower
        (2 * (ofTwistedA rank q hvalid).fieldExponent) := by
  let _ : ExpChar (ofTwistedA rank q hvalid).Closure
      (ofTwistedA rank q hvalid).characteristic := expChar _
  exact SlStd.twistedFrobenius_comp_self rank
    (ofTwistedA rank q hvalid).characteristic
    (ofTwistedA rank q hvalid).fieldExponent (ofTwistedA rank q hvalid).Closure

/-- The positive simple-root subgroup at a Bourbaki node of a type-`A` ambient group. -/
@[expose] noncomputable def simpleRootSubgroup (d : TypeAIndex) (i : Fin d.rank) :
    Multiplicative d.Closure →* d.AmbientGroup :=
  SlStd.rootSubgroupPoints d.rank (.inl i) d.Closure

/-- **The pinned simple-root equation for a type-`A` Steinberg map.** The map applies the diagram
permutation to the Bourbaki node and raises the root parameter to the `q`-th power. -/
@[simp]
theorem steinberg_simpleRootSubgroup (d : TypeAIndex) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.diagramPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.fieldOrder)) := by
  cases d with
  | ofA rank q hvalid =>
      let _ : ExpChar (ofA rank q hvalid).Closure
          (ofA rank q hvalid).characteristic := expChar _
      have hdiagram : (ofA rank q hvalid).diagramPerm i = i := rfl
      have hfield : (ofA rank q hvalid).fieldOrder =
          (ofA rank q hvalid).characteristic ^ (ofA rank q hvalid).fieldExponent :=
        (ofA rank q hvalid).validIndex.fieldOrder_eq_characteristic_pow
      rw [hdiagram, hfield]
      convert SlStd.frobenius_rootSubgroupPoints rank (ofA rank q hvalid).characteristic
        (ofA rank q hvalid).fieldExponent (ofA rank q hvalid).Closure (.inl i) u using 1
      · rfl
      · rfl
  | ofTwistedA rank q hvalid =>
      let _ : ExpChar (ofTwistedA rank q hvalid).Closure
          (ofTwistedA rank q hvalid).characteristic := expChar _
      have hdiagram : (ofTwistedA rank q hvalid).diagramPerm i = i.rev :=
        Fin.revPerm_apply i
      have hfield : (ofTwistedA rank q hvalid).fieldOrder =
          (ofTwistedA rank q hvalid).characteristic ^
            (ofTwistedA rank q hvalid).fieldExponent :=
        (ofTwistedA rank q hvalid).validIndex.fieldOrder_eq_characteristic_pow
      rw [hdiagram, hfield]
      convert SlStd.twistedFrobenius_rootSubgroupPoints rank
        (ofTwistedA rank q hvalid).characteristic
        (ofTwistedA rank q hvalid).fieldExponent (ofTwistedA rank q hvalid).Closure (.inl i) u
          using 1
      · rfl
      · simp only [simpleRootSubgroup, SlStd.graphRootPerm_inl]

/-! ## Fixed points and the candidate group -/

/-- The fixed subgroup of the type-`A` Steinberg endomorphism. -/
noncomputable abbrev FixedPoints (d : TypeAIndex) :
    Subgroup d.AmbientGroup := fixedSubgroup d.steinberg

/-- **The finite-simple-group candidate attached to a type-`A` index:** the derived subgroup of
the Steinberg fixed points, modulo the centre of that derived subgroup. No finiteness or
simplicity instance is asserted. -/
noncomputable abbrev Group (d : TypeAIndex) : Type := FixedPointCandidate d.steinberg

end TypeAIndex

end TauCeti
