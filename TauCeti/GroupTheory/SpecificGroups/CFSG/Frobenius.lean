/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.AlgClosedSubfield
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The field Frobenius of a Lie-type index

Every Steinberg endomorphism in the CFSG list starts from the map `x ↦ x ^ q` on the algebraic
closure of the prime field, where `q` is the Frobenius parameter recorded by the index. This file
constructs that map, `TauCeti.ValidLieTypeIndex.frobenius`, and identifies the field it fixes.

The construction is Mathlib's iterated Frobenius. Writing `q = p ^ e` with
`TauCeti.LieTypeIndex.fieldExponent`, the map is the `e`-fold iterate of the `p`-power Frobenius of
`TauCeti.ValidLieTypeIndex.Closure`, which is a ring *automorphism* because an algebraically closed
field is perfect. Its fixed field is the copy of `𝔽_q` inside the closure: it has exactly `q`
elements, it is the unique subfield with that many, and every element of the closure lies in the
fixed field of some such map. So the ambient field of a group of Lie type is the union of the
finite fields that its Frobenius powers cut out, and the field of definition attached to the index
is the one cut out by `frobenius` itself.

Nothing here concerns a group. The graph-twisted and Suzuki--Ree branches compose this map with a
diagram automorphism or replace it by an odd power of a half-Frobenius, and both of those act on a
group and not on the field; the field-level map is the same `x ↦ x ^ q` on every branch, which is
why it is defined for every valid index and not only for the untwisted ones.

## Main definitions

* `TauCeti.ValidLieTypeIndex.frobenius`: the `q`-power Frobenius automorphism of the closure.
* `TauCeti.ValidLieTypeIndex.fixedField`: the subfield it fixes.

## Main results

* `TauCeti.ValidLieTypeIndex.frobenius_apply` and
  `TauCeti.ValidLieTypeIndex.iterate_frobenius_apply`: the Frobenius and its iterates raise to the
  corresponding powers of `q`.
* `TauCeti.ValidLieTypeIndex.card_fixedField`: the fixed field has `q` elements.
* `TauCeti.ValidLieTypeIndex.eq_fixedField_of_natCard`: it is the only subfield with `q` elements.
* `TauCeti.ValidLieTypeIndex.nonempty_ringEquiv_galoisField`: it is a copy of `GaloisField p e`.
* `TauCeti.ValidLieTypeIndex.mem_frobeniusFixedSubfield_iff_iterate_frobenius_eq`: the `k`-th
  iterate fixes the field of `q ^ k` elements.
* `TauCeti.ValidLieTypeIndex.exists_mem_frobeniusFixedSubfield`: the closure is the union of the
  fixed fields of the iterated Frobenius maps.

## Roadmap

This is the field-level half of `Frob_q` in milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which sets "`Frob_q` the endomorphism induced on points
by `x ↦ x ^ d.fieldOrder` on the algebraic closure". The endomorphism of points that L1 asks for
is induced by this map once milestone L0 supplies the ambient pinned group, which waits on Layer 9
of `TauCetiRoadmap/ReductiveGroups/README.md`; the map being induced from is this one. The
`fieldExponent` data it uses belongs to the numbered conventions of milestone I0.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* D. Gorenstein, R. Lyons, and R. Solomon, *The Classification of the Finite Simple Groups*,
  Number 3, §2.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

variable (d : ValidLieTypeIndex)

/-! ## The Frobenius automorphism -/

/-- The `q`-power Frobenius of the algebraic closure attached to a valid Lie-type index, where
`q = d.fieldOrder`.

It is the `fieldExponent`-fold iterate of the `p`-power Frobenius, and is an automorphism rather
than merely an endomorphism because an algebraically closed field is perfect. -/
def frobenius : d.Closure ≃+* d.Closure :=
  iterateFrobeniusEquiv d.Closure d.characteristic d.fieldExponent

/-- The Frobenius attached to an index raises to the power recorded by the index. -/
@[simp]
theorem frobenius_apply (x : d.Closure) : d.frobenius x = x ^ d.fieldOrder := by
  rw [frobenius, iterateFrobeniusEquiv_def, ← d.fieldOrder_eq_characteristic_pow]

/-- Iterating the Frobenius attached to an index raises to the corresponding power of `q`. This is
the form the graph-twisted branches use: their Steinberg map has a `d`-th power equal to the plain
`Frob_{q ^ d}`, with `d` the order of the diagram automorphism. -/
theorem iterate_frobenius_apply (k : ℕ) (x : d.Closure) :
    (d.frobenius : d.Closure → d.Closure)^[k] x = x ^ d.fieldOrder ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, frobenius_apply, ← pow_mul, ← pow_succ]

/-! ## The field of definition -/

/-- The subfield of the algebraic closure fixed by the Frobenius attached to a valid Lie-type
index: the copy of `𝔽_q` inside the closure, with `q = d.fieldOrder`. -/
def fixedField : Subfield d.Closure :=
  frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent

variable {d}

/-- Membership in the fixed field is the equation `x ^ q = x`. -/
@[simp]
theorem mem_fixedField {x : d.Closure} : x ∈ d.fixedField ↔ x ^ d.fieldOrder = x := by
  rw [fixedField, mem_frobeniusFixedSubfield, d.fieldOrder_eq_characteristic_pow]

/-- The fixed field is the fixed-point set of the Frobenius, which is what makes it the field of
definition of the group cut out by that Frobenius. -/
theorem mem_fixedField_iff_frobenius_eq {x : d.Closure} :
    x ∈ d.fixedField ↔ d.frobenius x = x := by
  rw [mem_fixedField, frobenius_apply]

variable (d)

/-- The fixed field is finite. The exponent is positive on every branch of the index, so unlike the
general statement this needs no side condition. -/
instance : Finite d.fixedField :=
  finite_frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent
    d.fieldExponent_pos.ne'

/-- **The field of definition has `q` elements.** The subfield of the algebraic closure fixed by
the Frobenius attached to a valid Lie-type index has exactly `d.fieldOrder` elements. -/
theorem card_fixedField : Nat.card d.fixedField = d.fieldOrder := by
  rw [fixedField,
    card_frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent
      d.fieldExponent_pos.ne',
    ← d.fieldOrder_eq_characteristic_pow]

/-- The fixed field is the unique subfield of the closure with `d.fieldOrder` elements, so the
index determines it without reference to the Frobenius that cut it out. -/
theorem eq_fixedField_of_natCard {F : Subfield d.Closure} [Finite F]
    (hF : Nat.card F = d.fieldOrder) : F = d.fixedField :=
  eq_frobeniusFixedSubfield_of_natCard d.Closure d.characteristic d.fieldExponent
    d.fieldExponent_pos.ne' (by rw [hF, d.fieldOrder_eq_characteristic_pow])

/-- The fixed field is a copy of Mathlib's `GaloisField`, non-canonically. -/
theorem nonempty_ringEquiv_galoisField :
    Nonempty (d.fixedField ≃+* GaloisField d.characteristic d.fieldExponent) :=
  _root_.TauCeti.nonempty_ringEquiv_galoisField d.Closure d.characteristic d.fieldExponent
    d.fieldExponent_pos.ne'

/-- **The closure is the union of the finite fields inside it.** Every element of the algebraic
closure attached to a valid Lie-type index is fixed by some positive iterate of the `p`-power
Frobenius, hence lies in a finite subfield.

Together with `card_fixedField` this places the field of definition of the index inside an
exhaustive tower of finite subfields, and it is why the closure, though itself infinite, carries no
element that is not algebraic over a field of definition. -/
theorem exists_mem_frobeniusFixedSubfield (x : d.Closure) :
    ∃ n ≠ 0, x ∈ frobeniusFixedSubfield d.Closure d.characteristic n :=
  _root_.TauCeti.exists_mem_frobeniusFixedSubfield d.Closure d.characteristic x

variable {d}

/-- The elements fixed by the `k`-th iterate of the Frobenius are the fixed subfield at exponent
`fieldExponent * k`, which by `card_frobeniusFixedSubfield` is the field of `q ^ k` elements. This
identifies the field of definition of a graph-twisted family's ambient untwisted group: the degree
`d` extension of `𝔽_q`, with `d` the order of the diagram automorphism. -/
theorem mem_frobeniusFixedSubfield_iff_iterate_frobenius_eq {k : ℕ} {x : d.Closure} :
    x ∈ frobeniusFixedSubfield d.Closure d.characteristic (d.fieldExponent * k) ↔
      (d.frobenius : d.Closure → d.Closure)^[k] x = x := by
  rw [iterate_frobenius_apply, mem_frobeniusFixedSubfield, pow_mul,
    ← d.fieldOrder_eq_characteristic_pow]

end

end TauCeti.ValidLieTypeIndex
