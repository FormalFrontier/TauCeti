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

On the ordinary and graph-twisted branches of the CFSG list the Steinberg endomorphism starts from
the map `x ↦ x ^ q` on the algebraic closure of the prime field, where `q` is the Frobenius
parameter recorded by the index; on the Suzuki--Ree and Tits branches the Steinberg map is instead
an odd power of a half-Frobenius, whose square is that same `x ↦ x ^ q`. Either way `𝔽_q` is the
field of definition, so the map is worth having for every valid index. This file constructs it,
`TauCeti.ValidLieTypeIndex.frobeniusEquiv`, and identifies the field it fixes.

The construction is Mathlib's iterated Frobenius. Writing `q = p ^ e` with
`TauCeti.LieTypeIndex.fieldExponent`, the map is the `e`-fold iterate of the `p`-power Frobenius of
`TauCeti.ValidLieTypeIndex.Closure`, which is a ring *automorphism* because an algebraically closed
field is perfect. Its fixed field is the copy of `𝔽_q` inside the closure: it has exactly `q`
elements, it is the unique subfield with that many, and every element of the closure is fixed by
some positive iterate. So the ambient field of a group of Lie type is the union of the finite
fields that its Frobenius powers cut out, and the field of definition attached to the index is the
one cut out by `frobeniusEquiv` itself.

Nothing here concerns a group. The graph-twisted branches compose this map with a diagram
automorphism and the Suzuki--Ree branches replace it by an odd power of a half-Frobenius, and both
of those act on a group and not on the field; the field-level map is the same `x ↦ x ^ q` on every
branch, which is why it is defined for every valid index and not only for the untwisted ones.

## Main definitions

* `TauCeti.ValidLieTypeIndex.frobeniusEquiv`: the `q`-power Frobenius automorphism of the closure.
* `TauCeti.ValidLieTypeIndex.fixedField`: the subfield it fixes.

## Main results

* `TauCeti.ValidLieTypeIndex.frobeniusEquiv_apply` and
  `TauCeti.ValidLieTypeIndex.iterate_frobeniusEquiv_apply`: the Frobenius and its iterates raise to
  the corresponding powers of `q`.
* `TauCeti.ValidLieTypeIndex.card_fixedField`: the fixed field has `q` elements.
* `TauCeti.ValidLieTypeIndex.eq_fixedField_of_natCard`: it is the only subfield with `q` elements.
* `TauCeti.ValidLieTypeIndex.nonempty_ringEquiv_galoisField`: it is a copy of `GaloisField p e`.
* `TauCeti.ValidLieTypeIndex.mem_frobeniusFixedSubfield_iff_iterate_frobeniusEquiv_eq`: the `k`-th
  iterate fixes the subfield at exponent `e * k`, which for `k ≠ 0` is the field of `q ^ k`
  elements.
* `TauCeti.ValidLieTypeIndex.exists_iterate_frobeniusEquiv_eq`: every element of the closure is
  fixed by some positive iterate.

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
def frobeniusEquiv : d.Closure ≃+* d.Closure :=
  iterateFrobeniusEquiv d.Closure d.characteristic d.fieldExponent

/-- The Frobenius attached to an index raises to the power recorded by the index. -/
@[simp]
theorem frobeniusEquiv_apply (x : d.Closure) : d.frobeniusEquiv x = x ^ d.fieldOrder := by
  rw [frobeniusEquiv, iterateFrobeniusEquiv_def, ← d.fieldOrder_eq_characteristic_pow]

/-- Iterating the Frobenius attached to an index raises to the corresponding power of `q`. This is
the form the graph-twisted branches use: their Steinberg map has an `r`-th power equal to the plain
`Frob_{q ^ r}`, with `r` the order of the diagram automorphism. -/
theorem iterate_frobeniusEquiv_apply (k : ℕ) (x : d.Closure) :
    (d.frobeniusEquiv : d.Closure → d.Closure)^[k] x = x ^ d.fieldOrder ^ k := by
  rw [show ⇑d.frobeniusEquiv = (· ^ d.fieldOrder) from funext d.frobeniusEquiv_apply, pow_iterate]

/-! ## The field of definition -/

/-- The subfield of the algebraic closure fixed by the Frobenius attached to a valid Lie-type
index: the copy of `𝔽_q` inside the closure, with `q = d.fieldOrder`. -/
def fixedField : Subfield d.Closure :=
  frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent

/-- The fixed field is the Frobenius-fixed subfield at the exponent recorded by the index. -/
theorem fixedField_def :
    d.fixedField = frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent := (rfl)

variable {d}

/-- Membership in the fixed field is the equation `x ^ q = x`. -/
@[simp]
theorem mem_fixedField {x : d.Closure} : x ∈ d.fixedField ↔ x ^ d.fieldOrder = x := by
  rw [fixedField, mem_frobeniusFixedSubfield, d.fieldOrder_eq_characteristic_pow]

/-- The fixed field is the fixed-point set of the Frobenius, which is what makes it the field of
definition of the group cut out by that Frobenius. -/
theorem mem_fixedField_iff_frobeniusEquiv_eq {x : d.Closure} :
    x ∈ d.fixedField ↔ d.frobeniusEquiv x = x := by
  rw [mem_fixedField, frobeniusEquiv_apply]

variable (d)

/-- The fixed field is finite. The exponent is positive on every branch of the index, so unlike the
general statement this needs no side condition. -/
instance : Finite d.fixedField :=
  finite_frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent
    d.fieldExponent_pos.ne'

/-- **The field of definition has `q` elements.** The subfield of the algebraic closure fixed by
the Frobenius attached to a valid Lie-type index has exactly `d.fieldOrder` elements.

This is not a `simp` lemma: `mem_fixedField` already rewrites the membership under the coercion,
so the left-hand side is not in `simp`-normal form. -/
theorem card_fixedField : Nat.card d.fixedField = d.fieldOrder := by
  rw [fixedField,
    card_frobeniusFixedSubfield d.Closure d.characteristic d.fieldExponent
      d.fieldExponent_pos.ne',
    ← d.fieldOrder_eq_characteristic_pow]

/-- The fixed field is the unique subfield of the closure with `d.fieldOrder` elements, so the
index determines it without reference to the Frobenius that cut it out. -/
theorem eq_fixedField_of_natCard {F : Subfield d.Closure}
    (hF : Nat.card F = d.fieldOrder) : F = d.fixedField :=
  eq_frobeniusFixedSubfield_of_natCard d.Closure d.characteristic d.fieldExponent
    (by rw [hF, d.fieldOrder_eq_characteristic_pow])

/-- The fixed field is a copy of Mathlib's `GaloisField`, non-canonically. -/
theorem nonempty_ringEquiv_galoisField :
    Nonempty (d.fixedField ≃+* GaloisField d.characteristic d.fieldExponent) :=
  _root_.TauCeti.nonempty_ringEquiv_galoisField d.Closure d.characteristic d.fieldExponent
    d.fieldExponent_pos.ne'

variable {d}

/-- The elements fixed by the `k`-th iterate of the Frobenius are the fixed subfield at exponent
`fieldExponent * k`, which for `k ≠ 0` is by `card_frobeniusFixedSubfield` the field of `q ^ k`
elements. This identifies the field of definition of a graph-twisted family's ambient untwisted
group: the degree `r` extension of `𝔽_q`, with `r` the order of the diagram automorphism. -/
theorem mem_frobeniusFixedSubfield_iff_iterate_frobeniusEquiv_eq {k : ℕ} {x : d.Closure} :
    x ∈ frobeniusFixedSubfield d.Closure d.characteristic (d.fieldExponent * k) ↔
      (d.frobeniusEquiv : d.Closure → d.Closure)^[k] x = x := by
  rw [iterate_frobeniusEquiv_apply, mem_frobeniusFixedSubfield, pow_mul,
    ← d.fieldOrder_eq_characteristic_pow]

/-- **The closure is the union of the finite fields inside it.** Every element of the algebraic
closure attached to a valid Lie-type index is fixed by some positive iterate of the Frobenius,
hence lies in a finite subfield of the closure.

Together with `card_fixedField` this places the field of definition of the index inside an
exhaustive tower of finite subfields, and it is why the closure, though itself infinite, carries no
element that is not algebraic over a field of definition. -/
theorem exists_iterate_frobeniusEquiv_eq (x : d.Closure) :
    ∃ k ≠ 0, (d.frobeniusEquiv : d.Closure → d.Closure)^[k] x = x := by
  obtain ⟨n, hn, hx⟩ := exists_mem_frobeniusFixedSubfield d.Closure d.characteristic x
  exact ⟨n, hn, mem_frobeniusFixedSubfield_iff_iterate_frobeniusEquiv_eq.mp
    (frobeniusFixedSubfield_le_of_dvd (dvd_mul_left n d.fieldExponent) hx)⟩

end

end TauCeti.ValidLieTypeIndex
