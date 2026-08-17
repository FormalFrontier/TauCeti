/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Pure inseparability above the range of finite-field Frobenius

Let `K` be a finite field with `q` elements and let `L` be any field extension of `K`. The image
of the `q`-power endomorphism of `L` is a subfield over which `L` is purely inseparable: every
`x : L` has `x ^ q` in that image, and `q` is a power of the exponential characteristic.

## Main result

* `TauCeti.FiniteField.isPurelyInseparable_fieldRange_frobeniusAlgHom`: `L` is purely
  inseparable over the field range of `FiniteField.frobeniusAlgHom K L`.

## Roadmap

This is the field-theoretic input to the Frobenius isogeny in Layer 1 of
`TauCetiRoadmap/EllipticCurves/README.md`, which requires `π_q` to be purely inseparable of degree
`q`. Stating it before specializing to a curve keeps the argument independent of the particular
function field, just as the degree computation first identifies the field range of the same
`q`-power map.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti.FiniteField

variable {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]

/-- **A field is purely inseparable over the image of its finite-base-field Frobenius**
(the field-theoretic statement in Silverman II.2.11(b)). Every element has its `q`-th power in
the image, where `q = Nat.card K` is a power of the exponential characteristic. -/
theorem isPurelyInseparable_fieldRange_frobeniusAlgHom :
    letI := Fintype.ofFinite K
    IsPurelyInseparable (_root_.FiniteField.frobeniusAlgHom K L).fieldRange L := by
  let _ := Fintype.ofFinite K
  obtain ⟨p, hpK, n, hp, hcard⟩ := _root_.FiniteField.card' K
  let _ : CharP K p := hpK
  let _ : ExpChar K p := ExpChar.prime hp
  have hcard' : Nat.card K = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  have hx : x ^ p ^ (n : ℕ) ∈
      (_root_.FiniteField.frobeniusAlgHom K L).fieldRange := by
    rw [AlgHom.mem_fieldRange]
    refine ⟨x, ?_⟩
    rw [_root_.FiniteField.coe_frobeniusAlgHom, ← Nat.card_eq_fintype_card, hcard']
  refine ⟨(n : ℕ), ?_⟩
  refine ⟨⟨x ^ p ^ (n : ℕ), hx⟩, ?_⟩
  exact IntermediateField.algebraMap_apply
    (S := (_root_.FiniteField.frobeniusAlgHom K L).fieldRange) _

end TauCeti.FiniteField

end
