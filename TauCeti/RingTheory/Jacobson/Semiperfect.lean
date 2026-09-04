/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Semiperfect rings

A ring is **semiperfect** when its radical quotient `R ⧸ Ring.jacobson R` is a semisimple ring and
idempotents lift modulo the radical. This is the hypothesis under which projective covers of
finitely generated modules exist, and it is the property of a finite-dimensional algebra that
`TauCeti/Algebra/Module/ProjectiveCover/Existence.lean` uses in its sharper, nilpotent form.

Mathlib packages the neighbouring notion, `IsSemiprimaryRing`: the radical is *nilpotent* and the
radical quotient is semisimple. Nilpotence of the radical makes its elements nil, so idempotents
lift along `R ↠ R ⧸ Ring.jacobson R` by Mathlib's
`exists_isIdempotentElem_eq_of_ker_isNilpotent`; a semiprimary ring is therefore semiperfect
(`TauCeti.IsSemiperfectRing.of_isSemiprimaryRing`), and a finite-dimensional algebra over a field,
being an Artinian ring, is semiprimary and hence semiperfect
(`TauCeti.isSemiperfectRing_of_finiteDimensional`).

Bass' characterization — `R` is semiperfect exactly when every finitely generated `R`-module has a
projective cover — is not proved here. The existence half of it over a semiprimary ring, in the
stronger form that covers *every* module, is
`TauCeti.exists_isProjectiveCover`.

## Main definitions

* `TauCeti.IsSemiperfectRing`: the radical quotient is semisimple and idempotents lift modulo the
  radical.

## Main results

* `TauCeti.IsSemiperfectRing.of_isSemiprimaryRing`: a semiprimary ring is semiperfect.
* `TauCeti.isSemiperfectRing_of_finiteDimensional`: a finite-dimensional algebra over a field is
  semiperfect.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, §23-24.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) [Ring R]

/-- A ring is **semiperfect** if its quotient by the Jacobson radical is a semisimple ring and
every idempotent of that quotient is the class of an idempotent of the ring. -/
class IsSemiperfectRing : Prop where
  /-- The radical quotient of a semiperfect ring is a semisimple ring. -/
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
  /-- Idempotents lift modulo the Jacobson radical. -/
  exists_isIdempotentElem_eq (e : R ⧸ Ring.jacobson R) (he : IsIdempotentElem e) :
    ∃ f : R, IsIdempotentElem f ∧ Ideal.Quotient.mk (Ring.jacobson R) f = e

attribute [instance] IsSemiperfectRing.isSemisimpleRing

/-- **A semiprimary ring is semiperfect.** Its radical quotient is semisimple by definition, and
every element of its radical is nilpotent because the radical is, so idempotents lift along
`R ↠ R ⧸ Ring.jacobson R` by `exists_isIdempotentElem_eq_of_ker_isNilpotent`. -/
instance IsSemiperfectRing.of_isSemiprimaryRing [IsSemiprimaryRing R] : IsSemiperfectRing R where
  isSemisimpleRing := inferInstance
  exists_isIdempotentElem_eq e he := by
    refine exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk (Ring.jacobson R))
      (fun x hx => ?_) e (RingHom.mem_range.mpr (Ideal.Quotient.mk_surjective e)) he
    obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := R)
    rw [Ideal.mk_ker] at hx
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at this

/-- **A finite-dimensional algebra is semiperfect.** It is an Artinian ring, hence semiprimary,
hence semiperfect. -/
theorem isSemiperfectRing_of_finiteDimensional (k : Type v) [Field k] (A : Type u) [Ring A]
    [Algebra k A] [FiniteDimensional k A] : IsSemiperfectRing A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  infer_instance

end TauCeti
