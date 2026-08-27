/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic

/-!
# The Selmer group of a number field is finite

The finiteness proved in `TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic` asks its
Dedekind domain for a finite class group and a finitely generated unit group. For the ring of
integers of a number field both are theorems of Mathlib -- the class number theorem and
Dirichlet's unit theorem -- so there the Selmer group `K(S, n)` is finite with no hypothesis
beyond the finiteness of `S`.

## Main results

* `IsDedekindDomain.finite_selmerGroup_of_numberField`: `K(S, n)` is finite for every finite `S`
  and every `n` with `NeZero n`.

## References

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at the
`EllipticCurves` roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), where the same
specialisation is drawn from the general finiteness statement.
-/

public section

namespace IsDedekindDomain

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)

/-- The Selmer group `K(S, n)` of a number field is finite for `S` finite and `n` with
`NeZero n`. -/
theorem finite_selmerGroup_of_numberField [NeZero n] (hS : S.Finite) :
    Finite (selmerGroup (R := 𝓞 F) (K := F) (S := S) (n := n)) := by
  have : Finite S := hS.to_subtype
  infer_instance

end IsDedekindDomain

end
