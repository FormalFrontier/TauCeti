/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# A power of the image of a finitely generated ideal

Let `I` be an ideal of a semiring `B` and let `f : B →+* C` be a ring homomorphism into a
commutative semiring. If every prime of `C` contains `I.map f`, that image lies in the nilradical
of `C`; when `I` is finitely generated the image is then a nilpotent ideal, so one of its powers
is `⊥`.

Nothing here mentions localisation, and nothing subtracts, so the statement is made for an
arbitrary ring homomorphism, with commutativity assumed only where primes are taken.

## Main results

* `Ideal.exists_pow_map_eq_bot`: if `I` is finitely generated and `I.map f` is contained in every
  prime of `C`, then `(I.map f) ^ n = ⊥` for some `n`.
-/

public section

namespace Ideal

variable {B C : Type*} [Semiring B] [CommSemiring C] {I : Ideal B}

/-- **A power of the image of `I` vanishes.** If every prime of `C` contains the image of `I`
under `f`, that image lies in the nilradical; being finitely generated it is then nilpotent. -/
theorem exists_pow_map_eq_bot (f : B →+* C) (hfg : I.FG)
    (hprime : ∀ P : Ideal C, P.IsPrime → I.map f ≤ P) :
    ∃ n : ℕ, (I.map f) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := (hfg.map f).isNilpotent_iff_le_nilradical.mpr
    fun x hx ↦ mem_nilradical.mpr (nilpotent_iff_mem_prime.mpr fun P hP ↦ hprime P hP hx)
  exact ⟨n, by simpa using hn⟩

end Ideal
