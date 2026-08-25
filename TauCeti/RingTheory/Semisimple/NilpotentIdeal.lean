/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Square-zero left ideals of a semisimple ring

A semisimple ring has no nonzero left ideal `I` with `I * I = 0`.  This is the standard way a
semisimple ring is used to rule out a degenerate case: one produces a left ideal on which
multiplication vanishes identically and concludes that the ideal was zero all along.

The proof is the complement argument, and it needs nothing but the definition of semisimplicity
as complementedness of the lattice of submodules.  Split the ring as `I ⊕ J` for a left ideal `J`
and write `1 = e + f` accordingly.  For `x ∈ I` the product `x * e` lies in `I * I`, so it
vanishes and `x = x * 1 = x * f`.  But `x * f = x • f` lies in the left ideal `J`, so `x` lies in
`I ⊓ J = ⊥`.

The hypothesis is spelled out elementwise rather than as an equation between submodules, because
a left ideal of a noncommutative ring is a `Submodule R R` and carries no multiplication of its
own.

## Main results

* `TauCeti.Submodule.eq_bot_of_forall_mul_eq_zero`: a left ideal of a semisimple ring whose
  elements multiply to zero is the zero ideal.
-/

public section

namespace TauCeti

namespace Submodule

variable {R : Type*} [Ring R] [IsSemisimpleRing R]

/-- **A square-zero left ideal of a semisimple ring is zero.**  Semisimplicity enters only through
the existence of a complementary left ideal. -/
theorem eq_bot_of_forall_mul_eq_zero {I : _root_.Submodule R R}
    (h : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) : I = ⊥ := by
  obtain ⟨J, hJ⟩ := exists_isCompl I
  obtain ⟨e, he, f, hf, hef⟩ :=
    _root_.Submodule.mem_sup.mp (hJ.sup_eq_top ▸ _root_.Submodule.mem_top (x := 1))
  refine le_bot_iff.mp fun x hx => ?_
  have hxf : x = x * f := by
    have hx1 : x * (e + f) = x := by rw [hef, mul_one]
    rwa [mul_add, h x hx e he, zero_add, eq_comm] at hx1
  have hmem : x ∈ I ⊓ J := ⟨hx, hxf ▸ J.smul_mem x hf⟩
  simpa [hJ.inf_eq_bot] using hmem

end Submodule

end TauCeti
