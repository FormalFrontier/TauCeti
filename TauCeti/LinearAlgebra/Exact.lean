/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finiteness consequences of exact sequences

This file records two elementary consequences of exactness at the middle term: finite-dimensional
outer vector spaces (over a division ring) force the middle vector space to be finite-dimensional,
and trivial outer types force the middle additive group to be trivial.
-/

public section

namespace TauCeti

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are finite-dimensional, then so
is `N`.

This is deduced from `Module.Finite.of_exact`, which asks the second map to be surjective, by
corestricting `g` to its range. -/
theorem finiteDimensional_of_exact {k M N P : Type*} [DivisionRing k] [AddCommGroup M]
    [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] {f : M →ₗ[k] N}
    {g : N →ₗ[k] P}
    (h : Function.Exact f g) [FiniteDimensional k M] [FiniteDimensional k P] :
    FiniteDimensional k N :=
  Module.Finite.of_exact (g := g.rangeRestrict)
    (fun x ↦ by rw [← h x, ← Subtype.coe_inj]; simp) g.surjective_rangeRestrict

/-- If `M --f--> N --g--> P` is exact at `N` and both `M` and `P` are trivial, then so is `N`. -/
theorem subsingleton_of_exact {M N P : Type*} [Zero M] [AddCommGroup N] [Zero P] {f : M → N}
    {g : N → P} (h : Function.Exact f g) (hf : f 0 = 0) [Subsingleton M] [Subsingleton P] :
    Subsingleton N := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (h x).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, hf]

end TauCeti
