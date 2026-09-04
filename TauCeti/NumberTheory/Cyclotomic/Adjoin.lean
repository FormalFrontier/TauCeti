/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Adjoining roots of unity as an intermediate field

Adjoining one primitive `m`-th root of unity to `K` inside `M` gives the same intermediate field as
adjoining all the `m`-th roots of unity.

Mathlib proves the corresponding equalities for `Algebra.adjoin`, in
`IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic` and
`IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots`. This file carries them across
`IntermediateField.adjoin_toSubalgebra` to the `IntermediateField` lattice, which is where the
Galois correspondence needs them.

## Main results

* `IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots`: `K(ζ) = K(μ_m)`.
-/

public section

open IntermediateField

/-- **Adjoining one primitive `m`-th root adjoins them all.** `K(ζ) = K(μ_m)` inside any
extension of `K` containing a primitive `m`-th root of unity `ζ`.

No algebraicity of the ambient extension is needed: each `m`-th root of unity is algebraic on
its own, being a root of the nonzero polynomial `X ^ m - 1`. -/
theorem IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) : adjoin K {ζ} = adjoin K {b : M | b ^ m = 1} := by
  -- an `m`-th root of unity is algebraic, being a root of unity
  have halg : ∀ b : M, b ^ m = 1 → IsAlgebraic K b := fun b hb ↦
    IsAlgebraic.of_pow (NeZero.pos m) (by rw [hb]; exact isAlgebraic_one)
  refine toSubalgebra_injective ?_
  rw [adjoin_toSubalgebra_of_isAlgebraic (S := {ζ})
      (fun x hx ↦ halg x (by rw [Set.mem_singleton_iff.mp hx]; exact hζ.pow_eq_one)),
    adjoin_toSubalgebra_of_isAlgebraic (S := {b : M | b ^ m = 1}) (fun x hx ↦ halg x hx)]
  refine (IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
    (A := K) hζ).symm.trans ?_
  refine (IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots (A := K) hζ).trans ?_
  congr 1
  ext b
  simp [NeZero.ne m]
