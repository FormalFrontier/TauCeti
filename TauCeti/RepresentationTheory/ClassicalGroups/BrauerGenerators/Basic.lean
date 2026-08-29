/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Bookkeeping for the Brauer generators on two strands

A Brauer diagram on two strands acts on a tensor square, so the calculations in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal` and in
`TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic` both expand pure
tensors indexed by `Fin 2`. That expansion needs the same two pieces of glue in either file: a sum
over the functions `Fin 2 → ι` is a double sum, and a pure tensor indexed by `Fin 2` may be
rewritten in `![·, ·]` form. Neither says anything about an invariant form, so both live here
rather than being repeated in the two files that use them.

## Main results

* `TauCeti.sum_pi_fin_two`: a sum over `Fin 2 → ι` is a double sum over `ι`.
* `TauCeti.tprod_fin_two`: a pure tensor on two strands is `⨂ₜ ![v 0, v 1]`.
-/

public section

namespace TauCeti

/-- A sum over the functions `Fin 2 → ι` is a double sum. -/
theorem sum_pi_fin_two {ι M : Type*} [Fintype ι] [AddCommMonoid M] (f : ι → ι → M) :
    ∑ r : Fin 2 → ι, f (r 0) (r 1) = ∑ p : ι, ∑ q : ι, f p q :=
  Eq.trans
    (Fintype.sum_equiv (piFinTwoEquiv fun _ : Fin 2 => ι) _
      (fun pq : ι × ι => f pq.1 pq.2) fun _ => rfl)
    (Fintype.sum_prod_type' f)

/-- A pure tensor on two strands, written in `![·, ·]` form. -/
theorem tprod_fin_two {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 2 → M) :
    PiTensorProduct.tprod R v = PiTensorProduct.tprod R ![v 0, v 1] := by
  congr 1
  funext i
  fin_cases i <;> simp

end TauCeti
