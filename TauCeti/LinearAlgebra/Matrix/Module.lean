/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Vanishing of a family fixed by a matrix

A family `y : n → P` in a module over a ring `A` satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` is exactly a
fixed point of the `Matrix n n A`-action on `n → P`, so it is killed by `1 - B`. If `1 - B` is
a unit, `y` vanishes.

This is pure algebra: no topology, and `A` need not be commutative. It is stated here rather
than beside the topological criteria that produce `IsUnit (1 - B)`, so that consumers do not
have to import a ring theory they do not use — in particular it applies where `P` is an
abstract subquotient with no topology of its own.

## Main results

* `TauCeti.eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul`: a family fixed by `B` vanishes as
  soon as `1 - B` is a unit.

## References

* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert],
  §3.7.2/1, where this is the algebraic engine behind closedness of finitely generated
  submodules.
-/

public section

open scoped Matrix.Module

namespace TauCeti

/-- **Nakayama once `1 - B` is known to be a unit.** A family with `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` is killed by
`1 - B` under the `Matrix n n A`-action on `n → P`, so invertibility of `1 - B` forces `y = 0`.

Nothing topological appears: `P` carries no topology, and `A` is an arbitrary ring — the matrix
action needs no commutativity. -/
theorem eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul {A : Type*} [Ring A] {n : Type*}
    [Fintype n] [DecidableEq n] {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hU : IsUnit (1 - B))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) : y = 0 := by
  have hrel : (1 - B) • y = 0 := by
    funext i
    simp only [Matrix.Module.smul_apply, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib,
      Matrix.one_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      one_smul, Pi.zero_apply]
    rw [← hy i, sub_self]
  exact hU.smul_eq_zero.mp hrel

end TauCeti
