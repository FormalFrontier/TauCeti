/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Domains of the iterates of a partially defined linear map

A partially defined linear map `A : E →ₗ.[R] E` cannot in general be composed with itself:
`LinearPMap.comp` asks for `A x ∈ D(A)` at every `x ∈ D(A)`, which is exactly what fails for an
unbounded operator. What always makes sense is the *domain* of the `n`-th iterate,

`D(A⁰) = E`,  `D(Aⁿ⁺¹) = {x ∈ D(A) | A x ∈ D(Aⁿ)}`,

the largest submodule on which `A` may be applied `n` times in succession. This file defines it
and develops its elementary structure: it shrinks as `n` grows, `D(A¹)` is `D(A)`, and `A` maps
`D(Aⁿ⁺¹)` into `D(Aⁿ)`.

The intended consumer is the theory of strongly continuous semigroups, where `D(Aⁿ)` for the
infinitesimal generator `A` is the space of vectors whose orbit is `n` times continuously
differentiable, and where the density of every `D(Aⁿ)` is the standard regularisation statement.

## Main declarations

* `TauCeti.domainPow`: the submodule `D(Aⁿ)`.
* `TauCeti.mem_domainPow_succ`: the recursive membership criterion defining it.
* `TauCeti.domainPow_antitone`: `D(Aⁿ)` decreases with `n`.
* `TauCeti.apply_mem_domainPow`: `A` maps `D(Aⁿ⁺¹)` into `D(Aⁿ)`.

Tau Ceti puts every declaration under `namespace TauCeti`, so a name in the `LinearPMap`
namespace could not be reached by generalized field notation anyway; these therefore live in the
root `TauCeti` namespace and are written out as `domainPow A n`.
-/

public section

namespace TauCeti

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The domain `D(Aⁿ)` of the `n`-th iterate of a partially defined linear map `A`: the
submodule of vectors to which `A` may be applied `n` times in succession. -/
def domainPow (A : E →ₗ.[R] E) : ℕ → Submodule R E
  | 0 => ⊤
  | n + 1 => Submodule.map A.domain.subtype ((domainPow A n).comap A.toFun)

@[simp]
theorem domainPow_zero (A : E →ₗ.[R] E) : domainPow A 0 = ⊤ := (rfl)

theorem domainPow_succ (A : E →ₗ.[R] E) (n : ℕ) :
    domainPow A (n + 1) = Submodule.map A.domain.subtype ((domainPow A n).comap A.toFun) :=
  (rfl)

/-- Membership in `D(Aⁿ⁺¹)`: a vector of `D(A)` whose image under `A` lies in `D(Aⁿ)`. -/
@[simp]
theorem mem_domainPow_succ {A : E →ₗ.[R] E} {n : ℕ} {x : E} :
    x ∈ domainPow A (n + 1) ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ domainPow A n := by
  rw [domainPow_succ]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hAx⟩
    exact ⟨⟨x, hx⟩, hAx, rfl⟩

@[simp]
theorem domainPow_one (A : E →ₗ.[R] E) : domainPow A 1 = A.domain := by
  ext x
  simp [mem_domainPow_succ]

theorem domainPow_succ_le (A : E →ₗ.[R] E) (n : ℕ) : domainPow A (n + 1) ≤ domainPow A n := by
  induction n with
  | zero => rw [domainPow_zero]; exact le_top
  | succ n ih =>
      intro x hx
      obtain ⟨hxd, hAx⟩ := mem_domainPow_succ.mp hx
      exact mem_domainPow_succ.mpr ⟨hxd, ih hAx⟩

/-- The iterated domains `D(Aⁿ)` decrease as the iteration count increases. -/
theorem domainPow_antitone (A : E →ₗ.[R] E) : Antitone (domainPow A) :=
  antitone_nat_of_succ_le (domainPow_succ_le A)

theorem domainPow_succ_le_domain (A : E →ₗ.[R] E) (n : ℕ) : domainPow A (n + 1) ≤ A.domain := by
  rw [← domainPow_one A]
  exact domainPow_antitone A (Nat.succ_le_succ (Nat.zero_le n))

/-- `A` maps `D(Aⁿ⁺¹)` into `D(Aⁿ)`. -/
theorem apply_mem_domainPow {A : E →ₗ.[R] E} {n : ℕ} {x : E} (hx : x ∈ domainPow A (n + 1)) :
    A ⟨x, domainPow_succ_le_domain A n hx⟩ ∈ domainPow A n :=
  (mem_domainPow_succ.mp hx).choose_spec

end TauCeti

end
