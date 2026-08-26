/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.LinearAlgebra.LinearPMap.DomainPow

/-!
# The resolvent raises the order of an iterated domain

At a point `lambda` of the resolvent set of an unbounded operator `A`, the resolvent
`R(lambda, A)` is a right inverse of `lambda • I - A`, so `A R(lambda) y = lambda R(lambda) y - y`
for every `y`. Reading that identity as a recursion turns a single regularity step,
`R(lambda) y ∈ D(A)`, into the statement that `R(lambda)` maps `D(Aⁿ)` into `D(Aⁿ⁺¹)`; in
particular `R(lambda)ⁿ` lands in `D(Aⁿ)`.

These are the regularising maps behind the density of the iterated domains `D(Aⁿ)`, since
`lambdaⁿ R(lambda)ⁿ` converges strongly to the identity for a generator.

## Main results

* `TauCeti.resolvent_mem_domainPow_succ`: `R(lambda)` maps `D(Aⁿ)` into `D(Aⁿ⁺¹)`.
* `TauCeti.resolvent_pow_mem_domainPow`: `R(lambda)ⁿ` maps `X` into `D(Aⁿ)`.
-/

public section

noncomputable section

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : X →ₗ.[ℝ] X} {lambda : ℝ}

/-- The resolvent raises the order of an iterated domain by one: it maps `D(Aⁿ)` into
`D(Aⁿ⁺¹)`. -/
theorem resolvent_mem_domainPow_succ (h : lambda ∈ LinearPMap.resolventSet A) {n : ℕ} {x : X}
    (hx : x ∈ domainPow A n) :
    LinearPMap.resolvent A lambda x ∈ domainPow A (n + 1) := by
  induction n generalizing x with
  | zero =>
      rw [zero_add, domainPow_one]
      exact LinearPMap.resolvent_mem_domain h x
  | succ n ih =>
      refine mem_domainPow_succ.mpr ⟨LinearPMap.resolvent_mem_domain h x, ?_⟩
      rw [LinearPMap.apply_resolvent h x]
      exact sub_mem (Submodule.smul_mem _ lambda (ih (domainPow_succ_le A n hx))) hx

/-- The `n`-th power of the resolvent regularises every vector to order `n`: it maps `X` into
`D(Aⁿ)`. -/
theorem resolvent_pow_mem_domainPow (h : lambda ∈ LinearPMap.resolventSet A) (n : ℕ) (x : X) :
    (LinearPMap.resolvent A lambda ^ n) x ∈ domainPow A n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (LinearPMap.resolvent A lambda ^ (n + 1)) x
          = LinearPMap.resolvent A lambda ((LinearPMap.resolvent A lambda ^ n) x) := by
        rw [pow_succ', mul_apply_eq_comp]
      rw [hstep]
      exact resolvent_mem_domainPow_succ h ih

end TauCeti

end

end
