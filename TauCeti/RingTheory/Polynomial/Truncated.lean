/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The truncated polynomial algebra `R[X]/(Xⁿ⁺¹)`

Mathlib builds `AdjoinRoot f` for any polynomial and, for a monic `f`, its power basis
`AdjoinRoot.powerBasis'`. It does not record what the quotient by a power of `X` looks like. This
file does: the class of `X` is nilpotent, over a field the algebra `k[X]/(Xⁿ⁺¹)` is a **local**
ring, and `R[X]/(Xⁿ)` is free of dimension `n`.

Locality is the useful form of the statement, because it is what pins the idempotents: through
`TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem` a truncated polynomial algebra has no
idempotent besides `0` and `1`. That is exactly the input to the indecomposability of a nilpotent
Jordan block, whose endomorphism algebra is `k[X]/(Xⁿ⁺¹)`.

The other half of that indecomposability argument -- that an endomorphism of the Jordan block *is*
multiplication by an element of `k[X]/(Xⁿ⁺¹)` -- is `TauCeti.eq_mulRight_of_root_mul`. It needs
nothing about `Xⁿ⁺¹` beyond monicity, so it is stated for an arbitrary monic relator; the truncated
algebras are its consumers, which is why it lives here.

## Main results

* `TauCeti.isNilpotent_root_X_pow`: the class of `X` is nilpotent in `R[X]/(Xⁿ⁺¹)`.
* `TauCeti.isLocalRing_adjoinRoot_X_pow`: over a field, `k[X]/(Xⁿ⁺¹)` is a local ring.
* `TauCeti.finrank_adjoinRoot_X_pow`: `R[X]/(Xⁿ)` has dimension `n` over `R`.
* `TauCeti.eq_mulRight_of_root_mul`: an `R`-linear endomorphism of `AdjoinRoot g`, for `g` monic,
  that commutes with multiplication by the root is multiplication by its value at `1`.

## Implementation notes

The evaluation `R[X]/(Xⁿ⁺¹) → R` reading off the constant term is `AdjoinRoot.lift` of the identity
of `R` at the root `0`, and `AdjoinRoot.lift_mk` computes it on a class. It is a step in the proof
of locality rather than API, so the three lemmas phrased against that unnamed map -- that it is well
defined, that its kernel consists of nilpotents, and that an element it sends to a unit is a unit --
are `private`.

Locality is proved from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`, splitting an element as its
constant term plus an element of the kernel: the constant term is a scalar, hence invertible unless
it vanishes, and adding a nilpotent to a unit leaves a unit
(`IsNilpotent.isUnit_add_left_of_commute`). Nontriviality, which that criterion needs, is
`AdjoinRoot.nontrivial` applied to the positive degree of `Xⁿ⁺¹`.

Everything except locality is stated over a commutative ring, since no proof below inverts
anything; locality itself genuinely wants a field, being the one place where a nonzero constant
term has to be a unit.

The dimension is stated for `Xⁿ` rather than for `Xⁿ⁺¹`, since the degenerate case `n = 0` -- the
zero ring, of dimension `0` -- is true and costs nothing; locality genuinely needs `n + 1`, the
zero ring not being local.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **The class of `X` is nilpotent in `R[X]/(Xⁿ⁺¹)`**: its `(n + 1)`-st power is the class of the
relator. -/
theorem isNilpotent_root_X_pow (n : ℕ) :
    IsNilpotent (AdjoinRoot.root ((X : R[X]) ^ (n + 1))) :=
  ⟨n + 1, by rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]⟩

/-- The evaluation `R[X]/(Xⁿ⁺¹) → R` at `0` is well defined: `Xⁿ⁺¹` vanishes at `0`. -/
private theorem eval₂_id_zero_X_pow_eq_zero (n : ℕ) :
    ((X : R[X]) ^ (n + 1)).eval₂ (RingHom.id R) 0 = 0 := by
  simp

/-- **An element of `R[X]/(Xⁿ⁺¹)` with vanishing constant term is nilpotent.** Such an element is
the class of a polynomial divisible by `X`, hence a multiple of the nilpotent class of `X`. -/
private theorem isNilpotent_of_lift_eq_zero_X_pow {n : ℕ} {x : AdjoinRoot ((X : R[X]) ^ (n + 1))}
    (hx : AdjoinRoot.lift (RingHom.id R) (0 : R) (eval₂_id_zero_X_pow_eq_zero n) x = 0) :
    IsNilpotent x := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hp : p.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa [AdjoinRoot.lift_mk, Polynomial.eval] using hx
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hp
    rw [map_mul, AdjoinRoot.mk_X]
    exact (Commute.all _ _).isNilpotent_mul_right (isNilpotent_root_X_pow n)

/-- An element of `R[X]/(Xⁿ⁺¹)` whose constant term is a unit is a unit: it is the sum of that unit
and a nilpotent. -/
private theorem isUnit_of_isUnit_lift_X_pow {n : ℕ} {x : AdjoinRoot ((X : R[X]) ^ (n + 1))}
    (hx : IsUnit (AdjoinRoot.lift (RingHom.id R) (0 : R) (eval₂_id_zero_X_pow_eq_zero n) x)) :
    IsUnit x := by
  set c := AdjoinRoot.lift (RingHom.id R) (0 : R) (eval₂_id_zero_X_pow_eq_zero n) x with hc
  have hker : AdjoinRoot.lift (RingHom.id R) (0 : R) (eval₂_id_zero_X_pow_eq_zero n)
      (x - algebraMap R _ c) = 0 := by
    rw [map_sub, ← hc, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, RingHom.id_apply, sub_self]
  have hunit : IsUnit (algebraMap R (AdjoinRoot ((X : R[X]) ^ (n + 1))) c) :=
    hx.map (algebraMap R _)
  have := (isNilpotent_of_lift_eq_zero_X_pow hker).isUnit_add_left_of_commute hunit
    (Commute.all _ _)
  rwa [add_sub_cancel] at this

/-- **The truncated polynomial algebra `R[X]/(Xⁿ)` has dimension `n`**: the classes of the powers of
`X` below `n` are a basis, Mathlib's `AdjoinRoot.powerBasis'` for the monic relator `Xⁿ`. -/
theorem finrank_adjoinRoot_X_pow (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    Module.finrank R (AdjoinRoot ((X : R[X]) ^ n)) = n := by
  rw [(AdjoinRoot.powerBasis' (monic_X_pow (R := R) n)).finrank]
  simp

/-- **An `R`-linear endomorphism of `AdjoinRoot g` commuting with multiplication by the root is
multiplication by its value at `1`.** It commutes with multiplication by every power of the root,
and for a monic relator those powers are a basis (`AdjoinRoot.powerBasis'`). -/
theorem eq_mulRight_of_root_mul {g : R[X]} (hg : g.Monic)
    {f : AdjoinRoot g →ₗ[R] AdjoinRoot g}
    (hf : ∀ x, f (AdjoinRoot.root g * x) = AdjoinRoot.root g * f x) :
    f = LinearMap.mulRight R (f 1) := by
  have hpow : ∀ i : ℕ, f (AdjoinRoot.root g ^ i) = AdjoinRoot.root g ^ i * f 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ' (AdjoinRoot.root g) i, hf, ih, ← mul_assoc,
        ← pow_succ' (AdjoinRoot.root g) i]
  refine (AdjoinRoot.powerBasis' hg).basis.ext fun i ↦ ?_
  rw [PowerBasis.coe_basis]
  simpa using hpow i

section Field

variable {k : Type*} [Field k]

/-- **The truncated polynomial algebra `k[X]/(Xⁿ⁺¹)` is a local ring.** An element is a unit exactly
when its constant term is, since the elements of vanishing constant term are nilpotent; so of `x`
and `1 - x` at least one has a nonzero constant term. -/
instance isLocalRing_adjoinRoot_X_pow (n : ℕ) :
    IsLocalRing (AdjoinRoot ((X : k[X]) ^ (n + 1))) := by
  have : Nontrivial (AdjoinRoot ((X : k[X]) ^ (n + 1))) := by
    refine AdjoinRoot.nontrivial _ ?_
    rw [degree_X_pow]
    exact_mod_cast Nat.succ_ne_zero n
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  rcases eq_or_ne (AdjoinRoot.lift (RingHom.id k) (0 : k) (eval₂_id_zero_X_pow_eq_zero n) x) 0 with
    h | h
  · refine Or.inr (isUnit_of_isUnit_lift_X_pow ?_)
    rw [map_sub, map_one, h, sub_zero]
    exact isUnit_one
  · exact Or.inl (isUnit_of_isUnit_lift_X_pow h.isUnit)

end Field

end TauCeti
