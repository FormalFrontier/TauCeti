/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.Reductive

public section

/-!
# The `sl n` ↔ `gl n` dictionary for irreducible modules

`gl n K` is reductive (`TauCeti.hasCentralRadical_matrix`), its centre is the scalar matrices and
its derived ideal is `sl n K` (`TauCeti.derivedSeries_one_eq_slIdeal`). Specializing the reductive
theory of `TauCeti/Algebra/Lie/Reductive.lean` to that data gives the two halves of the transfer
between the representation theory of `gl n K` and that of `sl n K`:

* restriction to `sl n K` preserves irreducibility, over an algebraically closed field of
  characteristic zero;
* an `sl n K`-equivariant map between `gl n K`-modules on which the identity matrix acts by one and
  the same scalar is already `gl n K`-equivariant.

Both statements are the concrete face of "the centre acts by scalars, and the centre and the
derived ideal span": nothing about a `gl n K`-module is invisible to `sl n K` except the single
scalar by which the identity matrix acts, which is the central weight of
`TauCeti/Algebra/Lie/Weights/Central.lean`.

## Main results

* `TauCeti.isIrreducible_slIdeal_of_isIrreducible_matrix`: **a finite-dimensional irreducible
  `gl n K`-module is irreducible over `sl n K`**, for `K` algebraically closed of characteristic
  zero.
* `TauCeti.map_lie_matrix_of_one_lie_eq_smul_of_forall_mem_slIdeal`: an `sl n K`-equivariant linear
  map between `gl n K`-modules on which `1` acts by the same scalar is `gl n K`-equivariant, with
  `TauCeti.lieModuleEquivOfOneLieEqSmulOfSlEquiv` the packaged equivalence.

## Roadmap

This is the "`sl ↔ gl` transfer, pinned" bullet of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, stated for an arbitrary
irreducible `gl n K`-module rather than for the not-yet-constructed named carrier
`glIrreducible n μ`, which it will specialize to.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u w w'

-- The commutator Lie ring structure of an associative ring is a local instance in Mathlib, to
-- avoid a diamond; it is what makes `Matrix n n K` the Lie algebra `gl n K`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [DecidableEq n] [Fintype n]
variable (K : Type u) [Field K] [CharZero K]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule (Matrix n n K) M]
variable {N : Type w'} [AddCommGroup N] [Module K N] [LieRingModule (Matrix n n K) N]

/-- **An `sl n K`-equivariant map between `gl n K`-modules on which the identity matrix acts by the
same scalar is `gl n K`-equivariant.** `gl n K` is spanned by its centre, the scalar matrices, and
its derived ideal `sl n K` (`TauCeti.sup_center_derivedSeries_eq_top`), so equivariance need only
be checked on those two. -/
theorem map_lie_matrix_of_one_lie_eq_smul_of_forall_mem_slIdeal
    [LieModule K (Matrix n n K) M]
    [LieModule K (Matrix n n K) N] (f : M →ₗ[K] N) {c : K}
    (hM : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hN : ∀ m : N, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hsl : ∀ A ∈ slIdeal K n, ∀ m : M, f ⁅A, m⁆ = ⁅A, f m⁆)
    (A : Matrix n n K) (m : M) :
    f ⁅A, m⁆ = ⁅A, f m⁆ := by
  refine map_lie_of_forall_center_of_forall_derivedSeries K (Matrix n n K) f ?_ ?_ A m
  · rintro z hz m
    obtain ⟨r, rfl⟩ := mem_center_matrix_iff.1 hz
    rw [smul_lie, smul_lie, hM, hN, map_smul, map_smul]
  · rw [derivedSeries_one_eq_slIdeal]
    exact hsl

/-- The packaged form of `TauCeti.map_lie_matrix_of_one_lie_eq_smul_of_forall_mem_slIdeal`: an
`sl n K`-equivariant linear equivalence between `gl n K`-modules on which the identity matrix acts
by the same scalar is an equivalence of `gl n K`-modules. -/
def lieModuleEquivOfOneLieEqSmulOfSlEquiv [LieModule K (Matrix n n K) M]
    [LieModule K (Matrix n n K) N]
    (e : M ≃ₗ[K] N) {c : K}
    (hM : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hN : ∀ m : N, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hsl : ∀ A ∈ slIdeal K n, ∀ m : M, e ⁅A, m⁆ = ⁅A, e m⁆) :
    M ≃ₗ⁅K, Matrix n n K⁆ N where
  __ := e
  map_lie' {A m} :=
    map_lie_matrix_of_one_lie_eq_smul_of_forall_mem_slIdeal K
      (e : M →ₗ[K] N) hM hN hsl A m

@[simp]
theorem lieModuleEquivOfOneLieEqSmulOfSlEquiv_apply [LieModule K (Matrix n n K) M]
    [LieModule K (Matrix n n K) N] (e : M ≃ₗ[K] N) {c : K}
    (hM : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hN : ∀ m : N, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hsl : ∀ A ∈ slIdeal K n, ∀ m : M, e ⁅A, m⁆ = ⁅A, e m⁆) (m : M) :
    lieModuleEquivOfOneLieEqSmulOfSlEquiv K e hM hN hsl m = e m :=
  (rfl)

@[simp]
theorem lieModuleEquivOfOneLieEqSmulOfSlEquiv_symm_apply [LieModule K (Matrix n n K) M]
    [LieModule K (Matrix n n K) N] (e : M ≃ₗ[K] N) {c : K}
    (hM : ∀ m : M, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hN : ∀ m : N, ⁅(1 : Matrix n n K), m⁆ = c • m)
    (hsl : ∀ A ∈ slIdeal K n, ∀ m : M, e ⁅A, m⁆ = ⁅A, e m⁆) (n : N) :
    (lieModuleEquivOfOneLieEqSmulOfSlEquiv K e hM hN hsl).symm n = e.symm n :=
  (rfl)

variable (M) [IsAlgClosed K] [LieModule K (Matrix n n K) M] [FiniteDimensional K M]
variable [LieModule.IsIrreducible K (Matrix n n K) M]

/-- **A finite-dimensional irreducible `gl n K`-module is irreducible over `sl n K`**, for `K`
algebraically closed of characteristic zero. This is
`TauCeti.isIrreducible_restrict_derivedSeries` for the reductive Lie algebra `gl n K`, whose
derived ideal is `sl n K`; the scalar matrices act by the central weight and so stabilize every
subspace. -/
theorem isIrreducible_slIdeal_of_isIrreducible_matrix :
    LieModule.IsIrreducible K (slIdeal K n) M :=
  derivedSeries_one_eq_slIdeal K n ▸ isIrreducible_restrict_derivedSeries K (Matrix n n K) M

end TauCeti
