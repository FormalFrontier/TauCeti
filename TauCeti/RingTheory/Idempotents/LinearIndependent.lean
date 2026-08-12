/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal nonzero idempotents are linearly independent

Let `k` be a commutative ring whose multiplication cancels (`IsCancelMulZero`, so in particular any
integral domain), let `A` be a torsion-free `k`-algebra -- no nonzero scalar annihilates a nonzero
element -- and let `e : ι → A` be a family of pairwise orthogonal idempotents, none of them zero.
Then the `eᵢ` are linearly independent over `k`: multiplying a vanishing combination
`∑ᵢ gᵢ • eᵢ = 0` by `e_j` kills every term but the `j`-th, which orthogonality and idempotence
leave as `g_j • e_j = 0`.

Mathlib has orthogonal families of idempotents (`OrthogonalIdempotents`, in
`Mathlib/RingTheory/Idempotents.lean`) and the ring-theoretic decompositions they generate, but
records nothing about their linear independence, which is what makes a complete orthogonal family
of the right size a *basis*.

## Main results

* `TauCeti.linearIndependent_of_orthogonalIdempotents`: **a family of pairwise orthogonal nonzero
  idempotents is linearly independent.**
-/

public section

namespace TauCeti

/-- **A family of pairwise orthogonal nonzero idempotents of a `k`-algebra is linearly
independent.** Multiplying a vanishing combination `∑ᵢ gᵢ • eᵢ = 0` by `e_j` kills every term but
the `j`-th and leaves `g_j • e_j = 0`, so `g_j = 0`. -/
theorem linearIndependent_of_orthogonalIdempotents {k A ι : Type*} [CommRing k]
    [IsCancelMulZero k] [Ring A] [Algebra k A] [Module.IsTorsionFree k A] {e : ι → A}
    (he : OrthogonalIdempotents e)
    (he₀ : ∀ i, e i ≠ 0) : LinearIndependent k e := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  have hmul := congrArg (· * e j) hg
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at hmul
  rw [Finset.sum_eq_single j] at hmul
  · rw [(he.idem j).eq] at hmul
    exact (smul_eq_zero.mp hmul).resolve_right (he₀ j)
  · intro i _ hij
    rw [he.ortho hij, smul_zero]
  · exact fun h => absurd hj h

end TauCeti
