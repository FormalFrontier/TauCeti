/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Division with remainder by a monic polynomial, against `degreeLT`

Mathlib's `Polynomial.degreeLT R n` is the submodule `R[X]_n` of polynomials of degree `< n`, and
`p %ₘ g` / `p /ₘ g` are division with remainder by a monic `g`. Mathlib relates the two only for
`g = X ^ m`, through `Polynomial.degreeLT.addLinearEquiv`; this file records the general monic
statements: that `%ₘ g` lands in `R[X]_(g.natDegree)`, that `/ₘ g` drops the degree bound by
`g.natDegree`, and how both read off `g * v + u`.

Together they say that `q ↦ (q %ₘ g, q /ₘ g)` inverts `(u, v) ↦ g * v + u`, which is the
`p = 1` case of the Sylvester map. `TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot` turns
that into a linear equivalence and uses it to identify a norm with a resultant.

## Main results

* `Polynomial.mem_degreeLT_natDegree_iff`: membership in `R[X]_(g.natDegree)` is `degree < degree`.
* `Polynomial.modByMonic_mem_degreeLT`, `Polynomial.divByMonic_mem_degreeLT`: where `%ₘ` and `/ₘ`
  land.
* `Polynomial.Monic.modByMonic_mul_add`, `Polynomial.Monic.divByMonic_mul_add`: division with
  remainder reads off `g * v + u`.

Stated over an arbitrary commutative ring, with the trivial ring dispatched by `nontriviality`
rather than excluded by hypothesis; `mem_degreeLT_natDegree_iff` needs only a semiring.

## Provenance

Adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file `EllipticCurves/Mathlib/Basic.lean` lines
629-690, where these are collected as Mathlib-bound prerequisites of the resultant description of
the norm on `AdjoinRoot`. The source targets Lean `v4.32.0`; this is a forward port, and the
proofs of `Monic.modByMonic_mul_add` and `Monic.divByMonic_mul_add` are restated over Mathlib's
current `Polynomial.add_modByMonic` and `Polynomial.self_mul_modByMonic` rather than over the
source's shared `div_modByMonic_unique` helper.
-/

public section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] {g q : R[X]}

theorem mem_degreeLT_natDegree_iff (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

end Semiring

variable {R : Type*} [CommRing R] {g q : R[X]} {n : ℕ}

@[simp]
theorem Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g := by
  rw [add_modByMonic, self_mul_modByMonic hg, zero_add]

theorem modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree := by
  nontriviality R
  exact (mem_degreeLT_natDegree_iff hg.ne_zero).mpr (degree_modByMonic_lt q hg)

theorem divByMonic_mem_degreeLT (hg : g.Monic) (hq : q ∈ degreeLT R (g.natDegree + n)) :
    q /ₘ g ∈ degreeLT R n := by
  nontriviality R
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

theorem Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g := by
  nontriviality R
  refine (div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩).1
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

end Polynomial
