/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis

/-!
# The coordinates of a pure symmetric tensor

`TauCeti/LinearAlgebra/SymmetricPower/Basis.lean` builds the basis `Module.Basis.symmetricPower`
of `Sym[R]^n M` induced by a basis `b : Basis κ R M`, and reads off the coordinates of a pure
symmetric tensor whose factors are *basis vectors*: it is a basis vector.  This file reads off the
coordinates of a pure symmetric tensor `⨂ₛ v` whose factors are arbitrary.

Expanding each factor in the basis and using multilinearity writes `⨂ₛ v` as a sum, over the
ordered tuples `p : Fin n → κ`, of the pure tensors `⨂ₛ i, b (p i)`, each scaled by
`∏ i, b.repr (v i) (p i)`.  Collecting the terms by the unordered tuple `TauCeti.Sym.ofFn p`
underlying `p` gives the coordinate at `s` as a sum over the orderings of `s`.

Two consequences are what the file exists for.

* **At a constant index the sum has one term.**  Only the constant tuple orders the unordered
  tuple `(k, …, k)`, so the coordinate of `⨂ₛ v` there is the plain product `∏ i, b.repr (v i) k`
  of one coordinate of each factor.
* **A pure power has no vanishing coordinate.**  The product `∏ i, b.repr (v i) (p i)` depends
  only on `TauCeti.Sym.ofFn p` when all the factors `v i` are equal, so the sum over the orderings
  of `s` has all its terms equal and no cancellation is possible: over a domain of characteristic
  zero, `⨂ₛ (u, …, u)` has a nonzero coordinate at *every* `s` as soon as every coordinate of `u`
  is nonzero.  For a general pure tensor this fails, the terms attached to different orderings
  being unrelated.

## Main results

* `SymmetricPower.repr_basis_symmetricPower_tprod`: the coordinate of a pure symmetric tensor at
  `s` is the sum, over the orderings of `s`, of the products of the corresponding coordinates of
  the factors.
* `SymmetricPower.repr_basis_symmetricPower_tprod_ofFn_const`: its value at a constant unordered
  tuple is a single product.
* `SymmetricPower.repr_basis_symmetricPower_tprod_const_ne_zero`: a pure power of a vector with
  nonzero coordinates has nonzero coordinates.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Appendix B, for the monomial basis of a symmetric power.
-/

public section

open Finset Module

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The product of the coordinates listed by an ordered tuple depends only on the unordered tuple
underlying it: reordering the factors permutes the terms of the product. -/
private theorem prod_eq_of_ofFn_eq (c : κ → R) {p q : Fin n → κ}
    (h : TauCeti.Sym.ofFn p = TauCeti.Sym.ofFn q) : ∏ i, c (p i) = ∏ i, c (q i) := by
  obtain ⟨σ, rfl⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 h
  exact (Equiv.prod_comp σ fun i => c (p i)).symm

/-- Two ordered tuples underlying the same unordered tuple as a constant one are equal to it. -/
private theorem eq_const_of_ofFn_eq_ofFn_const {p : Fin n → κ} {k : κ}
    (h : TauCeti.Sym.ofFn p = TauCeti.Sym.ofFn fun _ => k) : p = fun _ => k := by
  obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 h
  exact funext fun i => by simpa using congrFun hσ (σ.symm i)

variable (b : Basis κ R M)

/-- **The coordinates of a pure symmetric tensor.**  Expanding each factor of `⨂ₛ v` in the basis
`b` and collecting the resulting pure tensors of basis vectors by the unordered tuple of indices
they use, the coordinate at `s` is the sum, over the ordered tuples `p` underlying `s`, of the
products of the corresponding coordinates of the factors.

For factors that are themselves basis vectors this recovers `Module.Basis.symmetricPower_apply`;
the content here is the general case. -/
theorem repr_basis_symmetricPower_tprod [Fintype κ] [DecidableEq κ] (v : Fin n → M) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) s =
      ∑ p ∈ {p : Fin n → κ | TauCeti.Sym.ofFn p = s}, ∏ i, b.repr (v i) (p i) := by
  have hv : (fun i => v i) = fun i => ∑ k, b.repr (v i) k • b k :=
    funext fun i => (b.sum_repr (v i)).symm
  rw [show (⨂ₛ[R] i, v i) = tprod R fun i => v i from rfl, hv,
    (tprod R).map_sum fun (i : Fin n) (k : κ) => b.repr (v i) k • b k, map_sum,
    Finsupp.finsetSum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hbasis : (tprod R fun i => b (p i)) = b.symmetricPower n (TauCeti.Sym.ofFn p) := by
    rw [Basis.symmetricPower_apply, tprodOfSym_ofFn]
  rw [(tprod R).map_smul_univ (fun i => b.repr (v i) (p i)) fun i => b (p i), hbasis, map_smul,
    Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]

/-- **The coordinates of a pure symmetric tensor at a constant unordered tuple.**  The only
ordering of `(k, …, k)` is the constant tuple, so the sum of
`SymmetricPower.repr_basis_symmetricPower_tprod` collapses to a single product: one coordinate of
each factor. -/
theorem repr_basis_symmetricPower_tprod_ofFn_const [Finite κ] (v : Fin n → M) (k : κ) :
    (b.symmetricPower n).repr (⨂ₛ[R] i, v i) (TauCeti.Sym.ofFn fun _ => k) =
      ∏ i, b.repr (v i) k := by
  classical
  have := Fintype.ofFinite κ
  rw [repr_basis_symmetricPower_tprod]
  exact Finset.sum_eq_single_of_mem (fun _ => k) (by simp) fun p hp hne =>
    absurd (eq_const_of_ofFn_eq_ofFn_const (Finset.mem_filter.1 hp).2) hne

end CommSemiring

section CommRing

variable [CommRing R] [IsDomain R] [CharZero R] [AddCommMonoid M] [Module R M]
variable (b : Basis κ R M)

/-- **A pure power has no vanishing coordinate.**  When all the factors are the same vector `u`,
every term of the sum of `SymmetricPower.repr_basis_symmetricPower_tprod` is the same product of
coordinates of `u`, so the coordinate at `s` is that product times the number of orderings of `s`,
which is positive.  Over a domain of characteristic zero neither factor vanishes.

Nothing like this holds for a general pure tensor: the terms attached to different orderings of
`s` can cancel. -/
theorem repr_basis_symmetricPower_tprod_const_ne_zero [Finite κ] {u : M}
    (hu : ∀ k, b.repr u k ≠ 0) (s : Sym κ n) :
    (b.symmetricPower n).repr (⨂ₛ[R] (_ : Fin n), u) s ≠ 0 := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨p₀, hp₀⟩ := TauCeti.Sym.ofFn_surjective s
  have hne : ({p : Fin n → κ | TauCeti.Sym.ofFn p = s} : Finset (Fin n → κ)).Nonempty :=
    ⟨p₀, by simp [hp₀]⟩
  rw [repr_basis_symmetricPower_tprod,
    Finset.sum_congr rfl fun p hp => prod_eq_of_ofFn_eq (fun k => b.repr u k) (p := p) (q := p₀)
      (by rw [(Finset.mem_filter.1 hp).2, hp₀]),
    Finset.sum_const, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_pos.2 hne).ne')
    (Finset.prod_ne_zero_iff.2 fun i _ => hu _)

end CommRing

end SymmetricPower
