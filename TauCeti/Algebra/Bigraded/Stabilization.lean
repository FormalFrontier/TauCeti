/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import TauCeti.Algebra.Bigraded.Basic

/-!
# Bigraded vector spaces up to `⊗ W`-stabilization

Grid homology comes in a family of flavors whose blocked versions depend on the size of the
grid rather than on the link alone: the fully blocked homology of an `n × n` grid diagram
presenting a link `L` is the simply blocked grid homology of `L` tensored with
`W^{⊗(n-1)}`, where `W` is the two-dimensional bigraded vector
space with one generator in bidegree `(0, 0)` and one in bidegree `(-1, -1)`. The link invariant
is therefore not the bigraded vector space itself but its class modulo tensoring with copies of
`W`. This file builds that quotient, together with the canonical representatives that make it
usable.

A finite-dimensional bigraded vector space over a field is determined up to bigraded isomorphism
by its dimension function, so the whole discussion takes place at the level of Poincaré series:
`TauCeti.Bigraded.Series` is `ℕ[ℤ × ℤ]`, a finitely supported function assigning a dimension to
each bidegree `(Maslov, Alexander)`, with convolution as its product. Tensoring with `W` is
multiplication by `TauCeti.Bigraded.W`, and unwinding the convolution gives the expected
`(P * W)(m, a) = P(m, a) + P(m + 1, a + 1)`.

The quotient is not vacuous, and that is the substance here. Multiplication by `W` is injective
(`TauCeti.Bigraded.mul_W_left_injective`), so no information beyond the number of stabilizations
is lost; note this genuinely uses finite support, since on unbounded bigraded vector spaces
tensoring with `W` is *not* injective. Consequently each stable class contains exactly one
`W`-indivisible series (`TauCeti.Bigraded.exists_isReduced`,
`TauCeti.Bigraded.IsReduced.eq_of_mul_W_pow_eq`), the reduced representative, and two series are
stably equivalent exactly when their reduced representatives agree
(`TauCeti.Bigraded.isStablyEquiv_iff_reducedRep_eq`). Reduction is therefore a complete invariant
of a stable class.

Finally, the Alexander-graded Euler characteristic `TauCeti.Bigraded.euler` records how much the
stabilization actually costs: it is a ring homomorphism to the Laurent polynomials sending `W` to
`1 - T⁻¹`, so stabilizing `k` times multiplies the Euler characteristic by `(1 - T⁻¹)^k`. That is
exactly the factor by which the grid state sum of an `n × n` diagram differs from the Alexander
polynomial of the link it presents, so the Euler characteristic is an invariant of a stable class
only after that factor is divided out.

## Main definitions

* `TauCeti.Bigraded.Series`: the Poincaré series of a finite-dimensional bigraded vector space.
* `TauCeti.Bigraded.W`: the Poincaré series of the stabilization factor `W`.
* `TauCeti.Bigraded.totalDim`: the total dimension, as a ring homomorphism.
* `TauCeti.Bigraded.IsStablyEquiv`, `TauCeti.Bigraded.StableSeries`: the stabilization
  equivalence and the quotient it defines.
* `TauCeti.Bigraded.IsReduced`, `TauCeti.Bigraded.reducedRep`: `W`-indivisibility and the
  canonical representative of a stable class.
* `TauCeti.Bigraded.euler`: the Alexander-graded Euler characteristic.

## Main results

* `TauCeti.Bigraded.coeff_mul_W` and `TauCeti.Bigraded.coeff_mul_W_pow`: tensoring with `W`
  adds the diagonal shift by `(1, 1)`, and iterating it adds binomial multiples of the shifts.
* `TauCeti.Bigraded.mul_W_left_injective`: tensoring with `W` is injective.
* `TauCeti.Bigraded.exists_isReduced` and `TauCeti.Bigraded.IsReduced.eq_of_mul_W_pow_eq`: every
  series is a stabilization of a unique reduced one.
* `TauCeti.Bigraded.isStablyEquiv_iff_reducedRep_eq`: the reduced representative is a complete
  invariant of a stable class.
* `TauCeti.Bigraded.reduce_injective` and `TauCeti.Bigraded.stableEquivReduced`: the reduced
  representative identifies the quotient with the `W`-indivisible series.
* `TauCeti.Bigraded.euler_mul_W_pow`: stabilizing multiplies the Euler characteristic by
  `1 - T⁻¹`.

## References

This supplies the stabilization convention of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane ALG, which asks for the "graded
vector space up to `⊗W`-stabilization" quotient "as API, not ad hoc", and which Lane G.5 needs to
state which of the blocked grid homologies is a link invariant. The bigraded conventions follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 4 and 5, where
`W` is the bigraded vector space with generators in bidegrees `(0, 0)` and `(-1, -1)`.
-/

public section

namespace TauCeti

namespace Bigraded

open AddMonoidAlgebra

/-
The implementation definitions below are deliberately sealed. Their characteristic lemmas are
the public interface; the parenthesized `(rfl)` proofs keep those lemmas propositional without
exposing the quotient and choice implementations downstream.
-/

/-- The Poincaré series of the stabilization factor `W`: one generator in bidegree `(0, 0)` and
one in bidegree `(-1, -1)`. -/
noncomputable def W : Series := 1 + single (-1, -1) 1

/-- The coefficient of `W` in bidegree `(0, 0)`. -/
@[simp]
theorem coeff_W_zero : W.coeff 0 = 1 := by
  simp [W, one_def]

/-- `W` is not the zero series: it has a generator in bidegree `(0, 0)`. -/
theorem W_ne_zero : W ≠ 0 := by
  intro h
  have h0 : W.coeff 0 = 0 := by rw [h]; simp
  rw [coeff_W_zero] at h0
  exact one_ne_zero h0

/-- Tensoring with `W` is a shifted sum: the bidegree `(m, a)` part of `P ⊗ W` is the bidegree
`(m, a)` part of `P` plus its bidegree `(m + 1, a + 1)` part. -/
theorem coeff_mul_W (P : Series) (g : ℤ × ℤ) :
    (P * W).coeff g = P.coeff g + P.coeff (g + (1, 1)) := by
  have h : (P * single ((-1 : ℤ), (-1 : ℤ)) 1).coeff g = P.coeff (g + (1, 1)) := by
    simp
  rw [W, mul_add, mul_one, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h]

/-- Tensoring with `W` is injective. This is where finite support is essential: on bigraded
vector spaces with unbounded support the same operation is not injective, since for instance a
one-dimensional summand in every bidegree `(m, m)` and a two-dimensional summand in every second
such bidegree have the same stabilization. -/
theorem mul_W_left_injective : Function.Injective fun P : Series => P * W :=
  fun _ _ h => mul_right_cancel₀ W_ne_zero h

/-- Tensoring with `W` repeatedly is injective. -/
theorem mul_W_pow_left_injective (k : ℕ) : Function.Injective fun P : Series => P * W ^ k :=
  fun _ _ h => mul_right_cancel₀ (pow_ne_zero k W_ne_zero) h

/-- The bigraded dimensions of a `k`-fold stabilization. The summand of `P ⊗ W^{⊗k}` in bidegree
`(m, a)` collects the summands of `P` in the bidegrees `(m + i, a + i)` on the diagonal above it,
each with the binomial multiplicity `k.choose i`. -/
theorem coeff_mul_W_pow (P : Series) (k : ℕ) (g : ℤ × ℤ) :
    (P * W ^ k).coeff g =
      ∑ i ∈ Finset.range (k + 1), k.choose i * P.coeff (g + ((i : ℤ), (i : ℤ))) := by
  induction k generalizing g with
  | zero =>
    have hzero : ((0 : ℤ), (0 : ℤ)) = 0 := Prod.ext (by simp) (by simp)
    simp [hzero]
  | succ k ih =>
    have hshift : ∀ i : ℕ,
        g + (1, 1) + ((i : ℤ), (i : ℤ)) = g + (((i + 1 : ℕ) : ℤ), ((i + 1 : ℕ) : ℤ)) := by
      intro i
      ext <;> · simp only [Prod.fst_add, Prod.snd_add]; push_cast; ring
    rw [pow_succ, ← mul_assoc, coeff_mul_W, ih g, ih (g + (1, 1))]
    rw [Finset.sum_range_succ'
      (fun i => (k + 1).choose i * P.coeff (g + ((i : ℤ), (i : ℤ)))) (k + 1)]
    rw [Finset.sum_range_succ' (fun i => k.choose i * P.coeff (g + ((i : ℤ), (i : ℤ)))) k]
    simp only [hshift, Nat.choose_succ_succ, Nat.choose_zero_right, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun i => k.choose (i + 1) *
      P.coeff (g + (((i + 1 : ℕ) : ℤ), ((i + 1 : ℕ) : ℤ))))]
    simp only [Nat.choose_succ_self, Nat.zero_mul, add_zero, Nat.cast_zero]
    push_cast
    ring

/-- The stabilization factor `W` is two-dimensional. -/
@[simp]
theorem totalDim_W : totalDim W = 2 := by
  rw [W, map_add, map_one, totalDim_single]

/-- Stabilizing `k` times multiplies the total dimension by `2 ^ k`: this is the grid-size
dependence of the blocked grid homologies, and it is why the unstabilized theories are not link
invariants. -/
theorem totalDim_mul_W_pow (P : Series) (k : ℕ) : totalDim (P * W ^ k) = 2 ^ k * totalDim P := by
  rw [map_mul, map_pow, totalDim_W, mul_comm]

section StablyEquiv

/-- Two bigraded vector spaces are stably equivalent when they become isomorphic after tensoring
each with some number of copies of `W`. -/
def IsStablyEquiv (P Q : Series) : Prop := ∃ i j : ℕ, P * W ^ i = Q * W ^ j

/-- Stable equivalence is witnessed by stabilizing each series some number of times. -/
theorem isStablyEquiv_iff {P Q : Series} :
    IsStablyEquiv P Q ↔ ∃ i j : ℕ, P * W ^ i = Q * W ^ j := by
  rfl

/-- Stable equivalence is reflexive. -/
@[refl]
theorem isStablyEquiv_refl (P : Series) : IsStablyEquiv P P := ⟨0, 0, rfl⟩

/-- Stable equivalence is symmetric. -/
theorem IsStablyEquiv.symm {P Q : Series} (h : IsStablyEquiv P Q) : IsStablyEquiv Q P :=
  let ⟨i, j, hij⟩ := h; ⟨j, i, hij.symm⟩

/-- Stable equivalence is transitive: tensor the two witnesses together. -/
theorem IsStablyEquiv.trans {P Q R : Series} (h : IsStablyEquiv P Q) (h' : IsStablyEquiv Q R) :
    IsStablyEquiv P R := by
  obtain ⟨i, j, hij⟩ := h
  obtain ⟨i', j', hij'⟩ := h'
  refine ⟨i + i', j + j', ?_⟩
  calc P * W ^ (i + i') = (P * W ^ i) * W ^ i' := by rw [pow_add, mul_assoc]
    _ = (Q * W ^ i') * W ^ j := by rw [hij]; ring
    _ = (R * W ^ j') * W ^ j := by rw [hij']
    _ = R * W ^ (j + j') := by rw [pow_add]; ring

/-- Tensoring with `W` does not change the stable class. -/
theorem isStablyEquiv_mul_W_pow (P : Series) (k : ℕ) : IsStablyEquiv (P * W ^ k) P :=
  ⟨0, k, by rw [pow_zero, mul_one]⟩

/-- Stable equivalence as a setoid, so that the stable classes form a quotient type. -/
def stableSetoid : Setoid Series where
  r := IsStablyEquiv
  iseqv := ⟨isStablyEquiv_refl, IsStablyEquiv.symm, IsStablyEquiv.trans⟩

/-- A bigraded vector space up to `⊗ W`-stabilization. This is the shape of the invariant
attached to a link by a blocked grid homology: the grid size is visible in a representative but
not in the class. -/
def StableSeries : Type := Quotient stableSetoid

/-- The stable class of a bigraded vector space. -/
def stableMk (P : Series) : StableSeries := Quotient.mk stableSetoid P

/-- Prove a property of a stable series by proving it on every representative. -/
protected theorem StableSeries.inductionOn {motive : StableSeries → Prop} (S : StableSeries)
    (mk : ∀ P, motive (stableMk P)) : motive S :=
  Quotient.inductionOn S mk

/-- Define a function on stable series from a function on representatives that respects stable
equivalence. -/
protected def StableSeries.lift {X : Sort*} (f : Series → X)
    (h : ∀ {P Q}, IsStablyEquiv P Q → f P = f Q) : StableSeries → X :=
  Quotient.lift f fun _ _ hPQ => h hPQ

/-- Lifting a function to the stable class of a representative returns its value there. -/
@[simp]
theorem StableSeries.lift_stableMk {X : Sort*} (f : Series → X)
    (h : ∀ {P Q}, IsStablyEquiv P Q → f P = f Q) (P : Series) :
    StableSeries.lift f h (stableMk P) = f P := (rfl)

/-- Two series have the same stable class exactly when they are stably equivalent. -/
theorem stableMk_eq_stableMk_iff {P Q : Series} :
    stableMk P = stableMk Q ↔ IsStablyEquiv P Q :=
  Quotient.eq (r := stableSetoid)

/-- Tensoring with copies of `W` does not change the stable class. -/
@[simp]
theorem stableMk_mul_W_pow (P : Series) (k : ℕ) : stableMk (P * W ^ k) = stableMk P :=
  stableMk_eq_stableMk_iff.mpr (isStablyEquiv_mul_W_pow P k)

end StablyEquiv

section Reduced

/-- A bigraded vector space is reduced when it is not a nontrivial stabilization: the only way to
write it as `Q ⊗ W` is with `Q = 0`. The zero series is reduced. -/
def IsReduced (P : Series) : Prop := ∀ Q : Series, P = Q * W → Q = 0

/-- A series is reduced exactly when every expression of it as a stabilization has zero
unstabilized factor. -/
theorem isReduced_iff {P : Series} : IsReduced P ↔ ∀ Q : Series, P = Q * W → Q = 0 := by
  rfl

/-- The zero series is reduced. -/
theorem isReduced_zero : IsReduced (0 : Series) :=
  fun _ hQ => (mul_eq_zero.mp hQ.symm).resolve_right W_ne_zero

/-- A series of odd total dimension is reduced, since a stabilization has even total dimension.
In particular the one-dimensional series in a single bidegree, the Poincaré series of the
simply blocked grid homology of the unknot, is reduced. -/
theorem isReduced_of_odd_totalDim {P : Series} (h : Odd (totalDim P)) : IsReduced P := by
  intro Q hQ
  exfalso
  rw [hQ, map_mul, totalDim_W] at h
  exact Nat.not_odd_iff_even.mpr ⟨totalDim Q, by ring⟩ h

/-- Every bigraded vector space is a stabilization of a reduced one. -/
theorem exists_isReduced (P : Series) : ∃ Q : Series, IsReduced Q ∧ ∃ k : ℕ, P = Q * W ^ k := by
  classical
  rcases eq_or_ne P 0 with rfl | hP
  · exact ⟨0, isReduced_zero, 0, by simp⟩
  have hbound : ∀ k : ℕ, (∃ Q : Series, P = Q * W ^ k) → k ≤ totalDim P := by
    rintro k ⟨Q, rfl⟩
    have hQ : Q ≠ 0 := by rintro rfl; simp at hP
    have h1 : 1 ≤ totalDim Q := Nat.one_le_iff_ne_zero.mpr (by simpa using hQ)
    have hlt : k < totalDim (Q * W ^ k) :=
      calc k < 2 ^ k := Nat.lt_two_pow_self
        _ = 2 ^ k * 1 := (mul_one _).symm
        _ ≤ 2 ^ k * totalDim Q := Nat.mul_le_mul_left _ h1
        _ = totalDim (Q * W ^ k) := (totalDim_mul_W_pow Q k).symm
    exact hlt.le
  have hzero : ∃ R : Series, P = R * W ^ 0 := ⟨P, by simp⟩
  obtain ⟨Q, hQ⟩ := Nat.findGreatest_spec (P := fun k => ∃ R : Series, P = R * W ^ k)
    (n := totalDim P) (m := 0) (Nat.zero_le _) hzero
  set m := Nat.findGreatest (fun k => ∃ R : Series, P = R * W ^ k) (totalDim P) with hm
  refine ⟨Q, ?_, m, hQ⟩
  intro R hR
  by_contra hR0
  have hsucc : ∃ S : Series, P = S * W ^ (m + 1) := by
    refine ⟨R, ?_⟩
    rw [hR] at hQ
    rw [hQ]
    ring
  have hle := Nat.le_findGreatest (P := fun k => ∃ R : Series, P = R * W ^ k)
    (hbound _ hsucc) hsucc
  rw [← hm] at hle
  omega

/-- Reduced representatives are unique: two reduced series with a common stabilization are
equal. -/
theorem IsReduced.eq_of_mul_W_pow_eq {P Q : Series} (hP : IsReduced P) (hQ : IsReduced Q)
    {i j : ℕ} (h : P * W ^ i = Q * W ^ j) : P = Q := by
  wlog hij : i ≤ j generalizing P Q i j
  · exact (this hQ hP h.symm (Nat.le_of_not_le hij)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hcancel : P = Q * W ^ d := by
    refine mul_W_pow_left_injective i ?_
    simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using hcancel
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    have hQ0 : Q * W ^ e = 0 := hP _ (by rw [hcancel, pow_add, pow_one]; ring)
    have hQz : Q = 0 := (mul_eq_zero.mp hQ0).resolve_right (pow_ne_zero e W_ne_zero)
    subst hQz
    simpa using hcancel

/-- The reduced representative of a bigraded vector space: the unique reduced series of which it
is a stabilization. -/
noncomputable def reducedRep (P : Series) : Series := (exists_isReduced P).choose

/-- The reduced representative is reduced. -/
theorem isReduced_reducedRep (P : Series) : IsReduced (reducedRep P) :=
  (exists_isReduced P).choose_spec.1

/-- A series is a stabilization of its reduced representative. -/
theorem exists_mul_W_pow_reducedRep (P : Series) : ∃ k : ℕ, P = reducedRep P * W ^ k :=
  (exists_isReduced P).choose_spec.2

/-- A series is stably equivalent to its reduced representative. -/
theorem isStablyEquiv_reducedRep (P : Series) : IsStablyEquiv P (reducedRep P) := by
  obtain ⟨k, hk⟩ := exists_mul_W_pow_reducedRep P
  exact ⟨0, k, by simpa using hk⟩

/-- A reduced series is its own reduced representative. -/
theorem reducedRep_eq_self {P : Series} (hP : IsReduced P) : reducedRep P = P := by
  obtain ⟨k, hk⟩ := exists_mul_W_pow_reducedRep P
  exact (isReduced_reducedRep P).eq_of_mul_W_pow_eq hP (i := k) (j := 0) (by simpa using hk.symm)

/-- Stably equivalent series have the same reduced representative, and conversely: reduction is a
complete invariant of a stable class. -/
theorem isStablyEquiv_iff_reducedRep_eq {P Q : Series} :
    IsStablyEquiv P Q ↔ reducedRep P = reducedRep Q := by
  constructor
  · rintro ⟨i, j, hij⟩
    obtain ⟨k, hk⟩ := exists_mul_W_pow_reducedRep P
    obtain ⟨l, hl⟩ := exists_mul_W_pow_reducedRep Q
    refine (isReduced_reducedRep P).eq_of_mul_W_pow_eq (isReduced_reducedRep Q)
      (i := k + i) (j := l + j) ?_
    calc reducedRep P * W ^ (k + i) = (reducedRep P * W ^ k) * W ^ i := by rw [pow_add, mul_assoc]
      _ = P * W ^ i := by rw [← hk]
      _ = Q * W ^ j := hij
      _ = (reducedRep Q * W ^ l) * W ^ j := by rw [← hl]
      _ = reducedRep Q * W ^ (l + j) := by rw [pow_add, mul_assoc]
  · intro h
    exact (isStablyEquiv_reducedRep P).trans (h ▸ (isStablyEquiv_reducedRep Q).symm)

/-- Reduction descends to the quotient: the canonical representative of a stable class. -/
noncomputable def reduce : StableSeries → Series :=
  StableSeries.lift reducedRep fun h => isStablyEquiv_iff_reducedRep_eq.mp h

/-- The canonical representative of the class of `P` is the reduced representative of `P`. -/
@[simp]
theorem reduce_stableMk (P : Series) : reduce (stableMk P) = reducedRep P := (rfl)

/-- The canonical representative of a stable class lies in that class. -/
@[simp]
theorem stableMk_reduce (S : StableSeries) : stableMk (reduce S) = S := by
  induction S using StableSeries.inductionOn with
  | _ P => exact (stableMk_eq_stableMk_iff.mpr (isStablyEquiv_reducedRep P)).symm

/-- A stable class is determined by its canonical representative. -/
theorem reduce_injective : Function.Injective reduce := by
  intro S T h
  rw [← stableMk_reduce S, ← stableMk_reduce T, h]

/-- The unit series, the Poincaré series of a one-dimensional bigraded vector space in bidegree
`(0, 0)`, is reduced. -/
theorem isReduced_one : IsReduced (1 : Series) :=
  isReduced_of_odd_totalDim (by simp)

/-- Stabilizing the trivial one-dimensional bigraded vector space `k` times doubles its dimension
each time. This is the grid-size dependence of the fully blocked grid homology of an `n × n`
unknot grid, whose Poincaré series is `W ^ (n - 1)`. -/
@[simp]
theorem totalDim_W_pow (k : ℕ) : totalDim (W ^ k) = 2 ^ k := by
  rw [map_pow, totalDim_W]

/-- All the stabilizations of the trivial bigraded vector space have the same reduced
representative, although their dimensions `2 ^ k` are all different. -/
@[simp]
theorem reducedRep_W_pow (k : ℕ) : reducedRep (W ^ k) = 1 := by
  obtain ⟨l, hl⟩ := exists_mul_W_pow_reducedRep (W ^ k)
  exact (isReduced_reducedRep (W ^ k)).eq_of_mul_W_pow_eq isReduced_one (i := l) (j := k)
    (by rw [← hl, one_mul])

/-- The stable classes of finite-dimensional bigraded vector spaces are exactly the
`W`-indivisible ones: reduction and inclusion are mutually inverse. -/
noncomputable def stableEquivReduced : StableSeries ≃ {P : Series // IsReduced P} where
  toFun S := ⟨reduce S, by
    induction S using StableSeries.inductionOn with
    | _ P => exact isReduced_reducedRep P⟩
  invFun P := stableMk P.1
  left_inv S := by simp
  right_inv P := Subtype.ext (by simpa using reducedRep_eq_self P.2)

end Reduced

open LaurentPolynomial

/-- The Euler characteristic of the stabilization factor is `1 - T⁻¹`. -/
@[simp]
theorem euler_W : euler W = 1 - T (-1) := by
  have hneg : (((-1 : ℤ).negOnePow : ℤ)) = -1 := by
    rw [Int.negOnePow_odd _ ⟨-1, by ring⟩]
    rfl
  rw [W, map_add, map_one, euler_single, hneg, Nat.cast_one, one_mul, single_neg]
  rw [T, sub_eq_add_neg]

/-- Stabilizing multiplies the Alexander-graded Euler characteristic by `1 - T⁻¹`. The blocked
grid homology of an `n × n` grid therefore has Euler characteristic `(1 - T⁻¹)^(n-1)` times that
of the link invariant it stabilizes, which is the discrepancy between the grid state sum and the
Alexander polynomial. -/
theorem euler_mul_W_pow (P : Series) (k : ℕ) :
    euler (P * W ^ k) = euler P * (1 - T (-1)) ^ k := by
  rw [map_mul, map_pow, euler_W]

end Bigraded

end TauCeti
