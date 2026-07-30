/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Sym.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The symmetric power of a field, charted by elementary symmetric functions

A point of the `n`-th symmetric power `Sym R n` is an unordered `n`-tuple of scalars, and the monic
polynomial `∏_{a ∈ s} (X - a)` records exactly that information: its coefficients are the
elementary symmetric functions of the tuple, up to sign. Over an algebraically closed field the
correspondence is a bijection in both directions, and composing it with Mathlib's identification of
monic degree-`n` polynomials with their lower coefficients presents `Sym K n` as the affine space
`Fin n → K`.

This is the algebraic heart of the *symmetric product chart*: for a Riemann surface `Σ` the
symmetric product `Sym^g(Σ)` is given its complex manifold structure by exactly this map, read in a
holomorphic coordinate on `Σ` — a local identification `Sym^g(ℂ) ≅ ℂ^g` whose coordinates are the
elementary symmetric functions of the `g` points. Only the pointwise algebra is settled here; the
topology and the complex structure are separate later steps.

## Main declarations

* `TauCeti.Sym.toMonic`: the monic polynomial of degree `n` whose roots, with multiplicity, are the
  points of `s : Sym R n`. This is Mathlib's `Polynomial.ofMultiset` restricted to a fixed
  cardinality, repackaged so that the target subtype records the degree.
* `TauCeti.Sym.coeff_toMonic`: Vieta's formulas, that the `k`-th coefficient of `toMonic s` is
  `(-1) ^ (n - k)` times the `(n - k)`-th elementary symmetric function of `s`.
* `TauCeti.Sym.toMonic_append`, `TauCeti.Sym.toMonic_cons`, `TauCeti.Sym.toMonic_replicate`: the
  map is multiplicative in the tuple, so adjoining a point multiplies by a linear factor and a
  constant tuple gives a pure power.
* `TauCeti.Sym.roots_toMonic`, `TauCeti.Sym.toMonic_injective`, `TauCeti.Sym.mem_iff_isRoot`: over
  an integral domain the tuple is recovered from the polynomial as its root multiset.
* `TauCeti.Sym.monicEquiv`: over an algebraically closed field, taking roots with multiplicity
  inverts `toMonic`, so `Sym K n` is equivalent to the monic polynomials of degree `n`.
* `TauCeti.Sym.coeffEquiv`: the resulting chart `Sym K n ≃ (Fin n → K)`, with
  `TauCeti.Sym.coeffEquiv_apply` naming its coordinates as the signed elementary symmetric
  functions and `TauCeti.Sym.coeffEquiv_symm_apply` describing the inverse as a root-taking map.
* `TauCeti.Sym.coeffEquiv_one_apply` and `TauCeti.Sym.coeffEquiv_two_apply`: the chart in degrees
  one and two, pinning down the sign convention.

The correspondence between an unordered tuple and its monic polynomial, and the complex structure
it puts on `Sym^g(Σ)`, is the opening item of Lane F4.1 of the analytic Heegaard Floer roadmap
(Ozsváth--Szabó, [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). Vieta's formulas,
the root multiset of a split monic polynomial, the multiset-to-polynomial map itself, and the
equivalence between monic polynomials of degree `n` and polynomials of degree `< n` are all
Mathlib's (`Multiset.prod_X_sub_C_coeff`,
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, `Polynomial.ofMultiset`,
`Polynomial.monicEquivDegreeLT`); nothing is vendored here.

Because the ambient type `Sym` is Mathlib's, the declarations below live in `TauCeti.Sym` and are
applied by name rather than by dot notation.
-/

public section

namespace TauCeti

open Multiset Polynomial

namespace Sym

section Basic

variable {R : Type*} [CommRing R] {m n : ℕ}

/-! ### The monic polynomial of an unordered tuple -/

section Defs

variable [Nontrivial R]

/-- The monic polynomial `∏_{a ∈ s} (X - a)` of an unordered `n`-tuple `s`, bundled with its
monicity and the fact that its degree is `n`.

The underlying polynomial is Mathlib's `Polynomial.ofMultiset`; the point of the subtype is that
the degree is pinned to `n` rather than to the cardinality of the underlying multiset, which is
what `Polynomial.monicEquivDegreeLT` consumes. -/
@[expose]
noncomputable def toMonic (s : Sym R n) : { p : R[X] // p.Monic ∧ p.natDegree = n } :=
  ⟨ofMultiset (s : Multiset R), by simpa using monic_multisetProd_X_sub_C (s : Multiset R),
    by simp [Sym.card_coe]⟩

theorem coe_toMonic (s : Sym R n) : (toMonic s : R[X]) = ofMultiset (s : Multiset R) :=
  rfl

@[simp]
theorem monic_toMonic (s : Sym R n) : (toMonic s : R[X]).Monic :=
  (toMonic s).2.1

@[simp]
theorem natDegree_toMonic (s : Sym R n) : (toMonic s : R[X]).natDegree = n :=
  (toMonic s).2.2

@[simp]
theorem toMonic_nil : (toMonic (Sym.nil : Sym R 0) : R[X]) = 1 := by
  rw [coe_toMonic]
  simp

/-- Adjoining a point to a tuple multiplies its monic polynomial by the corresponding linear
factor. -/
@[simp]
theorem toMonic_cons (a : R) (s : Sym R n) :
    (toMonic (a ::ₛ s) : R[X]) = (X - C a) * (toMonic s : R[X]) := by
  simp only [coe_toMonic, Sym.coe_cons]
  simp

/-- The monic polynomial of a union of two tuples is the product of their monic polynomials: this
is the multiplicativity that makes `Polynomial.ofMultiset` an additive character. -/
theorem toMonic_append (s : Sym R n) (t : Sym R m) :
    (toMonic (s.append t) : R[X]) = (toMonic s : R[X]) * (toMonic t : R[X]) := by
  simp only [coe_toMonic, Sym.coe_append]
  exact ofMultiset.map_add_eq_mul _ _

/-- The monic polynomial of a constant tuple is a pure power of a linear factor. -/
theorem toMonic_replicate (a : R) :
    (toMonic (Sym.replicate n a) : R[X]) = (X - C a) ^ n := by
  rw [coe_toMonic, Sym.coe_replicate]
  simp

/-- Evaluating the monic polynomial of a tuple at `x` multiplies together the differences between
`x` and the points of the tuple. -/
theorem eval_toMonic (s : Sym R n) (x : R) :
    (toMonic s : R[X]).eval x = ((s : Multiset R).map fun a => x - a).prod := by
  rw [coe_toMonic]
  simp [eval_multiset_prod, Multiset.map_map]

/-- **Vieta's formulas** on the symmetric power: the `k`-th coefficient of the monic polynomial of
an unordered `n`-tuple is the `(n - k)`-th elementary symmetric function of the tuple, up to the
sign `(-1) ^ (n - k)`. -/
theorem coeff_toMonic (s : Sym R n) {k : ℕ} (hk : k ≤ n) :
    (toMonic s : R[X]).coeff k = (-1) ^ (n - k) * (s : Multiset R).esymm (n - k) := by
  have hcard : Multiset.card (s : Multiset R) = n := Sym.card_coe
  have hk' : k ≤ Multiset.card (s : Multiset R) := by rw [hcard]; exact hk
  rw [coe_toMonic]
  simpa [hcard] using (s : Multiset R).prod_X_sub_C_coeff hk'

/-- The constant term of the monic polynomial of a tuple is the signed product of its points. -/
theorem coeff_zero_toMonic (s : Sym R n) :
    (toMonic s : R[X]).coeff 0 = (-1) ^ n * (s : Multiset R).prod := by
  rw [coeff_zero_eq_eval_zero, eval_toMonic]
  simp [Sym.card_coe]

end Defs

section Domain

variable [IsDomain R]

/-- Over an integral domain the points of a tuple are recovered, with multiplicity, as the roots of
its monic polynomial. -/
@[simp]
theorem roots_toMonic (s : Sym R n) : (toMonic s : R[X]).roots = (s : Multiset R) := by
  rw [coe_toMonic]
  exact roots_ofMultiset _

theorem toMonic_injective : Function.Injective (toMonic (R := R) (n := n)) := fun s t h => by
  refine Sym.coe_injective ?_
  rw [← roots_toMonic s, ← roots_toMonic t, h]

/-- A scalar lies in a tuple exactly when it is a root of the tuple's monic polynomial. -/
theorem mem_iff_isRoot {a : R} {s : Sym R n} :
    a ∈ (s : Multiset R) ↔ (toMonic s : R[X]).IsRoot a := by
  rw [← roots_toMonic s, mem_roots (monic_toMonic s).ne_zero]

end Domain

end Basic

/-! ### The chart over an algebraically closed field -/

section AlgClosed

variable (K : Type*) [Field K] [IsAlgClosed K] (n : ℕ)

/-- Over an algebraically closed field, `TauCeti.Sym.toMonic` is a bijection from the `n`-th
symmetric power onto the monic polynomials of degree `n`, inverted by taking roots with
multiplicity. -/
@[expose]
noncomputable def monicEquiv : Sym K n ≃ { p : K[X] // p.Monic ∧ p.natDegree = n } where
  toFun := toMonic
  invFun p := ⟨p.1.roots, by rw [splits_iff_card_roots.mp (IsAlgClosed.splits p.1), p.2.2]⟩
  left_inv s := Sym.coe_injective (roots_toMonic s)
  right_inv p := Subtype.ext <| by
    rw [coe_toMonic]
    simpa using prod_multiset_X_sub_C_of_monic_of_roots_card_eq p.2.1
      (splits_iff_card_roots.mp (IsAlgClosed.splits p.1))

@[simp]
theorem monicEquiv_apply (s : Sym K n) : monicEquiv K n s = toMonic s :=
  rfl

@[simp]
theorem coe_monicEquiv_symm_apply (p : { p : K[X] // p.Monic ∧ p.natDegree = n }) :
    (((monicEquiv K n).symm p : Sym K n) : Multiset K) = p.1.roots :=
  rfl

/-- The **elementary symmetric chart** on the `n`-th symmetric power of an algebraically closed
field: an unordered `n`-tuple is determined by, and freely determines, the `n` lower coefficients of
its monic polynomial.

By `TauCeti.Sym.coeffEquiv_apply` the `i`-th coordinate is `(-1) ^ (n - i)` times the `(n - i)`-th
elementary symmetric function of the tuple. -/
@[expose]
noncomputable def coeffEquiv : Sym K n ≃ (Fin n → K) :=
  (monicEquiv K n).trans ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)

variable {K n}

/-- The chart reads off the lower coefficients of the monic polynomial of the tuple. -/
theorem coeffEquiv_apply_eq_coeff (s : Sym K n) (i : Fin n) :
    coeffEquiv K n s i = (toMonic s : K[X]).coeff i := by
  have hne : (i : ℕ) ≠ (toMonic s : K[X]).natDegree := by
    rw [natDegree_toMonic]
    exact i.2.ne
  change (toMonic s : K[X]).eraseLead.coeff (i : ℕ) = _
  exact eraseLead_coeff_of_ne _ hne

/-- The coordinates of the elementary symmetric chart are the elementary symmetric functions of the
tuple, in decreasing order and with alternating signs. -/
theorem coeffEquiv_apply (s : Sym K n) (i : Fin n) :
    coeffEquiv K n s i = (-1) ^ (n - (i : ℕ)) * (s : Multiset K).esymm (n - (i : ℕ)) := by
  rw [coeffEquiv_apply_eq_coeff, coeff_toMonic s i.2.le]

/-- The inverse chart sends a coefficient tuple to the root multiset of the monic polynomial it
determines. -/
theorem coeffEquiv_symm_apply (f : Fin n → K) :
    (((coeffEquiv K n).symm f : Sym K n) : Multiset K) =
      (X ^ n + ∑ i : Fin n, monomial (i : ℕ) (f i)).roots :=
  rfl

/-- In degree one the chart is negation: the single coordinate of a one-point tuple is minus that
point. -/
theorem coeffEquiv_one_apply {s : Sym K 1} {a : K} (hs : (s : Multiset K) = {a}) :
    coeffEquiv K 1 s 0 = -a := by
  rw [coeffEquiv_apply_eq_coeff, coe_toMonic, hs]
  simp

/-- In degree two the chart is `{a, b} ↦ (ab, -(a + b))`: the two lower coefficients of
`(X - a) (X - b) = X ^ 2 - (a + b) X + ab`. -/
theorem coeffEquiv_two_apply {s : Sym K 2} {a b : K} (hs : (s : Multiset K) = {a, b}) :
    coeffEquiv K 2 s = ![a * b, -(a + b)] := by
  have hp : (toMonic s : K[X]) = X ^ 2 - C (a + b) * X + C (a * b) := by
    rw [coe_toMonic, hs, C_add, C_mul]
    simp only [ofMultiset_apply, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_singleton, Multiset.prod_singleton]
    ring
  ext i
  fin_cases i <;> rw [coeffEquiv_apply_eq_coeff, hp] <;> simp

end AlgClosed

end Sym

end TauCeti
