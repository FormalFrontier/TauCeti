/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeWhile
public import TauCeti.Algebra.Polynomial.CoeffList

/-!
# The cyclotomic polynomials, computably

Mathlib defines `Polynomial.cyclotomic n R` through the primitive `n`-th roots of unity in `ℂ`,
so nothing about it evaluates: `Polynomial` is a `Finsupp` and `cyclotomic` is `noncomputable`.
This file computes the coefficients of `Φ_n` over `ℤ` instead, and proves that the computation is
right.

The algorithm is the defining recursion `∏_{d ∣ n} Φ_d = X ^ n - 1` read as a division: starting
from the coefficients of `X ^ n - 1`, divide successively by `Φ_d` for each proper divisor `d` of
`n`, each of which is monic and already computed, and what is left is `Φ_n`.  The divisions are
the synthetic division of `TauCeti.Polynomial.divByMonicList`; the recursion is made structural by
passing a fuel argument, so that `TauCeti.cyclotomicCoeffs` reduces in the kernel, as the closing
examples check.

`TauCeti.cyclotomicCoeffs_eq_coeffList` identifies the computed list with Mathlib's
`Polynomial.coeffList` of `Polynomial.cyclotomic n ℤ`, so it is not merely *a* list of
coefficients for `Φ_n` but *the* one: leading coefficient first, with no leading zeros.

This is the arithmetic that the executable Burnside--Dixon--Schneider character-table algorithm
computes in: the exact cyclotomic integers `ℤ[ζ_e] = ℤ[X]/Φ_e` are coefficient vectors on the
power basis, and reducing a product modulo `Φ_e` needs the coefficients of `Φ_e` themselves.
-/

public section

open Polynomial TauCeti.Polynomial

namespace TauCeti

/-- The coefficients of `X ^ n - 1`, highest degree first, for `n ≠ 0`. -/
@[expose] def xPowSubOneCoeffs (n : ℕ) : List ℤ :=
  (1 :: List.replicate (n - 1) 0) ++ [-1]

/-- `TauCeti.xPowSubOneCoeffs` lists the coefficients of `X ^ n - 1`. -/
theorem ofCoeffList_xPowSubOneCoeffs {n : ℕ} (hn : n ≠ 0) :
    ofCoeffList (xPowSubOneCoeffs n) = X ^ n - 1 := by
  rw [xPowSubOneCoeffs, ofCoeffList_concat, ofCoeffList_cons]
  simp only [List.length_replicate, ofCoeffList_replicate_zero, add_zero, map_one, one_mul]
  rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
  simp [sub_eq_add_neg]

/-- The coefficients of the `n`-th cyclotomic polynomial over `ℤ`, computed by dividing `X ^ n - 1`
successively by the cyclotomic polynomials of the proper divisors of `n`.  The first argument is
fuel, which makes the recursion structural; `TauCeti.cyclotomicCoeffs` supplies enough of it, and
is the intended interface.  This recursion cannot be `private`, since the exposed body of
`TauCeti.cyclotomicCoeffs` mentions it. -/
@[expose] def cyclotomicCoeffsAux : ℕ → ℕ → List ℤ
  | 0, _ => [1]
  | fuel + 1, n =>
    if n = 0 then [1]
    else
      (((List.range n).filter fun d => n % d == 0).foldl
        (fun l d => divByMonicList (cyclotomicCoeffsAux fuel d).tail l)
        (xPowSubOneCoeffs n)).dropWhile (· == 0)

/-- **The coefficients of the `n`-th cyclotomic polynomial over `ℤ`**, highest degree first, as a
genuine `def`: `cyclotomicCoeffs 12 = [1, 0, -1, 0, 1]`, the coefficients of `X ^ 4 - X ^ 2 + 1`.
`TauCeti.cyclotomicCoeffs_eq_coeffList` proves that this is `Polynomial.coeffList` of
`Polynomial.cyclotomic n ℤ`. -/
@[expose] def cyclotomicCoeffs (n : ℕ) : List ℤ := cyclotomicCoeffsAux n n

/-- Dropping leading zeros from a coefficient list does not change the polynomial. -/
private theorem ofCoeffList_dropWhile_beq_zero (l : List ℤ) :
    ofCoeffList (l.dropWhile (· == 0)) = ofCoeffList l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0
    · subst ha; simpa [List.dropWhile_cons] using ih
    · simp [ha]

/-- The computed coefficient list never starts with a zero: it is either `[1]` or the result of
dropping the leading zeros. -/
private theorem headD_cyclotomicCoeffsAux_ne_zero (fuel n : ℕ)
    (h : cyclotomicCoeffsAux fuel n ≠ []) : (cyclotomicCoeffsAux fuel n).headD 0 ≠ 0 := by
  cases fuel with
  | zero => simp [cyclotomicCoeffsAux]
  | succ fuel =>
    rw [cyclotomicCoeffsAux] at h ⊢
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0]; simp
    · -- what is left after dropping the leading zeros does not start with a zero
      have hdrop : ∀ l : List ℤ, l.dropWhile (· == 0) ≠ [] →
          (l.dropWhile (· == 0)).headD 0 ≠ 0 := fun l hl => by
        have hpos : 0 < (l.dropWhile (· == 0)).length := List.length_pos_iff.2 hl
        simpa [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] using
          List.dropWhile_get_zero_not (· == 0) l hpos
      rw [ite_eq_right hn0] at h ⊢
      exact hdrop _ h

/-- **Dividing out a known family of monic factors.**  If the polynomial of `l` is `A` times the
product of the cyclotomic polynomials indexed by `L`, then dividing successively by those factors
leaves `A`.  The factors are supplied as coefficient lists through `f`, in the form
`TauCeti.divByMonicList` consumes them. -/
private theorem ofCoeffList_foldl_divByMonicList (f : ℕ → List ℤ) (A : ℤ[X]) (L : List ℕ)
    (l : List ℤ)
    (hf : ∀ d ∈ L, X ^ (f d).tail.length + ofCoeffList (f d).tail = cyclotomic d ℤ)
    (hl : ofCoeffList l = A * (L.map fun d => cyclotomic d ℤ).prod) :
    ofCoeffList (L.foldl (fun l d => divByMonicList (f d).tail l) l) = A := by
  induction L generalizing l with
  | nil => simpa using hl
  | cons d L ih =>
    refine ih _ (fun e he => hf e (List.mem_cons_of_mem _ he)) ?_
    rw [ofCoeffList_divByMonicList, hf d List.mem_cons_self, hl, List.map_cons, List.prod_cons,
      ← mul_assoc, mul_comm A, mul_assoc, mul_divByMonic_cancel_left _ (cyclotomic.monic d ℤ)]

/-- The list the recursion folds over is exactly the set of proper divisors of `n`. -/
private theorem mem_filter_range_iff_mem_properDivisors {n d : ℕ} :
    d ∈ (List.range n).filter (fun d => n % d == 0) ↔ d ∈ n.properDivisors := by
  simp [List.mem_filter, Nat.mem_properDivisors, Nat.dvd_iff_mod_eq_zero, and_comm]

/-- **The recursion computes the cyclotomic polynomial**, once it is given enough fuel: `n` steps
suffice for `Φ_n`, since each recursive call is at a proper divisor. -/
private theorem ofCoeffList_cyclotomicCoeffsAux (fuel : ℕ) :
    ∀ n ≤ fuel, ofCoeffList (cyclotomicCoeffsAux fuel n) = cyclotomic n ℤ := by
  induction fuel with
  | zero =>
    intro n hn
    rw [Nat.le_zero.1 hn]
    simp [cyclotomicCoeffsAux, ofCoeffList_cons]
  | succ fuel ih =>
    intro n hn
    rw [cyclotomicCoeffsAux]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, hn0]
      simp [ofCoeffList_cons]
    rw [ite_eq_right hn0, ofCoeffList_dropWhile_beq_zero]
    have hnodup : ((List.range n).filter (fun d => n % d == 0)).Nodup :=
      (List.nodup_range).filter _
    have htoFinset : ((List.range n).filter (fun d => n % d == 0)).toFinset = n.properDivisors := by
      ext d
      simpa using mem_filter_range_iff_mem_properDivisors
    refine ofCoeffList_foldl_divByMonicList _ _ _ _ (fun d hd => ?_) ?_
    · have hd' := mem_filter_range_iff_mem_properDivisors.1 hd
      have hdn : d < n := (Nat.mem_properDivisors.1 hd').2
      have hIH : ofCoeffList (cyclotomicCoeffsAux fuel d) = cyclotomic d ℤ := ih d (by omega)
      have hne : cyclotomicCoeffsAux fuel d ≠ [] := by
        intro h0
        rw [h0, ofCoeffList_nil] at hIH
        exact cyclotomic_ne_zero d ℤ hIH.symm
      rw [X_pow_add_ofCoeffList_tail (headD_cyclotomicCoeffsAux_ne_zero fuel d hne)
        (hIH ▸ cyclotomic.monic d ℤ), hIH]
    · rw [ofCoeffList_xPowSubOneCoeffs hn0, ← List.prod_toFinset _ hnodup, htoFinset,
        ← Polynomial.prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_ne_zero hn0) ℤ,
        ← Nat.cons_self_properDivisors hn0, Finset.prod_cons]

/-- **The computed coefficients are the coefficients of the cyclotomic polynomial.** -/
@[simp]
theorem ofCoeffList_cyclotomicCoeffs (n : ℕ) :
    ofCoeffList (cyclotomicCoeffs n) = cyclotomic n ℤ :=
  ofCoeffList_cyclotomicCoeffsAux n n le_rfl

/-- The computed list is nonempty, `Φ_n` being nonzero. -/
theorem cyclotomicCoeffs_ne_nil (n : ℕ) : cyclotomicCoeffs n ≠ [] := by
  intro h
  have := ofCoeffList_cyclotomicCoeffs n
  rw [h, ofCoeffList_nil] at this
  exact cyclotomic_ne_zero n ℤ this.symm

/-- The computed list has no leading zero. -/
theorem headD_cyclotomicCoeffs_ne_zero (n : ℕ) : (cyclotomicCoeffs n).headD 0 ≠ 0 :=
  headD_cyclotomicCoeffsAux_ne_zero n n (cyclotomicCoeffs_ne_nil n)

/-- The computed list starts with the leading coefficient `1` of the cyclotomic polynomial.

This is deliberately not a `simp` lemma: `List.headD_eq_head?_getD` is itself `simp`, so the
left-hand side is not in simp normal form and the `simpNF` linter rejects the annotation. -/
theorem headD_cyclotomicCoeffs (n : ℕ) : (cyclotomicCoeffs n).headD 0 = 1 := by
  rw [← leadingCoeff_ofCoeffList (Or.inr (headD_cyclotomicCoeffs_ne_zero n)),
    ofCoeffList_cyclotomicCoeffs, (cyclotomic.monic n ℤ).leadingCoeff]

/-- The computed list has one entry for each coefficient of `Φ_n`, whose degree is `φ n`. -/
@[simp]
theorem length_cyclotomicCoeffs (n : ℕ) : (cyclotomicCoeffs n).length = n.totient + 1 := by
  have h := natDegree_ofCoeffList (Or.inr (headD_cyclotomicCoeffs_ne_zero n))
  rw [ofCoeffList_cyclotomicCoeffs, natDegree_cyclotomic] at h
  have : (cyclotomicCoeffs n).length ≠ 0 := by simpa using cyclotomicCoeffs_ne_nil n
  omega

/-- **`TauCeti.cyclotomicCoeffs n` is the coefficient list of `Polynomial.cyclotomic n ℤ`**: the
computation returns the canonical list, leading coefficient first and with no leading zeros.

This is deliberately not a `simp` lemma: it would rewrite `cyclotomicCoeffs` away, and then
`TauCeti.length_cyclotomicCoeffs` — which does normalize the vector size, and is `simp` — has a
left-hand side that is no longer in simp normal form, which the `simpNF` linter rejects. -/
theorem cyclotomicCoeffs_eq_coeffList (n : ℕ) :
    cyclotomicCoeffs n = (cyclotomic n ℤ).coeffList := by
  rw [← ofCoeffList_cyclotomicCoeffs n,
    coeffList_ofCoeffList (Or.inr (headD_cyclotomicCoeffs_ne_zero n))]

/-- **Reduction modulo `Φ_e`**, on coefficient lists: the residue of the polynomial with
coefficient list `l`, returned as its `φ e` coordinates on the power basis
`ζ ^ (φ e - 1), …, ζ, 1` of `ℤ[ζ_e] = ℤ[X]/Φ_e`, highest power first.  This is the reduction step
of multiplication in the exact cyclotomic integers. -/
@[expose] def modByCyclotomic (e : ℕ) (l : List ℤ) : List ℤ :=
  modByMonicList (cyclotomicCoeffs e).tail l

/-- The computed list, presented as `TauCeti.Polynomial.divByMonicList` and
`TauCeti.Polynomial.modByMonicList` consume a monic divisor: `Φ_e` is `X ^ φ e` plus the polynomial
of the remaining coefficients. -/
theorem X_pow_add_ofCoeffList_tail_cyclotomicCoeffs (e : ℕ) :
    X ^ (cyclotomicCoeffs e).tail.length + ofCoeffList (cyclotomicCoeffs e).tail
      = cyclotomic e ℤ := by
  rw [X_pow_add_ofCoeffList_tail (headD_cyclotomicCoeffs_ne_zero e)
    (ofCoeffList_cyclotomicCoeffs e ▸ cyclotomic.monic e ℤ), ofCoeffList_cyclotomicCoeffs]

/-- **Reduction modulo `Φ_e` is computed correctly**: it is Mathlib's `%ₘ` by
`Polynomial.cyclotomic e ℤ`. -/
@[simp]
theorem ofCoeffList_modByCyclotomic (e : ℕ) (l : List ℤ) :
    ofCoeffList (modByCyclotomic e l) = ofCoeffList l %ₘ cyclotomic e ℤ := by
  rw [modByCyclotomic, ofCoeffList_modByMonicList, X_pow_add_ofCoeffList_tail_cyclotomicCoeffs]

/-- A residue modulo `Φ_e` is a vector of `φ e` coordinates, one for each element of the power
basis of `ℤ[ζ_e]`. -/
@[simp]
theorem length_modByCyclotomic (e : ℕ) (l : List ℤ) :
    (modByCyclotomic e l).length = e.totient := by
  rw [modByCyclotomic, length_modByMonicList, List.length_tail, length_cyclotomicCoeffs]
  omega

/-! The computation evaluates in the kernel; `Φ₁ = X - 1`, `Φ₄ = X² + 1`, `Φ₆ = X² - X + 1` and
`Φ₁₂ = X⁴ - X² + 1`, and `ζ₅ ^ 5 = 1`. -/

example : cyclotomicCoeffs 1 = [1, -1] := by decide

example : cyclotomicCoeffs 4 = [1, 0, 1] := by decide

example : cyclotomicCoeffs 6 = [1, -1, 1] := by decide

example : cyclotomicCoeffs 12 = [1, 0, -1, 0, 1] := by decide

example : modByCyclotomic 5 [1, 0, 0, 0, 0, 0] = [0, 0, 0, 1] := by decide

end TauCeti
