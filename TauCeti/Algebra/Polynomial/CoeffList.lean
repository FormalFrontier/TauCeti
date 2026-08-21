/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.NoncommRing

/-!
# Polynomials from a list of coefficients, and division by a monic polynomial

`Polynomial` is a `Finsupp`, so none of its arithmetic reduces in the kernel.  A polynomial
presented instead by the list of its coefficients does compute, and this file sets up the
translation, together with the one algorithm a computation on such lists needs: division by a
monic polynomial.

`TauCeti.Polynomial.ofCoeffList l` is the polynomial whose coefficients are the entries of `l`,
read from the highest degree down, so that it inverts Mathlib's `Polynomial.coeffList`
(`TauCeti.Polynomial.coeffList_ofCoeffList` and `TauCeti.Polynomial.ofCoeffList_coeffList`).  Its
defining recursion is Horner's, `ofCoeffList (l ++ [a]) = ofCoeffList l * X + C a`, and every proof
below runs along it.  It is a `noncomputable` specification map: the *lists* are what compute.

`TauCeti.Polynomial.mulCoeffList` multiplies two such lists by convolving their coefficients, and
`TauCeti.Polynomial.ofCoeffList_mulCoeffList` identifies the result with the product polynomial.

`TauCeti.Polynomial.divModByMonicList t l` is long division of `ofCoeffList l` by the monic
polynomial `X ^ t.length + ofCoeffList t`, carried out as the usual synthetic division: a window of
`t.length` remainder coefficients is carried along the dividend, and at each step the coefficient
shifted out of the window is the next quotient coefficient and is used to clear the window against
the divisor.  Presenting the divisor by the list `t` of the coefficients *below* its leading one
makes it monic by construction, so `TauCeti.Polynomial.ofCoeffList_divByMonicList` and
`TauCeti.Polynomial.ofCoeffList_modByMonicList`, which identify the two outputs with Mathlib's `/ₘ`
and `%ₘ`, need no hypotheses at all.  Like Mathlib's `/ₘ` and `%ₘ`, the division needs no
commutativity: the window is cleared by `x - y * c`, with the quotient coefficient `c` on the
right, which is what matches Mathlib's convention `f = g * q + r` with the divisor on the left.

The division definitions are `@[expose]`d, since a consumer computing with them in another module
reduces them in the kernel.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The polynomial whose coefficients are the entries of `l`, highest degree first:
`ofCoeffList [a, b, c] = C a * X ^ 2 + C b * X + C c`.  This is Horner's rule, and it inverts
Mathlib's `Polynomial.coeffList` (`TauCeti.Polynomial.coeffList_ofCoeffList`). -/
noncomputable def ofCoeffList (l : List R) : R[X] :=
  l.foldl (fun p a => p * X + C a) 0

/-- The empty list of coefficients defines the zero polynomial. -/
@[simp]
theorem ofCoeffList_nil : ofCoeffList ([] : List R) = 0 := by
  simp [ofCoeffList]

/-- The Horner recursion defining `TauCeti.Polynomial.ofCoeffList`: appending the coefficient `a`
at the bottom multiplies the polynomial so far by `X` and adds the constant `C a`. -/
@[simp]
theorem ofCoeffList_concat (l : List R) (a : R) :
    ofCoeffList (l ++ [a]) = ofCoeffList l * X + C a := by
  simp [ofCoeffList]

/-- The coefficients of `TauCeti.Polynomial.ofCoeffList l` are the entries of `l` read backwards. -/
@[simp]
theorem coeff_ofCoeffList (l : List R) (i : ℕ) :
    (ofCoeffList l).coeff i = l.reverse.getD i 0 := by
  induction l using List.reverseRecOn generalizing i with
  | nil => simp
  | append_singleton l a ih =>
    rw [ofCoeffList_concat]
    cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- A list of `n` coefficients defines a polynomial of degree less than `n`. -/
theorem degree_ofCoeffList_lt (l : List R) : (ofCoeffList l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_ofCoeffList, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by simpa using hm), Option.getD_none]

/-- Splitting off the leading coefficient of a list of coefficients. -/
@[simp]
theorem ofCoeffList_cons (a : R) (l : List R) :
    ofCoeffList (a :: l) = C a * X ^ l.length + ofCoeffList l := by
  ext i
  rw [coeff_add, coeff_ofCoeffList, coeff_ofCoeffList, coeff_C_mul, coeff_X_pow,
    List.reverse_cons]
  rcases lt_or_ge i l.length with h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h), ite_eq_right h.ne, mul_zero, zero_add]
  · rw [List.getD_eq_getElem?_getD (l := l.reverse),
      List.getElem?_eq_none (by simpa using h), Option.getD_none,
      List.getD_append_right _ _ _ _ (by simpa using h)]
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h', ite_eq_left rfl, mul_one, add_zero]
      simp
    · rw [ite_eq_right (by omega), mul_zero, zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), Option.getD_none]

/-- A leading zero coefficient may be dropped.  This is not a `simp` lemma: `simp` already gets
there through `TauCeti.Polynomial.ofCoeffList_cons`. -/
theorem ofCoeffList_zero_cons (l : List R) : ofCoeffList ((0 : R) :: l) = ofCoeffList l := by
  simp [ofCoeffList_cons]

/-- A list of zeros defines the zero polynomial. -/
@[simp]
theorem ofCoeffList_replicate_zero (n : ℕ) : ofCoeffList (List.replicate n (0 : R)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, ofCoeffList_zero_cons, ih]

/-- Splitting off the leading coefficient of a nonempty list of coefficients. -/
theorem ofCoeffList_eq_headD_add_tail {l : List R} (hl : l ≠ []) :
    ofCoeffList l = C (l.headD 0) * X ^ l.tail.length + ofCoeffList l.tail := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => simp [ofCoeffList_cons]

/-- The top coefficient of `TauCeti.Polynomial.ofCoeffList l` is the head of `l`. -/
theorem coeff_ofCoeffList_length_sub_one (l : List R) :
    (ofCoeffList l).coeff (l.length - 1) = l.headD 0 := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [coeff_ofCoeffList, List.reverse_cons, List.headD_cons,
      List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- A list with no leading zero has exactly one more entry than the degree of the polynomial it
defines.  The empty list is allowed: it defines `0`, of degree `0`. -/
theorem natDegree_ofCoeffList {l : List R} (h : l = [] ∨ l.headD 0 ≠ 0) :
    (ofCoeffList l).natDegree = l.length - 1 := by
  rcases h with rfl | h
  · simp
  have hl : l ≠ [] := by rintro rfl; exact h rfl
  have hc : (ofCoeffList l).coeff (l.length - 1) ≠ 0 := by
    rw [coeff_ofCoeffList_length_sub_one]; exact h
  have hne : ofCoeffList l ≠ 0 := fun h0 => hc (by simp [h0])
  refine le_antisymm ?_ (le_natDegree_of_ne_zero hc)
  have hlt := degree_ofCoeffList_lt l
  rw [degree_eq_natDegree hne, Nat.cast_lt] at hlt
  have : l.length ≠ 0 := by simpa using hl
  omega

/-- A list with no leading zero has its head as the leading coefficient of the polynomial it
defines.  The empty list is allowed: it defines `0`, whose leading coefficient is `0`. -/
theorem leadingCoeff_ofCoeffList {l : List R} (h : l = [] ∨ l.headD 0 ≠ 0) :
    (ofCoeffList l).leadingCoeff = l.headD 0 := by
  rw [leadingCoeff, natDegree_ofCoeffList h, coeff_ofCoeffList_length_sub_one]

/-- Two lists of the same length define the same polynomial only if they are equal.  This is not
injectivity of `TauCeti.Polynomial.ofCoeffList`, which discards leading zeros. -/
theorem eq_of_length_eq_of_ofCoeffList_eq {l l' : List R} (hlen : l.length = l'.length)
    (h : ofCoeffList l = ofCoeffList l') : l = l' := by
  have hrev : l.reverse = l'.reverse := by
    refine List.ext_getElem (by simpa using hlen) fun i hi hi' => ?_
    have hc := congrArg (fun p => Polynomial.coeff p i) h
    rw [coeff_ofCoeffList, coeff_ofCoeffList, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hi'] at hc
    exact hc
  simpa using congrArg List.reverse hrev

/-- `TauCeti.Polynomial.ofCoeffList` inverts Mathlib's `Polynomial.coeffList` on the lists that
arise as coefficient lists, namely those with no leading zero. -/
theorem coeffList_ofCoeffList {l : List R} (h : l = [] ∨ l.headD 0 ≠ 0) :
    (ofCoeffList l).coeffList = l := by
  classical
  rcases h with rfl | h
  · simp
  have hl : l ≠ [] := by rintro rfl; exact h rfl
  have hlpos : l.length ≠ 0 := by simpa using hl
  have hne : ofCoeffList l ≠ 0 := by
    intro h0
    exact h (by rw [← coeff_ofCoeffList_length_sub_one, h0, coeff_zero])
  have hlen : (ofCoeffList l).coeffList.length = l.length := by
    rw [Polynomial.length_coeffList_eq_ite, ite_eq_right hne, natDegree_ofCoeffList (Or.inr h)]
    omega
  have hdeg : (ofCoeffList l).degree.succ = l.length := by
    rw [← Polynomial.length_coeffList_eq_withBotSucc_degree]; exact hlen
  refine List.ext_getElem hlen fun i hi hi' => ?_
  simp only [Polynomial.coeffList, List.getElem_map, List.getElem_reverse, List.length_range,
    List.getElem_range, hdeg, coeff_ofCoeffList]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse]
  congr 1
  omega

/-- `TauCeti.Polynomial.ofCoeffList` is a left inverse of Mathlib's `Polynomial.coeffList`: every
polynomial is recovered from its coefficient list. -/
@[simp]
theorem ofCoeffList_coeffList (p : R[X]) : ofCoeffList p.coeffList = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hsucc : p.degree.succ = p.natDegree + 1 := withBotSucc_degree_eq_natDegree_add_one hp
  ext i
  rw [coeff_ofCoeffList, Polynomial.coeffList, List.map_reverse, List.reverse_reverse]
  rcases lt_or_ge i (p.natDegree + 1) with h | h
  · rw [List.getD_eq_getElem _ _ (by simp [hsucc]; omega)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hsucc]; omega),
      Option.getD_none]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Multiplication of descending coefficient lists, by convolving them in ascending degree order.
The output has the usual `l.length + m.length - 1` slots; if either input is empty, all of those
slots are zero.  This is `@[expose]`d, since a consumer computing with it in another module
reduces it in the kernel. -/
@[expose] def mulCoeffList (l m : List R) : List R :=
  (List.ofFn fun i : Fin (l.length + m.length - 1) =>
    ∑ jk ∈ Finset.antidiagonal (i : ℕ),
      l.reverse.getD jk.1 0 * m.reverse.getD jk.2 0).reverse

/-- `TauCeti.Polynomial.mulCoeffList` lists the coefficients of a product of polynomials. -/
theorem ofCoeffList_mulCoeffList (l m : List R) :
    ofCoeffList (mulCoeffList l m) = ofCoeffList l * ofCoeffList m := by
  ext n
  rw [coeff_ofCoeffList, coeff_mul]
  by_cases hn : n < l.length + m.length - 1
  · rw [mulCoeffList, List.reverse_reverse, List.getD_eq_getElem]
    · simp
    · simpa using hn
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp [mulCoeffList]; omega),
      Option.getD_none]
    simp only [coeff_ofCoeffList]
    symm
    apply Finset.sum_eq_zero
    intro jk hjk
    rw [Finset.mem_antidiagonal] at hjk
    by_cases hl : jk.1 < l.length
    · have hm : m.length ≤ jk.2 := by omega
      have hm0 : m.reverse.getD jk.2 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hm),
          Option.getD_none]
      rw [hm0, mul_zero]
    · have hl0 : l.reverse.getD jk.1 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hl),
          Option.getD_none]
      rw [hl0, zero_mul]

/-- The divisor `X ^ t.length + ofCoeffList t` of `TauCeti.Polynomial.divModByMonicList` is
monic. -/
theorem monic_X_pow_add_ofCoeffList (t : List R) : (X ^ t.length + ofCoeffList t).Monic :=
  monic_X_pow_add (degree_ofCoeffList_lt t)

/-- The divisor `X ^ t.length + ofCoeffList t` has degree exactly `t.length`. -/
theorem degree_X_pow_add_ofCoeffList [Nontrivial R] (t : List R) :
    (X ^ t.length + ofCoeffList t).degree = ((t.length : ℕ) : WithBot ℕ) := by
  rw [degree_add_eq_left_of_degree_lt (by simpa using degree_ofCoeffList_lt t), degree_X_pow]

/-- A monic polynomial is `X ^ n` plus the polynomial of its remaining coefficients.  This is how
a computed coefficient list is recognized as a divisor for `TauCeti.Polynomial.divByMonicList`. -/
theorem X_pow_add_ofCoeffList_tail {l : List R} (hhead : l.headD 0 ≠ 0)
    (hmonic : (ofCoeffList l).Monic) :
    X ^ l.tail.length + ofCoeffList l.tail = ofCoeffList l := by
  have hl : l ≠ [] := by rintro rfl; exact hhead rfl
  have ha : l.headD 0 = 1 := by
    rw [← leadingCoeff_ofCoeffList (Or.inr hhead), hmonic.leadingCoeff]
  rw [ofCoeffList_eq_headD_add_tail hl, ha, map_one, one_mul]

end Semiring

section Ring

variable [Ring R]

/-- Negating every coefficient negates the polynomial. -/
@[simp]
theorem ofCoeffList_map_neg (l : List R) : ofCoeffList (l.map (-·)) = -ofCoeffList l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.map_append, List.map_cons, List.map_nil, ofCoeffList_concat, ofCoeffList_concat, ih,
      map_neg, neg_mul, ← neg_add]

/-- Subtracting a right multiple of one list of coefficients from another, entrywise. -/
theorem ofCoeffList_zipWith_sub (c : R) {l l' : List R} (h : l.length = l'.length) :
    ofCoeffList (List.zipWith (fun x y => x - y * c) l l')
      = ofCoeffList l - ofCoeffList l' * C c := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons a l ih =>
    cases l' with
    | nil => simp at h
    | cons b l' =>
      have hlen : l.length = l'.length := by simpa using h
      rw [List.zipWith_cons_cons, ofCoeffList_cons, ofCoeffList_cons, ofCoeffList_cons,
        ih hlen, List.length_zipWith, hlen, min_self, C_sub, C_mul, sub_mul, add_mul,
        X_pow_mul_assoc_C]
      abel

/-- One step of synthetic division by the monic polynomial `X ^ t.length + ofCoeffList t`: the
pair `qr` holds the quotient coefficients found so far together with a window of `t.length`
remainder coefficients, and `a` is the next coefficient of the dividend. -/
@[expose] def divModByMonicStep (t : List R) (qr : List R × List R) (a : R) :
    List R × List R :=
  let w := qr.2 ++ [a]
  let c := w.headD 0
  (qr.1 ++ [c], List.zipWith (fun x y => x - y * c) w.tail t)

/-- One step of synthetic division appends the coefficient shifted out of the remainder window to
the quotient. -/
@[simp]
theorem divModByMonicStep_fst (t : List R) (qr : List R × List R) (a : R) :
    (divModByMonicStep t qr a).1 = qr.1 ++ [(qr.2 ++ [a]).headD 0] :=
  rfl

/-- One step of synthetic division clears the remaining window against the divisor. -/
@[simp]
theorem divModByMonicStep_snd (t : List R) (qr : List R × List R) (a : R) :
    (divModByMonicStep t qr a).2
      = List.zipWith (fun x y => x - y * (qr.2 ++ [a]).headD 0) (qr.2 ++ [a]).tail t :=
  rfl

/-- Long division of the polynomial with coefficient list `l` by the monic polynomial
`X ^ t.length + ofCoeffList t`, by synthetic division.  The first component is the coefficient
list of the quotient, the second that of the remainder. -/
@[expose] def divModByMonicList (t l : List R) : List R × List R :=
  l.foldl (divModByMonicStep t) ([], List.replicate t.length 0)

/-- The quotient of `ofCoeffList l` by the monic polynomial `X ^ t.length + ofCoeffList t`, as a
coefficient list. -/
@[expose] def divByMonicList (t l : List R) : List R := (divModByMonicList t l).1

/-- The remainder of `ofCoeffList l` on division by the monic polynomial
`X ^ t.length + ofCoeffList t`, as a coefficient list. -/
@[expose] def modByMonicList (t l : List R) : List R := (divModByMonicList t l).2

/-- Dividing the zero polynomial leaves the empty quotient and the zero remainder window. -/
@[simp]
theorem divModByMonicList_nil (t : List R) :
    divModByMonicList t ([] : List R) = ([], List.replicate t.length 0) := rfl

/-- The division sweeps the dividend from the top coefficient down, one step per coefficient. -/
@[simp]
theorem divModByMonicList_concat (t l : List R) (a : R) :
    divModByMonicList t (l ++ [a]) = divModByMonicStep t (divModByMonicList t l) a := by
  simp [divModByMonicList]

/-- The remainder window keeps the length of the divisor's degree throughout the division. -/
theorem length_divModByMonicList_snd (t l : List R) :
    (divModByMonicList t l).2.length = t.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih => simp [divModByMonicList_concat, ih]

/-- The computed remainder has the length of the divisor's degree. -/
@[simp]
theorem length_modByMonicList (t l : List R) : (modByMonicList t l).length = t.length :=
  length_divModByMonicList_snd t l

/-- **The division identity for synthetic division**: at every stage of the sweep, the part of the
dividend read so far is the divisor times the quotient found so far, plus the remainder window. -/
theorem ofCoeffList_divModByMonicList (t l : List R) :
    ofCoeffList l = (X ^ t.length + ofCoeffList t) * ofCoeffList (divModByMonicList t l).1
      + ofCoeffList (divModByMonicList t l).2 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    have hlen : (divModByMonicList t l).2.length = t.length := length_divModByMonicList_snd t l
    have hwne : (divModByMonicList t l).2 ++ [a] ≠ [] := by simp
    have hwlen : ((divModByMonicList t l).2 ++ [a]).tail.length = t.length := by
      simp [hlen]
    have hw1 : ofCoeffList ((divModByMonicList t l).2 ++ [a])
        = ofCoeffList (divModByMonicList t l).2 * X + C a := ofCoeffList_concat _ _
    have hw2 : ofCoeffList ((divModByMonicList t l).2 ++ [a])
        = C (((divModByMonicList t l).2 ++ [a]).headD 0) * X ^ t.length
          + ofCoeffList ((divModByMonicList t l).2 ++ [a]).tail := by
      rw [ofCoeffList_eq_headD_add_tail hwne, hwlen]
    -- the window, with its top coefficient split off and the quotient coefficient moved to the
    -- right of `X ^ t.length`, which is where the divisor puts it
    have hw : ofCoeffList ((divModByMonicList t l).2 ++ [a]).tail
        = ofCoeffList (divModByMonicList t l).2 * X + C a
          - X ^ t.length * C (((divModByMonicList t l).2 ++ [a]).headD 0) := by
      rw [eq_sub_iff_add_eq, X_pow_mul_C, add_comm, ← hw2, hw1]
    rw [ofCoeffList_concat, ih, divModByMonicList_concat, divModByMonicStep_fst,
      divModByMonicStep_snd, ofCoeffList_concat, ofCoeffList_zipWith_sub _ hwlen, hw]
    noncomm_ring

/-- **Synthetic division computes the quotient**: the first output of
`TauCeti.Polynomial.divModByMonicList` is Mathlib's `/ₘ` by the monic divisor. -/
@[simp]
theorem ofCoeffList_divByMonicList (t l : List R) :
    ofCoeffList (divByMonicList t l) = ofCoeffList l /ₘ (X ^ t.length + ofCoeffList t) := by
  nontriviality R
  refine ((div_modByMonic_unique (ofCoeffList (divByMonicList t l))
    (ofCoeffList (modByMonicList t l)) (monic_X_pow_add_ofCoeffList t) ⟨?_, ?_⟩).1).symm
  · rw [add_comm]; exact (ofCoeffList_divModByMonicList t l).symm
  · rw [degree_X_pow_add_ofCoeffList]
    exact lt_of_lt_of_le (degree_ofCoeffList_lt _) (by rw [length_modByMonicList])

/-- **Synthetic division computes the remainder**: the second output of
`TauCeti.Polynomial.divModByMonicList` is Mathlib's `%ₘ` by the monic divisor. -/
@[simp]
theorem ofCoeffList_modByMonicList (t l : List R) :
    ofCoeffList (modByMonicList t l) = ofCoeffList l %ₘ (X ^ t.length + ofCoeffList t) := by
  nontriviality R
  refine ((div_modByMonic_unique (ofCoeffList (divByMonicList t l))
    (ofCoeffList (modByMonicList t l)) (monic_X_pow_add_ofCoeffList t) ⟨?_, ?_⟩).2).symm
  · rw [add_comm]; exact (ofCoeffList_divModByMonicList t l).symm
  · rw [degree_X_pow_add_ofCoeffList]
    exact lt_of_lt_of_le (degree_ofCoeffList_lt _) (by rw [length_modByMonicList])

end Ring

end TauCeti.Polynomial
