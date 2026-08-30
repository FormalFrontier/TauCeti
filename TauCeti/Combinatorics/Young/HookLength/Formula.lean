/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.BetaNumbers
public import TauCeti.Combinatorics.Young.StandardTableau.Corner
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Combinatorics.Young.StandardTableau.Reading
import TauCeti.LinearAlgebra.Vandermonde

/-!
# The Frobenius determinant formula and the hook-length formula

Let `μ` be a Young diagram with `n = μ.card` cells and let `f^μ = TauCeti.standardCount μ` be its
number of standard Young tableaux. This file proves the **multiplicative hook-length formula**

`f^μ * ∏ c ∈ μ.cells, hookLength μ c = n !`

(`TauCeti.standardCount_mul_prod_hookLength`), the milestone of Layer 5 of the Schur--Weyl
roadmap. It carries no division obligation, and the quotient form `f^μ = n ! / ∏ hooks`, which
follows from it because the hook lengths are positive, is simply not stated here.

## The route

Fix a bound `r` on the number of rows and write `βᵢ = μ.rowLen i + (r - 1 - i)` for the
beta-numbers `YoungDiagram.betaNumber μ r i`, which strictly decrease across
`i < j < r`. The hook lengths are already related to them by
`YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`:

`(∏ c ∈ μ.cells, hookLength μ c) * ∏_{i < j < r} (βᵢ - βⱼ) = ∏_{i < r} βᵢ !`.

What remains, and is the substance of this file, is the **Frobenius determinant formula**

`f^μ * ∏_{i < r} βᵢ ! = n ! * ∏_{i < j < r} (βᵢ - βⱼ)`

(`TauCeti.standardCount_mul_prod_factorial_betaNumber`). Dividing one by the other cancels the
Vandermonde-style product, which is positive, and leaves the hook-length formula.

The Frobenius formula is proved by induction on `n` along the corner recursion
`TauCeti.standardCount_eq_sum_corners`, `f^μ = ∑_{c a corner} f^{μ ∖ c}`. Erasing a corner lowers
the beta-number of its row by one and leaves the others alone
(`YoungDiagram.IsCorner.betaNumber_erase`), and `βᵢ ! = βᵢ * (βᵢ - 1) !` converts the induction
hypothesis for `μ ∖ c` into a statement about `μ`. Summing it over the corners reduces the
induction step to an identity between Vandermonde-style products,

`∑_{i < r} βᵢ * ∏_{k < l < r} (β^{(i)}_k - β^{(i)}_l)`
` = (∑_{i < r} βᵢ - ∑_{i < r} i) * ∏_{k < l < r} (β_k - β_l)`

where `β^{(i)}` lowers `βᵢ` by one, which is `TauCeti.sum_mul_prod_sub_update_sub_one`. Two
bookkeeping facts fit the two sides together. First, the rows of the corners inject into
`{0, …, r - 1}`,
because a corner is the last cell of its row; and a row `i < r` carrying no corner contributes
nothing to the left-hand sum, since either `βᵢ = 0` or `βᵢ₊₁ = βᵢ - 1` with `i + 1 < r`, which
puts a zero factor in its product. Second, `∑_{i < r} βᵢ - ∑_{i < r} i = n`, because the row
lengths sum to `n` and the shifts `r - 1 - i` are a reflection of `0, 1, …, r - 1`.

## Main results

* `TauCeti.standardCount_mul_prod_factorial_betaNumber`: **the Frobenius determinant formula.**
* `TauCeti.standardCount_mul_prod_hookLength`: **the multiplicative hook-length formula.**

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, and Section 7, Example 6, for the beta-number route to the hook-length formula.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose `hookLengthFormula` milestone this closes.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {r i : ℕ}

/-! ### Corners and beta-numbers -/

/-- A row inside the bound that carries no corner and whose beta-number is nonzero is followed,
still inside the bound, by a row whose beta-number is one smaller: either the row is empty and
only the shift `r - 1 - i` contributes, or the row below it has the same length. -/
private theorem betaNumber_succ_add_one_of_forall_ne (hr : μ.colLen 0 ≤ r) (hi : i < r)
    (hβ : μ.betaNumber r i ≠ 0) (hno : ∀ c ∈ corners μ, c.1 ≠ i) :
    i + 1 < r ∧ μ.betaNumber r (i + 1) + 1 = μ.betaNumber r i := by
  have hanti : μ.rowLen (i + 1) ≤ μ.rowLen i := μ.rowLen_anti i (i + 1) (by omega)
  have hcase : μ.rowLen i = 0 ∨ μ.rowLen (i + 1) = μ.rowLen i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, hne⟩ := hcon
    refine hno (i, μ.rowLen i - 1) (mem_corners.mpr ((isCorner_def μ _).mpr ⟨?_, ?_, ?_⟩)) rfl
    · exact mem_iff_lt_rowLen.mpr (by omega)
    · simp only [mem_iff_lt_rowLen]; omega
    · simp only [mem_iff_lt_rowLen]; omega
  simp only [betaNumber_def] at hβ ⊢
  rcases hcase with h0 | h1
  · have h1 : μ.rowLen (i + 1) = 0 := by omega
    omega
  · rcases Nat.eq_zero_or_pos (μ.rowLen i) with h0 | h0
    · have h2 : μ.rowLen (i + 1) = 0 := by omega
      omega
    · have hmem : (i + 1, 0) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
      have := mem_iff_lt_colLen.mp hmem
      omega

end YoungDiagram

namespace TauCeti

open Finset Nat YoungDiagram

/-! ### The Frobenius determinant formula -/

/-- The Vandermonde-style product of the differences of the beta-numbers is computed by the same
formula over `ℤ`, the differences being nonnegative. -/
private theorem cast_prod_betaNumber_sub (μ : YoungDiagram) (r : ℕ) :
    ((∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r, (μ.betaNumber r k - μ.betaNumber r l) : ℕ) : ℤ)
      = ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
          ((μ.betaNumber r k : ℤ) - (μ.betaNumber r l : ℤ)) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [mem_Ico] at hl
  exact Nat.cast_sub (μ.betaNumber_lt_betaNumber (by omega) hl.2).le

/-- A row of the diagram carrying no corner contributes nothing to the lowering identity: either
its beta-number vanishes, or lowering that beta-number by one makes it agree with the next one,
which puts a zero factor in the product. -/
private theorem betaNumber_term_eq_zero {μ : YoungDiagram} {r i : ℕ} (hr : μ.colLen 0 ≤ r)
    (hi : i ∈ range r) (hno : ∀ c ∈ corners μ, c.1 ≠ i) :
    (μ.betaNumber r i : ℤ) *
        ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
          (Function.update (fun j => (μ.betaNumber r j : ℤ)) i ((μ.betaNumber r i : ℤ) - 1) k
            - Function.update (fun j => (μ.betaNumber r j : ℤ)) i
                ((μ.betaNumber r i : ℤ) - 1) l)
      = 0 := by
  by_cases hβ : μ.betaNumber r i = 0
  · rw [hβ]; simp
  obtain ⟨hlt, hsucc⟩ := betaNumber_succ_add_one_of_forall_ne hr (mem_range.mp hi) hβ hno
  have hcast : ((μ.betaNumber r (i + 1) : ℤ)) + 1 = (μ.betaNumber r i : ℤ) := by
    exact_mod_cast hsucc
  have hinner : ∏ l ∈ Ico (i + 1) r,
      (Function.update (fun j => (μ.betaNumber r j : ℤ)) i ((μ.betaNumber r i : ℤ) - 1) i
        - Function.update (fun j => (μ.betaNumber r j : ℤ)) i
            ((μ.betaNumber r i : ℤ) - 1) l) = 0 := by
    refine Finset.prod_eq_zero (mem_Ico.mpr ⟨le_rfl, hlt⟩) ?_
    rw [Function.update_self, Function.update_of_ne (by omega)]
    omega
  rw [Finset.prod_eq_zero hi hinner, mul_zero]

/-- The rows of the corners inject into the rows inside the bound, and a row carrying no corner
contributes nothing, so a sum over the corners of a diagram is a sum over its rows. -/
private theorem sum_corners_eq_sum_range {μ : YoungDiagram} {r : ℕ} (hr : μ.colLen 0 ≤ r)
    (F : ℕ → ℤ) (hF : ∀ i ∈ range r, (∀ c ∈ corners μ, c.1 ≠ i) → F i = 0) :
    ∑ c ∈ corners μ, F c.1 = ∑ i ∈ range r, F i := by
  classical
  have hinj : ∀ c ∈ corners μ, ∀ d ∈ corners μ, c.1 = d.1 → c = d :=
    fun c hc d hd h => (mem_corners.mp hc).eq_of_fst_eq (mem_corners.mp hd) h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_subset (fun i hi => ?_) fun i hi hni => ?_
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
    exact mem_range.mpr (((mem_corners.mp hc).fst_lt_colLen_zero).trans_le hr)
  · exact hF i hi fun c hc h => hni (Finset.mem_image.mpr ⟨c, hc, h⟩)

/-- The beta-numbers overshoot the number of cells by exactly `0 + 1 + ⋯ + (r - 1)`: the row
lengths sum to `μ.card`, and the shifts `r - 1 - i` are a reflection of `0, 1, …, r - 1`. -/
private theorem sum_betaNumber_sub_sum_range (μ : YoungDiagram) {r : ℕ} (hr : μ.colLen 0 ≤ r) :
    (∑ i ∈ range r, (μ.betaNumber r i : ℤ)) - ∑ i ∈ range r, (i : ℤ) = (μ.card : ℤ) := by
  have hsplit : ∑ i ∈ range r, (μ.betaNumber r i : ℤ)
      = (∑ i ∈ range r, (μ.rowLen i : ℤ)) + ∑ i ∈ range r, ((r - 1 - i : ℕ) : ℤ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [betaNumber_def]; push_cast; ring
  have hrows : ∑ i ∈ range r, (μ.rowLen i : ℤ) = (μ.card : ℤ) := by
    rw [← Nat.cast_sum, ← YoungDiagram.card_eq_sum_range_rowLen μ hr]
  rw [hsplit, hrows, Finset.sum_range_reflect (fun j : ℕ => (j : ℤ)) r]
  ring

/-- The inductive form of the Frobenius determinant formula, with the number of cells fixed so
that the corner recursion is an ordinary induction. -/
private theorem standardCount_mul_prod_factorial_betaNumber_aux (n : ℕ) :
    ∀ (μ : YoungDiagram) (r : ℕ), μ.card = n → μ.colLen 0 ≤ r →
      (standardCount μ : ℤ) * ∏ i ∈ range r, ((μ.betaNumber r i) ! : ℤ)
        = (n ! : ℤ) * ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
            ((μ.betaNumber r k : ℤ) - (μ.betaNumber r l : ℤ)) := by
  induction n with
  | zero =>
    intro μ r hcard hr
    have hcells : μ.cells = ∅ := Finset.card_eq_zero.mp hcard
    have hcol : μ.colLen 0 = 0 := by
      by_contra hc
      have hmem : (0, 0) ∈ μ := mem_iff_lt_colLen.mpr (by omega)
      rw [← mem_cells, hcells] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    have hprod := YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial μ hr
    rw [hcells, Finset.prod_empty, one_mul] at hprod
    rw [standardCount_eq_one_of_colLen_le_one (by omega), Nat.cast_one, one_mul,
      Nat.factorial_zero, Nat.cast_one, one_mul, ← cast_prod_betaNumber_sub, hprod, Nat.cast_prod]
  | succ n ih =>
    intro μ r hcard hr
    -- the induction hypothesis at each corner, rescaled by the beta-number of its row
    have hcorner : ∀ c ∈ corners μ,
        (standardCount (μ.erase c) : ℤ) * ∏ i ∈ range r, ((μ.betaNumber r i) ! : ℤ)
          = (n ! : ℤ) * ((μ.betaNumber r c.1 : ℤ) *
              ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
                (Function.update (fun j => (μ.betaNumber r j : ℤ)) c.1
                    ((μ.betaNumber r c.1 : ℤ) - 1) k
                  - Function.update (fun j => (μ.betaNumber r j : ℤ)) c.1
                      ((μ.betaNumber r c.1 : ℤ) - 1) l)) := by
      intro c hc
      have hcc : IsCorner μ c := mem_corners.mp hc
      have hb : 1 ≤ μ.betaNumber r c.1 := by
        rw [betaNumber_def, hcc.rowLen_eq_snd_add_one]; omega
      have hcard' : (μ.erase c).card = n := by have := hcc.card_erase; omega
      have hr' : (μ.erase c).colLen 0 ≤ r := by
        rw [hcc.colLen_erase]; split_ifs <;> omega
      -- the erased beta-numbers are the original ones with the corner's row lowered by one
      have hbeta : ∀ i, (((μ.erase c).betaNumber r i : ℕ) : ℤ)
          = Function.update (fun j => (μ.betaNumber r j : ℤ)) c.1
              ((μ.betaNumber r c.1 : ℤ) - 1) i := by
        intro i
        rcases eq_or_ne c.1 i with rfl | h
        · rw [hcc.betaNumber_erase r c.1, ite_eq_left rfl, Function.update_self]
          omega
        · rw [hcc.betaNumber_erase r i, ite_eq_right h, Function.update_of_ne (Ne.symm h)]
      -- `βᵢ ! = βᵢ * (βᵢ - 1) !` at the corner's row, and nothing changes elsewhere
      have hmem : c.1 ∈ range r := mem_range.mpr (hcc.fst_lt_colLen_zero.trans_le hr)
      have hfact : (μ.betaNumber r c.1 : ℤ) *
          ∏ i ∈ range r, (((μ.erase c).betaNumber r i) ! : ℤ)
            = ∏ i ∈ range r, ((μ.betaNumber r i) ! : ℤ) := by
        rw [← Finset.mul_prod_erase (range r) (fun i => (((μ.erase c).betaNumber r i) ! : ℤ)) hmem,
          ← Finset.mul_prod_erase (range r) (fun i => ((μ.betaNumber r i) ! : ℤ)) hmem,
          ← mul_assoc]
        refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun i hi => ?_)
        · rw [hcc.betaNumber_erase r c.1, ite_eq_left rfl, ← Nat.cast_mul,
            Nat.mul_factorial_pred (by omega)]
        · rw [hcc.betaNumber_erase r i, ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hi))]
      rw [← hfact, ← mul_assoc, mul_comm ((standardCount (μ.erase c) : ℤ)), mul_assoc,
        ih (μ.erase c) r hcard' hr', ← mul_assoc, mul_comm ((μ.betaNumber r c.1 : ℤ)), mul_assoc]
      exact congrArg _ (congrArg _ (Finset.prod_congr rfl fun k _ =>
        Finset.prod_congr rfl fun l _ => by rw [hbeta k, hbeta l]))
    have hzero : ∀ i ∈ range r, (∀ c ∈ corners μ, c.1 ≠ i) →
        (μ.betaNumber r i : ℤ) *
          ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
            (Function.update (fun j => (μ.betaNumber r j : ℤ)) i ((μ.betaNumber r i : ℤ) - 1) k
              - Function.update (fun j => (μ.betaNumber r j : ℤ)) i
                  ((μ.betaNumber r i : ℤ) - 1) l) = 0 :=
      fun i hi hno => betaNumber_term_eq_zero hr hi hno
    rw [standardCount_eq_sum_corners (by omega : 0 < μ.card), Nat.cast_sum, Finset.sum_mul,
      Finset.sum_congr rfl hcorner, ← Finset.mul_sum,
      sum_corners_eq_sum_range hr _ hzero,
      TauCeti.sum_mul_prod_sub_update_sub_one r fun j => (μ.betaNumber r j : ℤ),
      sum_betaNumber_sub_sum_range μ hr, hcard]
    rw [Nat.factorial_succ]
    push_cast
    ring

/-- **The Frobenius determinant formula** for the number `f^μ` of standard Young tableaux of shape
`μ`: for any bound `r` on the number of rows, `f^μ` times the product of the factorials of the
beta-numbers is `μ.card !` times the product of their differences over the ordered pairs of rows.

The differences are differences of natural numbers, and are truncated at no ordered pair: the
beta-numbers strictly decrease across `k < l < r`.

This is the multiplicative form of `f^μ = n ! * ∏_{k < l} (β_k - β_l) / ∏_k β_k !`, and carries no
division obligation. -/
theorem standardCount_mul_prod_factorial_betaNumber (μ : YoungDiagram) {r : ℕ}
    (hr : μ.colLen 0 ≤ r) :
    standardCount μ * ∏ i ∈ range r, (μ.betaNumber r i) !
      = μ.card ! * ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
          (μ.betaNumber r k - μ.betaNumber r l) := by
  have h := standardCount_mul_prod_factorial_betaNumber_aux μ.card μ r rfl hr
  rw [← cast_prod_betaNumber_sub] at h
  exact_mod_cast h

/-! ### The hook-length formula -/

/-- **The multiplicative hook-length formula.** The number of standard Young tableaux of shape `μ`,
times the product of the hook lengths of the cells of `μ`, is the factorial of the number of cells.

The quotient form `f^μ = μ.card ! / ∏ hooks`, which follows from this one because the hook lengths
are positive, is not stated here. -/
theorem standardCount_mul_prod_hookLength (μ : YoungDiagram) :
    standardCount μ * ∏ c ∈ μ.cells, YoungDiagram.hookLength μ c = μ.card ! := by
  obtain ⟨r, hr⟩ : ∃ r, μ.colLen 0 ≤ r := ⟨μ.colLen 0, le_rfl⟩
  have hV : 0 < ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r, (μ.betaNumber r k - μ.betaNumber r l) :=
    Finset.prod_pos fun k _ => Finset.prod_pos fun l hl => by
      rw [mem_Ico] at hl
      have := μ.betaNumber_lt_betaNumber (i := k) (j := l) (by omega) hl.2
      omega
  have hhook := YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial μ hr
  refine Nat.eq_of_mul_eq_mul_right hV ?_
  rw [mul_assoc, hhook]
  exact standardCount_mul_prod_factorial_betaNumber μ hr

end TauCeti
