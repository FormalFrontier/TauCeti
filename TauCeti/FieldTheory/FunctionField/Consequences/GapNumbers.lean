/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.LargeDegree

/-!
# Pole numbers, gap numbers, and the Weierstrass gap theorem

Fix a place `P` of an algebraic function field `F / k`.  A natural number `n` is a **pole
number** of `P` when some function of `F` has pole divisor exactly `n · P`, and a **gap number**
otherwise (Stichtenoth, Definition 1.6.7).  Pole numbers are detected by the Riemann–Roch
dimensions of the multiples of `P`: `n ≥ 1` is a pole number exactly when
`ℓ((n-1) · P) < ℓ(n · P)`, since a function realizing the jump must have a pole of order exactly
`n` at `P` and none elsewhere.

Because `ℓ` grows by at most `deg P` at each step and is eventually `deg (n · P) + 1 - g`, the
gap numbers are confined to a finite window and can be counted.  At a **rational** place of a
function field of genus `g > 0` the count is exactly `g`, with `1` always a gap and every gap
below `2g` — the **Weierstrass gap theorem** (Stichtenoth, Theorem 1.6.8).  For `g = 0` there
are no gaps at all, and the same statements read correctly.

As in `TauCeti/FieldTheory/FunctionField/Consequences/LargeDegree.lean`, the results that need
Riemann–Roch take a divisor `W` satisfying the Riemann–Roch identity as a hypothesis; its value
`g₀` is the genus by `TauCeti.Divisor.IsRiemannRochDivisor.genus_eq`.

## Main definitions

* `TauCeti.Place.IsPoleNumber`: `n` is a pole number of `P`, that is some function has pole
  divisor `n · P` (Definition 1.6.7).
* `TauCeti.Place.gapNumbers`: the set of gap numbers of `P`, the complement of the pole
  numbers — the set the Weierstrass gap theorem counts.

## Main results

* `TauCeti.Place.isPoleNumber_iff_dim_lt`: **Stichtenoth, Lemma 1.6.7** — for `n ≥ 1`, being a
  pole number is exactly the jump `ℓ((n-1) · P) < ℓ(n · P)`.
* `TauCeti.Place.isPoleNumber_of_two_mul_le`: **Stichtenoth, Proposition 1.6.6** — every
  `n ≥ 2g` is a pole number of every place, at any degree.
* `TauCeti.Place.ncard_gapNumbers_inter_Iio_add_dim`: the gap-counting identity at a rational
  place — the number of gaps below `N + 1` plus `ℓ(N · P)` is `N + 1`.
* `TauCeti.Place.gapNumbers_subset_Ico`, `TauCeti.Place.ncard_gapNumbers` and
  `TauCeti.Place.one_mem_gapNumbers`: **the Weierstrass gap theorem** (Theorem 1.6.8) at a
  rational place — the gap numbers lie in `[1, 2g)`, there are exactly `g` of them, and `1` is
  one of them as soon as `g ≥ 1`.

## Implementation notes

The count comes from the telescoping identity
`TauCeti.Place.ncard_gapNumbers_inter_Iio_add_dim`: for a rational place `P`, the number of gaps
below `N + 1` plus `ℓ(N · P)` is `N + 1`.  Each step from `N` to `N + 1` either is a gap and
leaves `ℓ` alone, or is a pole number and raises `ℓ` by exactly one, since `deg P = 1` caps the
increase.  Evaluating at `N = 2g - 1`, where `ℓ((2g-1) · P) = g`, gives the count `g`.

The characteristic-`p` refinements of Stichtenoth's Remark 1.6.9 — that all but finitely many
places share one gap sequence, and the resulting Weierstrass points — are not proved there and
are not attempted here.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 1.6.7, Proposition 1.6.6, Lemma 1.6.7 and Theorem 1.6.8.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {W : Divisor k F} {g₀ : ℕ}

/-- **A pole number of a place** (Stichtenoth, Definition 1.6.7): `n` is a pole number of `P`
when some nonzero function of `F` has pole divisor exactly `n · P`, that is a pole of order `n`
at `P` and no pole at any other place.  Every place has `0` as a pole number, realized by the
constants. -/
def Place.IsPoleNumber (P : Place k F) (hF : IsFunctionField k F) (n : ℕ) : Prop :=
  ∃ z : Fˣ, Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P

/-- `n` is a pole number of `P` exactly when some nonzero function has pole divisor `n · P`. -/
theorem Place.isPoleNumber_iff {P : Place k F} {hF : IsFunctionField k F} {n : ℕ} :
    P.IsPoleNumber hF n ↔ ∃ z : Fˣ, Divisor.poles hF z = (n : ℤ) • WeilDivisor.ofPoint P :=
  (Iff.rfl)

/-- **The gap numbers of a place** (Stichtenoth, Definition 1.6.7): the natural numbers that are
not pole numbers of `P`.  Stichtenoth restricts the notion to `n ≥ 1`; the restriction is
automatic, since `0` is always a pole number
(`TauCeti.Place.one_le_of_mem_gapNumbers`). -/
def Place.gapNumbers (P : Place k F) (hF : IsFunctionField k F) : Set ℕ :=
  {n | ¬ P.IsPoleNumber hF n}

@[simp]
theorem Place.mem_gapNumbers_iff {P : Place k F} {hF : IsFunctionField k F} {n : ℕ} :
    n ∈ P.gapNumbers hF ↔ ¬ P.IsPoleNumber hF n :=
  (Iff.rfl)

/-- `0` is a pole number of every place: the constants have no poles at all. -/
theorem Place.isPoleNumber_zero (P : Place k F) (hF : IsFunctionField k F) :
    P.IsPoleNumber hF 0 :=
  ⟨1, WeilDivisor.ext fun Q ↦ by simp⟩

/-- Gap numbers are positive. -/
theorem Place.one_le_of_mem_gapNumbers {P : Place k F} {hF : IsFunctionField k F} {n : ℕ}
    (hn : n ∈ P.gapNumbers hF) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact absurd (P.isPoleNumber_zero hF) hn
  · exact h

/-- A positive pole number, unfolded: `n ≥ 1` is a pole number of `P` exactly when some function
has order `-n` at `P` and nonnegative order at every other place. -/
theorem Place.isPoleNumber_iff_ord_eq_neg (P : Place k F) (hF : IsFunctionField k F) {n : ℕ}
    (hn : 1 ≤ n) :
    P.IsPoleNumber hF n ↔
      ∃ z : Fˣ, P.ord (z : F) = -(n : ℤ) ∧ ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (z : F) := by
  refine exists_congr fun z ↦ ⟨fun hz ↦ ⟨?_, fun Q hQ ↦ ?_⟩, fun ⟨hP, hQ⟩ ↦ ?_⟩
  · have h := congrArg (fun D ↦ WeilDivisor.coeff D P) hz
    simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self,
      mul_one] at h
    omega
  · have h := congrArg (fun D ↦ WeilDivisor.coeff D Q) hz
    simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_of_ne hQ, mul_zero] at h
    omega
  · refine WeilDivisor.ext fun Q ↦ ?_
    rcases eq_or_ne Q P with rfl | h
    · simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self,
        mul_one, hP]
      omega
    · simp only [Divisor.coeff_poles, WeilDivisor.coeff_zsmul,
        WeilDivisor.coeff_ofPoint_of_ne h, mul_zero]
      have := hQ Q h
      omega

/-- **Stichtenoth, Lemma 1.6.7**: for `n ≥ 1`, being a pole number of `P` is exactly the jump
`ℓ((n-1) · P) < ℓ(n · P)`.

A function witnessing the jump lies in `L(n · P)` but not in `L((n-1) · P)`, which forces its
order at `P` to be exactly `-n` and its order elsewhere to be nonnegative; conversely such a
function witnesses the jump. -/
theorem Place.isPoleNumber_iff_dim_lt (P : Place k F) (hF : IsFunctionField k F) {n : ℕ}
    (hn : 1 ≤ n) :
    P.IsPoleNumber hF n ↔
      Divisor.dim (((n : ℤ) - 1) • WeilDivisor.ofPoint P) <
        Divisor.dim ((n : ℤ) • WeilDivisor.ofPoint P) := by
  have hle : (((n : ℤ) - 1) • WeilDivisor.ofPoint P : Divisor k F)
      ≤ (n : ℤ) • WeilDivisor.ofPoint P := WeilDivisor.zsmul_ofPoint_le_zsmul_ofPoint P (by omega)
  constructor
  · rintro h
    obtain ⟨z, hzP, hzQ⟩ := (P.isPoleNumber_iff_ord_eq_neg hF hn).mp h
    have hmem : (z : F) ∈ riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F) :=
      (mem_riemannRochSpace_zsmul_ofPoint_iff z.ne_zero).mpr ⟨by omega, hzQ⟩
    have := finiteDimensional_riemannRochSpace hF
      ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F)
    rw [Divisor.dim_def, Divisor.dim_def]
    refine Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (riemannRochSpace_mono hle) fun heq ↦ ?_)
    rw [← heq] at hmem
    have := ((mem_riemannRochSpace_zsmul_ofPoint_iff z.ne_zero).mp hmem).1
    omega
  · intro h
    by_contra hnp
    -- With no function of pole divisor `n · P`, the two Riemann–Roch spaces coincide.
    have hsub : riemannRochSpace ((n : ℤ) • WeilDivisor.ofPoint P : Divisor k F)
        ≤ riemannRochSpace (((n : ℤ) - 1) • WeilDivisor.ofPoint P) := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · exact Submodule.zero_mem _
      obtain ⟨hordP, hordQ⟩ := (mem_riemannRochSpace_zsmul_ofPoint_iff hx0).mp hx
      refine (mem_riemannRochSpace_zsmul_ofPoint_iff hx0).mpr ⟨?_, hordQ⟩
      by_contra hlt
      refine hnp ((P.isPoleNumber_iff_ord_eq_neg hF hn).mpr ⟨Units.mk0 x hx0, ?_, ?_⟩)
      · rw [Units.val_mk0]
        omega
      · simpa using hordQ
    rw [Divisor.dim_def, Divisor.dim_def,
      le_antisymm (riemannRochSpace_mono hle) hsub] at h
    exact lt_irrefl _ h

/-- **Stichtenoth, Proposition 1.6.6**, with no hypothesis on the degree of `P`: every `n ≥ 2g`
is a pole number of every place `P`.  Equivalently, for such `n` there is a function whose pole
divisor is exactly `n · P`.

Both `(n-1) · P` and `n · P` have degree at least `2g - 1`, so
`TauCeti.Divisor.IsRiemannRochDivisor.dim_eq_degree_add_one_sub` evaluates both dimensions and
their difference is `deg P ≥ 1`. -/
theorem Place.isPoleNumber_of_two_mul_le (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) {n : ℕ}
    (hn : 2 * g₀ ≤ n) : P.IsPoleNumber hF n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · exact P.isPoleNumber_zero hF
  have hd : (1 : ℤ) ≤ (P.degree : ℤ) := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hdegA : Divisor.degree ((((n : ℤ) - 1)) • WeilDivisor.ofPoint P : Divisor k F)
      = ((n : ℤ) - 1) * P.degree := by
    rw [Divisor.degree_zsmul, Divisor.degree_ofPoint]
  have hdegB : Divisor.degree (((n : ℤ)) • WeilDivisor.ofPoint P : Divisor k F)
      = (n : ℤ) * P.degree := by
    rw [Divisor.degree_zsmul, Divisor.degree_ofPoint]
  -- `(n-1) · deg P` is already in the range where Riemann's inequality is an equality.
  have hbound : 2 * (g₀ : ℤ) - 1 ≤ ((n : ℤ) - 1) * P.degree := by
    have := mul_le_mul_of_nonneg_left hd (by omega : (0 : ℤ) ≤ (n : ℤ) - 1)
    have hn' : 2 * (g₀ : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    nlinarith
  have hA := hW.dim_eq_degree_add_one_sub hF hex (D := ((n : ℤ) - 1) • WeilDivisor.ofPoint P)
    (by rw [hdegA]; exact hbound)
  have hB := hW.dim_eq_degree_add_one_sub hF hex (D := (n : ℤ) • WeilDivisor.ofPoint P)
    (by rw [hdegB]; nlinarith)
  rw [hdegA] at hA
  rw [hdegB] at hB
  refine (P.isPoleNumber_iff_dim_lt hF hn1).mpr ?_
  have hstep : ((n : ℤ) - 1) * P.degree < (n : ℤ) * P.degree := by nlinarith
  omega

/-- The gap numbers of `P` lie in the window `[1, 2g)` (Stichtenoth, Theorem 1.6.8, the bound
`i_g ≤ 2g - 1`). -/
theorem Place.gapNumbers_subset_Ico (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    P.gapNumbers hF ⊆ Set.Ico 1 (2 * g₀) := fun _ hn ↦
  ⟨Place.one_le_of_mem_gapNumbers hn,
    lt_of_not_ge fun h ↦ hn (P.isPoleNumber_of_two_mul_le hF hex hW h)⟩

/-- The gap numbers of a place form a finite set. -/
theorem Place.finite_gapNumbers (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) :
    (P.gapNumbers hF).Finite :=
  (Set.finite_Ico 1 (2 * g₀)).subset (P.gapNumbers_subset_Ico hF hex hW)

open scoped Classical in
/-- The `Finset` form of `TauCeti.Place.ncard_gapNumbers_inter_Iio_add_dim`, in which the
induction on `N` runs. -/
private theorem card_filter_mem_gapNumbers_add_dim (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hP : P.degree = 1) (N : ℕ) :
    ((Finset.range (N + 1)).filter fun n ↦ n ∈ P.gapNumbers hF).card
      + Divisor.dim ((N : ℤ) • WeilDivisor.ofPoint P) = N + 1 := by
  induction N with
  | zero =>
    have h0 : (0 : ℕ) ∉ P.gapNumbers hF := not_not_intro (P.isPoleNumber_zero hF)
    rw [Finset.range_one, Finset.filter_singleton, ite_eq_right h0, Finset.card_empty,
      Nat.cast_zero, zero_zsmul, Divisor.dim_zero_of_isIntegrallyClosedIn hF hex]
  | succ N ih =>
    have hstep : ((N : ℤ) • WeilDivisor.ofPoint P : Divisor k F)
        ≤ ((N + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P :=
      WeilDivisor.zsmul_ofPoint_le_zsmul_ofPoint P (by push_cast; omega)
    have hdegN : Divisor.degree ((N : ℤ) • WeilDivisor.ofPoint P : Divisor k F) = (N : ℤ) := by
      rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one]
    have hdegN1 : Divisor.degree (((N + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P : Divisor k F)
        = (N : ℤ) + 1 := by
      rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one]
      push_cast
      ring
    have hmono := Divisor.dim_mono hF hstep
    have hle := Divisor.dim_le_dim_add_degree_sub hF hstep
    rw [hdegN, hdegN1] at hle
    have hiff := P.isPoleNumber_iff_dim_lt hF (n := N + 1) (Nat.le_add_left 1 N)
    rw [show (((N + 1 : ℕ) : ℤ) - 1) = (N : ℤ) by push_cast; ring] at hiff
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hg : (N + 1) ∈ P.gapNumbers hF
    · rw [ite_eq_left hg, Finset.card_insert_of_notMem (by simp)]
      have hnotlt : ¬ Divisor.dim ((N : ℤ) • WeilDivisor.ofPoint P) <
          Divisor.dim (((N + 1 : ℕ) : ℤ) • WeilDivisor.ofPoint P) :=
        fun hlt ↦ Place.mem_gapNumbers_iff.mp hg (hiff.mpr hlt)
      omega
    · rw [ite_eq_right hg]
      have hlt := hiff.mp (not_not.mp hg)
      omega

/-- **The gap-counting identity** at a rational place: the number of gap numbers below `N + 1`,
plus `ℓ(N · P)`, is `N + 1`.

Each step from `N` to `N + 1` raises `ℓ` by one when `N + 1` is a pole number and leaves it
alone when `N + 1` is a gap, since `deg P = 1` caps the increase at one. -/
theorem Place.ncard_gapNumbers_inter_Iio_add_dim (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hP : P.degree = 1) (N : ℕ) :
    (P.gapNumbers hF ∩ Set.Iio (N + 1)).ncard
      + Divisor.dim ((N : ℤ) • WeilDivisor.ofPoint P) = N + 1 := by
  classical
  rw [show P.gapNumbers hF ∩ Set.Iio (N + 1)
      = ↑((Finset.range (N + 1)).filter fun n ↦ n ∈ P.gapNumbers hF) from Set.ext fun n ↦ by
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_Iio]
    exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩, Set.ncard_coe_finset]
  exact card_filter_mem_gapNumbers_add_dim P hF hex hP N

/-- **The Weierstrass gap theorem, the count** (Stichtenoth, Theorem 1.6.8): a rational place of
a function field of genus `g` has exactly `g` gap numbers.  The set really is finite, by
`TauCeti.Place.finite_gapNumbers`, so this is not the junk value of `Set.ncard`. -/
theorem Place.ncard_gapNumbers (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) (hP : P.degree = 1) :
    (P.gapNumbers hF).ncard = g₀ := by
  classical
  have heq : P.gapNumbers hF
      = ↑((Finset.range (2 * g₀)).filter fun n ↦ n ∈ P.gapNumbers hF) := by
    ext n
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hn ↦ ⟨(P.gapNumbers_subset_Ico hF hex hW hn).2, hn⟩, fun h ↦ h.2⟩
  rw [heq, Set.ncard_coe_finset]
  rcases Nat.eq_zero_or_pos g₀ with rfl | hg
  · simp
  have hcount := card_filter_mem_gapNumbers_add_dim P hF hex hP (2 * g₀ - 1)
  rw [show 2 * g₀ - 1 + 1 = 2 * g₀ by omega] at hcount
  have hdeg : Divisor.degree ((((2 * g₀ - 1 : ℕ)) : ℤ) • WeilDivisor.ofPoint P : Divisor k F)
      = ((2 * g₀ - 1 : ℕ) : ℤ) := by
    rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP, Nat.cast_one, mul_one]
  have hdim := hW.dim_eq_degree_add_one_sub hF hex
    (D := (((2 * g₀ - 1 : ℕ)) : ℤ) • WeilDivisor.ofPoint P) (by rw [hdeg]; omega)
  rw [hdeg] at hdim
  omega

/-- **The Weierstrass gap theorem, the first gap** (Stichtenoth, Theorem 1.6.8): at a rational
place of a function field of genus `g ≥ 1` the number `1` is a gap, so the smallest gap is
`i₁ = 1`.

Were `1` a pole number, a function `z` with a single simple pole at `P` would make every power
`zⁿ` witness the pole number `n`, leaving no gaps at all — contradicting the count `g ≥ 1`. -/
theorem Place.one_mem_gapNumbers (P : Place k F) (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hW : W.IsRiemannRochDivisor g₀) (hP : P.degree = 1)
    (hg : 1 ≤ g₀) : 1 ∈ P.gapNumbers hF := by
  rw [Place.mem_gapNumbers_iff]
  intro h1
  obtain ⟨z, hz, hzQ⟩ := (P.isPoleNumber_iff_ord_eq_neg hF le_rfl).mp h1
  rw [Nat.cast_one] at hz
  have hall : ∀ n : ℕ, P.IsPoleNumber hF n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact P.isPoleNumber_zero hF
    refine (P.isPoleNumber_iff_ord_eq_neg hF hn).mpr ⟨z ^ n, ?_, fun Q hQ ↦ ?_⟩
    · rw [Units.val_pow_eq_pow_val, P.ord_pow, hz]
      ring
    · rw [Units.val_pow_eq_pow_val, Q.ord_pow]
      exact mul_nonneg (Nat.cast_nonneg n) (hzQ Q hQ)
  have hempty : P.gapNumbers hF = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun n hn ↦ hn (hall n)
  have hcount := P.ncard_gapNumbers hF hex hW hP
  rw [hempty, Set.ncard_empty] at hcount
  omega

end TauCeti
