/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# The classical integral roots of type `Dₙ`

This file constructs the classical integral root set of type `Dₙ`, uniformly for `n ≥ 4`, and
gives the concrete infrastructure needed to build its pinned integral root datum.

The classical roots are the `2 * n * (n - 1)` vectors `±e_a ±e_b`, `a < b`. They are first
enumerated by a sign and an ordered pair of distinct coordinates: increasing pairs represent
`e_a - e_b`, decreasing pairs represent `e_b + e_a`. The enumeration puts the chain roots
`e_i - e_(i+1)` first, followed by the fork root `e_(n-2) + e_(n-1)`; the remaining order is
explicit but mathematically immaterial.

Every root is expanded explicitly in the Bourbaki-numbered simple roots. Reflections are
constructed directly on the set of squared-length-two vectors and proved involutive.

## Main definitions and results

* `TauCeti.DynkinType.TypeDRoot` is the set of integral vectors of squared length two.
* `TauCeti.DynkinType.typeDRootEquiv` enumerates these roots by `Fin (2 * n * (n - 1))`.
* `TauCeti.DynkinType.typeDSimpleRoot` gives the Bourbaki-numbered simple roots.
* `TauCeti.DynkinType.sum_smul_typeDSimpleRootCoordinates` expands every root in that basis.
* `TauCeti.DynkinType.typeDRootReflectionEquiv` is reflection in a root.

## References

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IV, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section 12.1.
This supplies the classical-root prerequisite for the `Dₙ` branch of “a named datum per valid
type” in Layer 6 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-! ## Classical roots and their enumeration -/

/-- Ordered pairs of distinct coordinate indices. Increasing pairs encode difference roots and
decreasing pairs encode sum roots. -/
private abbrev TypeDPair (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The positive type `Dₙ` root encoded by an ordered pair: `e_a - e_b` for `a < b`, and
`e_b + e_a` for `b < a`. -/
private def typeDPairVector (p : TypeDPair n) : Fin n → ℤ :=
  if p.val.1 < p.val.2 then Pi.single p.val.1 1 - Pi.single p.val.2 1
  else Pi.single p.val.2 1 + Pi.single p.val.1 1

/-- A sign and an ordered pair encode all roots of type `Dₙ`. Sign `0` is positive and sign `1`
is negative. -/
private abbrev TypeDRawIndex (n : ℕ) := Fin 2 × TypeDPair n

private def typeDRawVector (r : TypeDRawIndex n) : Fin n → ℤ :=
  if r.1 = 0 then typeDPairVector r.2 else -typeDPairVector r.2

private lemma typeDPairVector_dot_self (p : TypeDPair n) :
    typeDPairVector p ⬝ᵥ typeDPairVector p = 2 := by
  have hp : p.val.1 ≠ p.val.2 := p.property
  by_cases h : p.val.1 < p.val.2
  · simp [typeDPairVector, h, dotProduct_sub, dotProduct_single, hp]
  · have h' : p.val.2 ≠ p.val.1 := Ne.symm hp
    simp [typeDPairVector, h, dotProduct_add, dotProduct_single, hp, h']

private lemma typeDRawVector_dot_self (r : TypeDRawIndex n) :
    typeDRawVector r ⬝ᵥ typeDRawVector r = 2 := by
  by_cases h : r.1 = 0
  · simpa [typeDRawVector, h] using typeDPairVector_dot_self r.2
  · simpa [typeDRawVector, h, neg_dotProduct, dotProduct_neg] using typeDPairVector_dot_self r.2

/-- The integral vectors of squared length two. For `n ≥ 2`, these are exactly the classical
roots `±e_a ±e_b` of type `Dₙ`. -/
abbrev TypeDRoot (n : ℕ) := {x : Fin n → ℤ // x ⬝ᵥ x = 2}

private def typeDRawRoot (r : TypeDRawIndex n) : TypeDRoot n :=
  ⟨typeDRawVector r, typeDRawVector_dot_self r⟩

private lemma support_typeDPairVector (p : TypeDPair n) :
    Function.support (typeDPairVector p) = {p.val.1, p.val.2} := by
  ext i
  have hp : p.val.1 ≠ p.val.2 := p.property
  by_cases hlt : p.val.1 < p.val.2
  · simp only [typeDPairVector, if_pos hlt]
    by_cases hi : i = p.val.1 <;> by_cases hj : i = p.val.2 <;>
      simp_all [Function.mem_support]
  · simp only [typeDPairVector, if_neg hlt]
    by_cases hi : i = p.val.1 <;> by_cases hj : i = p.val.2 <;>
      simp_all [Function.mem_support]

private lemma support_typeDRawVector (r : TypeDRawIndex n) :
    Function.support (typeDRawVector r) = {r.2.val.1, r.2.val.2} := by
  by_cases h : r.1 = 0
  · simpa [typeDRawVector, h] using support_typeDPairVector r.2
  · simpa [typeDRawVector, h, Function.support_neg] using support_typeDPairVector r.2

private lemma typeDRawVector_injective : Injective (typeDRawVector (n := n)) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  have hsupp : ({p.val.1, p.val.2} : Set (Fin n)) = {q.val.1, q.val.2} := by
    rw [← support_typeDRawVector (s, p), ← support_typeDRawVector (t, q), h]
  rcases Set.pair_eq_pair_iff.mp hsupp with hsame | hswap
  · have hpq : p = q := Subtype.ext (Prod.ext hsame.1 hsame.2)
    subst q
    apply Prod.ext
    · apply Fin.ext
      have hv := congrFun h p.val.1
      have hp : p.val.1 ≠ p.val.2 := p.property
      by_cases hlt : p.val.1 < p.val.2 <;> fin_cases s <;> fin_cases t <;>
        simp [typeDRawVector, typeDPairVector, hlt, hp] at hv <;> simp_all
    · rfl
  · have hp : p.val.1 ≠ p.val.2 := p.property
    have hq : q.val.1 ≠ q.val.2 := q.property
    have qeq : q = (⟨(p.val.2, p.val.1), Ne.symm hp⟩ : TypeDPair n) := by
      apply Subtype.ext
      exact Prod.ext hswap.2.symm hswap.1.symm
    rw [qeq] at h
    exfalso
    have hv₁ := congrFun h p.val.1
    have hv₂ := congrFun h p.val.2
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · fin_cases s <;> fin_cases t <;>
        simp [typeDRawVector, typeDPairVector, hlt, not_lt_of_ge (le_of_lt hlt), hp] at hv₁ hv₂
    · fin_cases s <;> fin_cases t <;>
        simp [typeDRawVector, typeDPairVector, hgt, not_lt_of_ge (le_of_lt hgt), hp] at hv₁ hv₂

private lemma typeDRawRoot_injective : Injective (typeDRawRoot (n := n)) := by
  intro r s h
  exact typeDRawVector_injective (congrArg Subtype.val h)

private lemma typeDRoot_sq_le_two (x : TypeDRoot n) (i : Fin n) : x.1 i ^ 2 ≤ 2 := by
  have hnonneg : ∀ j : Fin n, 0 ≤ x.1 j ^ 2 := fun j => sq_nonneg _
  have hi : x.1 i ^ 2 ≤ ∑ j : Fin n, x.1 j ^ 2 :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  calc
    x.1 i ^ 2 ≤ ∑ j : Fin n, x.1 j ^ 2 := hi
    _ = x.1 ⬝ᵥ x.1 := by simp [dotProduct, pow_two]
    _ = 2 := x.2

private lemma typeDRoot_support_card (x : TypeDRoot n) :
    (Finset.univ.filter fun i : Fin n => x.1 i ≠ 0).card = 2 := by
  classical
  have hsquare : ∀ i : Fin n, x.1 i ^ 2 = if x.1 i = 0 then 0 else 1 := by
    intro i
    split_ifs with hi
    · simp [hi]
    · exact Int.sq_eq_one_of_sq_le_three ((typeDRoot_sq_le_two x i).trans (by norm_num)) hi
  have hsum : ∑ i : Fin n, (if x.1 i = 0 then 0 else (1 : ℤ)) = 2 := by
    calc
      _ = ∑ i : Fin n, x.1 i ^ 2 := Finset.sum_congr rfl fun i _ => (hsquare i).symm
      _ = x.1 ⬝ᵥ x.1 := by simp [dotProduct, pow_two]
      _ = 2 := x.2
  have hsum' : ((Finset.univ.filter fun i : Fin n => x.1 i ≠ 0).card : ℤ) = 2 := by
    simpa [Finset.sum_ite] using hsum
  exact_mod_cast hsum'

private lemma exists_typeDRawRoot_eq_of_lt (x : TypeDRoot n) {a b : Fin n} (hab : a < b)
    (hsupp : (Finset.univ.filter fun i : Fin n => x.1 i ≠ 0) = {a, b})
    (ha : x.1 a = 1 ∨ x.1 a = -1) (hb : x.1 b = 1 ∨ x.1 b = -1) :
    ∃ r, typeDRawRoot r = x := by
  classical
  have hne : a ≠ b := ne_of_lt hab
  have hout : ∀ i, i ≠ a → i ≠ b → x.1 i = 0 := by
    intro i hia hib
    by_contra hi
    have : i ∈ Finset.univ.filter fun j : Fin n => x.1 j ≠ 0 := by simp [hi]
    rw [hsupp] at this
    simp [hia, hib] at this
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · let p : TypeDPair n := ⟨(b, a), Ne.symm (ne_of_lt hab)⟩
    refine ⟨(0, p), Subtype.ext (funext fun i => ?_)⟩
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp_all [typeDRawRoot, typeDRawVector, typeDPairVector, p,
        not_lt_of_ge (le_of_lt hab)]
  · let p : TypeDPair n := ⟨(a, b), ne_of_lt hab⟩
    refine ⟨(0, p), Subtype.ext (funext fun i => ?_)⟩
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp_all [typeDRawRoot, typeDRawVector, typeDPairVector, p]
  · let p : TypeDPair n := ⟨(a, b), ne_of_lt hab⟩
    refine ⟨(1, p), Subtype.ext (funext fun i => ?_)⟩
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp_all [typeDRawRoot, typeDRawVector, typeDPairVector, p]
  · let p : TypeDPair n := ⟨(b, a), Ne.symm (ne_of_lt hab)⟩
    refine ⟨(1, p), Subtype.ext (funext fun i => ?_)⟩
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      simp_all [typeDRawRoot, typeDRawVector, typeDPairVector, p,
        not_lt_of_ge (le_of_lt hab)]

private lemma typeDRawRoot_surjective : Surjective (typeDRawRoot (n := n)) := by
  classical
  intro x
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp (typeDRoot_support_card x)
  have hamem : a ∈ Finset.univ.filter fun i : Fin n => x.1 i ≠ 0 := by
    rw [hsupp]
    simp
  have hbmem : b ∈ Finset.univ.filter fun i : Fin n => x.1 i ≠ 0 := by
    rw [hsupp]
    simp
  have ha0 : x.1 a ≠ 0 := (Finset.mem_filter.mp hamem).2
  have hb0 : x.1 b ≠ 0 := (Finset.mem_filter.mp hbmem).2
  have ha : x.1 a = 1 ∨ x.1 a = -1 := sq_eq_one_iff.mp
    (Int.sq_eq_one_of_sq_le_three ((typeDRoot_sq_le_two x a).trans (by norm_num)) ha0)
  have hb : x.1 b = 1 ∨ x.1 b = -1 := sq_eq_one_iff.mp
    (Int.sq_eq_one_of_sq_le_three ((typeDRoot_sq_le_two x b).trans (by norm_num)) hb0)
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact exists_typeDRawRoot_eq_of_lt x hab hsupp ha hb
  · exact exists_typeDRawRoot_eq_of_lt x hba (by simpa [Finset.pair_comm] using hsupp) hb ha

/-- The explicit signed-pair model enumerates every integral vector of squared length two. -/
private noncomputable def typeDRawRootEquiv (n : ℕ) : TypeDRawIndex n ≃ TypeDRoot n :=
  Equiv.ofBijective typeDRawRoot ⟨typeDRawRoot_injective, typeDRawRoot_surjective⟩

/-! ### The Bourbaki order -/

private lemma one_le_typeDDifference {n : ℕ} (hn : 1 ≤ n) (p : TypeDPair n) :
    1 ≤ ((p.val.2 - p.val.1 : Fin n) : ℕ) := by
  let _ : NeZero n := ⟨by omega⟩
  have h : (p.val.2 - p.val.1 : Fin n) ≠ 0 := fun h =>
    p.property (sub_eq_zero.mp h).symm
  have : ((p.val.2 - p.val.1 : Fin n) : ℕ) ≠ 0 := by
    simpa [Fin.val_eq_zero_iff] using h
  omega

private def typeDDifference (hn : 1 ≤ n) (p : TypeDPair n) : Fin (n - 1) :=
  ⟨((p.val.2 - p.val.1 : Fin n) : ℕ) - 1, by
    have h₁ := one_le_typeDDifference hn p
    have h₂ := (p.val.2 - p.val.1 : Fin n).isLt
    omega⟩

private def typeDSucc (i : Fin (n - 1)) : Fin n := ⟨(i : ℕ) + 1, by omega⟩

private lemma typeDSucc_ne_zero (hn : 1 ≤ n) (i : Fin (n - 1)) :
    typeDSucc i ≠ (⟨0, by omega⟩ : Fin n) := by
  let _ : NeZero n := ⟨by omega⟩
  intro h
  have := congrArg Fin.val h
  simp [typeDSucc] at this

/-- Enumerate ordered distinct pairs by their nonzero cyclic difference first, then their source. -/
private def typeDPairEquiv (n : ℕ) (hn : 1 ≤ n) : TypeDPair n ≃ Fin (n - 1) × Fin n := by
  letI : NeZero n := ⟨by omega⟩
  refine ⟨(fun p => (typeDDifference hn p, p.val.1)),
    (fun q => ⟨(q.2, q.2 + typeDSucc q.1), by
      intro h
      refine typeDSucc_ne_zero hn q.1 ?_
      have h0 : q.2 + 0 = q.2 + typeDSucc q.1 := by simpa using h
      exact (add_left_cancel h0).symm⟩), ?_, ?_⟩
  · intro p
    have h₁ := one_le_typeDDifference hn p
    have hx : typeDSucc (typeDDifference hn p) = p.val.2 - p.val.1 :=
      Fin.ext (by simp [typeDSucc, typeDDifference]; omega)
    refine Subtype.ext (Prod.ext rfl ?_)
    change p.val.1 + typeDSucc (typeDDifference hn p) = p.val.2
    rw [hx]
    abel
  · intro q
    refine Prod.ext (Fin.ext ?_) rfl
    change ((q.2 + typeDSucc q.1 - q.2 : Fin n) : ℕ) - 1 = (q.1 : ℕ)
    simp [typeDSucc]

private def typeDPairFinEquiv (n : ℕ) (hn : 1 ≤ n) : TypeDPair n ≃ Fin (n * (n - 1)) :=
  (typeDPairEquiv n hn).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n - 1) n)))

private def typeDChainEndIndex (n : ℕ) (hn : 2 ≤ n) : Fin (n * (n - 1)) :=
  ⟨n - 1, lt_mul_of_one_lt_left (by omega) hn⟩

private def typeDForkOldIndex (n : ℕ) (hn : 2 ≤ n) : Fin (n * (n - 1)) :=
  ⟨n * (n - 1) - 1, Nat.sub_lt (mul_pos (by omega) (by omega)) (by omega)⟩

/-- The pair enumeration with the fork root moved directly after the `n - 1` chain roots. -/
private def typeDBourbakiPairEquiv (n : ℕ) (hn : 2 ≤ n) :
    TypeDPair n ≃ Fin (n * (n - 1)) :=
  (typeDPairFinEquiv n (by omega)).trans
    (Equiv.swap (typeDChainEndIndex n hn) (typeDForkOldIndex n hn))

/-- The explicit signed-pair enumeration of all `2 * n * (n - 1)` roots, with positive roots
before negative roots and the Bourbaki simple roots in the first `n` positions. -/
private def typeDRawFinEquiv (n : ℕ) (hn : 2 ≤ n) :
    TypeDRawIndex n ≃ Fin (2 * n * (n - 1)) :=
  ((Equiv.refl (Fin 2)).prodCongr (typeDBourbakiPairEquiv n hn)).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

/-- Enumerate the `2 * n * (n - 1)` roots of type `Dₙ`, with the Bourbaki simple roots first. -/
noncomputable def typeDRootEquiv (n : ℕ) (hn : 2 ≤ n) :
    Fin (2 * n * (n - 1)) ≃ TypeDRoot n :=
  (typeDRawFinEquiv n hn).symm.trans (typeDRawRootEquiv n)

/-- The `i`-th simple root occupies root index `i`. -/
def typeDSimpleIndex (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : Fin (2 * n * (n - 1)) :=
  ⟨i, lt_of_lt_of_le i.isLt (by
    have h : n ≤ n * (n - 1) := Nat.le_mul_of_pos_right n (by omega)
    have h' : n * (n - 1) ≤ 2 * (n * (n - 1)) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    simpa [mul_assoc] using h.trans h')⟩

@[simp] lemma typeDSimpleIndex_val (hn : 2 ≤ n) (i : Fin n) :
    (typeDSimpleIndex n hn i : ℕ) = i := (rfl)

lemma typeDSimpleIndex_injective (hn : 2 ≤ n) : Injective (typeDSimpleIndex n hn) := by
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

private def typeDSimpleRawIndex (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : TypeDRawIndex n :=
  if h : (i : ℕ) + 1 < n then
    (0, ⟨(i, ⟨(i : ℕ) + 1, h⟩), by simp [Fin.ext_iff]⟩)
  else
    (0, ⟨(⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩), by simp [Fin.ext_iff]; omega⟩)

private lemma typeDPairFinEquiv_chain (hn : 2 ≤ n) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeDPairFinEquiv n (by omega)
        ⟨(i, ⟨(i : ℕ) + 1, hi⟩), by simp [Fin.ext_iff]⟩ =
      ⟨i, lt_of_lt_of_le i.isLt (Nat.le_mul_of_pos_right n (by omega))⟩ := by
  apply Fin.ext
  suffices (i : ℕ) + n * ((n - (i : ℕ) + ((i : ℕ) + 1)) % n - 1) = (i : ℕ) by
    simpa [typeDPairFinEquiv, typeDPairEquiv, typeDDifference, finProdFinEquiv,
      Fin.sub_def]
  have heq : n - (i : ℕ) + ((i : ℕ) + 1) = n + 1 := by omega
  rw [heq]
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)]

private lemma typeDPairFinEquiv_fork (hn : 2 ≤ n) :
    typeDPairFinEquiv n (by omega)
        ⟨(⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩), by simp [Fin.ext_iff]; omega⟩ =
      typeDForkOldIndex n hn := by
  apply Fin.ext
  suffices n - 1 + n * ((n - (n - 1) + (n - 2)) % n - 1) = n * (n - 1) - 1 by
    simpa [typeDPairFinEquiv, typeDPairEquiv, typeDDifference, typeDForkOldIndex,
      finProdFinEquiv, Fin.sub_def]
  have heq : n - (n - 1) + (n - 2) = n - 1 := by omega
  rw [heq, Nat.mod_eq_of_lt (by omega)]
  have hprev : n - 1 - 1 = n - 2 := by omega
  rw [hprev]
  have hmul : n * (n - 1) = n + n * (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    ring
  rw [hmul]
  omega

private lemma typeDRawFinEquiv_simple (hn : 2 ≤ n) (i : Fin n) :
    typeDRawFinEquiv n hn (typeDSimpleRawIndex n hn i) = typeDSimpleIndex n hn i := by
  by_cases hi : (i : ℕ) + 1 < n
  · have hraw : typeDSimpleRawIndex n hn i =
        (0, ⟨(i, ⟨(i : ℕ) + 1, hi⟩), by simp [Fin.ext_iff]⟩) := by
      simp [typeDSimpleRawIndex, hi]
    rw [hraw]
    apply Fin.ext
    simp only [typeDRawFinEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, typeDBourbakiPairEquiv, Equiv.trans_apply, Prod.map_apply]
    rw [typeDPairFinEquiv_chain hn i hi]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · rfl
    · intro h
      have := congrArg Fin.val h
      simp [typeDChainEndIndex] at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp [typeDForkOldIndex] at this
      have hlt := lt_mul_of_one_lt_left (by omega : 0 < n - 1) hn
      omega
  · have hraw : typeDSimpleRawIndex n hn i =
        (0, ⟨(⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩),
          by simp [Fin.ext_iff]; omega⟩) := by
      simp [typeDSimpleRawIndex, hi]
    have hieq : (i : ℕ) = n - 1 := by omega
    rw [hraw]
    apply Fin.ext
    simp only [typeDRawFinEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, typeDBourbakiPairEquiv, Equiv.trans_apply, Prod.map_apply]
    rw [typeDPairFinEquiv_fork hn, Equiv.swap_apply_right]
    simp [finProdFinEquiv, typeDChainEndIndex, typeDSimpleIndex, hieq]

private lemma typeDRootEquiv_simple (hn : 2 ≤ n) (i : Fin n) :
    typeDRootEquiv n hn (typeDSimpleIndex n hn i) =
      typeDRawRoot (typeDSimpleRawIndex n hn i) := by
  change typeDRawRoot ((typeDRawFinEquiv n hn).symm (typeDSimpleIndex n hn i)) =
    typeDRawRoot (typeDSimpleRawIndex n hn i)
  congr 1
  apply (typeDRawFinEquiv n hn).injective
  rw [Equiv.apply_symm_apply, typeDRawFinEquiv_simple]

/-! ## The pinned lattices -/

/-- The Bourbaki-numbered simple roots of type `Dₙ` in classical orthogonal coordinates. -/
def typeDSimpleRoot (n : ℕ) (hn : 2 ≤ n) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then
    Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1
  else
    Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1

/-- The first `n` entries of `typeDRootEquiv` are the Bourbaki-numbered simple roots. -/
theorem typeDRootEquiv_typeDSimpleIndex (hn : 2 ≤ n) (i : Fin n) :
    (typeDRootEquiv n hn (typeDSimpleIndex n hn i)).1 = typeDSimpleRoot n hn i := by
  rw [typeDRootEquiv_simple]
  by_cases hi : (i : ℕ) + 1 < n
  · have hlt : i < (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by simp [Fin.lt_def]
    simp [typeDSimpleRawIndex, typeDRawRoot, typeDRawVector, typeDPairVector,
      typeDSimpleRoot, hi, hlt]
  · have hlt : ¬(⟨n - 1, by omega⟩ : Fin n) < ⟨n - 2, by omega⟩ := by
      simp [Fin.lt_def]
      omega
    simp [typeDSimpleRawIndex, typeDRawRoot, typeDRawVector, typeDPairVector,
      typeDSimpleRoot, hi, hlt]

private lemma typeDRoot_sum (x : TypeDRoot n) :
    (∑ i : Fin n, x.1 i) = -2 ∨ (∑ i : Fin n, x.1 i) = 0 ∨
      (∑ i : Fin n, x.1 i) = 2 := by
  let r := (typeDRawRootEquiv n).symm x
  have hx : typeDRawRoot r = x := by
    change typeDRawRootEquiv n r = x
    exact Equiv.apply_symm_apply _ x
  have hxv : typeDRawVector r = x.1 := congrArg Subtype.val hx
  rw [← hxv]
  rcases r with ⟨s, p⟩
  fin_cases s <;> by_cases hp : p.val.1 < p.val.2 <;>
    simp [typeDRawVector, typeDPairVector, hp, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]

/-- Half the sum of the classical coordinates. It is integral on type `Dₙ` roots. -/
private def typeDHalfTotal (x : TypeDRoot n) : ℤ :=
  if (∑ i : Fin n, x.1 i) = 2 then 1
  else if (∑ i : Fin n, x.1 i) = -2 then -1 else 0

private lemma two_mul_typeDHalfTotal (x : TypeDRoot n) :
    2 * typeDHalfTotal x = ∑ i : Fin n, x.1 i := by
  rcases typeDRoot_sum x with h | h | h <;> simp [typeDHalfTotal, h]

/-- The coefficients of a type `Dₙ` root in the Bourbaki simple-root basis. -/
def typeDSimpleRootCoordinates (n : ℕ) (hn : 2 ≤ n) (x : TypeDRoot n) : Fin n → ℤ := fun k =>
  if (k : ℕ) + 2 < n then ∑ j ∈ Finset.Iic k, x.1 j
  else if (k : ℕ) + 1 < n then typeDHalfTotal x - x.1 ⟨n - 1, by omega⟩
  else typeDHalfTotal x

/-- Reconstruct a classical vector from its simple-root coordinates. -/
private def typeDSimpleCombination (n : ℕ) (hn : 2 ≤ n) (c : Fin n → ℤ) : Fin n → ℤ :=
  ∑ i : Fin n, c i • typeDSimpleRoot n hn i

private lemma typeDChainHeadSum (c : Fin n → ℤ) (j : Fin n) :
    (∑ i : Fin n, if _h : (i : ℕ) + 1 < n then
      c i * (if j = i then 1 else 0) else 0) =
      if (j : ℕ) + 1 < n then c j else 0 := by
  by_cases hj : (j : ℕ) + 1 < n
  · rw [if_pos hj, Fintype.sum_eq_single j]
    · simp [hj]
    · intro i hi
      simp [Ne.symm hi]
  · rw [if_neg hj, Finset.sum_eq_zero]
    intro i _
    split_ifs with h hij
    · exact False.elim (hj (by simpa [hij] using h))
    · simp
    · rfl

private lemma typeDChainTailSum (c : Fin n → ℤ) (j : Fin n) :
    (∑ i : Fin n, if h : (i : ℕ) + 1 < n then
      c i * (if j = (⟨(i : ℕ) + 1, h⟩ : Fin n) then 1 else 0) else 0) =
      if hj : (j : ℕ) = 0 then 0 else c ⟨(j : ℕ) - 1, by omega⟩ := by
  by_cases hj : (j : ℕ) = 0
  · rw [dif_pos hj, Finset.sum_eq_zero]
    intro i _
    split_ifs with h hi
    · have hv := congrArg Fin.val hi
      simp at hv
      omega
    · simp
    · rfl
  · rw [dif_neg hj, Fintype.sum_eq_single (⟨(j : ℕ) - 1, by omega⟩ : Fin n)]
    · have h : (j : ℕ) - 1 + 1 < n := by omega
      simp only [dif_pos h, Fin.ext_iff]
      rw [if_pos (by omega)]
      simp
    · intro i hi
      split_ifs with h hij
      · have hv := congrArg Fin.val hij
        have hiv : (i : ℕ) ≠ (j : ℕ) - 1 := by
          intro heq
          apply hi
          exact Fin.ext heq
        simp at hv
        omega
      · simp
      · rfl

private lemma typeDForkSum (hn : 1 ≤ n) (c : Fin n → ℤ) :
    (∑ i : Fin n, if (i : ℕ) + 1 < n then 0 else c i) =
      c ⟨n - 1, by omega⟩ := by
  rw [Fintype.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
  · rw [if_neg (by simp only; omega)]
  · intro i hi
    split_ifs with h
    · rfl
    · exfalso
      apply hi
      apply Fin.ext
      simp only
      omega

private lemma typeDSimpleCombination_apply (hn : 2 ≤ n) (c : Fin n → ℤ) (j : Fin n) :
    typeDSimpleCombination n hn c j =
      (if (j : ℕ) + 1 < n then c j else 0) -
        (if hj : (j : ℕ) = 0 then 0 else c ⟨(j : ℕ) - 1, by omega⟩) +
        c ⟨n - 1, by omega⟩ * (if j = ⟨n - 2, by omega⟩ then 1 else 0) +
        c ⟨n - 1, by omega⟩ * (if j = ⟨n - 1, by omega⟩ then 1 else 0) := by
  simp only [typeDSimpleCombination, typeDSimpleRoot, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  calc
    _ = ∑ i : Fin n,
        ((if h : (i : ℕ) + 1 < n then
            c i * (if j = i then 1 else 0) else 0) -
          (if h : (i : ℕ) + 1 < n then
            c i * (if j = (⟨(i : ℕ) + 1, h⟩ : Fin n) then 1 else 0) else 0) +
          (if (i : ℕ) + 1 < n then 0 else c i) *
            (if j = ⟨n - 2, by omega⟩ then 1 else 0) +
          (if (i : ℕ) + 1 < n then 0 else c i) *
            (if j = ⟨n - 1, by omega⟩ then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all [Pi.single_apply, Fin.ext_iff]
      all_goals ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        typeDChainHeadSum, typeDChainTailSum]
      rw [← Finset.sum_mul, typeDForkSum (by omega)]
      rw [← Finset.sum_mul, typeDForkSum (by omega)]

/-! ## Reflections of the concrete roots -/

/-- Reflection of a type `Dₙ` root `v` in the root `u`. -/
def typeDRootReflection (u v : TypeDRoot n) : TypeDRoot n :=
  ⟨v.1 - (v.1 ⬝ᵥ u.1) • u.1, by
    have hu := u.2
    have hv := v.2
    have hsymm : u.1 ⬝ᵥ v.1 = v.1 ⬝ᵥ u.1 := dotProduct_comm _ _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hu, hv, hsymm]
    ring⟩

lemma typeDRootReflection_involutive (u : TypeDRoot n) :
    Function.Involutive (typeDRootReflection u) := by
  intro v
  have hpair : (v.1 - (v.1 ⬝ᵥ u.1) • u.1) ⬝ᵥ u.1 = -(v.1 ⬝ᵥ u.1) := by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, u.2]
    ring
  apply Subtype.ext
  simp only [typeDRootReflection, Subtype.coe_mk, hpair]
  module

/-- Reflection in a type `Dₙ` root, as an involutive permutation of all roots. -/
def typeDRootReflectionEquiv (u : TypeDRoot n) : TypeDRoot n ≃ TypeDRoot n :=
  ⟨typeDRootReflection u, typeDRootReflection u, typeDRootReflection_involutive u,
    typeDRootReflection_involutive u⟩

private lemma sum_Iic_eq_sum_Iic_pred_add (x : Fin n → ℤ) (j : Fin n)
    (hj : (j : ℕ) ≠ 0) :
    ∑ i ∈ Finset.Iic j, x i =
      (∑ i ∈ Finset.Iic (⟨(j : ℕ) - 1, by omega⟩ : Fin n), x i) + x j := by
  have hset : Finset.Iic j =
      insert j (Finset.Iic (⟨(j : ℕ) - 1, by omega⟩ : Fin n)) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def]
    omega
  rw [hset]
  rw [Finset.sum_insert]
  · abel
  · simp only [Finset.mem_Iic, Fin.le_def]
    omega

/-- Every type `Dₙ` root is the indicated integral combination of the Bourbaki simple roots. -/
theorem sum_smul_typeDSimpleRootCoordinates (hn : 4 ≤ n) (x : TypeDRoot n) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n (by omega) x i •
      typeDSimpleRoot n (by omega) i = x.1 := by
  change typeDSimpleCombination n (by omega) (typeDSimpleRootCoordinates n (by omega) x) = x.1
  funext j
  rw [typeDSimpleCombination_apply]
  by_cases hj₀ : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hj₀
    have h₁ : 1 < n := by omega
    have h₂ : 2 < n := by omega
    have hn₂ : (0 : ℕ) ≠ n - 2 := by omega
    have hn₁ : (0 : ℕ) ≠ n - 1 := by omega
    rw [hj]
    have hIic : Finset.Iic (⟨0, by omega⟩ : Fin n) =
        {(⟨0, by omega⟩ : Fin n)} := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    simp (disch := omega) [typeDSimpleRootCoordinates, hIic, h₁, h₂, hn₂, hn₁,
      Fin.ext_iff]
  by_cases hj : (j : ℕ) + 2 < n
  · have hj₁ : (j : ℕ) + 1 < n := by omega
    have hpred : (j : ℕ) - 1 + 2 < n := by omega
    rw [if_pos hj₁, dif_neg hj₀]
    simp only [typeDSimpleRootCoordinates]
    rw [if_pos hj, if_pos hpred]
    rw [sum_Iic_eq_sum_Iic_pred_add x.1 j hj₀]
    have hjfork₁ : j ≠ (⟨n - 2, by omega⟩ : Fin n) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hjfork₂ : j ≠ (⟨n - 1, by omega⟩ : Fin n) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [hjfork₁, hjfork₂]
  · by_cases hj₁ : (j : ℕ) + 1 < n
    · have hjval : (j : ℕ) = n - 2 := by omega
      have hjEq : j = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hjval
      have hpred : (j : ℕ) - 1 + 2 < n := by omega
      rw [if_pos hj₁, dif_neg hj₀]
      simp only [typeDSimpleRootCoordinates]
      rw [if_neg hj, if_pos hj₁, if_pos hpred]
      have hlast : (∑ i : Fin n, x.1 i) =
          (∑ i ∈ Finset.Iic (⟨n - 2, by omega⟩ : Fin n), x.1 i) +
            x.1 ⟨n - 1, by omega⟩ := by
        have h := sum_Iic_eq_sum_Iic_pred_add x.1 (⟨n - 1, by omega⟩ : Fin n)
          (by simp; omega)
        have hIic : Finset.Iic (⟨n - 1, by omega⟩ : Fin n) = Finset.univ := by
          ext i
          simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
          omega
        have hprev : (⟨n - 1 - 1, by omega⟩ : Fin n) =
            (⟨n - 2, by omega⟩ : Fin n) := by
          apply Fin.ext
          simp only
          omega
        rw [hIic, hprev] at h
        exact h
      have hprefix := sum_Iic_eq_sum_Iic_pred_add x.1
        (⟨n - 2, by omega⟩ : Fin n) (by simp; omega)
      have hlast₂ : ¬(n - 1 + 2 < n) := by omega
      rw [← two_mul_typeDHalfTotal x] at hlast
      rw [hprefix] at hlast
      have hindex :
          (⟨((⟨n - 2, by omega⟩ : Fin n) : ℕ) - 1, by omega⟩ : Fin n) =
            (⟨n - 2 - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        rfl
      rw [hindex] at hlast
      (simp (disch := omega) [hjEq, hlast₂, Fin.ext_iff]; omega)
    · have hjval : (j : ℕ) = n - 1 := by omega
      have hjEq : j = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hjval
      have hpred₁ : (j : ℕ) - 1 + 1 < n := by omega
      have hpred₂ : ¬((j : ℕ) - 1 + 2 < n) := by omega
      have hlast₂ : ¬(n - 1 + 2 < n) := by omega
      have hliteral : ¬(n - 1 - 1 + 2 < n) := by omega
      have hnpos : 0 < n := by omega
      have hforkne : n - 1 ≠ n - 2 := by omega
      rw [if_neg hj₁, dif_neg hj₀]
      rw [hjEq]
      simp (disch := omega) [typeDSimpleRootCoordinates, hlast₂, hliteral, hnpos,
        hforkne, Fin.ext_iff]

end DynkinType

end TauCeti
