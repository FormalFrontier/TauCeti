/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.LinearAlgebra.Matrix.Gram

public section

/-!
# The classical integral roots of type `Dₙ`

This file constructs the classical integral root set of type `Dₙ` and gives the concrete
infrastructure needed to build its pinned integral root datum. The squared-length-two root type and
its reflection API are rank-polymorphic. The enumeration and Bourbaki simple-root APIs require
`4 ≤ n`, the rank range on which `TauCeti.DynkinType.Valid` admits `D n`: the smaller ranks name no
type of the classification, `D 2` being reducible and `D 3` being `A 3`.

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
* `TauCeti.DynkinType.typeDSimpleRoot` gives the Bourbaki-numbered simple roots, computed by
  `TauCeti.DynkinType.typeDSimpleRoot_of_add_one_lt` on the chain and by
  `TauCeti.DynkinType.typeDSimpleRoot_of_not_add_one_lt` at the fork.
* `TauCeti.DynkinType.sum_smul_typeDSimpleRootCoordinates` expands every root in that basis, and
  `TauCeti.DynkinType.typeDSimpleRootCoordinates_nonneg_or_nonpos` says the expansion has
  coefficients of one sign.
* `TauCeti.DynkinType.linearIndependent_typeDSimpleRoot` says that basis is linearly independent.
* `TauCeti.DynkinType.typeDRootReflectionEquiv` is reflection in a root, acting on the coordinates
  by `TauCeti.DynkinType.typeDSimpleRootCoordinates_typeDRootReflection`.

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
  · simp only [typeDPairVector, ite_eq_left hlt]
    by_cases hi : i = p.val.1 <;> by_cases hj : i = p.val.2 <;>
      simp_all [Function.mem_support]
  · simp only [typeDPairVector, ite_eq_right hlt]
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

private lemma typeDRawRootEquiv_apply (r : TypeDRawIndex n) :
    typeDRawRootEquiv n r = typeDRawRoot r := rfl

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
    -- the inverse sends `q` to `(q.2, q.2 + typeDSucc q.1)`, so the goal left by `Prod.ext` is
    -- the displayed equation on second components only after unfolding that anonymous constructor
    change p.val.1 + typeDSucc (typeDDifference hn p) = p.val.2
    rw [hx]
    abel
  · intro q
    refine Prod.ext (Fin.ext ?_) rfl
    -- likewise `typeDDifference` of the constructed pair is by definition the displayed
    -- truncated subtraction of `Fin` values
    change ((q.2 + typeDSucc q.1 - q.2 : Fin n) : ℕ) - 1 = (q.1 : ℕ)
    simp [typeDSucc]

private def typeDPairFinEquiv (n : ℕ) (hn : 1 ≤ n) : TypeDPair n ≃ Fin (n * (n - 1)) :=
  (typeDPairEquiv n hn).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm (n - 1) n)))

private lemma typeDDifference_val (hn : 1 ≤ n) (p : TypeDPair n) :
    (typeDDifference hn p : ℕ) = ((p.val.2 - p.val.1 : Fin n) : ℕ) - 1 := rfl

/-- The numerical value of the pair enumeration: the source index runs fastest, the cyclic
difference of the pair slowest. -/
private lemma typeDPairFinEquiv_val (hn : 1 ≤ n) (p : TypeDPair n) :
    (typeDPairFinEquiv n hn p : ℕ) = (p.val.1 : ℕ) + n * (typeDDifference hn p : ℕ) := by
  simp [typeDPairFinEquiv, typeDPairEquiv, finProdFinEquiv]

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
noncomputable def typeDRootEquiv (n : ℕ) (hn : 4 ≤ n) :
    Fin (2 * n * (n - 1)) ≃ TypeDRoot n :=
  (typeDRawFinEquiv n (by omega)).symm.trans (typeDRawRootEquiv n)

private lemma typeDRootEquiv_apply (hn : 4 ≤ n) (k : Fin (2 * n * (n - 1))) :
    typeDRootEquiv n hn k = typeDRawRoot ((typeDRawFinEquiv n (by omega)).symm k) := rfl

/-- The `i`-th simple root occupies root index `i`. -/
def typeDSimpleIndex (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : Fin (2 * n * (n - 1)) :=
  ⟨i, lt_of_lt_of_le i.isLt (by
    have h : n ≤ n * (n - 1) := Nat.le_mul_of_pos_right n (by omega)
    have h' : n * (n - 1) ≤ 2 * (n * (n - 1)) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    simpa [mul_assoc] using h.trans h')⟩

@[simp] lemma typeDSimpleIndex_val (hn : 4 ≤ n) (i : Fin n) :
    (typeDSimpleIndex n hn i : ℕ) = i := (rfl)

lemma typeDSimpleIndex_injective (hn : 4 ≤ n) : Injective (typeDSimpleIndex n hn) := by
  intro i j h
  exact Fin.ext (by simpa using congrArg Fin.val h)

private def typeDSimpleRawIndex (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : TypeDRawIndex n :=
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
  rw [typeDPairFinEquiv_val, typeDDifference_val]
  have hdiff : (((⟨(i : ℕ) + 1, hi⟩ : Fin n) - i : Fin n) : ℕ) = 1 := by
    have heq : n - (i : ℕ) + ((i : ℕ) + 1) = n + 1 := by omega
    simp only [Fin.sub_def, heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < n)]
  simp [hdiff]

private lemma typeDPairFinEquiv_fork (hn : 2 ≤ n) :
    typeDPairFinEquiv n (by omega)
        ⟨(⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩), by simp [Fin.ext_iff]; omega⟩ =
      typeDForkOldIndex n hn := by
  apply Fin.ext
  rw [typeDPairFinEquiv_val, typeDDifference_val]
  have hdiff : (((⟨n - 2, by omega⟩ : Fin n) - ⟨n - 1, by omega⟩ : Fin n) : ℕ) = n - 1 := by
    have heq : n - (n - 1) + (n - 2) = n - 1 := by omega
    simp only [Fin.sub_def, heq, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  rw [hdiff]
  have hprev : n - 1 - 1 = n - 2 := by omega
  rw [hprev]
  -- both sides are `Fin.val` of explicit numerals, so this only strips the wrappers
  change n - 1 + n * (n - 2) = n * (n - 1) - 1
  have hmul : n * (n - 1) = n + n * (n - 2) := by
    have hpred : n - 1 = (n - 2) + 1 := by omega
    conv_lhs => rw [hpred]
    ring
  rw [hmul]
  omega

private lemma typeDRawFinEquiv_simple (hn : 4 ≤ n) (i : Fin n) :
    typeDRawFinEquiv n (by omega) (typeDSimpleRawIndex n hn i) = typeDSimpleIndex n hn i := by
  by_cases hi : (i : ℕ) + 1 < n
  · have hraw : typeDSimpleRawIndex n hn i =
        (0, ⟨(i, ⟨(i : ℕ) + 1, hi⟩), by simp [Fin.ext_iff]⟩) := by
      simp [typeDSimpleRawIndex, hi]
    rw [hraw]
    apply Fin.ext
    simp only [typeDRawFinEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, typeDBourbakiPairEquiv, Equiv.trans_apply, Prod.map_apply]
    rw [typeDPairFinEquiv_chain (by omega) i hi]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · rfl
    · intro h
      have := congrArg Fin.val h
      simp [typeDChainEndIndex] at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp [typeDForkOldIndex] at this
      have hlt := lt_mul_of_one_lt_left (by omega : 0 < n - 1) (by omega : 1 < n)
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
    rw [typeDPairFinEquiv_fork (by omega), Equiv.swap_apply_right]
    simp [finProdFinEquiv, typeDChainEndIndex, typeDSimpleIndex, hieq]

private lemma typeDRootEquiv_simple (hn : 4 ≤ n) (i : Fin n) :
    typeDRootEquiv n hn (typeDSimpleIndex n hn i) =
      typeDRawRoot (typeDSimpleRawIndex n hn i) := by
  rw [typeDRootEquiv_apply]
  congr 1
  apply (typeDRawFinEquiv n (by omega)).injective
  rw [Equiv.apply_symm_apply, typeDRawFinEquiv_simple]

/-! ## The pinned lattices -/

/-- The Bourbaki-numbered simple roots of type `Dₙ` in classical orthogonal coordinates. -/
def typeDSimpleRoot (n : ℕ) (hn : 4 ≤ n) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then
    Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1
  else
    Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1

/-- The chain simple roots of type `Dₙ`, the `Fin`-indices `0` to `n - 2`: the `i`-th one is
`e_i - e_{i+1}`. Here and below both the simple roots and the coordinates `e_j` are indexed from
zero, so `Fin`-index `i` is Bourbaki node `i + 1`. -/
@[simp] theorem typeDSimpleRoot_of_add_one_lt (hn : 4 ≤ n) {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeDSimpleRoot n hn i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The fork simple root of type `Dₙ`, the `Fin`-index `n - 1` and so Bourbaki node `n`: in the
zero-based coordinates it is `e_{n-2} + e_{n-1}`, the only simple root that is not a difference of
two coordinates. -/
@[simp] theorem typeDSimpleRoot_of_not_add_one_lt (hn : 4 ≤ n) {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    typeDSimpleRoot n hn i =
      Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single ⟨n - 1, by omega⟩ 1 :=
  dite_eq_right hi

/-- The first `n` entries of `typeDRootEquiv` are the Bourbaki-numbered simple roots. -/
@[simp] theorem typeDRootEquiv_apply_typeDSimpleIndex (hn : 4 ≤ n) (i : Fin n) :
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
  have hx : typeDRawRoot r = x :=
    (typeDRawRootEquiv_apply r).symm.trans (Equiv.apply_symm_apply _ x)
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
def typeDSimpleRootCoordinates (n : ℕ) (hn : 4 ≤ n) (x : TypeDRoot n) : Fin n → ℤ := fun k =>
  if (k : ℕ) + 2 < n then ∑ j ∈ Finset.Iic k, x.1 j
  else if (k : ℕ) + 1 < n then typeDHalfTotal x - x.1 ⟨n - 1, by omega⟩
  else typeDHalfTotal x

/-- The coordinates of the `i`-th simple root are the `i`-th standard basis vector. -/
@[simp] theorem typeDSimpleRootCoordinates_typeDRootEquiv_apply_typeDSimpleIndex
    (hn : 4 ≤ n) (i : Fin n) :
    typeDSimpleRootCoordinates n hn (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) =
      Pi.single i 1 := by
  funext k
  rw [typeDSimpleRootCoordinates]
  simp only [typeDRootEquiv_apply_typeDSimpleIndex]
  by_cases hi : (i : ℕ) + 1 < n
  · have htotal : ∑ j : Fin n, typeDSimpleRoot n hn i j = 0 := by
      rw [typeDSimpleRoot, dite_eq_left hi]
      simp_rw [Pi.sub_apply]
      rw [Finset.sum_sub_distrib, Fintype.sum_pi_single', Fintype.sum_pi_single']
      omega
    have hhalf : typeDHalfTotal
        (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) = 0 := by
      simp only [typeDHalfTotal, typeDRootEquiv_apply_typeDSimpleIndex, htotal]
      norm_num
    by_cases hk₂ : (k : ℕ) + 2 < n
    · rw [ite_eq_left hk₂]
      rw [typeDSimpleRoot, dite_eq_left hi]
      simp_rw [Pi.sub_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
      simp only [Finset.mem_Iic, Fin.le_def, Pi.single_apply]
      split_ifs <;> omega
    · by_cases hk₁ : (k : ℕ) + 1 < n
      · rw [ite_eq_right hk₂, ite_eq_left hk₁]
        rw [hhalf]
        simp (disch := omega) [typeDSimpleRoot, hi, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> omega
      · rw [ite_eq_right hk₂, ite_eq_right hk₁]
        rw [hhalf]
        simp only [Pi.single_apply]
        omega
  · have hiv : (i : ℕ) = n - 1 := by omega
    have htotal : ∑ j : Fin n, typeDSimpleRoot n hn i j = 2 := by
      rw [typeDSimpleRoot, dite_eq_right hi]
      simp_rw [Pi.add_apply]
      rw [Finset.sum_add_distrib, Fintype.sum_pi_single', Fintype.sum_pi_single']
      norm_num
    have hhalf : typeDHalfTotal
        (typeDRootEquiv n hn (typeDSimpleIndex n hn i)) = 1 := by
      simp only [typeDHalfTotal, typeDRootEquiv_apply_typeDSimpleIndex, htotal]
      norm_num
    by_cases hk₂ : (k : ℕ) + 2 < n
    · rw [ite_eq_left hk₂]
      rw [typeDSimpleRoot, dite_eq_right hi]
      simp_rw [Pi.add_apply]
      rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
      simp only [Finset.mem_Iic, Fin.le_def, Pi.single_apply]
      split_ifs <;> omega
    · by_cases hk₁ : (k : ℕ) + 1 < n
      · rw [ite_eq_right hk₂, ite_eq_left hk₁]
        rw [hhalf]
        simp (disch := omega) [typeDSimpleRoot, Pi.add_apply, Pi.single_apply, Fin.ext_iff, hiv]
        omega
      · rw [ite_eq_right hk₂, ite_eq_right hk₁]
        rw [hhalf]
        have hkv : (k : ℕ) = n - 1 := by omega
        simp [Pi.single_apply, Fin.ext_iff, hiv, hkv]

private lemma typeDChainHeadSum (c : Fin n → ℤ) (j : Fin n) :
    (∑ i : Fin n, if _h : (i : ℕ) + 1 < n then
      c i * (if j = i then 1 else 0) else 0) =
      if (j : ℕ) + 1 < n then c j else 0 := by
  by_cases hj : (j : ℕ) + 1 < n
  · rw [ite_eq_left hj, Fintype.sum_eq_single j]
    · simp [hj]
    · intro i hi
      simp [Ne.symm hi]
  · rw [ite_eq_right hj, Finset.sum_eq_zero]
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
  · rw [dite_eq_left hj, Finset.sum_eq_zero]
    intro i _
    split_ifs with h hi
    · have hv := congrArg Fin.val hi
      simp at hv
      omega
    · simp
    · rfl
  · rw [dite_eq_right hj, Fintype.sum_eq_single (⟨(j : ℕ) - 1, by omega⟩ : Fin n)]
    · have h : (j : ℕ) - 1 + 1 < n := by omega
      simp only [dite_eq_left h, Fin.ext_iff]
      rw [ite_eq_left (by omega)]
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
  · rw [ite_eq_right (by simp only; omega)]
  · intro i hi
    split_ifs with h
    · rfl
    · exfalso
      apply hi
      apply Fin.ext
      simp only
      omega

/-- The coordinate `j` of an integral combination of the Bourbaki simple roots: the chain roots
contribute a telescoping pair, and the fork root contributes at the two nodes `n - 2` and
`n - 1`. -/
private lemma sum_smul_typeDSimpleRoot_apply (hn : 4 ≤ n) (c : Fin n → ℤ) (j : Fin n) :
    (∑ i : Fin n, c i • typeDSimpleRoot n hn i) j =
      (if (j : ℕ) + 1 < n then c j else 0) -
        (if hj : (j : ℕ) = 0 then 0 else c ⟨(j : ℕ) - 1, by omega⟩) +
        c ⟨n - 1, by omega⟩ * (if j = ⟨n - 2, by omega⟩ then 1 else 0) +
        c ⟨n - 1, by omega⟩ * (if j = ⟨n - 1, by omega⟩ then 1 else 0) := by
  simp only [typeDSimpleRoot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
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

private lemma typeDDot_apply_self (u : TypeDRoot n) :
    dotProductBilin ℤ ℤ u.1 u.1 = 2 := u.2

/-- Reflection in a type `Dₙ` root, as a linear equivalence of the ambient coordinate space:
Mathlib's `Module.reflection` for the dot-product form of `u`. -/
private def typeDAmbientReflection (u : TypeDRoot n) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  Module.reflection (typeDDot_apply_self u)

private lemma typeDAmbientReflection_apply (u : TypeDRoot n) (v : Fin n → ℤ) :
    typeDAmbientReflection u v = v - (v ⬝ᵥ u.1) • u.1 := by
  rw [typeDAmbientReflection, Module.reflection_apply, dotProduct_comm]
  rfl

private lemma typeDAmbientReflection_dotProduct_self (u : TypeDRoot n) {v : Fin n → ℤ}
    (hv : v ⬝ᵥ v = 2) : typeDAmbientReflection u v ⬝ᵥ typeDAmbientReflection u v = 2 := by
  have h := reflect_vecMul_dotProduct_self Matrix.isSymm_one (u := u.1) (by simpa using u.2) v
  simpa [typeDAmbientReflection_apply, Matrix.one_vecMul, hv] using h

/-- Reflection of a type `Dₙ` root `v` in the root `u`. -/
def typeDRootReflection (u v : TypeDRoot n) : TypeDRoot n :=
  ⟨typeDAmbientReflection u v.1, typeDAmbientReflection_dotProduct_self u v.2⟩

/-- Reflection in a root acts by the classical formula on coordinates. -/
@[simp] lemma typeDRootReflection_val (u v : TypeDRoot n) :
    (typeDRootReflection u v).1 = v.1 - (v.1 ⬝ᵥ u.1) • u.1 :=
  typeDAmbientReflection_apply u v.1

/-- Reflection in a type `Dₙ` root is involutive. -/
lemma typeDRootReflection_involutive (u : TypeDRoot n) :
    Function.Involutive (typeDRootReflection u) := fun v =>
  Subtype.ext (Module.involutive_reflection (typeDDot_apply_self u) v.1)

/-- Reflection in a type `Dₙ` root, as an involutive permutation of all roots. -/
def typeDRootReflectionEquiv (u : TypeDRoot n) : TypeDRoot n ≃ TypeDRoot n :=
  (typeDRootReflection_involutive u).toPerm _

/-- The reflection equivalence acts by `typeDRootReflection`. -/
@[simp] lemma typeDRootReflectionEquiv_apply (u v : TypeDRoot n) :
    typeDRootReflectionEquiv u v = typeDRootReflection u v := by
  rw [typeDRootReflectionEquiv, Function.Involutive.coe_toPerm]

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

/-! ### Reconstruction, node by node

The reconstruction of a root from its coordinates is checked at one coordinate `j` at a time,
in the four cases distinguished by the shape of the Bourbaki diagram at `j`: the first node, an
interior node of the chain, the fork node `n - 2`, and the final node `n - 1`. -/

/-- At the first node only the head of the first chain root contributes. -/
private lemma sum_smul_typeDSimpleRootCoordinates_apply_zero (hn : 4 ≤ n) (x : TypeDRoot n)
    (j : Fin n) (hj₀ : (j : ℕ) = 0) :
    (∑ i : Fin n, typeDSimpleRootCoordinates n hn x i • typeDSimpleRoot n hn i) j = x.1 j := by
  rw [sum_smul_typeDSimpleRoot_apply]
  have hj : j = ⟨0, by omega⟩ := Fin.ext hj₀
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

/-- At an interior node of the chain the two neighbouring partial sums telescope. -/
private lemma sum_smul_typeDSimpleRootCoordinates_apply_chain (hn : 4 ≤ n) (x : TypeDRoot n)
    (j : Fin n) (hj₀ : (j : ℕ) ≠ 0) (hj : (j : ℕ) + 2 < n) :
    (∑ i : Fin n, typeDSimpleRootCoordinates n hn x i • typeDSimpleRoot n hn i) j = x.1 j := by
  rw [sum_smul_typeDSimpleRoot_apply]
  have hj₁ : (j : ℕ) + 1 < n := by omega
  have hpred : (j : ℕ) - 1 + 2 < n := by omega
  rw [ite_eq_left hj₁, dite_eq_right hj₀]
  simp only [typeDSimpleRootCoordinates]
  rw [ite_eq_left hj, ite_eq_left hpred]
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

/-- At the fork node `n - 2` the chain prefix and the fork root combine into half the total. -/
private lemma sum_smul_typeDSimpleRootCoordinates_apply_fork (hn : 4 ≤ n) (x : TypeDRoot n)
    (j : Fin n) (hj : ¬((j : ℕ) + 2 < n)) (hj₁ : (j : ℕ) + 1 < n) :
    (∑ i : Fin n, typeDSimpleRootCoordinates n hn x i • typeDSimpleRoot n hn i) j = x.1 j := by
  rw [sum_smul_typeDSimpleRoot_apply]
  have hj₀ : ¬((j : ℕ) = 0) := by omega
  have hjval : (j : ℕ) = n - 2 := by omega
  have hjEq : j = (⟨n - 2, by omega⟩ : Fin n) := Fin.ext hjval
  have hpred : (j : ℕ) - 1 + 2 < n := by omega
  rw [ite_eq_left hj₁, dite_eq_right hj₀]
  simp only [typeDSimpleRootCoordinates]
  rw [ite_eq_right hj, ite_eq_left hj₁, ite_eq_left hpred]
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

/-- At the final node `n - 1` only the fork root contributes, with half the total as coefficient. -/
private lemma sum_smul_typeDSimpleRootCoordinates_apply_last (hn : 4 ≤ n) (x : TypeDRoot n)
    (j : Fin n) (hj₁ : ¬((j : ℕ) + 1 < n)) :
    (∑ i : Fin n, typeDSimpleRootCoordinates n hn x i • typeDSimpleRoot n hn i) j = x.1 j := by
  rw [sum_smul_typeDSimpleRoot_apply]
  have hjlt := j.isLt
  have hj₀ : ¬((j : ℕ) = 0) := by omega
  have hjval : (j : ℕ) = n - 1 := by omega
  have hjEq : j = (⟨n - 1, by omega⟩ : Fin n) := Fin.ext hjval
  have hpred₁ : (j : ℕ) - 1 + 1 < n := by omega
  have hpred₂ : ¬((j : ℕ) - 1 + 2 < n) := by omega
  have hlast₂ : ¬(n - 1 + 2 < n) := by omega
  have hliteral : ¬(n - 1 - 1 + 2 < n) := by omega
  have hnpos : 0 < n := by omega
  have hforkne : n - 1 ≠ n - 2 := by omega
  rw [ite_eq_right hj₁, dite_eq_right hj₀]
  rw [hjEq]
  simp (disch := omega) [typeDSimpleRootCoordinates, hlast₂, hliteral, hnpos,
    hforkne, Fin.ext_iff]

/-- Every type `Dₙ` root is the indicated integral combination of the Bourbaki simple roots. -/
theorem sum_smul_typeDSimpleRootCoordinates (hn : 4 ≤ n) (x : TypeDRoot n) :
    ∑ i : Fin n, typeDSimpleRootCoordinates n hn x i • typeDSimpleRoot n hn i = x.1 := by
  funext j
  by_cases hj₀ : (j : ℕ) = 0
  · exact sum_smul_typeDSimpleRootCoordinates_apply_zero hn x j hj₀
  by_cases hj : (j : ℕ) + 2 < n
  · exact sum_smul_typeDSimpleRootCoordinates_apply_chain hn x j hj₀ hj
  by_cases hj₁ : (j : ℕ) + 1 < n
  · exact sum_smul_typeDSimpleRootCoordinates_apply_fork hn x j hj hj₁
  · exact sum_smul_typeDSimpleRootCoordinates_apply_last hn x j hj₁

/-! ## Positivity of the coordinates

Every classical root is a nonnegative or a nonpositive integral combination of the Bourbaki simple
roots. The four positive coordinate patterns are read off the two shapes of a positive root,
`e_a - e_b` and `e_a + e_b`, and the negative roots follow by negating. -/

private lemma typeDHalfTotal_of_eq_neg {x y : TypeDRoot n} (h : y.1 = -x.1) :
    typeDHalfTotal y = -typeDHalfTotal x := by
  have h2x := two_mul_typeDHalfTotal x
  have h2y := two_mul_typeDHalfTotal y
  have hs : ∑ i : Fin n, y.1 i = -∑ i : Fin n, x.1 i := by rw [h]; simp
  linarith

private lemma typeDSimpleRootCoordinates_of_eq_neg (hn : 4 ≤ n) {x y : TypeDRoot n}
    (h : y.1 = -x.1) (k : Fin n) :
    typeDSimpleRootCoordinates n hn y k = -typeDSimpleRootCoordinates n hn x k := by
  simp only [typeDSimpleRootCoordinates]
  split_ifs
  · rw [h]; simp
  · rw [typeDHalfTotal_of_eq_neg h, h]
    simp only [Pi.neg_apply]
    ring
  · exact typeDHalfTotal_of_eq_neg h

/-- A positive classical root, one of the two shapes `e_a - e_b` with `a < b` and `e_a + e_b`, has
nonnegative coordinates in the Bourbaki simple-root basis. -/
private lemma typeDSimpleRootCoordinates_nonneg_of_pairVector (hn : 4 ≤ n) (x : TypeDRoot n)
    (p : TypeDPair n) (hx : x.1 = typeDPairVector p) (k : Fin n) :
    0 ≤ typeDSimpleRootCoordinates n hn x k := by
  have hne : (p.val.1 : ℕ) ≠ (p.val.2 : ℕ) := fun h => p.property (Fin.ext h)
  have hb₁ := p.val.1.isLt
  have hb₂ := p.val.2.isLt
  by_cases hp : p.val.1 < p.val.2
  · have hplt : (p.val.1 : ℕ) < (p.val.2 : ℕ) := hp
    have hv : x.1 = Pi.single p.val.1 1 - Pi.single p.val.2 1 := by
      rw [hx, typeDPairVector, ite_eq_left hp]
    have htot : ∑ i : Fin n, x.1 i = 0 := by
      simp [hv, Finset.sum_sub_distrib]
    have hhalf : typeDHalfTotal x = 0 := by
      linarith [two_mul_typeDHalfTotal x, htot]
    simp only [typeDSimpleRootCoordinates]
    split_ifs
    · rw [hv]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_Iic,
        Fin.le_def]
      split_ifs <;> omega
    · rw [hhalf, hv]
      simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · exact le_of_eq hhalf.symm
  · have hv : x.1 = Pi.single p.val.2 1 + Pi.single p.val.1 1 := by
      rw [hx, typeDPairVector, ite_eq_right hp]
    have htot : ∑ i : Fin n, x.1 i = 2 := by
      simp [hv, Finset.sum_add_distrib]
    have hhalf : typeDHalfTotal x = 1 := by
      linarith [two_mul_typeDHalfTotal x, htot]
    simp only [typeDSimpleRootCoordinates]
    split_ifs
    · rw [hv]
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_Iic,
        Fin.le_def]
      split_ifs <;> omega
    · rw [hhalf, hv]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · simp [hhalf]

/-- **Every classical type `Dₙ` root is positive or negative.** Its coefficients in the
Bourbaki simple-root basis are either all nonnegative or all nonpositive, which is what makes the
first `n` root indices a base of the pinned root datum. -/
theorem typeDSimpleRootCoordinates_nonneg_or_nonpos (hn : 4 ≤ n) (x : TypeDRoot n) :
    (∀ k, 0 ≤ typeDSimpleRootCoordinates n hn x k) ∨
      (∀ k, typeDSimpleRootCoordinates n hn x k ≤ 0) := by
  obtain ⟨⟨s, p⟩, hx⟩ : ∃ r : TypeDRawIndex n, typeDRawRoot r = x :=
    ⟨(typeDRawRootEquiv n).symm x, by
      rw [← typeDRawRootEquiv_apply]; exact (typeDRawRootEquiv n).apply_symm_apply x⟩
  have hxv : x.1 = typeDRawVector (s, p) := (congrArg Subtype.val hx).symm
  by_cases hs : s = 0
  · exact Or.inl (typeDSimpleRootCoordinates_nonneg_of_pairVector hn x p
      (by rw [hxv, typeDRawVector, ite_eq_left hs]))
  · refine Or.inr fun k => ?_
    have hyv : (typeDRawRoot ((0 : Fin 2), p)).1 = typeDPairVector p := by
      simp [typeDRawRoot, typeDRawVector]
    have hneg : x.1 = -(typeDRawRoot ((0 : Fin 2), p)).1 := by
      rw [hyv, hxv, typeDRawVector, ite_eq_right hs]
    rw [typeDSimpleRootCoordinates_of_eq_neg hn hneg k, neg_nonpos]
    exact typeDSimpleRootCoordinates_nonneg_of_pairVector hn _ p hyv k

/-! ## The doubled fundamental coweights

The coefficients of a root in the Bourbaki simple-root basis are read off the classical vector by
pairing it against an explicit integral family, twice the fundamental coweights. Halving is
unavoidable — the last two fundamental coweights of type `Dₙ` are not integral vectors — and
doubling is harmless, since `ℤ` is torsion free. That one family does two jobs: it is a dual family
for the simple roots up to the factor two, which gives their linear independence, and it exhibits
the coefficient map as the restriction of a linear map, which gives the action of a reflection on
the coordinates. -/

/-- Twice the `k`-th fundamental coweight of type `Dₙ`, in classical orthogonal coordinates. The
last two fundamental coweights of type `Dₙ` are half-integral, so the doubling is what keeps this
family inside `ℤ ^ n`; over `ℤ` it is still enough to separate the simple roots. -/
private def typeDDoubleCoweight (n : ℕ) (k : Fin n) : Fin n → ℤ := fun j =>
  if (k : ℕ) + 2 < n then (if (j : ℕ) ≤ (k : ℕ) then 2 else 0)
  else if (k : ℕ) + 1 < n then (if (j : ℕ) + 1 = n then -1 else 1)
  else 1

/-- The doubled fundamental coweights are dual to the simple roots, up to the factor two. -/
private lemma typeDDoubleCoweight_dotProduct_typeDSimpleRoot (hn : 4 ≤ n) (k i : Fin n) :
    typeDDoubleCoweight n k ⬝ᵥ typeDSimpleRoot n hn i = if (k : ℕ) = (i : ℕ) then 2 else 0 := by
  have hk := k.isLt
  have hi' := i.isLt
  by_cases hi : (i : ℕ) + 1 < n
  · rw [typeDSimpleRoot_of_add_one_lt hn hi, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp only [typeDDoubleCoweight, mul_one]
    split_ifs <;> omega
  · rw [typeDSimpleRoot_of_not_add_one_lt hn hi, dotProduct_add, dotProduct_single,
      dotProduct_single]
    simp only [typeDDoubleCoweight, mul_one]
    split_ifs <;> omega

/-- Pairing an integral combination of the simple roots against a doubled fundamental coweight
isolates twice the corresponding coefficient. -/
private lemma typeDDoubleCoweight_dotProduct_sum_smul (hn : 4 ≤ n) (c : Fin n → ℤ) (k : Fin n) :
    typeDDoubleCoweight n k ⬝ᵥ ∑ i : Fin n, c i • typeDSimpleRoot n hn i = 2 * c k := by
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, typeDDoubleCoweight_dotProduct_typeDSimpleRoot,
    Fin.val_inj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The Bourbaki simple roots of type `Dₙ` are linearly independent.** Pairing a relation with a
doubled fundamental coweight isolates twice one coefficient, and `ℤ` is torsion free. -/
theorem linearIndependent_typeDSimpleRoot (hn : 4 ≤ n) :
    LinearIndependent ℤ (typeDSimpleRoot n hn) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h := typeDDoubleCoweight_dotProduct_sum_smul hn g k
  rw [hg, dotProduct_zero] at h
  omega

/-- Twice the coefficients of a root in the Bourbaki simple-root basis are the dot products with
the doubled fundamental coweights. -/
private lemma two_mul_typeDSimpleRootCoordinates (hn : 4 ≤ n) (x : TypeDRoot n) (k : Fin n) :
    2 * typeDSimpleRootCoordinates n hn x k = typeDDoubleCoweight n k ⬝ᵥ x.1 := by
  conv_rhs => rw [← sum_smul_typeDSimpleRootCoordinates hn x]
  rw [typeDDoubleCoweight_dotProduct_sum_smul]

/-- **Reflection acts on the simple-root coordinates by the classical formula.** Doubling the
coordinates turns them into dot products, which are linear, and `ℤ` is torsion free. -/
theorem typeDSimpleRootCoordinates_typeDRootReflection (hn : 4 ≤ n) (u v : TypeDRoot n) :
    typeDSimpleRootCoordinates n hn (typeDRootReflection u v) =
      typeDSimpleRootCoordinates n hn v - (v.1 ⬝ᵥ u.1) • typeDSimpleRootCoordinates n hn u := by
  funext k
  have h := two_mul_typeDSimpleRootCoordinates hn (typeDRootReflection u v) k
  rw [typeDRootReflection_val, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    ← two_mul_typeDSimpleRootCoordinates hn v k, ← two_mul_typeDSimpleRootCoordinates hn u k] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end DynkinType

end TauCeti
