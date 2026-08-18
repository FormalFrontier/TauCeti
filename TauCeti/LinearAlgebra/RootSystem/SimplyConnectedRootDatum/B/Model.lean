/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

/-!
# The pinned coordinate model of the roots of type `Bₙ`

This file records the roots of type `Bₙ` in the two lattices pinned by the Bourbaki numbering: the
character lattice `Fin n → ℤ` written in the fundamental-weight basis, and the cocharacter lattice
`Fin n → ℤ` written in the simple-coroot basis. It stops just short of assembling a `RootDatum`,
which is done in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum` once the roots
have been enumerated by `Fin (2 * n ^ 2)`.

## The coordinates

Write `e₀, …, e_{n-1}` for the standard basis of the classical model `ℤ ^ n`, in which the roots of
type `Bₙ` are the `2 * n ^ 2` vectors `± e_a ± e_b` (`a ≠ b`) and `± e_a`, the simple roots are
`αᵢ = eᵢ - eᵢ₊₁` for `i + 1 < n` and `α_{n-1} = e_{n-1}`, and the coroot of a root `α` is
`2 α / (α, α)`, so the long roots are self-dual while `(± e_a)^∨ = ± 2 e_a`. Everything below is the
image of that model in the two pinned lattices:

```text
weight n a   = (⟨e_a, αₖ^∨⟩)ₖ,          the character coordinates of `e_a`,
coweight n b = the simple-coroot coordinates of `2 e_b`.
```

The doubling in `coweight` is not a normalisation: `e_b` itself is a half-integral combination of
the simple coroots, because `α_{n-1}^∨ = 2 e_{n-1}`, while `2 e_b` is integral. The single identity
`TauCeti.DynkinType.TypeB.weight_dotProduct_coweight`, that the two families pair to `2 * [a = b]`,
is what the rest of the file computes with.

## Signed basis vectors and the pairs naming a root

A root is a sum of one or two signed basis vectors on distinct axes, so `Fin (2 * n)` indexes the
signed basis vectors, `u < n` standing for `e_u` and `u ≥ n` for `-e_{u-n}`, and a root is named by
an unordered pair `{u, v}`, with `u = v` for a short root. Two devices make this uniform.

The cyclic offset `TauCeti.DynkinType.TypeB.shift` turns the unordered pair into the ordered datum
`(u, d) : Fin (2 * n) × Fin n`. For a distinct admissible pair, exactly one of the two orders has
its offset in the range `Fin n`; a short root uses the coincident order with offset zero. This is
the index type the datum is built on, and `TauCeti.DynkinType.TypeB.index` is the inverse
normalisation.

The coroot is *uniform* in the pair while the root is not:
`TauCeti.DynkinType.TypeB.corootOfPair` computes
the simple-coroot coordinates of the coroot from the pair, and specialises to the short coroot when
the two entries agree, since `(e_a)^∨ = 2 e_a = e_a + e_a`. It is a genuine half, and the integral
identity `TauCeti.DynkinType.TypeB.corootOfPair_add_self` is how the reflection identity for
coroots is proved.

## Main definitions

* `TauCeti.DynkinType.TypeB.signedWeight` and `TauCeti.DynkinType.TypeB.signedCoweight`: the
  coordinates of a signed basis vector and of its double.
* `TauCeti.DynkinType.TypeB.rootOfPair` and `TauCeti.DynkinType.TypeB.corootOfPair`: the root and
  coroot named by a pair of signed basis vectors.
* `TauCeti.DynkinType.TypeB.reflMap`: the signed permutation realising the reflection in a root.

The coordinate definitions are used through their defining and case-characterization lemmas below;
their bodies are not exposed to importing modules.

## Main results

* `TauCeti.DynkinType.TypeB.signedWeight_reflMap` and
  `TauCeti.DynkinType.TypeB.signedCoweight_reflMap`: the reflection
  formulas on a single signed basis vector, from which the root-datum axioms follow additively.
* `TauCeti.DynkinType.TypeB.index_eq_of_pair_mem_iff`: an index is recovered from its unordered
  signed-vector pair.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate II, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is part of the `Bₙ` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.
-/

namespace TauCeti.DynkinType.TypeB

variable {n : ℕ}

/-! ## The two coordinate families -/

/-- The character-lattice coordinates of the classical basis vector `e_a` of type `Bₙ`, namely its
pairings `⟨e_a, αₖ^∨⟩` against the simple coroots. The last simple coroot is `2 e_{n-1}`, which is
why the diagonal entry doubles there. The value is `0` for `n ≤ a`, where there is no basis
vector. -/
def weight (n a : ℕ) : Fin n → ℤ := fun k =>
  (if a = (k : ℕ) then (if (k : ℕ) + 1 = n then 2 else 1) else 0) -
    (if a = (k : ℕ) + 1 ∧ (k : ℕ) + 1 < n then 1 else 0)
@[simp] lemma weight_apply (n a : ℕ) (k : Fin n) : weight n a k =
    (if a = (k : ℕ) then (if (k : ℕ) + 1 = n then 2 else 1) else 0) -
      (if a = (k : ℕ) + 1 ∧ (k : ℕ) + 1 < n then 1 else 0) := (rfl)

/-- The cocharacter-lattice coordinates of `2 e_b`, that is, its coordinates in the simple coroots
`αₖ^∨ = e_k - e_{k+1}` and `α_{n-1}^∨ = 2 e_{n-1}`. The vector `e_b` alone is half-integral in that
basis, so it is its double that is recorded. -/
def coweight (n b : ℕ) : Fin n → ℤ := fun k =>
  (if (k : ℕ) + 1 = n then 1 else 2) * (if b ≤ (k : ℕ) then 1 else 0)
@[simp] lemma coweight_apply (n b : ℕ) (k : Fin n) : coweight n b k =
    (if (k : ℕ) + 1 = n then 1 else 2) * (if b ≤ (k : ℕ) then 1 else 0) := (rfl)

@[simp] lemma weight_eq_zero_of_le {a : ℕ} (ha : n ≤ a) : weight n a = 0 := by
  funext k
  have := k.isLt
  simp only [weight, Pi.zero_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  ring

@[simp] lemma coweight_eq_zero_of_le {b : ℕ} (hb : n ≤ b) : coweight n b = 0 := by
  funext k
  have := k.isLt
  simp only [coweight, Pi.zero_apply]
  rw [ite_eq_right (show ¬ b ≤ (k : ℕ) by omega), mul_zero]

/-- **The fundamental pairing identity of type `Bₙ`.** In the classical model `⟨e_a, 2 e_b⟩` is
`2 * [a = b]`, and the two pinned lattices see exactly that. -/
lemma weight_dotProduct_coweight {a b : ℕ} (ha : a < n) :
    weight n a ⬝ᵥ coweight n b = if a = b then 2 else 0 := by
  have step : weight n a ⬝ᵥ coweight n b =
      ∑ m ∈ Finset.range n,
        ((if a = m then (if m + 1 = n then (2 : ℤ) else 1) *
            ((if m + 1 = n then 1 else 2) * (if b ≤ m then 1 else 0)) else 0) -
          (if a = m + 1 ∧ m + 1 < n then
            (if m + 1 = n then (1 : ℤ) else 2) * (if b ≤ m then 1 else 0) else 0)) := by
    rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun m =>
      ((if a = m then (if m + 1 = n then (2 : ℤ) else 1) *
          ((if m + 1 = n then 1 else 2) * (if b ≤ m then 1 else 0)) else 0) -
        (if a = m + 1 ∧ m + 1 < n then
          (if m + 1 = n then (1 : ℤ) else 2) * (if b ≤ m then 1 else 0) else 0))) n]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [weight, coweight]
    split_ifs <;> ring
  have h1 : ∑ m ∈ Finset.range n,
      (if a = m then (if m + 1 = n then (2 : ℤ) else 1) *
        ((if m + 1 = n then 1 else 2) * (if b ≤ m then 1 else 0)) else 0)
      = 2 * (if b ≤ a then 1 else 0) := by
    rw [Finset.sum_eq_single a (fun m _ hm => ite_eq_right (Ne.symm hm))
      (fun hm => absurd (Finset.mem_range.mpr ha) hm), ite_eq_left rfl]
    split_ifs <;> ring
  have h2 : ∑ m ∈ Finset.range n,
      (if a = m + 1 ∧ m + 1 < n then
        (if m + 1 = n then (1 : ℤ) else 2) * (if b ≤ m then 1 else 0) else 0)
      = if a = 0 then 0 else 2 * (if b ≤ a - 1 then 1 else 0) := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [ite_eq_left rfl]
      exact Finset.sum_eq_zero fun m _ => ite_eq_right (by omega)
    · rw [ite_eq_right (by omega),
        Finset.sum_eq_single (a - 1) (fun m _ hm => ite_eq_right (by omega))
          (fun hm => absurd (Finset.mem_range.mpr (by omega)) hm),
        ite_eq_left ⟨by omega, by omega⟩, ite_eq_right (show ¬(a - 1 + 1 = n) by omega)]
  rw [step, Finset.sum_sub_distrib, h1, h2]
  split_ifs <;> omega

/-! ## Signed basis vectors -/

/-- The axis of the signed basis vector indexed by `u`, which stands for `e_u` when `u < n` and for
`-e_{u-n}` otherwise. -/
def axis (u : Fin (2 * n)) : ℕ := if (u : ℕ) < n then (u : ℕ) else (u : ℕ) - n
lemma axis_def (u : Fin (2 * n)) : axis u = if (u : ℕ) < n then (u : ℕ) else (u : ℕ) - n := (rfl)

/-- The sign of the signed basis vector indexed by `u`. -/
def sgn (u : Fin (2 * n)) : ℤ := if (u : ℕ) < n then 1 else -1
lemma sgn_def (u : Fin (2 * n)) : sgn u = if (u : ℕ) < n then 1 else -1 := (rfl)

/-- The index of the opposite signed basis vector. -/
def opp (u : Fin (2 * n)) : Fin (2 * n) :=
  ⟨if (u : ℕ) < n then (u : ℕ) + n else (u : ℕ) - n, by have := u.isLt; split <;> omega⟩

private lemma rank_pos (u : Fin (2 * n)) : 0 < n := by have := u.isLt; omega

lemma axis_lt (u : Fin (2 * n)) : axis u < n := by
  have := u.isLt; simp only [axis]; split <;> omega

lemma sgn_eq_one_or_neg_one (u : Fin (2 * n)) : sgn u = 1 ∨ sgn u = -1 := by
  simp only [sgn]; split <;> simp

lemma coe_opp (u : Fin (2 * n)) :
    ((opp u : Fin (2 * n)) : ℕ) = if (u : ℕ) < n then (u : ℕ) + n else (u : ℕ) - n := (rfl)

@[simp] lemma axis_opp (u : Fin (2 * n)) : axis (opp u) = axis u := by
  have := u.isLt
  simp only [axis, coe_opp]
  split_ifs <;> omega

@[simp] lemma sgn_opp (u : Fin (2 * n)) : sgn (opp u) = -sgn u := by
  have := u.isLt
  simp only [sgn, coe_opp]
  split_ifs <;> omega

@[simp] lemma opp_opp (u : Fin (2 * n)) : opp (opp u) = u := by
  have := u.isLt
  refine Fin.ext ?_
  simp only [coe_opp]
  split_ifs <;> omega

lemma opp_ne_self (u : Fin (2 * n)) : opp u ≠ u := by
  have := u.isLt
  intro h
  have := congrArg Fin.val h
  rw [coe_opp] at this
  split_ifs at this <;> omega

lemma eq_or_eq_opp_of_axis_eq {u v : Fin (2 * n)} (h : axis u = axis v) : u = v ∨ u = opp v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [axis] at h
  split_ifs at h with h1 h2 h2
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr (Fin.ext (by rw [coe_opp, ite_eq_right h2]; omega))
  · exact Or.inr (Fin.ext (by rw [coe_opp, ite_eq_left h2]; omega))
  · exact Or.inl (Fin.ext (by omega))

lemma ne_of_axis_ne {u v : Fin (2 * n)} (h : axis u ≠ axis v) : u ≠ v := fun hc => h (by rw [hc])

/-- The character coordinates of the signed basis vector indexed by `u`. -/
def signedWeight (u : Fin (2 * n)) : Fin n → ℤ := sgn u • weight n (axis u)
lemma signedWeight_def (u : Fin (2 * n)) : signedWeight u = sgn u • weight n (axis u) := (rfl)

/-- The cocharacter coordinates of twice the signed basis vector indexed by `u`. -/
def signedCoweight (u : Fin (2 * n)) : Fin n → ℤ := sgn u • coweight n (axis u)
lemma signedCoweight_def (u : Fin (2 * n)) :
    signedCoweight u = sgn u • coweight n (axis u) := (rfl)

@[simp] lemma signedWeight_opp (u : Fin (2 * n)) : signedWeight (opp u) = -signedWeight u := by
  simp only [signedWeight, sgn_opp, axis_opp, neg_smul]

@[simp] lemma signedCoweight_opp (u : Fin (2 * n)) :
    signedCoweight (opp u) = -signedCoweight u := by
  simp only [signedCoweight, sgn_opp, axis_opp, neg_smul]

/-- The pairing of two signed basis vectors: `2` on the diagonal, `-2` on opposite vectors, and `0`
on different axes. -/
lemma signedWeight_dotProduct_signedCoweight (u v : Fin (2 * n)) :
    signedWeight u ⬝ᵥ signedCoweight v = if u = v then 2 else if u = opp v then -2 else 0 := by
  have h := weight_dotProduct_coweight (n := n) (a := axis u) (b := axis v) (axis_lt u)
  simp only [signedWeight, signedCoweight, smul_dotProduct, dotProduct_smul, smul_eq_mul, h]
  by_cases hax : axis u = axis v
  · rw [ite_eq_left hax]
    rcases eq_or_eq_opp_of_axis_eq hax with rfl | rfl
    · rw [ite_eq_left rfl]
      rcases sgn_eq_one_or_neg_one u with hs | hs <;> rw [hs] <;> norm_num
    · rw [ite_eq_right (opp_ne_self v), ite_eq_left rfl, sgn_opp]
      rcases sgn_eq_one_or_neg_one v with hs | hs <;> rw [hs] <;> norm_num
  · rw [ite_eq_right hax, ite_eq_right (ne_of_axis_ne hax),
      ite_eq_right (ne_of_axis_ne (by rwa [axis_opp]))]
    ring

@[simp] lemma signedWeight_dotProduct_self (u : Fin (2 * n)) :
    signedWeight u ⬝ᵥ signedCoweight u = 2 := by
  rw [signedWeight_dotProduct_signedCoweight, ite_eq_left rfl]

lemma signedWeight_dotProduct_eq_zero {u v : Fin (2 * n)} (h1 : u ≠ v) (h2 : u ≠ opp v) :
    signedWeight u ⬝ᵥ signedCoweight v = 0 := by
  rw [signedWeight_dotProduct_signedCoweight, ite_eq_right h1, ite_eq_right h2]

lemma signedWeight_dotProduct_of_axis_ne {u v : Fin (2 * n)} (h : axis u ≠ axis v) :
    signedWeight u ⬝ᵥ signedCoweight v = 0 :=
  signedWeight_dotProduct_eq_zero (ne_of_axis_ne h) (ne_of_axis_ne (by rwa [axis_opp]))

/-! ## The coroot attached to a pair of signed basis vectors -/

/-- The simple-coroot coordinates of the coroot named by the pair `{u, v}`: the half of
`signedCoweight u + signedCoweight v`, which is integral. When `u = v` this is the short coroot
`signedCoweight u`, and otherwise it is the long coroot `± e_a ± e_b` itself. -/
def corootOfPair (u v : Fin (2 * n)) : Fin n → ℤ := fun k =>
  if (k : ℕ) + 1 = n then (if sgn u = sgn v then sgn u else 0)
  else sgn u * (if axis u ≤ (k : ℕ) then 1 else 0) + sgn v * (if axis v ≤ (k : ℕ) then 1 else 0)
lemma corootOfPair_apply (u v : Fin (2 * n)) (k : Fin n) : corootOfPair u v k =
    if (k : ℕ) + 1 = n then (if sgn u = sgn v then sgn u else 0)
    else sgn u * (if axis u ≤ (k : ℕ) then 1 else 0) + sgn v *
      (if axis v ≤ (k : ℕ) then 1 else 0) := (rfl)

lemma corootOfPair_comm (u v : Fin (2 * n)) : corootOfPair u v = corootOfPair v u := by
  funext k
  simp only [corootOfPair]
  by_cases hk : (k : ℕ) + 1 = n
  · rw [ite_eq_left hk, ite_eq_left hk]
    by_cases hs : sgn u = sgn v
    · rw [ite_eq_left hs, ite_eq_left hs.symm, hs]
    · rw [ite_eq_right hs, ite_eq_right fun hc => hs hc.symm]
  · rw [ite_eq_right hk, ite_eq_right hk]
    ring

@[simp] lemma corootOfPair_self (u : Fin (2 * n)) : corootOfPair u u = signedCoweight u := by
  funext k
  have hlt := axis_lt u
  simp only [corootOfPair, signedCoweight, coweight, Pi.smul_apply, smul_eq_mul]
  by_cases hk : (k : ℕ) + 1 = n
  · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left (show axis u ≤ (k : ℕ) by omega)]
    simp
  · rw [ite_eq_right hk, ite_eq_right hk]
    ring

/-- **The integral form of the halving.** -/
lemma corootOfPair_add_self (u v : Fin (2 * n)) :
    corootOfPair u v + corootOfPair u v = signedCoweight u + signedCoweight v := by
  funext k
  have hlt := axis_lt u
  have hlt' := axis_lt v
  simp only [corootOfPair, signedCoweight, coweight, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : (k : ℕ) + 1 = n
  · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left (show axis u ≤ (k : ℕ) by omega),
      ite_eq_left (show axis v ≤ (k : ℕ) by omega)]
    rcases sgn_eq_one_or_neg_one u with h | h <;> rcases sgn_eq_one_or_neg_one v with h' | h' <;>
      rw [h, h'] <;> norm_num
  · rw [ite_eq_right hk, ite_eq_right hk]
    ring

lemma two_smul_corootOfPair (u v : Fin (2 * n)) :
    (2 : ℤ) • corootOfPair u v = signedCoweight u + signedCoweight v := by
  rw [two_smul]
  exact corootOfPair_add_self u v

/-! ## Cyclic offsets and the index of a pair -/

/-- The signed basis vector `d` steps after `u` in the cyclic order on `Fin (2 * n)`. -/
def shift (u : Fin (2 * n)) (d : Fin n) : Fin (2 * n) :=
  ⟨if (u : ℕ) + (d : ℕ) < 2 * n then (u : ℕ) + (d : ℕ) else (u : ℕ) + (d : ℕ) - 2 * n,
    by have := u.isLt; have := d.isLt; split <;> omega⟩

lemma coe_shift (u : Fin (2 * n)) (d : Fin n) :
    ((shift u d : Fin (2 * n)) : ℕ) =
      if (u : ℕ) + (d : ℕ) < 2 * n then (u : ℕ) + (d : ℕ) else (u : ℕ) + (d : ℕ) - 2 * n := (rfl)

lemma shift_eq_self {u : Fin (2 * n)} {d : Fin n} (hd : (d : ℕ) = 0) : shift u d = u := by
  have := u.isLt
  exact Fin.ext (by rw [coe_shift, hd]; split <;> omega)

lemma axis_shift_ne {u : Fin (2 * n)} {d : Fin n} (hd : (d : ℕ) ≠ 0) :
    axis (shift u d) ≠ axis u := by
  have hu := u.isLt
  have hd' := d.isLt
  simp only [axis, coe_shift]
  split_ifs <;> omega

/-- The cyclic distance from `u` to `v` in `Fin (2 * n)`. -/
def cyclicDistance (u v : Fin (2 * n)) : ℕ :=
  if (u : ℕ) ≤ (v : ℕ) then (v : ℕ) - (u : ℕ) else (v : ℕ) + 2 * n - (u : ℕ)

lemma cyclicDistance_lt (u v : Fin (2 * n)) : cyclicDistance u v < 2 * n := by
  have := u.isLt; have := v.isLt
  simp only [cyclicDistance]; split <;> omega

@[simp] lemma cyclicDistance_eq_zero_iff {u v : Fin (2 * n)} : cyclicDistance u v = 0 ↔ u = v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [cyclicDistance, Fin.ext_iff]
  split <;> omega

@[simp] lemma cyclicDistance_shift (u : Fin (2 * n)) (d : Fin n) :
    cyclicDistance u (shift u d) = (d : ℕ) := by
  have hu := u.isLt
  have hd := d.isLt
  simp only [cyclicDistance, coe_shift]
  split_ifs <;> omega

lemma shift_cyclicDistance {u v : Fin (2 * n)} (h : cyclicDistance u v < n) :
    shift u ⟨cyclicDistance u v, h⟩ = v := by
  have hu := u.isLt
  have hv := v.isLt
  refine Fin.ext ?_
  simp only [coe_shift, cyclicDistance]
  split_ifs <;> omega

lemma cyclicDistance_add_cyclicDistance {u v : Fin (2 * n)} (h : u ≠ v) :
    cyclicDistance u v + cyclicDistance v u = 2 * n := by
  have hu := u.isLt
  have hv := v.isLt
  have : (u : ℕ) ≠ (v : ℕ) := fun hc => h (Fin.ext hc)
  simp only [cyclicDistance]
  split_ifs <;> omega

lemma cyclicDistance_eq_rank_iff {u v : Fin (2 * n)} : cyclicDistance u v = n ↔ u = opp v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [cyclicDistance, Fin.ext_iff, coe_opp]
  split_ifs <;> omega

/-- A pair of signed basis vectors naming a root: either equal, for a short root, or on distinct
axes, for a long root. -/
def IsPair (u v : Fin (2 * n)) : Prop := u = v ∨ axis u ≠ axis v

/-- Characterization of the signed-vector pairs that name roots of type `Bₙ`. This is the public
introduction and elimination rule for the body-hidden predicate `IsPair`. -/
lemma isPair_iff (u v : Fin (2 * n)) : IsPair u v ↔ u = v ∨ axis u ≠ axis v := Iff.rfl

lemma IsPair.cyclicDistance_ne {u v : Fin (2 * n)} (h : IsPair u v) (huv : u ≠ v) :
    cyclicDistance u v ≠ 0 ∧ cyclicDistance u v ≠ n := by
  have hax : axis u ≠ axis v := h.resolve_left huv
  refine ⟨fun hc => huv (cyclicDistance_eq_zero_iff.mp hc), fun hc => hax ?_⟩
  rw [cyclicDistance_eq_rank_iff.mp hc, axis_opp]

lemma isPair_shift (u : Fin (2 * n)) (d : Fin n) : IsPair u (shift u d) := by
  rcases Nat.eq_zero_or_pos (d : ℕ) with hd | hd
  · exact Or.inl (shift_eq_self hd).symm
  · exact Or.inr fun hc => axis_shift_ne (n := n) (u := u) (d := d) (by omega) hc.symm

/-- The canonical index in `Fin (2 * n) × Fin n` of the root named by a pair of signed basis
vectors. For a distinct admissible pair it uses the unique order whose cyclic offset lies in
`Fin n`; a short pair uses the coincident order with offset zero. -/
def index (u v : Fin (2 * n)) : Fin (2 * n) × Fin n :=
  if h : cyclicDistance u v < n then (u, ⟨cyclicDistance u v, h⟩)
  else if h' : cyclicDistance v u < n then (v, ⟨cyclicDistance v u, h'⟩)
  else (u, ⟨0, rank_pos u⟩)

@[simp] lemma index_shift (z : Fin (2 * n) × Fin n) : index z.1 (shift z.1 z.2) = z := by
  have h := cyclicDistance_shift z.1 z.2
  rw [index, dite_eq_left (by rw [h]; exact z.2.isLt)]
  exact Prod.ext rfl (Fin.ext h)

lemma index_comm {u v : Fin (2 * n)} (h : IsPair u v) : index u v = index v u := by
  rcases eq_or_ne u v with rfl | huv
  · rfl
  obtain ⟨h0, hn⟩ := h.cyclicDistance_ne huv
  have hsum := cyclicDistance_add_cyclicDistance huv
  have hlt := cyclicDistance_lt u v
  by_cases h1 : cyclicDistance u v < n
  · rw [index, dite_eq_left h1, index, dite_eq_right (by omega), dite_eq_left h1]
  · rw [index, dite_eq_right h1, dite_eq_left (by omega), index, dite_eq_left (by omega)]

lemma shift_index {u v : Fin (2 * n)} (h : IsPair u v) :
    ((index u v).1 = u ∧ shift (index u v).1 (index u v).2 = v) ∨
      ((index u v).1 = v ∧ shift (index u v).1 (index u v).2 = u) := by
  rcases eq_or_ne u v with rfl | huv
  · have hlt : cyclicDistance u u < n := by
      rw [cyclicDistance_eq_zero_iff.mpr rfl]; exact rank_pos u
    exact Or.inl ⟨by rw [index, dite_eq_left hlt],
      by rw [index, dite_eq_left hlt]; exact shift_cyclicDistance hlt⟩
  obtain ⟨h0, hn⟩ := h.cyclicDistance_ne huv
  have hsum := cyclicDistance_add_cyclicDistance huv
  have hlt := cyclicDistance_lt u v
  by_cases h1 : cyclicDistance u v < n
  · exact Or.inl ⟨by rw [index, dite_eq_left h1],
      by rw [index, dite_eq_left h1]; exact shift_cyclicDistance h1⟩
  · have h2 : cyclicDistance v u < n := by omega
    exact Or.inr ⟨by rw [index, dite_eq_right h1, dite_eq_left h2],
      by rw [index, dite_eq_right h1, dite_eq_left h2]; exact shift_cyclicDistance h2⟩

/-! ## Roots and coroots -/

/-- The character coordinates of the root named by a pair of signed basis vectors. -/
def rootOfPair (u v : Fin (2 * n)) : Fin n → ℤ :=
  if u = v then signedWeight u else signedWeight u + signedWeight v

lemma rootOfPair_comm (u v : Fin (2 * n)) : rootOfPair u v = rootOfPair v u := by
  rcases eq_or_ne u v with rfl | huv
  · rfl
  · rw [rootOfPair, rootOfPair, ite_eq_right huv, ite_eq_right (Ne.symm huv), add_comm]

@[simp] lemma rootOfPair_self (u : Fin (2 * n)) : rootOfPair u u = signedWeight u := by
  rw [rootOfPair, ite_eq_left rfl]

@[simp] lemma rootOfPair_of_ne {u v : Fin (2 * n)} (h : u ≠ v) :
    rootOfPair u v = signedWeight u + signedWeight v := by
  rw [rootOfPair, ite_eq_right h]

/-- The root indexed by an element of `Fin (2 * n) × Fin n`. -/
def rootIdx (z : Fin (2 * n) × Fin n) : Fin n → ℤ := rootOfPair z.1 (shift z.1 z.2)
lemma rootIdx_def (z : Fin (2 * n) × Fin n) : rootIdx z = rootOfPair z.1 (shift z.1 z.2) := (rfl)

/-- The coroot indexed by an element of `Fin (2 * n) × Fin n`. -/
def corootIdx (z : Fin (2 * n) × Fin n) : Fin n → ℤ :=
  corootOfPair z.1 (shift z.1 z.2)
lemma corootIdx_def (z : Fin (2 * n) × Fin n) :
    corootIdx z = corootOfPair z.1 (shift z.1 z.2) := (rfl)

@[simp] lemma rootIdx_index {u v : Fin (2 * n)} (h : IsPair u v) :
    rootIdx (index u v) = rootOfPair u v := by
  rcases shift_index h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [rootIdx, h2, h1]
  · rw [rootIdx, h2, h1, rootOfPair_comm]

@[simp] lemma corootIdx_index {u v : Fin (2 * n)} (h : IsPair u v) :
    corootIdx (index u v) = corootOfPair u v := by
  rcases shift_index h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [corootIdx, h2, h1]
  · rw [corootIdx, h2, h1, corootOfPair_comm]

lemma two_mul_dotProduct_corootOfPair (u p q : Fin (2 * n)) :
    2 * (signedWeight u ⬝ᵥ corootOfPair p q) =
      signedWeight u ⬝ᵥ signedCoweight p + signedWeight u ⬝ᵥ signedCoweight q := by
  rw [← dotProduct_add, ← corootOfPair_add_self p q, dotProduct_add]
  ring

lemma rootOfPair_dotProduct_corootOfPair {u v : Fin (2 * n)} (h : IsPair u v) :
    rootOfPair u v ⬝ᵥ corootOfPair u v = 2 := by
  rcases eq_or_ne u v with rfl | huv
  · rw [rootOfPair_self, corootOfPair_self, signedWeight_dotProduct_self]
  · have hax : axis u ≠ axis v := h.resolve_left huv
    have h1 := two_mul_dotProduct_corootOfPair u u v
    have h2 := two_mul_dotProduct_corootOfPair v u v
    rw [signedWeight_dotProduct_self, signedWeight_dotProduct_of_axis_ne hax] at h1
    rw [signedWeight_dotProduct_self, signedWeight_dotProduct_of_axis_ne (Ne.symm hax)] at h2
    rw [rootOfPair_of_ne huv, add_dotProduct]
    omega

/-- Cartan integers between roots in the classical type `B` model have absolute value at most
two. -/
lemma abs_rootOfPair_dotProduct_corootOfPair_le_two {u v p q : Fin (2 * n)}
    (huv : IsPair u v) (hpq : IsPair p q) :
    |rootOfPair u v ⬝ᵥ corootOfPair p q| ≤ 2 := by
  have atom_le_two (z : Fin (2 * n)) : |signedWeight z ⬝ᵥ corootOfPair p q| ≤ 2 := by
    have hval := two_mul_dotProduct_corootOfPair z p q
    rw [signedWeight_dotProduct_signedCoweight,
      signedWeight_dotProduct_signedCoweight] at hval
    rw [abs_le]
    constructor <;> split_ifs at hval <;> omega
  rcases eq_or_ne u v with rfl | huv_ne
  · simpa only [rootOfPair_self] using atom_le_two u
  rcases eq_or_ne p q with rfl | hpq_ne
  · have haxis : axis u ≠ axis v := huv.resolve_left huv_ne
    have huv_opp : u ≠ opp v := ne_of_axis_ne (by simpa using haxis)
    have hvu : v ≠ u := ne_of_axis_ne haxis.symm
    have hvu_opp : v ≠ opp u := ne_of_axis_ne (by simpa using haxis.symm)
    rw [rootOfPair_of_ne huv_ne, corootOfPair_self, add_dotProduct,
      signedWeight_dotProduct_signedCoweight,
      signedWeight_dotProduct_signedCoweight, abs_le]
    constructor <;> split_ifs <;> simp_all
  · have atom_le_one (z : Fin (2 * n)) : |signedWeight z ⬝ᵥ corootOfPair p q| ≤ 1 := by
      have haxis : axis p ≠ axis q := hpq.resolve_left hpq_ne
      have hpq_opp : p ≠ opp q := ne_of_axis_ne (by simpa using haxis)
      have hqp : q ≠ p := ne_of_axis_ne haxis.symm
      have hqp_opp : q ≠ opp p := ne_of_axis_ne (by simpa using haxis.symm)
      have hoppp_oppq : opp p ≠ opp q := by
        intro h
        exact hpq_ne (by simpa using congrArg opp h)
      have hval := two_mul_dotProduct_corootOfPair z p q
      rw [signedWeight_dotProduct_signedCoweight,
        signedWeight_dotProduct_signedCoweight] at hval
      rw [abs_le]
      constructor <;> split_ifs at hval <;> subst_vars <;> simp_all
    rw [rootOfPair_of_ne huv_ne, add_dotProduct]
    have hu := atom_le_one u
    have hv := atom_le_one v
    calc
      |signedWeight u ⬝ᵥ corootOfPair p q + signedWeight v ⬝ᵥ corootOfPair p q| ≤
          |signedWeight u ⬝ᵥ corootOfPair p q| +
            |signedWeight v ⬝ᵥ corootOfPair p q| := abs_add_le _ _
      _ ≤ 2 := by omega

/-! ## The reflection in a root -/

/-- The signed permutation of the basis vectors realising the reflection in the root named by the
pair `{p, q}`. On a long root it exchanges `p` with `-q` and `q` with `-p`; on a short root, where
`p = q`, it is the sign change on the axis of `p`. -/
def reflMap (p q u : Fin (2 * n)) : Fin (2 * n) :=
  if u = p then (if p = q then opp p else opp q)
  else if u = q then opp p
  else if u = opp p then (if p = q then p else q)
  else if u = opp q then p
  else u

section Refl

variable {p q : Fin (2 * n)}

lemma reflMap_fst (p q : Fin (2 * n)) : reflMap p q p = if p = q then opp p else opp q := by
  rw [reflMap, ite_eq_left rfl]

lemma reflMap_snd (h : q ≠ p) : reflMap p q q = opp p := by
  rw [reflMap, ite_eq_right h, ite_eq_left rfl]

lemma reflMap_opp_fst (h : opp p ≠ q) : reflMap p q (opp p) = if p = q then p else q := by
  rw [reflMap, ite_eq_right (opp_ne_self p), ite_eq_right h, ite_eq_left rfl]

lemma reflMap_opp_snd (h1 : opp q ≠ p) (h2 : opp q ≠ opp p) : reflMap p q (opp q) = p := by
  rw [reflMap, ite_eq_right h1, ite_eq_right (opp_ne_self q), ite_eq_right h2, ite_eq_left rfl]

lemma reflMap_of_ne {u : Fin (2 * n)} (h1 : u ≠ p) (h2 : u ≠ q) (h3 : u ≠ opp p) (h4 : u ≠ opp q) :
    reflMap p q u = u := by
  rw [reflMap, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

/-- The eight inequalities between `p`, `q` and their opposites available on a long root. -/
private lemma long_ne (hax : axis p ≠ axis q) :
    p ≠ q ∧ p ≠ opp q ∧ q ≠ p ∧ q ≠ opp p ∧ opp p ≠ q ∧ opp p ≠ opp q ∧ opp q ≠ p ∧
      opp q ≠ opp p :=
  ⟨ne_of_axis_ne hax, ne_of_axis_ne (by rwa [axis_opp]), ne_of_axis_ne (Ne.symm hax),
    ne_of_axis_ne (by rw [axis_opp]; exact Ne.symm hax), ne_of_axis_ne (by rwa [axis_opp]),
    ne_of_axis_ne (by rw [axis_opp, axis_opp]; exact hax),
    ne_of_axis_ne (by rw [axis_opp]; exact Ne.symm hax),
    ne_of_axis_ne (by rw [axis_opp, axis_opp]; exact Ne.symm hax)⟩

lemma reflMap_involutive (h : IsPair p q) : Function.Involutive (reflMap p q) := by
  intro u
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    by_cases h1 : u = p
    · subst h1
      rw [reflMap_fst, ite_eq_left rfl, reflMap_opp_fst hop, ite_eq_left rfl]
    · by_cases h2 : u = opp p
      · subst h2
        rw [reflMap_opp_fst hop, ite_eq_left rfl, reflMap_fst, ite_eq_left rfl]
      · rw [reflMap_of_ne h1 h1 h2 h2, reflMap_of_ne h1 h1 h2 h2]
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    by_cases c1 : u = p
    · subst c1
      rw [reflMap_fst, ite_eq_right h1, reflMap_opp_snd h7 h8]
    by_cases c2 : u = q
    · subst c2
      rw [reflMap_snd h3, reflMap_opp_fst h5, ite_eq_right h1]
    by_cases c3 : u = opp p
    · subst c3
      rw [reflMap_opp_fst h5, ite_eq_right h1, reflMap_snd h3]
    by_cases c4 : u = opp q
    · subst c4
      rw [reflMap_opp_snd h7 h8, reflMap_fst, ite_eq_right h1]
    · rw [reflMap_of_ne c1 c2 c3 c4, reflMap_of_ne c1 c2 c3 c4]

lemma reflMap_opp (h : IsPair p q) (u : Fin (2 * n)) :
    reflMap p q (opp u) = opp (reflMap p q u) := by
  have key : ∀ a b : Fin (2 * n), opp a = b ↔ a = opp b := by
    intro a b
    constructor
    · rintro rfl; rw [opp_opp]
    · rintro rfl; rw [opp_opp]
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    by_cases h1 : u = p
    · subst h1
      rw [reflMap_opp_fst hop, ite_eq_left rfl, reflMap_fst, ite_eq_left rfl, opp_opp]
    · by_cases h2 : u = opp p
      · subst h2
        rw [opp_opp, reflMap_fst, ite_eq_left rfl, reflMap_opp_fst hop, ite_eq_left rfl]
      · have h1' : opp u ≠ p := fun hc => h2 ((key u p).mp hc)
        have h2' : opp u ≠ opp p := fun hc => h1 (by simpa using congrArg opp hc)
        rw [reflMap_of_ne h1' h1' h2' h2', reflMap_of_ne h1 h1 h2 h2]
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    by_cases c1 : u = p
    · subst c1
      rw [reflMap_opp_fst h5, ite_eq_right h1, reflMap_fst, ite_eq_right h1, opp_opp]
    by_cases c2 : u = q
    · subst c2
      rw [reflMap_opp_snd h7 h8, reflMap_snd h3, opp_opp]
    by_cases c3 : u = opp p
    · subst c3
      rw [opp_opp, reflMap_fst, ite_eq_right h1, reflMap_opp_fst h5, ite_eq_right h1]
    by_cases c4 : u = opp q
    · subst c4
      rw [opp_opp, reflMap_snd h3, reflMap_opp_snd h7 h8]
    · have c1' : opp u ≠ p := fun hc => c3 ((key u p).mp hc)
      have c2' : opp u ≠ q := fun hc => c4 ((key u q).mp hc)
      have c3' : opp u ≠ opp p := fun hc => c1 (by simpa using congrArg opp hc)
      have c4' : opp u ≠ opp q := fun hc => c2 (by simpa using congrArg opp hc)
      rw [reflMap_of_ne c1' c2' c3' c4', reflMap_of_ne c1 c2 c3 c4]

lemma isPair_reflMap (h : IsPair p q) {u v : Fin (2 * n)} (huv : IsPair u v) :
    IsPair (reflMap p q u) (reflMap p q v) := by
  rcases eq_or_ne u v with rfl | hne
  · exact Or.inl rfl
  refine Or.inr fun hc => ?_
  rcases eq_or_eq_opp_of_axis_eq hc with hc' | hc'
  · exact hne ((reflMap_involutive h).injective hc')
  · rw [← reflMap_opp h] at hc'
    have heq := (reflMap_involutive h).injective hc'
    exact (huv.resolve_left hne) (by rw [heq, axis_opp])

/-- **The reflection formula on a single signed basis vector.** -/
lemma signedWeight_reflMap (h : IsPair p q) (u : Fin (2 * n)) :
    signedWeight (reflMap p q u) =
      signedWeight u - (signedWeight u ⬝ᵥ corootOfPair p q) • rootOfPair p q := by
  -- A short root only swaps `p` and `opp p`; all other signed basis vectors are fixed and pair
  -- trivially with its coroot.
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    rw [corootOfPair_self, rootOfPair_self]
    by_cases c1 : u = p
    · rw [c1, reflMap_fst, ite_eq_left rfl, signedWeight_dotProduct_self, signedWeight_opp]
      module
    · by_cases c2 : u = opp p
      · rw [c2, reflMap_opp_fst hop, ite_eq_left rfl, signedWeight_opp, neg_dotProduct,
          signedWeight_dotProduct_self]
        module
      · rw [reflMap_of_ne c1 c1 c2 c2, signedWeight_dotProduct_eq_zero c1 c2]
        module
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    have hpq' : signedWeight p ⬝ᵥ signedCoweight q = 0 := signedWeight_dotProduct_of_axis_ne hax
    have hqp : signedWeight q ⬝ᵥ signedCoweight p = 0 :=
      signedWeight_dotProduct_of_axis_ne (Ne.symm hax)
    rw [rootOfPair_of_ne h1]
    -- For a long root, split the signed basis vectors into `p`, `q`, their opposites, and the
    -- complement. The pairing is respectively `1`, `1`, `-1`, `-1`, and `0`.
    by_cases c1 : u = p
    · have hval := two_mul_dotProduct_corootOfPair p p q
      rw [signedWeight_dotProduct_self, hpq'] at hval
      rw [c1, show signedWeight p ⬝ᵥ corootOfPair p q = 1 by omega, reflMap_fst, ite_eq_right h1,
        signedWeight_opp]
      module
    by_cases c2 : u = q
    · have hval := two_mul_dotProduct_corootOfPair q p q
      rw [signedWeight_dotProduct_self, hqp] at hval
      rw [c2, show signedWeight q ⬝ᵥ corootOfPair p q = 1 by omega, reflMap_snd h3,
        signedWeight_opp]
      module
    by_cases c3 : u = opp p
    · have e1 : signedWeight (opp p) ⬝ᵥ signedCoweight p = -2 := by
        rw [signedWeight_opp, neg_dotProduct, signedWeight_dotProduct_self]
      have e2 : signedWeight (opp p) ⬝ᵥ signedCoweight q = 0 := by
        rw [signedWeight_opp, neg_dotProduct, hpq', neg_zero]
      have hval := two_mul_dotProduct_corootOfPair (opp p) p q
      rw [e1, e2] at hval
      rw [c3, show signedWeight (opp p) ⬝ᵥ corootOfPair p q = -1 by omega,
        reflMap_opp_fst h5, ite_eq_right h1, signedWeight_opp]
      module
    by_cases c4 : u = opp q
    · have e1 : signedWeight (opp q) ⬝ᵥ signedCoweight p = 0 := by
        rw [signedWeight_opp, neg_dotProduct, hqp, neg_zero]
      have e2 : signedWeight (opp q) ⬝ᵥ signedCoweight q = -2 := by
        rw [signedWeight_opp, neg_dotProduct, signedWeight_dotProduct_self]
      have hval := two_mul_dotProduct_corootOfPair (opp q) p q
      rw [e1, e2] at hval
      rw [c4, show signedWeight (opp q) ⬝ᵥ corootOfPair p q = -1 by omega,
        reflMap_opp_snd h7 h8, signedWeight_opp]
      module
    · have hval := two_mul_dotProduct_corootOfPair u p q
      rw [signedWeight_dotProduct_eq_zero c1 c3, signedWeight_dotProduct_eq_zero c2 c4] at hval
      rw [show signedWeight u ⬝ᵥ corootOfPair p q = 0 by omega, reflMap_of_ne c1 c2 c3 c4]
      module

/-- **The reflection formula on the double of a single signed basis vector.** -/
lemma signedCoweight_reflMap (h : IsPair p q) (u : Fin (2 * n)) :
    signedCoweight (reflMap p q u) =
      signedCoweight u - (rootOfPair p q ⬝ᵥ signedCoweight u) • corootOfPair p q := by
  -- The short-root case has the same two-point orbit as `signedWeight_reflMap`, now on the doubled
  -- coweight coordinates.
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    rw [corootOfPair_self, rootOfPair_self]
    by_cases c1 : u = p
    · rw [c1, reflMap_fst, ite_eq_left rfl, signedWeight_dotProduct_self, signedCoweight_opp]
      module
    · by_cases c2 : u = opp p
      · rw [c2, reflMap_opp_fst hop, ite_eq_left rfl, signedCoweight_opp, dotProduct_neg,
          signedWeight_dotProduct_self]
        module
      · rw [reflMap_of_ne c1 c1 c2 c2, signedWeight_dotProduct_eq_zero (Ne.symm c1)
          (fun hc => c2 (by rw [hc, opp_opp]))]
        module
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    have hpq' : signedWeight p ⬝ᵥ signedCoweight q = 0 := signedWeight_dotProduct_of_axis_ne hax
    have hqp : signedWeight q ⬝ᵥ signedCoweight p = 0 :=
      signedWeight_dotProduct_of_axis_ne (Ne.symm hax)
    have hsum := two_smul_corootOfPair p q
    have hneg : ((-2 : ℤ)) • corootOfPair p q = -(signedCoweight p + signedCoweight q) := by
      rw [← hsum, show ((-2 : ℤ)) • corootOfPair p q =
        -((2 : ℤ) • corootOfPair p q) from by module]
    rw [rootOfPair_of_ne h1]
    -- As above, the long-root reflection has four exceptional signed basis vectors. Their
    -- root-pairing values are `2`, `2`, `-2`, and `-2`; the complement pairs to zero.
    by_cases c1 : u = p
    · rw [c1, add_dotProduct, signedWeight_dotProduct_self, hqp, reflMap_fst, ite_eq_right h1,
        signedCoweight_opp,
        show (2 : ℤ) + 0 = 2 by ring, hsum]
      module
    by_cases c2 : u = q
    · rw [c2, add_dotProduct, hpq', signedWeight_dotProduct_self, reflMap_snd h3,
        signedCoweight_opp,
        show (0 : ℤ) + 2 = 2 by ring, hsum]
      module
    by_cases c3 : u = opp p
    · have e1 : signedWeight p ⬝ᵥ signedCoweight (opp p) = -2 := by
        rw [signedCoweight_opp, dotProduct_neg, signedWeight_dotProduct_self]
      have e2 : signedWeight q ⬝ᵥ signedCoweight (opp p) = 0 := by
        rw [signedCoweight_opp, dotProduct_neg, hqp, neg_zero]
      rw [c3, add_dotProduct, e1, e2, reflMap_opp_fst h5, ite_eq_right h1,
        show -(2 : ℤ) + 0 = -2 by ring, hneg, signedCoweight_opp]
      module
    by_cases c4 : u = opp q
    · have e1 : signedWeight p ⬝ᵥ signedCoweight (opp q) = 0 := by
        rw [signedCoweight_opp, dotProduct_neg, hpq', neg_zero]
      have e2 : signedWeight q ⬝ᵥ signedCoweight (opp q) = -2 := by
        rw [signedCoweight_opp, dotProduct_neg, signedWeight_dotProduct_self]
      rw [c4, add_dotProduct, e1, e2, reflMap_opp_snd h7 h8,
        show (0 : ℤ) + -2 = -2 by ring, hneg, signedCoweight_opp]
      module
    · rw [add_dotProduct,
        signedWeight_dotProduct_eq_zero (Ne.symm c1) (fun hc => c3 (by rw [hc, opp_opp])),
        signedWeight_dotProduct_eq_zero (Ne.symm c2) (fun hc => c4 (by rw [hc, opp_opp])),
        reflMap_of_ne c1 c2 c3 c4]
      module

end Refl

/-! ## Recovering the index from the root -/

/-- The signed basis vectors occurring in a root are exactly those pairing to `2` with it. -/
lemma rootIdx_dotProduct_signedCoweight_eq_two_iff (z : Fin (2 * n) × Fin n) (m : Fin (2 * n)) :
    rootIdx z ⬝ᵥ signedCoweight m = 2 ↔ (m = z.1 ∨ m = shift z.1 z.2) := by
  have hpair : IsPair z.1 (shift z.1 z.2) := isPair_shift z.1 z.2
  rcases eq_or_ne z.1 (shift z.1 z.2) with heq | hne
  · rw [rootIdx, ← heq, rootOfPair_self, signedWeight_dotProduct_signedCoweight]
    constructor
    · intro hc
      by_cases hc1 : z.1 = m
      · exact Or.inl hc1.symm
      · rw [ite_eq_right hc1] at hc
        split_ifs at hc
        omega
    · rintro (rfl | rfl)
      · rw [ite_eq_left rfl]
      · rw [ite_eq_left rfl]
  · have hax : axis z.1 ≠ axis (shift z.1 z.2) := hpair.resolve_left hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    rw [rootIdx, rootOfPair_of_ne hne, add_dotProduct,
      signedWeight_dotProduct_signedCoweight, signedWeight_dotProduct_signedCoweight]
    constructor
    · intro hc
      by_cases hm1 : z.1 = m
      · exact Or.inl hm1.symm
      by_cases hm2 : shift z.1 z.2 = m
      · exact Or.inr hm2.symm
      rw [ite_eq_right hm1, ite_eq_right hm2] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | hm)
      · rw [ite_eq_left rfl, ite_eq_right h3, ite_eq_right h4]
        ring
      · rw [hm, ite_eq_left rfl, ite_eq_right h1, ite_eq_right h2]
        ring

/-- The signed basis vectors occurring in a coroot, detected by a doubled pairing so that both the
short and the long case are covered. -/
lemma two_mul_signedWeight_dotProduct_corootIdx_iff (z : Fin (2 * n) × Fin n) (m : Fin (2 * n)) :
    (2 * (signedWeight m ⬝ᵥ corootIdx z) = 4 ∨ 2 * (signedWeight m ⬝ᵥ corootIdx z) = 2) ↔
      (m = z.1 ∨ m = shift z.1 z.2) := by
  have hpair : IsPair z.1 (shift z.1 z.2) := isPair_shift z.1 z.2
  have hval : 2 * (signedWeight m ⬝ᵥ corootIdx z) =
      signedWeight m ⬝ᵥ signedCoweight z.1 +
        signedWeight m ⬝ᵥ signedCoweight (shift z.1 z.2) :=
    two_mul_dotProduct_corootOfPair m z.1 (shift z.1 z.2)
  rw [hval, signedWeight_dotProduct_signedCoweight, signedWeight_dotProduct_signedCoweight]
  rcases eq_or_ne z.1 (shift z.1 z.2) with heq | hne
  · rw [← heq]
    constructor
    · intro hc
      by_cases hm : m = z.1
      · exact Or.inl hm
      rw [ite_eq_right hm] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | rfl)
      · rw [ite_eq_left rfl]
        omega
      · rw [ite_eq_left rfl]
        omega
  · have hax : axis z.1 ≠ axis (shift z.1 z.2) := hpair.resolve_left hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    constructor
    · intro hc
      by_cases hm1 : m = z.1
      · exact Or.inl hm1
      by_cases hm2 : m = shift z.1 z.2
      · exact Or.inr hm2
      rw [ite_eq_right hm1, ite_eq_right hm2] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | rfl)
      · rw [ite_eq_left rfl, ite_eq_right hne, ite_eq_right h2]
        omega
      · rw [ite_eq_left rfl, ite_eq_right h3, ite_eq_right h4]
        omega

/-- Two indices naming the same pair of signed basis vectors are equal. -/
lemma index_eq_of_pair_mem_iff {z z' : Fin (2 * n) × Fin n}
    (h : ∀ m, (m = z.1 ∨ m = shift z.1 z.2) ↔ (m = z'.1 ∨ m = shift z'.1 z'.2)) : z = z' := by
  have e1 : cyclicDistance z.1 (shift z.1 z.2) = (z.2 : ℕ) := cyclicDistance_shift _ _
  have e2 : cyclicDistance z'.1 (shift z'.1 z'.2) = (z'.2 : ℕ) := cyclicDistance_shift _ _
  have hz := z.2.isLt
  have hz' := z'.2.isLt
  have h1 := (h z.1).mp (Or.inl rfl)
  have h2 := (h z'.1).mpr (Or.inl rfl)
  have hfst : z.1 = z'.1 := by
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2.symm
    rcases eq_or_ne z.1 (shift z.1 z.2) with heq | hne
    · exact (h2.trans heq.symm).symm
    · exfalso
      have hne' : z.1 ≠ z'.1 := by rw [h2]; exact hne
      have hsum := cyclicDistance_add_cyclicDistance hne'
      rw [← h1] at e2
      rw [← h2] at e1
      omega
  refine Prod.ext hfst (Fin.ext ?_)
  have hsnd : shift z.1 z.2 = shift z'.1 z'.2 := by
    rcases (h (shift z.1 z.2)).mp (Or.inr rfl) with hc | hc
    · rcases (h (shift z'.1 z'.2)).mpr (Or.inr rfl) with hc' | hc'
      · rw [hc', hc]
        exact hfst.symm
      · exact hc'.symm
    · exact hc
  rw [← e1, ← e2, hsnd, hfst]

end TauCeti.DynkinType.TypeB
