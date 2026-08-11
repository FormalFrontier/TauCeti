/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual

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
`(u, d) : Fin (2 * n) × Fin n`, exactly one of the two orders having its offset in the range
`Fin n`; this is the index type the datum is built on, and `TauCeti.DynkinType.TypeB.index` is the
inverse normalisation.

The coroot is *uniform* in the pair while the root is not:
`TauCeti.DynkinType.TypeB.corootOfPair` computes
the simple-coroot coordinates of the coroot from the pair, and specialises to the short coroot when
the two entries agree, since `(e_a)^∨ = 2 e_a = e_a + e_a`. It is a genuine half, and the integral
identity `TauCeti.DynkinType.TypeB.corootOfPair_add_self` is how the reflection identity for
coroots is proved.

## Main definitions

* `TauCeti.DynkinType.TypeB.wt` and `TauCeti.DynkinType.TypeB.cwt`: the coordinates of a signed
  basis vector and of its double.
* `TauCeti.DynkinType.TypeB.rootOfPair` and `TauCeti.DynkinType.TypeB.corootOfPair`: the root and
  coroot named by a pair of signed basis vectors.
* `TauCeti.DynkinType.TypeB.reflMap`: the signed permutation realising the reflection in a root.

The coordinate definitions are used through their defining and case-characterization lemmas below;
their bodies are not exposed to importing modules.

## Main results

* `TauCeti.DynkinType.TypeB.wt_reflMap` and `TauCeti.DynkinType.TypeB.cwt_reflMap`: the reflection
  formulas on a single signed basis vector, from which the root-datum axioms follow additively.
* `TauCeti.DynkinType.TypeB.eq_of_forall_mem_iff`: an index is recovered from its unordered
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
lemma weight_apply (n a : ℕ) (k : Fin n) : weight n a k =
    (if a = (k : ℕ) then (if (k : ℕ) + 1 = n then 2 else 1) else 0) -
      (if a = (k : ℕ) + 1 ∧ (k : ℕ) + 1 < n then 1 else 0) := (rfl)

/-- The cocharacter-lattice coordinates of `2 e_b`, that is, its coordinates in the simple coroots
`αₖ^∨ = e_k - e_{k+1}` and `α_{n-1}^∨ = 2 e_{n-1}`. The vector `e_b` alone is half-integral in that
basis, so it is its double that is recorded. -/
def coweight (n b : ℕ) : Fin n → ℤ := fun k =>
  (if (k : ℕ) + 1 = n then 1 else 2) * (if b ≤ (k : ℕ) then 1 else 0)
lemma coweight_apply (n b : ℕ) (k : Fin n) : coweight n b k =
    (if (k : ℕ) + 1 = n then 1 else 2) * (if b ≤ (k : ℕ) then 1 else 0) := (rfl)

lemma weight_eq_zero_of_le {a : ℕ} (ha : n ≤ a) : weight n a = 0 := by
  funext k
  have := k.isLt
  simp only [weight, Pi.zero_apply]
  rw [if_neg (by omega), if_neg (by omega)]
  ring

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
    rw [Finset.sum_eq_single a (fun m _ hm => if_neg (Ne.symm hm))
      (fun hm => absurd (Finset.mem_range.mpr ha) hm), if_pos rfl]
    split_ifs <;> ring
  have h2 : ∑ m ∈ Finset.range n,
      (if a = m + 1 ∧ m + 1 < n then
        (if m + 1 = n then (1 : ℤ) else 2) * (if b ≤ m then 1 else 0) else 0)
      = if a = 0 then 0 else 2 * (if b ≤ a - 1 then 1 else 0) := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [if_pos rfl]
      exact Finset.sum_eq_zero fun m _ => if_neg (by omega)
    · rw [if_neg (by omega), Finset.sum_eq_single (a - 1) (fun m _ hm => if_neg (by omega))
        (fun hm => absurd (Finset.mem_range.mpr (by omega)) hm),
        if_pos ⟨by omega, by omega⟩, if_neg (show ¬(a - 1 + 1 = n) by omega)]
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
  · exact Or.inr (Fin.ext (by rw [coe_opp, if_neg h2]; omega))
  · exact Or.inr (Fin.ext (by rw [coe_opp, if_pos h2]; omega))
  · exact Or.inl (Fin.ext (by omega))

lemma ne_of_axis_ne {u v : Fin (2 * n)} (h : axis u ≠ axis v) : u ≠ v := fun hc => h (by rw [hc])

/-- The character coordinates of the signed basis vector indexed by `u`. -/
def wt (u : Fin (2 * n)) : Fin n → ℤ := sgn u • weight n (axis u)
lemma wt_def (u : Fin (2 * n)) : wt u = sgn u • weight n (axis u) := (rfl)

/-- The cocharacter coordinates of twice the signed basis vector indexed by `u`. -/
def cwt (u : Fin (2 * n)) : Fin n → ℤ := sgn u • coweight n (axis u)
lemma cwt_def (u : Fin (2 * n)) : cwt u = sgn u • coweight n (axis u) := (rfl)

@[simp] lemma wt_opp (u : Fin (2 * n)) : wt (opp u) = -wt u := by
  simp only [wt, sgn_opp, axis_opp, neg_smul]

@[simp] lemma cwt_opp (u : Fin (2 * n)) : cwt (opp u) = -cwt u := by
  simp only [cwt, sgn_opp, axis_opp, neg_smul]

/-- The pairing of two signed basis vectors: `2` on the diagonal, `-2` on opposite vectors, and `0`
on different axes. -/
lemma wt_dotProduct_cwt (u v : Fin (2 * n)) :
    wt u ⬝ᵥ cwt v = if u = v then 2 else if u = opp v then -2 else 0 := by
  have h := weight_dotProduct_coweight (n := n) (a := axis u) (b := axis v) (axis_lt u)
  simp only [wt, cwt, smul_dotProduct, dotProduct_smul, smul_eq_mul, h]
  by_cases hax : axis u = axis v
  · rw [if_pos hax]
    rcases eq_or_eq_opp_of_axis_eq hax with rfl | rfl
    · rw [if_pos rfl]
      rcases sgn_eq_one_or_neg_one u with hs | hs <;> rw [hs] <;> norm_num
    · rw [if_neg (opp_ne_self v), if_pos rfl, sgn_opp]
      rcases sgn_eq_one_or_neg_one v with hs | hs <;> rw [hs] <;> norm_num
  · rw [if_neg hax, if_neg (ne_of_axis_ne hax), if_neg (ne_of_axis_ne (by rwa [axis_opp]))]
    ring

@[simp] lemma wt_dotProduct_cwt_self (u : Fin (2 * n)) : wt u ⬝ᵥ cwt u = 2 := by
  rw [wt_dotProduct_cwt, if_pos rfl]

lemma wt_dotProduct_cwt_eq_zero {u v : Fin (2 * n)} (h1 : u ≠ v) (h2 : u ≠ opp v) :
    wt u ⬝ᵥ cwt v = 0 := by
  rw [wt_dotProduct_cwt, if_neg h1, if_neg h2]

lemma wt_dotProduct_cwt_of_axis_ne {u v : Fin (2 * n)} (h : axis u ≠ axis v) :
    wt u ⬝ᵥ cwt v = 0 :=
  wt_dotProduct_cwt_eq_zero (ne_of_axis_ne h) (ne_of_axis_ne (by rwa [axis_opp]))

/-! ## The coroot attached to a pair of signed basis vectors -/

/-- The simple-coroot coordinates of the coroot named by the pair `{u, v}`: the half of
`cwt u + cwt v`, which is integral. When `u = v` this is the short coroot `cwt u`, and otherwise it
is the long coroot `± e_a ± e_b` itself. -/
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
  · rw [if_pos hk, if_pos hk]
    by_cases hs : sgn u = sgn v
    · rw [if_pos hs, if_pos hs.symm, hs]
    · rw [if_neg hs, if_neg fun hc => hs hc.symm]
  · rw [if_neg hk, if_neg hk]
    ring

@[simp] lemma corootOfPair_self (u : Fin (2 * n)) : corootOfPair u u = cwt u := by
  funext k
  have hlt := axis_lt u
  simp only [corootOfPair, cwt, coweight, Pi.smul_apply, smul_eq_mul]
  by_cases hk : (k : ℕ) + 1 = n
  · rw [if_pos hk, if_pos hk, if_pos (show axis u ≤ (k : ℕ) by omega)]
    simp
  · rw [if_neg hk, if_neg hk]
    ring

/-- **The integral form of the halving.** -/
lemma corootOfPair_add_self (u v : Fin (2 * n)) :
    corootOfPair u v + corootOfPair u v = cwt u + cwt v := by
  funext k
  have hlt := axis_lt u
  have hlt' := axis_lt v
  simp only [corootOfPair, cwt, coweight, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : (k : ℕ) + 1 = n
  · rw [if_pos hk, if_pos hk, if_pos (show axis u ≤ (k : ℕ) by omega),
      if_pos (show axis v ≤ (k : ℕ) by omega)]
    rcases sgn_eq_one_or_neg_one u with h | h <;> rcases sgn_eq_one_or_neg_one v with h' | h' <;>
      rw [h, h'] <;> norm_num
  · rw [if_neg hk, if_neg hk]
    ring

lemma two_smul_corootOfPair (u v : Fin (2 * n)) :
    (2 : ℤ) • corootOfPair u v = cwt u + cwt v := by
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
def cdiff (u v : Fin (2 * n)) : ℕ :=
  if (u : ℕ) ≤ (v : ℕ) then (v : ℕ) - (u : ℕ) else (v : ℕ) + 2 * n - (u : ℕ)

lemma cdiff_lt (u v : Fin (2 * n)) : cdiff u v < 2 * n := by
  have := u.isLt; have := v.isLt
  simp only [cdiff]; split <;> omega

@[simp] lemma cdiff_eq_zero_iff {u v : Fin (2 * n)} : cdiff u v = 0 ↔ u = v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [cdiff, Fin.ext_iff]
  split <;> omega

@[simp] lemma cdiff_shift (u : Fin (2 * n)) (d : Fin n) : cdiff u (shift u d) = (d : ℕ) := by
  have hu := u.isLt
  have hd := d.isLt
  simp only [cdiff, coe_shift]
  split_ifs <;> omega

lemma shift_cdiff {u v : Fin (2 * n)} (h : cdiff u v < n) : shift u ⟨cdiff u v, h⟩ = v := by
  have hu := u.isLt
  have hv := v.isLt
  refine Fin.ext ?_
  simp only [coe_shift, cdiff]
  split_ifs <;> omega

lemma cdiff_add_cdiff {u v : Fin (2 * n)} (h : u ≠ v) : cdiff u v + cdiff v u = 2 * n := by
  have hu := u.isLt
  have hv := v.isLt
  have : (u : ℕ) ≠ (v : ℕ) := fun hc => h (Fin.ext hc)
  simp only [cdiff]
  split_ifs <;> omega

lemma cdiff_eq_rank_iff {u v : Fin (2 * n)} : cdiff u v = n ↔ u = opp v := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [cdiff, Fin.ext_iff, coe_opp]
  split_ifs <;> omega

/-- A pair of signed basis vectors naming a root: either equal, for a short root, or on distinct
axes, for a long root. -/
def IsPair (u v : Fin (2 * n)) : Prop := u = v ∨ axis u ≠ axis v

lemma IsPair.cdiff_ne {u v : Fin (2 * n)} (h : IsPair u v) (huv : u ≠ v) :
    cdiff u v ≠ 0 ∧ cdiff u v ≠ n := by
  have hax : axis u ≠ axis v := h.resolve_left huv
  refine ⟨fun hc => huv (cdiff_eq_zero_iff.mp hc), fun hc => hax ?_⟩
  rw [cdiff_eq_rank_iff.mp hc, axis_opp]

lemma isPair_shift (u : Fin (2 * n)) (d : Fin n) : IsPair u (shift u d) := by
  rcases Nat.eq_zero_or_pos (d : ℕ) with hd | hd
  · exact Or.inl (shift_eq_self hd).symm
  · exact Or.inr fun hc => axis_shift_ne (n := n) (u := u) (d := d) (by omega) hc.symm

/-- The canonical index in `Fin (2 * n) × Fin n` of the root named by a pair of signed basis
vectors: whichever of the two cyclic offsets lands in `Fin n`. -/
def index (u v : Fin (2 * n)) : Fin (2 * n) × Fin n :=
  if h : cdiff u v < n then (u, ⟨cdiff u v, h⟩)
  else if h' : cdiff v u < n then (v, ⟨cdiff v u, h'⟩)
  else (u, ⟨0, rank_pos u⟩)

@[simp] lemma index_shift (z : Fin (2 * n) × Fin n) : index z.1 (shift z.1 z.2) = z := by
  have h := cdiff_shift z.1 z.2
  rw [index, dif_pos (by rw [h]; exact z.2.isLt)]
  exact Prod.ext rfl (Fin.ext h)

lemma index_comm {u v : Fin (2 * n)} (h : IsPair u v) : index u v = index v u := by
  rcases eq_or_ne u v with rfl | huv
  · rfl
  obtain ⟨h0, hn⟩ := h.cdiff_ne huv
  have hsum := cdiff_add_cdiff huv
  have hlt := cdiff_lt u v
  by_cases h1 : cdiff u v < n
  · rw [index, dif_pos h1, index, dif_neg (by omega), dif_pos h1]
  · rw [index, dif_neg h1, dif_pos (by omega), index, dif_pos (by omega)]

lemma shift_index {u v : Fin (2 * n)} (h : IsPair u v) :
    ((index u v).1 = u ∧ shift (index u v).1 (index u v).2 = v) ∨
      ((index u v).1 = v ∧ shift (index u v).1 (index u v).2 = u) := by
  rcases eq_or_ne u v with rfl | huv
  · have hlt : cdiff u u < n := by rw [cdiff_eq_zero_iff.mpr rfl]; exact rank_pos u
    exact Or.inl ⟨by rw [index, dif_pos hlt], by rw [index, dif_pos hlt]; exact shift_cdiff hlt⟩
  obtain ⟨h0, hn⟩ := h.cdiff_ne huv
  have hsum := cdiff_add_cdiff huv
  have hlt := cdiff_lt u v
  by_cases h1 : cdiff u v < n
  · exact Or.inl ⟨by rw [index, dif_pos h1], by rw [index, dif_pos h1]; exact shift_cdiff h1⟩
  · have h2 : cdiff v u < n := by omega
    exact Or.inr ⟨by rw [index, dif_neg h1, dif_pos h2],
      by rw [index, dif_neg h1, dif_pos h2]; exact shift_cdiff h2⟩

/-! ## Roots and coroots -/

/-- The character coordinates of the root named by a pair of signed basis vectors. -/
def rootOfPair (u v : Fin (2 * n)) : Fin n → ℤ := if u = v then wt u else wt u + wt v

lemma rootOfPair_comm (u v : Fin (2 * n)) : rootOfPair u v = rootOfPair v u := by
  rcases eq_or_ne u v with rfl | huv
  · rfl
  · rw [rootOfPair, rootOfPair, if_neg huv, if_neg (Ne.symm huv), add_comm]

@[simp] lemma rootOfPair_self (u : Fin (2 * n)) : rootOfPair u u = wt u := by
  rw [rootOfPair, if_pos rfl]

@[simp] lemma rootOfPair_of_ne {u v : Fin (2 * n)} (h : u ≠ v) : rootOfPair u v = wt u + wt v := by
  rw [rootOfPair, if_neg h]

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
    2 * (wt u ⬝ᵥ corootOfPair p q) = wt u ⬝ᵥ cwt p + wt u ⬝ᵥ cwt q := by
  rw [← dotProduct_add, ← corootOfPair_add_self p q, dotProduct_add]
  ring

lemma rootOfPair_dotProduct_corootOfPair {u v : Fin (2 * n)} (h : IsPair u v) :
    rootOfPair u v ⬝ᵥ corootOfPair u v = 2 := by
  rcases eq_or_ne u v with rfl | huv
  · rw [rootOfPair_self, corootOfPair_self, wt_dotProduct_cwt_self]
  · have hax : axis u ≠ axis v := h.resolve_left huv
    have h1 := two_mul_dotProduct_corootOfPair u u v
    have h2 := two_mul_dotProduct_corootOfPair v u v
    rw [wt_dotProduct_cwt_self, wt_dotProduct_cwt_of_axis_ne hax] at h1
    rw [wt_dotProduct_cwt_self, wt_dotProduct_cwt_of_axis_ne (Ne.symm hax)] at h2
    rw [rootOfPair_of_ne huv, add_dotProduct]
    omega

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
  rw [reflMap, if_pos rfl]

lemma reflMap_snd (h : q ≠ p) : reflMap p q q = opp p := by
  rw [reflMap, if_neg h, if_pos rfl]

lemma reflMap_opp_fst (h : opp p ≠ q) : reflMap p q (opp p) = if p = q then p else q := by
  rw [reflMap, if_neg (opp_ne_self p), if_neg h, if_pos rfl]

lemma reflMap_opp_snd (h1 : opp q ≠ p) (h2 : opp q ≠ opp p) : reflMap p q (opp q) = p := by
  rw [reflMap, if_neg h1, if_neg (opp_ne_self q), if_neg h2, if_pos rfl]

lemma reflMap_of_ne {u : Fin (2 * n)} (h1 : u ≠ p) (h2 : u ≠ q) (h3 : u ≠ opp p) (h4 : u ≠ opp q) :
    reflMap p q u = u := by
  rw [reflMap, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

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
      rw [reflMap_fst, if_pos rfl, reflMap_opp_fst hop, if_pos rfl]
    · by_cases h2 : u = opp p
      · subst h2
        rw [reflMap_opp_fst hop, if_pos rfl, reflMap_fst, if_pos rfl]
      · rw [reflMap_of_ne h1 h1 h2 h2, reflMap_of_ne h1 h1 h2 h2]
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    by_cases c1 : u = p
    · subst c1
      rw [reflMap_fst, if_neg h1, reflMap_opp_snd h7 h8]
    by_cases c2 : u = q
    · subst c2
      rw [reflMap_snd h3, reflMap_opp_fst h5, if_neg h1]
    by_cases c3 : u = opp p
    · subst c3
      rw [reflMap_opp_fst h5, if_neg h1, reflMap_snd h3]
    by_cases c4 : u = opp q
    · subst c4
      rw [reflMap_opp_snd h7 h8, reflMap_fst, if_neg h1]
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
      rw [reflMap_opp_fst hop, if_pos rfl, reflMap_fst, if_pos rfl, opp_opp]
    · by_cases h2 : u = opp p
      · subst h2
        rw [opp_opp, reflMap_fst, if_pos rfl, reflMap_opp_fst hop, if_pos rfl]
      · have h1' : opp u ≠ p := fun hc => h2 ((key u p).mp hc)
        have h2' : opp u ≠ opp p := fun hc => h1 (by simpa using congrArg opp hc)
        rw [reflMap_of_ne h1' h1' h2' h2', reflMap_of_ne h1 h1 h2 h2]
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    by_cases c1 : u = p
    · subst c1
      rw [reflMap_opp_fst h5, if_neg h1, reflMap_fst, if_neg h1, opp_opp]
    by_cases c2 : u = q
    · subst c2
      rw [reflMap_opp_snd h7 h8, reflMap_snd h3, opp_opp]
    by_cases c3 : u = opp p
    · subst c3
      rw [opp_opp, reflMap_fst, if_neg h1, reflMap_opp_fst h5, if_neg h1]
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
lemma wt_reflMap (h : IsPair p q) (u : Fin (2 * n)) :
    wt (reflMap p q u) = wt u - (wt u ⬝ᵥ corootOfPair p q) • rootOfPair p q := by
  -- A short root only swaps `p` and `opp p`; all other signed basis vectors are fixed and pair
  -- trivially with its coroot.
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    rw [corootOfPair_self, rootOfPair_self]
    by_cases c1 : u = p
    · rw [c1, reflMap_fst, if_pos rfl, wt_dotProduct_cwt_self, wt_opp]
      module
    · by_cases c2 : u = opp p
      · rw [c2, reflMap_opp_fst hop, if_pos rfl, wt_opp, neg_dotProduct,
          wt_dotProduct_cwt_self]
        module
      · rw [reflMap_of_ne c1 c1 c2 c2, wt_dotProduct_cwt_eq_zero c1 c2]
        module
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    have hpq' : wt p ⬝ᵥ cwt q = 0 := wt_dotProduct_cwt_of_axis_ne hax
    have hqp : wt q ⬝ᵥ cwt p = 0 := wt_dotProduct_cwt_of_axis_ne (Ne.symm hax)
    rw [rootOfPair_of_ne h1]
    -- For a long root, split the signed basis vectors into `p`, `q`, their opposites, and the
    -- complement. The pairing is respectively `1`, `1`, `-1`, `-1`, and `0`.
    by_cases c1 : u = p
    · have hval := two_mul_dotProduct_corootOfPair p p q
      rw [wt_dotProduct_cwt_self, hpq'] at hval
      rw [c1, show wt p ⬝ᵥ corootOfPair p q = 1 by omega, reflMap_fst, if_neg h1,
        wt_opp]
      module
    by_cases c2 : u = q
    · have hval := two_mul_dotProduct_corootOfPair q p q
      rw [wt_dotProduct_cwt_self, hqp] at hval
      rw [c2, show wt q ⬝ᵥ corootOfPair p q = 1 by omega, reflMap_snd h3, wt_opp]
      module
    by_cases c3 : u = opp p
    · have e1 : wt (opp p) ⬝ᵥ cwt p = -2 := by
        rw [wt_opp, neg_dotProduct, wt_dotProduct_cwt_self]
      have e2 : wt (opp p) ⬝ᵥ cwt q = 0 := by rw [wt_opp, neg_dotProduct, hpq', neg_zero]
      have hval := two_mul_dotProduct_corootOfPair (opp p) p q
      rw [e1, e2] at hval
      rw [c3, show wt (opp p) ⬝ᵥ corootOfPair p q = -1 by omega,
        reflMap_opp_fst h5, if_neg h1, wt_opp]
      module
    by_cases c4 : u = opp q
    · have e1 : wt (opp q) ⬝ᵥ cwt p = 0 := by rw [wt_opp, neg_dotProduct, hqp, neg_zero]
      have e2 : wt (opp q) ⬝ᵥ cwt q = -2 := by
        rw [wt_opp, neg_dotProduct, wt_dotProduct_cwt_self]
      have hval := two_mul_dotProduct_corootOfPair (opp q) p q
      rw [e1, e2] at hval
      rw [c4, show wt (opp q) ⬝ᵥ corootOfPair p q = -1 by omega,
        reflMap_opp_snd h7 h8, wt_opp]
      module
    · have hval := two_mul_dotProduct_corootOfPair u p q
      rw [wt_dotProduct_cwt_eq_zero c1 c3, wt_dotProduct_cwt_eq_zero c2 c4] at hval
      rw [show wt u ⬝ᵥ corootOfPair p q = 0 by omega, reflMap_of_ne c1 c2 c3 c4]
      module

/-- **The reflection formula on the double of a single signed basis vector.** -/
lemma cwt_reflMap (h : IsPair p q) (u : Fin (2 * n)) :
    cwt (reflMap p q u) = cwt u - (rootOfPair p q ⬝ᵥ cwt u) • corootOfPair p q := by
  -- The short-root case has the same two-point orbit as `wt_reflMap`, now on the doubled
  -- coweight coordinates.
  rcases eq_or_ne p q with rfl | hpq
  · have hop := opp_ne_self p
    rw [corootOfPair_self, rootOfPair_self]
    by_cases c1 : u = p
    · rw [c1, reflMap_fst, if_pos rfl, wt_dotProduct_cwt_self, cwt_opp]
      module
    · by_cases c2 : u = opp p
      · rw [c2, reflMap_opp_fst hop, if_pos rfl, cwt_opp, dotProduct_neg,
          wt_dotProduct_cwt_self]
        module
      · rw [reflMap_of_ne c1 c1 c2 c2, wt_dotProduct_cwt_eq_zero (Ne.symm c1)
          (fun hc => c2 (by rw [hc, opp_opp]))]
        module
  · have hax : axis p ≠ axis q := h.resolve_left hpq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    have hpq' : wt p ⬝ᵥ cwt q = 0 := wt_dotProduct_cwt_of_axis_ne hax
    have hqp : wt q ⬝ᵥ cwt p = 0 := wt_dotProduct_cwt_of_axis_ne (Ne.symm hax)
    have hsum := two_smul_corootOfPair p q
    have hneg : ((-2 : ℤ)) • corootOfPair p q = -(cwt p + cwt q) := by
      rw [← hsum, show ((-2 : ℤ)) • corootOfPair p q =
        -((2 : ℤ) • corootOfPair p q) from by module]
    rw [rootOfPair_of_ne h1]
    -- As above, the long-root reflection has four exceptional signed basis vectors. Their
    -- root-pairing values are `2`, `2`, `-2`, and `-2`; the complement pairs to zero.
    by_cases c1 : u = p
    · rw [c1, add_dotProduct, wt_dotProduct_cwt_self, hqp, reflMap_fst, if_neg h1, cwt_opp,
        show (2 : ℤ) + 0 = 2 by ring, hsum]
      module
    by_cases c2 : u = q
    · rw [c2, add_dotProduct, hpq', wt_dotProduct_cwt_self, reflMap_snd h3, cwt_opp,
        show (0 : ℤ) + 2 = 2 by ring, hsum]
      module
    by_cases c3 : u = opp p
    · have e1 : wt p ⬝ᵥ cwt (opp p) = -2 := by
        rw [cwt_opp, dotProduct_neg, wt_dotProduct_cwt_self]
      have e2 : wt q ⬝ᵥ cwt (opp p) = 0 := by rw [cwt_opp, dotProduct_neg, hqp, neg_zero]
      rw [c3, add_dotProduct, e1, e2, reflMap_opp_fst h5, if_neg h1,
        show -(2 : ℤ) + 0 = -2 by ring, hneg, cwt_opp]
      module
    by_cases c4 : u = opp q
    · have e1 : wt p ⬝ᵥ cwt (opp q) = 0 := by rw [cwt_opp, dotProduct_neg, hpq', neg_zero]
      have e2 : wt q ⬝ᵥ cwt (opp q) = -2 := by
        rw [cwt_opp, dotProduct_neg, wt_dotProduct_cwt_self]
      rw [c4, add_dotProduct, e1, e2, reflMap_opp_snd h7 h8,
        show (0 : ℤ) + -2 = -2 by ring, hneg, cwt_opp]
      module
    · rw [add_dotProduct,
        wt_dotProduct_cwt_eq_zero (Ne.symm c1) (fun hc => c3 (by rw [hc, opp_opp])),
        wt_dotProduct_cwt_eq_zero (Ne.symm c2) (fun hc => c4 (by rw [hc, opp_opp])),
        reflMap_of_ne c1 c2 c3 c4]
      module

end Refl

/-! ## Recovering the index from the root -/

/-- The signed basis vectors occurring in a root are exactly those pairing to `2` with it. -/
lemma rootIdx_dotProduct_cwt_eq_two_iff (z : Fin (2 * n) × Fin n) (m : Fin (2 * n)) :
    rootIdx z ⬝ᵥ cwt m = 2 ↔ (m = z.1 ∨ m = shift z.1 z.2) := by
  have hpair : IsPair z.1 (shift z.1 z.2) := isPair_shift z.1 z.2
  rcases eq_or_ne z.1 (shift z.1 z.2) with heq | hne
  · rw [rootIdx, ← heq, rootOfPair_self, wt_dotProduct_cwt]
    constructor
    · intro hc
      by_cases hc1 : z.1 = m
      · exact Or.inl hc1.symm
      · rw [if_neg hc1] at hc
        split_ifs at hc
        omega
    · rintro (rfl | rfl)
      · rw [if_pos rfl]
      · rw [if_pos rfl]
  · have hax : axis z.1 ≠ axis (shift z.1 z.2) := hpair.resolve_left hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    rw [rootIdx, rootOfPair_of_ne hne, add_dotProduct, wt_dotProduct_cwt, wt_dotProduct_cwt]
    constructor
    · intro hc
      by_cases hm1 : z.1 = m
      · exact Or.inl hm1.symm
      by_cases hm2 : shift z.1 z.2 = m
      · exact Or.inr hm2.symm
      rw [if_neg hm1, if_neg hm2] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | hm)
      · rw [if_pos rfl, if_neg h3, if_neg h4]
        ring
      · rw [hm, if_pos rfl, if_neg h1, if_neg h2]
        ring

/-- The signed basis vectors occurring in a coroot, detected by a doubled pairing so that both the
short and the long case are covered. -/
lemma two_mul_wt_dotProduct_corootIdx_iff (z : Fin (2 * n) × Fin n) (m : Fin (2 * n)) :
    (2 * (wt m ⬝ᵥ corootIdx z) = 4 ∨ 2 * (wt m ⬝ᵥ corootIdx z) = 2) ↔
      (m = z.1 ∨ m = shift z.1 z.2) := by
  have hpair : IsPair z.1 (shift z.1 z.2) := isPair_shift z.1 z.2
  have hval : 2 * (wt m ⬝ᵥ corootIdx z) = wt m ⬝ᵥ cwt z.1 + wt m ⬝ᵥ cwt (shift z.1 z.2) :=
    two_mul_dotProduct_corootOfPair m z.1 (shift z.1 z.2)
  rw [hval, wt_dotProduct_cwt, wt_dotProduct_cwt]
  rcases eq_or_ne z.1 (shift z.1 z.2) with heq | hne
  · rw [← heq]
    constructor
    · intro hc
      by_cases hm : m = z.1
      · exact Or.inl hm
      rw [if_neg hm] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | rfl)
      · rw [if_pos rfl]
        omega
      · rw [if_pos rfl]
        omega
  · have hax : axis z.1 ≠ axis (shift z.1 z.2) := hpair.resolve_left hne
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := long_ne hax
    constructor
    · intro hc
      by_cases hm1 : m = z.1
      · exact Or.inl hm1
      by_cases hm2 : m = shift z.1 z.2
      · exact Or.inr hm2
      rw [if_neg hm1, if_neg hm2] at hc
      split_ifs at hc <;> omega
    · rintro (rfl | rfl)
      · rw [if_pos rfl, if_neg hne, if_neg h2]
        omega
      · rw [if_pos rfl, if_neg h3, if_neg h4]
        omega

/-- Two indices naming the same pair of signed basis vectors are equal. -/
lemma eq_of_forall_mem_iff {z z' : Fin (2 * n) × Fin n}
    (h : ∀ m, (m = z.1 ∨ m = shift z.1 z.2) ↔ (m = z'.1 ∨ m = shift z'.1 z'.2)) : z = z' := by
  have e1 : cdiff z.1 (shift z.1 z.2) = (z.2 : ℕ) := cdiff_shift _ _
  have e2 : cdiff z'.1 (shift z'.1 z'.2) = (z'.2 : ℕ) := cdiff_shift _ _
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
      have hsum := cdiff_add_cdiff hne'
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
