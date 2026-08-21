/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootLength
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Basic

public section

/-!
# Simple-root coordinates and squared lengths of the pinned `G₂` roots

`TauCeti.DynkinType.g2SimplyConnectedRootDatum` tabulates its twelve roots in the
fundamental-weight basis and its twelve coroots in the simple-coroot basis. Neither table displays
the *simple-root* coordinates of a root, and neither displays how long a root is. Both are needed
by a consumer that has to distinguish long roots from short ones, which is what a
characteristic-three special isogeny of type `G₂` does.

This file supplies the two missing tables, in the pinned index order

```text
α₁,  α₂,  α₁ + α₂,  2 α₁ + α₂,  3 α₁ + α₂,  3 α₁ + 2 α₂
```

on the positive roots, index `k + 6` being the negative of index `k`.

`TauCeti.DynkinType.g2Length` is normalised as `TauCeti.DynkinType.rootLength` normalises the
simple roots: `1` on the six short roots `± α₁, ± (α₁ + α₂), ± (2 α₁ + α₂)` and `3` on the six long
ones `± α₂, ± (3 α₁ + α₂), ± (3 α₁ + 2 α₂)`. That normalisation is not a stipulation:
`TauCeti.DynkinType.g2Length_mul_g2Coroot` derives the whole table from the two simple lengths by
expanding `β∨ = 2 β / (β, β)` on the simple coroots, and
`TauCeti.DynkinType.eq_g2Length_of_mul_g2Coroot` shows those equations determine it.

## Main definitions

* `TauCeti.DynkinType.g2Coeff`: the simple-root coordinates of the twelve roots.
* `TauCeti.DynkinType.g2Length`: their squared lengths.

## Main results

* `TauCeti.DynkinType.g2Root_eq_smul_add_smul` and `TauCeti.DynkinType.eq_g2Coeff_of_root_eq`: the
  coordinate table expands the roots on the two simple ones, and is the only table that does.
* `TauCeti.DynkinType.g2Length_mul_g2Coroot` and
  `TauCeti.DynkinType.eq_g2Length_of_mul_g2Coroot`: the length table is the one forced by the two
  simple lengths.
* `TauCeti.DynkinType.g2Length_castLE`: on the two simple roots it is
  `TauCeti.DynkinType.rootLength`.
* `TauCeti.DynkinType.isLongSimpleRoot_iff_g2Length_eq_three` and
  `TauCeti.DynkinType.g2Length_castLE_eq_one_iff`: the long simple root is the one of length three
  and the short one the one of length one.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate IX. The tables are the type `G₂` input asked for by the "special isogenies in
characteristics two and three" bullet of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`,
matching the rank-two type `B` tables of
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/B/RankTwo.lean`.
-/

namespace TauCeti.DynkinType

open Function

/-- The simple-root coordinates of the twelve roots of the pinned `G₂` datum, in the index order of
`TauCeti.DynkinType.g2Root`. -/
@[expose] def g2Coeff : Fin 12 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![1, 1], ![2, 1], ![3, 1], ![3, 2],
    ![-1, 0], ![0, -1], ![-1, -1], ![-2, -1], ![-3, -1], ![-3, -2]]

/-- Each tabulated root is the tabulated combination of the two simple roots. -/
theorem g2Root_eq_smul_add_smul (k : Fin 12) :
    g2Root k = g2Coeff k 0 • g2Root 0 + g2Coeff k 1 • g2Root 1 := by
  decide +revert

private lemma g2_smul_add_smul_inj {a b a' b' : ℤ}
    (h : a • g2Root 0 + b • g2Root 1 = a' • g2Root 0 + b' • g2Root 1) : a = a' ∧ b = b' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [g2Root, Function.Embedding.coeFn_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

/-- The two simple roots are linearly independent, so the expansion above determines the
coefficients. -/
theorem eq_g2Coeff_of_root_eq {k : Fin 12} {c : Fin 2 → ℤ}
    (h : g2Root k = c 0 • g2Root 0 + c 1 • g2Root 1) : c = g2Coeff k := by
  obtain ⟨h0, h1⟩ := g2_smul_add_smul_inj (h.symm.trans (g2Root_eq_smul_add_smul k))
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The six positive roots come first: their simple-root coordinates are nonnegative. -/
theorem g2Coeff_nonneg (k : Fin 12) (hk : (k : ℕ) < 6) (i : Fin 2) : 0 ≤ g2Coeff k i := by
  decide +revert

/-- The six negative roots come last: their simple-root coordinates are nonpositive. -/
theorem g2Coeff_nonpos (k : Fin 12) (hk : 6 ≤ (k : ℕ)) (i : Fin 2) : g2Coeff k i ≤ 0 := by
  decide +revert

/-- The last six roots are the negatives of the first six, in simple-root coordinates. -/
@[simp] theorem g2Coeff_add_six (k : Fin 12) : g2Coeff (k + 6) = -g2Coeff k := by
  decide +revert

/-- The squared lengths of the twelve roots of the pinned `G₂` datum, normalised as
`TauCeti.DynkinType.rootLength` normalises the simple ones: `1` on the six short roots
`± α₁, ± (α₁ + α₂), ± (2 α₁ + α₂)` and `3` on the six long ones
`± α₂, ± (3 α₁ + α₂), ± (3 α₁ + 2 α₂)`. -/
@[expose] def g2Length : Fin 12 → ℤ := ![1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3]

/-- **The length table is the one forced by the simple lengths.** Writing `β = Σ cᵢ αᵢ` and
`β∨ = Σ dᵢ αᵢ∨`, the identity `β∨ = 2 β / (β, β)` reads `ℓ(β) dᵢ = cᵢ ℓ(αᵢ)` once both sides are
expanded on the simple coroots. -/
theorem g2Length_mul_g2Coroot (k : Fin 12) (i : Fin 2) :
    g2Length k * g2Coroot k i = g2Coeff k i * G2.rootLength i := by
  rw [rootLength_G2]
  decide +revert

private lemma g2_exists_g2Coroot_ne_zero (k : Fin 12) : ∃ i, g2Coroot k i ≠ 0 := by decide +revert

/-- No coroot vanishes, so `TauCeti.DynkinType.g2Length_mul_g2Coroot` determines the length
table. -/
theorem eq_g2Length_of_mul_g2Coroot {k : Fin 12} {c : ℤ}
    (h : ∀ i, c * g2Coroot k i = g2Coeff k i * G2.rootLength i) : c = g2Length k := by
  obtain ⟨i, hi⟩ := g2_exists_g2Coroot_ne_zero k
  exact mul_right_cancel₀ hi ((h i).trans (g2Length_mul_g2Coroot k i).symm)

/-- On the two simple roots the length table is `TauCeti.DynkinType.rootLength`. -/
@[simp] theorem g2Length_castLE (i : Fin 2) :
    g2Length (Fin.castLE (by omega) i) = G2.rootLength i := by
  rw [rootLength_G2]
  decide +revert

/-- A root and its negative have the same length. -/
@[simp] theorem g2Length_add_six (k : Fin 12) : g2Length (k + 6) = g2Length k := by
  decide +revert

/-- Every root of the pinned `G₂` datum is short or long, of squared length `1` or `3`. -/
theorem g2Length_eq_one_or_eq_three (k : Fin 12) : g2Length k = 1 ∨ g2Length k = 3 := by
  decide +revert

/-- Every root of the pinned `G₂` datum has positive squared length. -/
theorem g2Length_pos (k : Fin 12) : 0 < g2Length k := by
  decide +revert

/-- **The long simple root is the one of length three**, which is the convention
`TauCeti.DynkinType.rootLength` fixes and the one a length-exchanging map is pinned against. -/
theorem isLongSimpleRoot_iff_g2Length_eq_three (i : Fin 2) :
    G2.IsLongSimpleRoot i ↔ g2Length (Fin.castLE (by omega) i) = 3 := by
  rw [isLongSimpleRoot_G2]
  fin_cases i
  · norm_num [g2Length]
  · norm_num [g2Length]
    decide

/-- **The short simple root is the one of length one.** This is the form in which a
characteristic-three special isogeny states which of its two rescaling exponents it attaches to
which node. -/
theorem g2Length_castLE_eq_one_iff (i : Fin 2) :
    g2Length (Fin.castLE (by omega) i) = 1 ↔ ¬ G2.IsLongSimpleRoot i := by
  rw [isLongSimpleRoot_iff_g2Length_eq_three]
  rcases g2Length_eq_one_or_eq_three (Fin.castLE (by omega : (2 : ℕ) ≤ 12) i) with h | h <;>
    rw [h] <;> norm_num

end TauCeti.DynkinType
