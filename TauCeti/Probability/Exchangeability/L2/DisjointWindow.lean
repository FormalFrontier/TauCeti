/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages

/-!
# Expanding a product of averages over disjoint windows

Writing `window N i j = (i + 1) * N + j` for the `i`-th block of `N` consecutive indices, a product
of block averages over these windows expands as an average of products over tuples:

```text
∏ i, blockAverage (Y i) (window N i) = 𝔼 js, ∏ i, Y i (window N i (js i))
```

Two facts make this the right shape for the block factorization.

*The expansion is exact.* It is `Fintype.prod_sum` together with the normalisation
`(N ^ m)⁻¹ = ∏ i, (N : ℝ)⁻¹`, so no error term appears.

*Every tuple is an injective selection.* The windows are pairwise disjoint —
`window N i j < window N i' j'` whenever `i < i'` **and** `j < N` — so distinct coordinates of a
tuple, whose entries are indices in `Fin N`, always carry distinct indices
(`window_selection_injective`). This is what removes the diagonal terms that an expansion
over a *single* window would produce, and it is why the factorization can apply a
contractability argument to every term of the average without exception.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the `L²` averaging library and
  the standard-Borel de Finetti route, supporting the finite-block conditional factorization.
-/

public section

open Finset

open scoped BigOperators

namespace TauCeti

namespace Probability

variable {Ω : Type*}

/-- The `i`-th window of `N` consecutive indices, starting after the first `(i + 1) * N` of them.
Shifting past `(i + 1) * N` rather than `i * N` keeps the windows disjoint from each other *and*
from the first `N` indices. -/
def window (N : ℕ) (i : ℕ) (j : ℕ) : ℕ := (i + 1) * N + j

@[simp]
theorem window_def (N i j : ℕ) : window N i j = (i + 1) * N + j := (rfl)

theorem window_lt_window {N : ℕ} {i i' j j' : ℕ} (hj : j < N) (hi : i < i') :
    window N i j < window N i' j' := by
  have h1 : (i + 1) * N + j < (i + 1) * N + N := by omega
  have h2 : (i + 1) * N + N = (i + 2) * N := by ring
  have h3 : (i + 2) * N ≤ (i' + 1) * N := Nat.mul_le_mul_right _ (by omega)
  simp only [window_def]
  omega

/-- **Distinct coordinates of a tuple land in distinct windows.** Since the windows are pairwise
disjoint, the selection `i ↦ window N i (js i)` is injective for every tuple `js`. -/
theorem window_selection_injective {m N : ℕ} (js : Fin m → Fin N) :
    Function.Injective fun i : Fin m => window N (i : ℕ) (js i : ℕ) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h : (a : ℕ) = (b : ℕ) => hne (Fin.ext h)) with h | h
  · exact absurd hab (window_lt_window (js a).isLt h).ne
  · exact absurd hab.symm (window_lt_window (js b).isLt h).ne

/-- **A product of block averages is an average of products.** Purely algebraic: the product of
sums distributes by `Fintype.prod_sum`, and the normalisations multiply. Disjointness of the
selections plays no role here — it matters only for what the individual terms mean. -/
theorem prod_blockAverage_eq_expect {m N : ℕ} (Y : Fin m → ℕ → Ω → ℝ) (k : Fin m → Fin N → ℕ)
    (ω : Ω) :
    (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = 𝔼 js : Fin m → Fin N, ∏ i : Fin m, Y i (k i (js i)) ω := by
  classical
  have hL : (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = ((N : ℝ)⁻¹) ^ m * ∏ i : Fin m, ∑ j : Fin N, Y i (k i j) ω := by
    simp [blockAverage_apply, Finset.prod_mul_distrib]
  rw [hL, Fintype.prod_sum fun i (j : Fin N) => Y i (k i j) ω, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, card_univ, div_eq_inv_mul]
  push_cast
  simp [inv_pow]

/-- **The disjoint-window instance.** The expansion of the previous theorem at the windows
`window N i`, where every tuple is an injective selection by `window_selection_injective`. -/
theorem prod_blockAverage_window_eq_expect {m N : ℕ} (Y : Fin m → ℕ → Ω → ℝ) (ω : Ω) :
    (∏ i : Fin m, blockAverage (Y i) (fun j : Fin N => window N (i : ℕ) (j : ℕ)) ω)
      = 𝔼 js : Fin m → Fin N, ∏ i : Fin m, Y i (window N (i : ℕ) (js i : ℕ)) ω :=
  prod_blockAverage_eq_expect Y (fun i j => window N (i : ℕ) (j : ℕ)) ω

end Probability

end TauCeti

end
