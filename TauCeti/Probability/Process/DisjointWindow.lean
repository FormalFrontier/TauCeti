/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.BlockAverage
import Mathlib.Tactic.Ring

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

## The moving selection

The same windows also appear as a *moving* selection, in the shape the `L²` convergence theorems
quantify over: `disjointWindow c` is the family `n ↦ (j ↦ window (n + 1) c j)`, so at each length
factor `c` reads `[(c + 1)(n + 1), (c + 2)(n + 1))`. Two facts make it usable there —
`disjointWindow_injective` at each length, with `disjointWindow_eventually_injective` the eventual
form those theorems take, and `disjointWindow_ne` for disjointness across factors.

That combination is what fixed starts cannot supply: windows from two distinct fixed starts overlap
once the common length exceeds the gap between the starts, whereas these move outward as the length
grows. The generic fixed-start selection is `fixedStart` in `Process/BlockAverage.lean`.

## References

Nothing here involves a measure or the `L²` theory: the module is index arithmetic plus
block-average algebra, which is why it sits with the process API rather than under
`Exchangeability/L2/`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the `L²` averaging library and
  the standard-Borel de Finetti route, supporting the finite-block conditional factorization.
-/

public section

open Filter Finset

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

/-- **The windows sit above the initial block.** Every window index exceeds every index of the
first `N` coordinates, so an initial selection and a window selection never collide. -/
theorem lt_window {N i j j' : ℕ} (hj : j < N) : j < window N i j' := by
  have : N ≤ (i + 1) * N := Nat.le_mul_of_pos_left _ (by omega)
  simp only [window_def]
  omega

/-- **The windows are ordered.** An index inside window `i` precedes every index of any later
window `i'`, provided the offset `j` stays inside the window. -/
theorem window_lt_window {N : ℕ} {i i' j j' : ℕ} (hj : j < N) (hi : i < i') :
    window N i j < window N i' j' := by
  have h1 : (i + 1) * N + j < (i + 1) * N + N := by omega
  have h2 : (i + 1) * N + N = (i + 2) * N := by ring
  have h3 : (i + 2) * N ≤ (i' + 1) * N := Nat.mul_le_mul_right _ (by omega)
  simp only [window_def]
  omega

/-- **A tuple reads the windows in order.** Reading factor `i` at position `js i` of *its own*
window gives a strictly monotone selection: the windows are ordered, so the factor index alone
decides the order, whatever position each factor reads. -/
theorem window_selection_strictMono {m N : ℕ} (js : Fin m → Fin N) :
    StrictMono fun i : Fin m => window N (i : ℕ) (js i : ℕ) := fun _ _ hab =>
  window_lt_window (js _).isLt (by exact_mod_cast hab)

/-- **Distinct coordinates of a tuple land in distinct windows.** Since the windows are pairwise
disjoint, the selection `i ↦ window N i (js i)` is injective for every tuple `js` — immediate from
`window_selection_strictMono`. -/
theorem window_selection_injective {m N : ℕ} (js : Fin m → Fin N) :
    Function.Injective fun i : Fin m => window N (i : ℕ) (js i : ℕ) :=
  (window_selection_strictMono js).injective

/-- **The disjoint-window instance.** This specialises `prod_blockAverage_eq_expect`, imported from
`Process/BlockAverage.lean`, to the windows `window N i`, where every tuple is an injective
selection by `window_selection_injective`. -/
theorem prod_blockAverage_window_eq_expect {m N : ℕ} (Y : Fin m → ℕ → Ω → ℝ) (ω : Ω) :
    (∏ i : Fin m, blockAverage (Y i) (fun j : Fin N => window N (i : ℕ) (j : ℕ)) ω)
      = 𝔼 js : Fin m → Fin N, ∏ i : Fin m, Y i (window N (i : ℕ) (js i : ℕ)) ω :=
  prod_blockAverage_eq_expect Y (fun i j => window N (i : ℕ) (j : ℕ)) ω

/-! ### The disjoint-window selection

The moving selection a block factorization needs: at each length, distinct factors read disjoint
windows. The generic fixed-start selection lives with `blockAverage` in
`Probability/Process/BlockAverage.lean`. -/

/-- The **disjoint-window selection**: at length `n + 1`, factor `c` reads the window
`window (n + 1) c`, occupying `[(c + 1)(n + 1), (c + 2)(n + 1))`. -/
def disjointWindow (c : ℕ) : ∀ n : ℕ, Fin (n + 1) → ℕ :=
  fun n j => window (n + 1) c (j : ℕ)

@[simp]
theorem disjointWindow_apply (c n : ℕ) (j : Fin (n + 1)) :
    disjointWindow c n j = window (n + 1) c (j : ℕ) := (rfl)

/-- Each disjoint window is an injective selection at each length. -/
theorem disjointWindow_injective (c n : ℕ) : Function.Injective (disjointWindow c n) := by
  intro a b hab
  simp only [disjointWindow_apply, window_def] at hab
  exact Fin.ext (Nat.add_left_cancel hab)

/-- The eventual form, as the moving-selection theorems take it. -/
theorem disjointWindow_eventually_injective (c : ℕ) :
    ∀ᶠ n in atTop, Function.Injective (disjointWindow c n) :=
  Eventually.of_forall (disjointWindow_injective c)

/-- **Distinct factors never collide.** The windows of two different factors are disjoint at every
length, which is exactly what fixed starts cannot provide. -/
theorem disjointWindow_ne {c c' : ℕ} (h : c ≠ c') (n : ℕ) (j j' : Fin (n + 1)) :
    disjointWindow c n j ≠ disjointWindow c' n j' := by
  simp only [disjointWindow_apply]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact (window_lt_window j.isLt hlt).ne
  · exact (window_lt_window j'.isLt hlt).ne'

end Probability

end TauCeti

end
