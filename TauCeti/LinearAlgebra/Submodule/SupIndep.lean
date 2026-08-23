/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.SupIndep

/-!
# An independent family of submodules has no proper refinement

Let `q : ι → Submodule R M` be an independent family and let `p : ι → Submodule R M` be a family
lying inside it termwise, `p i ≤ q i`. If the two families have the same supremum, then they are
equal: `p i = q i` for every `i`.

The argument is the usual uniqueness of a decomposition. An element `x` of `q i` lies in the common
supremum, so it splits as `x = a + b` with `a ∈ p i` and `b` in the supremum of the other `p j`.
Then `b = x - a` lies in `q i` as well, while it lies in the supremum of the other `q j`, and
independence forces `b = 0`.

This is the step that upgrades a coarse decomposition into a fine one: when a module is written as
the supremum of a family that is known to be *refined* by an independent family, each member of the
independent family is pinned down exactly. It is used for the weight spaces of a tensor product of
Lie modules in `TauCeti/Algebra/Lie/Weights/TensorProduct.lean`, where the fine family is the family
of generalized weight spaces of the tensor product and the coarse one is built from pure tensors of
weight vectors.

## Main results

* `TauCeti.eq_of_le_of_iSup_eq_iSup`: a family lying termwise inside an independent family and
  having the same supremum coincides with it.
-/

public section

namespace TauCeti

variable {ι : Type*} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **An independent family of submodules has no proper refinement with the same supremum.** If
`p i ≤ q i` for every `i`, the family `q` is independent, and the two families have the same
supremum, then `p i = q i`.

Independence of `q` is essential and not a convenience: for `p = ![⊥, ⊥]` and `q = ![S, S]` with
`S ≠ ⊥` the hypothesis `⨆ p = ⨆ q` fails, but replacing the first `⊥` by `S` gives a family with
the same supremum as `q` and a strictly smaller second term. -/
theorem eq_of_le_of_iSup_eq_iSup {p q : ι → Submodule R M} (hq : iSupIndep q)
    (hpq : ∀ i, p i ≤ q i) (hsup : ⨆ i, p i = ⨆ i, q i) (i : ι) : p i = q i := by
  refine le_antisymm (hpq i) fun x hx ↦ ?_
  have hx' : x ∈ ⨆ j, p j := by
    rw [hsup]
    exact le_iSup q i hx
  rw [iSup_split_single p i, Submodule.mem_sup] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have hbi : b ∈ q i := by
    have hb' : a + b - a ∈ q i := Submodule.sub_mem _ hx (hpq i ha)
    simpa using hb'
  have hbne : b ∈ ⨆ (j) (_ : j ≠ i), q j := iSup₂_mono (fun j _ ↦ hpq j) hb
  rw [Submodule.disjoint_def.mp (hq i) b hbi hbne, add_zero]
  exact ha

end TauCeti
