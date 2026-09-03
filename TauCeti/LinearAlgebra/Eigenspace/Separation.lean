/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

/-!
# Separating eigenspace summands

Suppose `p` is a sum `⨆ j ∈ s, W j` of subspaces on which an endomorphism `A` already
acts by scalars, one scalar `g j` per summand, and suppose the scalar `g k` of one distinguished
summand is attained by no other. Then that summand is *exactly* the `g k`-eigenspace of `A` inside
`p`: no eigenvector of eigenvalue `g k` hides in the other summands, because eigenspaces for
distinct eigenvalues are independent. This is how a weight space is recovered from an eigenspace of
a single operator once a decomposition separating the weights is available.

## Main results

* `TauCeti.biSup_inf_eigenspace_eq_self`: a summand whose scalar is attained only by itself is cut
  out by the corresponding eigenspace.
-/

namespace TauCeti

open Module

universe u v w

variable {K : Type u} {V : Type v} [CommRing K] [IsDomain K] [AddCommGroup V] [Module K V]
  [Module.IsTorsionFree K V]

/-- **Separated summands are cut out by their eigenspaces.** If every `W j`, for `j` in a set `s`,
consists of eigenvectors of `A` of eigenvalue `g j`, and if the scalar `g k` of a distinguished
index `k ∈ s` is attained by no other index of `s`, then meeting the sum `⨆ j ∈ s, W j` with the
`g k`-eigenspace of `A` returns `W k` exactly.

In particular no eigenvector of eigenvalue `g k` in the sum lies outside `W k`. -/
theorem biSup_inf_eigenspace_eq_self {ι : Type w} (A : Module.End K V) (W : ι → Submodule K V)
    (g : ι → K) {s : Set ι} (hW : ∀ j, j ∈ s → W j ≤ A.eigenspace (g j))
    {k : ι} (hk : k ∈ s)
    (hg : ∀ j ∈ s, j ≠ k → g j ≠ g k) :
    (⨆ j ∈ s, W j) ⊓ A.eigenspace (g k) = W k := by
  have hsplit : (⨆ j ∈ s, W j) = W k ⊔ ⨆ j ∈ s \ {k}, W j := by
    conv_lhs => rw [← Set.insert_sdiff_self_of_mem hk]
    rw [iSup_insert]
  have hle : (⨆ j ∈ s \ {k}, W j) ≤ ⨆ c ≠ g k, A.eigenspace c := by
    refine iSup₂_le fun j hj ↦ (hW j hj.1).trans ?_
    exact le_iSup₂ (f := fun (c : K) (_ : c ≠ g k) ↦ A.eigenspace c) (g j) (hg j hj.1 hj.2)
  have hdisj : Disjoint (⨆ j ∈ s \ {k}, W j) (A.eigenspace (g k)) :=
    ((A.eigenspaces_iSupIndep (g k)).mono_right hle).symm
  rw [hsplit, sup_inf_assoc_of_le _ (hW k hk), disjoint_iff.mp hdisj, sup_bot_eq]

end TauCeti
