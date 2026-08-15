/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

/-!
# Eigenspaces inside an invariant subspace

Let `A` be an endomorphism of a module `V` and let `p` be an `A`-invariant submodule. This file
records two facts about the eigenspaces of `A` seen inside `p`.

The first is bookkeeping: the `c`-eigenspace of the restriction `A|ₚ` is the part of the
`c`-eigenspace of `A` that lies in `p`, so the two have the same dimension.

The second is the useful one. Suppose `p` is a sum `⨆ j ∈ s, W j` of subspaces on which `A` already
acts by scalars, one scalar `g j` per summand, and suppose the scalar `g k` of one distinguished
summand is attained by no other. Then that summand is *exactly* the `g k`-eigenspace of `A` inside
`p`: no eigenvector of eigenvalue `g k` hides in the other summands, because eigenspaces for
distinct eigenvalues are independent. This is how a weight space is recovered from an eigenspace of
a single operator once a decomposition separating the weights is available.

## Main results

* `TauCeti.finrank_eigenspace_restrict`: the eigenspaces of `A|ₚ` are the eigenspaces of `A` met
  with `p`.
* `TauCeti.biSup_inf_eigenspace_eq`: a summand whose scalar is attained only by itself is cut out
  by the corresponding eigenspace.
-/

namespace TauCeti

open Module

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- **Eigenspaces of a restriction.** The `c`-eigenspace of the restriction of `A` to an invariant
submodule `p` has the dimension of the part of the `c`-eigenspace of `A` lying in `p`. -/
theorem finrank_eigenspace_restrict (A : Module.End K V) {p : Submodule K V}
    (hA : ∀ v ∈ p, A v ∈ p) (c : K) :
    finrank K (Module.End.eigenspace (A.restrict hA) c) =
      finrank K (p ⊓ A.eigenspace c : Submodule K V) := by
  have h₁ : Module.End.eigenspace (A.restrict hA) c =
      Submodule.comap p.subtype (p ⊓ A.eigenspace c) := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, v.2, true_and, Subtype.ext_iff, LinearMap.coe_restrict_apply,
      Submodule.coe_smul_of_tower]
  rw [h₁, (Submodule.comapSubtypeEquivOfLe (inf_le_left : p ⊓ A.eigenspace c ≤ p)).finrank_eq]

/-- **Separated summands are cut out by their eigenspaces.** If every `W j`, for `j` in a set `s`,
consists of eigenvectors of `A` of eigenvalue `g j`, and if the scalar `g k` of a distinguished
index `k ∈ s` is attained by no other index of `s`, then meeting the sum `⨆ j ∈ s, W j` with the
`g k`-eigenspace of `A` returns `W k` exactly.

The inclusion `W k ≤ ⨆ j ∈ s, W j ⊓ eigenspace (g k)` is immediate; the content is the reverse one,
and it is the independence of the eigenspaces of `A` at distinct eigenvalues. -/
theorem biSup_inf_eigenspace_eq {ι : Type w} (A : Module.End K V) (W : ι → Submodule K V)
    (g : ι → K) (hW : ∀ j, W j ≤ A.eigenspace (g j)) {s : Set ι} {k : ι} (hk : k ∈ s)
    (hg : ∀ j ∈ s, j ≠ k → g j ≠ g k) :
    (⨆ j ∈ s, W j) ⊓ A.eigenspace (g k) = W k := by
  have hsplit : (⨆ j ∈ s, W j) = W k ⊔ ⨆ j ∈ s \ {k}, W j := by
    conv_lhs => rw [← Set.insert_sdiff_self_of_mem hk]
    rw [iSup_insert]
  have hle : (⨆ j ∈ s \ {k}, W j) ≤ ⨆ c ≠ g k, A.eigenspace c := by
    refine iSup₂_le fun j hj ↦ (hW j).trans ?_
    exact le_iSup₂ (f := fun (c : K) (_ : c ≠ g k) ↦ A.eigenspace c) (g j) (hg j hj.1 hj.2)
  have hdisj : Disjoint (⨆ j ∈ s \ {k}, W j) (A.eigenspace (g k)) :=
    ((A.eigenspaces_iSupIndep (g k)).mono_right hle).symm
  rw [hsplit, sup_inf_assoc_of_le _ (hW k), disjoint_iff.mp hdisj, sup_bot_eq]

end TauCeti
