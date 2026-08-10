/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Algebra.ZeroSequenceOfUnits
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# The Baire step of Henkel's open mapping theorem

Henkel's open mapping theorem says that a continuous surjective linear map between complete
Hausdorff first-countable modules over a ring with a zero sequence of units is open. Its first
half is a Baire-category argument, and that half is what this file isolates. It needs none of
the hypotheses the second half needs — no completeness, no first countability, not even
continuity of the map. What it does need is that the target is a Baire space and that the map is
equivariant, the latter being what lets a dilate pass through it.

The argument is the classical one, with the zero sequence of units supplying the countability
Baire needs. Any neighbourhood `U` of zero in the domain has its dilates `uₙ⁻¹ • U` cover the
domain, indexed by `ℕ` (`TauCeti.iUnion_inv_smul_eq_univ_of_tendsto_zero`); a surjection carries
that cover to a cover of the target by the corresponding dilates of `f '' U`; Baire forces one of
their closures to have interior; and dilating back by a unit — a homeomorphism of the target —
moves that interior onto `closure (f '' U)` itself.

What this does **not** give is that `closure (f '' U)` is a *neighbourhood of zero*, still less
that `f '' U` is. Both are later steps of Henkel's proof and neither is proved here; the second
is where completeness and first countability enter.

## Main results

* `TauCeti.nonempty_interior_closure_of_iUnion_smul`: if countably many dilates of a set by a
  group acting continuously cover a Baire space, then the closure of that set has nonempty
  interior. This is the Baire argument by itself, with no map in sight.
* `TauCeti.nonempty_interior_closure_image_of_tendsto_zero`: the form Henkel's proof uses — along
  a zero sequence of units, the closure of the image of any neighbourhood of zero under a
  surjective equivariant map has nonempty interior.
* `TauCeti.HasZeroSequenceOfUnits.nonempty_interior_closure_image`: the same, taking the sequence
  from the class rather than from the caller.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647). The Baire argument formalised here is the
  opening of its proof.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Theorem 6.16 and Propositions 6.17–6.18, which are
  proved from Henkel's theorem; downstream context for this file rather than its source.
-/

public section

open Filter Pointwise Topology

namespace TauCeti

section Baire

variable {G N : Type*} [Group G] [TopologicalSpace N] [MulAction G N] [ContinuousConstSMul G N]

/-- **The Baire step**, on its own: if countably many dilates of `V` by elements of a group acting
continuously cover a Baire space, then `closure V` has nonempty interior.

Invertibility of the scalars is what makes the conclusion about `V` rather than about one dilate:
`x ↦ g • x` is then a homeomorphism, so it carries interior to interior and commutes with closure.
Countability of the index is the whole reason Henkel's hypothesis is a *sequence* of units — a
cover indexed by all of `Aˣ` would exhaust the space just as well but could not start a Baire
argument. Nothing else about either parameter is used, so the group is arbitrary and the index is
an arbitrary countable type; the caller below supplies `Aˣ` and `ℕ`. -/
theorem nonempty_interior_closure_of_iUnion_smul [BaireSpace N] [Nonempty N] {ι : Type*}
    [Countable ι] {u : ι → G} {V : Set N} (hV : ⋃ i, u i • V = Set.univ) :
    (interior (closure V)).Nonempty := by
  have hcov : ⋃ i : ι, closure (u i • V) = Set.univ :=
    Set.eq_univ_of_univ_subset (hV ▸ Set.iUnion_mono fun _ ↦ subset_closure)
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed (fun _ : ι ↦ isClosed_closure) hcov
  rwa [closure_smul, interior_smul, Set.smul_set_nonempty] at hn

end Baire

section Image

variable {A M N : Type*} [MonoidWithZero A] [TopologicalSpace A]
  [Zero M] [TopologicalSpace M] [MulActionWithZero A M]
  [TopologicalSpace N] [MulAction A N] [ContinuousConstSMul A N]

/-- **The Baire step in the form Henkel's proof uses.** Along a zero sequence of units, the
closure of the image of a neighbourhood of zero under a surjective equivariant map has nonempty
interior.

Besides the equivariance carried by `MulActionHomClass` — which is what lets a dilate pass
through the map — surjectivity is the only property used: together they turn the countable cover
of the domain by `uₙ⁻¹ • U` into a countable cover of the target. Continuity of the map is not
needed here and is not assumed; it enters Henkel's proof only afterwards.

The hypothesis `hc` is the one carried by
`TauCeti.iUnion_inv_smul_eq_univ_of_tendsto_zero`: continuity of the action in the scalar alone,
at zero, at every vector. `ContinuousSMul A M` implies it and is strictly stronger. -/
theorem nonempty_interior_closure_image_of_tendsto_zero [BaireSpace N] {F : Type*}
    [FunLike F M N] [MulActionHomClass F A M N] (f : F) (hf : Function.Surjective f) {u : ℕ → Aˣ}
    (hu : Tendsto (fun n ↦ ((u n : A))) atTop (𝓝 0))
    (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) {U : Set M} (hU : U ∈ 𝓝 (0 : M)) :
    (interior (closure (f '' U))).Nonempty := by
  have : Nonempty N := ⟨f 0⟩
  refine nonempty_interior_closure_of_iUnion_smul (G := Aˣ) (u := fun n ↦ (u n)⁻¹) ?_
  -- `v • s` for `v : Aˣ` is by definition `(v : A) • s`, which is the form `image_smul_set` takes.
  have himg : ∀ v : Aˣ, v • f '' U = f '' (v • U) := fun v ↦ (image_smul_set f (v : A) U).symm
  calc ⋃ n, ((u n)⁻¹ : Aˣ) • f '' U
      = f '' ⋃ n, ((u n)⁻¹ : Aˣ) • U := by
        rw [Set.image_iUnion]; exact Set.iUnion_congr fun n ↦ himg _
    _ = f '' Set.univ := by rw [iUnion_inv_smul_eq_univ_of_tendsto_zero hu hc hU]
    _ = Set.univ := by rw [Set.image_univ, hf.range_eq]

/-- **The Baire step under the class hypothesis.** The same conclusion as
`TauCeti.nonempty_interior_closure_image_of_tendsto_zero`, with the zero sequence taken from
`TauCeti.HasZeroSequenceOfUnits` instead of supplied by the caller. This is the form a downstream
open mapping theorem wants, since the roadmap states Henkel's hypothesis as the class. -/
theorem HasZeroSequenceOfUnits.nonempty_interior_closure_image [HasZeroSequenceOfUnits A]
    [BaireSpace N] {F : Type*} [FunLike F M N] [MulActionHomClass F A M N] (f : F)
    (hf : Function.Surjective f) (hc : ∀ x : M, ContinuousAt (fun a : A ↦ a • x) 0) {U : Set M}
    (hU : U ∈ 𝓝 (0 : M)) : (interior (closure (f '' U))).Nonempty :=
  let ⟨_, hu⟩ := ‹HasZeroSequenceOfUnits A›.exists_tendsto
  nonempty_interior_closure_image_of_tendsto_zero f hf hu hc hU

end Image

end TauCeti

end
