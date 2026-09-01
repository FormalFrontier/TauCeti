/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Composing immersions with diffeomorphisms

Mathlib defines `Manifold.IsImmersion` by a normal form in charts — `f` looks like `u ↦ (u, 0)`
for suitable charts of the source and the target — and lists `IsImmersion.comp` as a `TODO` in
`Mathlib/Geometry/Manifold/Immersion.lean`, because a general composite has to combine two
complements and needs the differential to split.

This file settles the special case that is elementary: composing with a **diffeomorphism** on
either side. Nothing has to be recombined, because a diffeomorphism carries charts to charts: if
`φ` is a chart of `M` in the maximal atlas and `e : M' ≃ₘ M` is a diffeomorphism, then `φ ∘ e` is
a chart of `M'` in the maximal atlas, and reading `f ∘ e` in it produces literally the same normal
form that `f` had in `φ`. The same argument on the other side pulls an ambient chart back along
`e⁻¹`. So both composites are immersions with the *same* complement.

Since a diffeomorphism is invertible, every composition rule here is in fact an equivalence, and
each is also stated in `_iff` form. The one-directional statements remain the primitive ones: they
need a manifold structure only on the manifold `e` introduces, whereas the `_iff` forms need one on
both sides, in order to apply the rule to `e.symm` as well.

## Main results

* `TauCeti.mem_maximalAtlas_diffeomorph_transOpenPartialHomeomorph`: a diffeomorphism pulls a chart
  of the maximal atlas back to a chart of the maximal atlas. This is the only geometric input.
* `TauCeti.isImmersion_comp_diffeomorph` and `TauCeti.isImmersion_diffeomorph_comp`, together with
  their `Manifold.IsImmersionAt`, `Manifold.IsImmersionAtOfComplement` and
  `Manifold.IsImmersionOfComplement` counterparts and the `_iff` companions of all of them:
  immersions are stable under composition with a diffeomorphism on either side.
* `TauCeti.isImmersion_diffeomorph`: a diffeomorphism is an immersion.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and their
  behaviour under composition.
-/

public section

noncomputable section

namespace TauCeti

open Manifold
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
  {n : ℕ∞ω} {f : M → N}

/-- A diffeomorphism `e : M' ≃ₘ M` pulls a chart `φ` of the maximal atlas of `M` back to the chart
`φ ∘ e` of the maximal atlas of `M'`. This is the only geometric input to the composition results
below: it is what lets a normal form in charts be read on the other side of a diffeomorphism.

The name records the hypothesis: for a mere homeomorphism `e` the pullback is a chart of the
topological atlas, but not of the maximal `C^n` atlas. -/
theorem mem_maximalAtlas_diffeomorph_transOpenPartialHomeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) {φ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas I n M) :
    e.toHomeomorph.transOpenPartialHomeomorph φ ∈ IsManifold.maximalAtlas I n M' := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨(contMDiffOn_of_mem_maximalAtlas hφ).comp e.contMDiff.contMDiffOn fun _ hx => hx,
    e.symm.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hφ)⟩

/-- Precomposing with a diffeomorphism of the source preserves the immersion normal form at a
point, with the same complement: the domain chart of the immersion is pulled back along the
diffeomorphism, and `f ∘ e` read in the new chart is what `f` was in the old one. -/
theorem isImmersionAtOfComplement_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) {x : M'} (h : IsImmersionAtOfComplement F I J n f (e x)) :
    IsImmersionAtOfComplement F I J n (f ∘ e) x := by
  -- `Homeomorph.transOpenPartialHomeomorph` is built from `Equiv.transPartialEquiv`, whose
  -- `PartialEquiv` is assembled with `copy`, so the pulled-back chart's source is *literally*
  -- `⇑e ⁻¹' h.domChart.source` and its target is *literally* `h.domChart.target`. The three
  -- identities this produces are what makes `h`'s data fit the new chart; we spell them out
  -- rather than leaving them to definitional unfolding.
  have hsource : (e.toHomeomorph.transOpenPartialHomeomorph h.domChart).source
      = ⇑e ⁻¹' h.domChart.source := rfl
  have htarget : ((e.toHomeomorph.transOpenPartialHomeomorph h.domChart).extend I).target
      = (h.domChart.extend I).target := rfl
  have hsymm : ⇑((e.toHomeomorph.transOpenPartialHomeomorph h.domChart).extend I).symm
      = ⇑e.symm ∘ ⇑(h.domChart.extend I).symm := rfl
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv
    (e.toHomeomorph.transOpenPartialHomeomorph h.domChart) h.codChart ?_ h.mem_codChart_source
    (mem_maximalAtlas_diffeomorph_transOpenPartialHomeomorph e h.domChart_mem_maximalAtlas)
    h.codChart_mem_maximalAtlas ?_ fun y hy => ?_
  · rw [hsource]
    exact h.mem_domChart_source
  · rw [hsource]
    exact fun _ hy => h.source_subset_preimage_source hy
  · rw [htarget] at hy
    -- Reading `f ∘ e` through the pulled-back chart reinstates `e.symm`, which cancels the `e`:
    -- what is left is exactly `f` read through `h.domChart`.
    rw [hsymm]
    simpa only [Function.comp_apply, _root_.Diffeomorph.apply_symm_apply] using
      h.writtenInCharts hy

/-- Postcomposing with a diffeomorphism of the target preserves the immersion normal form at a
point, with the same complement: the codomain chart of the immersion is pulled back along the
inverse diffeomorphism, and `e ∘ f` read in the new chart is what `f` was in the old one. -/
theorem isImmersionAtOfComplement_diffeomorph_comp [IsManifold J n P]
    {x : M} (h : IsImmersionAtOfComplement F I J n f x) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionAtOfComplement F I J n (e ∘ f) x := by
  -- The mirror image of the previous proof, on the target side: pulling `h.codChart` back along
  -- `e.symm` gives a chart whose source is literally `⇑e.symm ⁻¹' h.codChart.source` and whose
  -- extended map is literally `h.codChart.extend J` precomposed with `e.symm`.
  have hsource : (e.symm.toHomeomorph.transOpenPartialHomeomorph h.codChart).source
      = ⇑e.symm ⁻¹' h.codChart.source := rfl
  have hextend : ⇑((e.symm.toHomeomorph.transOpenPartialHomeomorph h.codChart).extend J)
      = ⇑(h.codChart.extend J) ∘ ⇑e.symm := rfl
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv h.domChart
    (e.symm.toHomeomorph.transOpenPartialHomeomorph h.codChart) h.mem_domChart_source ?_
    h.domChart_mem_maximalAtlas
    (mem_maximalAtlas_diffeomorph_transOpenPartialHomeomorph e.symm h.codChart_mem_maximalAtlas)
    (fun y hy => ?_) fun y hy => ?_
  · rw [hsource]
    simpa only [Set.mem_preimage, Function.comp_apply, _root_.Diffeomorph.symm_apply_apply] using
      h.mem_codChart_source
  · rw [hsource]
    simpa only [Set.mem_preimage, Function.comp_apply, _root_.Diffeomorph.symm_apply_apply] using
      h.source_subset_preimage_source hy
  · -- Reading `e ∘ f` through the pulled-back ambient chart reinstates `e.symm`, which cancels
    -- the `e`: what is left is exactly `f` read through `h.codChart`.
    rw [hextend]
    simpa only [Function.comp_apply, _root_.Diffeomorph.symm_apply_apply] using
      h.writtenInCharts hy

/-- Precomposing with a diffeomorphism of the source preserves being an immersion at a point. -/
theorem isImmersionAt_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) {x : M'} (h : IsImmersionAt I J n f (e x)) :
    IsImmersionAt I J n (f ∘ e) x :=
  (isImmersionAtOfComplement_comp_diffeomorph e
    h.isImmersionAtOfComplement_complement).isImmersionAt

/-- Postcomposing with a diffeomorphism of the target preserves being an immersion at a point. -/
theorem isImmersionAt_diffeomorph_comp [IsManifold J n P]
    {x : M} (h : IsImmersionAt I J n f x) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionAt I J n (e ∘ f) x :=
  (isImmersionAtOfComplement_diffeomorph_comp
    h.isImmersionAtOfComplement_complement e).isImmersionAt

/-- Precomposing an immersion with a fixed complement by a diffeomorphism of the source gives an
immersion with the same complement. -/
theorem isImmersionOfComplement_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) (h : IsImmersionOfComplement F I J n f) :
    IsImmersionOfComplement F I J n (f ∘ e) :=
  fun x => isImmersionAtOfComplement_comp_diffeomorph e (h (e x))

/-- Postcomposing an immersion with a fixed complement by a diffeomorphism of the target gives an
immersion with the same complement. -/
theorem isImmersionOfComplement_diffeomorph_comp [IsManifold J n P]
    (h : IsImmersionOfComplement F I J n f) (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionOfComplement F I J n (e ∘ f) :=
  fun x => isImmersionAtOfComplement_diffeomorph_comp (h x) e

/-- Reparametrising an immersion by a diffeomorphism of the source gives an immersion. -/
theorem isImmersion_comp_diffeomorph [IsManifold I n M']
    (e : M' ≃ₘ^n⟮I, I⟯ M) (h : IsImmersion I J n f) : IsImmersion I J n (f ∘ e) :=
  (isImmersionOfComplement_comp_diffeomorph e h.isImmersionOfComplement_complement).isImmersion

/-- Transporting an immersion by a diffeomorphism of the target gives an immersion. -/
theorem isImmersion_diffeomorph_comp [IsManifold J n P]
    (h : IsImmersion I J n f) (e : N ≃ₘ^n⟮J, J⟯ P) : IsImmersion I J n (e ∘ f) :=
  (isImmersionOfComplement_diffeomorph_comp h.isImmersionOfComplement_complement e).isImmersion

section Iff

section Source

variable [IsManifold I n M] [IsManifold I n M']

/-- Precomposition with a diffeomorphism of the source neither creates nor destroys the immersion
normal form at a point. -/
theorem isImmersionAtOfComplement_comp_diffeomorph_iff (e : M' ≃ₘ^n⟮I, I⟯ M) {x : M'} :
    IsImmersionAtOfComplement F I J n (f ∘ e) x ↔ IsImmersionAtOfComplement F I J n f (e x) := by
  refine ⟨fun h => ?_, isImmersionAtOfComplement_comp_diffeomorph e⟩
  have hcomp : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y => by simp
  have h' := isImmersionAtOfComplement_comp_diffeomorph (f := f ∘ ⇑e) e.symm (x := e x)
    (by rw [e.symm_apply_apply]; exact h)
  rwa [hcomp] at h'

/-- Precomposition with a diffeomorphism of the source neither creates nor destroys an immersion
at a point. -/
theorem isImmersionAt_comp_diffeomorph_iff (e : M' ≃ₘ^n⟮I, I⟯ M) {x : M'} :
    IsImmersionAt I J n (f ∘ e) x ↔ IsImmersionAt I J n f (e x) := by
  refine ⟨fun h => ?_, isImmersionAt_comp_diffeomorph e⟩
  have hcomp : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y => by simp
  have h' := isImmersionAt_comp_diffeomorph (f := f ∘ ⇑e) e.symm (x := e x)
    (by rw [e.symm_apply_apply]; exact h)
  rwa [hcomp] at h'

/-- Precomposition with a diffeomorphism of the source neither creates nor destroys an immersion
with a fixed complement. -/
theorem isImmersionOfComplement_comp_diffeomorph_iff (e : M' ≃ₘ^n⟮I, I⟯ M) :
    IsImmersionOfComplement F I J n (f ∘ e) ↔ IsImmersionOfComplement F I J n f := by
  refine ⟨fun h => ?_, isImmersionOfComplement_comp_diffeomorph e⟩
  have hcomp : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y => by simp
  have h' := isImmersionOfComplement_comp_diffeomorph e.symm h
  rwa [hcomp] at h'

/-- Precomposition with a diffeomorphism of the source neither creates nor destroys an
immersion. -/
theorem isImmersion_comp_diffeomorph_iff (e : M' ≃ₘ^n⟮I, I⟯ M) :
    IsImmersion I J n (f ∘ e) ↔ IsImmersion I J n f := by
  refine ⟨fun h => ?_, isImmersion_comp_diffeomorph e⟩
  have hcomp : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y => by simp
  have h' := isImmersion_comp_diffeomorph e.symm h
  rwa [hcomp] at h'

end Source

section Target

variable [IsManifold J n N] [IsManifold J n P]

/-- Postcomposition with a diffeomorphism of the target neither creates nor destroys the immersion
normal form at a point. -/
theorem isImmersionAtOfComplement_diffeomorph_comp_iff (e : N ≃ₘ^n⟮J, J⟯ P) {x : M} :
    IsImmersionAtOfComplement F I J n (e ∘ f) x ↔ IsImmersionAtOfComplement F I J n f x := by
  refine ⟨fun h => ?_, fun h => isImmersionAtOfComplement_diffeomorph_comp h e⟩
  have hcomp : ⇑e.symm ∘ ⇑e ∘ f = f := funext fun y => by simp
  have h' := isImmersionAtOfComplement_diffeomorph_comp h e.symm
  rwa [hcomp] at h'

/-- Postcomposition with a diffeomorphism of the target neither creates nor destroys an immersion
at a point. -/
theorem isImmersionAt_diffeomorph_comp_iff (e : N ≃ₘ^n⟮J, J⟯ P) {x : M} :
    IsImmersionAt I J n (e ∘ f) x ↔ IsImmersionAt I J n f x := by
  refine ⟨fun h => ?_, fun h => isImmersionAt_diffeomorph_comp h e⟩
  have hcomp : ⇑e.symm ∘ ⇑e ∘ f = f := funext fun y => by simp
  have h' := isImmersionAt_diffeomorph_comp h e.symm
  rwa [hcomp] at h'

/-- Postcomposition with a diffeomorphism of the target neither creates nor destroys an immersion
with a fixed complement. -/
theorem isImmersionOfComplement_diffeomorph_comp_iff (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersionOfComplement F I J n (e ∘ f) ↔ IsImmersionOfComplement F I J n f := by
  refine ⟨fun h => ?_, fun h => isImmersionOfComplement_diffeomorph_comp h e⟩
  have hcomp : ⇑e.symm ∘ ⇑e ∘ f = f := funext fun y => by simp
  have h' := isImmersionOfComplement_diffeomorph_comp h e.symm
  rwa [hcomp] at h'

/-- Postcomposition with a diffeomorphism of the target neither creates nor destroys an
immersion. -/
theorem isImmersion_diffeomorph_comp_iff (e : N ≃ₘ^n⟮J, J⟯ P) :
    IsImmersion I J n (e ∘ f) ↔ IsImmersion I J n f := by
  refine ⟨fun h => ?_, fun h => isImmersion_diffeomorph_comp h e⟩
  have hcomp : ⇑e.symm ∘ ⇑e ∘ f = f := funext fun y => by simp
  have h' := isImmersion_diffeomorph_comp h e.symm
  rwa [hcomp] at h'

end Target

end Iff

/-- A diffeomorphism is an immersion: it is the identity immersion transported by itself.

This is the statement Mathlib lists as the `TODO` `Diffeomorph.isImmersion` in
`Mathlib/Geometry/Manifold/Immersion.lean`; the name is flat here because a `Diffeomorph`
namespace nested in `TauCeti` would break dot notation on Mathlib's type. -/
theorem isImmersion_diffeomorph [IsManifold I n M] [IsManifold I n M'] (e : M ≃ₘ^n⟮I, I⟯ M') :
    IsImmersion I I n e :=
  (isImmersion_diffeomorph_comp (IsImmersion.id (I := I) (n := n) (M := M)) e).congr rfl

end TauCeti
