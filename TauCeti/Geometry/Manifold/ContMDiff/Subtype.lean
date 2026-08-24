/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Smoothness of maps into an open submanifold

A map into an open submanifold `U ⊆ M` is `C^n` exactly when its composition with the inclusion
`U → M` is `C^n`: the charts of `U` are restrictions of the charts of `M`, so smoothness is
insensitive to whether the codomain is read in the submanifold or in the ambient manifold.

Mathlib records this through `contMDiffAt_subtype_iff` at a point, and through
`ContMDiffWithinAt.subtypeVal_comp_iff` and siblings for regularity `∞`. Since smoothness into a
manifold is a local invariant property at *every* regularity, the same characterizations hold for
arbitrary `n`; this file supplies them.

## Main results

* `TauCeti.contMDiffWithinAt_subtypeVal_comp_iff`, `TauCeti.contMDiffOn_subtypeVal_comp_iff`,
  and `TauCeti.contMDiff_subtypeVal_comp_iff`: a map into an open submanifold is `C^n`
  (within a set, on a set, globally) iff its composition with the inclusion is.

## References

* Used to lift ambient curves (e.g. straight segments) to `C¹` curves in open submanifolds;
  see `TauCeti.Geometry.Manifold.Riemannian.Convex`.
-/

public section

open ChartedSpace Set TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω}

/-- A map into an open submanifold is `C^n` within a set at a point iff its composition with the
inclusion is, at every regularity: smoothness is a local invariant property and the charts agree. -/
theorem contMDiffWithinAt_subtypeVal_comp_iff (U : Opens M') (f : M → U) (s : Set M)
    (x : M) :
    ContMDiffWithinAt I I' n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I I' n f s x :=
  liftPropWithinAt_subtypeVal_comp_iff ..

/-- A map into an open submanifold is `C^n` on a set iff its composition with the inclusion is,
at every regularity. -/
theorem contMDiffOn_subtypeVal_comp_iff (U : Opens M') (f : M → U) (s : Set M) :
    ContMDiffOn I I' n (Subtype.val ∘ f) s ↔ ContMDiffOn I I' n f s :=
  ⟨fun h a ha => (contMDiffWithinAt_subtypeVal_comp_iff U f s a).mp (h a ha),
   fun h a ha => (contMDiffWithinAt_subtypeVal_comp_iff U f s a).mpr (h a ha)⟩

/-- A map into an open submanifold is `C^n` iff its composition with the inclusion is, at every
regularity. -/
theorem contMDiff_subtypeVal_comp_iff (U : Opens M') (f : M → U) :
    ContMDiff I I' n (Subtype.val ∘ f) ↔ ContMDiff I I' n f :=
  ⟨fun h _ => (contMDiffWithinAt_subtypeVal_comp_iff U f Set.univ _).mp (h _),
   fun h _ => (contMDiffWithinAt_subtypeVal_comp_iff U f Set.univ _).mpr (h _)⟩

end TauCeti
