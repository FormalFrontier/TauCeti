/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Base change of group-scheme isogenies

This file proves that isogenies of group schemes over a field remain isogenies after base change
along a morphism between spectra of fields. The group-scheme base change is the pullback functor
on the over category, lifted to group objects.

## Main declarations

* `TauCeti.GroupScheme.IsIsogeny.baseChange`: isogenies remain isogenies after base change.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

The base-change argument follows
`TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.baseChange`.

This is the base-change stability needed for the central-isogeny interface in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

section Field

variable {k L : Type u} [Field k] [Field L]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

/-- Base change along a morphism between spectra of fields preserves group-scheme isogenies. -/
theorem IsIsogeny.baseChange
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsIsogeny f) : IsIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isIsogeny_iff, Functor.mapGrp_map_hom_hom]
  exact ⟨MorphismProperty.overPullbackMap _ _ hf.isFinite,
    MorphismProperty.overPullbackMap _ _ hf.flat,
    MorphismProperty.overPullbackMap _ _ hf.surjective⟩

end Field

end TauCeti.GroupScheme
