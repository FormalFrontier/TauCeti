/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Base change of group-scheme isogenies

This file proves that isogenies of group schemes over a field remain isogenies after extension of
the ground field. The group-scheme base change is the pullback functor on the over category,
lifted to group objects.

## Main declarations

* `TauCeti.GroupScheme.IsIsogeny.baseChange`: isogenies remain isogenies after field extension.
* `TauCeti.GroupScheme.IsIsogeny.baseChange_isCentral_of_isCommMonObj`: isogenies from a
  commutative source become central isogenies after field extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

This is the base-change stability needed for the central-isogeny interface in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

section Field

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

/-- Extending the ground field preserves group-scheme isogenies. -/
theorem IsIsogeny.baseChange {f : G ⟶ H} (hf : IsIsogeny f) :
    IsIsogeny ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.map f) := by
  rw [isIsogeny_iff] at hf ⊢
  exact ⟨MorphismProperty.overPullbackMap (P := @IsFinite) _ _ hf.1,
    MorphismProperty.overPullbackMap (P := @Flat) _ _ hf.2.1,
    MorphismProperty.overPullbackMap (P := @Surjective) _ _ hf.2.2⟩

/-- Extending the ground field turns an isogeny from a commutative group scheme into a central
isogeny. -/
theorem IsIsogeny.baseChange_isCentral_of_isCommMonObj {f : G ⟶ H}
    (hf : IsIsogeny f) [IsCommMonObj G.X] :
    IsCentralIsogeny
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.map f) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let _ : IsCommMonObj ((Over.pullback s).mapGrp.obj G).X :=
    ((Over.pullback s).mapCommMon.obj (.mk G.X)).comm
  exact hf.baseChange.isCentral_of_isCommMonObj

end Field

end TauCeti.GroupScheme
