/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks of split epimorphisms

This file proves that a chosen section pulls back along an arbitrary morphism. If
`s : S ⟶ X` is a section of `f : X ⟶ S` and `g : T ⟶ S`, its base change is the
canonical morphism

```
T ⟶ X ×[S] T
```

whose projections are `g ≫ s` and `𝟙 T`. The construction is packaged as
`CategoryTheory.SplitEpi.pullback`; its projection formulas characterize it uniquely.
The file also records naturality in both the split epimorphism and the base-change
morphism, and supplies the corresponding low-priority `IsSplitEpi` instance.

For a scheme over a field, a rational point is precisely such a chosen section of the
structure morphism. Thus this construction supplies base change of rational points, as
required by the displayed `x₀.baseChange K` and base-change compatibility target in
`TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is vendored; the
construction is the universal property of Mathlib's `pullback`.
-/

public section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace SplitEpi

variable {X S : C} {f : X ⟶ S}

/-- Pull a chosen section of `f : X ⟶ S` back along `g : T ⟶ S`.

The resulting section of `pullback.snd f g` has first projection `g ≫ h.section_`
and second projection the identity of `T`. -/
noncomputable def pullback (h : SplitEpi f) {T : C} (g : T ⟶ S) [HasPullback f g] :
    SplitEpi (Limits.pullback.snd f g) where
  section_ := Limits.pullback.lift (g ≫ h.section_) (𝟙 T) (by simp)
  id := Limits.pullback.lift_snd _ _ _

/-- The section underlying `SplitEpi.pullback` is the canonical pullback lift. -/
lemma pullback_section_def (h : SplitEpi f) {T : C} (g : T ⟶ S) [HasPullback f g] :
    (h.pullback g).section_ =
      Limits.pullback.lift (g ≫ h.section_) (𝟙 T) (by simp) :=
  (rfl)

/-- The first projection of a pulled-back section is the original section after
the base-change morphism. -/
@[reassoc (attr := simp)]
lemma pullback_section_fst (h : SplitEpi f) {T : C} (g : T ⟶ S) [HasPullback f g] :
    (h.pullback g).section_ ≫ Limits.pullback.fst f g = g ≫ h.section_ := by
  simp only [pullback_section_def, Limits.pullback.lift_fst]

/-- The two projection formulas uniquely determine the pulled-back section. -/
lemma eq_pullback_section (h : SplitEpi f) {T : C} (g : T ⟶ S) [HasPullback f g]
    (t : T ⟶ Limits.pullback f g) (hfst : t ≫ Limits.pullback.fst f g = g ≫ h.section_)
    (hsnd : t ≫ Limits.pullback.snd f g = 𝟙 T) :
    t = (h.pullback g).section_ := by
  apply Limits.pullback.hom_ext
  · rw [hfst, pullback_section_fst]
  · rw [hsnd, (h.pullback g).id]

/-- Pullback of chosen sections is natural in morphisms of split epimorphisms.

Here `i : X ⟶ Y` lies over `S`, and `h.section_ ≫ i = h'.section_` says that it
preserves the chosen sections. The induced map of pullbacks then preserves their
pulled-back sections. -/
lemma pullback_section_naturality {Y : C} {f' : Y ⟶ S} (h : SplitEpi f)
    (h' : SplitEpi f') (i : X ⟶ Y) (hi : f = i ≫ f')
    (hsection : h.section_ ≫ i = h'.section_) {T : C} (g : T ⟶ S)
    [HasPullback f g] [HasPullback f' g] : (h.pullback g).section_ ≫
        Limits.pullback.map f g f' g i (𝟙 T) (𝟙 S) (by simp [hi]) (by simp) =
      (h'.pullback g).section_ := by
  apply Limits.pullback.hom_ext
  · simp [Limits.pullback.map, Limits.pullback.lift_fst, Category.assoc, hsection]
  · simp [Limits.pullback.map, Limits.pullback.lift_snd, Category.assoc]

/-- Pullback of a chosen section is natural in the base-change morphism.

For `k : T' ⟶ T`, the canonical map from the pullback along `k ≫ g` to the
pullback along `g` carries the section over `T'` to the section over `T`
precomposed with `k`. -/
lemma pullback_section_map (h : SplitEpi f) {T T' : C} (g : T ⟶ S) (k : T' ⟶ T)
    [HasPullback f g] [HasPullback f (k ≫ g)] : (h.pullback (k ≫ g)).section_ ≫
        Limits.pullback.map f (k ≫ g) f g (𝟙 X) k (𝟙 S) (by simp) (by simp) =
      k ≫ (h.pullback g).section_ := by
  apply Limits.pullback.hom_ext
  · simp [Limits.pullback.map, Limits.pullback.lift_fst, Category.assoc]
  · simp [Limits.pullback.map, Limits.pullback.lift_snd, Category.assoc]

end SplitEpi

/-- A pullback of a split epimorphism is a split epimorphism.

The low priority leaves more specialized instances, such as the diagonal pullback,
in control when they apply. Use `SplitEpi.pullback` when the particular chosen
section matters. -/
noncomputable instance (priority := 100) Limits.pullback.snd_isSplitEpi
    {X S T : C} (f : X ⟶ S) (g : T ⟶ S) [HasPullback f g] [IsSplitEpi f] :
    IsSplitEpi (Limits.pullback.snd f g) :=
  IsSplitEpi.mk' (IsSplitEpi.exists_splitEpi.some.pullback g)

end CategoryTheory
