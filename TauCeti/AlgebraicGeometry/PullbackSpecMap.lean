/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pullback of schemes along `Spec.map`

Mathlib's `CategoryTheory.Over.pullbackId` and `CategoryTheory.Over.pullbackComp` compare the
pullback functors on `Over` categories along an identity morphism and along a composite. This
file reads those comparisons through `Spec`: `Spec.map` takes an identity ring map to an
identity morphism of schemes and a composite `f ≫ g` to `Spec.map g ≫ Spec.map f`, so pullback
along `Spec.map (𝟙 R)` is the identity functor on schemes over `Spec R`, and pullback along
`Spec.map (f ≫ g)` is the composite of pullback along `Spec.map f` with pullback along
`Spec.map g`.

Nothing here mentions affineness or group objects: these are statements about arbitrary schemes
over an affine base, and they are the underlying comparisons of the base-change functors on
affine group schemes in `TauCeti/AlgebraicGeometry/AffineGroupScheme/BaseChange/Basic.lean`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapId`: pullback along `Spec.map (𝟙 R)` is the
  identity functor.
* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp`: pullback along `Spec.map (f ≫ g)` is a
  composite of pullbacks.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {R S T : CommRingCat.{u}}

/-- Pullback along `Spec.map (𝟙 R)` is the identity functor on schemes over `Spec R`. -/
noncomputable def Over.pullbackSpecMapId :
    Over.pullback (Spec.map (𝟙 R)) ≅ 𝟭 (Over (Spec R)) :=
  eqToIso (by simp only [Spec.map_id]) ≪≫ Over.pullbackId

/-- Pullback along `Spec.map (f ≫ g)` is pullback along `Spec.map f` followed by pullback along
`Spec.map g`. -/
noncomputable def Over.pullbackSpecMapComp (f : R ⟶ S) (g : S ⟶ T) :
    Over.pullback (Spec.map (f ≫ g)) ≅
      Over.pullback (Spec.map f) ⋙ Over.pullback (Spec.map g) :=
  eqToIso (by simp only [Spec.map_comp]) ≪≫ Over.pullbackComp (Spec.map g) (Spec.map f)

end AlgebraicGeometry

end TauCeti
