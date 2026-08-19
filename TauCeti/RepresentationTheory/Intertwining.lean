/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining

/-!
# An injective intertwining map is an isomorphism onto its image

Mathlib records the image of an intertwining map as a subrepresentation
(`Representation.IntertwiningMap.range`) and turns a bijective intertwining map into an
equivalence (`Representation.IntertwiningMap.ofBijective`), but it does not connect the two: an
*injective* intertwining map is an isomorphism onto its image, and that is the usual way a
construction "`W` is the subrepresentation cut out by such and such an operator" is turned into an
identification of `W` with a representation built independently.

This file supplies the corestriction and that identification. The subrepresentation is taken as an
argument together with a proof that the image fills it, rather than being fixed to be
`IntertwiningMap.range f`: in practice the target subrepresentation is defined some other way -- as
the range of a different operator, say -- and matching the two ranges is a separate step that the
caller has already done.

## Main definitions

* `Representation.IntertwiningMap.codRestrict`: corestrict an intertwining map to a
  subrepresentation containing its image.
* `Representation.IntertwiningMap.equivOfRange`: an injective intertwining map is an equivalence
  onto a subrepresentation that its image fills.
-/

public section

namespace Representation.IntertwiningMap

variable {A G V W : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

/-- Corestrict an intertwining map to a subrepresentation of the target containing its image. -/
def codRestrict (f : IntertwiningMap ρ σ) (P : Subrepresentation σ)
    (hP : ∀ v, f v ∈ P.toSubmodule) : IntertwiningMap ρ P.toRepresentation where
  toLinearMap := LinearMap.codRestrict P.toSubmodule f.toLinearMap hP
  isIntertwining' g :=
    LinearMap.ext fun v =>
      Subtype.ext (congrArg (fun l : V →ₗ[A] W => l v) (f.isIntertwining' g))

@[simp]
theorem codRestrict_apply_coe (f : IntertwiningMap ρ σ) (P : Subrepresentation σ)
    (hP : ∀ v, f v ∈ P.toSubmodule) (v : V) :
    ((f.codRestrict P hP v : P.toSubmodule) : W) = f v := by
  rfl

/-- **An injective intertwining map is an isomorphism onto its image**, here onto any
subrepresentation `P` that the image fills. -/
noncomputable def equivOfRange (f : IntertwiningMap ρ σ) (hf : Function.Injective f)
    {P : Subrepresentation σ} (hP : LinearMap.range f.toLinearMap = P.toSubmodule) :
    ρ.Equiv P.toRepresentation :=
  (f.codRestrict P fun v => hP.le (LinearMap.mem_range_self _ v)).ofBijective
    ⟨fun _ _ h => hf (by exact congrArg Subtype.val h), fun w => by
      obtain ⟨v, hv⟩ := hP.ge w.2
      exact ⟨v, Subtype.ext (by exact hv)⟩⟩

@[simp]
theorem equivOfRange_apply_coe (f : IntertwiningMap ρ σ) (hf : Function.Injective f)
    {P : Subrepresentation σ} (hP : LinearMap.range f.toLinearMap = P.toSubmodule) (v : V) :
    ((f.equivOfRange hf hP v : P.toSubmodule) : W) = f v := by
  rfl

end Representation.IntertwiningMap
