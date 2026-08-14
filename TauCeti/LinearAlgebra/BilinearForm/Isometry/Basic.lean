/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Isometry

/-!
# Isometric endomorphisms of a bilinear form

This file defines the predicate that an endomorphism preserves a bilinear form and provides its
elementary API, including the bridge to Mathlib's bundled isometric maps. The isometry group and
the determinant, base-change, and orthogonal-complement API are developed in
`TauCeti.LinearAlgebra.BilinearForm.Isometry`.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An endomorphism `f` of `M` is an *isometry* of the bilinear form `B` when it preserves `B`,
that is, when `B (f x) (f y) = B x y` for all `x` and `y`.

Isometric endomorphisms form a monoid, not a group: for the zero form on `ℤ ^ 2` every endomorphism
is one. For a finite free `ℤ`-module `V` and a left-separating integral form `Q` an isometric
endomorphism is automatically invertible (`TauCeti.BilinForm.IsIsometry.toIsometryGroup`), and the
resulting automorphisms are the arithmetic group `Aut(V, Q)`; see
`TauCeti.BilinForm.isometryGroup`. -/
def IsIsometry (B : BilinForm R M) (f : M →ₗ[R] M) : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

/-- An endomorphism is an isometry of `B` exactly when it preserves `B` pointwise. -/
theorem isIsometry_iff : IsIsometry B f ↔ ∀ x y, B (f x) (f y) = B x y := (Iff.rfl)

/-- An endomorphism is an isometry of `B` exactly when precomposing `B` with it on both sides
returns `B`. -/
theorem isIsometry_iff_comp : IsIsometry B f ↔ B.comp f f = B :=
  ⟨fun h => LinearMap.BilinForm.ext fun x y => h x y, fun h x y =>
    LinearMap.BilinForm.congr_fun h x y⟩

/-- The underlying map of one of Mathlib's isometric maps `B →bᵢ B` is an isometry. -/
theorem isIsometry_toLinearMap (φ : B →bᵢ B) : IsIsometry B φ.toLinearMap := φ.map_app

namespace IsIsometry

/-- An isometry takes the same value under `B` after applying the endomorphism to both inputs. -/
@[grind =]
protected theorem apply (hf : IsIsometry B f) (x y : M) : B (f x) (f y) = B x y :=
  isIsometry_iff.mp hf x y

/-- An isometry, bundled as one of Mathlib's isometric maps `B →bᵢ B`. -/
def toIsometry (hf : IsIsometry B f) : B →bᵢ B := ⟨f, hf⟩

@[simp]
theorem toIsometry_apply (hf : IsIsometry B f) (x : M) : hf.toIsometry x = f x := (rfl)

@[simp]
theorem toIsometry_toLinearMap (hf : IsIsometry B f) : hf.toIsometry.toLinearMap = f := (rfl)

protected theorem id : IsIsometry B LinearMap.id := fun _ _ => rfl

protected theorem comp (hf : IsIsometry B f) (hg : IsIsometry B g) : IsIsometry B (f ∘ₗ g) :=
  fun x y => (hf (g x) (g y)).trans (hg x y)

end IsIsometry

end CommSemiring

end BilinForm

end TauCeti
