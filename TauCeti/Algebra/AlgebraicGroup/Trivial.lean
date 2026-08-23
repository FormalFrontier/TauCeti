/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The trivial affine group

This file records the functor-of-points calculation for the trivial affine group scheme. Its
coordinate Hopf algebra is the base ring `R`, with Mathlib's canonical Hopf algebra structure
on `R` over itself. For every commutative `R`-algebra `A`, there is exactly one `R`-algebra
homomorphism `R →ₐ[R] A`, namely `Algebra.ofId R A`; consequently the convolution group of
`A`-points is the one-element group `PUnit`.

This is the terminal-object example in the Hopf-algebra/functor-of-points side of the
ReductiveGroups roadmap, Layer 0. It is the identity object needed by the product and affine
group scheme dictionary: `Spec R` over `Spec R` represents the trivial group-valued functor.

## Main declarations

* `TauCeti.TrivialGroup.pointsMulEquiv`: the convolution group of points is `PUnit`.
* `TauCeti.TrivialGroup.pointsMulEquiv_mapValue`: the equivalence is natural in the value
  algebra.

## References

This uses Mathlib's `Algebra.ofId`, its `Subsingleton (R →ₐ[R] A)` instance, and the
canonical Hopf algebra structure on `R` over itself from `Mathlib.RingTheory.HopfAlgebra.Basic`.
-/

public section

open WithConv

namespace TauCeti

namespace TrivialGroup

universe u v w

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The functor of points of the trivial affine group is the one-element group.

The source is the convolution group of `R`-algebra maps out of the Hopf algebra `R`; since
there is only one such algebra map, the convolution group is multiplicatively equivalent to
`PUnit`. -/
noncomputable def pointsMulEquiv : WithConv (R →ₐ[R] A) ≃* PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := toConv (Algebra.ofId R A)
  left_inv f := by
    apply WithConv.ofConv_injective
    exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The equivalence sends every convolution point to the unique element of `PUnit`. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) f = PUnit.unit :=
  Subsingleton.elim _ _

/-- The inverse equivalence sends the unique element of `PUnit` to `Algebra.ofId R A`. -/
@[simp]
theorem pointsMulEquiv_symm_apply (u : PUnit.{1}) :
    (pointsMulEquiv (R := R) (A := A)).symm u = toConv (Algebra.ofId R A) :=
  by
    apply WithConv.ofConv_injective
    exact Subsingleton.elim _ _

/-- The unique convolution point is the identity point. -/
theorem convPoint_eq_one (f : WithConv (R →ₐ[R] A)) : f = 1 := by
  apply WithConv.ofConv_injective
  rw [AlgHom.convOne_def]
  exact Subsingleton.elim _ _

/-- The identity normal form for trivial-group convolution points, as a simp proposition. -/
@[simp]
theorem convPoint_eq_one_iff (f : WithConv (R →ₐ[R] A)) : f = 1 ↔ True :=
  ⟨fun _ => trivial, fun _ => convPoint_eq_one f⟩

/-- The underlying algebra map of any trivial-group convolution point is `Algebra.ofId`. -/
@[simp]
theorem ofConv_eq_ofId (f : WithConv (R →ₐ[R] A)) :
    f.ofConv = Algebra.ofId R A :=
  Subsingleton.elim _ _

/-- Evaluating any trivial-group convolution point gives the algebra map. -/
theorem convPoint_apply (f : WithConv (R →ₐ[R] A)) (r : R) :
    f r = algebraMap R A r := by
  rw [convPoint_eq_one f]
  rw [AlgHom.convOne_def]
  rfl

/-- Every `R`-algebra map `R →ₐ[R] A` becomes the convolution identity. -/
@[simp]
theorem toConv_eq_one (f : R →ₐ[R] A) : toConv f = (1 : WithConv (R →ₐ[R] A)) :=
  convPoint_eq_one (toConv f)

/-- Evaluating the inverse of a trivial-group point gives the algebra map. -/
theorem convInv_apply (f : WithConv (R →ₐ[R] A)) (r : R) :
    f⁻¹ r = algebraMap R A r := by
  rw [convPoint_eq_one f]
  rw [AlgHom.convOne_def]
  rfl

section Naturality

variable {B : Type w} [CommSemiring B] [Algebra R B]

/-- The trivial-group points equivalence is natural in the value algebra. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B) (f : WithConv (R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := R) φ f) =
      pointsMulEquiv (R := R) (A := A) f :=
  rfl

/-- Naturality of the inverse trivial-group points equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (u : PUnit.{1}) :
    AlgHom.mapValue (H := R) φ ((pointsMulEquiv (R := R) (A := A)).symm u) =
      (pointsMulEquiv (R := R) (A := B)).symm u := by
  apply (pointsMulEquiv (R := R) (A := B)).injective
  rw [pointsMulEquiv_mapValue]

end Naturality

end TrivialGroup

end TauCeti
