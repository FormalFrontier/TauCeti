/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Basic

/-!
# Finiteness of the tangent space of a finite-type affine monoid

An augmentation `f : A →ₐ[R] R` makes the cotangent space at the corresponding point,
`ker(f) / ker(f)²`, a finite `R`-module whenever `A` is noetherian. Although the augmentation
ideal is initially only known to be finitely generated over `A`, its action on the cotangent
space factors through `f`; the same generators therefore span over `R`.

Applied to the counit of a commutative bialgebra of finite type over a noetherian base, this gives
the finite cotangent space at the identity. Over a field it is consequently finite-dimensional
and projective, which is the finiteness input for the scalar-extension description of the tangent
space and the adjoint representation in the ReductiveGroups roadmap, Layer 2.

## Main declarations

* `AlgHom.smul_cotangent_ker_eq`: the action on the cotangent space of an augmented algebra
  factors through the augmentation.
* `AlgHom.finite_cotangent_ker`: the cotangent space of an augmented noetherian algebra is finite
  over the base.
* `TauCeti.Bialgebra.instModuleFiniteCotangent`: the specialization to the counit of a finite-type
  commutative bialgebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
-/

public section

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- On `ker(f) / ker(f)²`, multiplication by `a : A` agrees with scalar multiplication by
`f a : R`, for an augmentation `f : A →ₐ[R] R`. -/
theorem smul_cotangent_ker_eq (f : A →ₐ[R] R) (a : A)
    (x : (RingHom.ker f.toRingHom).Cotangent) :
    a • x = f a • x := by
  let I := RingHom.ker f.toRingHom
  have ha : a - algebraMap R A (f a) ∈ I := by
    simp [I]
  have hzero : (a - algebraMap R A (f a)) • x = 0 :=
    Ideal.Cotangent.smul_eq_zero_of_mem ha x
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at hzero
  exact hzero

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent := by
  classical
  let I := RingHom.ker f.toRingHom
  let _ : Module.Finite A I := by
    rw [Module.Finite.iff_fg]
    exact I.fg_of_isNoetherianRing
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := I)
  refine Module.finite_def.mpr ⟨s.image I.toCotangent, ?_⟩
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective x
  have hy : y ∈ Submodule.span A (s : Set I) := by
    rw [hs]
    exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy =>
      exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul a y _ hy =>
      rw [map_smul, f.smul_cotangent_ker_eq]
      exact Submodule.smul_mem _ (f a) hy

end AlgHom

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The cotangent space at the identity of a finite-type commutative bialgebra over a noetherian
base is finite over that base. -/
instance instModuleFiniteCotangent [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Module.Finite R (RingHom.ker (counitAlgHom R A).toRingHom).Cotangent := by
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact AlgHom.finite_cotangent_ker (counitAlgHom R A)

end TauCeti.Bialgebra
