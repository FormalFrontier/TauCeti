/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Additive structure on comodule morphisms

This file records the pointwise additive-monoid structure on morphisms of right comodules.
The underlying linear maps already have zero, addition, natural-number scalar
multiplication, and finite sums; the only point to check is that these operations still
commute with the coactions.

This is basic infrastructure for the reductive-groups roadmap Layer 1 target
"Comodules over a coalgebra/Hopf algebra": the representation category of an affine group
scheme should have additive hom-sets before finite-dimensional, tensor, and dual structures
are built on top.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Hom

/-- The zero morphism of right comodules. -/
instance instZero : Zero (Hom R C M N) where
  zero :=
    { toLinearMap := 0
      map_coact := by
        ext m
        simp }

/-- Addition of right-comodule morphisms, defined pointwise. -/
instance instAdd : Add (Hom R C M N) where
  add f g :=
    { toLinearMap := f.toLinearMap + g.toLinearMap
      map_coact := by
        ext m
        simp [TensorProduct.map_add_left, map_coact_apply] }

/-- Scalar multiplication of right-comodule morphisms, defined pointwise. -/
instance instSMul : SMul R (Hom R C M N) where
  smul r f :=
    { toLinearMap := r • f.toLinearMap
      map_coact := by
        ext m
        simp [TensorProduct.map_smul_left, map_coact_apply] }

/-- The zero comodule morphism has the zero linear map underneath. -/
@[simp]
theorem zero_toLinearMap : (0 : Hom R C M N).toLinearMap = 0 :=
  rfl

/-- Addition of comodule morphisms is addition of the underlying linear maps. -/
@[simp]
theorem add_toLinearMap (f g : Hom R C M N) : (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- Scalar multiplication of comodule morphisms is scalar multiplication of the underlying
linear maps. -/
@[simp]
theorem smul_toLinearMap (r : R) (f : Hom R C M N) : (r • f).toLinearMap = r • f.toLinearMap :=
  rfl

/-- The zero comodule morphism evaluates to zero. -/
@[simp]
theorem zero_apply (m : M) : (0 : Hom R C M N) m = 0 :=
  rfl

/-- Addition of comodule morphisms is pointwise addition. -/
@[simp]
theorem add_apply (f g : Hom R C M N) (m : M) : (f + g) m = f m + g m :=
  rfl

/-- Scalar multiplication of comodule morphisms is pointwise scalar multiplication. -/
@[simp]
theorem smul_apply (r : R) (f : Hom R C M N) (m : M) : (r • f) m = r • f m :=
  rfl

/-- Comodule morphisms form an additive commutative monoid under pointwise zero and
addition, with the default natural-number scalar multiplication `nsmulRec`. -/
instance instAddCommMonoid : AddCommMonoid (Hom R C M N) where
  zero := 0
  add := (· + ·)
  nsmul := nsmulRec
  zero_add f := by
    ext m
    simp
  add_zero f := by
    ext m
    simp
  add_assoc f g h := by
    ext m
    simp [add_assoc]
  add_comm f g := by
    ext m
    simp [add_comm]

/-- The map sending a comodule morphism to its underlying linear map, bundled as an
additive monoid homomorphism. -/
@[expose] def toLinearMapAddMonoidHom : Hom R C M N →+ M →ₗ[R] N where
  toFun f := f.toLinearMap
  map_zero' := zero_toLinearMap
  map_add' := add_toLinearMap

/-- Comodule morphisms form an `R`-module under pointwise scalar multiplication. -/
instance instModule : Module R (Hom R C M N) :=
  fast_instance%
  Function.Injective.module R toLinearMapAddMonoidHom (fun f g h => by
    ext m
    exact LinearMap.congr_fun h m) fun _ _ => smul_toLinearMap _ _

/-- Natural-number scalar multiplication of comodule morphisms is pointwise. -/
@[simp]
theorem nsmul_apply (n : ℕ) (f : Hom R C M N) (m : M) : (n • f) m = n • f m := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      rfl
  | succ n ih =>
      rw [succ_nsmul, add_apply, ih, succ_nsmul]

/-- Natural-number scalar multiplication of comodule morphisms is natural-number scalar
multiplication of the underlying linear maps. -/
@[simp]
theorem nsmul_toLinearMap (n : ℕ) (f : Hom R C M N) : (n • f).toLinearMap = n • f.toLinearMap := by
  ext m
  simp

/-- Finite sums of comodule morphisms are evaluated pointwise. -/
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Hom R C M N) (m : M) :
    (∑ i ∈ s, f i) m = ∑ i ∈ s, f i m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- Finite sums of comodule morphisms are finite sums of the underlying linear maps. -/
@[simp]
theorem sum_toLinearMap {ι : Type*} (s : Finset ι) (f : ι → Hom R C M N) :
    (∑ i ∈ s, f i).toLinearMap = ∑ i ∈ s, (f i).toLinearMap := by
  ext m
  simp

section Comp

variable {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- Composition of comodule morphisms is additive in the left argument. -/
@[simp]
theorem add_comp (g h : Hom R C N P) (f : Hom R C M N) :
    comp (g + h) f = comp g f + comp h f := by
  ext m
  rfl

/-- Composition of comodule morphisms is additive in the right argument. -/
@[simp]
theorem comp_add (g : Hom R C N P) (f h : Hom R C M N) :
    comp g (f + h) = comp g f + comp g h := by
  ext m
  exact map_add g.toLinearMap (f m) (h m)

/-- Composition of comodule morphisms is compatible with scalar multiplication in the left
argument. -/
@[simp]
theorem smul_comp (r : R) (g : Hom R C N P) (f : Hom R C M N) :
    comp (r • g) f = r • comp g f := by
  ext m
  rfl

/-- Composition of comodule morphisms is compatible with scalar multiplication in the right
argument. -/
@[simp]
theorem comp_smul (r : R) (g : Hom R C N P) (f : Hom R C M N) :
    comp g (r • f) = r • comp g f := by
  ext m
  exact map_smul g.toLinearMap r (f m)

/-- Composing the zero morphism on the left gives the zero morphism. -/
@[simp]
theorem zero_comp (f : Hom R C M N) : comp (0 : Hom R C N P) f = 0 := by
  ext m
  rfl

/-- Composing the zero morphism on the right gives the zero morphism. -/
@[simp]
theorem comp_zero (g : Hom R C N P) : comp g (0 : Hom R C M N) = 0 := by
  ext m
  exact map_zero g.toLinearMap

end Comp

end Hom

end Comodule

end TauCeti
