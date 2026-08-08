/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf structure on a symmetric algebra

Mathlib equips `SymmetricAlgebra R M` with the cocommutative bialgebra structure in which each
generator `ι x` is primitive, `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and `ε(ι x) = 0`, but it stops short
of the antipode. Over a commutative ring `R` the symmetric algebra is a *Hopf* algebra: the
antipode is the algebra map sending each `ι x` to `-ι x`.

## Main declarations

* `TauCeti.SymmetricAlgebra.instHopfAlgebra`: the Hopf algebra structure on
  `SymmetricAlgebra R M` over a commutative ring `R`.
* `TauCeti.SymmetricAlgebra.antipode_ι`: the Hopf antipode sends each generator to its
  negative.
* `TauCeti.SymmetricAlgebra.lift_symm_apply`: the inverse of `SymmetricAlgebra.lift`
  evaluates an algebra map at generators.
* `TauCeti.SymmetricAlgebra.convMul_apply_ι`: convolution of algebra maps evaluates on
  generators by adding their values.

## References

The cocommutative bialgebra structure on the symmetric algebra is Robert Hawkins' Mathlib work
in `Mathlib.RingTheory.Bialgebra.SymmetricAlgebra`. The Hopf-algebra-from-an-antipode
constructor `HopfAlgebra.ofAlgHom` is from `Mathlib.RingTheory.HopfAlgebra.Basic`.
-/

public section

open Coalgebra HopfAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace SymmetricAlgebra

universe u v w

section Hopf

variable (R : Type u) [CommRing R] (M : Type v) [AddCommMonoid M] [Module R M]

/-- The antipode of the symmetric-algebra Hopf algebra: the `R`-algebra map sending each
generator `ι x` to `-ι x`. -/
noncomputable def antipodeHom :
    _root_.SymmetricAlgebra R M →ₐ[R] _root_.SymmetricAlgebra R M :=
  _root_.SymmetricAlgebra.lift (-(_root_.SymmetricAlgebra.ι R M))

@[simp]
theorem antipodeHom_ι (x : M) :
    antipodeHom R M (_root_.SymmetricAlgebra.ι R M x) =
      -(_root_.SymmetricAlgebra.ι R M x) := by
  simp [antipodeHom]

/-- The symmetric algebra over a commutative ring is a Hopf algebra: its antipode sends each
generator `ι x` to `-ι x`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (_root_.SymmetricAlgebra R M) :=
  .ofAlgHom (antipodeHom R M)
    (by
      ext x
      simp only [LinearMap.coe_comp, LinearMap.coe_coe, AlgHom.coe_comp, Function.comp_apply,
        Bialgebra.comulAlgHom_apply, _root_.SymmetricAlgebra.comul_ι, map_add,
        _root_.SymmetricAlgebra.counitAlgHom_eq, Algebra.ofId_apply]
      erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
      simp [_root_.SymmetricAlgebra.algebraMapInv_ι])
    (by
      ext x
      simp [_root_.SymmetricAlgebra.comul_ι, _root_.SymmetricAlgebra.algebraMapInv_ι])

/-- The Hopf-algebra antipode on a symmetric algebra sends each generator `ι x` to `-ι x`. -/
@[simp]
theorem antipode_ι (x : M) :
    antipode R (_root_.SymmetricAlgebra.ι R M x) = -(_root_.SymmetricAlgebra.ι R M x) :=
  antipodeHom_ι R M x

end Hopf

section Lift

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommSemiring A] [Algebra R A]

/-- The inverse of the symmetric-algebra lift evaluates an algebra map at a generator: it sends
`H` to the linear map `x ↦ H (ι x)`. -/
@[simp]
theorem lift_symm_apply (H : _root_.SymmetricAlgebra R M →ₐ[R] A) (x : M) :
    _root_.SymmetricAlgebra.lift.symm H x = H (_root_.SymmetricAlgebra.ι R M x) := by
  conv_rhs => rw [← Equiv.apply_symm_apply _root_.SymmetricAlgebra.lift H]
  rw [_root_.SymmetricAlgebra.lift_ι_apply]

/-- The convolution product of two points of a symmetric algebra is, on each generator, the sum
of their values: `(F * G)(ι x) = F(ι x) + G(ι x)`. -/
@[simp]
theorem convMul_apply_ι (F G : WithConv (_root_.SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    (F * G).ofConv (_root_.SymmetricAlgebra.ι R M x) =
      F.ofConv (_root_.SymmetricAlgebra.ι R M x) +
        G.ofConv (_root_.SymmetricAlgebra.ι R M x) := by
  simpa [_root_.SymmetricAlgebra.comul_ι, Algebra.TensorProduct.lift_tmul] using
    AlgHom.convMul_apply F G (_root_.SymmetricAlgebra.ι R M x)

end Lift

end SymmetricAlgebra

end TauCeti
