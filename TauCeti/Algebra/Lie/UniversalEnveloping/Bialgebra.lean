/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# The bialgebra structure on a universal enveloping algebra

This file equips the universal enveloping algebra of a Lie algebra with its standard
cocommutative bialgebra structure. Every element of the original Lie algebra is primitive:
its comultiplication is `x ⊗ 1 + 1 ⊗ x`, and its counit is zero.

The construction is needed for the Kostant integral form in the Chevalley--Demazure construction.
The integral form is generated inside a universal enveloping algebra by divided powers of root
vectors and binomial coefficients in coroots; its stability under this comultiplication is what
eventually makes the corresponding distribution algebra a Hopf algebra over `ℤ`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.instBialgebra`: the resulting bialgebra structure.
* `TauCeti.UniversalEnvelopingAlgebra.comul_ι`: the comultiplication of a Lie generator.
* `TauCeti.UniversalEnvelopingAlgebra.counit_ι`: the counit of a Lie generator.
* `TauCeti.Bialgebra.comul_pow_of_primitive`: the binomial formula for a primitive element.
* `TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow`: the comultiplication of a generator power.

## References

The construction follows J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §26, and J. C. Jantzen, *Representations of Algebraic Groups*, II.1. It supplies a
prerequisite for the Kostant `ℤ`-form in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra

universe u w

/-- The comultiplication of a power of a primitive element is its binomial expansion. -/
theorem comul_pow_of_primitive
    {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Bialgebra R A]
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a) (n : ℕ) :
    (Coalgebra.comul (R := R)) (a ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((a ^ mn.1) ⊗ₜ[R] (a ^ mn.2)) := by
  rw [Bialgebra.comul_pow, h]
  have hcomm : Commute (a ⊗ₜ[R] 1) (1 ⊗ₜ[R] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [hcomm.add_pow']
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end TauCeti.Bialgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The standard cocommutative bialgebra structure on a universal enveloping algebra. -/
instance instBialgebra : Bialgebra R U :=
  let primitive : L →ₗ⁅R⁆ U ⊗[R] U :=
    { toFun x :=
        _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
          1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x
      map_add' := by
        intros
        simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
        abel
      map_smul' := by intros; simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      map_lie' := by
        intro x y
        simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_eq_add_neg,
          add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, neg_add_rev,
          TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.neg_tmul,
          TensorProduct.tmul_neg]
        abel }
  have primitive_apply (x : L) :
      primitive x =
        _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
          1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := rfl
  let comul := _root_.UniversalEnvelopingAlgebra.lift R primitive
  let counit := _root_.UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)
  have comul_ι (x : L) :
      comul (_root_.UniversalEnvelopingAlgebra.ι R x) =
        _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
          1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
    simpa only [comul, primitive_apply] using
      (_root_.UniversalEnvelopingAlgebra.lift_ι_apply R primitive x)
  have counit_ι (x : L) : counit (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 := by
    simpa only [counit, LieHom.zero_apply] using
      (_root_.UniversalEnvelopingAlgebra.lift_ι_apply R (0 : L →ₗ⁅R⁆ R) x)
  Bialgebra.ofAlgHom comul counit
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comul_ι, map_add, Algebra.TensorProduct.map_tmul, map_one,
        TensorProduct.add_tmul, TensorProduct.tmul_add, AlgHom.id_apply]
      abel)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comul_ι, map_add, Algebra.TensorProduct.map_tmul, counit_ι,
        AlgHom.id_apply, map_one, TensorProduct.zero_tmul, zero_add]
      rfl)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comul_ι, map_add, Algebra.TensorProduct.map_tmul, counit_ι,
        AlgHom.id_apply, map_one, TensorProduct.tmul_zero, add_zero]
      rfl)

/-- Lie generators are primitive for the bialgebra comultiplication, stated in `simp`-normal
form: `simp` unfolds `ι` into `mkAlgHom` applied to the tensor algebra generator. -/
@[simp]
theorem comul_ι (x : L) :
    Coalgebra.comul
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) := by
  change (instBialgebra R L).toCoalgebra.toCoalgebraStruct.comul
    (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = _
  dsimp only [instBialgebra, Bialgebra.toCoalgebra, Coalgebra.toCoalgebraStruct,
    Bialgebra.ofAlgHom, Bialgebra.mk', CoalgebraStruct.comul]
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply]
  exact _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The comultiplication of a power of a Lie generator is its binomial expansion.

This integral-coefficient formula is the input for proving that divided powers of Chevalley root
vectors are stable under comultiplication in the Kostant form. The two tensor factors commute even
though the universal enveloping algebra itself need not be commutative. -/
theorem comul_ι_pow (x : L) (n : ℕ) :
    (Coalgebra.comul (R := R)) (_root_.UniversalEnvelopingAlgebra.ι R x ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.1) ⊗ₜ[R]
          (_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.2)) := by
  apply TauCeti.Bialgebra.comul_pow_of_primitive _
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using comul_ι R L x

/-- The bialgebra counit vanishes on Lie generators, stated in `simp`-normal form: `simp`
unfolds `ι` into `mkAlgHom` applied to the tensor algebra generator. -/
@[simp]
theorem counit_ι (x : L) :
    (Coalgebra.counit (R := R))
      (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = 0 := by
  change (instBialgebra R L).toCoalgebra.toCoalgebraStruct.counit
    (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = 0
  dsimp only [instBialgebra, Bialgebra.toCoalgebra, Coalgebra.toCoalgebraStruct,
    Bialgebra.ofAlgHom, Bialgebra.mk', CoalgebraStruct.counit]
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply]
  exact _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The standard bialgebra structure on a universal enveloping algebra is cocommutative. -/
instance instIsCocomm : Coalgebra.IsCocomm R U where
  comm_comp_comul := by
    have h :
        (Algebra.TensorProduct.comm R U U : U ⊗[R] U →ₐ[R] U ⊗[R] U).comp
            (Bialgebra.comulAlgHom R U) =
          Bialgebra.comulAlgHom R U := by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply, _root_.UniversalEnvelopingAlgebra.ι_apply, comul_ι,
        map_add]
      -- The algebra equivalence and linear equivalence implementing the tensor swap have
      -- definitionally equal underlying functions, but their wrappers do not rewrite directly.
      change
        (TensorProduct.comm R U U)
              (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) ⊗ₜ[R] 1) +
            (TensorProduct.comm R U U)
              (1 ⊗ₜ[R]
                _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = _
      simp only [TensorProduct.comm_tmul]
      abel
    exact congrArg AlgHom.toLinearMap h

end TauCeti.UniversalEnvelopingAlgebra
