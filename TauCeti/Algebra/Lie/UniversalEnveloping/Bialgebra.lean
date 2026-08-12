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

* `TauCeti.UniversalEnvelopingAlgebra.primitive`: the primitive-element Lie homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.comulAlgHom`: the induced comultiplication.
* `TauCeti.UniversalEnvelopingAlgebra.counitAlgHom`: the induced counit.
* `TauCeti.UniversalEnvelopingAlgebra.instBialgebra`: the resulting bialgebra structure.

## References

The construction follows J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §26, and J. C. Jantzen, *Representations of Algebraic Groups*, II.1. It supplies a
prerequisite for the Kostant `ℤ`-form in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie homomorphism that sends `x` to the primitive tensor
`x ⊗ 1 + 1 ⊗ x` in the tensor square of the universal enveloping algebra. -/
@[expose] def primitive : L →ₗ⁅R⁆ U ⊗[R] U where
  toFun x :=
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
    abel

/-- The primitive-element formula for `primitive`. -/
@[simp]
theorem primitive_apply (x : L) :
    primitive R L x =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x :=
  by simp [primitive]

/-- The standard comultiplication on a universal enveloping algebra, characterized by declaring
the image of every Lie algebra element primitive. -/
def comulAlgHom : U →ₐ[R] U ⊗[R] U :=
  _root_.UniversalEnvelopingAlgebra.lift R (primitive R L)

/-- The comultiplication sends each Lie generator to a primitive element. -/
-- `simp` rewrites `ι R x` by `UniversalEnvelopingAlgebra.ι_apply`, so this is not in
-- `simp`-normal form; the `simp` lemma at the coalgebra level is `comul_ι'`.
theorem comulAlgHom_ι (x : L) :
    comulAlgHom R L (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
  simpa only [comulAlgHom, primitive_apply] using
    (_root_.UniversalEnvelopingAlgebra.lift_ι_apply R (primitive R L) x)

/-- The standard counit on a universal enveloping algebra, characterized by vanishing on the
original Lie algebra. -/
def counitAlgHom : U →ₐ[R] R :=
  _root_.UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

/-- The counit vanishes on each Lie generator. -/
-- `simp` rewrites `ι R x` by `UniversalEnvelopingAlgebra.ι_apply`, so this is not in
-- `simp`-normal form; the `simp` lemma at the coalgebra level is `counit_ι'`.
theorem counitAlgHom_ι (x : L) :
    counitAlgHom R L (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 := by
  simpa only [counitAlgHom, LieHom.zero_apply] using
    (_root_.UniversalEnvelopingAlgebra.lift_ι_apply R (0 : L →ₗ⁅R⁆ R) x)

/-- The standard cocommutative bialgebra structure on a universal enveloping algebra. -/
instance instBialgebra : Bialgebra R U :=
  Bialgebra.ofAlgHom (comulAlgHom R L) (counitAlgHom R L)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comulAlgHom_ι, map_add, Algebra.TensorProduct.map_tmul, map_one,
        TensorProduct.add_tmul, TensorProduct.tmul_add, AlgHom.id_apply]
      abel)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comulAlgHom_ι, map_add, Algebra.TensorProduct.map_tmul, counitAlgHom_ι,
        AlgHom.id_apply, map_one, TensorProduct.zero_tmul, zero_add]
      rfl)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comulAlgHom_ι, map_add, Algebra.TensorProduct.map_tmul, counitAlgHom_ι,
        AlgHom.id_apply, map_one, TensorProduct.tmul_zero, add_zero]
      rfl)

/-- The bialgebra comultiplication agrees with `comulAlgHom`. -/
theorem coalgebra_comul_eq :
    (Coalgebra.comul : U →ₗ[R] U ⊗[R] U) = (comulAlgHom R L).toLinearMap :=
  rfl

/-- The bialgebra counit agrees with `counitAlgHom`. -/
theorem coalgebra_counit_eq :
    (Coalgebra.counit : U →ₗ[R] R) = (counitAlgHom R L).toLinearMap :=
  rfl

/-- Lie generators are primitive for the bialgebra comultiplication. -/
-- `simp` rewrites `ι R x` by `UniversalEnvelopingAlgebra.ι_apply`, so this is not in
-- `simp`-normal form; the `simp` lemma is `comul_ι'`.
theorem comul_ι (x : L) :
    Coalgebra.comul (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [coalgebra_comul_eq]
  exact comulAlgHom_ι R L x

/-- Lie generators are primitive for the bialgebra comultiplication, stated in `simp`-normal
form: `simp` unfolds `ι` into `mkAlgHom` applied to the tensor algebra generator. -/
@[simp]
theorem comul_ι' (x : L) :
    Coalgebra.comul
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using comul_ι R L x

/-- The comultiplication of a power of a Lie generator is its divided binomial expansion.

This integral-coefficient formula is the input for proving that divided powers of Chevalley root
vectors are stable under comultiplication in the Kostant form. The two tensor factors commute even
though the universal enveloping algebra itself need not be commutative. -/
theorem comul_pow_ι (x : L) (n : ℕ) :
    (Coalgebra.comul (R := R)) (_root_.UniversalEnvelopingAlgebra.ι R x ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.1) ⊗ₜ[R]
          (_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.2)) := by
  rw [Bialgebra.comul_pow, comul_ι]
  have hcomm : Commute
      (_root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1)
      (1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [hcomm.add_pow']
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The bialgebra counit vanishes on Lie generators. -/
-- `simp` rewrites `ι R x` by `UniversalEnvelopingAlgebra.ι_apply`, so this is not in
-- `simp`-normal form; the `simp` lemma is `counit_ι'`.
theorem counit_ι (x : L) :
    (Coalgebra.counit (R := R)) (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 := by
  rw [coalgebra_counit_eq]
  exact counitAlgHom_ι R L x

/-- The bialgebra counit vanishes on Lie generators, stated in `simp`-normal form: `simp`
unfolds `ι` into `mkAlgHom` applied to the tensor algebra generator. -/
@[simp]
theorem counit_ι' (x : L) :
    (Coalgebra.counit (R := R))
      (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = 0 := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using counit_ι R L x

/-- The standard bialgebra structure on a universal enveloping algebra is cocommutative. -/
instance instIsCocomm : Coalgebra.IsCocomm R U where
  comm_comp_comul := by
    have h :
        (Algebra.TensorProduct.comm R U U : U ⊗[R] U →ₐ[R] U ⊗[R] U).comp
            (comulAlgHom R L) =
          comulAlgHom R L := by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        comulAlgHom_ι, map_add]
      change
        (TensorProduct.comm R U U)
              (_root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1) +
            (TensorProduct.comm R U U)
              (1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x) = _
      simp only [TensorProduct.comm_tmul]
      abel
    exact congrArg AlgHom.toLinearMap h

end TauCeti.UniversalEnvelopingAlgebra
