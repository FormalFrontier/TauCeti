/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import TauCeti.Algebra.Bialgebra.Primitive
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality

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

* `TauCeti.UniversalEnvelopingAlgebra.primitiveComul`: the comultiplication, as an algebra
  homomorphism, before it is installed as coalgebra data.
* `TauCeti.UniversalEnvelopingAlgebra.augmentation`: the counit, as an algebra homomorphism,
  before it is installed as coalgebra data.
* `TauCeti.UniversalEnvelopingAlgebra.instBialgebra`: the resulting bialgebra structure.
* `TauCeti.UniversalEnvelopingAlgebra.mapBialgHom`: the bialgebra homomorphism induced by a Lie
  homomorphism.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.comul_ι`: the comultiplication of a Lie generator.
* `TauCeti.UniversalEnvelopingAlgebra.counit_ι`: the counit of a Lie generator.
* `TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow`: the comultiplication of a generator power.
* `TauCeti.UniversalEnvelopingAlgebra.mapBialgHom_id` and
  `TauCeti.UniversalEnvelopingAlgebra.mapBialgHom_comp`: the induced bialgebra homomorphisms are
  functorial.

## References

The construction follows J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §26, and J. C. Jantzen, *Representations of Algebraic Groups*, II.1. It supplies a
prerequisite for the Kostant `ℤ`-form in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.

The formal development is modelled on the closest Mathlib analogue,
`Mathlib/RingTheory/Bialgebra/SymmetricAlgebra.lean` by Robert Hawkins, which makes the generators
of a symmetric algebra primitive: the declaration order (structure, generator equations,
cocommutativity), the use of `Bialgebra.ofAlgHom` on maps produced by a universal property, and
the identification of the instance projections with those maps are all adapted from that file.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The comultiplication of the standard bialgebra structure on a universal enveloping algebra,
as an algebra homomorphism: the unique algebra homomorphism making every Lie generator primitive.

The bialgebra instance below is built from this map, so it is the comultiplication of that
instance; `comulAlgHom_eq` records the identification. -/
def primitiveComul : U →ₐ[R] U ⊗[R] U :=
  _root_.UniversalEnvelopingAlgebra.lift R
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

/-- Lie generators are primitive for `primitiveComul`. -/
theorem primitiveComul_ι (x : L) :
    primitiveComul R L (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [primitiveComul, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The augmentation of a universal enveloping algebra: the algebra homomorphism to the base ring
killing every Lie generator.

The bialgebra instance below is built from this map, so it is the counit of that instance;
`counitAlgHom_eq` records the identification. -/
def augmentation : U →ₐ[R] R :=
  _root_.UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

/-- The augmentation kills the Lie generators. -/
theorem augmentation_ι (x : L) :
    augmentation R L (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 := by
  rw [augmentation, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.zero_apply]

/-- The standard cocommutative bialgebra structure on a universal enveloping algebra. -/
instance instBialgebra : Bialgebra R U :=
  Bialgebra.ofAlgHom (primitiveComul R L) (augmentation R L)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        primitiveComul_ι, map_add, Algebra.TensorProduct.map_tmul, map_one,
        TensorProduct.add_tmul, TensorProduct.tmul_add, AlgHom.id_apply]
      abel)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        primitiveComul_ι, map_add, Algebra.TensorProduct.map_tmul, augmentation_ι,
        AlgHom.id_apply, map_one, TensorProduct.zero_tmul, zero_add]
      rfl)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        primitiveComul_ι, map_add, Algebra.TensorProduct.map_tmul, augmentation_ι,
        AlgHom.id_apply, map_one, TensorProduct.tmul_zero, add_zero]
      rfl)

/-- The comultiplication of `instBialgebra` is the algebra homomorphism it was built from.
This is the one place where the internal shape of `Bialgebra.ofAlgHom` is used; the generator
equations below go through this identification rather than through unification. -/
theorem comulAlgHom_eq : Bialgebra.comulAlgHom R U = primitiveComul R L := rfl

/-- The counit of `instBialgebra` is the algebra homomorphism it was built from. -/
theorem counitAlgHom_eq : Bialgebra.counitAlgHom R U = augmentation R L := rfl

/-- Lie generators are primitive for the bialgebra comultiplication. -/
-- `simp`-normal form is `comul_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem comul_ι (x : L) :
    Coalgebra.comul (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
  have h : (Coalgebra.comul : U →ₗ[R] U ⊗[R] U) = (primitiveComul R L).toLinearMap := by
    rw [← Bialgebra.toLinearMap_comulAlgHom (R := R) (A := U), comulAlgHom_eq]
  rw [h]
  exact primitiveComul_ι R L x

/-- The `simp`-normal form of `comul_ι`, stated for the canonical generators as `simp` writes
them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem comul_ι' (x : L) :
    Coalgebra.comul (R := R)
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using comul_ι R L x

/-- The bialgebra counit vanishes on Lie generators. -/
-- `simp`-normal form is `counit_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem counit_ι (x : L) :
    Coalgebra.counit (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 := by
  have h : (Coalgebra.counit : U →ₗ[R] R) = (augmentation R L).toLinearMap := by
    rw [← Bialgebra.toLinearMap_counitAlgHom (R := R) (A := U), counitAlgHom_eq]
  rw [h]
  exact augmentation_ι R L x

/-- The `simp`-normal form of `counit_ι`, stated for the canonical generators as `simp` writes
them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem counit_ι' (x : L) :
    Coalgebra.counit (R := R)
      (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) = 0 := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using counit_ι R L x

/-- The comultiplication of a power of a Lie generator is its binomial expansion.

This integral-coefficient formula is the input for proving that divided powers of Chevalley root
vectors are stable under comultiplication in the Kostant form. The two tensor factors commute even
though the universal enveloping algebra itself need not be commutative. -/
theorem comul_ι_pow (x : L) (n : ℕ) :
    (Coalgebra.comul (R := R)) (_root_.UniversalEnvelopingAlgebra.ι R x ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.1) ⊗ₜ[R]
          (_root_.UniversalEnvelopingAlgebra.ι R x ^ mn.2)) :=
  TauCeti.Bialgebra.comul_pow_of_primitive _ (comul_ι R L x) n

variable {L₁ : Type v} {L₂ : Type w} {L₃ : Type x}
variable [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
variable [LieRing L₃] [LieAlgebra R L₃]

/-- A Lie algebra homomorphism induces a bialgebra homomorphism of universal enveloping
algebras. -/
noncomputable def mapBialgHom (f : LieHom R L₁ L₂) :
    _root_.UniversalEnvelopingAlgebra R L₁ →ₐc[R]
      _root_.UniversalEnvelopingAlgebra R L₂ :=
  .ofAlgHom (map R f)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        Bialgebra.counitAlgHom_apply, map_ι, counit_ι])
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply, map_ι, comul_ι, map_add,
        Algebra.TensorProduct.map_tmul, map_one])

/-- The algebra homomorphism underlying `mapBialgHom` is the induced map `map`. -/
@[simp]
theorem mapBialgHom_toAlgHom (f : LieHom R L₁ L₂) :
    (mapBialgHom R f : _root_.UniversalEnvelopingAlgebra R L₁ →ₐ[R]
      _root_.UniversalEnvelopingAlgebra R L₂) = map R f :=
  AlgHom.ext fun _ => rfl

/-- The bialgebra homomorphism induced by a Lie homomorphism agrees with it on Lie generators. -/
-- `simp`-normal form is `mapBialgHom_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem mapBialgHom_ι (f : LieHom R L₁ L₂) (x : L₁) :
    mapBialgHom R f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R (f x) :=
  map_ι R f x

/-- The `simp`-normal form of `mapBialgHom_ι`, stated for the canonical generators as `simp`
writes them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem mapBialgHom_ι' (f : LieHom R L₁ L₂) (x : L₁) :
    mapBialgHom R f
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L₁ (TensorAlgebra.ι R x)) =
      _root_.UniversalEnvelopingAlgebra.mkAlgHom R L₂ (TensorAlgebra.ι R (f x)) := by
  simpa using mapBialgHom_ι R f x

/-- The identity Lie homomorphism induces the identity bialgebra homomorphism. -/
@[simp]
theorem mapBialgHom_id :
    mapBialgHom R (LieHom.id : LieHom R L₁ L₁) =
      BialgHom.id R (_root_.UniversalEnvelopingAlgebra R L₁) := by
  apply BialgHom.coe_toAlgHom_injective
  rw [mapBialgHom_toAlgHom, map_id, BialgHom.id_toAlgHom]

/-- Composition of Lie homomorphisms becomes composition of the induced bialgebra
homomorphisms. -/
@[simp]
theorem mapBialgHom_comp (f : LieHom R L₁ L₂) (g : LieHom R L₂ L₃) :
    mapBialgHom R (g.comp f) = (mapBialgHom R g).comp (mapBialgHom R f) := by
  apply BialgHom.coe_toAlgHom_injective
  rw [mapBialgHom_toAlgHom, map_comp, BialgHom.comp_toAlgHom, mapBialgHom_toAlgHom,
    mapBialgHom_toAlgHom]

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
        Bialgebra.comulAlgHom_apply, comul_ι, map_add, AlgEquiv.toAlgHom_apply,
        Algebra.TensorProduct.comm_tmul]
      abel
    exact congrArg AlgHom.toLinearMap h

end TauCeti.UniversalEnvelopingAlgebra
