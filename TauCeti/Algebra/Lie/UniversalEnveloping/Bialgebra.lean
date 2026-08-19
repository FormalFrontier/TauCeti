/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

* `TauCeti.UniversalEnvelopingAlgebra.instBialgebra`: the bialgebra structure. Its
  comultiplication and counit are given inline, so that `Bialgebra.comulAlgHom` and
  `Bialgebra.counitAlgHom` are the names for them.
* `TauCeti.UniversalEnvelopingAlgebra.mapBialgHom`: the bialgebra homomorphism induced by a Lie
  homomorphism.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.comul_ι`: the comultiplication of a Lie generator.
* `TauCeti.UniversalEnvelopingAlgebra.counit_ι`: the counit of a Lie generator.
* `TauCeti.UniversalEnvelopingAlgebra.comul_ι_pow`: the comultiplication of a generator power.
* `TauCeti.UniversalEnvelopingAlgebra.comul_ι_dividedPower` and
  `TauCeti.UniversalEnvelopingAlgebra.comul_ι_choose`: the coefficient-one coproduct formulas
  for the two families of Kostant generators.
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

/-- Local notation for the universal enveloping algebra currently under consideration. -/
local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The standard cocommutative bialgebra structure on a universal enveloping algebra: the unique
one for which every Lie generator is primitive.

The comultiplication and the counit are supplied inline, as the algebra homomorphisms the
universal property produces from `x ↦ x ⊗ 1 + 1 ⊗ x` and from `0`, so that `Bialgebra.comulAlgHom`
and `Bialgebra.counitAlgHom` remain the names for them. How they act on Lie generators is recorded
by `comulAlgHom_ι` and `counitAlgHom_ι` below. -/
instance instBialgebra : Bialgebra R U :=
  Bialgebra.ofAlgHom
    (_root_.UniversalEnvelopingAlgebra.lift R
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
          abel })
    (_root_.UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R))
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.coe_mk, map_add,
        Algebra.TensorProduct.map_tmul, map_one, TensorProduct.add_tmul, TensorProduct.tmul_add,
        AlgHom.id_apply]
      abel)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.coe_mk, map_add,
        Algebra.TensorProduct.map_tmul, LieHom.zero_apply, AlgHom.id_apply, map_one,
        TensorProduct.zero_tmul, zero_add]
      rfl)
    (by
      apply _root_.UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext
      intro x
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
        _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.coe_mk, map_add,
        Algebra.TensorProduct.map_tmul, LieHom.zero_apply, AlgHom.id_apply, map_one,
        TensorProduct.tmul_zero, add_zero]
      rfl)

/-- The comultiplication of `instBialgebra`, evaluated at a Lie generator.

Together with `counitAlgHom_ι` this is the only place where the internal shape of
`Bialgebra.ofAlgHom` is used: the comultiplication of the instance just above is the algebra
homomorphism given to it, so the universal property computes it on generators. The generator
equations below go through these two lemmas rather than through unification. -/
private theorem comulAlgHom_ι (x : L) :
    Bialgebra.comulAlgHom R U (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- The counit of `instBialgebra` kills the Lie generators. -/
private theorem counitAlgHom_ι (x : L) :
    Bialgebra.counitAlgHom R U (_root_.UniversalEnvelopingAlgebra.ι R x) = 0 :=
  _root_.UniversalEnvelopingAlgebra.lift_ι_apply R _ x

/-- Lie generators are primitive for the bialgebra comultiplication. -/
-- `simp`-normal form is `comul_ι'`, since `simp` unfolds `ι` through `ι_apply`.
theorem comul_ι (x : L) :
    Coalgebra.comul (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x) =
      _root_.UniversalEnvelopingAlgebra.ι R x ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [← Bialgebra.comulAlgHom_apply (R := R)]
  exact comulAlgHom_ι R L x

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
  rw [← Bialgebra.counitAlgHom_apply (R := R)]
  exact counitAlgHom_ι R L x

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

section Rational

variable (L : Type v) [LieRing L] [LieAlgebra ℚ L]

attribute [local instance] TauCeti.moduleNNRat

/-- The comultiplication of a divided power of a canonical Lie generator is the antidiagonal
sum of the corresponding divided powers in the two tensor factors. -/
theorem comul_ι_dividedPower (x : L) (n : ℕ) :
    (Coalgebra.comul (R := ℚ))
        (Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) =
      ∑ ij ∈ Finset.antidiagonal n,
        Associative.dividedPower ij.1 (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ⊗ₜ[ℚ]
          Associative.dividedPower ij.2 (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  TauCeti.Bialgebra.comul_dividedPower_of_primitive _ (comul_ι ℚ L x) n

/-- The `simp`-normal form of `comul_ι_dividedPower`, stated for canonical generators as
`simp` writes them. -/
@[simp]
theorem comul_ι_dividedPower' (x : L) (n : ℕ) :
    (Coalgebra.comul (R := ℚ))
        (Associative.dividedPower n
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x))) =
      ∑ ij ∈ Finset.antidiagonal n,
        Associative.dividedPower ij.1
            (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) ⊗ₜ[ℚ]
          Associative.dividedPower ij.2
            (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using comul_ι_dividedPower L x n

/-- Every positive divided power of a canonical Lie generator has counit zero. -/
theorem counit_ι_dividedPower (x : L) (n : ℕ) :
    (Coalgebra.counit (R := ℚ))
        (Associative.dividedPower (n + 1) (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) = 0 :=
  TauCeti.Bialgebra.counit_dividedPower_of_counit_eq_zero _ (counit_ι ℚ L x) n

/-- The `simp`-normal form of `counit_ι_dividedPower`, stated for canonical generators as
`simp` writes them. -/
@[simp]
theorem counit_ι_dividedPower' (x : L) (n : ℕ) :
    (Coalgebra.counit (R := ℚ))
        (Associative.dividedPower (n + 1)
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x))) = 0 := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using counit_ι_dividedPower L x n

/-- The comultiplication of a binomial coefficient in a canonical Lie generator is the
antidiagonal sum of the corresponding binomial coefficients in the two tensor factors. -/
theorem comul_ι_choose (x : L) (n : ℕ) :
    (Coalgebra.comul (R := ℚ)) (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) n) =
      ∑ ij ∈ Finset.antidiagonal n,
        Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ij.1 ⊗ₜ[ℚ]
          Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ij.2 :=
  TauCeti.Bialgebra.comul_choose_of_primitive _ (comul_ι ℚ L x) n

/-- The `simp`-normal form of `comul_ι_choose`, stated for canonical generators as `simp`
writes them. -/
@[simp]
theorem comul_ι_choose' (x : L) (n : ℕ) :
    (Coalgebra.comul (R := ℚ))
        (Ring.choose
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) n) =
      ∑ ij ∈ Finset.antidiagonal n,
        Ring.choose
            (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) ij.1 ⊗ₜ[ℚ]
          Ring.choose
            (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) ij.2 := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using comul_ι_choose L x n

/-- Every positive binomial coefficient in a canonical Lie generator has counit zero. -/
theorem counit_ι_choose (x : L) (n : ℕ) :
    (Coalgebra.counit (R := ℚ))
        (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ x) (n + 1)) = 0 :=
  TauCeti.Bialgebra.counit_choose_of_counit_eq_zero _ (counit_ι ℚ L x) n

/-- The `simp`-normal form of `counit_ι_choose`, stated for canonical generators as `simp`
writes them. -/
@[simp]
theorem counit_ι_choose' (x : L) (n : ℕ) :
    (Coalgebra.counit (R := ℚ))
        (Ring.choose
          (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ L (TensorAlgebra.ι ℚ x)) (n + 1)) = 0 := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using counit_ι_choose L x n

end Rational

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
