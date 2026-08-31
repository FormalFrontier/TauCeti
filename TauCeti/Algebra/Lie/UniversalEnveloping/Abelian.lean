/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic

/-!
# Enveloping algebras of abelian Lie algebras

The universal enveloping algebra of an abelian Lie algebra is its symmetric algebra. This file
constructs the canonical algebra equivalence directly from the two universal properties. This is a
standalone UEA--symmetric-algebra equivalence prerequisite: it does not claim to provide the Layer 3
triangular-decomposition isomorphism, non-vacuous Verma-module results, or the downstream Layer 7
Harish--Chandra endpoint.

The construction uses Mathlib's `UniversalEnvelopingAlgebra.lift` and `hom_ext`,
`SymmetricAlgebra.lift` and `algHom_ext`, and `Algebra.isMulCommutative_adjoin` APIs. Its
two-universal-property proof pattern is adapted from `Mathlib/Algebra/Lie/Free.lean`, specifically
`FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`.

## Main definition

* `TauCeti.UniversalEnvelopingAlgebra.instIsMulCommutativeUniversalEnvelopingAlgebra`:
  the enveloping algebra of an abelian Lie algebra has commutative multiplication.
* `TauCeti.UniversalEnvelopingAlgebra.equivSymmetricAlgebra`: the canonical algebra equivalence
  from the enveloping algebra of an abelian Lie algebra to its symmetric algebra.
-/

public section

open scoped IsMulCommutative

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [IsLieAbelian L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The universal enveloping algebra of an abelian Lie algebra has commutative multiplication. -/
instance instIsMulCommutativeUniversalEnvelopingAlgebra : IsMulCommutative U := by
  let S := Algebra.adjoin R
    (Set.range ⇑(_root_.UniversalEnvelopingAlgebra.ι R : LieHom R L U))
  have hS : IsMulCommutative S := Algebra.isMulCommutative_adjoin R <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (commute_of_lie_eq_zero (AlgHom.id R U) (trivial_lie_zero L L x y)).eq
  apply IsMulCommutative.of_comm
  intro a b
  let a' : S := ⟨a, by simp only [S, adjoin_range_ι R L]; simp⟩
  let b' : S := ⟨b, by simp only [S, adjoin_range_ι R L]; simp⟩
  simpa only [Subalgebra.coe_mul, a', b'] using
    congrArg Subtype.val (hS.is_comm.comm a' b')

private noncomputable def toSymmetricLie : LieHom R L (SymmetricAlgebra R L) :=
  { SymmetricAlgebra.ι R L with
    map_lie' := by
      intro x y
      simp [trivial_lie_zero, LieRing.of_associative_ring_bracket, mul_comm] }

@[simp]
private theorem toSymmetricLie_apply (x : L) :
    toSymmetricLie R L x = SymmetricAlgebra.ι R L x :=
  rfl

private noncomputable def toSymmetric : U →ₐ[R] SymmetricAlgebra R L :=
  _root_.UniversalEnvelopingAlgebra.lift R (toSymmetricLie R L)

private noncomputable def ofSymmetric : SymmetricAlgebra R L →ₐ[R] U := by
  exact SymmetricAlgebra.lift (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap

private theorem toSymmetric_ι (x : L) :
    toSymmetric R L (_root_.UniversalEnvelopingAlgebra.ι R x) = SymmetricAlgebra.ι R L x := by
  change (_root_.UniversalEnvelopingAlgebra.lift R (toSymmetricLie R L))
      (_root_.UniversalEnvelopingAlgebra.ι R x) = _
  exact _root_.UniversalEnvelopingAlgebra.lift_ι_apply R (toSymmetricLie R L) x

private theorem ofSymmetric_ι (x : L) :
    ofSymmetric R L (SymmetricAlgebra.ι R L x) = _root_.UniversalEnvelopingAlgebra.ι R x := by
  change (SymmetricAlgebra.lift (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap)
      (SymmetricAlgebra.ι R L x) = _
  simpa only [LieHom.coe_toLinearMap] using
    SymmetricAlgebra.lift_ι_apply (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap x

private theorem toSymmetric_comp_ofSymmetric :
    (toSymmetric R L).comp (ofSymmetric R L) = AlgHom.id R (SymmetricAlgebra R L) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  change toSymmetric R L (ofSymmetric R L (SymmetricAlgebra.ι R L x)) =
    SymmetricAlgebra.ι R L x
  rw [ofSymmetric_ι, toSymmetric_ι]

private theorem ofSymmetric_comp_toSymmetric :
    (ofSymmetric R L).comp (toSymmetric R L) = AlgHom.id R U := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  ext x
  change ofSymmetric R L (toSymmetric R L (_root_.UniversalEnvelopingAlgebra.ι R x)) =
    _root_.UniversalEnvelopingAlgebra.ι R x
  rw [toSymmetric_ι, ofSymmetric_ι]

/-- The canonical algebra equivalence from the enveloping algebra of an abelian Lie algebra to its
symmetric algebra. -/
noncomputable def equivSymmetricAlgebra : U ≃ₐ[R] SymmetricAlgebra R L :=
  AlgEquiv.ofAlgHom (toSymmetric R L) (ofSymmetric R L)
    (toSymmetric_comp_ofSymmetric R L) (ofSymmetric_comp_toSymmetric R L)

/-- The canonical equivalence sends each Lie generator to the corresponding symmetric generator. -/
theorem equivSymmetricAlgebra_ι (x : L) :
    equivSymmetricAlgebra R L (_root_.UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R L x := by
  rw [equivSymmetricAlgebra, AlgEquiv.ofAlgHom_apply, toSymmetric_ι]

/-- The `simp`-normal form of `equivSymmetricAlgebra_ι`. -/
@[simp]
theorem equivSymmetricAlgebra_ι' (x : L) :
    equivSymmetricAlgebra R L
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      SymmetricAlgebra.ι R L x := by
  simpa using equivSymmetricAlgebra_ι R L x

/-- The inverse canonical equivalence sends each symmetric generator to the corresponding Lie
generator. -/
@[simp]
theorem equivSymmetricAlgebra_symm_ι (x : L) :
    (equivSymmetricAlgebra R L).symm (SymmetricAlgebra.ι R L x) =
      _root_.UniversalEnvelopingAlgebra.ι R x := by
  rw [equivSymmetricAlgebra, AlgEquiv.ofAlgHom_symm_apply, ofSymmetric_ι]

end TauCeti.UniversalEnvelopingAlgebra
