/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange

/-!
# Base change of the endomorphism ring of an abelian variety

Extending the base field along `K → L` sends an endomorphism of an abelian variety `A` over `K`
to an endomorphism of `A.baseChange L`. This assignment is a ring homomorphism
`AbelianVariety.End.baseChange : End A →+* End (A.baseChange L)`: it is additive because base
change respects the pointwise group law on homomorphisms
(`AbelianVariety.Hom.baseChangeMonoidHom`), and multiplicative because it is functorial
(`AbelianVariety.Hom.baseChange_comp`).

* `AbelianVariety.End.baseChange`: the ring homomorphism, with
  `AbelianVariety.End.toHom_baseChange` translating it back into base change of morphisms;
* `AbelianVariety.End.congr_baseChange`: base change commutes with the identification of
  endomorphism rings along an isomorphism of abelian varieties;
* `AbelianVariety.baseChange_mulBy`: multiplication by `n` base changes to multiplication by `n`.

The last statement is the concrete check that the ring homomorphism is the expected one: `[n]` is
the image of the integer `n` in the endomorphism ring, and a ring homomorphism preserves integers,
so `[n]` is intrinsic to the abelian variety and does not depend on the base field. That is also
what a later Layer E statement about `[n]` being an isogeny needs in order to be checked after
base change to an algebraic closure.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API" and its item "`[n]` as an
isogeny", together with the base-change compatibility required in the roadmap's end goal: the
Jacobian's universal property produces homomorphisms of abelian varieties, and comparing them
after base change is exactly comparing them in the base-changed endomorphism ring.

No external mathematics is vendored. The ring structure is Mathlib's, transported along the
already-established base-change functoriality of abelian-variety homomorphisms.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

open scoped Hom

variable {K : Type u} [Field K]

noncomputable section

namespace End

variable (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L]

/-- Extension of the base field along `K → L`, as a ring homomorphism between endomorphism rings.

Addition in an endomorphism ring is the pointwise group law of the abelian variety and
multiplication is composition, so additivity is `AbelianVariety.Hom.baseChange_mul` and
multiplicativity is `AbelianVariety.Hom.baseChange_comp` (composition being taken in the reversed
order in which `AbelianVariety.End` multiplies).

The action is characterized by `AbelianVariety.End.toHom_baseChange` and
`AbelianVariety.End.baseChange_ofHom`, so the implementation is not exposed. -/
def baseChange : End A →+* End (A.baseChange L) where
  toFun x := ofHom (Hom.baseChange (toHom x) L)
  map_one' := by
    apply toHom_injective
    simp only [toHom_ofHom, toHom_one, Hom.baseChange_id]
  map_mul' x y := by
    apply toHom_injective
    simp only [toHom_ofHom, toHom_mul, Hom.baseChange_comp]
  map_zero' := by
    apply toHom_injective
    simp only [toHom_ofHom, toHom_zero, Hom.baseChange_one]
  map_add' x y := by
    apply toHom_injective
    simp only [toHom_ofHom, toHom_add, Hom.baseChange_mul]

variable {A L}

/-- The endomorphism denoted by a base-changed element of the endomorphism ring is the base change
of the endomorphism denoted by that element. -/
@[simp]
lemma toHom_baseChange (x : End A) :
    toHom (baseChange A L x) = Hom.baseChange (toHom x) L :=
  toHom_ofHom _

/-- Base change of an endomorphism, read back in the endomorphism ring. -/
@[simp]
lemma baseChange_ofHom (f : A ⟶ A) :
    baseChange A L (ofHom f) = ofHom (Hom.baseChange f L) := by
  apply toHom_injective
  simp only [toHom_baseChange, toHom_ofHom]

variable {B : AbelianVariety K}

/-- Base change commutes with conjugation by an isomorphism of abelian varieties: conjugating and
then extending the base field is the same as extending the base field and conjugating by the
base-changed isomorphism, `CategoryTheory.Functor.mapIso` for `AbelianVariety.baseChangeFunctor`.

`Functor.mapIso` produces an isomorphism `(baseChangeFunctor L).obj A ≅ (baseChangeFunctor L).obj B`
and `AbelianVariety.baseChangeFunctor_obj` identifies its endpoints with the base changes, so the
conjugating isomorphism is the composite of the three; writing it that way keeps the statement
type-correct without unfolding the functor. -/
@[simp]
lemma congr_baseChange (e : A ≅ B) (L : Type u) [Field L] [Algebra K L] (x : End A) :
    baseChange B L (congr e x) =
      congr (eqToIso (baseChangeFunctor_obj L A).symm ≪≫ (baseChangeFunctor L).mapIso e ≪≫
        eqToIso (baseChangeFunctor_obj L B)) (baseChange A L x) := by
  apply toHom_injective
  -- Both sides unfold to a conjugate of `Hom.baseChange (toHom x) L`, the transport isomorphisms
  -- of `baseChangeFunctor_obj` cancelling because they are equalities of the same object.
  simp

end End

/-! ### Multiplication by `n` -/

variable (A : AbelianVariety K) (L : Type u) [Field L] [Algebra K L]

/-- Multiplication by `n` is compatible with extension of the base field.

Proved directly from `AbelianVariety.mulBy_eq_zpow`: `[n]` is the `n`-th power of the identity for
the pointwise group law, and base change preserves that law and the identity. -/
@[simp]
lemma baseChange_mulBy (n : ℤ) :
    Hom.baseChange (mulBy A n) L = mulBy (A.baseChange L) n := by
  rw [mulBy_eq_zpow, mulBy_eq_zpow, Hom.baseChange_zpow, Hom.baseChange_id]

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
