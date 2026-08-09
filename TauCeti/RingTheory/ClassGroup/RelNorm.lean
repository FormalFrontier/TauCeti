/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.GroupTheory.Congruence.Basic

/-!
# The relative norm on ideal class groups

For a finite extension `S / R` of Dedekind domains, Mathlib's relative ideal norm
`Ideal.relNorm R : Ideal S →*₀ Ideal R` is multiplicative and sends principal ideals to
principal ideals (`Ideal.relNorm_singleton`), so it descends to a group homomorphism
`ClassGroup.relNorm : ClassGroup S →* ClassGroup R` on ideal class groups.

The descent is along `ClassGroup.mk0 : (Ideal S)⁰ →* ClassGroup S`, which is surjective. Since
`(Ideal S)⁰` is a monoid rather than a group, `MonoidHom.liftOfSurjective` does not apply; the
descent instead goes through the monoid congruence `Con.ker` and
`Con.quotientKerEquivOfSurjective`.

## Main definitions

* `Ideal.relNorm0 : (Ideal S)⁰ →* (Ideal R)⁰`: the relative ideal norm on nonzero ideals.
* `ClassGroup.relNorm : ClassGroup S →* ClassGroup R`.

## Main results

* `ClassGroup.relNorm_mk0`: `relNorm (mk0 I) = mk0 (relNorm0 I)`, the defining computation on an
  integral representative.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Pic0/ClassGroupNorm.lean`, declarations `relNorm0`, `mk0CompRelNorm0`,
`mk0CompRelNorm0_apply`, `mk0CompRelNorm0_eq_of_mk0_eq`, `ClassGroup.relNorm`,
`ClassGroup.relNorm_mk0` and `ClassGroup.relNorm_mk0'`.

Deviations from the source. It descends by `Function.surjInv` on `ClassGroup.mk0_surjective`, with
`Function.surjInv_eq` rewrites discharging `map_one'` and `map_mul'`; the congruence route used
here needs no choice plumbing in the proofs. It assumes `IsDomain` and `IsIntegrallyClosed`
alongside `IsDedekindDomain` for both rings, which are implied. Its intermediate
`mk0CompRelNorm0` and that lemma's `_apply` are inlined, the well-definedness fact being stated
directly about `mk0 ∘ relNorm0`. Finally its `relNorm_mk0'`, a restatement of `relNorm_mk0` with
the membership proof spelled out inline, is not ported.
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

variable (R) in
/-- The relative ideal norm restricted to nonzero ideals, using that it reflects `⊥`
(`Ideal.relNorm_eq_bot_iff`). -/
noncomputable def Ideal.relNorm0 : (Ideal S)⁰ →* (Ideal R)⁰ :=
  ((Ideal.relNorm R).toMonoidHom.domRestrict (Ideal S)⁰).codRestrict (Ideal R)⁰ fun I =>
    mem_nonZeroDivisors_iff_ne_zero.mpr <|
      Ideal.relNorm_eq_bot_iff.not.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2

@[simp]
theorem Ideal.coe_relNorm0 (I : (Ideal S)⁰) :
    (Ideal.relNorm0 R I : Ideal R) = Ideal.relNorm R (I : Ideal S) :=
  (rfl)

namespace ClassGroup

/-- **Well-definedness of the class-group relative norm**: integral ideals with the same class have
relative norms with the same class.

By `ClassGroup.mk0_eq_mk0_iff` the hypothesis says `span {x} * I = span {y} * J` for nonzero
`x y : S`; applying `Ideal.relNorm` and using `Ideal.relNorm_singleton` turns this into the same
relation between the norms, with the nonzero elements `Algebra.intNorm R S x` and
`Algebra.intNorm R S y`. -/
private theorem mk0_relNorm0_eq_of_mk0_eq {I J : (Ideal S)⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (Ideal.relNorm0 R I) = ClassGroup.mk0 (Ideal.relNorm0 R J) := by
  -- `Algebra.intNorm_ne_zero` needs the fraction fields to form a finite extension; the lifted
  -- algebra is deliberately not an instance, so it is supplied here.
  let _ : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  have : IsScalarTower R (FractionRing R) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) (FractionRing S) :=
    IsIntegralClosure.isLocalization R (FractionRing R) (FractionRing S) S
  have : IsScalarTower R S (FractionRing S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (FractionRing R) (FractionRing S) :=
    Module.Finite.of_isLocalization R S R⁰
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ClassGroup.mk0_eq_mk0_iff.mpr ⟨Algebra.intNorm R S x, Algebra.intNorm R S y,
    Algebra.intNorm_ne_zero.mpr hx, Algebra.intNorm_ne_zero.mpr hy, ?_⟩
  rw [Ideal.coe_relNorm0, Ideal.coe_relNorm0, ← Ideal.relNorm_singleton (R := R) x,
    ← Ideal.relNorm_singleton (R := R) y, ← map_mul, ← map_mul, hxy]

/-- The **relative norm on class groups**, induced by `Ideal.relNorm`.

Every class has an integral representative, since `ClassGroup.mk0` is surjective, and the class of
the norm does not depend on the representative; `ClassGroup.relNorm_mk0` is the resulting
computation. -/
noncomputable def relNorm : ClassGroup S →* ClassGroup R :=
  ((Con.ker (ClassGroup.mk0 (R := S))).lift ((ClassGroup.mk0 (R := R)).comp (Ideal.relNorm0 R))
      fun _ _ h => mk0_relNorm0_eq_of_mk0_eq h).comp
    (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm.toMonoidHom

/-- The relative norm of the class represented by a nonzero ideal `I` is the class represented by
`I`'s relative norm. This is the computation rule for `ClassGroup.relNorm`. -/
@[simp]
theorem relNorm_mk0 (I : (Ideal S)⁰) :
    relNorm (R := R) (ClassGroup.mk0 I) = ClassGroup.mk0 (Ideal.relNorm0 R I) := by
  have h : (Con.quotientKerEquivOfSurjective _ ClassGroup.mk0_surjective).symm
      (ClassGroup.mk0 (R := S) I) = (I : (Con.ker (ClassGroup.mk0 (R := S))).Quotient) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [relNorm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

end ClassGroup
