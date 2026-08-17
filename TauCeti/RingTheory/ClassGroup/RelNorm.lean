/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
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
* `ClassGroup.relNorm_extendedHom`: **extend then norm is the `finrank`-th power**,
  `relNorm (extendedHom R S c) = c ^ Module.finrank R S`, with
  `ClassGroup.relNorm_comp_extendedHom` the same statement as an identity of monoid homomorphisms.
  The extension direction is Mathlib's `ClassGroup.extendedHom`; the composite itself is the
  source's `ClassGroup.relNorm_comp_map`, respelt against it.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/Pic0/ClassGroupNorm.lean`, declarations `relNorm0`, `mk0CompRelNorm0`,
`mk0CompRelNorm0_apply`, `mk0CompRelNorm0_eq_of_mk0_eq`, `ClassGroup.relNorm`,
`ClassGroup.relNorm_mk0`, `ClassGroup.relNorm_mk0'`, `ClassGroup.relNorm_comp_map` and
`ClassGroup.relNorm_comp_map_eq`.

Deviations from the source. It descends by `Function.surjInv` on `ClassGroup.mk0_surjective`, with
`Function.surjInv_eq` rewrites discharging `map_one'` and `map_mul'`; the congruence route used
here needs no choice plumbing in the proofs. It assumes `IsDomain` and `IsIntegrallyClosed`
alongside `IsDedekindDomain` for both rings, which are implied. Its intermediate
`mk0CompRelNorm0` and that lemma's `_apply` are inlined, the well-definedness fact being stated
directly about `mk0 ∘ relNorm0`. Finally its `relNorm_mk0'`, a restatement of `relNorm_mk0` with
the membership proof spelled out inline, is not ported.

**The source's extension direction is not ported at all.** Its `map0`, `mk0CompMap0`,
`ClassGroup.map`, `ClassGroup.map_mk0`, `ClassGroup.map_one` and `ClassGroup.map_mul` are Mathlib's
`ClassGroup.extendedIdeal`, `ClassGroup.extendedHom` and `ClassGroup.extendedHom_mk0`
(`Mathlib/RingTheory/ClassGroup/ExtendedHom.lean`), which the pinned Mathlib already carries; the
first version of this file duplicated them under the source's names and `reuse` blocked it. Its
`Ideal.relNorm_map_algebraMap` is likewise not ported: it converts `Ideal.relNorm_algebraMap`'s
exponent from `Module.finrank (FractionRing R) (FractionRing S)` to `Module.finrank R S`, and the
pinned `Ideal.relNorm_algebraMap` already concludes in the latter form, with the converting lemma
`finrank_of_isFractionRing` now deprecated.

**The composite is ported, not original.** `relNorm_extendedHom` and `relNorm_comp_extendedHom` are
the source's `ClassGroup.relNorm_comp_map` and `ClassGroup.relNorm_comp_map_eq`, respelt so that the
extension direction is Mathlib's `ClassGroup.extendedHom` rather than the source's own
`ClassGroup.map`. What is new here is only that respelling and the shape of the proof: the source
reaches the ideal level inline, by `congrArg ClassGroup.mk0`, `Subtype.ext` and a `change`, landing
on its own `Ideal.relNorm_map_algebraMap`; this file names that step as
`Ideal.relNorm0_extendedIdeal` and lands on Mathlib's `Ideal.relNorm_algebraMap` directly, no
exponent conversion being needed. The composite is nonetheless new *relative to Mathlib*, since it
needs `ClassGroup.relNorm`, which Mathlib does not carry.
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

/-- **Norm of an extended ideal is the `finrank`-th power**, on nonzero ideals: the
`(Ideal R)⁰`-level form of Mathlib's `Ideal.relNorm_algebraMap`, against Mathlib's
`ClassGroup.extendedIdeal`. -/
@[simp]
theorem Ideal.relNorm0_extendedIdeal (I : (Ideal R)⁰) :
    Ideal.relNorm0 R (ClassGroup.extendedIdeal R S I) = I ^ Module.finrank R S := by
  refine Subtype.ext ?_
  rw [Ideal.coe_relNorm0, SubmonoidClass.coe_pow]
  exact Ideal.relNorm_algebraMap S (I : Ideal R)

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

/-- **Extending a class and taking its relative norm raises it to the `finrank`-th power.**

The extension direction is Mathlib's `ClassGroup.extendedHom`; the arithmetic is Mathlib's
`Ideal.relNorm_algebraMap`, which needs no separability, Galois or perfect-field hypothesis, so
neither does this. The composite is the source's `ClassGroup.relNorm_comp_map`; see the
module's Provenance. -/
@[simp]
theorem relNorm_extendedHom (c : ClassGroup R) :
    relNorm (ClassGroup.extendedHom R S c) = c ^ Module.finrank R S := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.extendedHom_mk0, relNorm_mk0, Ideal.relNorm0_extendedIdeal]
  exact map_pow ClassGroup.mk0 I (Module.finrank R S)

/-- `ClassGroup.relNorm_extendedHom` as an identity of monoid homomorphisms: the composite
`relNorm ∘ extendedHom` is the `finrank`-th power map on `ClassGroup R`. -/
theorem relNorm_comp_extendedHom :
    (relNorm (R := R)).comp (ClassGroup.extendedHom R S) = powMonoidHom (Module.finrank R S) := by
  ext c
  rw [MonoidHom.comp_apply, powMonoidHom_apply, relNorm_extendedHom]


end ClassGroup
