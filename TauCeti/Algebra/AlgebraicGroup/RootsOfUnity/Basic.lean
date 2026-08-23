/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic

/-!
# The roots-of-unity group scheme

This file records the functor-of-points calculation for the diagonalizable group
`D(Multiplicative (ZMod n))`. For positive `n`, this is the usual finite diagonalizable group
scheme `μ_n`: for every commutative `R`-algebra `A`, its convolution group of `A`-points is the
group of `n`th roots of unity in `A`.

The result is deliberately just the points calculation. The represented Hopf algebra is the
group algebra `R[Multiplicative (ZMod n)]`; identifying it with the more classical
coordinate ring `R[X]/(X^n - 1)` is separate quotient-polynomial infrastructure.

## Main definitions

* `TauCeti.RootsOfUnityGroup.pointsMulEquiv`: the multiplicative equivalence from
  convolution points of `R[Multiplicative (ZMod n)]` to `rootsOfUnity n A`.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_apply`: the equivalence sends a point to its
  value on the standard generator `single (ofAdd 1) 1`.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator_smul`: the inverse
  equivalence evaluates scalar multiples of the standard generator.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_zmod_val`: the inverse
  equivalence evaluates any cyclic group-algebra generator as the corresponding power of
  the chosen root of unity.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator`: the inverse
  equivalence sends a root of unity to the point taking the standard generator to it.

This is a worked-example check for the reductive-groups roadmap, Layer 4:
"`μ_n = D(ℤ/n)`" in the diagonalizable-groups lane, together with the Layer 0 functor-of-points
calculation.

## References

The diagonalizable-group points calculation is Tau Ceti's
`DiagonalizableGroup.pointsMulEquiv`. The internal cyclic character group calculation uses Mathlib's
`IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator`, from
`Mathlib.RingTheory.RootsOfUnity.Basic`.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

/-- The standard generator of the character group defining `μ_n = D(ℤ/n)`. -/
abbrev generator (n : ℕ) : Multiplicative (ZMod n) :=
  Multiplicative.ofAdd 1

section Characters

variable {A : Type v} [CommMonoid A]

private noncomputable def characterMulEquivRootsOfUnity (n : ℕ) :
    (Multiplicative (ZMod n) →* Aˣ) ≃* rootsOfUnity n A :=
  let hg : ∀ x : Multiplicative (ZMod n), x ∈ Subgroup.zpowers (generator n) := by
    intro x
    refine ⟨(Multiplicative.toAdd x).cast, ?_⟩
    simp only [generator]
    rw [← ofAdd_zsmul]
    calc
      Multiplicative.ofAdd ((Multiplicative.toAdd x).cast • (1 : ZMod n)) =
          Multiplicative.ofAdd (((Multiplicative.toAdd x).cast : ℤ) : ZMod n) := by simp
      _ =
          Multiplicative.ofAdd (Multiplicative.toAdd x) := by rw [ZMod.intCast_zmod_cast]
      _ = x := ofAdd_toAdd x
  let hcard : Nat.card (Multiplicative (ZMod n)) = n :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans
      (Nat.card_zmod n)
  ((IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator (g := generator n) hg Aˣ).trans
      (MulEquiv.subgroupCongr (by rw [hcard]))).trans
    (rootsOfUnityUnitsMulEquiv A n)

-- The proof is `rfl`: each composed equivalence acts on the underlying unit by projection.
@[simp]
private lemma characterMulEquivRootsOfUnity_apply (n : ℕ)
    (χ : Multiplicative (ZMod n) →* Aˣ) :
    ((characterMulEquivRootsOfUnity (A := A) n χ : Aˣ) : A) =
      (χ (generator n) : A) :=
  rfl

@[simp]
private lemma characterMulEquivRootsOfUnity_symm_apply_generator
    (n : ℕ) (ζ : rootsOfUnity n A) :
    (((characterMulEquivRootsOfUnity (A := A) n).symm ζ (generator n) : Aˣ) : A) =
      ((ζ : Aˣ) : A) := by
  rw [← characterMulEquivRootsOfUnity_apply n
    ((characterMulEquivRootsOfUnity (A := A) n).symm ζ)]
  simp

end Characters

private lemma generator_pow_val (n : ℕ) [NeZero n] (x : Multiplicative (ZMod n)) :
    generator n ^ (Multiplicative.toAdd x).val = x := by
  rw [← ofAdd_nsmul]
  simp only [nsmul_eq_mul, mul_one]
  -- Expose the `ZMod` cast hidden in the additive scalar multiple so that
  -- `ZMod.natCast_zmod_val` applies directly.
  change Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℕ) : ZMod n) = x
  rw [ZMod.natCast_zmod_val, ofAdd_toAdd]

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The functor of points of `μ_n = D(ℤ/n)` is the group of `n`th roots of unity.

The source is the convolution group of `R`-algebra maps out of the group algebra
`R[Multiplicative (ZMod n)]`, and the target is Mathlib's subgroup of units whose `n`th power
is one. -/
noncomputable def pointsMulEquiv (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) ≃*
      rootsOfUnity n A :=
  (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).trans (characterMulEquivRootsOfUnity n)

/-- The points equivalence sends a point to its value on the standard generator. -/
@[simp]
lemma pointsMulEquiv_apply (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    ((pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) =
      f.ofConv (MonoidAlgebra.single (generator n) 1) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, DiagonalizableGroup.pointsMulEquiv_apply,
    characterMulEquivRootsOfUnity_apply]
  exact DiagonalizableGroup.charOfPoint_apply_coe f.ofConv (generator n)

/-- The points equivalence is natural in the value algebra. -/
lemma pointsMulEquiv_mapValue (n : ℕ) (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B) n
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ f) =
      restrictRootsOfUnity φ.toMonoidHom n (pointsMulEquiv (R := R) (A := A) n f) := by
  ext
  simp [pointsMulEquiv_apply]

/-- The inverse points equivalence sends a root of unity to the point taking the standard
generator to that root. -/
lemma pointsMulEquiv_symm_apply_single_generator (n : ℕ) (ζ : rootsOfUnity n A) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (generator n) 1) =
      ((ζ : Aˣ) : A) := by
  rw [pointsMulEquiv, MulEquiv.symm_trans_apply,
    DiagonalizableGroup.pointsMulEquiv_symm_apply, ofConv_toConv,
    DiagonalizableGroup.point_single_one,
    characterMulEquivRootsOfUnity_symm_apply_generator]

/-- The inverse points equivalence evaluates scalar multiples of the standard generator by
scalar multiplication of the chosen root of unity. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_generator_smul (n : ℕ) (ζ : rootsOfUnity n A) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (generator n) r) =
      r • ((ζ : Aˣ) : A) := by
  -- The scalar-action rewrite fixes the coefficient from `r` to `1`, so the existing generator
  -- evaluation lemma applies directly.
  rw [show MonoidAlgebra.single (generator n) r =
      r • MonoidAlgebra.single (generator n) (1 : R) by simp]
  rw [map_smul]
  rw [pointsMulEquiv_symm_apply_single_generator]

/-- The inverse `μ_n` points equivalence evaluates the group-like generator indexed by
`x : Multiplicative (ZMod n)` as the corresponding power of the chosen root of unity.

For `x = generator n`, this specializes to
`RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator`. -/
lemma pointsMulEquiv_symm_apply_single_zmod_val (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (x : Multiplicative (ZMod n)) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single x (1 : R)) =
      ((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) := by
  have hsingle :
      MonoidAlgebra.single x (1 : R) =
        MonoidAlgebra.single (generator n) (1 : R) ^ (Multiplicative.toAdd x).val := by
    rw [MonoidAlgebra.single_pow, one_pow, generator_pow_val]
  rw [hsingle, map_pow, pointsMulEquiv_symm_apply_single_generator]
  rw [Units.val_pow_eq_pow_val]

/-- The inverse `μ_n` points equivalence evaluates scalar multiples of the group-like generator
indexed by `x : Multiplicative (ZMod n)` by scalar multiplication of the corresponding power
of the chosen root of unity. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_zmod_val_smul (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (x : Multiplicative (ZMod n)) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single x r) =
      r • (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A) := by
  -- The scalar-action rewrite fixes the coefficient from `r` to `1`, so the arbitrary-generator
  -- evaluation lemma applies directly.
  rw [show MonoidAlgebra.single x r = r • MonoidAlgebra.single x (1 : R) by simp]
  rw [map_smul, pointsMulEquiv_symm_apply_single_zmod_val]

/-- The previous normal form, specialized to an additive residue class `j : ZMod n`. -/
lemma pointsMulEquiv_symm_apply_single_ofAdd_val (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) =
      ((ζ : Aˣ) ^ j.val : Aˣ) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j), toAdd_ofAdd]

/-- The scalar version of `pointsMulEquiv_symm_apply_single_ofAdd_val`. -/
lemma pointsMulEquiv_symm_apply_single_ofAdd_val_smul (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) r) =
      r • (((ζ : Aˣ) ^ j.val : Aˣ) : A) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val_smul (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j) r, toAdd_ofAdd]

/-- Naturality of the inverse `μ_n` points equivalence in the value algebra: post-composing
the point attached to `ζ` gives the point attached to the image of `ζ`. -/
lemma mapValue_pointsMulEquiv_symm_apply (n : ℕ) (φ : A →ₐ[R] B) (ζ : rootsOfUnity n A) :
    AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ) =
      (pointsMulEquiv (R := R) (A := B) n).symm
        (restrictRootsOfUnity φ.toMonoidHom n ζ) := by
  apply (pointsMulEquiv (R := R) (A := B) n).injective
  rw [pointsMulEquiv_mapValue]
  simp

/-- Naturality of the inverse `μ_n` points equivalence, evaluated on an arbitrary cyclic
group-algebra generator. -/
lemma mapValue_pointsMulEquiv_symm_apply_single_zmod_val (n : ℕ) [NeZero n] (φ : A →ₐ[R] B)
    (ζ : rootsOfUnity n A) (x : Multiplicative (ZMod n)) :
    (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
        (MonoidAlgebra.single x (1 : R)) =
      φ (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A) := by
  rw [mapValue_pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply_single_zmod_val]
  simp [map_pow]

/-- Naturality of the inverse `μ_n` points equivalence on scalar multiples of arbitrary cyclic
group-algebra generators. -/
lemma mapValue_pointsMulEquiv_symm_apply_single_zmod_val_smul (n : ℕ) [NeZero n] (φ : A →ₐ[R] B)
    (ζ : rootsOfUnity n A) (x : Multiplicative (ZMod n)) (r : R) :
    (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
        (MonoidAlgebra.single x r) =
      φ (r • (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A)) := by
  rw [mapValue_pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply_single_zmod_val_smul]
  simp [map_pow]

end RootsOfUnityGroup

end TauCeti
