/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.Basic

/-!
# The additive group

The affine scheme `Spec (SymmetricAlgebra R M)` is the **additive (vector) group** on `M`.
Its functor of points is computed here: for a commutative `R`-algebra `A`, the
convolution monoid of `R`-algebra maps `SymmetricAlgebra R M →ₐ[R] A` is the additive monoid
of `R`-linear maps `M →ₗ[R] A`, with convolution corresponding to addition. Taking `M = R`
recovers the one-dimensional additive group `𝔾ₐ = Spec R[X]`, whose `A`-valued points are
`(A, +)`; the `R`-points are this construction specialized to `A = R`.

This is the worked example `𝔾ₐ` from the Tau Ceti reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, "Worked examples" and Layer 0, "R-points as a
group"), in the same spirit as the multiplicative group `𝔾ₘ`.

## Main declarations

* `TauCeti.AdditiveGroup.pointsMulEquiv`: the convolution monoid of points
  `SymmetricAlgebra R M →ₐ[R] A` is the additive monoid `M →ₗ[R] A`.
* `TauCeti.AdditiveGroup.gaPointsMulEquiv`: the monoid of `A`-valued points of `𝔾ₐ` over `R`
  is the additive monoid of `A`.
* `TauCeti.AdditiveGroup.gaPointMul`: multiplication of the parameters of two `𝔾ₐ`-points.
* `TauCeti.AdditiveGroup.pointsMulEquiv_mapValue`: the points equivalence is natural in the
  value algebra.

## References

The symmetric-algebra Hopf structure is supplied by
`TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra.Basic`, on top of Mathlib's symmetric-algebra
bialgebra and convolution monoid APIs.
-/

public section

open _root_.Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w

section Points

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- **The convolution monoid of points of a vector group.** For a commutative `R`-algebra `A`,
the convolution monoid of `R`-algebra maps out of `SymmetricAlgebra R M` is the additive monoid
of `R`-linear maps `M →ₗ[R] A`: a point `F` corresponds to the linear map `x ↦ F (ι x)`, and
convolution of points corresponds to addition of linear maps. -/
@[expose] noncomputable def pointsMulEquiv :
    WithConv (SymmetricAlgebra R M →ₐ[R] A) ≃* Multiplicative (M →ₗ[R] A) where
  toFun F := Multiplicative.ofAdd (SymmetricAlgebra.lift.symm F.ofConv)
  invFun φ := toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ))
  left_inv F := by
    simp only [toAdd_ofAdd, Equiv.apply_symm_apply, toConv_ofConv]
  right_inv φ := by
    simp only [Equiv.symm_apply_apply, ofAdd_toAdd]
  map_mul' F G := by
    have h : SymmetricAlgebra.lift.symm (F * G).ofConv =
        SymmetricAlgebra.lift.symm F.ofConv + SymmetricAlgebra.lift.symm G.ofConv := by
      ext x
      simp [LinearMap.add_apply]
    exact (congrArg Multiplicative.ofAdd h).trans (ofAdd_add _ _)

/-- A point of the additive group, as a linear map, is `x ↦ F (ι x)`. -/
@[simp]
theorem toAdd_pointsMulEquiv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd (pointsMulEquiv F) = SymmetricAlgebra.lift.symm F.ofConv :=
  rfl

/-- The linear map underlying a point evaluates as `x ↦ F (ι x)`. -/
theorem toAdd_pointsMulEquiv_apply (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    Multiplicative.toAdd (pointsMulEquiv F) x = F.ofConv (ι R M x) :=
  TauCeti.SymmetricAlgebra.lift_symm_apply F.ofConv x

/-- The inverse equivalence sends a linear map to the corresponding algebra map. -/
@[simp]
theorem pointsMulEquiv_symm_apply (φ : Multiplicative (M →ₗ[R] A)) :
    (pointsMulEquiv (R := R) (M := M) (A := A)).symm φ =
      toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ)) :=
  rfl

/-- Reading a vector-group point as a linear map is natural in the value algebra:
post-composing the point with an `R`-algebra map post-composes the corresponding linear map. -/
theorem toAdd_pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd
        (pointsMulEquiv (R := R) (M := M) (A := B)
          (AlgHom.mapValue (H := SymmetricAlgebra R M) φ F)) =
      φ.toLinearMap.comp (Multiplicative.toAdd (pointsMulEquiv F)) := by
  ext x
  simp [LinearMap.comp_apply]

/-- The vector-group points equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    pointsMulEquiv (R := R) (M := M) (A := B)
        (AlgHom.mapValue (H := SymmetricAlgebra R M) φ F) =
      Multiplicative.ofAdd
        (φ.toLinearMap.comp (Multiplicative.toAdd (pointsMulEquiv F))) := by
  exact congrArg Multiplicative.ofAdd (toAdd_pointsMulEquiv_mapValue φ F)

/-- Naturality of the inverse vector-group points equivalence in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B)
    (ψ : Multiplicative (M →ₗ[R] A)) :
    AlgHom.mapValue (H := SymmetricAlgebra R M) φ
        ((pointsMulEquiv (R := R) (M := M) (A := A)).symm ψ) =
      (pointsMulEquiv (R := R) (M := M) (A := B)).symm
        (Multiplicative.ofAdd (φ.toLinearMap.comp (Multiplicative.toAdd ψ))) := by
  apply (pointsMulEquiv (R := R) (M := M) (A := B)).injective
  rw [pointsMulEquiv_mapValue]
  rw [(pointsMulEquiv (R := R) (M := M) (A := A)).apply_symm_apply ψ]
  exact ((pointsMulEquiv (R := R) (M := M) (A := B)).apply_symm_apply
    (Multiplicative.ofAdd (φ.toLinearMap.comp (Multiplicative.toAdd ψ)))).symm

end Points

section RingPoints

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Over commutative rings, `pointsMulEquiv` identifies the convolution inverse of a point with
negation of the corresponding linear map. -/
@[simp]
theorem pointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    pointsMulEquiv (F⁻¹) = (pointsMulEquiv F)⁻¹ :=
  map_inv pointsMulEquiv F

/-- In additive notation, the convolution inverse of a point corresponds to negating its linear
map of generator values. -/
theorem toAdd_pointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd (pointsMulEquiv (F⁻¹)) = -Multiplicative.toAdd (pointsMulEquiv F) := by
  rw [pointsMulEquiv_inv]
  rfl

end RingPoints

section Ga

variable {R : Type u} [CommSemiring R] {A : Type w} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- **The one-dimensional additive monoid of points** for `𝔾ₐ = Spec (SymmetricAlgebra R R)`.
Specializing the vector group to `M = R`, the convolution monoid of `A`-valued points over `R`
is the additive monoid `(A, +)`. -/
noncomputable def gaPointsMulEquiv :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃* Multiplicative A :=
  pointsMulEquiv.trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf R R A).toAddEquiv)

/-- A point of `𝔾ₐ` is the additive group element obtained by evaluating it at the generator
`ι 1`. -/
@[simp]
theorem toAdd_gaPointsMulEquiv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv F) = F.ofConv (ι R R 1) := by
  rw [gaPointsMulEquiv]
  simp

/-- The inverse equivalence sends an element of the value algebra to the corresponding
`A`-valued point of `𝔾ₐ`. -/
@[simp]
theorem gaPointsMulEquiv_symm_apply_ι (a : Multiplicative A) :
    ((gaPointsMulEquiv (R := R) (A := A)).symm a).ofConv (ι R R 1) =
      Multiplicative.toAdd a := by
  rw [gaPointsMulEquiv]
  simp

/-- Reading a `𝔾ₐ`-point as an element of the value algebra is natural in the value algebra:
post-composing the point with an `R`-algebra map applies that map to the corresponding
element. -/
theorem toAdd_gaPointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd
        (gaPointsMulEquiv (R := R) (A := B)
          (AlgHom.mapValue (H := SymmetricAlgebra R R) φ F)) =
      φ (Multiplicative.toAdd (gaPointsMulEquiv F)) := by
  simp

/-- The `𝔾ₐ` points equivalence is natural in the value algebra. -/
theorem gaPointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := SymmetricAlgebra R R) φ F) =
      Multiplicative.ofAdd (φ (Multiplicative.toAdd (gaPointsMulEquiv F))) := by
  exact congrArg Multiplicative.ofAdd (toAdd_gaPointsMulEquiv_mapValue φ F)

/-- Naturality of the inverse `𝔾ₐ` points equivalence in the value algebra. -/
theorem mapValue_gaPointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (a : Multiplicative A) :
    AlgHom.mapValue (H := SymmetricAlgebra R R) φ
        ((gaPointsMulEquiv (R := R) (A := A)).symm a) =
      (gaPointsMulEquiv (R := R) (A := B)).symm
        (Multiplicative.ofAdd (φ (Multiplicative.toAdd a))) := by
  apply (gaPointsMulEquiv (R := R) (A := B)).injective
  rw [gaPointsMulEquiv_mapValue]
  rw [(gaPointsMulEquiv (R := R) (A := A)).apply_symm_apply a]
  exact ((gaPointsMulEquiv (R := R) (A := B)).apply_symm_apply
    (Multiplicative.ofAdd (φ (Multiplicative.toAdd a)))).symm

/-- The `A`-valued point of `𝔾ₐ` whose parameter is the product of the parameters of `F` and
`G`.

This is not the convolution multiplication of `𝔾ₐ(A)`: convolution corresponds to addition,
whereas `gaPointMul F G` records multiplication in the value algebra. -/
noncomputable def gaPointMul
    (F G : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
  (gaPointsMulEquiv (R := R) (A := A)).symm <|
    Multiplicative.ofAdd
      (Multiplicative.toAdd (gaPointsMulEquiv F) *
        Multiplicative.toAdd (gaPointsMulEquiv G))

/-- Under the points equivalence, `gaPointMul` is multiplication in the value algebra. -/
@[simp]
theorem gaPointsMulEquiv_gaPointMul
    (F G : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointsMulEquiv (gaPointMul F G) =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (gaPointsMulEquiv F) *
          Multiplicative.toAdd (gaPointsMulEquiv G)) := by
  rw [gaPointMul, MulEquiv.apply_symm_apply]

/-- The value of `gaPointMul F G` on the additive coordinate is the product of the two original
coordinate values. -/
@[simp]
theorem gaPointMul_apply_ι (F G : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    (gaPointMul F G).ofConv (ι R R 1) =
      F.ofConv (ι R R 1) * G.ofConv (ι R R 1) := by
  rw [← toAdd_gaPointsMulEquiv, gaPointsMulEquiv_gaPointMul, toAdd_ofAdd,
    toAdd_gaPointsMulEquiv, toAdd_gaPointsMulEquiv]

/-- Multiplication of `𝔾ₐ`-point parameters is natural in the value algebra. -/
theorem mapValue_gaPointMul (φ : A →ₐ[R] B)
    (F G : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    AlgHom.mapValue (H := SymmetricAlgebra R R) φ (gaPointMul F G) =
      gaPointMul
        (AlgHom.mapValue (H := SymmetricAlgebra R R) φ F)
        (AlgHom.mapValue (H := SymmetricAlgebra R R) φ G) := by
  rw [gaPointMul, mapValue_gaPointsMulEquiv_symm_apply, gaPointMul,
    toAdd_gaPointsMulEquiv_mapValue, toAdd_gaPointsMulEquiv_mapValue]
  exact congrArg (gaPointsMulEquiv (R := R) (A := B)).symm
    (congrArg Multiplicative.ofAdd (map_mul φ _ _))

/-- Multiplying the zero parameter on the left gives the zero parameter; the zero point is the
convolution identity. -/
@[simp]
theorem gaPointMul_one_left (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul 1 F = 1 := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simp

/-- Multiplying the zero parameter on the right gives the zero parameter; the zero point is the
convolution identity. -/
@[simp]
theorem gaPointMul_one_right (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul F 1 = 1 := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simp

/-- Multiplication of `𝔾ₐ`-point parameters is commutative. -/
theorem gaPointMul_comm (F G : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul F G = gaPointMul G F := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simp only [gaPointsMulEquiv_gaPointMul]
  exact congrArg Multiplicative.ofAdd (mul_comm _ _)

/-- Multiplication of `𝔾ₐ`-point parameters is associative. -/
theorem gaPointMul_assoc (F G K : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul (gaPointMul F G) K = gaPointMul F (gaPointMul G K) := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simp only [gaPointsMulEquiv_gaPointMul, toAdd_ofAdd]
  exact congrArg Multiplicative.ofAdd (mul_assoc _ _ _)

/-- Multiplication of `𝔾ₐ`-point parameters distributes over convolution in the left input. -/
@[simp]
theorem gaPointMul_mul_left (F G K : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul (F * G) K = gaPointMul F K * gaPointMul G K := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simpa only [gaPointsMulEquiv_gaPointMul, map_mul, toAdd_mul, ofAdd_add] using
    congrArg Multiplicative.ofAdd (add_mul
      (Multiplicative.toAdd (gaPointsMulEquiv F))
      (Multiplicative.toAdd (gaPointsMulEquiv G))
      (Multiplicative.toAdd (gaPointsMulEquiv K)))

/-- Multiplication of `𝔾ₐ`-point parameters distributes over convolution in the right input. -/
@[simp]
theorem gaPointMul_mul_right (F G K : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointMul F (G * K) = gaPointMul F G * gaPointMul F K := by
  apply (gaPointsMulEquiv (R := R) (A := A)).injective
  simpa only [gaPointsMulEquiv_gaPointMul, map_mul, toAdd_mul, ofAdd_add] using
    congrArg Multiplicative.ofAdd (mul_add
      (Multiplicative.toAdd (gaPointsMulEquiv F))
      (Multiplicative.toAdd (gaPointsMulEquiv G))
      (Multiplicative.toAdd (gaPointsMulEquiv K)))

end Ga

section GaRing

variable {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]

/-- Over commutative rings, `gaPointsMulEquiv` identifies the convolution inverse of a
`𝔾ₐ`-point with negation in the value ring. -/
@[simp]
theorem gaPointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointsMulEquiv (F⁻¹) = (gaPointsMulEquiv F)⁻¹ :=
  map_inv gaPointsMulEquiv F

/-- In additive notation, the convolution inverse of a `𝔾ₐ`-point is the negative of its value
on the generator `ι 1`. -/
theorem toAdd_gaPointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv (F⁻¹)) = -Multiplicative.toAdd (gaPointsMulEquiv F) := by
  rw [gaPointsMulEquiv_inv]
  rfl

end GaRing

end AdditiveGroup

end TauCeti
