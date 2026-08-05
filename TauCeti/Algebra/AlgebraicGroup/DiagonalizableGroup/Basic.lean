/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# The diagonalizable group and its character functor of points

For a commutative group `G`, the group algebra `R[G]` is a commutative Hopf algebra in which
every group element `g` is group-like (`Δ(single g 1) = single g 1 ⊗ single g 1`,
`ε(single g 1) = 1`, antipode `single g 1 ↦ single g⁻¹ 1`). The associated affine group
scheme `Spec R[G]` is the *diagonalizable group* `D(G)` of the reductive-groups roadmap.

This file records the functor-of-points calculation for `D(G)`: for every commutative
`R`-algebra `A`, the convolution group of `R`-algebra homomorphisms `R[G] →ₐ[R] A` is the
**character group** `G →* Aˣ`, with convolution corresponding to the pointwise product of
characters. A point `f` is sent to the character `g ↦ f (single g 1)` (a unit of `A` with
inverse `f (single g⁻¹ 1)`), and a character `χ` is sent to the algebra map extending it via
`MonoidAlgebra.lift`.

Specializing to `G = Multiplicative ℤ` recovers the multiplicative group `𝔾ₘ` on the
group-algebra presentation `R[Multiplicative ℤ]`: the character read from a point is its value
on the generator, and this agrees with the canonical Laurent-polynomial `𝔾ₘ` of
`TauCeti.MultiplicativeGroup` after precomposition by
`AddMonoidAlgebra.toMultiplicativeAlgEquiv`.

This is a worked-example check for the reductive-groups roadmap (Layer 4, "diagonalizable
groups and groups of multiplicative type: the anti-equivalence `M ↦ D(M) = Spec k[M]`", and
the Layer 0 target "R-points as a group"), in the same spirit as the existing multiplicative
group `𝔾ₘ`.

## Main definitions

* `TauCeti.DiagonalizableGroup.point`: the `R[G]`-point extending a character of `G`.
* `TauCeti.DiagonalizableGroup.charOfPoint`: the character of `G` read off from a point.
* `TauCeti.DiagonalizableGroup.pointEquiv`: algebra maps `R[G] →ₐ[R] A` are equivalent to
  characters `G →* Aˣ`.
* `TauCeti.DiagonalizableGroup.pointsMulEquiv`: the same equivalence as a multiplicative
  equivalence from the convolution group of points to the character group.
* `TauCeti.DiagonalizableGroup.multiplicativeGroup_pointEquiv_apply`: the bridge from the
  `G = Multiplicative ℤ` specialization to the canonical Laurent-polynomial `𝔾ₘ` API of
  `TauCeti.MultiplicativeGroup`.

## References

The Hopf algebra structure on a group algebra is Mathlib's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra` (with the bialgebra structure of Amelia
Livingston's monoid-algebra formalization), and `MonoidAlgebra.lift` is its universal
property. The convolution group of points and its antipode-driven inverse are Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`, built on the Mathlib convolution monoid of
Yaël Dillies, Michał Mrugała and Yunzhou Xie. This realizes the diagonalizable-group worked
example of the Tau Ceti reductive-groups roadmap (Layer 4 and Layer 0).
-/

public section

open WithConv

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [CommGroup G]

/-- The `R[G]`-point of the diagonalizable group `D(G)` corresponding to a character of `G`.
It is the algebra map extending `χ` via the universal property of the group algebra; it sends
`single g r` to `r • χ g`. -/
@[expose] noncomputable def point (χ : G →* Aˣ) : MonoidAlgebra R G →ₐ[R] A :=
  MonoidAlgebra.lift R A G ((Units.coeHom A).comp χ)

/-- The point associated to a character sends `single g r` to `r • χ g`. -/
@[simp]
theorem point_single (χ : G →* Aˣ) (g : G) (r : R) :
    point (R := R) χ (MonoidAlgebra.single g r) = r • (χ g : A) := by
  rw [point, MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply,
    Units.coeHom_apply]

/-- The point associated to a character sends the group-like `single g 1` to `χ g`. -/
theorem point_single_one (χ : G →* Aˣ) (g : G) :
    point (R := R) χ (MonoidAlgebra.single g 1) = (χ g : A) := by
  rw [point_single, one_smul]

/-- The character of `G` read off from an `R[G]`-point: it sends `g` to the unit
`f (single g 1)` of `A`, whose inverse is `f (single g⁻¹ 1)`. It is the monoid hom
`(MonoidAlgebra.lift R A G).symm f : G →* A` made unit-valued through `MonoidHom.toHomUnits`,
using that `G` is a group. -/
@[expose] noncomputable def charOfPoint (f : MonoidAlgebra R G →ₐ[R] A) : G →* Aˣ :=
  ((MonoidAlgebra.lift R A G).symm f).toHomUnits

/-- The character read off from a point sends `g` to the value of the point on `single g 1`. -/
@[simp]
theorem charOfPoint_apply_coe (f : MonoidAlgebra R G →ₐ[R] A) (g : G) :
    (charOfPoint f g : A) = f (MonoidAlgebra.single g 1) :=
  rfl

/-- The inverse of the unit `charOfPoint f g` is the value of the point on `single g⁻¹ 1`. -/
@[simp]
theorem charOfPoint_apply_inv_coe (f : MonoidAlgebra R G →ₐ[R] A) (g : G) :
    (↑(charOfPoint f g)⁻¹ : A) = f (MonoidAlgebra.single g⁻¹ 1) :=
  (congrArg (fun u : Aˣ => (u : A)) ((charOfPoint f).map_inv g)).symm.trans
    (charOfPoint_apply_coe f g⁻¹)

/-- Reading off the character of the point of `χ` recovers `χ`. -/
@[simp]
theorem charOfPoint_point (χ : G →* Aˣ) :
    charOfPoint (point (R := R) χ) = χ := by
  ext g
  rw [charOfPoint_apply_coe, point_single_one]

/-- The point of the character read off from `f` recovers `f`. -/
@[simp]
theorem point_charOfPoint (f : MonoidAlgebra R G →ₐ[R] A) :
    point (R := R) (charOfPoint f) = f := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [point_single_one, charOfPoint_apply_coe]
  · ext

/-- Algebra maps out of `R[G]` are the same as characters `G →* Aˣ` of `G`. -/
@[expose] noncomputable def pointEquiv : (MonoidAlgebra R G →ₐ[R] A) ≃ (G →* Aˣ) :=
  (MonoidAlgebra.lift R A G).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

/-- The equivalence sends a point to the character read off from it. -/
@[simp]
theorem pointEquiv_apply (f : MonoidAlgebra R G →ₐ[R] A) :
    pointEquiv (R := R) (A := A) (G := G) f = charOfPoint f :=
  rfl

/-- The inverse equivalence sends a character to the point extending it. -/
@[simp]
theorem pointEquiv_symm_apply (χ : G →* Aˣ) :
    (pointEquiv (R := R) (A := A) (G := G)).symm χ = point χ :=
  rfl

/-- Reading off characters turns the convolution product of points into the pointwise
product of characters. -/
@[simp]
theorem charOfPoint_convMul (f g : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    charOfPoint ((f * g).ofConv) = charOfPoint f.ofConv * charOfPoint g.ofConv := by
  ext x
  rw [charOfPoint_apply_coe, MonoidHom.mul_apply, Units.val_mul, charOfPoint_apply_coe,
    charOfPoint_apply_coe, MonoidAlgebra.convMul_algHom_single_one]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Reading off characters is natural in the value algebra: post-composing a point with an
`R`-algebra map sends the associated character through the induced map on units. -/
theorem charOfPoint_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    charOfPoint ((AlgHom.mapValue (H := MonoidAlgebra R G) φ f).ofConv) =
      (Units.map φ.toMonoidHom).comp (charOfPoint f.ofConv) := by
  ext x
  simp

/-- The functor of points of the diagonalizable group `D(G)` is the character group `G →* Aˣ`.

The source is the convolution group of `R`-algebra maps out of `R[G]`; the target is the
group of characters of `G` valued in the units of `A`, under pointwise multiplication. -/
@[expose] noncomputable def pointsMulEquiv : WithConv (MonoidAlgebra R G →ₐ[R] A) ≃* (G →* Aˣ) where
  toFun f := charOfPoint f.ofConv
  invFun χ := toConv (point (R := R) χ)
  left_inv f := congrArg toConv (point_charOfPoint f.ofConv)
  right_inv := charOfPoint_point
  map_mul' := charOfPoint_convMul

/-- The multiplicative equivalence sends a convolution point to the character read off from it. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) (G := G) f = charOfPoint f.ofConv :=
  rfl

/-- The multiplicative point equivalence is natural in the value algebra. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B) (G := G)
        (AlgHom.mapValue (H := MonoidAlgebra R G) φ f) =
      (Units.map φ.toMonoidHom).comp
        (pointsMulEquiv (R := R) (A := A) (G := G) f) := by
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply, charOfPoint_mapValue]

/-- The inverse multiplicative equivalence sends a character to the point extending it. -/
@[simp]
theorem pointsMulEquiv_symm_apply (χ : G →* Aˣ) :
    (pointsMulEquiv (R := R) (A := A) (G := G)).symm χ = toConv (point χ) :=
  rfl

/-! ### The multiplicative group `𝔾ₘ` as `D(Multiplicative ℤ)`

Specializing to `G = Multiplicative ℤ` recovers the multiplicative group on the group-algebra
presentation `R[Multiplicative ℤ]`. The canonical `𝔾ₘ` points API remains
`TauCeti.MultiplicativeGroup.pointEquiv` for Laurent polynomials; the theorem below records how
the group-algebra presentation compares to it through
`AddMonoidAlgebra.toMultiplicativeAlgEquiv`. -/

/-- Evaluating `AddMonoidAlgebra.toMultiplicativeAlgEquiv` on the Laurent generator `T n`:
it sends `T n` to the group-like `single (ofAdd n) 1` of `R[Multiplicative ℤ]`. -/
private theorem toMultiplicativeAlgEquiv_T (n : ℤ) :
    AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R ℤ (LaurentPolynomial.T n) =
      MonoidAlgebra.single (Multiplicative.ofAdd n) 1 := by
  simp only [AddMonoidAlgebra.toMultiplicativeAlgEquiv, AlgEquiv.coe_mk,
    AddMonoidAlgebra.toMultiplicative, Equiv.coe_fn_mk, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single, MonoidAlgebra.ofCoeff_single]

/-- The group-algebra presentation of `D(Multiplicative ℤ)` agrees with the
Laurent-polynomial multiplicative group `𝔾ₘ` of `TauCeti.MultiplicativeGroup`: reading a point
on the generator `single (ofAdd 1) 1` gives the same unit as first precomposing it with
`AddMonoidAlgebra.toMultiplicativeAlgEquiv` and then using the canonical
`TauCeti.MultiplicativeGroup.pointEquiv`. -/
theorem multiplicativeGroup_pointEquiv_apply
    (f : MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) :
    charOfPoint f (Multiplicative.ofAdd 1) =
      MultiplicativeGroup.pointEquiv
        (f.comp (AddMonoidAlgebra.toMultiplicativeAlgEquiv (R := R) R ℤ).toAlgHom) := by
  ext
  rw [charOfPoint_apply_coe, MultiplicativeGroup.pointEquiv_apply,
    MultiplicativeGroup.unitOfPoint_val, AlgHom.comp_apply]
  congr 1
  exact (toMultiplicativeAlgEquiv_T 1).symm

end DiagonalizableGroup

end TauCeti
