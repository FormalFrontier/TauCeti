/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra

/-!
# Base change of the general linear coordinate Hopf algebra

For a morphism of commutative rings `R → K`, this file identifies scalar extension of the
coordinate ring of `GLₙ` with the coordinate ring constructed directly over `K`:

```text
K ⊗[R] R[Xᵢⱼ, det(X)⁻¹] ≃ K[Xᵢⱼ, det(X)⁻¹].
```

The equivalence first commutes tensor product with localization, then uses Mathlib's scalar
extension equivalence for multivariate polynomial rings. It preserves the generic matrix,
comultiplication, and counit, and is therefore bundled as an isomorphism of commutative Hopf
algebras. In particular, this is an identification of the chosen coordinate Hopf structures, not
only an abstract algebra isomorphism.

This is the general-linear compatibility needed by the base-change part of the explicit
Chevalley--Demazure construction in Layer 9 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.GeneralLinear.coordinateBaseChangeAlgEquiv`: the coordinate-algebra equivalence.
* `TauCeti.GeneralLinear.coordinateBaseChangeBialgEquiv`: the bialgebra equivalence.
* `TauCeti.GeneralLinear.coordinateBaseChangeIso`: its bundled commutative-Hopf-algebra form.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

private noncomputable abbrev genericDeterminant (S : Type*) [CommRing S] :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) S)

private noncomputable abbrev polynomialBaseChangeEquiv :
    K ⊗[R] MatrixMonoid.CoordinateRing R n ≃ₐ[K] MatrixMonoid.CoordinateRing K n :=
  MvPolynomial.algebraTensorAlgEquiv R K

private theorem polynomialBaseChangeEquiv_genericDeterminant :
    polynomialBaseChangeEquiv R K n
        (1 ⊗ₜ[R] genericDeterminant (n := n) R) = genericDeterminant (n := n) K := by
  rw [polynomialBaseChangeEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp only [one_smul]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

private noncomputable def localizedPolynomialBaseChangeHom :
    Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) →ₐ[K]
      CoordinateRing K n := by
  let e := polynomialBaseChangeEquiv R K n
  let f := e.toAlgHom
  have hdet : f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) =
      genericDeterminant (n := n) K :=
    polynomialBaseChangeEquiv_genericDeterminant R K n
  let _ : IsLocalization.Away
      (f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R)) (CoordinateRing K n) := by
    rw [hdet]
    infer_instance
  exact IsLocalization.Away.mapₐ
    (Aₚ := Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R))
    (Bₚ := CoordinateRing K n) f
    ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R)

private theorem localizedPolynomialBaseChangeHom_injective :
    Function.Injective (localizedPolynomialBaseChangeHom R K n) := by
  let e := polynomialBaseChangeEquiv R K n
  let f := e.toAlgHom
  have hdet : f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) =
      genericDeterminant (n := n) K :=
    polynomialBaseChangeEquiv_genericDeterminant R K n
  let _ : IsLocalization.Away
      (f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R)) (CoordinateRing K n) := by
    rw [hdet]
    infer_instance
  exact IsLocalization.Away.mapₐ_injective_of_injective
    (Aₚ := Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R))
    (Bₚ := CoordinateRing K n) (f := f)
    ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) e.injective

private theorem localizedPolynomialBaseChangeHom_surjective :
    Function.Surjective (localizedPolynomialBaseChangeHom R K n) := by
  let e := polynomialBaseChangeEquiv R K n
  let f := e.toAlgHom
  have hdet : f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) =
      genericDeterminant (n := n) K :=
    polynomialBaseChangeEquiv_genericDeterminant R K n
  let _ : IsLocalization.Away
      (f ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R)) (CoordinateRing K n) := by
    rw [hdet]
    infer_instance
  exact IsLocalization.Away.mapₐ_surjective_of_surjective
    (Aₚ := Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R))
    (Bₚ := CoordinateRing K n) (f := f)
    ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) e.surjective

private noncomputable def localizedPolynomialBaseChangeEquiv :
    Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) ≃ₐ[K]
      CoordinateRing K n :=
  AlgEquiv.ofBijective (localizedPolynomialBaseChangeHom R K n)
    ⟨localizedPolynomialBaseChangeHom_injective R K n,
      localizedPolynomialBaseChangeHom_surjective R K n⟩

/-- Scalar extension of the general-linear coordinate algebra is canonically the
general-linear coordinate algebra over the new base. -/
noncomputable def coordinateBaseChangeAlgEquiv :
    K ⊗[R] CoordinateRing R n ≃ₐ[K] CoordinateRing K n :=
  (IsLocalization.Away.tensorProductEquivTMulRight R K
      (genericDeterminant (n := n) R) (CoordinateRing R n)).trans
    (localizedPolynomialBaseChangeEquiv R K n)

/-- Base change sends a scalar tensored with a polynomial coordinate to that scalar times the
same polynomial with its coefficients extended to the new base. -/
@[simp]
theorem coordinateBaseChangeAlgEquiv_tmul_coordinateRingMap
    (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    coordinateBaseChangeAlgEquiv R K n (s ⊗ₜ[R] coordinateRingMap R n p) =
      s • coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p) := by
  rw [coordinateBaseChangeAlgEquiv, AlgEquiv.trans_apply, coordinateRingMap_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul]
  change localizedPolynomialBaseChangeHom R K n
      (algebraMap _ _ (s ⊗ₜ[R] p)) = _
  rw [localizedPolynomialBaseChangeHom, IsLocalization.Away.mapₐ_apply,
    IsLocalization.Away.map]
  simp [polynomialBaseChangeEquiv, Algebra.smul_def]

/-- Base change carries each localized generic matrix entry to the corresponding generic entry
over the new base. -/
@[simp]
theorem coordinateBaseChangeAlgEquiv_tmul_X (i j : Fin n) :
    coordinateBaseChangeAlgEquiv R K n
        (1 ⊗ₜ[R] coordinateRingMap R n (MvPolynomial.X (i, j))) =
      coordinateRingMap K n (MvPolynomial.X (i, j)) := by
  simp

private theorem coordinateHopfAlgebraAlgEquiv_symm_apply_apply
    (S : Type*) [CommRing S] (x : CoordinateRing S n) :
    (coordinateHopfAlgebraAlgEquiv S n).symm
        (coordinateHopfAlgebraAlgEquiv S n x) = x :=
  (coordinateHopfAlgebraAlgEquiv S n).symm_apply_apply x

private noncomputable def bundledCoordinateBaseChangeHom :
    K ⊗[R] coordinateHopfAlgebra R n →ₐ[K] coordinateHopfAlgebra K n := by
  letI : Algebra R (coordinateHopfAlgebra K n) :=
    Algebra.compHom _ (algebraMap R K)
  letI : IsScalarTower R K (coordinateHopfAlgebra K n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let g : coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra K n :=
    ((coordinateHopfAlgebraAlgEquiv K n).toAlgHom.restrictScalars R).comp
      (((coordinateBaseChangeAlgEquiv R K n).toAlgHom.restrictScalars R).comp
        ((Algebra.TensorProduct.includeRight :
          CoordinateRing R n →ₐ[R] K ⊗[R] CoordinateRing R n).comp
            (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom))
  exact (Algebra.TensorProduct.liftEquivRight R K (coordinateHopfAlgebra R n)
    (coordinateHopfAlgebra K n)) g

@[simp]
private theorem bundledCoordinateBaseChangeHom_tmul
    (s : K) (x : coordinateHopfAlgebra R n) :
    bundledCoordinateBaseChangeHom R K n
        (s ⊗ₜ[R] x) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateBaseChangeAlgEquiv R K n
          (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R n).symm x)) := by
  rw [bundledCoordinateBaseChangeHom]
  simp only [Algebra.TensorProduct.liftEquivRight_apply, Algebra.TensorProduct.lift_tmul,
    AlgHom.coe_restrictScalars', AlgHom.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  change algebraMap K (coordinateHopfAlgebra K n) s * _ = _
  rw [← Algebra.smul_def, ← map_smul, ← map_smul,
    ← TensorProduct.tmul_eq_smul_one_tmul]
  rfl

private noncomputable def bundledTensorMap :
    K ⊗[R] CoordinateRing R n →ₐ[K] K ⊗[R] coordinateHopfAlgebra R n := by
  let g : CoordinateRing R n →ₐ[R] K ⊗[R] coordinateHopfAlgebra R n :=
    (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
      K ⊗[R] coordinateHopfAlgebra R n).comp
        (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
  exact (Algebra.TensorProduct.liftEquivRight R K (CoordinateRing R n)
    (K ⊗[R] coordinateHopfAlgebra R n)) g

private theorem bundledTensorMap_eq_map (z : K ⊗[R] CoordinateRing R n) :
    bundledTensorMap R K n z =
      Algebra.TensorProduct.map (AlgHom.id R K)
        (coordinateHopfAlgebraAlgEquiv R n).toAlgHom z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x => simp [bundledTensorMap]

private theorem bundledCoordinateBaseChangeHom_bundledTensorMap
    (z : K ⊗[R] CoordinateRing R n) :
    bundledCoordinateBaseChangeHom R K n (bundledTensorMap R K n z) =
      coordinateHopfAlgebraAlgEquiv K n (coordinateBaseChangeAlgEquiv R K n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
      rw [bundledTensorMap_eq_map, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        bundledCoordinateBaseChangeHom_tmul]
      exact congrArg
        (fun y : CoordinateRing R n =>
          coordinateHopfAlgebraAlgEquiv K n
            (coordinateBaseChangeAlgEquiv R K n (s ⊗ₜ[R] y)))
        (coordinateHopfAlgebraAlgEquiv_symm_apply_apply (n := n) R x)

private theorem bundledTensorMap_bijective :
    Function.Bijective (bundledTensorMap R K n) := by
  rw [show (bundledTensorMap R K n : K ⊗[R] CoordinateRing R n →
      K ⊗[R] coordinateHopfAlgebra R n) =
      Algebra.TensorProduct.map (AlgHom.id R K)
        (coordinateHopfAlgebraAlgEquiv R n).toAlgHom from
    funext (bundledTensorMap_eq_map R K n)]
  exact Algebra.TensorProduct.map_bijective Function.bijective_id
    (coordinateHopfAlgebraAlgEquiv R n).bijective

private theorem bundledCoordinateBaseChangeHom_bijective :
    Function.Bijective (bundledCoordinateBaseChangeHom R K n) := by
  apply (Function.Bijective.of_comp_iff _ (bundledTensorMap_bijective R K n)).mp
  rw [show (bundledCoordinateBaseChangeHom R K n :
        K ⊗[R] coordinateHopfAlgebra R n → coordinateHopfAlgebra K n) ∘
        bundledTensorMap R K n =
      (coordinateHopfAlgebraAlgEquiv K n : CoordinateRing K n →
          coordinateHopfAlgebra K n) ∘ coordinateBaseChangeAlgEquiv R K n from
    funext (bundledCoordinateBaseChangeHom_bundledTensorMap R K n)]
  exact (coordinateHopfAlgebraAlgEquiv K n).bijective.comp
    (coordinateBaseChangeAlgEquiv R K n).bijective

private noncomputable def bundledCoordinateBaseChangeAlgEquiv :
    K ⊗[R] coordinateHopfAlgebra R n ≃ₐ[K] coordinateHopfAlgebra K n :=
  AlgEquiv.ofBijective (bundledCoordinateBaseChangeHom R K n)
    (bundledCoordinateBaseChangeHom_bijective R K n)

@[simp]
private theorem bundledCoordinateBaseChangeAlgEquiv_tmul
    (s : K) (x : coordinateHopfAlgebra R n) :
    bundledCoordinateBaseChangeAlgEquiv R K n (s ⊗ₜ[R] x) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateBaseChangeAlgEquiv R K n
          (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R n).symm x)) :=
  bundledCoordinateBaseChangeHom_tmul R K n s x

private theorem bundledCoordinateBaseChangeAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (coordinateHopfAlgebra K n)).comp
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom =
      Bialgebra.counitAlgHom K
        (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n)) := by
  have hrestrict :
      (((Bialgebra.counitAlgHom K (coordinateHopfAlgebra K n)).comp
          (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
              K ⊗[R] coordinateHopfAlgebra R n) =
        (Algebra.ofId R K).comp
          (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n)) := by
    apply coordinateHopfAlgebra_algHom_ext R n
    intro i j
    simp
  have hinclude :
      (((Bialgebra.counitAlgHom K (coordinateHopfAlgebra K n)).comp
          (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
              K ⊗[R] coordinateHopfAlgebra R n) =
        ((Bialgebra.counitAlgHom K
          (CommHopfAlgCat.baseChange (K := K)
            (coordinateHopfAlgebra R n))).restrictScalars R).comp
              (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
                K ⊗[R] coordinateHopfAlgebra R n) :=
    hrestrict.trans (Bialgebra.counitAlgHom_comp_includeRight
      (R := R) (A := K) (B := coordinateHopfAlgebra R n)).symm
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul]
      congr 1
      simpa only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
        Algebra.TensorProduct.includeRight_apply]
        using DFunLike.congr_fun hinclude x

private theorem bundledCoordinateBaseChangeAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).comp
          (Bialgebra.comulAlgHom K
            (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n))) =
      (Bialgebra.comulAlgHom K (coordinateHopfAlgebra K n)).comp
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom := by
  let _ : Algebra R
      (coordinateHopfAlgebra K n ⊗[K] coordinateHopfAlgebra K n) :=
    Algebra.compHom _ (algebraMap R K)
  let _ : IsScalarTower R K
      (coordinateHopfAlgebra K n ⊗[K] coordinateHopfAlgebra K n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hrestrict :
      ((((Algebra.TensorProduct.map
          (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom
          (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).comp
          (Bialgebra.comulAlgHom K
            (CommHopfAlgCat.baseChange (K := K)
              (coordinateHopfAlgebra R n)))).restrictScalars R).comp
                (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
                  K ⊗[R] coordinateHopfAlgebra R n)) =
        (((Bialgebra.comulAlgHom K (coordinateHopfAlgebra K n)).comp
          (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : coordinateHopfAlgebra R n →ₐ[R]
              K ⊗[R] coordinateHopfAlgebra R n) := by
    apply coordinateHopfAlgebra_algHom_ext R n
    intro i j
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply,
      TensorProduct.comul_tmul, CommSemiring.comul_apply, coordinateHopfAlgebra_comul_X,
      AlgEquiv.coe_toAlgHom, bundledCoordinateBaseChangeAlgEquiv_tmul,
      AlgEquiv.symm_apply_apply, coordinateBaseChangeAlgEquiv_tmul_coordinateRingMap,
      MvPolynomial.map_X, one_smul]
    rw [TensorProduct.tmul_sum, map_sum]
    simp
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul]
      congr 1
      simpa only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
        Algebra.TensorProduct.includeRight_apply]
        using DFunLike.congr_fun hrestrict x

/-- **The coordinate Hopf algebra of `GLₙ` commutes with base change.** -/
noncomputable def coordinateBaseChangeBialgEquiv :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≃ₐc[K]
      coordinateHopfAlgebra K n :=
  BialgEquiv.ofAlgEquiv (bundledCoordinateBaseChangeAlgEquiv R K n)
    (bundledCoordinateBaseChangeAlgEquiv_counit_comp R K n)
    (bundledCoordinateBaseChangeAlgEquiv_map_comp_comul R K n)

/-- On polynomial coordinates, the Hopf-algebra base-change equivalence extends coefficients and
multiplies by the scalar in the new base. -/
@[simp]
theorem coordinateBaseChangeBialgEquiv_tmul_coordinateRingMap
    (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    coordinateBaseChangeBialgEquiv R K n
        (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) =
      coordinateHopfAlgebraAlgEquiv K n
        (s • coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p)) := by
  rw [coordinateBaseChangeBialgEquiv, BialgEquiv.ofAlgEquiv_apply,
    bundledCoordinateBaseChangeAlgEquiv]
  change bundledCoordinateBaseChangeHom R K n
      (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) = _
  rw [bundledCoordinateBaseChangeHom_tmul]
  have hcancel :
      (coordinateHopfAlgebraAlgEquiv R n).symm
          (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) =
        coordinateRingMap R n p :=
    (coordinateHopfAlgebraAlgEquiv R n).symm_apply_apply _
  calc
    coordinateHopfAlgebraAlgEquiv K n
          (coordinateBaseChangeAlgEquiv R K n
            (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R n).symm
              (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)))) =
        coordinateHopfAlgebraAlgEquiv K n
          (coordinateBaseChangeAlgEquiv R K n
            (s ⊗ₜ[R] coordinateRingMap R n p)) :=
      congrArg
        (fun x : CoordinateRing R n =>
          coordinateHopfAlgebraAlgEquiv K n
            (coordinateBaseChangeAlgEquiv R K n (s ⊗ₜ[R] x))) hcancel
    _ = _ := congrArg (coordinateHopfAlgebraAlgEquiv K n)
      (coordinateBaseChangeAlgEquiv_tmul_coordinateRingMap R K n s p)

/-- Base change carries each bundled generic matrix entry to the corresponding entry over the
new base. -/
@[simp]
theorem coordinateBaseChangeBialgEquiv_tmul_X (i j : Fin n) :
    coordinateBaseChangeBialgEquiv R K n
        (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateRingMap K n (MvPolynomial.X (i, j))) := by
  simpa using coordinateBaseChangeBialgEquiv_tmul_coordinateRingMap R K n
    (1 : K) (MvPolynomial.X (i, j))

/-- Base change of the bundled general-linear coordinate Hopf algebra is canonically the
general-linear coordinate Hopf algebra over the new base. -/
noncomputable def coordinateBaseChangeIso
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  (CommHopfAlgCat.ofIsoSelf
      (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n))).symm ≪≫
    CommHopfAlgCat.isoMk (coordinateBaseChangeBialgEquiv R K n) ≪≫
      CommHopfAlgCat.ofIsoSelf (coordinateHopfAlgebra K n)

end TauCeti.GeneralLinear
