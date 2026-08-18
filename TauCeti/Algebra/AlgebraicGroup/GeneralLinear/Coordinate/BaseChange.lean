/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
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

* `TauCeti.GeneralLinear.coordinateRingBaseChangeAlgEquiv`: the coordinate-ring equivalence.
* `TauCeti.GeneralLinear.coordinateHopfAlgebraBaseChangeBialgEquiv`: the bialgebra equivalence.
* `TauCeti.GeneralLinear.coordinateHopfAlgebraBaseChangeIso`: its bundled
  commutative-Hopf-algebra form, when the extension ring's universe contains the base ring's.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).
* The underlying formal equivalences are Mathlib's
  `IsLocalization.Away.tensorProductEquivTMulRight` and
  `MvPolynomial.algebraTensorAlgEquiv`; the bundled base-changed Hopf structure is
  Tau Ceti's `CommHopfAlgCat.baseChange`.
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

private theorem polynomialBaseChangeEquiv_one_tmul_genericDeterminant :
    polynomialBaseChangeEquiv R K n
        (1 ⊗ₜ[R] genericDeterminant (n := n) R) = genericDeterminant (n := n) K := by
  rw [polynomialBaseChangeEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]
  simp only [one_smul]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

private noncomputable def localizedPolynomialBaseChangeEquiv :
    Localization.Away ((1 : K) ⊗ₜ[R] genericDeterminant (n := n) R) ≃ₐ[K]
      CoordinateRing K n :=
  IsLocalization.algEquivOfAlgEquiv _ _ (polynomialBaseChangeEquiv R K n) (by
    rw [Submonoid.map_powers, polynomialBaseChangeEquiv_one_tmul_genericDeterminant])

/-- Scalar extension of the general-linear coordinate algebra is canonically the
general-linear coordinate algebra over the new base. -/
noncomputable def coordinateRingBaseChangeAlgEquiv :
    K ⊗[R] CoordinateRing R n ≃ₐ[K] CoordinateRing K n :=
  (IsLocalization.Away.tensorProductEquivTMulRight R K
      (genericDeterminant (n := n) R) (CoordinateRing R n)).trans
    (localizedPolynomialBaseChangeEquiv R K n)

/-- Base change sends a scalar tensored with a polynomial coordinate to that scalar times the
same polynomial with its coefficients extended to the new base. -/
@[simp]
theorem coordinateRingBaseChangeAlgEquiv_tmul_coordinateRingMap
    (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    coordinateRingBaseChangeAlgEquiv R K n (s ⊗ₜ[R] coordinateRingMap R n p) =
      s • coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p) := by
  rw [coordinateRingBaseChangeAlgEquiv, AlgEquiv.trans_apply, coordinateRingMap_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul]
  rw [localizedPolynomialBaseChangeEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  simp [polynomialBaseChangeEquiv, Algebra.smul_def]

/-- Base change carries each localized generic matrix entry to the corresponding generic entry
over the new base. -/
theorem coordinateRingBaseChangeAlgEquiv_one_tmul_X (i j : Fin n) :
    coordinateRingBaseChangeAlgEquiv R K n
        (1 ⊗ₜ[R] coordinateRingMap R n (MvPolynomial.X (i, j))) =
      coordinateRingMap K n (MvPolynomial.X (i, j)) := by
  simp

/-- The inverse coordinate-ring base-change equivalence sends a polynomial coordinate with
extended coefficients back to the corresponding pure tensor. -/
@[simp]
theorem coordinateRingBaseChangeAlgEquiv_symm_coordinateRingMap
    (p : MatrixMonoid.CoordinateRing R n) :
    (coordinateRingBaseChangeAlgEquiv R K n).symm
        (coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p)) =
      1 ⊗ₜ[R] coordinateRingMap R n p := by
  apply (coordinateRingBaseChangeAlgEquiv R K n).symm_apply_eq.mpr
  simp

private noncomputable def bundledCoordinateBaseChangeAlgEquiv :
    K ⊗[R] coordinateHopfAlgebra R n ≃ₐ[K] coordinateHopfAlgebra K n :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K))
      (coordinateHopfAlgebraAlgEquiv R n)).symm.trans
    ((coordinateRingBaseChangeAlgEquiv R K n).trans
      (coordinateHopfAlgebraAlgEquiv K n))

@[simp]
private theorem bundledCoordinateBaseChangeAlgEquiv_tmul
    (s : K) (x : coordinateHopfAlgebra R n) :
    bundledCoordinateBaseChangeAlgEquiv R K n (s ⊗ₜ[R] x) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateRingBaseChangeAlgEquiv R K n
          (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R n).symm x)) :=
  by simp [bundledCoordinateBaseChangeAlgEquiv]

/-- Two `K`-algebra maps out of the base-changed coordinate Hopf algebra of `GLₙ` are equal if
they agree on the pure tensors of localized generic entries. -/
theorem coordinateHopfAlgebra_baseChange_algHom_ext
    {C : Type*} [CommRing C] [Algebra R C] [Algebra K C] [IsScalarTower R K C]
    {f g : K ⊗[R] coordinateHopfAlgebra R n →ₐ[K] C}
    (h : ∀ i j, f (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      g (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
        (coordinateRingMap R n (MvPolynomial.X (i, j))))) :
    f = g := by
  apply (Algebra.TensorProduct.liftEquivRight R K _ _).symm.injective
  apply coordinateHopfAlgebra_algHom_ext R n
  intro i j
  simpa only [Algebra.TensorProduct.liftEquivRight_symm_apply, AlgHom.comp_apply,
    AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply] using h i j

-- `CommHopfAlgCat.baseChange H` abbreviates `CommHopfAlgCat.of K (K ⊗[R] H)`, so its
-- stored counit and comultiplication are definitionally Mathlib's tensor-product bialgebra
-- structure used in the following two preservation proofs and by `BialgEquiv.ofAlgEquiv`.
private theorem bundledCoordinateBaseChangeAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (coordinateHopfAlgebra K n)).comp
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom =
      Bialgebra.counitAlgHom K
        (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n)) := by
  apply coordinateHopfAlgebra_baseChange_algHom_ext R K n
  intro i j
  simp

private theorem bundledCoordinateBaseChangeAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom).comp
          (Bialgebra.comulAlgHom K
            (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n))) =
      (Bialgebra.comulAlgHom K (coordinateHopfAlgebra K n)).comp
        (bundledCoordinateBaseChangeAlgEquiv R K n).toAlgHom := by
  -- The tensor target has no global `R`-algebra instance. `Algebra.compHom` supplies the one
  -- needed by the extensionality lemma, and the scalar-tower law is definitionally `rfl`.
  let _ : Algebra R
      (coordinateHopfAlgebra K n ⊗[K] coordinateHopfAlgebra K n) :=
    Algebra.compHom _ (algebraMap R K)
  let _ : IsScalarTower R K
      (coordinateHopfAlgebra K n ⊗[K] coordinateHopfAlgebra K n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply coordinateHopfAlgebra_baseChange_algHom_ext R K n
  intro i j
  simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply, coordinateHopfAlgebra_comul_X,
    AlgEquiv.coe_toAlgHom, bundledCoordinateBaseChangeAlgEquiv_tmul,
    AlgEquiv.symm_apply_apply, coordinateRingBaseChangeAlgEquiv_tmul_coordinateRingMap,
    MvPolynomial.map_X, one_smul]
  rw [TensorProduct.tmul_sum, map_sum]
  simp

/-- **The coordinate Hopf algebra of `GLₙ` commutes with base change.** -/
noncomputable def coordinateHopfAlgebraBaseChangeBialgEquiv :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≃ₐc[K]
      coordinateHopfAlgebra K n :=
  BialgEquiv.ofAlgEquiv (bundledCoordinateBaseChangeAlgEquiv R K n)
    (bundledCoordinateBaseChangeAlgEquiv_counit_comp R K n)
    (bundledCoordinateBaseChangeAlgEquiv_map_comp_comul R K n)

/-- The Hopf-algebra base-change equivalence on an arbitrary pure tensor, expressed through the
coordinate-ring equivalence. -/
theorem coordinateHopfAlgebraBaseChangeBialgEquiv_tmul
    (s : K) (x : coordinateHopfAlgebra R n) :
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n (s ⊗ₜ[R] x) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateRingBaseChangeAlgEquiv R K n
          (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R n).symm x)) := by
  exact bundledCoordinateBaseChangeAlgEquiv_tmul R K n s x

/-- On polynomial coordinates, the Hopf-algebra base-change equivalence extends coefficients and
multiplies by the scalar in the new base. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeBialgEquiv_tmul_coordinateRingMap
    (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n
        (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) =
      coordinateHopfAlgebraAlgEquiv K n
        (s • coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p)) := by
  simp [coordinateHopfAlgebraBaseChangeBialgEquiv,
    bundledCoordinateBaseChangeAlgEquiv]

/-- The inverse Hopf-algebra base-change equivalence sends a polynomial coordinate with extended
coefficients back to the corresponding pure tensor. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeBialgEquiv_symm_coordinateRingMap
    (p : MatrixMonoid.CoordinateRing R n) :
    (coordinateHopfAlgebraBaseChangeBialgEquiv R K n).symm
        (coordinateHopfAlgebraAlgEquiv K n
          (coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p))) =
      1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p) := by
  apply (coordinateHopfAlgebraBaseChangeBialgEquiv R K n).symm_apply_eq.mpr
  change coordinateHopfAlgebraAlgEquiv K n
      (coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p)) =
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n
      (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p))
  simpa only [one_smul] using
    (coordinateHopfAlgebraBaseChangeBialgEquiv_tmul_coordinateRingMap R K n
      (1 : K) p).symm

/-- Base change carries each bundled generic matrix entry to the corresponding entry over the
new base. -/
theorem coordinateHopfAlgebraBaseChangeBialgEquiv_one_tmul_X (i j : Fin n) :
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n
        (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateHopfAlgebraAlgEquiv K n
        (coordinateRingMap K n (MvPolynomial.X (i, j))) := by
  simpa using coordinateHopfAlgebraBaseChangeBialgEquiv_tmul_coordinateRingMap R K n
    (1 : K) (MvPolynomial.X (i, j))

/-- Base change carries each inverse localized generic matrix entry to the corresponding inverse
entry over the new base. -/
theorem coordinateHopfAlgebraBaseChangeBialgEquiv_one_tmul_nonsing_inv (i j : Fin n) :
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n
        (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
          ((localizedGenericMatrix R n)⁻¹ i j)) =
      coordinateHopfAlgebraAlgEquiv K n ((localizedGenericMatrix K n)⁻¹ i j) := by
  rw [← coordinateHopfAlgebra_antipode_X R n i j,
    ← coordinateHopfAlgebra_antipode_X K n i j]
  calc
    coordinateHopfAlgebraBaseChangeBialgEquiv R K n
          (1 ⊗ₜ[R] HopfAlgebra.antipode R
            (coordinateHopfAlgebraAlgEquiv R n
              (coordinateRingMap R n (MvPolynomial.X (i, j))))) =
        coordinateHopfAlgebraBaseChangeBialgEquiv R K n
          (HopfAlgebra.antipode K
            (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
              (coordinateRingMap R n (MvPolynomial.X (i, j))))) := by
      rfl
    _ = HopfAlgebra.antipode K
          (coordinateHopfAlgebraBaseChangeBialgEquiv R K n
            (1 ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n
              (coordinateRingMap R n (MvPolynomial.X (i, j))))) :=
      BialgHomClass.map_antipode _ _
    _ = HopfAlgebra.antipode K
          (coordinateHopfAlgebraAlgEquiv K n
            (coordinateRingMap K n (MvPolynomial.X (i, j)))) := by
      rw [coordinateHopfAlgebraBaseChangeBialgEquiv_one_tmul_X]

/-- Base change of the bundled general-linear coordinate Hopf algebra is canonically the
general-linear coordinate Hopf algebra over the new base. The extension ring's carrier universe
must contain the base ring's carrier universe; in particular, this covers `ℤ → K` for `K` in any
universe. The unbundled algebra and bialgebra equivalences have no such restriction. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ) :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  (CommHopfAlgCat.ofIsoSelf
      (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n))).symm ≪≫
    CommHopfAlgCat.isoMk (coordinateHopfAlgebraBaseChangeBialgEquiv R K n) ≪≫
      CommHopfAlgCat.ofIsoSelf (coordinateHopfAlgebra K n)

/-- The categorical base-change isomorphism has the same action on polynomial coordinates as the
underlying bialgebra equivalence. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_hom_apply
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
    (n : ℕ) (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    (coordinateHopfAlgebraBaseChangeIso R K n).hom
        (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) =
      coordinateHopfAlgebraAlgEquiv K n
        (s • coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p)) := by
  change coordinateHopfAlgebraBaseChangeBialgEquiv R K n
      (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) = _
  exact coordinateHopfAlgebraBaseChangeBialgEquiv_tmul_coordinateRingMap R K n s p

/-- The inverse categorical base-change isomorphism sends an extended polynomial coordinate back
to its scalar pure tensor. -/
@[simp]
theorem coordinateHopfAlgebraBaseChangeIso_inv_apply
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
    (n : ℕ) (s : K) (p : MatrixMonoid.CoordinateRing R n) :
    s • (coordinateHopfAlgebraBaseChangeIso R K n).inv
        (coordinateHopfAlgebraAlgEquiv K n
          (coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p))) =
      s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p) := by
  change s • (coordinateHopfAlgebraBaseChangeBialgEquiv R K n).symm
      (coordinateHopfAlgebraAlgEquiv K n
        (coordinateRingMap K n (MvPolynomial.map (algebraMap R K) p))) = _
  rw [coordinateHopfAlgebraBaseChangeBialgEquiv_symm_coordinateRingMap]
  exact (TensorProduct.tmul_eq_smul_one_tmul (R := R) s
    (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p))).symm

end TauCeti.GeneralLinear
