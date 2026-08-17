/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare

/-!
# Exterior bivectors and the standard orthogonal Lie algebra

For the standard sum-of-squares quadratic form on `Fin n → R`, the second exterior power is
canonically the matrix orthogonal Lie algebra. The forward map sends `u ∧ v` to the skew matrix
with entries `2 * (u i * v j - v i * u j)`; the factor of two matches the polar form of the
sum-of-squares quadratic form.

The inverse reads `⅟ 2` times the upper-triangular entries of a skew matrix in the
standard exterior basis.
Lie compatibility is proved through the faithful Clifford generators and the established
commutator action of Clifford bivectors, rather than by expanding a matrix commutator.

## Main results

* `CliffordAlgebra.bivectorEquivSo`: the standard exterior-bivector Lie equivalence.
* `CliffordAlgebra.bivectorEquivSo_apply_ιMulti`: its value on a decomposable bivector.
* `CliffordAlgebra.bivectorEquivSo_symm_repr_apply`: the coefficients of its inverse.
* `CliffordAlgebra.bivectorEquivSo_apply_ιMulti_mulVec`: its normalized action on a vector.

## References

This implements the Layer 3 "Bivectors are `𝔰𝔬(V)`" target in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`.
-/

public section

open scoped Matrix

open TauCeti

universe u

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (R : Type u) [CommRing R]

private def standardBivectorMatrix :
    (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] Matrix (Fin n) (Fin n) R :=
  2 • (vecMulVecBilin R R - LinearMap.flip (vecMulVecBilin R R))

@[simp]
private theorem standardBivectorMatrix_apply (u v : Fin n → R) (i j : Fin n) :
    standardBivectorMatrix n R u v i j = 2 * (u i * v j - v i * u j) :=
  by simp [standardBivectorMatrix, Matrix.vecMulVec_apply, mul_sub]

private theorem standardBivectorMatrix_self (u : Fin n → R) :
    standardBivectorMatrix n R u u = 0 := by
  ext i j
  simp

private noncomputable def standardBivectorAlternating :
    (Fin n → R) [⋀^Fin 2]→ₗ[R] LieAlgebra.Orthogonal.so (Fin n) R :=
  { toFun := fun v =>
      ⟨standardBivectorMatrix n R (v 0) (v 1), by
        apply (LieAlgebra.Orthogonal.mem_so (Fin n) R _).2
        ext i j
        simp [Matrix.transpose_apply]
        ring⟩
    map_update_add' := by
      intro _ v i x y
      fin_cases i
      · apply Subtype.ext
        simp
      · apply Subtype.ext
        simp
    map_update_smul' := by
      intro _ v i c x
      fin_cases i
      · apply Subtype.ext
        simp
      · apply Subtype.ext
        simp
    map_eq_zero_of_eq' := by
      intro v i j h hij
      fin_cases i <;> fin_cases j <;> simp_all [standardBivectorMatrix_self] <;> rfl }

private noncomputable def standardBivectorToSoLinear :
    ⋀[R]^2 (Fin n → R) →ₗ[R] LieAlgebra.Orthogonal.so (Fin n) R :=
  exteriorPower.alternatingMapLinearEquiv (standardBivectorAlternating n R)

private theorem standardBivectorToSoLinear_apply_ιMulti (u v : Fin n → R) :
    ((standardBivectorToSoLinear n R (exteriorPower.ιMulti R 2 ![u, v]) :
      LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      fun i j => 2 * (u i * v j - v i * u j) := by
  funext i j
  simp [standardBivectorToSoLinear, standardBivectorAlternating]

private noncomputable def exteriorBasis :
    Module.Basis (Set.powersetCard (Fin n) 2) R (⋀[R]^2 (Fin n → R)) :=
  (Pi.basisFun R (Fin n)).exteriorPower 2

variable [Invertible (2 : R)]

private noncomputable def soCoordinates :
    LieAlgebra.Orthogonal.so (Fin n) R →ₗ[R] Set.powersetCard (Fin n) 2 → R where
  toFun A s :=
    let e := Set.powersetCard.ofFinEmbEquiv.symm s
    (⅟ (2 : R)) * (A : Matrix (Fin n) (Fin n) R) (e 0) (e 1)
  map_add' A B := by
    funext s
    dsimp
    ring
  map_smul' c A := by
    funext s
    dsimp
    ring

private noncomputable def soToExteriorLinear :
    LieAlgebra.Orthogonal.so (Fin n) R →ₗ[R] ⋀[R]^2 (Fin n → R) :=
  (exteriorBasis n R).equivFun.symm.toLinearMap.comp (soCoordinates n R)

private theorem soCoordinates_standardBivectorToSoLinear
    (x : ⋀[R]^2 (Fin n → R)) :
    soCoordinates n R (standardBivectorToSoLinear n R x) = (exteriorBasis n R).equivFun x := by
  have hmap : (soCoordinates n R).comp (standardBivectorToSoLinear n R) =
      (exteriorBasis n R).equivFun.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    funext s
    let e := Set.powersetCard.ofFinEmbEquiv.symm s
    -- Expose the coordinate map's local order embedding before evaluating the exterior basis.
    change (⅟ (2 : R)) *
        ((standardBivectorToSoLinear n R (exteriorPower.ιMulti R 2 u) :
          LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) (e 0) (e 1) =
      (exteriorBasis n R).equivFun (exteriorPower.ιMulti R 2 u) s
    rw [Module.Basis.equivFun_apply]
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hu]
    rw [exteriorBasis, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, standardBivectorToSoLinear_apply_ιMulti]
    rw [Matrix.det_fin_two]
    dsimp [e]
    simp [Pi.basisFun, ← mul_assoc, mul_comm]
  exact LinearMap.congr_fun hmap x

private theorem soToExteriorLinear_standardBivectorToSoLinear
    (x : ⋀[R]^2 (Fin n → R)) :
    soToExteriorLinear n R (standardBivectorToSoLinear n R x) = x := by
  apply (exteriorBasis n R).equivFun.injective
  -- Expose the basis equivalence and its inverse hidden by the composed linear map.
  change (exteriorBasis n R).equivFun
      ((exteriorBasis n R).equivFun.symm
        (soCoordinates n R (standardBivectorToSoLinear n R x))) =
    (exteriorBasis n R).equivFun x
  rw [LinearEquiv.apply_symm_apply, soCoordinates_standardBivectorToSoLinear]

private theorem soCoordinates_injective : Function.Injective (soCoordinates n R) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have hskew (C : LieAlgebra.Orthogonal.so (Fin n) R) (a b : Fin n) :
      (C : Matrix (Fin n) (Fin n) R) b a =
        -(C : Matrix (Fin n) (Fin n) R) a b := by
    have hC := (LieAlgebra.Orthogonal.mem_so (Fin n) R
      (C : Matrix (Fin n) (Fin n) R)).1 C.property
    exact congr_fun (congr_fun hC a) b
  have hupper (a b : Fin n) (hab : a < b) :
      (A : Matrix (Fin n) (Fin n) R) a b =
        (B : Matrix (Fin n) (Fin n) R) a b := by
    let e : Fin 2 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b] (by
      apply Fin.strictMono_iff_lt_succ.2
      intro k
      fin_cases k
      simpa using hab)
    have hs := congr_fun h (Set.powersetCard.ofFinEmbEquiv e)
    -- Expose the upper-triangular coordinate selected by the local order embedding.
    change (⅟ (2 : R)) *
        (A : Matrix (Fin n) (Fin n) R)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv e) 0)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv e) 1) =
      (⅟ (2 : R)) *
        (B : Matrix (Fin n) (Fin n) R)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv e) 0)
          (Set.powersetCard.ofFinEmbEquiv.symm
            (Set.powersetCard.ofFinEmbEquiv e) 1) at hs
    rw [Equiv.symm_apply_apply] at hs
    -- Normalize the coordinate equality before cancelling the invertible factor `⅟ 2`.
    change (⅟ (2 : R)) * (A : Matrix (Fin n) (Fin n) R) a b =
      (⅟ (2 : R)) * (B : Matrix (Fin n) (Fin n) R) a b at hs
    exact (mul_right_inj_of_invertible (⅟ (2 : R))).mp hs
  by_cases hij : i < j
  · exact hupper i j hij
  by_cases hji : j < i
  · calc
      (A : Matrix (Fin n) (Fin n) R) i j =
          -(A : Matrix (Fin n) (Fin n) R) j i := hskew A j i
      _ = -(B : Matrix (Fin n) (Fin n) R) j i := congrArg Neg.neg (hupper j i hji)
      _ = (B : Matrix (Fin n) (Fin n) R) i j := (hskew B j i).symm
  · have hij' : i = j := le_antisymm (not_lt.mp hji) (not_lt.mp hij)
    subst j
    have hdiag (C : LieAlgebra.Orthogonal.so (Fin n) R) :
        (C : Matrix (Fin n) (Fin n) R) i i = 0 := by
      have hs := hskew C i i
      have htwo : (2 : R) * (C : Matrix (Fin n) (Fin n) R) i i = 0 := by
        calc
          (2 : R) * (C : Matrix (Fin n) (Fin n) R) i i =
              (C : Matrix (Fin n) (Fin n) R) i i +
                (C : Matrix (Fin n) (Fin n) R) i i := two_mul _
          _ = -(C : Matrix (Fin n) (Fin n) R) i i +
                (C : Matrix (Fin n) (Fin n) R) i i := congrArg
                  (fun x => x + (C : Matrix (Fin n) (Fin n) R) i i) hs
          _ = 0 := neg_add_cancel _
      exact (mul_right_inj_of_invertible (2 : R)).mp (by simpa using htwo)
    rw [hdiag A, hdiag B]

private theorem standardBivectorToSoLinear_soToExteriorLinear
    (A : LieAlgebra.Orthogonal.so (Fin n) R) :
    standardBivectorToSoLinear n R (soToExteriorLinear n R A) = A := by
  apply soCoordinates_injective n R
  rw [soCoordinates_standardBivectorToSoLinear]
  -- Expose the basis equivalence and inverse hidden by `soToExteriorLinear`.
  change (exteriorBasis n R).equivFun
      ((exteriorBasis n R).equivFun.symm (soCoordinates n R A)) = soCoordinates n R A
  exact LinearEquiv.apply_symm_apply (exteriorBasis n R).equivFun (soCoordinates n R A)

private noncomputable def standardBivectorLinearEquiv :
    ⋀[R]^2 (Fin n → R) ≃ₗ[R] LieAlgebra.Orthogonal.so (Fin n) R where
  toLinearMap := standardBivectorToSoLinear n R
  invFun := soToExteriorLinear n R
  left_inv := soToExteriorLinear_standardBivectorToSoLinear n R
  right_inv := standardBivectorToSoLinear_soToExteriorLinear n R

omit [Invertible (2 : R)] in
private theorem standardBivectorToSoLinear_mulVec (u v x : Fin n → R) :
    (((standardBivectorToSoLinear n R (exteriorPower.ιMulti R 2 ![u, v]) :
      LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x) =
      (2 * ∑ i, v i * x i) • u - (2 * ∑ i, u i * x i) • v := by
  rw [standardBivectorToSoLinear_apply_ιMulti]
  -- Expose the bilinear outer-product representation for Mathlib's named action theorem.
  rw [show (fun i j => 2 * (u i * v j - v i * u j)) =
      standardBivectorMatrix n R u v by
    funext i j
    exact (standardBivectorMatrix_apply n R u v i j).symm]
  change (2 • (Matrix.vecMulVec u v - Matrix.vecMulVec v u)) *ᵥ x = _
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp [dotProduct]
  ring

private theorem ι_standardBivectorToSoLinear_mulVec
    (x : ⋀[R]^2 (Fin n → R)) (y : Fin n → R) :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    ι Q ((((standardBivectorToSoLinear n R x :
      LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ y)) =
      ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q x :
        quadraticLieSubalgebra Q) : CliffordAlgebra Q), ι Q y⁆ := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let lhs : ⋀[R]^2 (Fin n → R) →ₗ[R] CliffordAlgebra Q :=
    { toFun := fun z =>
        ι Q ((((standardBivectorToSoLinear n R z :
          LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ y))
      map_add' := by
        intro a b
        rw [(standardBivectorToSoLinear n R).map_add]
        -- Expose matrix addition beneath the orthogonal-Lie-subalgebra coercion.
        change ι Q ((↑(standardBivectorToSoLinear n R a) +
          ↑(standardBivectorToSoLinear n R b)) *ᵥ y) = _
        rw [Matrix.add_mulVec, map_add]
      map_smul' := by
        intro c a
        rw [(standardBivectorToSoLinear n R).map_smul]
        -- Expose matrix scalar multiplication beneath the subalgebra coercion.
        change ι Q ((c • ↑(standardBivectorToSoLinear n R a)) *ᵥ y) = _
        rw [Matrix.smul_mulVec, map_smul]
        rfl }
  let rhs : ⋀[R]^2 (Fin n → R) →ₗ[R] CliffordAlgebra Q :=
    { toFun := fun z =>
        ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q z :
          quadraticLieSubalgebra Q) : CliffordAlgebra Q), ι Q y⁆
      map_add' := by
        intro a b
        rw [(bivectorExteriorEquivQuadraticLieSubalgebra Q).map_add]
        -- Expose addition after coercing quadratic elements into the Clifford algebra.
        change ⁅(↑(bivectorExteriorEquivQuadraticLieSubalgebra Q a) :
            CliffordAlgebra Q) +
          ↑(bivectorExteriorEquivQuadraticLieSubalgebra Q b), ι Q y⁆ = _
        simp only [Ring.lie_def, add_mul, mul_add]
        abel
      map_smul' := by
        intro c a
        rw [(bivectorExteriorEquivQuadraticLieSubalgebra Q).map_smul]
        -- Expose scalar multiplication after the same Clifford-algebra coercion.
        change ⁅c • (↑(bivectorExteriorEquivQuadraticLieSubalgebra Q a) :
          CliffordAlgebra Q), ι Q y⁆ = _
        simp only [Ring.lie_def, smul_sub, smul_mul_assoc, mul_smul_comm]
        rfl }
  -- Replace the two local linear-map wrappers by their pointwise equality.
  change lhs x = rhs x
  apply LinearMap.congr_fun
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  -- Expose the local quadratic form and the decomposable exterior generator.
  change ι Q
      ((((standardBivectorToSoLinear n R (exteriorPower.ιMulti R 2 ![u 0, u 1]) :
        LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ y)) = _
  rw [standardBivectorToSoLinear_mulVec, map_sub, map_smul, map_smul]
  -- Expose the quadratic-subalgebra coercion before applying its public equation.
  change _ =
    ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q
        (exteriorPower.ιMulti R 2 ![u 0, u 1]) :
      quadraticLieSubalgebra Q) : CliffordAlgebra Q), ι Q y⁆
  rw [coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply,
    bivectorExterior_apply_ιMulti, bivector_lie_ι]
  have hpolar (a b : Fin n → R) : QuadraticMap.polar Q a b =
      2 * ∑ i, a i * b i := by
    -- Expose the local standard form so its named polar-form equation applies.
    change QuadraticMap.polar (QuadraticMap.weightedSumSquares R (1 : Fin n → R)) a b = _
    rw [← QuadraticMap.polarBilin_apply_apply,
      QuadraticForm.polarBilin_weightedSumSquares_one]
    simp [Matrix.toLinearMap₂'_apply, Matrix.one_apply]
  rw [hpolar, hpolar, map_sub, map_smul, map_smul]

private noncomputable def standardQuadraticToSoLinearEquiv :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    quadraticLieSubalgebra Q ≃ₗ[R] LieAlgebra.Orthogonal.so (Fin n) R :=
  (bivectorExteriorEquivQuadraticLieSubalgebra
      (QuadraticMap.weightedSumSquares R (1 : Fin n → R))).symm.trans
    (standardBivectorLinearEquiv n R)

private theorem standardQuadraticToSoLinearEquiv_map_lie
    (a b : quadraticLieSubalgebra
      (QuadraticMap.weightedSumSquares R (1 : Fin n → R))) :
    standardQuadraticToSoLinearEquiv n R ⁅a, b⁆ =
      ⁅standardQuadraticToSoLinearEquiv n R a,
        standardQuadraticToSoLinearEquiv n R b⁆ := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let e := bivectorExteriorEquivQuadraticLieSubalgebra Q
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext z
  apply ι_injective Q
  -- Expose matrix action beneath the faithful Clifford generator map.
  change ι Q
      ((↑(standardBivectorToSoLinear n R (e.symm ⁅a, b⁆)) :
        Matrix (Fin n) (Fin n) R) *ᵥ z) = _
  rw [ι_standardBivectorToSoLinear_mulVec]
  -- Expose the transported equivalence beneath the Clifford-algebra coercion.
  change ⁅(↑(e (e.symm ⁅a, b⁆)) : CliffordAlgebra Q), ι Q z⁆ = _
  rw [e.apply_symm_apply]
  symm
  -- Expose the matrix commutator action beneath the orthogonal-subalgebra coercion.
  change ι Q
      ((↑(⁅standardBivectorToSoLinear n R (e.symm a),
        standardBivectorToSoLinear n R (e.symm b)⁆ :
          LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ z) = _
  rw [LieSubalgebra.coe_bracket]
  simp only [Ring.lie_def, Matrix.sub_mulVec]
  rw [map_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [ι_standardBivectorToSoLinear_mulVec n R (e.symm a)
    ((↑(standardBivectorToSoLinear n R (e.symm b)) : Matrix (Fin n) (Fin n) R) *ᵥ z)]
  rw [ι_standardBivectorToSoLinear_mulVec n R (e.symm b)
    ((↑(standardBivectorToSoLinear n R (e.symm a)) : Matrix (Fin n) (Fin n) R) *ᵥ z)]
  rw [ι_standardBivectorToSoLinear_mulVec n R (e.symm b) z,
    ι_standardBivectorToSoLinear_mulVec n R (e.symm a) z]
  -- Expose the nested brackets after coercing quadratic elements to the ambient algebra.
  change ⁅(↑(e (e.symm a)) : CliffordAlgebra Q),
      ⁅(↑(e (e.symm b)) : CliffordAlgebra Q), ι Q z⁆⁆ -
    ⁅(↑(e (e.symm b)) : CliffordAlgebra Q),
      ⁅(↑(e (e.symm a)) : CliffordAlgebra Q), ι Q z⁆⁆ = _
  -- Expose the ambient representative of the quadratic-subalgebra bracket.
  change _ = ⁅(↑⁅a, b⁆ : CliffordAlgebra Q), ι Q z⁆
  rw [e.apply_symm_apply, e.apply_symm_apply]
  rw [← lie_lie, LieSubalgebra.coe_bracket]

private noncomputable def standardQuadraticToSoLieEquiv :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    quadraticLieSubalgebra Q ≃ₗ⁅R⁆ LieAlgebra.Orthogonal.so (Fin n) R := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let e := standardQuadraticToSoLinearEquiv n R
  exact LieEquiv.mk
    { toLinearMap := e.toLinearMap
      map_lie' := fun {a b} => standardQuadraticToSoLinearEquiv_map_lie n R a b }
    e.symm
    e.symm_apply_apply
    e.apply_symm_apply

/-- The second exterior power of the standard quadratic module is the matrix orthogonal Lie
algebra. The Lie structure on the exterior power is the one transported from quadratic Clifford
elements for the standard sum-of-squares form. -/
noncomputable def bivectorEquivSo :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    ⋀[R]^2 (Fin n → R) ≃ₗ⁅R⁆ LieAlgebra.Orthogonal.so (Fin n) R := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  exact (bivectorLieEquiv Q).trans (standardQuadraticToSoLieEquiv n R)

private theorem bivectorEquivSo_apply (x : ⋀[R]^2 (Fin n → R)) :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    bivectorEquivSo n R x = standardBivectorToSoLinear n R x := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  rw [bivectorEquivSo]
  -- Expose the two constituent equivalences in the transported Lie equivalence.
  change standardBivectorToSoLinear n R
      ((bivectorExteriorEquivQuadraticLieSubalgebra Q).symm
        (bivectorLieEquiv Q x)) = _
  rw [bivectorLieEquiv_apply, LinearEquiv.symm_apply_apply]

/-- On a decomposable bivector, `bivectorEquivSo` is the normalized skew matrix
`2 * (u vᵀ - v uᵀ)`. -/
@[simp]
theorem bivectorEquivSo_apply_ιMulti (u v : Fin n → R) :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    ((bivectorEquivSo n R (exteriorPower.ιMulti R 2 ![u, v]) :
      LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      fun i j => 2 * (u i * v j - v i * u j) := by
  rw [bivectorEquivSo_apply]
  exact standardBivectorToSoLinear_apply_ιMulti n R u v

/-- The inverse of `bivectorEquivSo` reads `⅟ 2` times an upper-triangular matrix entry as the
corresponding coefficient in the standard exterior basis. -/
@[simp]
theorem bivectorEquivSo_symm_repr_apply (A : LieAlgebra.Orthogonal.so (Fin n) R)
    (s : Set.powersetCard (Fin n) 2) :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    ((Pi.basisFun R (Fin n)).exteriorPower 2).repr ((bivectorEquivSo n R).symm A) s =
      let e := Set.powersetCard.ofFinEmbEquiv.symm s
      (⅟ (2 : R)) * (A : Matrix (Fin n) (Fin n) R) (e 0) (e 1) := by
  let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
  let _ := bivectorLieRing Q
  let _ := bivectorLieAlgebra Q
  have hsymm : (bivectorEquivSo n R).symm A = soToExteriorLinear n R A := by
    apply (bivectorEquivSo n R).injective
    calc
      (bivectorEquivSo n R) ((bivectorEquivSo n R).symm A) = A :=
        (bivectorEquivSo n R).apply_symm_apply A
      _ = standardBivectorToSoLinear n R (soToExteriorLinear n R A) :=
        (standardBivectorToSoLinear_soToExteriorLinear n R A).symm
      _ = (bivectorEquivSo n R) (soToExteriorLinear n R A) :=
        (bivectorEquivSo_apply n R (soToExteriorLinear n R A)).symm
  rw [hsymm]
  -- Expose the basis equivalence inside the coordinate-map composition before its inverse law.
  change (exteriorBasis n R).equivFun
      ((exteriorBasis n R).equivFun.symm (soCoordinates n R A)) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The standard exterior bivector `u ∧ v` acts on a vector by the polar-form-normalized
infinitesimal rotation. -/
theorem bivectorEquivSo_apply_ιMulti_mulVec (u v x : Fin n → R) :
    let Q := QuadraticMap.weightedSumSquares R (1 : Fin n → R)
    letI := bivectorLieRing Q
    letI := bivectorLieAlgebra Q
    (((bivectorEquivSo n R (exteriorPower.ιMulti R 2 ![u, v]) :
      LieAlgebra.Orthogonal.so (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x) =
      (2 * ∑ i, v i * x i) • u - (2 * ∑ i, u i * x i) • v := by
  rw [bivectorEquivSo_apply]
  exact standardBivectorToSoLinear_mulVec n R u v x

end CliffordAlgebra
