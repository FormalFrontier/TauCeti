/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme

/-!
# The full-weight type-C carrier preserves the standard alternating form

`TauCeti.SpStd.groupScheme n` is the explicit full-weight Chevalley carrier of type `C_(n+1)`: the
smallest closed subgroup scheme of `GL_(2n+2)` containing the divided-power exponentials of the
Bourbaki-numbered Chevalley generators of `sp_(2n+2)` together with the weight torus of the
standard lattice. This file proves that it sits inside the symplectic group scheme
`TauCeti.Symplectic.groupScheme`, the subgroup scheme of `GL_(2n+2)` cut out by `X J Xᵀ = J`.

The proof is the two generator computations the toral-closure construction reduces to. A root
generator squares to zero in the standard representation, so its divided-power exponential is
`1 + t X` for `X` the integral matrix `TauCeti.SpStd.rootIntMatrix` of the generator itself; that
matrix is skew-adjoint for `J` because the generator lies in Mathlib's `LieAlgebra.Symplectic.sp`,
and `(1 + t X) J (1 + t X)ᵀ = J` follows from skew-adjointness together with `X ^ 2 = 0`. The weight
torus contributes a diagonal matrix whose entries at a coordinate and at its symplectic partner are
inverse characters, because the standard weights come in the pairs `ε_a` and `-ε_a`, and a diagonal
matrix preserves `J` exactly when each such pair multiplies to one.

The reverse inclusion is not proved: identifying the carrier with `Sp_(2n+2)` needs a generation
theorem, as in the type-`A` case, and none is asserted here. Nothing below claims that the carrier
is reductive, that its weight torus is maximal, or that any group in sight is finite or simple.

## Main definitions

* `TauCeti.SpStd.rootIntMatrix`: the integral matrix of a numbered root generator in the
  enumerated coordinate basis of the standard lattice.
* `TauCeti.SpStd.toSymplectic`: the canonical closed immersion from the carrier to `Sp_(2n+2)`.

## Main results

* `TauCeti.SpStd.rep_rootGenerator_latticeBasis_eq_sum` and
  `TauCeti.SpStd.map_rootIntMatrix`: that matrix is the matrix of the root generator, on the
  lattice and after extending scalars to `ℚ`.
* `TauCeti.SpStd.rootIntMatrix_map_mul_JFin_add_eq_zero` and
  `TauCeti.SpStd.rootIntMatrix_map_mul_self_eq_zero`: it is skew-adjoint for the transported
  alternating form, and squares to zero, over every value ring.
* `TauCeti.SpStd.symplecticDefiningHopfIdeal_le_definingIdeal`: the symplectic relations belong to
  the defining Hopf ideal of the carrier.
* `TauCeti.SpStd.mem_GLSymplecticFin_of_mem_points`: every matrix point of the carrier preserves
  the standard alternating form.
* `TauCeti.SpStd.toSymplectic_comp_inclusion`: composing with `Sp_(2n+2) → GL_(2n+2)` recovers the
  carrier inclusion.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.

The file follows the type-`A` counterpart
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/DeterminantOne.lean`, which proves the same
containment for the special linear group; the class-two exponential computation and the symplectic
matrix identities are specific to this file.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: the full-weight type `C` carrier is now proved to lie
in the expected pinned ambient group. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, which needs a simply connected pinned carrier for the
`C_n(q)` family.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.SpStd

open LieAlgebra.Symplectic

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

universe v

variable (n : ℕ)

/-- The integral matrix of a numbered root generator in the enumerated coordinate basis of the
standard lattice. Its columns are the coefficients of the images of the basis vectors, which are
integral because the generator preserves the lattice. -/
noncomputable def rootIntMatrix (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) ℤ :=
  (latticeBasis n).toMatrix fun s =>
    ⟨rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) (latticeBasis n s),
      rep_rootGenerator_mem_lattice n k (latticeBasis n s).2⟩

/-- A numbered root generator acts on a coordinate basis vector by the corresponding column of
`TauCeti.SpStd.rootIntMatrix`. -/
theorem rep_rootGenerator_latticeBasis_eq_sum (k : Fin (n + 1) ⊕ Fin (n + 1))
    (s : Fin ((n + 1) + (n + 1))) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))
        ((latticeBasis n s : (lattice n).toAddSubgroup) : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) =
      ∑ r, rootIntMatrix n k r s •
        ((latticeBasis n r : (lattice n).toAddSubgroup) :
          (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  have h := ((latticeBasis n).sum_toMatrix_smul_self
    (fun s => (⟨rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))
        (latticeBasis n s),
      rep_rootGenerator_mem_lattice n k (latticeBasis n s).2⟩ :
        (lattice n).toAddSubgroup)) s).symm
  have h' := congrArg
    (fun w : (lattice n).toAddSubgroup => (w : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ)) h
  simp only [AddSubmonoidClass.coe_finsetSum] at h'
  exact h'

/-- Extending an entry of `TauCeti.SpStd.rootIntMatrix` to `ℚ` recovers the corresponding entry of
the rational matrix of the root generator, at the standard indices enumerated by the coordinate
basis. -/
theorem intCast_rootIntMatrix (k : Fin (n + 1) ⊕ Fin (n + 1))
    (r s : Fin ((n + 1) + (n + 1))) :
    ((rootIntMatrix n k r s : ℤ) : ℚ) =
      (rootGenerator n k :
        Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ)
        (finSumFinEquiv.symm r) (finSumFinEquiv.symm s) := by
  rw [rootIntMatrix, Module.Basis.toMatrix_apply, intCast_latticeBasis_repr]
  -- Reduce the coercion of the anonymous constructor before rewriting under it.
  dsimp only
  rw [rep_ι_apply, coe_latticeBasis]
  simp [Matrix.mulVec_single]

/-- `TauCeti.SpStd.rootIntMatrix` is the reindexed rational matrix of the root generator. -/
theorem map_rootIntMatrix (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootIntMatrix n k).map (Int.cast : ℤ → ℚ) =
      (rootGenerator n k :
          Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext r s
  rw [Matrix.map_apply, Matrix.submatrix_apply, intCast_rootIntMatrix]

/-! ### Skew-adjointness and squaring to zero, over ℤ -/

private theorem mul_J_add_J_mul_transpose_eq_zero_of_mem_sp {l : Type*} [DecidableEq l]
    [Fintype l] {R : Type*} [CommRing R] {G : Matrix (l ⊕ l) (l ⊕ l) R}
    (hG : G ∈ sp l R) :
    G * Matrix.J l R + Matrix.J l R * Gᵀ = 0 := by
  rw [sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at hG
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_neg] at hG
  have hJ : Matrix.J l R * Matrix.J l R = -1 := Matrix.J_squared _ _
  have h1 : Matrix.J l R * Gᵀ * Matrix.J l R = G := by
    rw [Matrix.mul_assoc, hG, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.neg_mul,
      Matrix.one_mul, neg_neg]
  have h2 : G * Matrix.J l R = -(Matrix.J l R * Gᵀ) := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one]
  rw [h2, neg_add_cancel]

private theorem rootIntMatrix_mul_JFin_add_eq_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootIntMatrix n k * TauCeti.JFin (n + 1) ℤ +
      TauCeti.JFin (n + 1) ℤ * (rootIntMatrix n k)ᵀ = 0 := by
  have key := mul_J_add_J_mul_transpose_eq_zero_of_mem_sp (rootGenerator n k).2
  have hJ : TauCeti.JFin (n + 1) ℚ =
      (Matrix.J (Fin (n + 1)) ℚ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← TauCeti.JFin_submatrix (n + 1) (R := ℚ), Matrix.submatrix_submatrix]
    simp
  refine Matrix.map_injective (f := ((Int.castRingHom ℚ : ℤ →+* ℚ) : ℤ → ℚ))
    Int.cast_injective ?_
  simp only [Matrix.map_zero _ (map_zero (Int.castRingHom ℚ))]
  rw [← RingHom.mapMatrix_apply, map_add, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply]
  rw [TauCeti.JFin_map (n + 1) (Int.castRingHom ℚ)]
  simp only [Int.coe_castRingHom]
  rw [Matrix.transpose_map, map_rootIntMatrix, hJ, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  ext r c
  have h := congrFun (congrFun key (finSumFinEquiv.symm r)) (finSumFinEquiv.symm c)
  simpa using h

private theorem rootIntMatrix_mul_self_eq_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootIntMatrix n k * rootIntMatrix n k = 0 := by
  have hsq := pow_two_rep_rootGenerator_eq_zero n k
  have hG : (rootGenerator n k :
      Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) *
      (rootGenerator n k : Matrix _ _ ℚ) = 0 := by
    ext a b
    have h := DFunLike.congr_fun hsq (Pi.single b (1 : ℚ))
    rw [pow_two, Module.End.mul_apply, rep_ι_apply, rep_ι_apply,
      Matrix.mulVec_mulVec] at h
    simp only [LinearMap.zero_apply] at h
    have := congrFun h a
    simpa [Matrix.mulVec_single] using this
  refine Matrix.map_injective (f := ((Int.castRingHom ℚ : ℤ →+* ℚ) : ℤ → ℚ))
    Int.cast_injective ?_
  simp only [Matrix.map_zero _ (map_zero (Int.castRingHom ℚ))]
  rw [← RingHom.mapMatrix_apply, map_mul]
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom]
  rw [map_rootIntMatrix, Matrix.submatrix_mul_equiv, hG]
  simp

/-! ### The two generator matrices preserve the form -/

private theorem diagonal_mul_mul_transpose_diagonal {N : ℕ} {A : Type*} [CommRing A]
    (d : Fin N → A) (Jm : Matrix (Fin N) (Fin N) A)
    (hd : ∀ r c, d r * Jm r c * d c = Jm r c) :
    Matrix.diagonal d * Jm * (Matrix.diagonal d)ᵀ = Jm := by
  ext r c
  rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact hd r c

private theorem one_add_smul_mul_mul_transpose {N : ℕ} {A : Type*} [CommRing A]
    (Jm Y : Matrix (Fin N) (Fin N) A) (t : A)
    (hskew : Y * Jm + Jm * Yᵀ = 0) (hsq : Y * Y = 0) :
    (1 + t • Y) * Jm * (1 + t • Y)ᵀ = Jm := by
  have hYJ : Y * Jm = -(Jm * Yᵀ) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hskew
  have hcube : Y * Jm * Yᵀ = 0 := by
    rw [hYJ, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hsq,
      Matrix.transpose_zero, Matrix.mul_zero, neg_zero]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [hcube, smul_zero, add_zero, hYJ, smul_neg]
  abel

/-- **A numbered root generator is skew-adjoint for the transported alternating form**, over every
value ring: `X J + J Xᵀ = 0`. -/
theorem rootIntMatrix_map_mul_JFin_add_eq_zero {A : Type*} [CommRing A]
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootIntMatrix n k).map (Int.cast : ℤ → A) * TauCeti.JFin (n + 1) A +
      TauCeti.JFin (n + 1) A * ((rootIntMatrix n k).map (Int.cast : ℤ → A))ᵀ = 0 := by
  have h2 : ((rootIntMatrix n k * TauCeti.JFin (n + 1) ℤ +
      TauCeti.JFin (n + 1) ℤ * (rootIntMatrix n k)ᵀ).map (Int.castRingHom A)) = 0 := by
    rw [rootIntMatrix_mul_JFin_add_eq_zero]
    simp
  rw [← RingHom.mapMatrix_apply, map_add, map_mul, map_mul] at h2
  simp only [RingHom.mapMatrix_apply] at h2
  rw [Matrix.transpose_map, TauCeti.JFin_map (n + 1) (Int.castRingHom A)] at h2
  exact h2

/-- A numbered root generator squares to zero on the enumerated coordinate basis, over every value
ring. -/
theorem rootIntMatrix_map_mul_self_eq_zero {A : Type*} [CommRing A]
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootIntMatrix n k).map (Int.cast : ℤ → A) *
      (rootIntMatrix n k).map (Int.cast : ℤ → A) = 0 := by
  have h2 : ((rootIntMatrix n k * rootIntMatrix n k).map (Int.castRingHom A)) = 0 := by
    rw [rootIntMatrix_mul_self_eq_zero]
    simp
  rw [← RingHom.mapMatrix_apply, map_mul] at h2
  simp only [RingHom.mapMatrix_apply] at h2
  exact h2

open TauCeti.UniversalEnvelopingAlgebra
  (exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul) in
private theorem rootCoordinateMap_symplectic (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (GeneralLinear.genericMatrix ℤ ((n + 1) + (n + 1))).map
        (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator n)
          (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
          (isNilpotent_rep_rootGenerator n k) (latticeBasis n)).hom.toAlgHom *
        (TauCeti.JFin (n + 1) ℤ).map
          (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) *
        ((GeneralLinear.genericMatrix ℤ ((n + 1) + (n + 1))).map
          (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator n)
            (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
            (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
            (isNilpotent_rep_rootGenerator n k) (latticeBasis n)).hom.toAlgHom)ᵀ =
      (TauCeti.JFin (n + 1) ℤ).map
        (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) := by
  obtain ⟨t, ht⟩ :=
    exists_map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
      (isNilpotent_rep_rootGenerator n k) (latticeBasis n) (rootIntMatrix n k)
      (nilpotencyClass_rep_rootGenerator n k).le (rep_rootGenerator_latticeBasis_eq_sum n k)
  rw [ht, TauCeti.JFin_map (n + 1) (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))]
  exact one_add_smul_mul_mul_transpose _ _ _ (rootIntMatrix_map_mul_JFin_add_eq_zero n k)
    (rootIntMatrix_map_mul_self_eq_zero n k)

/-! ### The weight torus preserves the form -/

private theorem map_genericMatrix_weightTorusCoordinateMap :
    (GeneralLinear.genericMatrix ℤ ((n + 1) + (n + 1))).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (basisWeight n)).hom.toAlgHom =
      Matrix.diagonal fun a => MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (basisWeight n a))) 1 := by
  apply Matrix.ext
  intro a c
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply]
  simp only [BialgHom.coe_toAlgHom]
  rw [GeneralLinear.weightTorusCoordinateMap_X, Matrix.diagonal_apply]

/-- The weight at the symplectic partner of a coordinate is the negative of the weight at the
coordinate: the standard weights come in the pairs `ε_a` and `-ε_a`. -/
private theorem basisWeight_inr_eq_neg (x : Fin (n + 1)) :
    basisWeight n (finSumFinEquiv (Sum.inr x)) =
      -basisWeight n (finSumFinEquiv (Sum.inl x)) := by
  funext j
  rw [basisWeight_apply, basisWeight_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    weight_inr, Pi.neg_apply, weight_inl]

/-- The weight-torus characters at a coordinate and at its symplectic partner are inverse to
each other, because their weights sum to zero. -/
private theorem torusCharacter_mul_partner (x : Fin (n + 1)) :
    (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm
        (basisWeight n (finSumFinEquiv (Sum.inl x))))) (1 : ℤ)) *
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm
        (basisWeight n (finSumFinEquiv (Sum.inr x))))) (1 : ℤ)) = 1 := by
  rw [MonoidAlgebra.single_mul_single, mul_one, ← ofAdd_add]
  have hz : Finsupp.equivFunOnFinite.symm (basisWeight n (finSumFinEquiv (Sum.inl x))) +
      Finsupp.equivFunOnFinite.symm (basisWeight n (finSumFinEquiv (Sum.inr x))) = 0 := by
    rw [basisWeight_inr_eq_neg]
    ext j
    simp
  rw [hz]
  rfl

private theorem torusCoordinateMap_symplectic :
    (GeneralLinear.genericMatrix ℤ ((n + 1) + (n + 1))).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (basisWeight n)).hom.toAlgHom *
        (TauCeti.JFin (n + 1) ℤ).map
          (algebraMap ℤ
            (DiagonalizableGroup.coordinateRing ℤ
              (SplitTorus.characterGroup (Fin (n + 1)))).obj) *
        ((GeneralLinear.genericMatrix ℤ ((n + 1) + (n + 1))).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (basisWeight n)).hom.toAlgHom)ᵀ =
      (TauCeti.JFin (n + 1) ℤ).map
        (algebraMap ℤ
          (DiagonalizableGroup.coordinateRing ℤ
            (SplitTorus.characterGroup (Fin (n + 1)))).obj) := by
  rw [map_genericMatrix_weightTorusCoordinateMap,
    TauCeti.JFin_map (n + 1)
      (algebraMap ℤ
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin (n + 1)))).obj)]
  refine diagonal_mul_mul_transpose_diagonal _ _ ?_
  intro r c
  -- Name the two indices through the enumeration of the coordinate basis, so that the entry of
  -- the transported form is an entry of Mathlib's `Matrix.J`.
  obtain ⟨a, rfl⟩ : ∃ a, finSumFinEquiv a = r := ⟨finSumFinEquiv.symm r, by simp⟩
  obtain ⟨b, rfl⟩ : ∃ b, finSumFinEquiv b = c := ⟨finSumFinEquiv.symm c, by simp⟩
  have hJ := congrFun (congrFun (TauCeti.JFin_submatrix (n + 1)
    (R := (DiagonalizableGroup.coordinateRing ℤ
      (SplitTorus.characterGroup (Fin (n + 1)))).obj)) a) b
  rw [Matrix.submatrix_apply] at hJ
  rw [hJ]
  -- Only the two off-diagonal blocks contribute, and there only at a coordinate and its own
  -- symplectic partner, where the two characters multiply to one.
  cases a with
  | inl x =>
    cases b with
    | inl y => simp [Matrix.J]
    | inr y =>
      rcases eq_or_ne x y with rfl | hxy
      · simp only [Matrix.J, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.one_apply_eq,
          mul_neg, mul_one, neg_mul, neg_inj]
        exact torusCharacter_mul_partner n x
      · simp [Matrix.J, hxy]
  | inr x =>
    cases b with
    | inl y =>
      rcases eq_or_ne x y with rfl | hxy
      · simp only [Matrix.J, Matrix.fromBlocks_apply₂₁, Matrix.one_apply_eq, mul_one]
        rw [mul_comm]
        exact torusCharacter_mul_partner n x
      · simp [Matrix.J, hxy]
    | inr y => simp [Matrix.J]

/-! ### The carrier lies in the symplectic group scheme -/

/-- **The symplectic relations belong to the defining Hopf ideal of the full-weight type
`C_(n+1)` carrier.** Equivalently, every represented root subgroup and the represented weight torus
factor through `Sp_(2n+2)`. -/
theorem symplecticDefiningHopfIdeal_le_definingIdeal :
    Symplectic.definingHopfIdeal ℤ (n + 1) ≤ definingIdeal n := by
  rw [definingIdeal_def, TauCeti.UniversalEnvelopingAlgebra.le_kostantToralDefiningIdeal_iff]
  refine ⟨fun k => ?_, ?_⟩
  · exact ConstantForm.definingHopfIdeal_toIdeal_le_ker_of_map_genericMatrix_mul_mul_transpose
      ℤ _ _ _ (rootCoordinateMap_symplectic n k)
  · exact ConstantForm.definingHopfIdeal_toIdeal_le_ker_of_map_genericMatrix_mul_mul_transpose
      ℤ _ _ _ (torusCoordinateMap_symplectic n)

/-- Every matrix-valued point of the full-weight type `C_(n+1)` carrier preserves the standard
alternating form. -/
theorem mem_GLSymplecticFin_of_mem_points {A : Type v} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A} (hg : g ∈ points n A) :
    g ∈ TauCeti.GLSymplecticFin (n + 1) A := by
  rw [points_def] at hg
  have hsp := GeneralLinear.hopfIdealPointsSubgroup_le_of_le ((n + 1) + (n + 1))
    (symplecticDefiningHopfIdeal_le_definingIdeal n) A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hsp
  have hmem : ((GeneralLinear.pointsMulEquiv (R := ℤ) ((n + 1) + (n + 1))).symm g) ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (Symplectic.definingHopfIdeal ℤ (n + 1)) (CommAlgCat.of ℤ A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr hsp
  rw [ConstantForm.mem_definingPointsSubgroup_iff, TauCeti.JFin_map,
    MulEquiv.apply_symm_apply] at hmem
  rw [TauCeti.GLSymplecticFin.mem_iff]
  exact hmem

/-- The canonical morphism from the full-weight type `C_(n+1)` carrier to `Sp_(2n+2)`, induced by
the containment of defining Hopf ideals. -/
noncomputable def toSymplectic : groupScheme n ⟶ Symplectic.groupScheme ℤ (n + 1) :=
  CommHopfAlgCat.quotientSpecMapOfLe
    (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
    ((symplecticDefiningHopfIdeal_le_definingIdeal n).trans (le_of_eq (definingIdeal_def n)))

/-- The canonical morphism from the type `C_(n+1)` carrier to `Sp_(2n+2)` is a closed
immersion. -/
instance isClosedImmersion_toSymplectic :
    AlgebraicGeometry.IsClosedImmersion (toSymplectic n).hom.hom.left := by
  rw [toSymplectic]
  infer_instance

/-- Including the type `C_(n+1)` carrier into `Sp_(2n+2)` and then into `GL_(2n+2)` recovers its
original ambient closed immersion. -/
@[simp]
theorem toSymplectic_comp_inclusion :
    toSymplectic n ≫ Symplectic.inclusion ℤ (n + 1) = carrierι n := by
  rw [toSymplectic, Symplectic.inclusion_def, GeneralLinear.hopfIdealInclusion_def,
    carrierι_def, TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι_def,
    ← Category.assoc, CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]
  simp

end TauCeti.SpStd
