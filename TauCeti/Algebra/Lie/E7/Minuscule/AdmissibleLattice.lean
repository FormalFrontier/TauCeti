/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The admissible lattice in the type-E7 minuscule representation

This file extends the integral `56`-dimensional minuscule representation of the type-`E₇`
Serre presentation to the rational Serre algebra and proves that its coordinate `ℤ`-lattice is
preserved by the Serre Kostant form. The raising and lowering matrices have integral entries, are
square-zero, and preserve the coordinate lattice. The Cartan matrices act diagonally through the
weights `TauCeti.DynkinType.e7MinusculeWeight`.

Thus the minuscule coordinate lattice is an admissible lattice for the explicit Serre-generator
Kostant form. Its weights span the full type-`E₇` character lattice by
`TauCeti.DynkinType.span_range_e7MinusculeWeight_eq_top`. These are the lattice inputs needed for
the full-weight type-`E₇` Chevalley--Demazure carrier in Layer 9 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.E7Minuscule.rationalSerreRepresentation`: the rational minuscule representation.
* `TauCeti.E7Minuscule.rep`: its extension to the universal enveloping algebra.
* `TauCeti.E7Minuscule.isNilpotent_rep_serreRootGenerator`: the simple-root generators act
  nilpotently.
* `TauCeti.E7Minuscule.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.E7Minuscule.rep_serreKostantForm_apply_mem_lattice`: the Serre Kostant form preserves
  the lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13 and 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

The formal organization follows the parallel type-`E₆` admissible-lattice development in
TauCetiProject/TauCeti#5204, specialized here to the already constructed `E₇` minuscule Serre
system.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Extension from the integral representation -/

/-- Entrywise coercion from integral to rational matrices, as a homomorphism of Lie rings. -/
private noncomputable def castMatrixLieHom :
    Matrix (Fin 56) (Fin 56) ℤ →ₗ⁅ℤ⁆ Matrix (Fin 56) (Fin 56) ℚ :=
  ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom).toLieHom

@[simp]
private theorem castMatrixLieHom_apply (M : Matrix (Fin 56) (Fin 56) ℤ) (a b : Fin 56) :
    castMatrixLieHom M a b = (M a b : ℚ) := by
  simp only [castMatrixLieHom, AlgHom.toLieHom_apply, RingHom.toIntAlgHom_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]

@[simp]
private theorem castMatrixLieHom_mul (M N : Matrix (Fin 56) (Fin 56) ℤ) :
    castMatrixLieHom (M * N) = castMatrixLieHom M * castMatrixLieHom N := by
  exact map_mul ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom) M N

/-- The rational raising matrix obtained from the integral minuscule representation. -/
noncomputable def raisingMatrixRat (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral minuscule representation. -/
noncomputable def loweringMatrixRat (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral minuscule representation. -/
noncomputable def cartanMatrixRat (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (cartanMatrix i)

/-- The entries of the rational raising matrix are the integral minuscule raising coefficients. -/
@[simp]
theorem raisingMatrixRat_apply (i : Fin 7) (a b : Fin 56) :
    raisingMatrixRat i a b =
      if e7MinusculeWeight b i = -1 ∧ a = e7MinusculeReflection i b then 1 else 0 := by
  rw [raisingMatrixRat, castMatrixLieHom_apply, raisingMatrix_apply]
  split_ifs <;> norm_num

/-- The entries of the rational lowering matrix are the integral minuscule lowering coefficients. -/
@[simp]
theorem loweringMatrixRat_apply (i : Fin 7) (a b : Fin 56) :
    loweringMatrixRat i a b =
      if e7MinusculeWeight b i = 1 ∧ a = e7MinusculeReflection i b then 1 else 0 := by
  rw [loweringMatrixRat, castMatrixLieHom_apply, loweringMatrix_apply]
  split_ifs <;> norm_num

/-- The rational Cartan matrix is diagonal with the minuscule weights on its diagonal. -/
@[simp]
theorem cartanMatrixRat_apply (i : Fin 7) (a b : Fin 56) :
    cartanMatrixRat i a b = if a = b then (e7MinusculeWeight a i : ℚ) else 0 := by
  rw [cartanMatrixRat, castMatrixLieHom_apply, cartanMatrix_apply]
  split_ifs <;> norm_num

private theorem ad_pow_int_eq_rat (x y : Matrix (Fin 56) (Fin 56) ℚ) (n : ℕ) :
    (LieAlgebra.ad ℤ _ x ^ n) y = (LieAlgebra.ad ℚ _ x ^ n) y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]
      exact ih ⁅x, y⁆

private theorem cast_lie_eq_zero {x y : Matrix (Fin 56) (Fin 56) ℤ}
    (h : ⁅x, y⁆ = 0) : ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = 0 := by
  rw [← LieHom.map_lie, h, map_zero]

private theorem cast_lie_eq {x y z : Matrix (Fin 56) (Fin 56) ℤ}
    (h : ⁅x, y⁆ = z) : ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = castMatrixLieHom z := by
  rw [← LieHom.map_lie, h]

private theorem cast_lie_eq_smul {x y z : Matrix (Fin 56) (Fin 56) ℤ} (c : ℤ)
    (h : ⁅x, y⁆ = c • z) :
    ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = c • castMatrixLieHom z := by
  rw [← LieHom.map_lie, h, map_zsmul]

private theorem cast_lie_eq_neg_smul {x y z : Matrix (Fin 56) (Fin 56) ℤ} (c : ℤ)
    (h : ⁅x, y⁆ = -(c • z)) :
    ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = -(c • castMatrixLieHom z) := by
  rw [← LieHom.map_lie, h, map_neg, map_zsmul]

private theorem cast_ad_pow_lie_eq_zero {x y : Matrix (Fin 56) (Fin 56) ℤ} (n : ℕ)
    (h : (LieAlgebra.ad ℤ _ x ^ n) ⁅x, y⁆ = 0) :
    (LieAlgebra.ad ℚ _ (castMatrixLieHom x) ^ n)
      ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = 0 := by
  have h' := congrArg castMatrixLieHom h
  rw [TauCeti.LieHom.map_ad_pow, LieHom.map_lie, map_zero] at h'
  rw [← ad_pow_int_eq_rat]
  exact h'

/-- The rational minuscule matrices satisfy the type-`E₇` Serre relations. -/
theorem isSerreSystemRat :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.E 7)
      cartanMatrixRat raisingMatrixRat loweringMatrixRat where
  lie_H_H i j := by
    simpa only [cartanMatrixRat] using cast_lie_eq_zero (isSerreSystem.lie_H_H i j)
  lie_E_F_self i := by
    simpa only [raisingMatrixRat, loweringMatrixRat, cartanMatrixRat] using
      cast_lie_eq (isSerreSystem.lie_E_F_self i)
  lie_E_F_of_ne i j hij := by
    simpa only [raisingMatrixRat, loweringMatrixRat] using
      cast_lie_eq_zero (isSerreSystem.lie_E_F_of_ne i j hij)
  lie_H_E i j := by
    simpa only [cartanMatrixRat, raisingMatrixRat] using
      cast_lie_eq_smul (CartanMatrix.E 7 i j) (isSerreSystem.lie_H_E i j)
  lie_H_F i j := by
    simpa only [cartanMatrixRat, loweringMatrixRat] using
      cast_lie_eq_neg_smul (CartanMatrix.E 7 i j) (isSerreSystem.lie_H_F i j)
  ad_pow_lie_E_E i j := by
    simpa only [raisingMatrixRat] using
      cast_ad_pow_lie_eq_zero (-(CartanMatrix.E 7) i j).toNat
        (isSerreSystem.ad_pow_lie_E_E i j)
  ad_pow_lie_F_F i j := by
    simpa only [loweringMatrixRat] using
      cast_ad_pow_lie_eq_zero (-(CartanMatrix.E 7) i j).toNat
        (isSerreSystem.ad_pow_lie_F_F i j)

/-- The rational `56`-dimensional minuscule representation of the type-`E₇` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7) →ₗ⁅ℚ⁆ Matrix (Fin 56) (Fin 56) ℚ :=
  TauCeti.serreLift isSerreSystemRat

/-- The rational Serre representation sends `H_i` to the rational Cartan matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.E 7) i) = cartanMatrixRat i :=
  TauCeti.serreLift_serreH isSerreSystemRat i

/-- The rational Serre representation sends `E_i` to the rational raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 7) i) = raisingMatrixRat i :=
  TauCeti.serreLift_serreE isSerreSystemRat i

/-- The rational Serre representation sends `F_i` to the rational lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.E 7) i) = loweringMatrixRat i :=
  TauCeti.serreLift_serreF isSerreSystemRat i

/-! ## The enveloping-algebra representation -/

/-- The rational minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7)) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    (Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp
      rationalSerreRepresentation)

/-- The enveloping-algebra inclusion acts by multiplying with the represented matrix. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7)) (v : Fin 56 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  simp [rep]

private theorem castMatrixLieHom_pow_two_eq_zero (M : Matrix (Fin 56) (Fin 56) ℤ)
    (hM : M * M = 0) : castMatrixLieHom M ^ 2 = 0 := by
  rw [pow_two, ← castMatrixLieHom_mul, hM, map_zero]

/-- Every rational minuscule raising matrix squares to zero. -/
@[simp]
theorem raisingMatrixRat_pow_two (i : Fin 7) : raisingMatrixRat i ^ 2 = 0 := by
  exact castMatrixLieHom_pow_two_eq_zero (raisingMatrix i) (raisingMatrix_mul_self i)

/-- Every rational minuscule lowering matrix squares to zero. -/
@[simp]
theorem loweringMatrixRat_pow_two (i : Fin 7) : loweringMatrixRat i ^ 2 = 0 := by
  exact castMatrixLieHom_pow_two_eq_zero (loweringMatrix i) (loweringMatrix_mul_self i)

private theorem mulVec_pow_two_eq_zero (M : Matrix (Fin 56) (Fin 56) ℚ) (hM : M ^ 2 = 0)
    (v : Fin 56 → ℚ) : M *ᵥ M *ᵥ v = 0 := by
  rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]

/-- Every simple-root generator acts with square zero in the rational minuscule
representation. -/
theorem pow_two_rep_serreRootGenerator_eq_zero (k : Fin 7 ⊕ Fin 7) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 7) k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  rw [pow_two, Module.End.mul_apply]
  cases k with
  | inl i =>
      simpa only [TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE, LinearMap.zero_apply] using
        mulVec_pow_two_eq_zero (raisingMatrixRat i) (raisingMatrixRat_pow_two i) v
  | inr i =>
      simpa only [TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF, LinearMap.zero_apply] using
        mulVec_pow_two_eq_zero (loweringMatrixRat i) (loweringMatrixRat_pow_two i) v

/-- Every represented simple-root generator is nilpotent, with nilpotence index at most two. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 7 ⊕ Fin 7) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 7) k))) :=
  ⟨2, pow_two_rep_serreRootGenerator_eq_zero k⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational minuscule module. -/
def lattice : Submodule ℤ (Fin 56 → ℚ) :=
  TauCeti.coordinateLattice (Fin 56)

/-- A minuscule-module vector belongs to the lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 56 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 56)

/-- The coordinate basis of the minuscule lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 56) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 56)

/-- Coercing a lattice basis vector to the rational module gives the corresponding coordinate
vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 56) :
    ((latticeBasis a : lattice) : Fin 56 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 56) a

private theorem castMatrix_mulVec_mem_lattice (M : Matrix (Fin 56) (Fin 56) ℤ)
    {v : Fin 56 → ℚ} (hv : v ∈ lattice) : castMatrixLieHom M *ᵥ v ∈ lattice := by
  rw [mem_lattice_iff] at hv ⊢
  choose z hz using hv
  intro a
  refine ⟨∑ b, M a b * z b, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, hz, Matrix.mulVec, dotProduct,
    castMatrixLieHom_apply]

/-- Every simple-root generator preserves the minuscule coordinate lattice. -/
theorem rep_serreRootGenerator_apply_mem_lattice (k : Fin 7 ⊕ Fin 7) {v : Fin 56 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 7) k)) v ∈ lattice := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE, raisingMatrixRat]
      exact castMatrix_mulVec_mem_lattice (raisingMatrix i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF, loweringMatrixRat]
      exact castMatrix_mulVec_mem_lattice (loweringMatrix i) hv

/-- Each coordinate basis vector has the corresponding minuscule weight for the Cartan
generators. -/
theorem isCartanWeightVector_single (a : Fin 56) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep (e7MinusculeWeight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep).mpr fun i ↦ ?_
  rw [rep_ι_apply, rationalSerreRepresentation_serreH]
  ext b
  by_cases h : b = a
  · subst b
    simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply, h]

/-- **The minuscule coordinate lattice is admissible for the type-`E₇` Serre Kostant form.** -/
theorem rep_serreKostantForm_apply_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7))}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.E 7)) {v : Fin 56 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (TauCeti.serreRootGenerator (CartanMatrix.E 7))
    (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep
    (wt := e7MinusculeWeight) pow_two_rep_serreRootGenerator_eq_zero
    (fun k _ hw ↦ rep_serreRootGenerator_apply_mem_lattice k hw) isCartanWeightVector_single hu hv

end TauCeti.E7Minuscule
