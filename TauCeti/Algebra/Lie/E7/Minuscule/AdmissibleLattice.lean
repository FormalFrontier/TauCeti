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
* `TauCeti.E7Minuscule.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.E7Minuscule.rep_serreKostantForm_mem_lattice`: the Serre Kostant form preserves the
  lattice.

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
    Matrix (Fin 56) (Fin 56) ℤ →ₗ⁅ℤ⁆ Matrix (Fin 56) (Fin 56) ℚ where
  toLinearMap := (Int.castRingHom ℚ).mapMatrix.toAddMonoidHom.toIntLinearMap
  map_lie' := by
    intro x y
    -- Expose the matrix commutator so the ring-homomorphism laws can rewrite each product.
    change (Int.castRingHom ℚ).mapMatrix (x * y - y * x) =
      (Int.castRingHom ℚ).mapMatrix x * (Int.castRingHom ℚ).mapMatrix y -
        (Int.castRingHom ℚ).mapMatrix y * (Int.castRingHom ℚ).mapMatrix x
    rw [map_sub, map_mul, map_mul]

@[simp]
private theorem castMatrixLieHom_apply (M : Matrix (Fin 56) (Fin 56) ℤ) (a b : Fin 56) :
    castMatrixLieHom M a b = (M a b : ℚ) := by
  rfl

/-- The rational raising matrix obtained from the integral minuscule representation. -/
noncomputable def raisingMatrixQ (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral minuscule representation. -/
noncomputable def loweringMatrixQ (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral minuscule representation. -/
noncomputable def cartanMatrixQ (i : Fin 7) : Matrix (Fin 56) (Fin 56) ℚ :=
  castMatrixLieHom (cartanMatrix i)

@[simp]
theorem raisingMatrixQ_apply (i : Fin 7) (a b : Fin 56) :
    raisingMatrixQ i a b =
      if e7MinusculeWeight b i = -1 ∧ a = e7MinusculeReflection i b then 1 else 0 := by
  rw [raisingMatrixQ, castMatrixLieHom_apply, raisingMatrix_apply]
  split_ifs <;> norm_num

@[simp]
theorem loweringMatrixQ_apply (i : Fin 7) (a b : Fin 56) :
    loweringMatrixQ i a b =
      if e7MinusculeWeight b i = 1 ∧ a = e7MinusculeReflection i b then 1 else 0 := by
  rw [loweringMatrixQ, castMatrixLieHom_apply, loweringMatrix_apply]
  split_ifs <;> norm_num

@[simp]
theorem cartanMatrixQ_apply (i : Fin 7) (a b : Fin 56) :
    cartanMatrixQ i a b = if a = b then (e7MinusculeWeight a i : ℚ) else 0 := by
  rw [cartanMatrixQ, castMatrixLieHom_apply, cartanMatrix_apply]
  split_ifs <;> norm_num

private theorem ad_pow_int_eq_rat (x y : Matrix (Fin 56) (Fin 56) ℚ) (n : ℕ) :
    (LieAlgebra.ad ℤ _ x ^ n) y = (LieAlgebra.ad ℚ _ x ^ n) y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply]
      exact ih ⁅x, y⁆

/-- The rational minuscule matrices satisfy the type-`E₇` Serre relations. -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.E 7) cartanMatrixQ raisingMatrixQ loweringMatrixQ where
  lie_H_H i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_H i j)
    simpa [cartanMatrixQ] using h
  lie_E_F_self i := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_E_F_self i)
    simpa [raisingMatrixQ, loweringMatrixQ, cartanMatrixQ] using h
  lie_E_F_of_ne i j hij := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_E_F_of_ne i j hij)
    simpa [raisingMatrixQ, loweringMatrixQ] using h
  lie_H_E i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_E i j)
    rw [LieHom.map_lie, map_zsmul] at h
    simpa only [cartanMatrixQ, raisingMatrixQ, Int.cast_smul_eq_zsmul] using h
  lie_H_F i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_F i j)
    rw [LieHom.map_lie, map_neg, map_zsmul] at h
    simpa only [cartanMatrixQ, loweringMatrixQ, Int.cast_smul_eq_zsmul] using h
  ad_pow_lie_E_E i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.ad_pow_lie_E_E i j)
    rw [TauCeti.LieHom.map_ad_pow, map_zero] at h
    rw [← ad_pow_int_eq_rat]
    simpa [raisingMatrixQ] using h
  ad_pow_lie_F_F i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.ad_pow_lie_F_F i j)
    rw [TauCeti.LieHom.map_ad_pow, map_zero] at h
    rw [← ad_pow_int_eq_rat]
    simpa [loweringMatrixQ] using h

/-- The rational `56`-dimensional minuscule representation of the type-`E₇` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7) →ₗ⁅ℚ⁆ Matrix (Fin 56) (Fin 56) ℚ :=
  TauCeti.serreLift isSerreSystemQ

@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.E 7) i) = cartanMatrixQ i :=
  TauCeti.serreLift_serreH isSerreSystemQ i

@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 7) i) = raisingMatrixQ i :=
  TauCeti.serreLift_serreE isSerreSystemQ i

@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 7) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.E 7) i) = loweringMatrixQ i :=
  TauCeti.serreLift_serreF isSerreSystemQ i

/-! ## The enveloping-algebra representation -/

/-- The rational minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7)) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv (Pi.basisFun ℚ (Fin 56))).toAlgHom.toLieHom.comp
      rationalSerreRepresentation)

theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7)) (v : Fin 56 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  rw [rep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv_apply]
  exact (Pi.basisFun ℚ (Fin 56)).sum_repr (rationalSerreRepresentation x *ᵥ v)

private theorem e7MinusculeWeight_reflection_apply_self (i : Fin 7) (a : Fin 56) :
    e7MinusculeWeight (e7MinusculeReflection i a) i = -e7MinusculeWeight a i := by
  have h := congrFun (e7MinusculeWeight_reflection i a) i
  rw [root_e7SimpleIndex] at h
  simp [CartanMatrix.E_diag] at h
  omega

/-- Every rational minuscule raising matrix squares to zero. -/
theorem raisingMatrixQ_sq (i : Fin 7) : raisingMatrixQ i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, raisingMatrixQ_apply, Matrix.zero_apply]
  by_cases hb : e7MinusculeWeight b i = -1
  · simp [hb, e7MinusculeWeight_reflection_apply_self]
  · simp [hb]

/-- Every rational minuscule lowering matrix squares to zero. -/
theorem loweringMatrixQ_sq (i : Fin 7) : loweringMatrixQ i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, loweringMatrixQ_apply, Matrix.zero_apply]
  by_cases hb : e7MinusculeWeight b i = 1
  · simp [hb, e7MinusculeWeight_reflection_apply_self]
  · simp [hb]

/-- Every simple-root generator acts with square zero in the rational minuscule
representation. -/
theorem pow_two_rep_serreRootGenerator_eq_zero (k : Fin 7 ⊕ Fin 7) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 7) k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  cases k with
  | inl i =>
      rw [pow_two, Module.End.mul_apply, rep_ι_apply, rep_ι_apply,
        TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE,
        Matrix.mulVec_mulVec, ← pow_two, raisingMatrixQ_sq, Matrix.zero_mulVec,
        LinearMap.zero_apply]
  | inr i =>
      rw [pow_two, Module.End.mul_apply, rep_ι_apply, rep_ι_apply,
        TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF,
        Matrix.mulVec_mulVec, ← pow_two, loweringMatrixQ_sq, Matrix.zero_mulVec,
        LinearMap.zero_apply]

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
theorem rep_serreRootGenerator_mem_lattice (k : Fin 7 ⊕ Fin 7) {v : Fin 56 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 7) k)) v ∈ lattice := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE, raisingMatrixQ]
      exact castMatrix_mulVec_mem_lattice (raisingMatrix i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF, loweringMatrixQ]
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
    simp [Matrix.mulVec, dotProduct, cartanMatrixQ_apply, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, cartanMatrixQ_apply, Pi.single_apply, h]

/-- **The minuscule coordinate lattice is admissible for the type-`E₇` Serre Kostant form.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 7))}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.E 7)) {v : Fin 56 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (TauCeti.serreRootGenerator (CartanMatrix.E 7))
    (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep
    (wt := e7MinusculeWeight) pow_two_rep_serreRootGenerator_eq_zero
    (fun k _ hw ↦ rep_serreRootGenerator_mem_lattice k hw) isCartanWeightVector_single hu hv

end TauCeti.E7Minuscule
