/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The admissible lattice in the type-E6 minuscule representation

This file extends the integral `27`-dimensional minuscule representation of the type-`E₆` Serre
presentation to the rational Serre algebra and proves that its coordinate `ℤ`-lattice is
preserved by the Serre Kostant form. The raising and lowering matrices have entries in `ℤ`, are
square-zero, and preserve the coordinate lattice. The Cartan matrices act diagonally with the
integral weights `TauCeti.DynkinType.e6MinusculeWeight`.

Thus the minuscule coordinate lattice is an admissible lattice for the explicit Serre-generator
Kostant form. Its weights already span the full type-`E₆` character lattice by
`TauCeti.DynkinType.span_range_e6MinusculeWeight_eq_top`. Together, these are the lattice inputs
needed to construct the full-weight type-`E₆` Chevalley--Demazure carrier in Layer 9 of the
ReductiveGroups roadmap.

## Main declarations

* `TauCeti.E6Minuscule.rationalSerreRepresentation`: the rational minuscule representation.
* `TauCeti.E6Minuscule.rep`: its extension to the universal enveloping algebra.
* `TauCeti.E6Minuscule.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.E6Minuscule.rep_serreKostantForm_mem_lattice`: the Serre Kostant form preserves the
  lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Extension from the integral representation -/

/-- Entrywise coercion from integral to rational matrices, as a homomorphism of Lie rings. -/
private noncomputable def castMatrixLieHom :
    Matrix (Fin 27) (Fin 27) ℤ →ₗ⁅ℤ⁆ Matrix (Fin 27) (Fin 27) ℚ :=
  ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom).toLieHom

@[simp]
private theorem castMatrixLieHom_apply (M : Matrix (Fin 27) (Fin 27) ℤ) (a b : Fin 27) :
    castMatrixLieHom M a b = (M a b : ℚ) := by
  simp only [castMatrixLieHom, AlgHom.toLieHom_apply, RingHom.toIntAlgHom_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]

/-- The rational raising matrix obtained from the integral minuscule representation. -/
noncomputable def raisingMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  castMatrixLieHom (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral minuscule representation. -/
noncomputable def loweringMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  castMatrixLieHom (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral minuscule representation. -/
noncomputable def cartanGeneratorMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  castMatrixLieHom (cartanGeneratorMatrix i)

/-- The entries of a rational raising matrix are the same zero-one coefficients as those of the
integral raising matrix. -/
@[simp]
theorem raisingMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    raisingMatrixQ i a b =
      if e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b then 1 else 0 := by
  rw [raisingMatrixQ, castMatrixLieHom_apply, raisingMatrix_apply]
  split_ifs <;> norm_num

/-- The entries of a rational lowering matrix are the same zero-one coefficients as those of the
integral lowering matrix. -/
@[simp]
theorem loweringMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    loweringMatrixQ i a b =
      if e6MinusculeWeight b i = 1 ∧ a = e6MinusculeReflection i b then 1 else 0 := by
  rw [loweringMatrixQ, castMatrixLieHom_apply, loweringMatrix_apply]
  split_ifs <;> norm_num

/-- The rational Cartan generator is diagonal with the minuscule weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    cartanGeneratorMatrixQ i a b =
      if a = b then (e6MinusculeWeight b i : ℚ) else 0 := by
  rw [cartanGeneratorMatrixQ, castMatrixLieHom_apply, cartanGeneratorMatrix_apply]
  split_ifs <;> norm_num

/-- Restricting scalars from `ℚ` to `ℤ` does not change the adjoint action on rational matrices. -/
private theorem ad_int_apply_eq_rat (x y : Matrix (Fin 27) (Fin 27) ℚ) :
    (LieAlgebra.ad ℤ _ x) y = (LieAlgebra.ad ℚ _ x) y := by
  simp only [LieAlgebra.ad_apply]

private theorem ad_pow_int_eq_rat (x y : Matrix (Fin 27) (Fin 27) ℚ) (n : ℕ) :
    (LieAlgebra.ad ℤ _ x ^ n) y = (LieAlgebra.ad ℚ _ x ^ n) y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        ad_int_apply_eq_rat]
      exact ih ((LieAlgebra.ad ℚ _ x) y)

/-- The rational minuscule matrices satisfy the type-`E₆` Serre relations. -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrixQ raisingMatrixQ
      loweringMatrixQ where
  lie_H_H i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_H i j)
    simpa only [LieHom.map_lie, map_zero, cartanGeneratorMatrixQ] using h
  lie_E_F_self i := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_E_F_self i)
    simpa only [LieHom.map_lie, raisingMatrixQ, loweringMatrixQ,
      cartanGeneratorMatrixQ] using h
  lie_E_F_of_ne i j hij := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_E_F_of_ne i j hij)
    simpa only [LieHom.map_lie, map_zero, raisingMatrixQ, loweringMatrixQ] using h
  lie_H_E i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_E i j)
    rw [LieHom.map_lie, map_zsmul] at h
    simpa only [cartanGeneratorMatrixQ, raisingMatrixQ, Int.cast_smul_eq_zsmul] using h
  lie_H_F i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.lie_H_F i j)
    rw [LieHom.map_lie, map_neg, map_zsmul] at h
    simpa only [cartanGeneratorMatrixQ, loweringMatrixQ, Int.cast_smul_eq_zsmul] using h
  ad_pow_lie_E_E i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.ad_pow_lie_E_E i j)
    rw [TauCeti.LieHom.map_ad_pow, map_zero] at h
    rw [← ad_pow_int_eq_rat]
    simpa only [LieHom.map_lie, raisingMatrixQ] using h
  ad_pow_lie_F_F i j := by
    have h := congrArg castMatrixLieHom (isSerreSystem.ad_pow_lie_F_F i j)
    rw [TauCeti.LieHom.map_ad_pow, map_zero] at h
    rw [← ad_pow_int_eq_rat]
    simpa only [LieHom.map_lie, loweringMatrixQ] using h

/-- The rational `27`-dimensional minuscule representation of the type-`E₆` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ →ₗ⁅ℚ⁆ Matrix (Fin 27) (Fin 27) ℚ :=
  TauCeti.serreLift isSerreSystemQ

/-- The rational representation sends each Cartan Serre generator to its diagonal minuscule
matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ i) =
      cartanGeneratorMatrixQ i :=
  TauCeti.serreLift_serreH isSerreSystemQ i

/-- The rational representation sends each positive Serre generator to its raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 6)ᵀ i) = raisingMatrixQ i :=
  TauCeti.serreLift_serreE isSerreSystemQ i

/-- The rational representation sends each negative Serre generator to its lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.E 6)ᵀ i) = loweringMatrixQ i :=
  TauCeti.serreLift_serreF isSerreSystemQ i

/-! ## The enveloping-algebra representation -/

/-- The rational minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) →ₐ[ℚ]
      Module.End ℚ (Fin 27 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv (Pi.basisFun ℚ (Fin 27))).toAlgHom.toLieHom.comp
      rationalSerreRepresentation)

/-- The enveloping-algebra representation acts on an included Lie element by matrix-vector
multiplication. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) (v : Fin 27 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  rw [rep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv_apply]
  exact (Pi.basisFun ℚ (Fin 27)).sum_repr (rationalSerreRepresentation x *ᵥ v)

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_sq (i : Fin 6) : raisingMatrixQ i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, raisingMatrixQ_apply, Matrix.zero_apply]
  by_cases hb : e6MinusculeWeight b i = -1
  · simp [hb, e6MinusculeWeight_reflection_apply_self]
  · simp [hb]

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_sq (i : Fin 6) : loweringMatrixQ i ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, loweringMatrixQ_apply, Matrix.zero_apply]
  by_cases hb : e6MinusculeWeight b i = 1
  · simp [hb, e6MinusculeWeight_reflection_apply_self]
  · simp [hb]

private theorem mulVec_sq_eq_zero (M : Matrix (Fin 27) (Fin 27) ℚ) (hM : M ^ 2 = 0)
    (v : Fin 27 → ℚ) : M *ᵥ M *ᵥ v = 0 := by
  rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]

/-- Every represented positive or negative Serre root generator is square-zero. -/
theorem rep_serreRootGenerator_sq (k : Fin 6 ⊕ Fin 6) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  rw [pow_two, Module.End.mul_apply]
  cases k with
  | inl i =>
      simpa only [TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE, LinearMap.zero_apply] using
        mulVec_sq_eq_zero (raisingMatrixQ i) (raisingMatrixQ_sq i) v
  | inr i =>
      simpa only [TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF, LinearMap.zero_apply] using
        mulVec_sq_eq_zero (loweringMatrixQ i) (loweringMatrixQ_sq i) v

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 6 ⊕ Fin 6) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))) :=
  ⟨2, rep_serreRootGenerator_sq k⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational minuscule module. -/
def lattice : Submodule ℤ (Fin 27 → ℚ) :=
  TauCeti.coordinateLattice (Fin 27)

/-- A minuscule-module vector belongs to the lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 27 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 27)

/-- Every standard coordinate vector belongs to the minuscule lattice. -/
theorem single_mem_lattice (a : Fin 27) : Pi.single a (1 : ℚ) ∈ lattice := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin 27) a

/-- The coordinate basis of the minuscule lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 27) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 27)

/-- Coercing a minuscule lattice-basis vector to the rational module gives the corresponding
coordinate vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 27) :
    ((latticeBasis a : lattice) : Fin 27 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 27) a

private theorem castMatrix_mulVec_mem_lattice (M : Matrix (Fin 27) (Fin 27) ℤ)
    {v : Fin 27 → ℚ} (hv : v ∈ lattice) : castMatrixLieHom M *ᵥ v ∈ lattice := by
  rw [mem_lattice_iff] at hv ⊢
  choose z hz using hv
  intro a
  refine ⟨∑ b, M a b * z b, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, hz, Matrix.mulVec, dotProduct,
    castMatrixLieHom_apply]

/-- Every represented Serre root generator preserves the minuscule coordinate lattice. -/
theorem rep_serreRootGenerator_mem_lattice (k : Fin 6 ⊕ Fin 6) {v : Fin 27 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) v ∈ lattice := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE,
        raisingMatrixQ]
      exact castMatrix_mulVec_mem_lattice (raisingMatrix i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF,
        loweringMatrixQ]
      exact castMatrix_mulVec_mem_lattice (loweringMatrix i) hv

/-- Each standard coordinate vector is a Cartan weight vector with its minuscule weight. -/
theorem isCartanWeightVector_single (a : Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6MinusculeWeight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep).mpr fun i ↦ ?_
  rw [rep_ι_apply, rationalSerreRepresentation_serreH]
  ext b
  simp [Matrix.mulVec, dotProduct, cartanGeneratorMatrixQ_apply, Pi.single_apply]

/-- Every minuscule lattice-basis vector is a Cartan weight vector with its minuscule weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6MinusculeWeight a)
      ((latticeBasis a : lattice) : Fin 27 → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The minuscule coordinate lattice is admissible for the type-`E₆` Serre Kostant form.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ)}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.E 6)ᵀ) {v : Fin 27 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep
    (wt := e6MinusculeWeight) rep_serreRootGenerator_sq
    (fun k _ hw ↦ rep_serreRootGenerator_mem_lattice k hw) isCartanWeightVector_single hu hv

end TauCeti.E6Minuscule
