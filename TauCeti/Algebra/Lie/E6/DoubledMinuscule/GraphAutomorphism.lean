/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry

/-!
# The graph automorphism of the doubled type-E6 minuscule carrier

The nontrivial symmetry of the Bourbaki-numbered `E₆` diagram exchanges the two minuscule
representations `V(ϖ₁)` and `V(ϖ₆)`. On their direct sum it has a signed monomial lift which
intertwines the represented positive and negative simple-root generators. This file constructs
that lift and descends it to the full-weight doubled minuscule carrier.

The resulting automorphism `TauCeti.E6DoubledMinuscule.graphAutomorphism` carries each numbered
root subgroup to the subgroup numbered by `TauCeti.DynkinType.graphPermE6`, without changing its
additive parameter, and relabels the represented split torus by the same diagram involution. It
has order dividing two.

No reductivity, maximality of the represented torus, or identification of the carrier's root datum
is asserted here.

## Main declarations

* `TauCeti.E6DoubledMinuscule.graphRootPerm`: the diagram involution on the positive and negative
  simple-root indices.
* `TauCeti.E6DoubledMinuscule.graphModuleEquiv`: its signed monomial lift to the doubled minuscule
  module.
* `TauCeti.E6DoubledMinuscule.graphAutomorphism`: the induced automorphism of the doubled carrier.
* `TauCeti.E6DoubledMinuscule.rootSubgroup_comp_graphAutomorphism_hom`: its pinned action on the
  numbered root subgroups.
* `TauCeti.E6DoubledMinuscule.weightTorus_comp_graphAutomorphism_hom`: its action on the split
  weight torus.
* `TauCeti.E6DoubledMinuscule.graphAutomorphism_hom_comp_self` and
  `TauCeti.E6DoubledMinuscule.graphAutomorphism_inv`: its order-two relation on the carrier.
* `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints`: the same automorphism on matrix-valued
  points.
* `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_rootSubgroupPoints` and
  `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_weightTorusPoints`: its pointwise pinning
  equations.
* `TauCeti.E6DoubledMinuscule.pointsMap_comp_graphAutomorphismPoints`: its naturality in the value
  ring, which makes it commute with Frobenius.
* `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_sq`: its pointwise order-two relation.
* `TauCeti.E6DoubledMinuscule.graphAutomorphismPoints_graphAutomorphismPoints`: the corresponding
  simp-normal pointwise involution.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra

universe v v'

attribute [local instance high] Algebra.toModule

/-! ## The signed symmetry of the doubled module -/

/-- The type-`E₆` diagram involution on both the positive and negative simple-root indices. -/
def graphRootPerm : Equiv.Perm (Fin 6 ⊕ Fin 6) :=
  Equiv.sumCongr graphPermE6 graphPermE6

@[simp]
theorem graphRootPerm_inl (i : Fin 6) : graphRootPerm (.inl i) = .inl (graphPermE6 i) :=
  by simp [graphRootPerm]

@[simp]
theorem graphRootPerm_inr (i : Fin 6) : graphRootPerm (.inr i) = .inr (graphPermE6 i) :=
  by simp [graphRootPerm]

@[simp]
theorem graphRootPerm_graphRootPerm (k : Fin 6 ⊕ Fin 6) :
    graphRootPerm (graphRootPerm k) = k := by
  cases k <;> simp only [graphRootPerm_inl, graphRootPerm_inr]
  all_goals rw [← Equiv.Perm.mul_apply, ← pow_two, graphPermE6_sq, Equiv.Perm.one_apply]

/-- The parity height used to orient the doubled minuscule weight graph. Its four coordinates are
invariant as a set under the type-`E₆` diagram involution, and every simple root has odd height. -/
private def basisHeight (a : Fin 27 ⊕ Fin 27) : ℤ :=
  e6DoubledMinusculeWeight a 1 + e6DoubledMinusculeWeight a 2 +
    e6DoubledMinusculeWeight a 3 + e6DoubledMinusculeWeight a 4

/-- The sign of a doubled minuscule basis vector, given by parity of its weight height. -/
def basisSign (a : Fin 27 ⊕ Fin 27) : ℤ :=
  (basisHeight a).negOnePow

@[simp]
theorem basisSign_sq (a : Fin 27 ⊕ Fin 27) : basisSign a * basisSign a = 1 := by
  exact congrArg Units.val (Int.units_mul_self (basisHeight a).negOnePow)

@[simp]
theorem basisSign_graphPerm (a : Fin 27 ⊕ Fin 27) :
    basisSign (e6DoubledMinusculeGraphPerm a) = basisSign a := by
  rw [basisSign, basisSign]
  congr 1
  simp only [basisHeight, e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm,
    graphPermE6_apply_one, graphPermE6_apply_two, graphPermE6_apply_three,
    graphPermE6_apply_four]
  ring_nf

private theorem doubledWeight_reflection (i : Fin 6) (a : Fin 27 ⊕ Fin 27) :
    e6DoubledMinusculeWeight (reflection i a) =
      e6DoubledMinusculeWeight a -
        e6DoubledMinusculeWeight a i • e6Root (e6SimpleIndex i) := by
  cases a with
  | inl a =>
      simpa only [reflection_inl, e6DoubledMinusculeWeight_inl] using
        e6MinusculeWeight_reflection i a
  | inr a =>
      rw [reflection_inr, e6DoubledMinusculeWeight_inr,
        e6MinusculeWeight_reflection]
      ext j
      simp only [e6DoubledMinusculeWeight_inr, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring_nf

private def simpleRootHeight (i : Fin 6) : ℤ :=
  e6Root (e6SimpleIndex i) 1 + e6Root (e6SimpleIndex i) 2 +
    e6Root (e6SimpleIndex i) 3 + e6Root (e6SimpleIndex i) 4

private theorem simpleRootHeight_odd (i : Fin 6) : Odd (simpleRootHeight i) := by
  fin_cases i <;> simp [simpleRootHeight, root_e6SimpleIndex, CartanMatrix.E_six_eq]

private theorem basisHeight_reflection (i : Fin 6) (a : Fin 27 ⊕ Fin 27) :
    basisHeight (reflection i a) =
      basisHeight a - e6DoubledMinusculeWeight a i * simpleRootHeight i := by
  rw [basisHeight, basisHeight, doubledWeight_reflection]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, simpleRootHeight]
  ring_nf

private theorem weight_odd_of_ne_zero (i : Fin 6) (a : Fin 27 ⊕ Fin 27)
    (ha : e6DoubledMinusculeWeight a i ≠ 0) :
    Odd (e6DoubledMinusculeWeight a i) := by
  cases a with
  | inl a =>
      simp only [e6DoubledMinusculeWeight_inl] at ha ⊢
      rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h <;>
        simp_all
  | inr a =>
      simp only [e6DoubledMinusculeWeight_inr, Pi.neg_apply] at ha ⊢
      rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with h | h | h <;>
        simp_all

private theorem basisSign_reflection_of_weight_ne_zero (i : Fin 6) (a : Fin 27 ⊕ Fin 27)
    (ha : e6DoubledMinusculeWeight a i ≠ 0) :
    basisSign (reflection i a) = -basisSign a := by
  rw [basisSign, basisSign, basisHeight_reflection, Int.negOnePow_sub,
    Int.negOnePow_odd _ ((weight_odd_of_ne_zero i a ha).mul (simpleRootHeight_odd i))]
  simp

private theorem graphPerm_reflection (i : Fin 6) (a : Fin 27 ⊕ Fin 27) :
    e6DoubledMinusculeGraphPerm (reflection i a) =
      reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm a) := by
  apply e6DoubledMinusculeWeight_injective
  funext j
  have hcart := cartanMatrix_E6_graphPermE6 i (graphPermE6 j)
  rw [DynkinType.cartanMatrix_E6, ← Equiv.Perm.mul_apply, ← pow_two, graphPermE6_sq,
    Equiv.Perm.one_apply] at hcart
  calc
    e6DoubledMinusculeWeight
          (e6DoubledMinusculeGraphPerm (reflection i a)) j =
        e6DoubledMinusculeWeight (reflection i a) (graphPermE6 j) :=
      e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm _ _
    _ = e6DoubledMinusculeWeight a (graphPermE6 j) -
        e6DoubledMinusculeWeight a i * CartanMatrix.E 6 i (graphPermE6 j) := by
      rw [congrFun (doubledWeight_reflection i a) (graphPermE6 j),
        root_e6SimpleIndex]
      rfl
    _ = e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm a) j -
        e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm a) (graphPermE6 i) *
          CartanMatrix.E 6 (graphPermE6 i) j := by
      rw [e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm,
        e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm,
        ← Equiv.Perm.mul_apply, ← pow_two, graphPermE6_sq, Equiv.Perm.one_apply, hcart]
    _ = e6DoubledMinusculeWeight
          (reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm a)) j := by
      rw [congrFun (doubledWeight_reflection (graphPermE6 i)
        (e6DoubledMinusculeGraphPerm a)) j, root_e6SimpleIndex]
      rfl

private theorem summandSign_graphPerm (a : Fin 27 ⊕ Fin 27) :
    summandSign (e6DoubledMinusculeGraphPerm a) = -summandSign a := by
  cases a <;> simp

private theorem graphModuleEquiv_involution_apply
    (v : (Fin 27 ⊕ Fin 27) → ℚ) (a : Fin 27 ⊕ Fin 27) :
    (basisSign a : ℚ) *
        ((basisSign (e6DoubledMinusculeGraphPerm a) : ℚ) *
          v (e6DoubledMinusculeGraphPerm (e6DoubledMinusculeGraphPerm a))) = v a := by
  rw [basisSign_graphPerm, e6DoubledMinusculeGraphPerm_apply_apply, ← mul_assoc,
    ← Int.cast_mul, basisSign_sq, Int.cast_one, one_mul]

/-- The signed monomial lift of the type-`E₆` diagram involution to
`V(ϖ₁) ⊕ V(ϖ₆)`. -/
def graphModuleEquiv :
    ((Fin 27 ⊕ Fin 27) → ℚ) ≃ₗ[ℚ] ((Fin 27 ⊕ Fin 27) → ℚ) where
  toFun v a := (basisSign a : ℚ) * v (e6DoubledMinusculeGraphPerm a)
  invFun v a := (basisSign a : ℚ) * v (e6DoubledMinusculeGraphPerm a)
  left_inv v := by
    funext a
    exact graphModuleEquiv_involution_apply v a
  right_inv v := by
    funext a
    exact graphModuleEquiv_involution_apply v a
  map_add' v w := by
    funext a
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    funext a
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf

@[simp]
theorem graphModuleEquiv_apply (v : (Fin 27 ⊕ Fin 27) → ℚ) (a : Fin 27 ⊕ Fin 27) :
    graphModuleEquiv v a =
      (basisSign a : ℚ) * v (e6DoubledMinusculeGraphPerm a) :=
  (rfl)

@[simp]
theorem graphModuleEquiv_apply_apply (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    graphModuleEquiv (graphModuleEquiv v) = v := by
  ext a
  simpa only [graphModuleEquiv_apply] using graphModuleEquiv_involution_apply v a

private theorem weight_graphPerm_graphPerm (b : Fin 27 ⊕ Fin 27) (i : Fin 6) :
    e6DoubledMinusculeWeight (e6DoubledMinusculeGraphPerm b) (graphPermE6 i) =
      e6DoubledMinusculeWeight b i := by
  rw [e6DoubledMinusculeWeight_e6DoubledMinusculeGraphPerm, ← Equiv.Perm.mul_apply,
    ← pow_two, graphPermE6_sq, Equiv.Perm.one_apply]

private theorem eq_reflection_graphPerm_iff (a b : Fin 27 ⊕ Fin 27) (i : Fin 6) :
    a = reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm b) ↔
      e6DoubledMinusculeGraphPerm a = reflection i b := by
  constructor
  · intro h
    calc
      e6DoubledMinusculeGraphPerm a =
          e6DoubledMinusculeGraphPerm
            (reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm b)) := congrArg _ h
      _ = reflection (graphPermE6 (graphPermE6 i))
          (e6DoubledMinusculeGraphPerm (e6DoubledMinusculeGraphPerm b)) :=
        graphPerm_reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm b)
      _ = reflection i b := by
        have hi := congrArg (fun σ : Equiv.Perm (Fin 6) => σ i) graphPermE6_sq
        rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at hi
        rw [hi, e6DoubledMinusculeGraphPerm_apply_apply]
  · intro h
    calc
      a = e6DoubledMinusculeGraphPerm (e6DoubledMinusculeGraphPerm a) := by
        rw [e6DoubledMinusculeGraphPerm_apply_apply]
      _ = e6DoubledMinusculeGraphPerm (reflection i b) := congrArg _ h
      _ = reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm b) :=
        graphPerm_reflection i b

private theorem graphModuleEquiv_rootMatrix_entry
    (target : ℤ) (htarget : target ≠ 0)
    (X : Fin 6 → Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ)
    (hX : ∀ i a b, X i a b =
      if e6DoubledMinusculeWeight b i = target ∧ a = reflection i b
      then (summandSign b : ℚ) else 0)
    (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    (basisSign a : ℚ) * X i (e6DoubledMinusculeGraphPerm a) b =
      X (graphPermE6 i) a (e6DoubledMinusculeGraphPerm b) * (basisSign b : ℚ) := by
  rw [hX, hX, weight_graphPerm_graphPerm]
  have hc :
      (e6DoubledMinusculeWeight b i = target ∧
          a = reflection (graphPermE6 i) (e6DoubledMinusculeGraphPerm b)) ↔
        (e6DoubledMinusculeWeight b i = target ∧
          e6DoubledMinusculeGraphPerm a = reflection i b) :=
    and_congr Iff.rfl (eq_reflection_graphPerm_iff a b i)
  by_cases h : e6DoubledMinusculeWeight b i = target ∧
      e6DoubledMinusculeGraphPerm a = reflection i b
  · rw [ite_eq_left h, ite_eq_left (hc.mpr h)]
    have ha : e6DoubledMinusculeWeight
        (e6DoubledMinusculeGraphPerm b) (graphPermE6 i) ≠ 0 := by
      rw [weight_graphPerm_graphPerm, h.1]
      exact htarget
    rw [(eq_reflection_graphPerm_iff a b i).mpr h.2,
      basisSign_reflection_of_weight_ne_zero _ _ ha, basisSign_graphPerm,
      summandSign_graphPerm]
    push_cast
    ring_nf
  · rw [ite_eq_right h, ite_eq_right (fun hr => h (hc.mp hr)), mul_zero, zero_mul]

private theorem graphModuleEquiv_raising_entry (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    (basisSign a : ℚ) * raisingMatrixQ i (e6DoubledMinusculeGraphPerm a) b =
      raisingMatrixQ (graphPermE6 i) a (e6DoubledMinusculeGraphPerm b) * (basisSign b : ℚ) := by
  exact graphModuleEquiv_rootMatrix_entry (-1) (by norm_num) raisingMatrixQ
    raisingMatrixQ_apply i a b

private theorem graphModuleEquiv_lowering_entry (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    (basisSign a : ℚ) * loweringMatrixQ i (e6DoubledMinusculeGraphPerm a) b =
      loweringMatrixQ (graphPermE6 i) a (e6DoubledMinusculeGraphPerm b) * (basisSign b : ℚ) := by
  exact graphModuleEquiv_rootMatrix_entry 1 (by norm_num) loweringMatrixQ
    loweringMatrixQ_apply i a b

private theorem graphModuleEquiv_mulVec
    (X : Fin 6 → Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ)
    (hX : ∀ i a b,
      (basisSign a : ℚ) * X i (e6DoubledMinusculeGraphPerm a) b =
        X (graphPermE6 i) a (e6DoubledMinusculeGraphPerm b) * (basisSign b : ℚ))
    (i : Fin 6) (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    graphModuleEquiv (X i *ᵥ v) = X (graphPermE6 i) *ᵥ graphModuleEquiv v := by
  ext a
  simp only [graphModuleEquiv_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum, ← Equiv.sum_comp e6DoubledMinusculeGraphPerm
    (fun b => X (graphPermE6 i) a b *
      ((basisSign b : ℚ) * v (e6DoubledMinusculeGraphPerm b)))]
  apply Finset.sum_congr rfl
  intro b _
  rw [e6DoubledMinusculeGraphPerm_apply_apply, basisSign_graphPerm,
    ← mul_assoc, hX]
  ring_nf

private theorem graphModuleEquiv_mulVec_raising (i : Fin 6)
    (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    graphModuleEquiv (raisingMatrixQ i *ᵥ v) =
      raisingMatrixQ (graphPermE6 i) *ᵥ graphModuleEquiv v := by
  exact graphModuleEquiv_mulVec raisingMatrixQ graphModuleEquiv_raising_entry i v

private theorem graphModuleEquiv_mulVec_lowering (i : Fin 6)
    (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    graphModuleEquiv (loweringMatrixQ i *ᵥ v) =
      loweringMatrixQ (graphPermE6 i) *ᵥ graphModuleEquiv v := by
  exact graphModuleEquiv_mulVec loweringMatrixQ graphModuleEquiv_lowering_entry i v

private theorem graphModuleEquiv_ι_rep_serreRootGenerator :
    ∀ (k : Fin 6 ⊕ Fin 6) (v : (Fin 27 ⊕ Fin 27) → ℚ),
      graphModuleEquiv
          (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) v) =
        rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
            (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ (graphRootPerm k)))
          (graphModuleEquiv v)
  | .inl i, v => by
      rw [TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE, graphRootPerm_inl,
        TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE]
      exact graphModuleEquiv_mulVec_raising i v
  | .inr i, v => by
      rw [TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF, graphRootPerm_inr,
        TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF]
      exact graphModuleEquiv_mulVec_lowering i v

/-- The signed graph symmetry preserves the integral coordinate lattice. -/
theorem graphModuleEquiv_mem_lattice_iff (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    graphModuleEquiv v ∈ lattice ↔ v ∈ lattice := by
  rw [mem_lattice_iff, mem_lattice_iff]
  constructor
  · intro h a
    obtain ⟨z, hz⟩ := h (e6DoubledMinusculeGraphPerm a)
    refine ⟨basisSign a * z, ?_⟩
    rw [Int.cast_mul, hz, graphModuleEquiv_apply, basisSign_graphPerm,
      e6DoubledMinusculeGraphPerm_apply_apply, ← mul_assoc, ← Int.cast_mul,
      basisSign_sq, Int.cast_one, one_mul]
  · intro h a
    obtain ⟨z, hz⟩ := h (e6DoubledMinusculeGraphPerm a)
    refine ⟨basisSign a * z, ?_⟩
    rw [Int.cast_mul, hz, graphModuleEquiv_apply]

/-- The coordinate permutation of the signed graph symmetry in the `Fin 54` matrix basis. -/
def graphMatrixPerm : Equiv.Perm (Fin 54) :=
  matrixIndexEquiv.symm |>.trans e6DoubledMinusculeGraphPerm |>.trans matrixIndexEquiv

/-- The integral scale of the signed graph symmetry in the `Fin 54` matrix basis. -/
def graphMatrixScale (i : Fin 54) : ℤ :=
  basisSign (matrixIndexEquiv.symm i)

private theorem coe_smul_latticeBasis (z : ℤ) (a : Fin 27 ⊕ Fin 27) :
    (((z • latticeBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ)) =
      (z : ℚ) • (((latticeBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ)) := by
  rw [Submodule.coe_smul_of_tower, Int.cast_smul_eq_zsmul]

private theorem graphModuleEquiv_latticeBasis (a : Fin 27 ⊕ Fin 27) :
    graphModuleEquiv (((latticeBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ)) =
      (((basisSign a) • latticeBasis (e6DoubledMinusculeGraphPerm a) : lattice) :
        (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [coe_latticeBasis, coe_smul_latticeBasis, coe_latticeBasis]
  ext b
  simp only [graphModuleEquiv_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : e6DoubledMinusculeGraphPerm b = a
  · rw [ite_eq_left h]
    have hb : b = e6DoubledMinusculeGraphPerm a := by
      rw [← h, e6DoubledMinusculeGraphPerm_apply_apply]
    rw [ite_eq_left hb, mul_one]
    rw [← h, basisSign_graphPerm]
    simp
  · rw [ite_eq_right h]
    have hb : b ≠ e6DoubledMinusculeGraphPerm a := by
      intro hb
      apply h
      rw [hb, e6DoubledMinusculeGraphPerm_apply_apply]
    rw [ite_eq_right hb, mul_zero]
    simp

@[simp]
private theorem matrixIndexEquiv_symm_graphMatrixPerm (i : Fin 54) :
    matrixIndexEquiv.symm (graphMatrixPerm i) =
      e6DoubledMinusculeGraphPerm (matrixIndexEquiv.symm i) := by
  simp [graphMatrixPerm]

@[simp]
theorem graphMatrixPerm_apply_apply (i : Fin 54) :
    graphMatrixPerm (graphMatrixPerm i) = i := by
  apply matrixIndexEquiv.symm.injective
  rw [matrixIndexEquiv_symm_graphMatrixPerm, matrixIndexEquiv_symm_graphMatrixPerm,
    e6DoubledMinusculeGraphPerm_apply_apply]

/-- The signed graph symmetry acts monomially on the matrix-coordinate lattice basis. -/
theorem graphModuleEquiv_matrixBasis (i : Fin 54) :
    graphModuleEquiv (((matrixBasis i : lattice) : (Fin 27 ⊕ Fin 27) → ℚ)) =
      (((graphMatrixScale i) • matrixBasis (graphMatrixPerm i) : lattice) :
        (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [matrixBasis_apply, graphModuleEquiv_latticeBasis]
  rw [matrixBasis_apply, matrixIndexEquiv_symm_graphMatrixPerm, graphMatrixScale]

/-- The coordinate permutation of the signed graph symmetry relabels the matrix weights by the
type-`E₆` diagram involution. -/
@[simp]
theorem matrixWeight_graphMatrixPerm (i : Fin 54) (k : Fin 6) :
    matrixWeight (graphMatrixPerm i) (graphPermE6 k) = matrixWeight i k := by
  rw [matrixWeight_apply, matrixWeight_apply]
  rw [matrixIndexEquiv_symm_graphMatrixPerm]
  exact weight_graphPerm_graphPerm _ _

/-! ## The graph automorphism of the carrier -/

private noncomputable def toralGraphAutomorphism :
    Aut (kostantToralGroupScheme
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight) :=
  kostantToralNumberedSymmetryIso
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    graphRootPerm graphModuleEquiv graphModuleEquiv_mem_lattice_iff
    graphModuleEquiv_ι_rep_serreRootGenerator graphRootPerm.surjective
    graphMatrixPerm graphMatrixScale graphModuleEquiv_matrixBasis graphPermE6
    matrixWeight_graphMatrixPerm

/-- **The pinned graph automorphism of the doubled type-`E₆` minuscule carrier.** -/
noncomputable def graphAutomorphism : Aut groupScheme :=
  toralGraphAutomorphism

/-- The graph automorphism renumbers each positive and negative pinned simple-root subgroup by the
type-`E₆` diagram involution, without changing its additive parameter. -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_graphAutomorphism_hom (k : Fin 6 ⊕ Fin 6) :
    rootSubgroup k ≫ graphAutomorphism.hom = rootSubgroup (graphRootPerm k) := by
  rw [rootSubgroup_def, graphAutomorphism, toralGraphAutomorphism,
    kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom]
  exact (rootSubgroup_def (graphRootPerm k)).symm

/-- The graph automorphism relabels the represented split weight torus by the type-`E₆` diagram
involution. -/
@[reassoc (attr := simp)]
theorem weightTorus_comp_graphAutomorphism_hom :
    weightTorus ≫ graphAutomorphism.hom =
      SplitTorus.relabel ℤ graphPermE6 ≫ weightTorus := by
  rw [weightTorus_def, graphAutomorphism, toralGraphAutomorphism,
    kostantWeightTorusToToral_comp_numberedSymmetryIso_hom, Equiv.Perm.inv_def,
    graphPermE6_symm]

/-- **The graph automorphism is an involution.** -/
@[simp]
theorem graphAutomorphism_sq : graphAutomorphism ^ 2 = 1 := by
  rw [graphAutomorphism, toralGraphAutomorphism]
  apply kostantToralNumberedSymmetryIso_pow_eq_one
  · funext k
    exact graphRootPerm_graphRootPerm k
  · exact graphPermE6_sq

/-- Applying the graph automorphism twice is the identity on the doubled type-`E₆` carrier. -/
@[reassoc (attr := simp)]
theorem graphAutomorphism_hom_comp_self :
    graphAutomorphism.hom ≫ graphAutomorphism.hom = 𝟙 groupScheme := by
  calc
    graphAutomorphism.hom ≫ graphAutomorphism.hom =
        (graphAutomorphism.trans graphAutomorphism).hom := (Iso.trans_hom _ _).symm
    _ = (graphAutomorphism * graphAutomorphism).hom :=
      congrArg Iso.hom
        (Aut.Aut_mul_def groupScheme graphAutomorphism graphAutomorphism).symm
    _ = (1 : Aut groupScheme).hom := by
      rw [← pow_two, graphAutomorphism_sq]
    _ = (Iso.refl groupScheme).hom := rfl
    _ = 𝟙 groupScheme := Iso.refl_hom groupScheme

/-- The inverse leg of the doubled type-`E₆` graph automorphism is its forward leg. -/
@[simp]
theorem graphAutomorphism_inv : graphAutomorphism.inv = graphAutomorphism.hom := by
  calc
    graphAutomorphism.inv = 𝟙 groupScheme ≫ graphAutomorphism.inv :=
      (Category.id_comp _).symm
    _ = (graphAutomorphism.hom ≫ graphAutomorphism.hom) ≫
        graphAutomorphism.inv := by rw [graphAutomorphism_hom_comp_self]
    _ = graphAutomorphism.hom ≫
        (graphAutomorphism.hom ≫ graphAutomorphism.inv) := Category.assoc _ _ _
    _ = graphAutomorphism.hom := by
      rw [graphAutomorphism.hom_inv_id, Category.comp_id]

/-! ## The graph automorphism on matrix-valued points -/

/-- The signed monomial matrix inducing the graph automorphism on points. -/
noncomputable def graphAutomorphismMatrix (A : Type v) [CommRing A] :
    Matrix.GeneralLinearGroup (Fin 54) A :=
  kostantNumberedSymmetryMatrix lattice.toAddSubgroup matrixBasis graphModuleEquiv
    graphModuleEquiv_mem_lattice_iff A

/-- The graph-automorphism matrix has the signed monomial entry formula determined by
`graphMatrixPerm` and `graphMatrixScale`. -/
theorem coe_graphAutomorphismMatrix_apply (A : Type v) [CommRing A] (i j : Fin 54) :
    (graphAutomorphismMatrix A : Matrix (Fin 54) (Fin 54) A) i j =
      if i = graphMatrixPerm j then algebraMap ℤ A (graphMatrixScale j) else 0 := by
  exact coe_kostantNumberedSymmetryMatrix_apply_of_monomial lattice.toAddSubgroup matrixBasis
    graphModuleEquiv graphModuleEquiv_mem_lattice_iff graphMatrixPerm graphMatrixScale
    graphModuleEquiv_matrixBasis A i j

/-- The graph-automorphism matrix commutes with extension of the value ring. -/
@[simp]
theorem map_graphAutomorphismMatrix {A : Type v} {B : Type v'} [CommRing A] [CommRing B]
    (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (graphAutomorphismMatrix A) =
      graphAutomorphismMatrix B :=
  map_kostantNumberedSymmetryMatrix lattice.toAddSubgroup matrixBasis graphModuleEquiv
    graphModuleEquiv_mem_lattice_iff f

/-- The signed graph-automorphism matrix is an involution over every commutative ring. -/
@[simp]
theorem graphAutomorphismMatrix_sq (A : Type v) [CommRing A] :
    graphAutomorphismMatrix A ^ 2 = 1 := by
  rw [graphAutomorphismMatrix]
  apply kostantNumberedSymmetryMatrix_pow_eq_one
  intro x
  rw [pow_two, LinearEquiv.mul_apply]
  exact graphModuleEquiv_apply_apply x

/-- Conjugation by the signed graph-automorphism matrix preserves the doubled carrier's point
subgroup. -/
theorem map_points_conj_graphAutomorphismMatrix (A : Type v) [CommRing A] :
    (points A).map (MulAut.conj (graphAutomorphismMatrix A)).toMonoidHom = points A := by
  rw [points_def, definingIdeal_def, graphAutomorphismMatrix]
  simpa only [kostantToralPointsSubgroup_def] using
    map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
    graphRootPerm graphModuleEquiv graphModuleEquiv_mem_lattice_iff
    graphModuleEquiv_ι_rep_serreRootGenerator graphRootPerm.surjective
    graphMatrixPerm graphMatrixScale graphModuleEquiv_matrixBasis graphPermE6
    matrixWeight_graphMatrixPerm A

private noncomputable def graphAutomorphismNormalizer (A : Type v) [CommRing A] :
    Subgroup.normalizer
      (points A : Set (Matrix.GeneralLinearGroup (Fin 54) A)) :=
  ⟨graphAutomorphismMatrix A, Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_points_conj_graphAutomorphismMatrix A)⟩

/-- **The graph automorphism on matrix-valued points of the doubled carrier**, given by
conjugation by its signed monomial matrix. -/
noncomputable def graphAutomorphismPoints (A : Type v) [CommRing A] : MulAut (points A) :=
  (points A).normalizerMonoidHom (graphAutomorphismNormalizer A)

/-- On matrices, the graph automorphism of points is conjugation by its signed monomial matrix. -/
@[simp]
theorem coe_graphAutomorphismPoints (A : Type v) [CommRing A] (g : points A) :
    (graphAutomorphismPoints A g : Matrix.GeneralLinearGroup (Fin 54) A) =
      graphAutomorphismMatrix A * g * (graphAutomorphismMatrix A)⁻¹ :=
  (rfl)

/-- The graph automorphism on points renumbers every pinned positive and negative simple-root
subgroup without changing its additive parameter. -/
@[simp]
theorem graphAutomorphismPoints_rootSubgroupPoints (A : Type v) [CommRing A]
    (k : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    graphAutomorphismPoints A (rootSubgroupPoints k A u) =
      rootSubgroupPoints (graphRootPerm k) A u := by
  apply Subtype.ext
  rw [coe_graphAutomorphismPoints, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    graphAutomorphismMatrix]
  exact kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis graphRootPerm
    graphModuleEquiv graphModuleEquiv_mem_lattice_iff
    graphModuleEquiv_ι_rep_serreRootGenerator A k _

/-- The graph automorphism relabels the coordinates of a represented split-torus point by the
type-`E₆` diagram involution. -/
@[simp]
theorem graphAutomorphismPoints_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin 6 → Aˣ) :
    graphAutomorphismPoints A (weightTorusPoints A s) =
      weightTorusPoints A (fun k => s (graphPermE6 k)) := by
  have hpt : ∀ i,
      torusCharacter s (matrixWeight (graphMatrixPerm⁻¹ i)) =
        torusCharacter (fun k => s (graphPermE6 k)) (matrixWeight i) := by
    intro i
    have hwt : matrixWeight (graphMatrixPerm⁻¹ i) = matrixWeight i ∘ graphPermE6 := by
      funext k
      have h := matrixWeight_graphMatrixPerm (graphMatrixPerm⁻¹ i) k
      rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h
    rw [hwt, ← torusCharacter_mulEquivArrowCongr graphPermE6 s (matrixWeight i)]
    exact congrArg (fun z => torusCharacter z (matrixWeight i))
      (funext fun k => by
        rw [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, graphPermE6_symm])
  have hconj := kostantNumberedSymmetryMatrix_conj_diagGL
    lattice.toAddSubgroup matrixBasis graphModuleEquiv graphModuleEquiv_mem_lattice_iff
    graphMatrixPerm graphMatrixScale graphModuleEquiv_matrixBasis A
    (fun i => torusCharacter s (matrixWeight i))
  apply Subtype.ext
  rw [coe_graphAutomorphismPoints, coe_weightTorusPoints, coe_weightTorusPoints,
    graphAutomorphismMatrix]
  simpa only [kostantTorusMatrix_apply] using hconj.trans (congrArg diagGL (funext hpt))

/-- **The automorphism on matrix-valued points is the map induced by the carrier
automorphism.** After inclusion into `GL₅₄`, composing a scheme-valued point with
`graphAutomorphism` is conjugation by `graphAutomorphismMatrix`. -/
theorem schemePointsMulEquiv_graphAutomorphism_comp_carrierι
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶ groupScheme.X) :
    GeneralLinear.schemePointsMulEquiv 54 A
        (p ≫ (graphAutomorphism.hom ≫ carrierι).hom.hom) =
      graphAutomorphismMatrix A *
          GeneralLinear.schemePointsMulEquiv 54 A (p ≫ carrierι.hom.hom) *
        (graphAutomorphismMatrix A)⁻¹ := by
  rw [graphAutomorphism, carrierι_def, graphAutomorphismMatrix]
  simpa only [toralGraphAutomorphism, Grp.comp_hom_hom, Category.assoc] using
    schemePointsMulEquiv_kostantToralNumberedSymmetryIso
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator matrixBasis matrixWeight
      graphRootPerm graphModuleEquiv graphModuleEquiv_mem_lattice_iff
      graphModuleEquiv_ι_rep_serreRootGenerator graphRootPerm.surjective
      graphMatrixPerm graphMatrixScale graphModuleEquiv_matrixBasis graphPermE6
      matrixWeight_graphMatrixPerm A p

/-- The graph automorphism on points is natural in the value ring. In particular, it commutes
with every iterated Frobenius map. -/
theorem pointsMap_comp_graphAutomorphismPoints {A : Type v} {B : Type v'}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (pointsMap f).comp (graphAutomorphismPoints A).toMonoidHom =
      (graphAutomorphismPoints B).toMonoidHom.comp (pointsMap f) := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, coe_pointsMap, coe_graphAutomorphismPoints,
    coe_graphAutomorphismPoints, coe_pointsMap, map_mul, map_mul, map_inv,
    map_graphAutomorphismMatrix]

/-- **The graph automorphism on matrix-valued points is an involution.** -/
@[simp]
theorem graphAutomorphismPoints_sq (A : Type v) [CommRing A] :
    graphAutomorphismPoints A ^ 2 = 1 := by
  have hnormalizer : graphAutomorphismNormalizer A ^ 2 = 1 :=
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact graphAutomorphismMatrix_sq A)
  rw [graphAutomorphismPoints, ← map_pow, hnormalizer, map_one]

/-- Applying the graph automorphism twice to a matrix-valued point is the identity. -/
@[simp]
theorem graphAutomorphismPoints_graphAutomorphismPoints
    (A : Type v) [CommRing A] (g : points A) :
    graphAutomorphismPoints A (graphAutomorphismPoints A g) = g := by
  have h := congrArg (fun σ : MulAut (points A) => σ g) (graphAutomorphismPoints_sq A)
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

end TauCeti.E6DoubledMinuscule
