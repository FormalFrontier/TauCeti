/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Base
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular
public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# Positive roots and the upper-triangular subgroup of the general linear group

For the consecutive-root base of the diagonal root datum of `GL_(n+1)`, the root indexed by
the ordered pair `(i, j)` is positive exactly when `i < j`. Thus the root subgroup attached to
every positive root consists of upper-triangular elementary matrices and factors through the
standard upper-triangular subgroup scheme.

## Main declarations

* `TauCeti.GeneralLinear.diagonalRootBase_isPos_iff`: positive diagonal roots are exactly
  the coordinate differences `e_i - e_j` with `i < j`.
* `TauCeti.GeneralLinear.UpperTriangular.rootSubgroupCoordinateMap`: the coordinate map of a
  positive root subgroup factored through the upper-triangular coordinate algebra.
* `TauCeti.GeneralLinear.UpperTriangular.rootSubgroup`: the corresponding group-scheme morphism.
* `TauCeti.GeneralLinear.UpperTriangular.rootSubgroup_comp_inclusion`: the factorization recovers
  the ambient root subgroup of `GL_(n+1)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 26--28.

This identifies the positive roots selected by the standard Borel in the split `GL_n` example of
Layer 7, "Structure theory", of the ReductiveGroups roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory Function Set WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- The diagonal root index attached to an ordered pair of distinct matrix coordinates. -/
private def diagonalRootIndexOfNe {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    DiagonalRootIndex n :=
  ⟨(ULift.up i, ULift.up j), fun h ↦ hij (ULift.up_injective h)⟩

@[simp]
private theorem diagonalRootIndexOfNe_fst {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (diagonalRootIndexOfNe i j hij).1.1 = ULift.up i := by
  rfl

@[simp]
private theorem diagonalRootIndexOfNe_snd {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (diagonalRootIndexOfNe i j hij).1.2 = ULift.up j := by
  rfl

private theorem diagonalRootIndexOfNe_eq_diagonalSimpleRootIndex (n : ℕ) (i : Fin n) :
    diagonalRootIndexOfNe i.castSucc i.succ i.castSucc_lt_succ.ne =
      diagonalSimpleRootIndex n i := by
  apply Subtype.ext
  apply Prod.ext <;> simp

private theorem diagonalRootIndexOfNe_isPos_of_lt (n : ℕ) (i j : Fin (n + 1))
    (hij : i < j) :
    (diagonalRootBase.{u} n).IsPos (diagonalRootIndexOfNe i j hij.ne) := by
  induction hdist : j.val - i.val using Nat.strong_induction_on generalizing i j with
  | h d ih =>
      by_cases hadj : i.val + 1 = j.val
      · let a : Fin n := ⟨i.val, by omega⟩
        have hidx : diagonalRootIndexOfNe i j hij.ne = diagonalSimpleRootIndex n a := by
          apply Subtype.ext
          apply Prod.ext
          · simp [a]
          · simp [a, hadj]
        rw [hidx]
        exact RootPairing.Base.isPos_of_mem_support
          ((mem_diagonalRootBase_support n _).2 ⟨a, rfl⟩)
      · let k : Fin (n + 1) := ⟨i.val + 1, by omega⟩
        have hik : i < k := by simp [Fin.lt_def, k]
        have hkj : k < j := by simp only [Fin.lt_def, k]; omega
        have hdist' : j.val - k.val < d := by simp only [k]; omega
        have hkpos := ih (j.val - k.val) hdist' k j hkj rfl
        let a : Fin n := ⟨i.val, by omega⟩
        have hipos : (diagonalRootBase.{u} n).IsPos
            (diagonalRootIndexOfNe i k hik.ne) := by
          have hidx : diagonalRootIndexOfNe i k hik.ne =
              diagonalSimpleRootIndex n a := by
            apply Subtype.ext
            apply Prod.ext
            · simp [a]
            · simp [a, k]
          rw [hidx]
          exact RootPairing.Base.isPos_of_mem_support
            ((mem_diagonalRootBase_support n _).2 ⟨a, rfl⟩)
        exact RootPairing.Base.IsPos.add hipos hkpos (by
          rw [diagonalRootDatum_root, diagonalRootDatum_root, diagonalRootDatum_root]
          ext x
          simp only [diagonalRoot_apply, diagonalRootIndexOfNe_fst,
            diagonalRootIndexOfNe_snd, ULift.down_up, Finsupp.add_apply]
          ring)

/-- A diagonal root is positive for the consecutive-root base exactly when its row index is
strictly smaller than its column index. -/
@[simp]
theorem diagonalRootBase_isPos_iff (n : ℕ)
    (p : DiagonalRootIndex.{u} (n + 1)) :
    (diagonalRootBase.{u} n).IsPos p ↔ p.1.1.down < p.1.2.down := by
  constructor
  · intro hp
    by_contra hlt
    have hrev : p.1.2.down < p.1.1.down := by
      exact lt_of_le_of_ne (not_lt.mp hlt) fun h ↦ p.2 (ULift.down_injective h.symm)
    let q := diagonalRootIndexOfNe p.1.2.down p.1.1.down hrev.ne
    have hq : (diagonalRootBase.{u} n).IsPos q :=
      diagonalRootIndexOfNe_isPos_of_lt n _ _ hrev
    let _ := (diagonalRootDatum.{u} (n + 1)).indexNeg
    have hneg : -p = q := by
      change (diagonalRootDatum.{u} (n + 1)).reflectionPerm p p = q
      rw [diagonalRootDatum_reflectionPerm]
      apply Subtype.ext
      rw [diagonalReflectionIndex_coe]
      simp [q, diagonalRootIndexOfNe]
    have := (RootPairing.Base.IsPos.neg_iff_not (diagonalRootBase.{u} n) p).mp
      (hneg.symm ▸ hq)
    exact this hp
  · intro hij
    convert diagonalRootIndexOfNe_isPos_of_lt n p.1.1.down p.1.2.down hij using 1
    apply Subtype.ext
    simp [diagonalRootIndexOfNe]

end

end TauCeti.GeneralLinear

namespace TauCeti.GeneralLinear.UpperTriangular

universe u w

noncomputable section

variable (R : Type u) [CommRing R] {n : ℕ} {i j : Fin n}

/-- A root subgroup indexed by `i < j` consists of upper-triangular matrices, so its points lie
in the standard upper-triangular closed subgroup. -/
theorem rootSubgroupPoints_mem (hij : i < j)
    {A : Type w} [CommRing A] [Algebra R A]
    (f : HopfAlgebra.points
      (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) (CommAlgCat.of R A)) :
    GeneralLinear.rootSubgroupPoints hij.ne f ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n)
        (CommAlgCat.of R A) := by
  rw [mem_definingPointsSubgroup_iff, GeneralLinear.pointsMulEquiv_rootSubgroupPoints,
    UpperTriangularGroup.mem_iff]
  intro a b hba
  simp only [id_eq] at hba
  have hab : a ≠ b := hba.ne.symm
  have hroot : ¬ (i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hij hba
  rw [coe_transvectionUnit, Matrix.transvection]
  simp [Matrix.add_apply, hab, hroot]

/-- The coordinate morphism of the root subgroup `x_ij`, for `i < j`, into the standard
upper-triangular coordinate Hopf algebra. -/
noncomputable def rootSubgroupCoordinateMap (hij : i < j) :
    coordinateHopfAlgebra R n ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R n)
    (GeneralLinear.rootSubgroupCoordinateMap hij.ne) (by
      rw [definingHopfIdeal_toIdeal, Ideal.span_le]
      intro x hx
      rw [mem_definingRelationSet_iff] at hx
      obtain ⟨a, b, hba, rfl⟩ := hx
      rw [SetLike.mem_coe, RingHom.mem_ker]
      let q : HopfAlgebra.points
          (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
          (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)) :=
        toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
      have hmem := rootSubgroupPoints_mem R hij q
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem
      have hzero := hmem
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (a, b))))
        (HopfIdeal.mem_toIdeal.mp
          (definingHopfIdeal_toIdeal R n ▸ Ideal.subset_span
            ((mem_definingRelationSet_iff R n _).2 ⟨a, b, hba, rfl⟩)))
      have hpoint :
          GeneralLinear.rootSubgroupPoints hij.ne q =
            (CommHopfAlgCat.mapPointsFunctor
              (GeneralLinear.rootSubgroupCoordinateMap hij.ne)).app
              (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)) q := by
        rw [GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app]
      rw [hpoint, CommHopfAlgCat.mapPointsFunctor_app_apply] at hzero
      exact hzero)

/-- Precomposing a factored positive-root coordinate morphism with the upper-triangular quotient
map recovers the ambient general-linear root-subgroup coordinate morphism. -/
@[simp]
theorem coordinateMap_comp_rootSubgroupCoordinateMap (hij : i < j) :
    coordinateMap R n ≫ rootSubgroupCoordinateMap R hij =
      GeneralLinear.rootSubgroupCoordinateMap hij.ne := by
  rw [coordinateMap_def, rootSubgroupCoordinateMap]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- The positive root subgroup `x_ij : 𝔾ₐ → B_n` inside the standard upper-triangular
subgroup scheme, for an ordered pair `i < j`. -/
noncomputable def rootSubgroup (hij : i < j) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R n :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap R hij).op ≫
    eqToHom (groupScheme_def R n).symm

/-- The upper-triangular root subgroup is relative spectrum applied contravariantly to its
coordinate morphism, transported across the named presentations. -/
theorem rootSubgroup_def (hij : i < j) :
    rootSubgroup R hij =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap R hij).op ≫
        eqToHom (groupScheme_def R n).symm := by
  rfl

/-- Composing a positive root subgroup of the standard upper-triangular group with its inclusion
into `GL_n` recovers the ambient root subgroup `x_ij`. -/
@[simp]
theorem rootSubgroup_comp_inclusion (hij : i < j) :
    rootSubgroup R hij ≫ inclusion R n = GeneralLinear.rootSubgroup hij.ne := by
  rw [rootSubgroup_def, inclusion, GeneralLinear.rootSubgroup_def,
    GeneralLinear.weightParabolicInclusion_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  have hmap :
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap R hij).op ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
            (definingHopfIdeal R n)).op =
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (GeneralLinear.rootSubgroupCoordinateMap hij.ne).op := by
    rw [← Functor.map_comp, ← op_comp, ← coordinateMap_def R n,
      coordinateMap_comp_rootSubgroupCoordinateMap]
  congr 1
  rw [← Category.assoc, hmap]
  rfl

end


end TauCeti.GeneralLinear.UpperTriangular
