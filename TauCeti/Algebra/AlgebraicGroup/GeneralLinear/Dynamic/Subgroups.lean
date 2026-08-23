/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Basic

/-!
# The dynamic Levi and unipotent subgroups of `GL₂`

For the cocharacter `t ↦ diag(t, 1)` of `GL₂`, the dynamic parabolic is the upper-triangular
Borel subgroup. This file identifies the other two pieces of its dynamic Levi decomposition:

* the dynamic Levi subgroup is the diagonal torus;
* the dynamic unipotent subgroup is the positive root subgroup `x₀₁`.

The statements hold on points over every commutative algebra over the base ring. They are first
expressed as concrete matrix membership criteria and then as equalities with the preimages of the
standard matrix subgroups. They also show that every such point comes from the existing diagonal
torus or root-subgroup point homomorphism. Thus the abstract dynamic decomposition agrees with
the standard `B = T U` decomposition of `GL₂`.

The proofs use the already computed dynamic limit: an upper-triangular matrix is sent to its
diagonal part. A point is in the Levi precisely when it equals that limit, while it is in the
unipotent subgroup precisely when the limit is one.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.mem_dynamicLevi_iff`: the dynamic Levi points are exactly the
  diagonal matrices.
* `TauCeti.GeneralLinear.Dynamic.dynamicLevi_eq_diagonalTorus_comap`: the dynamic Levi is the
  preimage of the diagonal torus under the matrix-point equivalence.
* `TauCeti.GeneralLinear.Dynamic.mem_dynamicUnipotent_iff`: the dynamic unipotent points are
  exactly the matrices `!![1, b; 0, 1]`.
* `TauCeti.GeneralLinear.Dynamic.dynamicUnipotent_eq_upperUnitriangularGroup_comap`: the dynamic
  unipotent subgroup is the preimage of `U₂` under the matrix-point equivalence.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This completes the concrete rank-one example in the dynamic parabolic/Levi route of Layer 7,
"Structure theory", of the ReductiveGroups roadmap.
-/

public section

open Matrix WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]

private theorem upperRightHom_eq_transvectionUnit (b : A) :
    Matrix.GeneralLinearGroup.upperRightHom b =
      transvectionUnit (by decide : (0 : Fin 2) ≠ 1) b := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_transvectionUnit]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom, Matrix.transvection, Matrix.single]

/-- A point belongs to the dynamic Levi subgroup for `t ↦ diag(t, 1)` exactly when its matrix is
diagonal. -/
@[simp]
theorem mem_dynamicLevi_iff
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.levi A (GL2.dynamicCocharacter (R := R)) ↔
      pointsMulEquiv 2 g ∈ TauCeti.diagonalTorus A 2 := by
  constructor
  · intro hg
    have hgP : g ∈ Cocharacter.parabolic A (GL2.dynamicCocharacter (R := R)) :=
      Cocharacter.levi_le_parabolic hg
    have hlimit := GL2.pointsMulEquiv_limit_dynamicCocharacter g hgP
    rw [Cocharacter.limit_of_mem_levi hg] at hlimit
    rw [mem_diagonalTorus_iff]
    intro i j hij
    have hentry := congrArg
      (fun M : GL (Fin 2) A => (M : Matrix (Fin 2) (Fin 2) A) i j) hlimit
    rw [GL2Borel.coe_torusHom] at hentry
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa using hentry
    · simpa using hentry
    · exact (hij rfl).elim
  · intro hg
    have hgDiag : (pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A).IsDiag :=
      mem_diagonalTorus_iff.mp hg
    have hgP : g ∈ Cocharacter.parabolic A (GL2.dynamicCocharacter (R := R)) := by
      rw [GL2.mem_dynamicParabolic_iff]
      exact GL2Borel.mem_iff.mpr (hgDiag (by decide))
    have hlimit := GL2.pointsMulEquiv_limit_dynamicCocharacter g hgP
    have hlimit_eq :
        Cocharacter.limit A (GL2.dynamicCocharacter (R := R)) ⟨g, hgP⟩ = g := by
      apply (pointsMulEquiv (R := R) (A := A) 2).injective
      rw [hlimit]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · simp [GL2Borel.coe_torusHom, GL2Borel.coe_mk]
      · simpa [GL2Borel.coe_torusHom, GL2Borel.coe_mk] using
          (hgDiag (by decide : (0 : Fin 2) ≠ 1)).symm
      · simpa [GL2Borel.coe_torusHom, GL2Borel.coe_mk] using
          (hgDiag (by decide : (1 : Fin 2) ≠ 0)).symm
      · simp [GL2Borel.coe_torusHom, GL2Borel.coe_mk]
    rw [← hlimit_eq]
    exact Cocharacter.limit_mem_levi ⟨g, hgP⟩

/-- The dynamic Levi subgroup for `t ↦ diag(t, 1)` is the preimage of the diagonal torus under
the general-linear point equivalence. -/
theorem dynamicLevi_eq_diagonalTorus_comap :
    Cocharacter.levi A (GL2.dynamicCocharacter (R := R)) =
      (TauCeti.diagonalTorus A 2).comap
        (pointsMulEquiv (R := R) (A := A) 2).toMonoidHom := by
  ext g
  exact mem_dynamicLevi_iff g

/-- A point belongs to the dynamic Levi subgroup exactly when it is the image of a point of the
rank-two split torus. -/
theorem mem_dynamicLevi_iff_exists_diagonalTorusPoint
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.levi A (GL2.dynamicCocharacter (R := R)) ↔
      ∃ q : WithConv
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) →ₐ[R] A),
        diagonalTorusPoints q = g := by
  rw [mem_dynamicLevi_iff]
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
    let q := (SplitTorus.pointsMulEquiv (R := R) (A := A)).symm
      (fun i : ULift.{u} (Fin 2) => t i.down)
    refine ⟨q, ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) 2).injective
    rw [pointsMulEquiv_diagonalTorusPoints, ← ht]
    congr 1
    funext i
    rw [diagonalTorusCoordinates_apply]
    exact congrFun
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).apply_symm_apply
        (fun j : ULift.{u} (Fin 2) => t j.down)) (ULift.up i)
  · rintro ⟨q, rfl⟩
    rw [pointsMulEquiv_diagonalTorusPoints]
    exact mem_diagonalTorus_iff_exists_diagGL.mpr
      ⟨diagonalTorusCoordinates (SplitTorus.pointsMulEquiv q), rfl⟩

/-- A point belongs to the dynamic unipotent subgroup for `t ↦ diag(t, 1)` exactly when its
matrix is `!![1, b; 0, 1]` for some `b`. -/
@[simp]
theorem mem_dynamicUnipotent_iff
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.unipotent A (GL2.dynamicCocharacter (R := R)) ↔
      ∃ b : A, pointsMulEquiv 2 g = Matrix.GeneralLinearGroup.upperRightHom b := by
  constructor
  · intro hg
    obtain ⟨hgP, hgLimit⟩ := Cocharacter.mem_unipotent_iff.mp hg
    have hlimit := GL2.pointsMulEquiv_limit_dynamicCocharacter g hgP
    rw [hgLimit, map_one] at hlimit
    let gB : GL2Borel A := ⟨pointsMulEquiv 2 g, (GL2.mem_dynamicParabolic_iff g).mp hgP⟩
    have htorus : GL2Borel.torusHom (GL2Borel.diag gB) = 1 := by
      apply Subtype.ext
      exact hlimit.symm
    have hdiag : GL2Borel.diag gB = 1 := by
      have := congrArg GL2Borel.diag htorus
      simpa using this
    obtain ⟨b, hb⟩ := (GL2Borel.mem_ker_diag_iff gB).mp
      (MonoidHom.mem_ker.mpr hdiag)
    refine ⟨b, ?_⟩
    have := congrArg (fun h : GL2Borel A => (h : GL (Fin 2) A)) hb
    simpa [gB] using this
  · rintro ⟨b, hb⟩
    have hgP : g ∈ Cocharacter.parabolic A (GL2.dynamicCocharacter (R := R)) := by
      rw [GL2.mem_dynamicParabolic_iff, hb]
      exact GL2Borel.upperRightHom_mem A b
    refine Cocharacter.mem_unipotent_iff.mpr ⟨hgP, ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) 2).injective
    rw [GL2.pointsMulEquiv_limit_dynamicCocharacter, map_one]
    let gB : GL2Borel A := ⟨pointsMulEquiv 2 g, (GL2.mem_dynamicParabolic_iff g).mp hgP⟩
    have hgB : gB = GL2Borel.unipotentHom b := by
      apply Subtype.ext
      simpa [gB] using hb
    have hdiag : GL2Borel.diag gB = 1 := by
      rw [hgB, GL2Borel.diag_unipotentHom]
    rw [hdiag, map_one]
    rfl

/-- The dynamic unipotent subgroup for `t ↦ diag(t, 1)` is the preimage of the standard
upper-unitriangular subgroup `U₂` under the general-linear point equivalence. -/
theorem dynamicUnipotent_eq_upperUnitriangularGroup_comap :
    Cocharacter.unipotent A (GL2.dynamicCocharacter (R := R)) =
      (upperUnitriangularGroup (Fin 2) A).comap
        (pointsMulEquiv (R := R) (A := A) 2).toMonoidHom := by
  ext g
  rw [mem_dynamicUnipotent_iff, Subgroup.mem_comap, UpperUnitriangularGroup.mem_iff]
  simp only [MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨b, hb⟩
    rw [hb, Matrix.isUpperUnitriangular_def]
    constructor
    · intro i j hji
      fin_cases i <;> fin_cases j <;>
        simp_all [Matrix.GeneralLinearGroup.upperRightHom]
    · intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.upperRightHom]
  · intro hg
    refine ⟨(pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 0 1, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.GeneralLinearGroup.upperRightHom] using hg.apply_diag 0
    · simp [Matrix.GeneralLinearGroup.upperRightHom]
    · simpa [Matrix.GeneralLinearGroup.upperRightHom] using
        hg.isUpperTriangular (by decide : (0 : Fin 2) < 1)
    · simpa [Matrix.GeneralLinearGroup.upperRightHom] using hg.apply_diag 1

/-- A point belongs to the dynamic unipotent subgroup exactly when it comes from the positive
simple-root point homomorphism `x₀₁`. -/
theorem mem_dynamicUnipotent_iff_exists_rootSubgroupPoint
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.unipotent A (GL2.dynamicCocharacter (R := R)) ↔
      ∃ q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A),
        rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) q = g := by
  rw [mem_dynamicUnipotent_iff]
  constructor
  · rintro ⟨b, hb⟩
    let q := (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm
      (Multiplicative.ofAdd b)
    refine ⟨q, ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) 2).injective
    rw [pointsMulEquiv_rootSubgroupPoints, hb, upperRightHom_eq_transvectionUnit]
    simp [q]
  · rintro ⟨q, rfl⟩
    refine ⟨Multiplicative.toAdd
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q), ?_⟩
    rw [pointsMulEquiv_rootSubgroupPoints, upperRightHom_eq_transvectionUnit]

end TauCeti.GeneralLinear.Dynamic
