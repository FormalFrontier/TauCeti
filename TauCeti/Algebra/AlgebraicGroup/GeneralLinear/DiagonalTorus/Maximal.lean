/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation

/-!
# Maximality of the diagonal torus in the general linear group

Over an algebraically closed field, the diagonal torus of `GL_n` is maximal among reduced
commutative closed subgroup schemes. In Hopf coordinates, its defining ideal is the kernel of
the surjective restriction morphism from `O(GL_n)` to the Laurent coordinate ring of the split
torus.

The proof compares algebraically closed points. A reduced commutative closed subgroup containing
the diagonal torus gives a commutative matrix subgroup containing all invertible diagonal
matrices. The point-level centralizer calculation says that this subgroup is exactly the diagonal
torus. Reduced finite-type point separation then upgrades equality of point subgroups to equality
of their defining Hopf ideals.

This statement is stronger than maximality among tori: every torus is reduced and commutative,
whereas the competing subgroup below need not itself be a torus or connected.

## Main declarations

* `TauCeti.GeneralLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `GL_n`.
* `TauCeti.GeneralLinear.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its points are the
  range of the diagonal-torus point morphism.
* `TauCeti.GeneralLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: no larger reduced
  commutative closed subgroup contains the diagonal torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 12.6 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 15.3 and 16.1.

This completes the standard `GL_n` maximal-torus example required by Layer 7, "Borel subgroups,
maximal tori", of the ReductiveGroups roadmap. Together with the existing adjoint root spaces and
normalizer quotient, it validates the torus used by the packaged `GL_n` root datum and Weyl group.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (k : Type u) [Field k] (n : ℕ)

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `GL_n`.

It is the ordinary kernel of the surjective restriction morphism to the split-torus coordinate
ring, packaged as a Hopf ideal. -/
noncomputable def diagonalTorusDefiningIdeal :
    HopfIdeal k (coordinateHopfAlgebra k n) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := k) (N := n)).hom
    (diagonalTorusCoordinateMap_surjective k n)

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) A =
      ((CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := k) (N := n))).app A).hom.range := by
  rw [diagonalTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro q
  rw [AlgHom.mapDomain_apply]
  exact (CommHopfAlgCat.mapPointsFunctor_app_apply
    (diagonalTorusCoordinateMap (R := k) (N := n)) A q).symm

variable [IsAlgClosed k]

private instance instNontrivialUnitsOfInfiniteField {F : Type*} [Field F] [Infinite F] :
    Nontrivial Fˣ := by
  let U := {x : F // x ∈ ({0} : Set F)ᶜ}
  let _ : Infinite U := (Set.toFinite ({0} : Set F)).infinite_compl.to_subtype
  obtain ⟨x, y, hxy⟩ := exists_pair_ne U
  refine ⟨Units.mk0 x (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property),
    Units.mk0 y (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.property), ?_⟩
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg Units.val h

omit [IsAlgClosed k] in
private theorem isReduced_quotient_diagonalTorusDefiningIdeal :
    IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n)) := by
  let f := (diagonalTorusCoordinateMap (R := k) (N := n)).hom
  let hf : Function.Surjective f := diagonalTorusCoordinateMap_surjective k n
  let e := HopfIdeal.kerLiftBialgEquiv f hf
  exact isReduced_of_injective e.toAlgEquiv.toRingEquiv.toRingHom e.injective

omit [IsAlgClosed k] in
private theorem pointsMulEquiv_diagonalTorusPoints_symm (t : Fin n → kˣ) :
    pointsMulEquiv (R := k) (A := k) n
        (diagonalTorusPoints
          ((SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
            (fun i : ULift.{u} (Fin n) ↦ t i.down))) =
      diagGL t := by
  rw [pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_apply]
  exact congrFun
    ((SplitTorus.pointsMulEquiv (R := k) (A := k)).apply_symm_apply
      (fun j : ULift.{u} (Fin n) ↦ t j.down)) (ULift.up i)

/-- **The diagonal torus of `GL_n` is maximal among reduced commutative closed subgroup
schemes over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal k n`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal k n) :
    I = diagonalTorusDefiningIdeal k n := by
  let H := coordinateHopfAlgebra k n
  let D := diagonalTorusDefiningIdeal k n
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) n
  let P : Subgroup (GL (Fin n) k) := GI.map e.toMonoidHom
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup
      (coordinateHopfAlgebra k n) I (CommAlgCat.of k k)
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI :=
    CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hdiagonalP : TauCeti.diagonalTorus k n ≤ P := by
    intro m hm
    obtain ⟨t, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hm
    let s : ULift.{u} (Fin n) → kˣ := fun i ↦ t i.down
    let q : WithConv
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k) :=
      (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
    let d := diagonalTorusPoints (R := k) (N := n) (A := k) q
    have hdD : d ∈ GD := by
      dsimp only [GD, D]
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      refine ⟨q, ?_⟩
      exact mapPointsFunctor_diagonalTorusCoordinateMap_app A q
    refine ⟨d, hDG hdD, ?_⟩
    -- Unfold the `e.toMonoidHom` coercion introduced by `Subgroup.map` to the coercion of `e`.
    change e d = diagGL t
    simpa only [e, d, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k n t
  have hP : P = TauCeti.diagonalTorus k n :=
    eq_diagonalTorus_of_le_of_isMulCommutative P hdiagonalP
  have hpoints : GI = GD := by
    apply le_antisymm
    · intro g hg
      have hegP : e g ∈ P := ⟨g, hg, rfl⟩
      have hegD : e g ∈ TauCeti.diagonalTorus k n := hP ▸ hegP
      obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hegD
      let s : ULift.{u} (Fin n) → kˣ := fun i ↦ t i.down
      let q : WithConv
          (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k) :=
        (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
      have hdiag : e (diagonalTorusPoints (R := k) (N := n) (A := k) q) = diagGL t := by
        simpa only [e, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k n t
      dsimp only [GD, D]
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      refine ⟨q, ?_⟩
      apply e.injective
      rw [mapPointsFunctor_diagonalTorusCoordinateMap_app]
      exact hdiag.trans ht
    · exact hDG
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    isReduced_quotient_diagonalTorusDefiningIdeal k n
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

end

end TauCeti.GeneralLinear
