/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Unipotence under injective morphisms into reduced Hopf algebras

An injective morphism `H ⟶ K` of coordinate Hopf algebras represents a schematically dense
homomorphism `Spec K ⟶ Spec H`. When `K` is reduced and finite type, its geometric points separate
elements. Applying this to the coefficients of the characteristic polynomial of every
representation shows that geometric unipotence descends from `K` to `H`.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_injective_of_reduced`: geometric
  unipotence descends along an injective coordinate morphism with reduced finite-type codomain.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 14.4, for the unipotent-radical application.

This supplies the reduced-source descent input for Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

attribute [local instance 1100] Module.Free.of_divisionRing

/-- Geometric unipotence descends along an injective morphism of coordinate Hopf algebras whose
codomain is reduced and finite type.

Contravariantly, the morphism represents a schematically dense homomorphism from `Spec K` to
`Spec H`. For a finite-dimensional `H`-comodule, every geometric point of `Spec K` makes the
characteristic polynomial of the restricted action equal to `(X - 1) ^ n`. Point separation in
the reduced algebra `K` gives the same identity for the universal coefficient matrix. Injectivity
then reflects it to `H`, where evaluation proves that every geometric point of `Spec H` acts
unipotently. -/
theorem of_injective_of_reduced (f : H ⟶ K) (hf : Function.Injective f.hom)
    [Algebra.FiniteType k K] [IsReduced K]
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k H := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hK ⊢
  intro g
  rw [HopfAlgebra.isUnipotentPoint_def]
  intro M
  let b := Module.Free.chooseBasis k M
  let C := Comodule.coefficientMatrix (C := H) b
  let D := C.map f.hom
  let d := Module.finrank (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] M)
  let P : Polynomial k := (Polynomial.X - 1) ^ d
  -- Point separation turns the characteristic polynomial identity at every source point into
  -- an identity for the universal coefficient matrix over the source coordinate algebra.
  have hDcharpoly : D.charpoly = P.map (algebraMap k K) := by
    apply Polynomial.ext
    intro r
    apply TauCeti.eq_of_forall_algHom_apply_eq
      (k := k) (K := AlgebraicClosure k)
    intro q
    let _ : Comodule k K M := Comodule.Corestrict f.hom.toCoalgHom
    let N : FGComoduleCat.{u, v, u} k K := FGComoduleCat.of (R := k) (C := K) M
    have hq := (HopfAlgebra.isUnipotentPoint_def (WithConv.toConv q)).mp
      (hK (WithConv.toConv q)) N
    have hqcharpoly : (Comodule.endOfPoint M q).charpoly =
        P.map (algebraMap k (AlgebraicClosure k)) := by
      have hcoe :
          ((LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction N (WithConv.toConv q))) : Module.End _ _) =
              Comodule.endOfPoint M q :=
        Comodule.pointsAction_toLinearMap N (WithConv.toConv q)
      rw [← hcoe]
      have hcharpoly := (LinearMap.GeneralLinearGroup.isUnipotent_iff_charpoly _).mp hq
      let e : N ≃ₗ[k] M := LinearEquiv.refl k M
      have hd : Module.finrank (AlgebraicClosure k)
          (AlgebraicClosure k ⊗[k] N) = d :=
        LinearEquiv.finrank_eq (e.baseChange k (AlgebraicClosure k) N M)
      rw [hd] at hcharpoly
      exact hcharpoly.trans (by simp [P])
    have hmatrix : D.map q =
        LinearMap.toMatrix (b.baseChange (AlgebraicClosure k))
          (b.baseChange (AlgebraicClosure k)) (Comodule.endOfPoint N q) := by
      rw [Comodule.toMatrix_endOfPoint]
      rw [Comodule.coefficientMatrix_corestrict b f.hom.toCoalgHom]
      -- Unfold the local names so `Matrix.map_map` sees the two successive coefficient maps.
      change (C.map f.hom).map q = _
      rw [Matrix.map_map]
      ext i j
      rfl
    rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint N q)
      (b.baseChange (AlgebraicClosure k)), ← hmatrix] at hqcharpoly
    calc
      q (D.charpoly.coeff r) = (D.charpoly.map q).coeff r := by
        exact (Polynomial.coeff_map q.toRingHom r).symm
      _ = (D.map q).charpoly.coeff r :=
        congrArg (fun p ↦ p.coeff r) (Matrix.charpoly_map D q.toRingHom).symm
      _ = (P.map (algebraMap k (AlgebraicClosure k))).coeff r :=
        congrArg (fun p ↦ p.coeff r) hqcharpoly
      _ = q ((P.map (algebraMap k K)).coeff r) := by
        rw [Polynomial.coeff_map, Polynomial.coeff_map]
        exact (q.commutes (P.coeff r)).symm
  -- Injectivity reflects the universal characteristic polynomial identity to the target.
  have hCcharpoly : C.charpoly = P.map (algebraMap k H) := by
    apply Polynomial.map_injective f.hom.toAlgHom.toRingHom hf
    rw [← Matrix.charpoly_map]
    -- Expose the local name for the mapped coefficient matrix.
    change D.charpoly = _
    rw [hDcharpoly]
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact (f.hom.toAlgHom.commutes x).symm
  -- Evaluating the reflected identity proves the required statement at an arbitrary target point.
  have hgcharpoly :
      (Comodule.endOfPoint M g.ofConv).charpoly =
        P.map (algebraMap k (AlgebraicClosure k)) := by
    rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M g.ofConv)
      (b.baseChange (AlgebraicClosure k)), Comodule.toMatrix_endOfPoint]
    -- Expose the local name for the target coefficient matrix before applying `charpoly_map`.
    change (C.map g.ofConv).charpoly = _
    calc
      (C.map g.ofConv).charpoly = C.charpoly.map g.ofConv.toRingHom :=
        Matrix.charpoly_map C g.ofConv.toRingHom
      _ = _ := by
        rw [hCcharpoly, Polynomial.map_map]
        congr 1
        ext x
        exact g.ofConv.commutes x
  apply LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq (n := d)
  have hcoe :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End _ _) =
          Comodule.endOfPoint M g.ofConv :=
    Comodule.pointsAction_toLinearMap M g
  rw [hcoe]
  exact hgcharpoly.trans (by simp [P])

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti
