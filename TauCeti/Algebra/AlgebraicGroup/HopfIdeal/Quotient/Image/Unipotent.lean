/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.FaithfullyFlat
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Unipotence of affine group images

For a morphism `f : H ⟶ K` of commutative Hopf algebras, its scheme-theoretic image has coordinate
algebra
`CommHopfAlgCat.image f = H / ker f`; finite type of `K` makes the canonical inclusion
`CommHopfAlgCat.image f ⟶ K` finite type. If this inclusion is faithfully flat, every
algebraically closed point of the image lifts to a point of `Spec K`.

There are two ways to descend unipotence from `Spec K` to the image. A faithfully flat inclusion
lifts every geometric point of the image to the source. More directly, when `K` is reduced and
finite type, its geometric points separate the coefficients of the characteristic polynomial of
every representation. The latter argument only needs the canonical inclusion to be injective,
and hence applies to every scheme-theoretic image of a smooth unipotent affine group.

## Main declaration

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_injective_of_reduced`: geometric
  unipotence descends along an injective coordinate morphism with reduced finite-type codomain.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced`: the image of a
  reduced finite-type geometrically unipotent affine group is geometrically unipotent.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.image_of_faithfullyFlat`: a
  faithfully flat finite-type affine group image has only unipotent geometric points when its
  source does.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 14.4, for the unipotent-radical application.

This is the image-unipotence step for Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. In particular, it supplies the remaining geometric-unipotence input in the binary-product
closure of connected normal smooth unipotent subgroup schemes.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

attribute [local instance 1100] Module.Free.of_divisionRing

private theorem coefficientMatrix_corestrict
    {C D : Type v} {M : Type w} {ι : Type x}
    [AddCommMonoid C] [Module k C] [Coalgebra k C]
    [AddCommMonoid D] [Module k D] [Coalgebra k D]
    [AddCommMonoid M] [Module k M] [Comodule k C M]
    (b : Module.Basis ι k M) (f : C →ₗc[k] D) :
    letI : Comodule k D M := Comodule.Corestrict f
    Comodule.coefficientMatrix (C := D) b =
      (Comodule.coefficientMatrix (C := C) b).map f := by
  let _ : Comodule k D M := Comodule.Corestrict f
  ext i j
  rw [Comodule.coefficientMatrix_apply, Matrix.map_apply,
    Comodule.coefficientMatrix_apply,
    Comodule.matrixCoefficient_def, Comodule.matrixCoefficient_def,
    Comodule.corestrict_coact_apply]
  have h := LinearMap.congr_fun
    (CoassocSimps.lid_comp_map (b.coord i) f.toLinearMap)
    (Comodule.coact (R := k) (C := C) (M := M) (b j))
  rw [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  -- `lid_comp_map` gives this naturality identity for the underlying linear map.
  change _ = f.toLinearMap _
  exact h

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
      have hd : Module.finrank (AlgebraicClosure k)
          (AlgebraicClosure k ⊗[k] N) = d := rfl
      rw [hd] at hcharpoly
      exact hcharpoly.trans (by simp [P])
    have hmatrix : D.map q =
        LinearMap.toMatrix (b.baseChange (AlgebraicClosure k))
          (b.baseChange (AlgebraicClosure k)) (Comodule.endOfPoint N q) := by
      rw [Comodule.toMatrix_endOfPoint]
      rw [coefficientMatrix_corestrict b f.hom.toCoalgHom]
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

/-- The scheme-theoretic image of a reduced finite-type geometrically unipotent affine group is
geometrically unipotent. -/
theorem image_of_reduced (f : H ⟶ K) [Algebra.FiniteType k K] [IsReduced K]
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K) :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.image f) :=
  of_injective_of_reduced (CommHopfAlgCat.imageι f)
    (CommHopfAlgCat.imageι_injective f) hK

/-- The scheme-theoretic image of a finite-type geometrically unipotent affine group is
geometrically unipotent when the source-to-image morphism is faithfully flat.

The finite-type hypothesis on `K` makes the canonical inclusion of the image coordinate algebra
into `K` a finite-type algebra map. Faithful flatness then lifts every algebraic-closure-valued
point of the image to a point of `K`, whose unipotence descends by precomposition. -/
theorem image_of_faithfullyFlat (f : H ⟶ K) [Algebra.FiniteType k K]
    (hK : geometricallyUnipotentPointsCommHopfAlgProperty k K)
    (hflat : (CommHopfAlgCat.imageι f).hom.toAlgHom.toRingHom.FaithfullyFlat) :
    geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.image f) := by
  have hfinite : (CommHopfAlgCat.imageι f).hom.toAlgHom.FiniteType := by
    apply AlgHom.FiniteType.of_comp_finiteType
      (f := Algebra.ofId k (CommHopfAlgCat.image f))
    rw [Algebra.comp_ofId]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact of_faithfullyFlat (CommHopfAlgCat.imageι f) hfinite hflat hK

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti
