/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Unipotence over reduced Hopf algebras

An injective morphism `H ⟶ K` of coordinate Hopf algebras represents a schematically dense
homomorphism `Spec K ⟶ Spec H`. When `K` is reduced and finite type, its geometric points separate
elements. Applying this to the coefficients of the characteristic polynomial of every
representation shows that geometric unipotence descends from `K` to `H`.

The same universal characteristic-polynomial identity also shows that every point valued in any
commutative algebra over the ground field is unipotent.

## Main declarations

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.of_injective_of_reduced`: geometric
  unipotence descends along an injective coordinate morphism with reduced finite-type codomain.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint`: geometric
  unipotence can be evaluated in any commutative algebra.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.iff_forall_isUnipotentPoint`:
  geometric unipotence can be characterized over any algebraically closed extension.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.isUnipotentPoint`: the smooth finite-type
  specialization, where reducedness follows from smoothness.
* `TauCeti.smoothUnipotentCommHopfAlgProperty.iff_smooth_and_forall_isUnipotentPoint`:
  the corresponding characterization for smooth unipotence.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 14.4, for the unipotent-radical application.

This supplies the reduced-source descent input for Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace geometricallyUnipotentPointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

attribute [local instance 1100] Module.Free.of_divisionRing

private theorem coefficientMatrix_charpoly_eq
    {A : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k A] [IsReduced A]
    (hA : geometricallyUnipotentPointsCommHopfAlgProperty k A)
    (M : FGComoduleCat.{u, v, u} k A) {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : _root_.Module.Basis ι k M) :
    (Comodule.coefficientMatrix (C := A) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map
        (algebraMap k A) := by
  let C := Comodule.coefficientMatrix (C := A) b
  let P : Polynomial k := (Polynomial.X - 1) ^ Module.finrank k M
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hA
  apply Polynomial.ext
  intro r
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := AlgebraicClosure k)
  intro q
  have hq := (HopfAlgebra.isUnipotentPoint_def (WithConv.toConv q)).mp
    (hA (WithConv.toConv q)) M
  have hqcharpoly : (Comodule.endOfPoint M q).charpoly =
      P.map (algebraMap k (AlgebraicClosure k)) := by
    have hcoe :
        ((LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction M (WithConv.toConv q))) : Module.End _ _) =
            Comodule.endOfPoint M q :=
      Comodule.pointsAction_toLinearMap M (WithConv.toConv q)
    rw [← hcoe]
    have hcharpoly := (LinearMap.GeneralLinearGroup.isUnipotent_iff_charpoly _).mp hq
    rw [Module.finrank_baseChange] at hcharpoly
    exact hcharpoly.trans (by simp [P])
  have hmatrix : C.map q =
      LinearMap.toMatrix (b.baseChange (AlgebraicClosure k))
        (b.baseChange (AlgebraicClosure k)) (Comodule.endOfPoint M q) := by
    rw [Comodule.toMatrix_endOfPoint]
  rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M q)
    (b.baseChange (AlgebraicClosure k)), ← hmatrix] at hqcharpoly
  calc
    q (C.charpoly.coeff r) = (C.charpoly.map q).coeff r := by
      exact (Polynomial.coeff_map q.toRingHom r).symm
    _ = (C.map q).charpoly.coeff r :=
      congrArg (fun p ↦ p.coeff r) (Matrix.charpoly_map C q.toRingHom).symm
    _ = (P.map (algebraMap k (AlgebraicClosure k))).coeff r :=
      congrArg (fun p ↦ p.coeff r) hqcharpoly
    _ = q ((P.map (algebraMap k A)).coeff r) := by
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact (q.commutes (P.coeff r)).symm

private theorem isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq
    {A : _root_.CommHopfAlgCat.{v} k} {L : Type w} [CommRing L] [Algebra k L]
    (M : FGComoduleCat.{u, v, u} k A) (g : WithConv (A →ₐ[k] L))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : _root_.Module.Basis ι k M)
    (hCcharpoly : (Comodule.coefficientMatrix (C := A) b).charpoly =
      ((Polynomial.X - (1 : Polynomial k)) ^ Module.finrank k M).map
        (algebraMap k A)) :
    LinearMap.GeneralLinearGroup.IsUnipotent
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
  let C := Comodule.coefficientMatrix (C := A) b
  let d := Module.finrank k M
  let P : Polynomial k := (Polynomial.X - 1) ^ d
  have hgcharpoly : (Comodule.endOfPoint M g.ofConv).charpoly =
      P.map (algebraMap k L) := by
    let e : A →ₐ[k] A := AlgHom.id k A
    calc
      (Comodule.endOfPoint M g.ofConv).charpoly =
          (Comodule.endOfPoint M e).charpoly.map g.ofConv := by
        simpa only [e, AlgHom.comp_id] using
          (Comodule.charpoly_endOfPoint_comp e g.ofConv)
      _ = C.charpoly.map g.ofConv := by
        congr 1
        rw [← LinearMap.charpoly_toMatrix (Comodule.endOfPoint M e) (b.baseChange A),
          Comodule.toMatrix_endOfPoint]
        exact congrArg Matrix.charpoly (by
          simpa only [e, AlgHom.coe_id] using Matrix.map_id C)
      _ = _ := by
        rw [hCcharpoly, Polynomial.map_map]
        congr 1
        ext x
        exact g.ofConv.commutes x
  apply LinearMap.GeneralLinearGroup.isUnipotent_of_charpoly_eq (n := d)
  have hcoe :
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End _ _) = Comodule.endOfPoint M g.ofConv :=
    Comodule.pointsAction_toLinearMap M g
  rw [hcoe]
  exact hgcharpoly.trans (by simp [P])

/-- If a reduced finite-type Hopf algebra is geometrically unipotent, every point valued in any
commutative algebra over the ground field is unipotent. In particular, the defining hypothesis
over the chosen algebraic closure implies unipotence for points over every other algebraically
closed extension. -/
theorem isUnipotentPoint
    {A : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k A] [IsReduced A]
    (hA : geometricallyUnipotentPointsCommHopfAlgProperty k A)
    {L : Type w} [CommRing L] [Algebra k L]
    (g : WithConv (A →ₐ[k] L)) : HopfAlgebra.IsUnipotentPoint g := by
  rw [HopfAlgebra.isUnipotentPoint_def]
  intro M
  let b := Module.Free.chooseBasis k M
  exact isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq M g b
    (coefficientMatrix_charpoly_eq hA M b)

/-- A reduced finite-type Hopf algebra is geometrically unipotent if and only if every point
valued in any fixed algebraically closed extension is unipotent. -/
theorem iff_forall_isUnipotentPoint
    {A : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k A] [IsReduced A]
    (L : Type w) [Field L] [Algebra k L] [IsAlgClosed L] :
    geometricallyUnipotentPointsCommHopfAlgProperty k A ↔
      ∀ g : WithConv (A →ₐ[k] L), HopfAlgebra.IsUnipotentPoint g := by
  constructor
  · intro hA g
    exact isUnipotentPoint hA g
  · intro hL
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    intro g
    let φ : AlgebraicClosure k →ₐ[k] L := IsAlgClosed.lift
    exact (HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g φ φ.injective).mp
      (hL (AlgHom.mapValue (H := A) φ g))

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
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at ⊢
  intro g
  rw [HopfAlgebra.isUnipotentPoint_def]
  intro M
  let b := Module.Free.chooseBasis k M
  let C := Comodule.coefficientMatrix (C := H) b
  let d := Module.finrank k M
  let P : Polynomial k := (Polynomial.X - 1) ^ d
  -- Point separation turns the characteristic polynomial identity at every source point into
  -- an identity for the universal coefficient matrix over the source coordinate algebra.
  let _ : Comodule k K M := Comodule.Corestrict f.hom.toCoalgHom
  let N : FGComoduleCat.{u, v, u} k K := FGComoduleCat.of (R := k) (C := K) M
  have hDcharpoly : (C.map f.hom.toAlgHom.toRingHom).charpoly = P.map (algebraMap k K) := by
    have hcharpoly := coefficientMatrix_charpoly_eq hK N b
    rw [Comodule.coefficientMatrix_corestrict b f.hom.toCoalgHom] at hcharpoly
    have hmap : (f.hom.toCoalgHom : H → K) = f.hom.toAlgHom.toRingHom := by
      ext
      rfl
    simpa only [hmap] using hcharpoly
  -- Injectivity reflects the universal characteristic polynomial identity to the target.
  have hCcharpoly : C.charpoly = P.map (algebraMap k H) := by
    apply Polynomial.map_injective f.hom.toAlgHom.toRingHom hf
    rw [← Matrix.charpoly_map]
    rw [hDcharpoly]
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact (f.hom.toAlgHom.commutes x).symm
  exact isUnipotent_pointsAction_of_coefficientMatrix_charpoly_eq M g b hCcharpoly

end geometricallyUnipotentPointsCommHopfAlgProperty

namespace smoothUnipotentCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {A : FiniteTypeCommHopfAlgCat.{u, v} k}

/-- Every point of a smooth geometrically unipotent affine group valued in a commutative algebra
over the ground field is unipotent. -/
theorem isUnipotentPoint
    (hA : smoothUnipotentCommHopfAlgProperty k A)
    {L : Type w} [CommRing L] [Algebra k L]
    (g : WithConv (A →ₐ[k] L)) : HopfAlgebra.IsUnipotentPoint g := by
  have hA' := (smoothUnipotentCommHopfAlgProperty_iff k A).mp hA
  let _ : Algebra.Smooth k A := hA'.1
  let _ : IsReduced A := isReduced_of_smooth_of_field k A
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty k A.obj := by
    rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
    exact hA'.2
  exact geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint
    (A := A.obj) (L := L) hgeom g

/-- A finite-type Hopf algebra is smooth unipotent if and only if it is smooth and every point
valued in any fixed algebraically closed extension is unipotent. -/
theorem iff_smooth_and_forall_isUnipotentPoint
    (L : Type w) [Field L] [Algebra k L] [IsAlgClosed L] :
    smoothUnipotentCommHopfAlgProperty k A ↔
      Algebra.Smooth k A ∧
        ∀ g : WithConv (A →ₐ[k] L), HopfAlgebra.IsUnipotentPoint g := by
  constructor
  · intro hA
    have hA' := (smoothUnipotentCommHopfAlgProperty_iff k A).mp hA
    exact ⟨hA'.1, fun g ↦ isUnipotentPoint hA g⟩
  · rintro ⟨hsm, hL⟩
    let _ : Algebra.Smooth k A := hsm
    let _ : IsReduced A := isReduced_of_smooth_of_field k A
    rw [smoothUnipotentCommHopfAlgProperty_iff]
    refine ⟨hsm, ?_⟩
    exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff k A.obj).mp
      ((geometricallyUnipotentPointsCommHopfAlgProperty.iff_forall_isUnipotentPoint
        (A := A.obj) L).mpr hL)

end smoothUnipotentCommHopfAlgProperty

end TauCeti
