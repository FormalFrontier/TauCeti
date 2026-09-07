/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.AlgebraicGeometry.Group.Smooth
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange

/-!
# Smooth affine groups over algebraically closed fields

A reduced group scheme locally of finite type over an algebraically closed field is smooth.
For finite-type commutative Hopf algebras this gives the particularly useful coordinate
criterion

```text
smooth over an algebraically closed field ↔ reduced coordinate ring.
```

These criteria let downstream constructions establish the ring-theoretic condition of ordinary
reducedness instead of proving smoothness directly. The geometric-reducedness criterion also
supplies the resulting stability under field extension when affine groups and their subgroup
schemes are compared after base change.

## Main declarations

* `TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced`: the
  scheme-theoretic criterion.
* `TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced`: a reduced finite-type
  commutative Hopf algebra over an algebraically closed field is smooth.
* `TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: the coordinate smoothness
  criterion.
* `TauCeti.geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: over an
  algebraically closed field, ordinary and geometric reducedness agree for finite-type
  commutative Hopf algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

-- The group-scheme argument is adapted from the private algebraically-closed-field lemma underlying
-- `AlgebraicGeometry.smooth_of_grpObj` in Mathlib.

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open _root_.AlgebraicGeometry

universe u v

noncomputable section

/-- **A reduced finite-type commutative Hopf algebra over an algebraically closed field is
smooth.** -/
theorem smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] [IsReduced H] :
    smoothCommHopfAlgProperty k H := by
  let K : Type (max u v) := AlgebraicClosure (ULift.{v} k)
  let _ : Algebra k K := Algebra.compHom K (algebraMap k (ULift.{v} k))
  let _ : IsScalarTower k (ULift.{v} k) K := IsScalarTower.of_algebraMap_eq' rfl
  have hIntegralMap :
      ((algebraMap (ULift.{v} k) K).comp
        (algebraMap k (ULift.{v} k))).IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (ULift.algEquiv (R := k) (A := k)).symm.surjective)
      (Algebra.IsIntegral.isIntegral (R := ULift.{v} k))
  let _ : Algebra.IsIntegral k K := ⟨by
    change ((algebraMap (ULift.{v} k) K).comp
      (algebraMap k (ULift.{v} k))).IsIntegral
    exact hIntegralMap⟩
  have hMap : Function.Bijective (algebraMap k K) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hInclude : Function.Bijective
      (Algebra.TensorProduct.includeRight : H →ₐ[k] (K ⊗[k] H)) :=
    Algebra.TensorProduct.includeRight_bijective hMap
  let e : H ≃ₐ[k] (K ⊗[k] H) :=
    AlgEquiv.ofBijective Algebra.TensorProduct.includeRight hInclude
  let _ : IsReduced (K ⊗[k] H) :=
    isReduced_of_injective e.symm.toRingHom e.symm.injective
  let HK := CommHopfAlgCat.baseChange (K := K) H
  have hSmooth : smoothCommHopfAlgProperty K HK := by
    let _ : Algebra.FiniteType K HK := inferInstance
    let _ : LocallyOfFiniteType
        (((hopfSpec (CommRingCat.of K)).obj (Opposite.op HK)).X.hom) :=
      (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec K HK).mp inferInstance
    let _ : IsReduced ((hopfSpec (CommRingCat.of K)).obj (Opposite.op HK)).X.left :=
      by
        rw [hopfSpec_obj_X_left]
        rw [affine_isReduced_iff]
        infer_instance
    let _ : GrpObj
        (Over.mk (((hopfSpec (CommRingCat.of K)).obj (Opposite.op HK)).X.hom)) :=
      inferInstanceAs (GrpObj ((hopfSpec (CommRingCat.of K)).obj (Opposite.op HK)).X)
    apply (algebraSmooth_iff_smooth_hopfSpec K HK).mpr
    rw [smoothAffineGroupSchemeProperty_iff]
    exact AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced _
  rw [smoothCommHopfAlgProperty_iff] at hSmooth ⊢
  let _ : Algebra.Smooth K (K ⊗[k] H) := hSmooth
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

/-- For a finite-type commutative Hopf algebra over an algebraically closed field, smoothness is
equivalent to reducedness of its coordinate ring. -/
theorem smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] :
    smoothCommHopfAlgProperty k H ↔ IsReduced H := by
  constructor
  · intro hH
    let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff H).mp hH
    exact isReduced_of_smooth_of_field k H
  · intro hH
    let _ : IsReduced H := hH
    exact smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k H

/-- Over an algebraically closed field, a finite-type commutative Hopf algebra is geometrically
reduced exactly when its coordinate ring is reduced. -/
theorem geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{v} k)
    [Algebra.FiniteType k H] :
    geometricallyReducedCommHopfAlgProperty k H ↔ IsReduced H := by
  rw [← smoothCommHopfAlgProperty_iff_geometricallyReduced,
    smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed]

end

end TauCeti
