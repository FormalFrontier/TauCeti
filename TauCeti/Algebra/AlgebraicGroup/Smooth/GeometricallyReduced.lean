/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness of geometrically reduced affine groups

For a commutative Hopf algebra `H` over a field `k`, geometric reducedness means that every
field extension `K / k` gives a reduced coordinate ring `H ⊗[k] K`. This file compares that
coordinate condition with Mathlib's scheme-theoretic `GeometricallyReduced` predicate on the
structural morphism of `Spec H`.

Mathlib proves that a geometrically reduced group scheme locally of finite type over a field is
smooth. Transporting that theorem through Tau Ceti's affine Hopf/group-scheme dictionary gives
the coordinate criterion

```text
finite type + geometrically reduced ⇒ smooth.
```

The finite-type hypothesis is kept separate throughout. In particular, neither geometric
reducedness nor smoothness is built into the category of commutative Hopf algebras.

Mathlib's `Algebra.IsGeometricallyReduced` tests the base change to algebraic closures of residue
fields. Its source currently lists equivalence with reducedness after arbitrary field extension
as a TODO. The all-extension condition used here is chosen because it agrees directly with the
scheme-theoretic predicate; `geometricallyReducedCommHopfAlgProperty.isGeometricallyReduced`
records the implication to Mathlib's existing algebra predicate.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlgProperty`: geometric reducedness after every field
  extension.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.isGeometricallyReduced`: comparison with
  Mathlib's algebra predicate.
* `TauCeti.geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec`: agreement with
  scheme-theoretic geometric reducedness.
* `TauCeti.smoothCommHopfAlgProperty_of_geometricallyReduced`: a finite-type geometrically
  reduced commutative Hopf algebra over a field is smooth.
* `TauCeti.finiteType_inf_geometricallyReduced_le_smooth`: the same implication as an inequality
  of object properties.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap. The scheme-theoretic input is Mathlib's `AlgebraicGeometry.smooth_of_grpObj`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

noncomputable section

/-- A commutative Hopf algebra over a field is geometrically reduced when its coordinate ring
remains reduced after every extension of the base field. -/
def geometricallyReducedCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{u} k) :=
  fun H ↦ ∀ (K : Type u) [Field K] [Algebra k K],
    IsReduced ((H : Type u) ⊗[k] K)

/-- Membership in the geometrically reduced commutative-Hopf-algebra object property. -/
@[simp]
theorem geometricallyReducedCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyReducedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsReduced ((H : Type u) ⊗[k] K) :=
  Iff.rfl

/-- A geometrically reduced commutative Hopf algebra has reduced coordinate ring over its base
field. -/
theorem geometricallyReducedCommHopfAlgProperty.isReduced
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    IsReduced H := by
  let _ : IsReduced ((H : Type u) ⊗[k] k) := hH k
  exact isReduced_of_injective (Algebra.TensorProduct.rid k k H).symm.toRingHom
    (Algebra.TensorProduct.rid k k H).symm.injective

/-- The all-extension coordinate condition implies Mathlib's algebraic geometric-reducedness
predicate, which over a field tests the base change to an algebraic closure. -/
theorem geometricallyReducedCommHopfAlgProperty.isGeometricallyReduced
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    Algebra.IsGeometricallyReduced k H := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let _ : IsReduced ((H : Type u) ⊗[k] AlgebraicClosure k) := hH (AlgebraicClosure k)
  exact isReduced_of_injective
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) H).toRingHom
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) H).injective

/-- Geometric reducedness is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallyReducedCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    rw [geometricallyReducedCommHopfAlgProperty_iff] at hH ⊢
    intro K _ _
    let _ := hH K
    let eK := Algebra.TensorProduct.congr
      (CommHopfAlgCat.ofIso e).toAlgEquiv (AlgEquiv.refl : K ≃ₐ[k] K)
    exact isReduced_of_injective eK.symm.toRingHom eK.symm.injective

/-- **Geometric reducedness agrees across the affine-group-scheme and coordinate-ring models.**
The structural morphism of a Hopf spectrum is geometrically reduced if and only if every field
extension of its coordinate algebra is reduced. -/
theorem geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyReducedCommHopfAlgProperty k H ↔
      GeometricallyReduced
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  let : MorphismProperty.RespectsIso @GeometricallyReduced :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyReducedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyReduced) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let _ : IsReduced ((H : Type u) ⊗[k] K) := h K
    have : IsReduced (Spec (CommRingCat.of ((H : Type u) ⊗[k] K))) := inferInstance
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k H K).hom
  · intro h K _ _
    let _ : IsReduced
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k H)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := h K
    have : IsReduced (Spec (CommRingCat.of ((H : Type u) ⊗[k] K))) :=
      isReduced_of_isOpenImmersion (pullbackSpecIso k H K).inv
    exact (affine_isReduced_iff (CommRingCat.of ((H : Type u) ⊗[k] K))).mp this

/-- **A finite-type geometrically reduced commutative Hopf algebra over a field is smooth.**

This is the coordinate-algebra form of Mathlib's `AlgebraicGeometry.smooth_of_grpObj`. The
finite-type comparison supplies local finite type for the structural morphism of the Hopf
spectrum, and the geometric-reducedness comparison supplies its other hypothesis. -/
theorem smoothCommHopfAlgProperty_of_geometricallyReduced
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H]
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    smoothCommHopfAlgProperty k H := by
  let _ : LocallyOfFiniteType
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance
  let _ : GeometricallyReduced
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec k H).mp hH
  let _ : GrpObj
      (Over.mk (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom)) :=
    inferInstanceAs (GrpObj ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X)
  apply (algebraSmooth_iff_smooth_hopfSpec k H).mpr
  rw [smoothAffineGroupSchemeProperty_iff]
  exact smooth_of_grpObj _

/-- Among commutative Hopf algebras over a field, finite type together with geometric
reducedness implies smoothness. -/
theorem finiteType_inf_geometricallyReduced_le_smooth (k : Type u) [Field k] :
    finiteTypeCommHopfAlgProperty k ⊓ geometricallyReducedCommHopfAlgProperty k ≤
      smoothCommHopfAlgProperty k := by
  intro H hH
  let _ : Algebra.FiniteType k H := hH.1
  exact smoothCommHopfAlgProperty_of_geometricallyReduced k H hH.2

end

end TauCeti
