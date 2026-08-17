/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The derived subgroup of an affine group scheme

Let `H` be a commutative Hopf algebra, representing an affine group scheme `G`. The commutator
morphism `G × G ⟶ G` need not be a group homomorphism, so its image is not directly represented by
a quotient Hopf algebra. Instead, this file defines `derivedDefiningIdeal H` to be the largest
Hopf ideal contained in the kernel of the commutator coordinate morphism

```text
H ⟶ H ⊗[R] H.
```

The quotient by this ideal represents the smallest closed subgroup scheme of `G` containing the
commutator image. Every algebra-valued commutator belongs to its subgroup of points. This makes
the subgroup normal and makes the pointwise quotient commutative.

## Main declarations

* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal`: the ideal cutting out the derived subgroup.
* `TauCeti.CommHopfAlgCat.derivedGroupScheme`: the derived affine group scheme.
* `TauCeti.CommHopfAlgCat.commutator_mem_derivedPointsSubgroup`: every pointwise commutator lies
  in the derived subgroup.
* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal_isNormal`: the derived subgroup is normal.
* `TauCeti.CommHopfAlgCat.isMulCommutative_derivedPointQuotient`: the quotient by derived points is
  commutative.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, especially Propositions 6.17 and 6.18.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

This supplies `G_der`, required in Layer 6 of the ReductiveGroups roadmap, and the
scheme-theoretic derived subgroup left outstanding by the Layer 5 solvability development.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]

/-- The largest Hopf ideal contained in the kernel of the commutator coordinate morphism.

Its quotient represents the smallest closed subgroup scheme containing the image of the
commutator morphism. -/
noncomputable def derivedDefiningIdeal (H : _root_.CommHopfAlgCat.{v} R) : HopfIdeal R H :=
  sSup {I | I.toIdeal ≤
    RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom}

/-- The derived defining ideal is killed by the commutator coordinate morphism. -/
theorem derivedDefiningIdeal_toIdeal_le_ker (H : _root_.CommHopfAlgCat.{v} R) :
    (derivedDefiningIdeal H).toIdeal ≤
      RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom := by
  rw [derivedDefiningIdeal, HopfIdeal.sSup_toIdeal]
  exact iSup_le fun I ↦ I.2

/-- A Hopf ideal is contained in the derived defining ideal exactly when the commutator
coordinate morphism kills it. This is the coordinate universal property of the derived
subgroup. -/
theorem le_derivedDefiningIdeal_iff (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    I ≤ derivedDefiningIdeal H ↔
      I.toIdeal ≤
        RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom := by
  constructor
  · intro h
    exact (HopfIdeal.toIdeal_le_toIdeal.mpr h).trans
      (derivedDefiningIdeal_toIdeal_le_ker H)
  · intro h
    exact le_sSup h

/-- The affine group scheme represented by the coordinate algebra of the derived subgroup. -/
noncomputable abbrev derivedGroupScheme (H : _root_.CommHopfAlgCat.{u} R) :
    Grp (Over (AlgebraicGeometry.Spec (CommRingCat.of R))) :=
  quotientSpec H (derivedDefiningIdeal H)

/-- The closed immersion of the derived group scheme into the ambient Hopf spectrum. -/
noncomputable abbrev derivedGroupSchemeι (H : _root_.CommHopfAlgCat.{u} R) :
    derivedGroupScheme H ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj (Opposite.op H) :=
  quotientSpecι H (derivedDefiningIdeal H)

/-- The inclusion of the derived group scheme is a closed immersion. -/
instance isClosedImmersion_derivedGroupSchemeι (H : _root_.CommHopfAlgCat.{u} R) :
    AlgebraicGeometry.IsClosedImmersion (derivedGroupSchemeι H).hom.hom.left :=
  inferInstance

/-- Every commutator of algebra-valued points lies in the derived subgroup. -/
theorem commutator_mem_derivedPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) (g h : HopfAlgebra.points (R := R) (H := H) A) :
    ⁅g, h⁆ ∈ quotientPointsSubgroup H (derivedDefiningIdeal H) A := by
  rw [mem_quotientPointsSubgroup_iff]
  intro x hx
  rw [← HopfAlgebra.productMap_comp_commutatorAlgHom]
  exact map_zero (Algebra.TensorProduct.productMap g.ofConv h.ofConv) ▸
    congrArg (Algebra.TensorProduct.productMap g.ofConv h.ofConv)
      (RingHom.mem_ker.mp
        (derivedDefiningIdeal_toIdeal_le_ker H ((HopfIdeal.mem_toIdeal).mpr hx)))

/-- The subgroup of algebra-valued points cut out by the derived ideal is normal. -/
theorem derivedPointsSubgroup_normal (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroup H (derivedDefiningIdeal H) A).Normal := by
  refine ⟨fun n hn g ↦ ?_⟩
  simpa [commutatorElement_def, mul_assoc] using
    (quotientPointsSubgroup H (derivedDefiningIdeal H) A).mul_mem
      (commutator_mem_derivedPointsSubgroup H A g n) hn

/-- The Hopf ideal defining the derived subgroup is normal. -/
theorem derivedDefiningIdeal_isNormal (H : _root_.CommHopfAlgCat.{v} R) :
    (derivedDefiningIdeal H).IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal]
  exact derivedPointsSubgroup_normal H

/-- The quotient of the point group by the derived subgroup is commutative. -/
theorem isMulCommutative_derivedPointQuotient (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    let _ : (quotientPointsSubgroup H (derivedDefiningIdeal H) A).Normal :=
      derivedPointsSubgroup_normal H A
    IsMulCommutative
      (HopfAlgebra.points (R := R) (H := H) A ⧸
        quotientPointsSubgroup H (derivedDefiningIdeal H) A) := by
  let _ : (quotientPointsSubgroup H (derivedDefiningIdeal H) A).Normal :=
    derivedPointsSubgroup_normal H A
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_eq_closure,
    Subgroup.closure_le]
  rintro _ ⟨g, h, rfl⟩
  exact commutator_mem_derivedPointsSubgroup H A g h

end TauCeti.CommHopfAlgCat
