/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Commutator
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

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
commutator image. Every algebra-valued commutator belongs to its subgroup of points. Consequently,
a normal closed subgroup contains the derived subgroup exactly when all of its algebra-valued
point-group quotients are commutative. If the coordinate Hopf algebra is cocommutative, the
derived subgroup is trivial.

## Main declarations

* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal`: the ideal cutting out the derived subgroup.
* `TauCeti.CommHopfAlgCat.derivedGroupScheme`: the derived affine group scheme.
* `TauCeti.CommHopfAlgCat.commutator_mem_derivedPointsSubgroup`: every pointwise commutator lies
  in the derived subgroup.
* `TauCeti.CommHopfAlgCat.isNormal_derivedDefiningIdeal`: the derived subgroup is normal.
* `TauCeti.CommHopfAlgCat.le_derivedDefiningIdeal_iff_isMulCommutative_pointQuotient`: the
  universal property of the derived closed subgroup.
* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_of_isCocomm`: a commutative affine
  group's derived subgroup is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, especially Propositions 6.17 and 6.18.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

This supplies `G_der`, required in Layer 6 of the ReductiveGroups roadmap, and the
scheme-theoretic derived subgroup left outstanding by the Layer 5 solvability development.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

section DefiningIdeal

variable {R : Type u} [CommSemiring R]
variable (H : Type v) [CommSemiring H] [_root_.HopfAlgebra R H]

/-- The largest Hopf ideal contained in the kernel of the commutator coordinate morphism.

Its quotient represents the smallest closed subgroup scheme containing the image of the
commutator morphism. -/
noncomputable def derivedDefiningIdeal : HopfIdeal R H :=
  sSup {I | I.toIdeal ≤
    RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom}

/-- The derived defining ideal is killed by the commutator coordinate morphism. -/
theorem derivedDefiningIdeal_toIdeal_le_ker :
    (derivedDefiningIdeal (R := R) H).toIdeal ≤
      RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom := by
  rw [derivedDefiningIdeal, HopfIdeal.sSup_toIdeal]
  exact iSup_le fun I ↦ I.2

/-- A Hopf ideal is contained in the derived defining ideal exactly when the commutator
coordinate morphism kills it. This is the coordinate universal property of the derived
subgroup. -/
@[simp] theorem le_derivedDefiningIdeal_iff (I : HopfIdeal R H) :
    I ≤ derivedDefiningIdeal (R := R) H ↔
      I.toIdeal ≤
        RingHom.ker (HopfAlgebra.commutatorAlgHom (R := R) (H := H)).toRingHom := by
  constructor
  · intro h
    exact (HopfIdeal.toIdeal_le_toIdeal.mpr h).trans
      (derivedDefiningIdeal_toIdeal_le_ker (R := R) H)
  · intro h
    exact le_sSup h

end DefiningIdeal

variable {R : Type u} [CommRing R]

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
    ⁅g, h⁆ ∈ quotientPointsSubgroup H (derivedDefiningIdeal (R := R) H) A := by
  rw [mem_quotientPointsSubgroup_iff]
  intro x hx
  rw [← HopfAlgebra.productMap_comp_commutatorAlgHom]
  exact map_zero (Algebra.TensorProduct.productMap g.ofConv h.ofConv) ▸
    congrArg (Algebra.TensorProduct.productMap g.ofConv h.ofConv)
      (RingHom.mem_ker.mp
        (derivedDefiningIdeal_toIdeal_le_ker (R := R) H ((HopfIdeal.mem_toIdeal).mpr hx)))

/-- The subgroup of algebra-valued points cut out by the derived ideal is normal. -/
theorem derivedPointsSubgroup_normal (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroup H (derivedDefiningIdeal (R := R) H) A).Normal := by
  refine ⟨fun n hn g ↦ ?_⟩
  simpa [commutatorElement_def, mul_assoc] using
    (quotientPointsSubgroup H (derivedDefiningIdeal (R := R) H) A).mul_mem
      (commutator_mem_derivedPointsSubgroup H A g n) hn

/-- Every Hopf ideal contained in the derived defining ideal is normal. -/
theorem isNormal_of_le_derivedDefiningIdeal (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hID : I ≤ derivedDefiningIdeal (R := R) H) : I.IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  apply Subgroup.Normal.of_commutator_le
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨g, h, rfl⟩
  exact mem_quotientPointsSubgroup_of_le H hID A
    (commutator_mem_derivedPointsSubgroup H A g h)

/-- The Hopf ideal defining the derived subgroup is normal. -/
theorem isNormal_derivedDefiningIdeal (H : _root_.CommHopfAlgCat.{v} R) :
    (derivedDefiningIdeal (R := R) H).IsNormal :=
  isNormal_of_le_derivedDefiningIdeal H _ le_rfl

/-- If a closed subgroup contains the derived subgroup, the corresponding quotient of every
algebra-valued point group is commutative. -/
theorem isMulCommutative_pointQuotient_of_le_derivedDefiningIdeal
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
    (hID : I ≤ derivedDefiningIdeal (R := R) H) (A : CommAlgCat.{w} R) :
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I (isNormal_of_le_derivedDefiningIdeal H I hID) A
    IsMulCommutative
      (HopfAlgebra.points (R := R) (H := H) A ⧸ quotientPointsSubgroup H I A) := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I (isNormal_of_le_derivedDefiningIdeal H I hID) A
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_eq_closure,
    Subgroup.closure_le]
  rintro _ ⟨g, h, rfl⟩
  exact mem_quotientPointsSubgroup_of_le H hID A
    (commutator_mem_derivedPointsSubgroup H A g h)

/-- A closed subgroup contains the derived subgroup exactly when it is normal and all of the
corresponding point-group quotients are commutative. The converse needs no point-separation or
rational-point hypothesis. -/
theorem le_derivedDefiningIdeal_iff_isMulCommutative_pointQuotient
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    I ≤ derivedDefiningIdeal (R := R) H ↔
      ∃ hI : I.IsNormal,
        ∀ A : CommAlgCat.{max v w} R,
          let _ : (quotientPointsSubgroup H I A).Normal :=
            quotientPointsSubgroup_normal H I hI A
          IsMulCommutative
            (HopfAlgebra.points (R := R) (H := H) A ⧸ quotientPointsSubgroup H I A) := by
  constructor
  · intro hID
    refine ⟨isNormal_of_le_derivedDefiningIdeal H I hID, fun A ↦ ?_⟩
    exact isMulCommutative_pointQuotient_of_le_derivedDefiningIdeal H I hID A
  · rintro ⟨hI, hquot⟩
    rw [le_derivedDefiningIdeal_iff]
    intro x hx
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    let A : CommAlgCat.{max v w} R :=
      CommAlgCat.of R (ULift.{max v w} (H ⊗[R] H))
    let up : (H ⊗[R] H) →ₐ[R] A := ULift.algEquiv.symm.toAlgHom
    let g : HopfAlgebra.points (R := R) (H := H) A :=
      toConv (up.comp (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom)
    let h : HopfAlgebra.points (R := R) (H := H) A :=
      toConv (up.comp (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom)
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    have hcomm : _root_.commutator (HopfAlgebra.points (R := R) (H := H) A) ≤
        quotientPointsSubgroup H I A :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp (hquot A)
    have hmem : ⁅g, h⁆ ∈ quotientPointsSubgroup H I A :=
      Subgroup.commutator_le.mp hcomm g (Subgroup.mem_top g) h (Subgroup.mem_top h)
    rw [mem_quotientPointsSubgroup_iff] at hmem
    have hzero := hmem x hx
    have hproduct : Algebra.TensorProduct.productMap g.ofConv h.ofConv =
        up := by
      simp [g, h, AffineGroup.Product.productMap_restrict]
    have heval := DFunLike.congr_fun
      (HopfAlgebra.productMap_comp_commutatorAlgHom g h) x
    rw [hproduct] at heval
    apply (ULift.algEquiv (R := R)).symm.injective
    simpa only [A, up, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, map_zero] using
      heval.trans hzero

section Commutative

variable (H : Type v) [CommRing H] [_root_.HopfAlgebra R H]

/-- The derived subgroup of a commutative affine group is trivial. For coordinate Hopf algebras,
commutativity of the represented group is cocommutativity of the coalgebra structure. -/
@[simp]
theorem derivedDefiningIdeal_eq_augmentation_of_isCocomm [Coalgebra.IsCocomm R H] :
    derivedDefiningIdeal (R := R) H = HopfIdeal.augmentation R H := by
  apply le_antisymm
  · exact (derivedDefiningIdeal (R := R) H).le_augmentation
  · rw [le_derivedDefiningIdeal_iff]
    intro x hx
    have hx' : x ∈ HopfIdeal.augmentation R H := (HopfIdeal.mem_toIdeal).mp hx
    rw [HopfIdeal.mem_augmentation] at hx'
    rw [RingHom.mem_ker]
    have hcommutator :
        toConv (HopfAlgebra.commutatorAlgHom (R := R) (H := H)) = 1 := by
      rw [HopfAlgebra.toConv_commutatorAlgHom]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have heval := congrArg
      (fun f : WithConv (H →ₐ[R] H ⊗[R] H) ↦ f.ofConv x) hcommutator
    simpa [AlgHom.convOne_apply, hx'] using heval

end Commutative

end TauCeti.CommHopfAlgCat
