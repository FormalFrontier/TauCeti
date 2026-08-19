/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# The derived subgroup and abelian quotients

The derived closed subgroup of an affine group is characterized by the same universal property as
the abstract commutator subgroup. If `I` is a normal Hopf ideal of a commutative Hopf algebra `H`,
then the derived subgroup is contained in the closed subgroup cut out by `I` exactly when, over
every commutative value algebra `A`, the quotient of `H(A)` by the `I`-points is commutative.

The reverse implication is tested on one universal value algebra, `H ⊗ H`. Its two tensor-factor
points evaluate the coordinate commutator morphism without losing information. This avoids any
density or rational-point hypothesis.

As an application, a cocommutative coordinate Hopf algebra represents a commutative affine group,
so its derived subgroup is trivial: the derived defining ideal is the augmentation ideal.

## Main declarations

* `TauCeti.CommHopfAlgCat.le_derivedDefiningIdeal_iff_isMulCommutative_pointQuotient`: the
  universal property of the derived closed subgroup.
* `TauCeti.CommHopfAlgCat.derivedDefiningIdeal_eq_augmentation_of_isCocomm`: a commutative affine
  group's derived subgroup is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

This supplies the abelianization property of `G_der` required by Layer 6, "Reductive and
semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]

section UniversalProperty

variable (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)

/-- If a normal closed subgroup contains the derived subgroup, the corresponding quotient of
every algebra-valued point group is commutative. -/
theorem isMulCommutative_pointQuotient_of_le_derivedDefiningIdeal
    (hI : I.IsNormal) (hID : I ≤ derivedDefiningIdeal (R := R) H)
    (A : CommAlgCat.{w} R) :
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    IsMulCommutative
      (HopfAlgebra.points (R := R) (H := H) A ⧸ quotientPointsSubgroup H I A) := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_eq_closure,
    Subgroup.closure_le]
  rintro _ ⟨g, h, rfl⟩
  refine (mem_quotientPointsSubgroup_iff H I A ⁅g, h⁆).2 ?_
  intro x hx
  rw [← HopfAlgebra.productMap_comp_commutatorAlgHom]
  have hzero : HopfAlgebra.commutatorAlgHom (R := R) (H := H) x = 0 :=
    RingHom.mem_ker.mp
      (derivedDefiningIdeal_toIdeal_le_ker (R := R) H
        ((HopfIdeal.mem_toIdeal).mpr (hID hx)))
  exact map_zero (Algebra.TensorProduct.productMap g.ofConv h.ofConv) ▸
    congrArg (Algebra.TensorProduct.productMap g.ofConv h.ofConv) hzero

/-- A normal closed subgroup contains the derived subgroup exactly when all of the corresponding
point-group quotients are commutative.

The converse needs no point-separation hypothesis: it is enough to use the two universal points
with values in `H ⊗ H`. -/
theorem le_derivedDefiningIdeal_iff_isMulCommutative_pointQuotient (hI : I.IsNormal) :
    I ≤ derivedDefiningIdeal (R := R) H ↔
      ∀ A : CommAlgCat.{v} R,
        let _ : (quotientPointsSubgroup H I A).Normal :=
          quotientPointsSubgroup_normal H I hI A
        IsMulCommutative
          (HopfAlgebra.points (R := R) (H := H) A ⧸ quotientPointsSubgroup H I A) := by
  constructor
  · intro hID A
    exact isMulCommutative_pointQuotient_of_le_derivedDefiningIdeal H I hI hID A
  · intro hquot
    rw [le_derivedDefiningIdeal_iff]
    intro x hx
    rw [RingHom.mem_ker]
    -- The universal property exposes the kernel through the underlying ring homomorphism;
    -- restate evaluation through the defining algebra homomorphism before using universal points.
    change HopfAlgebra.commutatorAlgHom (R := R) (H := H) x = 0
    let A : CommAlgCat.{v} R := CommAlgCat.of R (H ⊗[R] H)
    let g : HopfAlgebra.points (R := R) (H := H) A :=
      toConv (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom
    let h : HopfAlgebra.points (R := R) (H := H) A :=
      toConv (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom
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
        AlgHom.id R (H ⊗[R] H) := by
      simpa [g, h] using
        (AffineGroup.Product.productMap_restrict (AlgHom.id R (H ⊗[R] H)))
    have heval := DFunLike.congr_fun
      (HopfAlgebra.productMap_comp_commutatorAlgHom g h) x
    rw [hproduct] at heval
    simpa only [A, AlgHom.comp_apply, AlgHom.id_apply] using heval.trans hzero

end UniversalProperty

section Commutative

variable (H : _root_.CommHopfAlgCat.{v} R)

/-- The derived subgroup of a commutative affine group is trivial.

For coordinate Hopf algebras, commutativity of the represented group is cocommutativity of the
coalgebra structure. The two universal tensor-factor points then commute, so their commutator is
the identity point and the derived defining ideal is the augmentation ideal. -/
theorem derivedDefiningIdeal_eq_augmentation_of_isCocomm [Coalgebra.IsCocomm R H] :
    derivedDefiningIdeal (R := R) H = HopfIdeal.augmentation R H := by
  apply le_antisymm
  · intro x hx
    rw [HopfIdeal.mem_augmentation]
    exact (derivedDefiningIdeal (R := R) H).counit_eq_zero hx
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
