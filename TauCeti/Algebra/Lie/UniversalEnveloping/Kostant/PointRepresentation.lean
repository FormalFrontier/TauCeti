/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic

/-!
# Kostant root subgroups as natural point representations

The divided-power exponential attached to a nilpotent root-vector action gives a homomorphism
from `𝔾ₐ(A)` to the automorphisms of `A ⊗[ℤ] M` for every commutative `ℤ`-algebra `A`.
This file packages those homomorphisms and their value-ring naturality as a
`HopfAlgebra.PointRepresentation`. The representation--comodule correspondence then recovers the
coordinate-side polynomial coaction

```text
m ↦ ∑ₙ D⁽ⁿ⁾(m) ⊗ Xⁿ.
```

Once integral PBW supplies a finite free admissible lattice, a basis turns this point
representation into the natural matrix-valued map used to recover the root-subgroup scheme
morphism `𝔾ₐ → GLₙ`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPointRepresentation`: the natural point
  representation of `𝔾ₐ` defined by the Kostant exponential.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupComodule`: the polynomial comodule
  recovered from that natural action.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupComodule_coact`: the explicit
  divided-power formula for its coaction.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {iota : Type w} {kappa : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : iota → L) (h : kappa → L)
variable (rho : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, rho u m ∈ M)
variable (i : iota)
variable (hnil : IsNilpotent (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

private noncomputable def kostantRootSubgroupPointAction (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) A ⟶
      GeneralLinear.scalarExtensionAutomorphisms (V := M) A :=
  GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil)

private theorem kostantRootSubgroupPointAction_naturality
    {A B : CommAlgCat.{v} ℤ} (phi : A ⟶ B)
    (f : HopfAlgebra.points (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) phi
        (kostantRootSubgroupPointAction
          (e := e) (h := h) (rho := rho) M hM i hnil A f) =
      kostantRootSubgroupPointAction
          (e := e) (h := h) (rho := rho) M hM i hnil B
        (HopfAlgebra.mapPoints (H := SymmetricAlgebra ℤ ℤ) phi f) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    (V := M) phi
  intro z
  have hmap (x : A ⊗[ℤ] M) :
      GeneralLinear.scalarExtensionMap (V := M) phi x =
        TensorProduct.map phi.hom.toLinearMap LinearMap.id x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp
    | add x y hx hy => simp [hx, hy]
  rw [hmap z, hmap]
  change
    (kostantRootSubgroupPoints (A := B) e h rho M hM i hnil
        (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) phi.hom f)).val
          (TensorProduct.map phi.hom.toLinearMap LinearMap.id z) =
      TensorProduct.map phi.hom.toLinearMap LinearMap.id
        ((kostantRootSubgroupPoints (A := A) e h rho M hM i hnil f).val z)
  exact (map_kostantRootSubgroupPoints e h rho M hM i hnil phi.hom f z).symm

/-- The natural point representation of `𝔾ₐ` on a Kostant-stable integral module attached to a
nilpotent root-vector action.

Its component over a commutative ring `A` is the divided-power exponential homomorphism
`kostantRootSubgroupPoints`; naturality is the compatibility of that polynomial action with maps
of value rings. -/
noncomputable def kostantRootSubgroupPointRepresentation :
    HopfAlgebra.PointRepresentation
      (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) (V := M) where
  app A := kostantRootSubgroupPointAction
      (e := e) (h := h) (rho := rho) M hM i hnil A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm
  naturality A B phi := by
    change
      HopfAlgebra.mapPoints (H := SymmetricAlgebra ℤ ℤ) phi ≫
          kostantRootSubgroupPointAction
            (e := e) (h := h) (rho := rho) M hM i hnil B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) B).symm =
        kostantRootSubgroupPointAction
          (e := e) (h := h) (rho := rho) M hM i hnil A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := M)).map phi
    have hraw :
        HopfAlgebra.mapPoints (H := SymmetricAlgebra ℤ ℤ) phi ≫
            kostantRootSubgroupPointAction
              (e := e) (h := h) (rho := rho) M hM i hnil B =
          kostantRootSubgroupPointAction
              (e := e) (h := h) (rho := rho) M hM i hnil A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := M) phi := by
      apply GrpCat.ext
      intro f
      exact (kostantRootSubgroupPointAction_naturality
        e h rho M hM i hnil phi f).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private theorem kostantRootSubgroupPointRepresentation_action (A : CommAlgCat.{v} ℤ) :
    (kostantRootSubgroupPointRepresentation
      (V := V) e h rho M hM i hnil).action A =
      kostantRootSubgroupPointAction
        (e := e) (h := h) (rho := rho) M hM i hnil A := by
  rw [HopfAlgebra.PointRepresentation.action_def,
    kostantRootSubgroupPointRepresentation]
  change
    (kostantRootSubgroupPointAction
        (e := e) (h := h) (rho := rho) M hM i hnil A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A) =
        kostantRootSubgroupPointAction
          (e := e) (h := h) (rho := rho) M hM i hnil A
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- On an ordinary commutative ring equipped with its canonical `ℤ`-algebra structure, the
concrete action of the natural point representation is `kostantRootSubgroupPoints`. -/
theorem kostantRootSubgroupPointRepresentation_action_of
    (A : Type v) [CommRing A] :
    (kostantRootSubgroupPointRepresentation
      (V := V) e h rho M hM i hnil).action (CommAlgCat.of ℤ A) =
      GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil) := by
  rw [kostantRootSubgroupPointRepresentation_action]
  rfl

/-- The right `ℤ[X]`-comodule on a Kostant-stable integral module encoded by the natural
root-subgroup action. This is the coordinate-side form of the divided-power exponential. -/
@[instance_reducible]
noncomputable def kostantRootSubgroupComodule : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
  HopfAlgebra.PointRepresentation.toComodule
    (kostantRootSubgroupPointRepresentation e h rho M hM i hnil)

/-- The Kostant root-subgroup coaction is the finite divided-power polynomial
`m ↦ ∑ₙ D⁽ⁿ⁾(m) ⊗ Xⁿ`. -/
@[simp]
theorem kostantRootSubgroupComodule_coact (m : M) :
    (kostantRootSubgroupComodule e h rho M hM i hnil).coact m =
      ∑ n ∈ Finset.range
          (nilpotencyClass (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
        integralDividedPower
            (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
              e h rho hM i n hv) m ⊗ₜ[ℤ]
          ((SymmetricAlgebra.ι ℤ ℤ 1) ^ n) := by
  rw [kostantRootSubgroupComodule,
    HopfAlgebra.PointRepresentation.toComodule_coact_apply,
    kostantRootSubgroupPointRepresentation_action]
  change
    TensorProduct.comm ℤ (SymmetricAlgebra ℤ ℤ) M
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          ((kostantRootSubgroupPoints
            (A := ULift.{v} (SymmetricAlgebra ℤ ℤ)) e h rho M hM i hnil
              (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[ℤ] m))) = _
  rw [kostantRootSubgroupPoints_tmul]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.comm_tmul, AdditiveGroup.toAdd_gaPointsMulEquiv, mul_one]
  rfl

end TauCeti.UniversalEnvelopingAlgebra
