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
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (rho : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, rho u m ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (rho (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

private noncomputable def kostantRootSubgroupPointAction (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) A ⟶
      GeneralLinear.scalarExtensionAutomorphisms (V := M) A :=
  GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil)

private theorem kostantRootSubgroupPointAction_eq (A : CommAlgCat.{v} ℤ) :
    kostantRootSubgroupPointAction
      (e := e) (h := h) (rho := rho) M hM i hnil A =
      GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil) := by
  rfl

@[simp]
private theorem kostantRootSubgroupPointAction_val (A : CommAlgCat.{v} ℤ)
    (f : HopfAlgebra.points (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) A) :
    (kostantRootSubgroupPointAction
      (e := e) (h := h) (rho := rho) M hM i hnil A f).val =
      (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil f).val := by
  rfl

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
  rw [kostantRootSubgroupPointAction_val, kostantRootSubgroupPointAction_val,
    HopfAlgebra.mapPoints_apply]
  simpa only [AlgHom.mapValue_apply] using
    (map_kostantRootSubgroupPoints_algHom e h rho M hM i hnil phi.hom f z).symm

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
    -- The structure-field goal contains the opaque object equalities of both functors, so expose
    -- the concrete point-action groups before applying their public map lemmas.
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

/-- At every categorical value ring, the concrete action is the Kostant root-subgroup point
homomorphism. -/
@[simp]
theorem kostantRootSubgroupPointRepresentation_action (A : CommAlgCat.{v} ℤ) :
    (kostantRootSubgroupPointRepresentation
      (V := V) e h rho M hM i hnil).action A =
      GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil) := by
  rw [HopfAlgebra.PointRepresentation.action_def,
    kostantRootSubgroupPointRepresentation]
  -- `action` inserts the opaque functor-object equality after the component, whose definition
  -- stores its inverse; expose that composite so the two transports can be cancelled.
  change
    (kostantRootSubgroupPointAction
        (e := e) (h := h) (rho := rho) M hM i hnil A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := M) A) =
        GrpCat.ofHom (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil)
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact kostantRootSubgroupPointAction_eq e h rho M hM i hnil A

private theorem kostantRootSubgroupPointRepresentation_action_val
    (A : CommAlgCat.{v} ℤ)
    (f : HopfAlgebra.points (R := ℤ) (H := SymmetricAlgebra ℤ ℤ) A) :
    ((kostantRootSubgroupPointRepresentation
      (V := V) e h rho M hM i hnil).action A f).val =
      (kostantRootSubgroupPoints (A := A) e h rho M hM i hnil f).val := by
  rw [kostantRootSubgroupPointRepresentation_action]
  simp only [GrpCat.hom_ofHom]

/-- The right `ℤ[X]`-comodule on a Kostant-stable integral module encoded by the natural
root-subgroup action. This is the coordinate-side form of the divided-power exponential. -/
@[irreducible]
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
  have hunlift :
      (ULift.algEquiv (R := ℤ) :
          ULift.{v} (SymmetricAlgebra ℤ ℤ) ≃ₐ[ℤ] SymmetricAlgebra ℤ ℤ)
          ((ULift.algEquiv (R := ℤ) :
            ULift.{v} (SymmetricAlgebra ℤ ℤ) ≃ₐ[ℤ] SymmetricAlgebra ℤ ℤ).symm
              (SymmetricAlgebra.ι ℤ ℤ 1)) =
        SymmetricAlgebra.ι ℤ ℤ 1 :=
    (ULift.algEquiv (R := ℤ) :
      ULift.{v} (SymmetricAlgebra ℤ ℤ) ≃ₐ[ℤ] SymmetricAlgebra ℤ ℤ).apply_symm_apply _
  unfold kostantRootSubgroupComodule
  rw [HopfAlgebra.PointRepresentation.toComodule_coact_apply,
    kostantRootSubgroupPointRepresentation_action_val,
    kostantRootSubgroupPoints_tmul]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.comm_tmul, AdditiveGroup.toAdd_gaPointsMulEquiv, mul_one,
    map_pow, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_toAlgHom, hunlift]

end TauCeti.UniversalEnvelopingAlgebra
