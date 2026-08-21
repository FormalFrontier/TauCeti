/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.LocalFunctional

/-!
# The unit law for Tannakian local functionals

Let `H` be a commutative Hopf algebra over a field `k`, and let `A` be a commutative
`k`-algebra. A tensor automorphism of scalar extension on the finite-dimensional
`H`-comodules determines compatible linear functionals on the finite subcomodules of the
regular comodule. This file proves the tensor-unit part of the algebra-map laws for those
functionals: whenever a finite regular subcomodule contains `1`, its local functional sends
that element to `1 : A`.

The proof maps the trivial tensor-unit comodule into the chosen regular subcomodule by
`r ↦ r • 1`. Naturality transports the tensor automorphism along this map, while its
monoidal unit axiom says that its component on the tensor unit fixes the canonical generator.
The resulting theorem is the unit-law prerequisite for gluing the local functionals into the
algebra-valued point in Tannakian reconstruction.

## Main declaration

* `TauCeti.Tannaka.localFunctional_one`: every local functional sends the unit of a finite
  regular subcomodule to one.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

variable (k H A : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A]

/-- The comodule morphism from the tensor unit to a finite regular subcomodule containing one. -/
private noncomputable def regularUnitHom
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hOne : (1 : H) ∈ N.1) :
    𝟙_ (FGComoduleCat.{u, u, u} k H) ⟶ finiteRegularObject k H N := by
  letI : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  letI : Comodule k H k := Comodule.trivial (R := k) (C := H) (M := k)
  exact FGComoduleCat.ofHom (R := k) (C := H)
    ((Comodule.Hom.trivialToRegular (R := k) (C := H)).codRestrict N.1 fun r ↦ by
      simpa [Algebra.smul_def] using N.1.toSubmodule.smul_mem r hOne)

@[simp]
private theorem regularUnitHom_apply
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hOne : (1 : H) ∈ N.1) (r : k) :
    regularUnitHom k H N hOne r =
      ⟨r • (1 : H), N.1.toSubmodule.smul_mem r hOne⟩ :=
  by
    let _ : Comodule k H k := Comodule.trivial (R := k) (C := H) (M := k)
    -- The application lemmas below do not rewrite through the bundled `FGComoduleCat`
    -- coercion, so expose first the underlying comodule map and then its `codRestrict`.
    change (regularUnitHom k H N hOne).hom.toLinearMap r = _
    unfold regularUnitHom
    change ((Comodule.Hom.trivialToRegular (R := k) (C := H)).codRestrict N.1 _ r) = _
    apply Subtype.ext
    rw [Comodule.Hom.codRestrict_apply, Comodule.Hom.trivialToRegular_apply]
    simp [Algebra.smul_def]

private theorem map_regularUnitHom_ε_one
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hOne : (1 : H) ∈ N.1) :
    (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map
          (regularUnitHom k H N hOne)
        (ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor (1 : A)) =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H A
        (finiteRegularObject k H N)).symm (1 ⊗ₜ[k] ⟨1, hOne⟩) := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H N)
  have hExplicit :
      eqToHom hN
          ((FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map
              (regularUnitHom k H N hOne)
            (ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor (1 : A))) =
        1 ⊗ₜ[k] ⟨1, hOne⟩ := by
    -- The bundled monoidal functor hides the two object transports. Reassociate the maps
    -- categorically so the inverse transports cancel before evaluating the pure tensor.
    change eqToHom hN
        ((FGComoduleCat.scalarExtensionFunctor k H A).map (regularUnitHom k H N hOne)
          (ε (FGComoduleCat.scalarExtensionFunctor k H A) (1 : A))) = _
    rw [← SemimoduleCat.comp_apply, ← SemimoduleCat.comp_apply]
    rw [FGComoduleCat.scalarExtensionFunctor_ε,
      FGComoduleCat.scalarExtensionFunctor_map]
    simp only [FGComoduleCat.of_obj, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, eqToHom_trans_assoc, Category.id_comp, SemimoduleCat.hom_comp,
      ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    change (regularUnitHom k H N hOne).hom.toLinearMap.baseChange A
      ((1 : A) ⊗ₜ[k] (1 : k)) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : A) ⊗ₜ[k] regularUnitHom k H N hOne (1 : k) = _
    rw [regularUnitHom_apply]
    congr 1
    ext
    simp
  have h := congrArg (fun z ↦ eqToHom hN.symm z) hExplicit
  calc
    _ = eqToHom hN.symm
        (eqToHom hN
          ((FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map
              (regularUnitHom k H N hOne)
            (ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor (1 : A)))) :=
      ((eqToIso hN).hom_inv_id_apply _).symm
    _ = _ := h

/-- The transported component of a tensor automorphism fixes `1 ⊗ 1` in every finite
regular subcomodule containing the unit. -/
@[simp]
theorem scalarExtensionComponent_one_tmul
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hOne : (1 : H) ∈ N.1) :
    scalarExtensionComponent k H A η (finiteRegularObject k H N)
        (1 ⊗ₜ[k] ⟨1, hOne⟩) = 1 ⊗ₜ[k] ⟨1, hOne⟩ := by
  let _ : Module.Finite k N.1 := Subcomodule.mem_finiteSubcomodules.mp N.2
  let i := regularUnitHom k H N hOne
  have hnat := η.hom.hom.naturality i
  have hunit := CategoryTheory.NatTrans.IsMonoidal.unit (τ := η.hom.hom)
  have hcat :
      ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor ≫
          (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map i ≫
            η.hom.hom.app (finiteRegularObject k H N) =
        ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor ≫
          (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map i := by
    calc
      _ = ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor ≫
          (η.hom.hom.app (𝟙_ (FGComoduleCat k H)) ≫
            (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map i) :=
        congrArg (fun f ↦
          ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor ≫ f) hnat
      _ = (ε (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).toFunctor ≫
          η.hom.hom.app (𝟙_ (FGComoduleCat k H))) ≫
            (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map i :=
        (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun f ↦
        f ≫ (FGComoduleCat.scalarExtensionMonoidalFunctor k H A).map i) hunit
  have happ := congrArg (fun f ↦ f (1 : A)) hcat
  simp only [SemimoduleCat.comp_apply] at happ
  dsimp only [i] at happ
  rw [map_regularUnitHom_ε_one] at happ
  let hN := FGComoduleCat.scalarExtensionFunctor_obj k H A
    (finiteRegularObject k H N)
  rw [scalarExtensionComponent_apply]
  exact (congrArg (fun z ↦ eqToHom hN z) happ).trans
    ((eqToIso hN).inv_hom_id_apply _)

/-- A local functional extracted from a tensor automorphism sends the unit of every finite
regular subcomodule containing it to `1`. This is the tensor-unit law needed to upgrade the
glued functional on `H` to an algebra homomorphism. -/
@[simp high]
theorem localFunctional_one
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A))
    (N : Subcomodule.finiteSubcomodules (R := k) (C := H) (M := H))
    (hOne : (1 : H) ∈ N.1) :
    localFunctional k H A η N ⟨1, hOne⟩ = 1 := by
  rw [localFunctional_apply, scalarExtensionComponent_one_tmul]
  rw [counitEvaluation_tmul k H A N.1 (1 : A) ⟨1, hOne⟩]
  simp only [Bialgebra.counit_one, map_one, one_mul]

end TauCeti.Tannaka
