/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Cofree comodules

For an `R`-coalgebra `C` and an `R`-module `M`, the tensor product `M ⊗[R] C` carries a right
`C`-comodule structure whose coaction is `id ⊗ Δ` followed by reassociation,
`m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`. This is the **cofree** (or coinduced) right comodule on `M`: it is
the value at `M` of the right adjoint to the forgetful functor from comodules to modules. The
universal property is `Comodule.Hom.cofreeEquiv`: comodule morphisms from a comodule `P` into
`M ⊗[R] C` are exactly `R`-linear maps `P → M`.

Taking `M = R` recovers (up to the unitor) the regular comodule already provided in
`TauCeti.Algebra.Coalgebra.Comodule.Regular`; the cofree construction generalizes it to an
arbitrary module of "coefficients".

The cofree comodule structure is provided as an explicit named definition `Comodule.cofree`,
not as a global instance: an `R`-module can carry many coactions, and the cofree one (which on
`M ⊗[R] C` would otherwise clash with a future tensor product of comodules) should be selected
explicitly. This follows the convention already used for `Comodule.trivial` and
`Comodule.groupLike`.

## Main definitions

* `TauCeti.Comodule.cofree`: the cofree right `C`-comodule structure on `M ⊗[R] C`.
* `TauCeti.Comodule.Hom.cofreeMap`: the functoriality of the cofree comodule in `M`, sending an
  `R`-linear map `f : M → N` to the comodule morphism `f ⊗ id`.
* `TauCeti.Comodule.Hom.cofreeUnit`: the coaction `P → P ⊗[R] C` of a comodule `P`, viewed as a
  comodule morphism into its cofree comodule (the unit of the adjunction).
* `TauCeti.Comodule.Hom.cofreeLift`: the comodule morphism `P → M ⊗[R] C` lifting an `R`-linear
  map `P → M`.
* `TauCeti.Comodule.Hom.cofreeEquiv`: the cofree adjunction, `Hom R C P (M ⊗[R] C) ≃ (P →ₗ[R] M)`.
* `TauCeti.ComoduleCat.cofree`: the cofree comodule, bundled as an object of `ComoduleCat`.

## References

This is the cofree (coinduced) comodule of a coalgebra; see for example Sweedler, *Hopf
Algebras*, Chapter 2. It is added for the Layer 1 target "Comodules over a coalgebra/Hopf
algebra" of the Tau Ceti reductive-groups roadmap,
`ReductiveGroups/README.md` in TauCetiRoadmap, specifically the regular/cofree representations and
the adjunction underlying the embedding theorem.
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct LinearMap

namespace TauCeti

universe u v w x y

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (R C M) in
/-- The coaction of the cofree right `C`-comodule on `M ⊗[R] C`, namely `id ⊗ Δ` followed by
reassociation: `m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`. This is an implementation detail of `Comodule.cofree`;
the public characterizations of the coaction are `Comodule.cofree_coact` and
`Comodule.cofree_coact_tmul`. -/
noncomputable def cofreeCoact : M ⊗[R] C →ₗ[R] (M ⊗[R] C) ⊗[R] C :=
  (TensorProduct.assoc R M C C).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor M

@[simp]
private theorem cofreeCoact_tmul (m : M) (c : C) :
    cofreeCoact R C M (m ⊗ₜ c) = (TensorProduct.assoc R M C C).symm (m ⊗ₜ Coalgebra.comul c) := by
  simp [cofreeCoact]

/-- Pushing the counit through the inverse associator (an instance of naturality). -/
private theorem counit_lTensor_comp_assoc_symm :
    Coalgebra.counit.lTensor (M ⊗[R] C) ∘ₗ (TensorProduct.assoc R M C C).symm.toLinearMap
      = (TensorProduct.assoc R M C R).symm.toLinearMap ∘ₗ
          LinearMap.lTensor M ((Coalgebra.counit (R := R) (A := C)).lTensor C) := by
  refine TensorProduct.ext' fun m x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
  | tmul a b => simp

/-- Pushing the comultiplication through the inverse associator (an instance of naturality). -/
private theorem comul_lTensor_comp_assoc_symm :
    Coalgebra.comul.lTensor (M ⊗[R] C) ∘ₗ (TensorProduct.assoc R M C C).symm.toLinearMap
      = (TensorProduct.assoc R M C (C ⊗[R] C)).symm.toLinearMap ∘ₗ
          LinearMap.lTensor M ((Coalgebra.comul (R := R) (A := C)).lTensor C) := by
  refine TensorProduct.ext' fun m x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
  | tmul a b => simp

/-- The double cofree coaction reorganized, with the coalgebra's own double comultiplication
isolated on the right factor. This is pure associator bookkeeping (it does not use
coassociativity), and feeds the coassociativity proof of the cofree coaction. -/
private theorem assoc_comp_cofreeCoact_rTensor_comp_cofreeCoact :
    TensorProduct.assoc R (M ⊗[R] C) C C ∘ₗ (cofreeCoact R C M).rTensor C ∘ₗ cofreeCoact R C M
      = (TensorProduct.assoc R M C (C ⊗[R] C)).symm.toLinearMap ∘ₗ
          LinearMap.lTensor M (TensorProduct.assoc R C C C ∘ₗ
            Coalgebra.comul.rTensor C ∘ₗ Coalgebra.comul) := by
  refine TensorProduct.ext' fun m c => ?_
  simp only [comp_apply, cofreeCoact_tmul, LinearEquiv.coe_coe, lTensor_tmul]
  induction Coalgebra.comul (R := R) (A := C) c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a b =>
    simp only [assoc_symm_tmul, rTensor_tmul, cofreeCoact_tmul]
    induction Coalgebra.comul (R := R) (A := C) a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, add_tmul, hx, hy]
    | tmul p q => simp [assoc_symm_tmul, assoc_tmul]

variable (R C M) in
/-- The cofree (coinduced) right `C`-comodule structure on `M ⊗[R] C`, with coaction
`m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`.

This is not registered as a global instance: an `R`-module can carry many coactions, and the
cofree one should be selected explicitly with `Comodule.cofree`. -/
@[implicit_reducible]
noncomputable def cofree : Comodule R C (M ⊗[R] C) where
  coact := cofreeCoact R C M
  coassoc := by
    rw [assoc_comp_cofreeCoact_rTensor_comp_cofreeCoact, Coalgebra.coassoc, cofreeCoact,
      ← LinearMap.comp_assoc, comul_lTensor_comp_assoc_symm, LinearMap.comp_assoc,
      ← LinearMap.lTensor_comp]
  lTensor_counit_comp_coact := by
    rw [cofreeCoact, ← LinearMap.comp_assoc, counit_lTensor_comp_assoc_symm,
      LinearMap.comp_assoc, ← LinearMap.lTensor_comp, Coalgebra.lTensor_counit_comp_comul]
    refine TensorProduct.ext' fun m c => ?_
    simp

-- Register `cofree` as a local instance for the rest of this file, so the cofree comodule on a
-- tensor product `· ⊗[R] C` resolves automatically and need not be threaded through every
-- statement with `letI`. It is deliberately *not* a global instance: an `R`-module can carry many
-- coactions, so a global cofree instance would make `Comodule` resolution non-confluent.
attribute [local instance] cofree

/-- The coaction of the cofree comodule is `id ⊗ Δ` followed by reassociation. -/
@[simp]
theorem cofree_coact :
    coact (R := R) (C := C) (M := M ⊗[R] C)
      = (TensorProduct.assoc R M C C).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor M :=
  rfl

/-- The coaction of the cofree comodule unfolds to its implementation `cofreeCoact`. -/
private theorem cofree_coact_eq_cofreeCoact :
    coact (R := R) (C := C) (M := M ⊗[R] C) = cofreeCoact R C M :=
  rfl

/-- The coaction of the cofree comodule on a simple tensor: `m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`. -/
@[simp]
theorem cofree_coact_tmul (m : M) (c : C) :
    coact (R := R) (C := C) (M := M ⊗[R] C) (m ⊗ₜ c)
      = (TensorProduct.assoc R M C C).symm (m ⊗ₜ Coalgebra.comul c) :=
  cofreeCoact_tmul m c

namespace Hom

/-- Functoriality of the cofree comodule in the coefficient module: an `R`-linear map
`f : M → N` induces the comodule morphism `f ⊗ id : M ⊗[R] C → N ⊗[R] C`. -/
noncomputable def cofreeMap (f : M →ₗ[R] N) :
    Hom R C (M ⊗[R] C) (N ⊗[R] C) := by
  exact
    { toLinearMap := f.rTensor C
      map_coact := by
        refine TensorProduct.ext' fun m c => ?_
        simp only [cofree_coact_eq_cofreeCoact, LinearMap.comp_apply, cofreeCoact_tmul,
          LinearMap.rTensor_tmul]
        induction Coalgebra.comul (R := R) (A := C) c using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
        | tmul a b => simp [assoc_symm_tmul, rTensor_tmul] }

/-- The underlying linear map of `cofreeMap f` is `f ⊗ id`. -/
@[simp]
theorem cofreeMap_toLinearMap (f : M →ₗ[R] N) : (cofreeMap (C := C) f).toLinearMap = f.rTensor C :=
  rfl

/-- `cofreeMap f` acts as `f ⊗ id`. -/
@[simp]
theorem cofreeMap_apply (f : M →ₗ[R] N) (x : M ⊗[R] C) :
    cofreeMap (C := C) f x = f.rTensor C x :=
  rfl

/-- The cofree functor preserves identities. -/
@[simp]
theorem cofreeMap_id :
    cofreeMap (C := C) (LinearMap.id : M →ₗ[R] M) = Comodule.Hom.id R C (M ⊗[R] C) := by
  refine Comodule.Hom.ext fun x => ?_
  rw [cofreeMap_apply, LinearMap.rTensor_id_apply]
  rfl

/-- The cofree functor preserves composition. -/
@[simp]
theorem cofreeMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    cofreeMap (C := C) (g.comp f) = comp (cofreeMap (C := C) g) (cofreeMap (C := C) f) := by
  refine Comodule.Hom.ext fun x => ?_
  simp [LinearMap.rTensor_comp]

variable (P) in
/-- The coaction of a comodule `P`, viewed as a comodule morphism `P → P ⊗[R] C` into its cofree
comodule. This is the unit of the cofree adjunction. -/
noncomputable def cofreeUnit [Comodule R C P] :
    Hom R C P (P ⊗[R] C) := by
  exact
    { toLinearMap := coact (R := R) (C := C) (M := P)
      map_coact := by
        rw [cofree_coact_eq_cofreeCoact]
        refine LinearMap.ext fun p => ?_
        simp only [LinearMap.comp_apply, cofreeCoact, LinearEquiv.coe_coe]
        rw [← Comodule.coassoc_apply p, LinearEquiv.symm_apply_apply]
        rfl }

/-- The underlying linear map of `cofreeUnit P` is the coaction of `P`. -/
@[simp]
theorem cofreeUnit_toLinearMap [Comodule R C P] :
    (cofreeUnit (R := R) (C := C) P).toLinearMap = coact (R := R) (C := C) (M := P) :=
  rfl

/-- `cofreeUnit P` acts as the coaction of `P`. -/
@[simp]
theorem cofreeUnit_apply [Comodule R C P] (p : P) :
    cofreeUnit (R := R) (C := C) P p = coact (R := R) (C := C) (M := P) p :=
  rfl

/-- The comodule morphism `P → M ⊗[R] C` lifting an `R`-linear map `g : P → M`, namely
`(g ⊗ id) ∘ ρ_P`. -/
noncomputable def cofreeLift [Comodule R C P] (g : P →ₗ[R] M) :
    Hom R C P (M ⊗[R] C) := by
  exact comp (cofreeMap (C := C) g) (cofreeUnit (R := R) (C := C) P)

/-- The underlying linear map of `cofreeLift g` is `(g ⊗ id) ∘ ρ_P`. -/
@[simp]
theorem cofreeLift_toLinearMap [Comodule R C P] (g : P →ₗ[R] M) :
    (cofreeLift (C := C) g).toLinearMap = g.rTensor C ∘ₗ coact (R := R) (C := C) (M := P) :=
  rfl

/-- `cofreeLift g` acts as `(g ⊗ id) ∘ ρ_P`. -/
@[simp]
theorem cofreeLift_apply [Comodule R C P] (g : P →ₗ[R] M) (p : P) :
    cofreeLift (C := C) g p = g.rTensor C (coact (R := R) (C := C) (M := P) p) :=
  rfl

/-- Pushing the counit past `g ⊗ id`. -/
private theorem counit_lTensor_rTensor (g : P →ₗ[R] M) (z : P ⊗[R] C) :
    (Coalgebra.counit (R := R) (A := C)).lTensor M (g.rTensor C z)
      = g.rTensor R ((Coalgebra.counit (R := R) (A := C)).lTensor P z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p c => simp

/-- Pushing the counit through the inverse associator, element form. -/
private theorem counit_rTensor_assoc_symm (m : M) (y : C ⊗[R] C) :
    ((Coalgebra.counit (R := R) (A := C)).lTensor M).rTensor C
        ((TensorProduct.assoc R M C C).symm (m ⊗ₜ y))
      = (TensorProduct.assoc R M R C).symm
          (m ⊗ₜ (Coalgebra.counit (R := R) (A := C)).rTensor C y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [tmul_add, map_add, hp, hq]
  | tmul a b => simp

/-- The cofree coaction is split by `(ε ∘ -) ∘ counit`: applying the counit to the right factor
and then the right unitor retracts the cofree coaction. This is the right-counit law of `C`
transported to `M ⊗[R] C`, and underlies the cofree adjunction. -/
private theorem cofree_retract (z : M ⊗[R] C) : (TensorProduct.rid R M).toLinearMap.rTensor C
        (((Coalgebra.counit (R := R) (A := C)).lTensor M).rTensor C (cofreeCoact R C M z)) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m c =>
    simp only [cofreeCoact_tmul, counit_rTensor_assoc_symm m (Coalgebra.comul c),
      Coalgebra.rTensor_counit_comul]
    simp

/-- Comodule morphisms `P → M ⊗[R] C` into the cofree comodule on `M` are exactly `R`-linear
maps `P → M`: this is the universal property of the cofree comodule (the cofree functor is right
adjoint to the forgetful functor). -/
noncomputable def cofreeEquiv [Comodule R C P] :
    Hom R C P (M ⊗[R] C) ≃ (P →ₗ[R] M) := by
  exact
    { toFun φ := (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := C)).lTensor M ∘ₗ φ.toLinearMap
      invFun g := cofreeLift (C := C) g
      left_inv φ := by
        refine Comodule.Hom.ext fun p => ?_
        have h1 : φ.toLinearMap.rTensor C (coact (R := R) (C := C) (M := P) p)
            = cofreeCoact R C M (φ p) := φ.map_coact_apply p
        rw [cofreeLift_apply, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
        simp only [LinearMap.comp_apply]
        rw [h1, cofree_retract]
      right_inv g := by
        refine LinearMap.ext fun p => ?_
        simp only [LinearMap.comp_apply, cofreeLift_toLinearMap]
        rw [counit_lTensor_rTensor, Comodule.lTensor_counit_coact]
        simp }

/-- The forward direction of the cofree adjunction sends a comodule morphism to the
`R`-linear map obtained by applying the counit to the `C` factor. -/
@[simp]
theorem cofreeEquiv_apply [Comodule R C P] :
    ∀ φ : Hom R C P (M ⊗[R] C),
      cofreeEquiv (R := R) (C := C) (M := M) (P := P) φ
        = (TensorProduct.rid R M).toLinearMap ∘ₗ
            (Coalgebra.counit (R := R) (A := C)).lTensor M ∘ₗ φ.toLinearMap := by
  intro φ
  rfl

/-- The inverse direction of the cofree adjunction is `cofreeLift`. -/
@[simp]
theorem cofreeEquiv_symm_apply [Comodule R C P] (g : P →ₗ[R] M) :
    (cofreeEquiv (R := R) (C := C) (M := M) (P := P)).symm g = cofreeLift (C := C) g :=
  rfl

end Hom

end Comodule

namespace ComoduleCat

variable (R : Type u) (C : Type v) [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- The cofree right `C`-comodule on a module `M`, bundled as an object of `ComoduleCat`. Its
underlying module is `M ⊗[R] C` and its coaction is `m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`. -/
noncomputable abbrev cofree (M : Type w) [AddCommMonoid M] [Module R M] :
    ComoduleCat.{u, v, max w v} R C :=
  letI := Comodule.cofree R C M
  of R C (M ⊗[R] C)

/-- The underlying semimodule of the bundled cofree comodule is `M ⊗[R] C`. -/
@[simp]
theorem cofree_toSemimoduleCat : (cofree R C M).toSemimoduleCat = SemimoduleCat.of R (M ⊗[R] C) :=
  rfl

/-- The coaction on the bundled cofree comodule is `id ⊗ Δ` followed by reassociation. -/
@[simp]
theorem cofree_coact :
    letI := Comodule.cofree R C M
    Comodule.coact (R := R) (C := C) (M := cofree R C M)
      = (TensorProduct.assoc R M C C).symm.toLinearMap ∘ₗ Coalgebra.comul.lTensor M :=
  rfl

/-- The coaction on the bundled cofree comodule on a simple tensor is
`m ⊗ c ↦ ∑ (m ⊗ c₁) ⊗ c₂`. -/
@[simp]
theorem cofree_coact_tmul (m : M) (c : C) :
    letI := Comodule.cofree R C M
    Comodule.coact (R := R) (C := C) (M := cofree R C M) (m ⊗ₜ[R] c)
      = (TensorProduct.assoc R M C C).symm (m ⊗ₜ Coalgebra.comul c) :=
  Comodule.cofree_coact_tmul m c

end ComoduleCat

end TauCeti
