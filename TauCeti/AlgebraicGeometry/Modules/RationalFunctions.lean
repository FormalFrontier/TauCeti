/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The sheaf of rational functions on an integral scheme

Mathlib defines the function field `X.functionField` of an irreducible scheme as the stalk of
its structure sheaf at the generic point, but it does not organize the rational functions into a
sheaf on `X`. On an integral scheme the sheaf of total quotient rings is the constant sheaf with
value `K(X)`, and the constant sheaf with value the stalk at the generic point is the pushforward
of the structure sheaf along the canonical morphism `Spec K(X) ⟶ X`: that morphism hits exactly
the generic point, and on an irreducible space an open subset contains the generic point as soon
as it is nonempty. This file takes that pushforward as the definition, which makes the sheaf
condition and the `𝒪_X`-module structure automatic.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`, the canonical morphism
  `Spec K(X) ⟶ X` from the spectrum of the function field, and
  `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField_preimage`: it pulls a nonempty open
  subset back to everything;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRing`, the sheaf `𝒦_X` as a sheaf of
  commutative rings, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctions`, its underlying
  `𝒪_X`-module sheaf, and `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsSectionsEquiv`,
  the canonical identification of their sections;
* `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctionsRing` and
  `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions`, the canonical morphisms from `𝒪_X`
  as ring and module sheaves, respectively;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsRingEquiv`, the identification of the
  ring of sections over a nonempty open subset with `K(X)`, compatible with restriction maps;
* `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv`, the identification
  `Γ(𝒦_X, U) ≃ₗ[Γ(X, U)] K(X)` of its sections over a nonempty open subset with the function
  field, `TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_map`, the compatibility of
  these identifications with the restriction maps, and the two statements which say that `𝒦_X`
  really is the constant sheaf: `TauCeti.AlgebraicGeometry.Scheme.isIso_rationalFunctions_map`,
  the restriction maps between nonempty open subsets are isomorphisms, and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions`, the sections over an empty
  open subset vanish;
* the module morphism `TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions` is
  `X.germToFunctionField` on sections
  (`TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv_toRationalFunctions_app`), is
  injective on sections over every open subset
  (`TauCeti.AlgebraicGeometry.Scheme.toRationalFunctions_app_injective`), and is therefore a
  monomorphism.

The Cartier divisors of `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A ("Divisors on a
curve: Weil divisors `⊕_x ℤ` and Cartier divisors; the dictionaries `Cartier ≃ line bundles`
and (smooth curve) `Weil ≃ Cartier`"), are the global sections of `𝒦_X^*/𝒪_X^*`, and the line
bundle `𝒪_X(D)` attached to a divisor is a subsheaf of `𝒦_X`; both need the sheaf `𝒦_X` and the
inclusion `𝒪_X ⟶ 𝒦_X` built here. On an integral scheme the sheaf of total quotient rings agrees
with this constant sheaf, so no generality is lost at that stage.

No formalization is vendored. The construction reuses Mathlib's `Scheme.functionField`,
`Scheme.germToFunctionField`, `Scheme.fromSpecStalk` with its computation of the closed point and
of the maps on sections, `Scheme.ΓSpecIso`, `Scheme.Modules.pushforward` and
`SheafOfModules.unit` with its universal property `SheafOfModules.unitHomEquiv`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The canonical morphism `Spec K(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme, that is, the morphism from the spectrum of the stalk at the generic point. -/
def fromSpecFunctionField : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

variable {X}

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
theorem genericPoint_mem (U : X.Opens) [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

instance instUniqueSpecFunctionField (X : Scheme.{u}) [IsIntegral X] :
    Unique (Spec X.functionField) :=
  inferInstanceAs (Unique (PrimeSpectrum X.functionField))

/-- The sheaf of commutative rings underlying the rational-function sheaf: the pushforward of
the structure sheaf of `Spec K(X)` along `fromSpecFunctionField`. -/
def rationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pushforward CommRingCat (fromSpecFunctionField X).base).obj
    (Spec X.functionField).sheaf

/-- The canonical morphism of sheaves of rings `𝒪_X ⟶ 𝒦_X`. -/
def toRationalFunctionsRing (X : Scheme.{u}) [IrreducibleSpace X] :
    X.sheaf ⟶ rationalFunctionsRing X where
  hom := (fromSpecFunctionField X).c

/-- The sheaf `𝒦_X` of rational functions on an integral scheme `X`: the constant sheaf with
value the function field, realized as the pushforward of the structure sheaf of `Spec K(X)`
along `TauCeti.AlgebraicGeometry.Scheme.fromSpecFunctionField`. -/
def rationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (SheafOfModules.unit _)

/-- The module sheaf and ring sheaf constructions of `𝒦_X` have canonically identified
sections. -/
def rationalFunctionsSectionsEquiv (X : Scheme.{u}) [IrreducibleSpace X] (U : X.Opens) :
    (Γ(rationalFunctions X, U) : Type u) ≃
      ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) := by
  change (Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) : Type u) ≃ _
  exact Equiv.refl _

/-- On a nonempty open subset, the morphism `Spec K(X) ⟶ X` acts on sections by the germ map to
the function field. -/
theorem fromSpecFunctionField_app (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U =
      X.germToFunctionField U ≫ (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec X.functionField).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_app (genericPoint_mem U)

variable [IsIntegral X]

/-- The morphism `Spec K(X) ⟶ X` pulls every nonempty open subset back to the whole of
`Spec K(X)`, its source having a single point, which maps to the generic point. -/
@[simp]
theorem fromSpecFunctionField_preimage (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro p _
  apply TopologicalSpace.Opens.mem_map.mpr
  rw [Subsingleton.elim p (IsLocalRing.closedPoint X.functionField),
    fromSpecFunctionField, Scheme.fromSpecStalk_closedPoint]
  exact genericPoint_mem U

private def functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U) ≅ X.functionField :=
  ((Spec X.functionField).presheaf.mapIso
    (eqToIso (fromSpecFunctionField_preimage U)).op).symm ≪≫ Scheme.ΓSpecIso X.functionField

/-- The sections of the ring sheaf `𝒦_X` over a nonempty open subset are the function field,
as commutative rings. -/
def rationalFunctionsRingEquiv (U : X.Opens) [Nonempty U] :
    ((rationalFunctionsRing X).presheaf.obj (.op U) : Type u) ≃+* X.functionField :=
  (functionFieldSectionsIso U).commRingCatIsoToRingEquiv

private theorem app_comp_functionFieldSectionsIso (U : X.Opens) [Nonempty U] :
    (fromSpecFunctionField X).app U ≫ (functionFieldSectionsIso U).hom =
      X.germToFunctionField U := by
  rw [fromSpecFunctionField_app, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim ((homOfLE le_top).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv) (𝟙 _)]
  simp

private theorem map_comp_functionFieldSectionsIso {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) :
    (Spec X.functionField).presheaf.map
        ((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (functionFieldSectionsIso U).hom = (functionFieldSectionsIso V).hom := by
  rw [functionFieldSectionsIso, functionFieldSectionsIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Functor.map_comp_assoc,
    Subsingleton.elim (((Opens.map (fromSpecFunctionField X).base).map i).op ≫
      (eqToIso (fromSpecFunctionField_preimage U)).op.inv)
      (eqToIso (fromSpecFunctionField_preimage V)).op.inv]

/-- The ring equivalences identifying sections of `𝒦_X` with the function field commute with
restriction maps. -/
@[simp]
theorem rationalFunctionsRingEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : (rationalFunctionsRing X).presheaf.obj (.op V)) :
    rationalFunctionsRingEquiv U ((rationalFunctionsRing X).presheaf.map i.op s) =
      rationalFunctionsRingEquiv V s := by
  unfold rationalFunctionsRing at s ⊢
  change (functionFieldSectionsIso U).hom
    ((Spec X.functionField).presheaf.map
      ((Opens.map (fromSpecFunctionField X).base).map i).op
        (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V))) =
          (functionFieldSectionsIso V).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply, map_comp_functionFieldSectionsIso]
  rfl

/-- The sections of `𝒦_X` over a nonempty open subset `U` are the function field, as a module
over the functions on `U`. -/
def rationalFunctionsEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃ₗ[Γ(X, U)] X.functionField where
  toFun s := (functionFieldSectionsIso U).hom s
  map_add' s t := map_add _ s t
  map_smul' r s := by
    -- The action of `Γ(X, U)` on the pushforward is multiplication after applying the map on
    -- sections, so multiplicativity of the identification reduces this to
    -- `app_comp_functionFieldSectionsIso`.
    have h : (functionFieldSectionsIso U).hom (r • s) =
        (functionFieldSectionsIso U).hom ((fromSpecFunctionField X).app U r *
          (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U))) := rfl
    rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
      app_comp_functionFieldSectionsIso, RingHom.id_apply, Algebra.smul_def]
    rfl
  invFun k := (functionFieldSectionsIso U).inv k
  left_inv s := (functionFieldSectionsIso U).hom_inv_id_apply s
  right_inv k := (functionFieldSectionsIso U).inv_hom_id_apply k

/-- The identifications of the sections of `𝒦_X` with the function field are compatible with the
restriction maps: `𝒦_X` is the constant sheaf. -/
@[simp]
theorem rationalFunctionsEquiv_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V)
    (s : Γ(rationalFunctions X, V)) :
    rationalFunctionsEquiv U ((rationalFunctions X).presheaf.map i.op s) =
      rationalFunctionsEquiv V s := by
  unfold rationalFunctionsEquiv rationalFunctions
  -- This normalization is exactly `Scheme.Modules.pushforward_obj_presheaf_map`. Rewriting by
  -- that lemma cannot transport `s` across the opaque `Scheme.Modules` wrapper, so unfold the
  -- local wrapper above and state the documented pushforward computation explicitly.
  change (functionFieldSectionsIso U).hom
    ((Spec X.functionField).presheaf.map
      ((Opens.map (fromSpecFunctionField X).base).map i).op
        (id s : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V))) =
      (functionFieldSectionsIso V).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply, map_comp_functionFieldSectionsIso]
  rfl

/-- The restriction maps of `𝒦_X` between nonempty open subsets are bijective. -/
theorem rationalFunctions_map_bijective {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    Function.Bijective ((rationalFunctions X).presheaf.map i.op) := by
  constructor
  · intro a b hab
    refine (rationalFunctionsEquiv V).injective ?_
    rw [← rationalFunctionsEquiv_map i a, ← rationalFunctionsEquiv_map i b, hab]
  · intro t
    refine ⟨(rationalFunctionsEquiv V).symm (rationalFunctionsEquiv U t), ?_⟩
    refine (rationalFunctionsEquiv U).injective ?_
    rw [rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply]

/-- The restriction maps of `𝒦_X` between nonempty open subsets are isomorphisms. -/
instance isIso_rationalFunctions_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) :
    IsIso ((rationalFunctions X).presheaf.map i.op) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (rationalFunctions_map_bijective i)

omit [IsIntegral X] in
/-- The sheaf `𝒦_X` has no nonzero sections over an empty open subset. -/
theorem subsingleton_rationalFunctions (U : X.Opens) (hU : U = ⊥) :
    Subsingleton Γ(rationalFunctions X, U) := by
  subst hU
  have h : (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by simp
  have : Subsingleton Γ(Spec X.functionField,
      (fromSpecFunctionField X) ⁻¹ᵁ (⊥ : X.Opens)) := by rw [h]; infer_instance
  exact this

/-- The inclusion of the structure sheaf into the sheaf of rational functions, given by the
global section `1` of `𝒦_X`. -/
-- The source is spelled through `Quiver.Hom` because `SheafOfModules.unit X.ringCatSheaf` is not
-- syntactically of type `X.Modules`; without this the `Scheme.Modules` API for morphisms of
-- `𝒪_X`-modules does not apply to the result.
def toRationalFunctions (X : Scheme.{u}) [IrreducibleSpace X] :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) (rationalFunctions X) :=
  (rationalFunctions X).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V => (1 : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ V.unop)))
      (fun _ _ _ => PresheafOfModules.unit_map_one _ _))

omit [IsIntegral X] in
/-- Application of `toRationalFunctions` is scalar multiplication by its defining global
section. This is definitional because `SheafOfModules.unitHomEquiv.symm` constructs the unique
module morphism from the unit object with that value at `1`. -/
private theorem toRationalFunctions_app (U : X.Opens) (r : Γ(X, U)) :
    Scheme.Modules.Hom.app (toRationalFunctions X) U r =
      r • (id (1 : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U)) :
        Γ(rationalFunctions X, U)) := rfl

omit [IsIntegral X] in
/-- The morphisms of ring sheaves and module sheaves `𝒪_X ⟶ 𝒦_X` agree on sections. -/
@[simp]
theorem toRationalFunctionsRing_app (U : X.Opens) (r : Γ(X, U)) :
    rationalFunctionsSectionsEquiv X U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      (toRationalFunctionsRing X).hom.app (.op U) r := by
  rw [toRationalFunctions_app]
  change (fromSpecFunctionField X).app U r * 1 = (fromSpecFunctionField X).app U r
  rw [mul_one]

private theorem rationalFunctionsEquiv_one (U : X.Opens) [Nonempty U] :
    rationalFunctionsEquiv U
      (id (1 : Γ(Spec X.functionField, (fromSpecFunctionField X) ⁻¹ᵁ U)) :
        Γ(rationalFunctions X, U)) = 1 := by
  exact map_one (ConcreteCategory.hom (functionFieldSectionsIso U).hom)

/-- On a nonempty open subset, the inclusion `𝒪_X ⟶ 𝒦_X` is the germ map to the function
field. -/
@[simp]
theorem rationalFunctionsEquiv_toRationalFunctions_app (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app (toRationalFunctions X) U r) =
      X.germToFunctionField U r := by
  rw [toRationalFunctions_app, map_smul, rationalFunctionsEquiv_one, Algebra.smul_def, mul_one]
  rfl

/-- The inclusion `𝒪_X ⟶ 𝒦_X` is injective on sections over every open subset: over a nonempty
one because the germ map to the function field of an integral scheme is injective, and over an
empty one because there are no nonzero functions there. -/
theorem toRationalFunctions_app_injective (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (toRationalFunctions X) U) := by
  rcases U.1.eq_empty_or_nonempty with h | h
  · have hU : U = ⊥ := SetLike.ext' h
    have hsub : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    exact fun a b _ => Subsingleton.elim (id a : Γ(X, U)) (id b : Γ(X, U))
  · have : Nonempty U := by simpa using h
    intro a b hab
    have key : X.germToFunctionField U (id a : Γ(X, U)) =
        X.germToFunctionField U (id b : Γ(X, U)) := by
      rw [← rationalFunctionsEquiv_toRationalFunctions_app,
        ← rationalFunctionsEquiv_toRationalFunctions_app]
      exact congrArg _ hab
    exact X.germToFunctionField_injective U key

instance : Mono (toRationalFunctions X) := by
  have hU : ∀ U : (Opens X)ᵒᵖ,
      Mono (((Scheme.Modules.toPresheaf X).map (toRationalFunctions X)).app U) := fun U =>
    ConcreteCategory.mono_of_injective _ (toRationalFunctions_app_injective U.unop)
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map (NatTrans.mono_of_mono_app _)

end Scheme

end

end AlgebraicGeometry

end TauCeti
