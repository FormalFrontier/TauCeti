/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import TauCeti.AlgebraicGeometry.WeilDivisor.Order
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# The sheaf `𝒪_X(D)` of a Weil divisor

For a Weil divisor `D` on an integral locally Noetherian scheme `X` which is regular in
codimension one, this file builds the sheaf of `𝒪_X`-modules

`Γ(U, 𝒪_X(D)) = {f ∈ K(X) | f = 0 or ord_x f ≥ -D(x) for every codimension-one x ∈ U}`,

as an `𝒪_X`-submodule of the sheaf `𝒦_X` of rational functions of
`TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`. Regularity in codimension one enters
as the hypothesis that the local ring at every codimension-one point is a discrete valuation
ring. Under this hypothesis, the nonarchimedean order inequality makes the displayed set a
submodule.

## Main declarations

* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.sections D U`, the displayed `Γ(X, U)`-submodule of
  `Γ(𝒦_X, U)`, with `mem_sections_iff` its description over a nonempty open subset;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.submodule D`, the same data as a submodule of the
  *sheaf* `𝒦_X` — the membership condition is local — and
  `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.sheaf D`, the resulting sheaf `𝒪_X(D)` of
  `𝒪_X`-modules, together with its monomorphism `sheafι D : 𝒪_X(D) ⟶ 𝒦_X`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.sheafHomOfLE`, the inclusion
  `𝒪_X(D) ⟶ 𝒪_X(E)` for `D ≤ E`, and
  `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.unitToSheaf`, the factorization of `𝒪_X ⟶ 𝒦_X`
  through `𝒪_X(D)` for an effective `D`;
* `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.sheafMulIso`, multiplication by a nonzero rational
  function as an isomorphism `𝒪_X(D) ≅ 𝒪_X(D - div g)`, and
  `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.nonempty_iso_sheaf_of_linearlyEquivalent`: linearly
  equivalent divisors have isomorphic sheaves.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve: Weil
divisors `⊕_x ℤ` and Cartier divisors; the dictionaries `Cartier ≃ line bundles` and (smooth
curve) `Weil ≃ Cartier`; principal divisors; `Cl(X) ≅ Pic X`". It supplies the map from divisors
to sheaves and the invariance of that map under linear equivalence, which is the first half of
`Cl(X) ≅ Pic X`; that `𝒪_X(D)` is invertible, and that the map is a bijection onto `Pic X`, are
left to later work and need the local principality of `D`.

No formalization is vendored. The construction reuses Mathlib's `AlgebraicGeometry.Scheme.ord`
with its order-of-vanishing lemmas, `SheafOfModules.Submodule`, and the sheaf `𝒦_X` and its
multiplication endomorphisms from `TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`.
-/

public section

open CategoryTheory Order TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

noncomputable section

section LocallyNoetherian

variable [IsLocallyNoetherian X]

open Scheme in
/-- The sections of `𝒪_X(D)` over an open subset `U`: the rational functions vanishing, or with
order at least `-D(x)`, at every codimension-one point `x` of `U`.

Closure under addition uses the nonarchimedean order inequality available when the codimension-one
local rings are discrete valuation rings; closure under multiplication by a regular function is
`Scheme.ord_le_smul`. -/
def sections (D : SchemeWeilDivisor X) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFunctions X, U) where
  carrier := {s | ∀ (x : CodimensionOnePoint X) (hx : (x : X) ∈ U),
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    rationalFunctionsEquiv U s = 0 ∨
      -WeilDivisor.coeff D x ≤ X.ord (rationalFunctionsEquiv U s) x}
  zero_mem' := by
    intro x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    exact Or.inl (map_zero _)
  add_mem' := by
    intro s t hs ht x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have hst : rationalFunctionsEquiv U (s + t) =
        rationalFunctionsEquiv U s + rationalFunctionsEquiv U t := map_add _ _ _
    rw [hst]
    rcases hs x hx with h₁ | h₁
    · rw [h₁, zero_add]
      exact ht x hx
    · rcases ht x hx with h₂ | h₂
      · rw [h₂, add_zero]
        exact Or.inr h₁
      · by_cases h : rationalFunctionsEquiv U s + rationalFunctionsEquiv U t = 0
        · exact Or.inl h
        · exact Or.inr <| le_trans (le_min h₁ h₂) (Scheme.ord_add h)
  smul_mem' := by
    intro r s hs x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have hrs : rationalFunctionsEquiv U (r • s) = r • rationalFunctionsEquiv U s :=
      map_smul _ _ _
    rw [hrs]
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl (by simp)
    · rcases hs x hx with h₁ | h₁
      · exact Or.inl (by rw [h₁, smul_zero])
      · exact Or.inr <| h₁.trans (Scheme.ord_le_smul hx hr _)

/-- Membership in `SchemeWeilDivisor.sections`, unfolded: the condition is imposed one
codimension-one point at a time, so it makes sense over an open subset not known to be
nonempty. -/
@[simp]
lemma mem_sections {D : SchemeWeilDivisor X} {U : X.Opens}
    {s : Γ(Scheme.rationalFunctions X, U)} :
    s ∈ sections D U ↔ ∀ (x : CodimensionOnePoint X) (hx : (x : X) ∈ U),
      haveI : Nonempty U := ⟨⟨x, hx⟩⟩
      Scheme.rationalFunctionsEquiv U s = 0 ∨
        -WeilDivisor.coeff D x ≤ X.ord (Scheme.rationalFunctionsEquiv U s) x :=
  (Iff.rfl)

open Scheme in
/-- Over a nonempty open subset, a section of `𝒦_X` lies in `𝒪_X(D)` exactly when it vanishes or
has order at least `-D` at every codimension-one point of that subset.

This is deliberately not tagged `@[simp]`: the general `mem_sections` above already rewrites
`s ∈ sections D U`, for an arbitrary open subset, so tagging this specialization as well is a
`simpNF` failure. Use it through `rw` or `simp [mem_sections_iff]`. -/
lemma mem_sections_iff {D : SchemeWeilDivisor X} {U : X.Opens} [Nonempty U]
    {s : Γ(rationalFunctions X, U)} :
    s ∈ sections D U ↔ rationalFunctionsEquiv U s = 0 ∨
      ∀ x : CodimensionOnePoint X, (x : X) ∈ U →
        -WeilDivisor.coeff D x ≤ X.ord (rationalFunctionsEquiv U s) x := by
  rw [mem_sections]
  constructor
  · intro h
    by_cases h0 : rationalFunctionsEquiv U s = 0
    · exact Or.inl h0
    · exact Or.inr fun x hx ↦ (h x hx).resolve_left h0
  · rintro (h0 | h) x hx
    · exact Or.inl h0
    · exact Or.inr (h x hx)

/-- Over an empty open subset, `𝒪_X(D)` has all of the (zero) sections of `𝒦_X`. -/
lemma sections_eq_top_of_eq_bot (D : SchemeWeilDivisor X) {U : X.Opens} (hU : U = ⊥) :
    sections D U = ⊤ :=
  eq_top_iff.mpr fun s _ ↦ mem_sections.mpr fun x hx ↦ absurd (hU ▸ hx) (by simp)

/-- Restricting to a smaller open subset preserves the bound imposed by `D`. -/
lemma sections_map {D : SchemeWeilDivisor X} {U V : X.Opens} (i : V ⟶ U)
    {s : Γ(Scheme.rationalFunctions X, U)} (hs : s ∈ sections D U) :
    (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D V := by
  refine mem_sections.mpr fun x hx ↦ ?_
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : Nonempty U := ⟨⟨x, i.le hx⟩⟩
  rw [Scheme.rationalFunctionsEquiv_map]
  exact mem_sections.mp hs x (i.le hx)

/-- The `𝒪_X`-submodule `𝒪_X(D)` of the sheaf `𝒦_X` of rational functions: over `U` it consists
of the rational functions whose divisor is at least `-D` at every codimension-one point of `U`.

The membership condition is local, so this really is a submodule of the *sheaf* `𝒦_X`. -/
def submodule (D : SchemeWeilDivisor X) : (Scheme.rationalFunctions X).Submodule where
  obj U := sections D U.unop
  map i := fun {_} hs ↦ sections_map i.unop hs
  isSheaf {U} s hs := by
    refine mem_sections.mpr fun x hx ↦ ?_
    obtain ⟨V, i, hi, hxV⟩ := hs (x : X) hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (Scheme.rationalFunctions X).presheaf.map i.op s ∈ sections D V := hi
    have h := mem_sections.mp hi' x hxV
    have key := Scheme.rationalFunctionsEquiv_map i s
    rw [← key]
    exact h

/-- The sheaf `𝒪_X(D)` of `𝒪_X`-modules attached to a Weil divisor `D`. -/
def sheaf (D : SchemeWeilDivisor X) : X.Modules :=
  (submodule D).toSheafOfModules

/-- The inclusion `𝒪_X(D) ⟶ 𝒦_X`. -/
def sheafι (D : SchemeWeilDivisor X) : sheaf D ⟶ Scheme.rationalFunctions X :=
  (submodule D).ι

/-- The canonical inclusion `𝒪_X(D) ⟶ 𝒦_X` is a monomorphism: over every open subset it is the
inclusion of a submodule, hence injective. -/
instance (D : SchemeWeilDivisor X) : Mono (sheafι D) := by
  have : ∀ U : (Opens X)ᵒᵖ,
      Mono (((Scheme.Modules.toPresheaf X).map (sheafι D)).app U) := fun _ ↦
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact (Scheme.Modules.toPresheaf X).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-- A larger divisor allows more sections. -/
lemma sections_mono {D E : SchemeWeilDivisor X} (h : D ≤ E) (U : X.Opens) :
    sections D U ≤ sections E U := by
  intro s hs
  refine mem_sections.mpr fun x hx ↦ ?_
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  exact (mem_sections.mp hs x hx).imp id
    (le_trans (neg_le_neg (WeilDivisor.coeff_le_coeff h x)))

/-- A larger divisor allows more sections, as submodules of `𝒦_X`. -/
lemma submodule_mono {D E : SchemeWeilDivisor X} (h : D ≤ E) :
    (submodule D).toSubmodule ≤ (submodule E).toSubmodule :=
  fun U ↦ sections_mono h U.unop

/-- The inclusion `𝒪_X(D) ⟶ 𝒪_X(E)` of the sheaf of a divisor into the sheaf of a larger one. -/
def sheafHomOfLE {D E : SchemeWeilDivisor X} (h : D ≤ E) : sheaf D ⟶ sheaf E :=
  TauCeti.SheafOfModules.Submodule.homOfLE (submodule_mono h)

@[reassoc (attr := simp)]
lemma sheafHomOfLE_ι {D E : SchemeWeilDivisor X} (h : D ≤ E) :
    sheafHomOfLE h ≫ sheafι E = sheafι D :=
  TauCeti.SheafOfModules.Submodule.homOfLE_ι (submodule_mono h)

/-- The inclusion attached to `le_refl D` is the identity of `𝒪_X(D)`. -/
@[simp]
lemma sheafHomOfLE_refl (D : SchemeWeilDivisor X) : sheafHomOfLE (le_refl D) = 𝟙 (sheaf D) := by
  rw [← cancel_mono (sheafι D), sheafHomOfLE_ι, Category.id_comp]

/-- The inclusions attached to `D ≤ E` and `E ≤ F` compose to the one attached to `D ≤ F`. -/
@[reassoc (attr := simp)]
lemma sheafHomOfLE_comp {D E F : SchemeWeilDivisor X} (h : D ≤ E) (h' : E ≤ F) :
    sheafHomOfLE h ≫ sheafHomOfLE h' = sheafHomOfLE (h.trans h') := by
  rw [← cancel_mono (sheafι F), Category.assoc, sheafHomOfLE_ι, sheafHomOfLE_ι, sheafHomOfLE_ι]

/-- For an effective divisor `D`, every regular function on `U` is a section of `𝒪_X(D)`. -/
lemma toRationalFunctions_app_mem_sections {D : SchemeWeilDivisor X}
    (hD : WeilDivisor.IsEffective D) (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U a ∈ sections D U := by
  refine mem_sections.mpr fun x hx ↦ ?_
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app]
  exact Or.inr <| (neg_nonpos.mpr ((WeilDivisor.isEffective_iff D).mp hD x)).trans
    (Scheme.ord_germToFunctionField_nonneg a hx)

/-- For an effective divisor `D`, the inclusion `𝒪_X ⟶ 𝒦_X` factors through `𝒪_X(D)`. -/
def unitToSheaf {D : SchemeWeilDivisor X} (hD : WeilDivisor.IsEffective D) :
    SheafOfModules.unit X.ringCatSheaf ⟶ sheaf D :=
  TauCeti.SheafOfModules.liftToSubmodule (submodule D) (Scheme.toRationalFunctions X)
    fun U a ↦ toRationalFunctions_app_mem_sections hD U.unop a

@[simp, reassoc]
lemma unitToSheaf_ι {D : SchemeWeilDivisor X} (hD : WeilDivisor.IsEffective D) :
    unitToSheaf hD ≫ sheafι D = Scheme.toRationalFunctions X :=
  TauCeti.SheafOfModules.liftToSubmodule_ι _ _ _

/-- Transporting `𝒪_X(D)` along an equality of divisors. -/
@[reassoc]
lemma eqToHom_sheafι {D E : SchemeWeilDivisor X} (h : D = E) :
    eqToHom (congrArg sheaf h) ≫ sheafι E = sheafι D := by
  subst h
  simp

end LocallyNoetherian

section Mul

variable [IsNoetherian X]
variable (g : Additive X.functionFieldˣ)

/-- Multiplying a section of `𝒪_X(D)` by a nonzero rational function `g` gives a section of
`𝒪_X(D - div g)`: multiplying by `g` shifts every order of vanishing by `ord g`. -/
lemma rationalFunctionsMul_mem_sections {D : SchemeWeilDivisor X} {U : X.Opens}
    {s : Γ(Scheme.rationalFunctions X, U)} (hs : s ∈ sections D U) :
    Scheme.Modules.Hom.app
        (Scheme.rationalFunctionsMul X ((Additive.toMul g : X.functionFieldˣ) : X.functionField))
        U s ∈ sections (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) U := by
  refine mem_sections.mpr fun x hx ↦ ?_
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app]
  by_cases h0 : Scheme.rationalFunctionsEquiv U s = 0
  · exact Or.inl (by rw [h0, mul_zero])
  · refine Or.inr ?_
    have hb := (mem_sections.mp hs x hx).resolve_left h0
    rw [Scheme.ord_mul (Units.ne_zero _) h0, WeilDivisor.coeff_sub,
      WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
      orderAt_apply]
    omega

/-- Multiplication by `g`, as a morphism `𝒪_X(D) ⟶ 𝒪_X(D - div g)`. -/
def sheafMul (D : SchemeWeilDivisor X) :
    sheaf D ⟶ sheaf (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) :=
  TauCeti.SheafOfModules.liftToSubmodule _
    (sheafι D ≫ Scheme.rationalFunctionsMul X
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField))
    fun U s ↦ rationalFunctionsMul_mem_sections g
      (TauCeti.SheafOfModules.ι_val_app_mem (submodule D) U s)

@[reassoc (attr := simp)]
lemma sheafMul_ι (D : SchemeWeilDivisor X) :
    sheafMul g D ≫ sheafι _ =
      sheafι D ≫ Scheme.rationalFunctionsMul X
        ((Additive.toMul g : X.functionFieldˣ) : X.functionField) :=
  TauCeti.SheafOfModules.liftToSubmodule_ι _ _ _

omit [AlgebraicGeometry.IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] in
/-- Multiplying by `g` and then by `g⁻¹` is the identity on `𝒦_X`. -/
lemma rationalFunctionsMul_comp_neg :
    Scheme.rationalFunctionsMul X ((Additive.toMul g : X.functionFieldˣ) : X.functionField) ≫
        Scheme.rationalFunctionsMul X
          ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField) = 𝟙 _ := by
  rw [← Scheme.rationalFunctionsMul_mul, toMul_neg, (Additive.toMul g).inv_mul,
    Scheme.rationalFunctionsMul_one]

omit [AlgebraicGeometry.IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] in
/-- Multiplying by `g⁻¹` and then by `g` is the identity on `𝒦_X`. -/
lemma rationalFunctionsMul_neg_comp :
    Scheme.rationalFunctionsMul X ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField) ≫
        Scheme.rationalFunctionsMul X
          ((Additive.toMul g : X.functionFieldˣ) : X.functionField) = 𝟙 _ := by
  simpa using rationalFunctionsMul_comp_neg (-g)

omit [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] in
/-- The divisor bookkeeping behind `SchemeWeilDivisor.sheafMulIso`. -/
private lemma sub_principalDivisor_sub_principalDivisor_neg (D : SchemeWeilDivisor X) :
    D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g -
        (WeilDivisor.OrderSystem.ofScheme X).principalDivisor (-g) = D := by
  rw [WeilDivisor.OrderSystem.principalDivisor_neg]
  abel

/-- **Multiplication by a nonzero rational function is an isomorphism**
`𝒪_X(D) ≅ 𝒪_X(D - div g)`: linearly equivalent divisors have isomorphic sheaves. -/
def sheafMulIso (D : SchemeWeilDivisor X) :
    sheaf D ≅ sheaf (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) :=
  have hg := sub_principalDivisor_sub_principalDivisor_neg g D
  { hom := sheafMul g D
    inv := sheafMul (-g) _ ≫ eqToHom (congrArg sheaf hg)
    hom_inv_id := by
      rw [← cancel_mono (sheafι D), Category.assoc, Category.assoc, eqToHom_sheafι hg,
        sheafMul_ι, sheafMul_ι_assoc, rationalFunctionsMul_comp_neg, Category.comp_id,
        Category.id_comp]
    inv_hom_id := by
      rw [← cancel_mono (sheafι _), Category.assoc, Category.assoc, sheafMul_ι,
        eqToHom_sheafι_assoc hg, sheafMul_ι_assoc, rationalFunctionsMul_neg_comp,
        Category.comp_id, Category.id_comp] }

/-- The forward morphism of `sheafMulIso` is multiplication by `g`. -/
@[simp]
lemma sheafMulIso_hom (D : SchemeWeilDivisor X) :
    (sheafMulIso g D).hom = sheafMul g D := by
  rw [sheafMulIso]

/-- The inverse morphism of `sheafMulIso`, included into `𝒦_X`, is multiplication by `g⁻¹`. -/
@[reassoc (attr := simp)]
lemma sheafMulIso_inv_ι (D : SchemeWeilDivisor X) :
    (sheafMulIso g D).inv ≫ sheafι D =
      sheafι (D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) ≫
        Scheme.rationalFunctionsMul X
          ((Additive.toMul (-g) : X.functionFieldˣ) : X.functionField) := by
  rw [← cancel_epi (sheafMulIso g D).hom, Iso.hom_inv_id_assoc, sheafMulIso_hom,
    sheafMul_ι_assoc, rationalFunctionsMul_comp_neg, Category.comp_id]

variable {g}

/-- **Linearly equivalent Weil divisors have isomorphic sheaves.** This is the sheaf-level form
of the fact that `𝒪_X(D)` depends only on the divisor class of `D`, and the reason the divisor
class group maps to isomorphism classes of `𝒪_X`-modules. -/
theorem nonempty_iso_sheaf_of_linearlyEquivalent {D E : SchemeWeilDivisor X}
    (h : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    Nonempty (sheaf D ≅ sheaf E) := by
  obtain ⟨g, hg⟩ :=
    (WeilDivisor.OrderSystem.linearlyEquivalent_iff_exists_principalDivisor _).mp h
  refine ⟨sheafMulIso g D ≪≫ eqToIso (congrArg sheaf ?_)⟩
  rw [hg]
  abel

end Mul

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
