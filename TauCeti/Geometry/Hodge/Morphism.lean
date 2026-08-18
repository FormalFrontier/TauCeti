/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Structure

/-!
# Morphisms of pure Hodge structures

A morphism between integral pure Hodge structures of the same weight is an integral linear map
whose complexification preserves the Hodge filtration.  The complex action is derived canonically
from the integral map through the universal property of the source base change; in particular, it
commutes with the lattice-induced conjugations.

This file develops the elementary morphism calculus.  Morphisms are closed under identities and
composition, and form an additive commutative group.  Preservation of the filtration and
compatibility with conjugation imply preservation of the conjugate filtration and hence of every
Hodge component `H^{p,n-p}`.

## Main declarations

* `TauCeti.Hodge.integralMapToComplex`: complexification of an integral linear map between abstract
  complexification models.
* `TauCeti.Hodge.HodgeStructure.Hom`: morphisms of integral pure Hodge structures of a fixed weight.
* `TauCeti.Hodge.HodgeStructure.Hom.id` and `Hom.comp`: identity and composition.
* `TauCeti.Hodge.HodgeStructure.Hom.map_conjF_le`: morphisms preserve the conjugate filtration.
* `TauCeti.Hodge.HodgeStructure.Hom.map_piece_le`: morphisms preserve every Hodge component.

This supplies the morphism companion in Layer L0 of
`TauCetiRoadmap/HodgeStructures/README.md`.  It follows the opposed-filtration convention of
Deligne, *Théorie de Hodge II*, §1.2.1, and the usual morphism convention in Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §7.
-/

public section

namespace TauCeti.Hodge

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
variable {W₁ : Type v₁} {W₂ : Type v₂} {W₃ : Type v₃}
variable [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]
variable [AddCommGroup W₃] [Module ℂ W₃]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {ι₃ : V₃ →ₗ[ℤ] W₃}

/-- The complexification of an integral linear map between abstract complexification models.
Its value on a lattice vector is computed by `IsBaseChange.lift_eq`. -/
noncomputable def integralMapToComplex (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) : W₁ →ₗ[ℂ] W₂ :=
  h₁.lift (ι₂ ∘ₗ f)

/-- Complexification sends the identity integral map to the identity complex map. -/
@[simp]
theorem integralMapToComplex_id (h₁ : IsBaseChange ℂ ι₁) :
    integralMapToComplex h₁ ι₁ (LinearMap.id : V₁ →ₗ[ℤ] V₁) = LinearMap.id :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification sends the zero integral map to the zero complex map. -/
@[simp]
theorem integralMapToComplex_zero (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) :
    integralMapToComplex h₁ ι₂ (0 : V₁ →ₗ[ℤ] V₂) = 0 :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves addition of integral linear maps. -/
@[simp]
theorem integralMapToComplex_add (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f + g) =
      integralMapToComplex h₁ ι₂ f + integralMapToComplex h₁ ι₂ g :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves negation of integral linear maps. -/
@[simp]
theorem integralMapToComplex_neg (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (-f) = -integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves subtraction of integral linear maps. -/
@[simp]
theorem integralMapToComplex_sub (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂)
    (f g : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (f - g) =
      integralMapToComplex h₁ ι₂ f - integralMapToComplex h₁ ι₂ g :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves natural-number multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_nsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℕ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves integer multiples of integral linear maps. -/
@[simp]
theorem integralMapToComplex_zsmul (h₁ : IsBaseChange ℂ ι₁) (ι₂ : V₂ →ₗ[ℤ] W₂) (k : ℤ)
    (f : V₁ →ₗ[ℤ] V₂) :
    integralMapToComplex h₁ ι₂ (k • f) = k • integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq]

/-- Complexification preserves composition of integral linear maps. -/
theorem integralMapToComplex_comp (h₁ : IsBaseChange ℂ ι₁) (h₂ : IsBaseChange ℂ ι₂)
    (ι₃ : V₃ →ₗ[ℤ] W₃) (f : V₁ →ₗ[ℤ] V₂) (g : V₂ →ₗ[ℤ] V₃) :
    integralMapToComplex h₁ ι₃ (g ∘ₗ f) =
      integralMapToComplex h₂ ι₃ g ∘ₗ integralMapToComplex h₁ ι₂ f :=
  h₁.algHom_ext _ _ fun x ↦ by simp [integralMapToComplex, h₁.lift_eq, h₂.lift_eq]

/-- The complexification of an integral map commutes with lattice-induced conjugation. -/
@[simp]
theorem integralMapToComplex_commutes_conj (h₁ : IsBaseChange ℂ ι₁)
    (h₂ : IsBaseChange ℂ ι₂) (f : V₁ →ₗ[ℤ] V₂) (x : W₁) :
    integralMapToComplex h₁ ι₂ f (latticeConj h₁ x) =
      latticeConj h₂ (integralMapToComplex h₁ ι₂ f x) := by
  induction x using h₁.inductionOn with
  | zero => simp
  | tmul x => simp [integralMapToComplex, h₁.lift_eq]
  | smul z x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]

namespace HodgeStructure

variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂}
variable {h₃ : IsBaseChange ℂ ι₃} {n : ℤ}

/-- A morphism between integral pure Hodge structures of the same weight.

Its primary datum is an integral linear map. Its complexification is derived from the source
`IsBaseChange` witness together with the target integral inclusion, and is required to preserve
every step of the Hodge filtration. -/
structure Hom (source : HodgeStructure h₁ n) (target : HodgeStructure h₂ n) where
  /-- The integral linear map underlying a Hodge morphism. -/
  toIntLinearMap : V₁ →ₗ[ℤ] V₂
  /-- The complexification of the underlying map preserves every Hodge filtration step. -/
  map_mem_F : ∀ p x, x ∈ source.F p →
    integralMapToComplex h₁ ι₂ toIntLinearMap x ∈ target.F p

namespace Hom

variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}
variable {third : HodgeStructure h₃ n}

/-- The complex-linear map induced by an integral Hodge morphism. -/
noncomputable def toLinearMap (f : Hom source target) : W₁ →ₗ[ℂ] W₂ :=
  integralMapToComplex h₁ ι₂ f.toIntLinearMap

/-- A Hodge morphism acts on complex vectors through the complexification of its integral map. -/
noncomputable instance : CoeFun (Hom source target) fun _ ↦ W₁ → W₂ :=
  ⟨fun f ↦ f.toLinearMap⟩

/-- A Hodge morphism acts on integral vectors by its underlying integral map. -/
@[simp]
theorem apply_ι (f : Hom source target) (x : V₁) : f (ι₁ x) = ι₂ (f.toIntLinearMap x) :=
  h₁.lift_eq (ι₂ ∘ₗ f.toIntLinearMap) x

/-- Two Hodge morphisms are equal when their integral maps agree on every vector. -/
@[ext]
theorem ext {f g : Hom source target} (h : ∀ x, f.toIntLinearMap x = g.toIntLinearMap x) :
    f = g := by
  cases f with
  | mk f hF =>
    cases g with
    | mk g hG =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

/-- The complex action of a Hodge morphism commutes with lattice-induced conjugation. -/
@[simp]
theorem commutes_conj (f : Hom source target) (x : W₁) :
    f (latticeConj h₁ x) = latticeConj h₂ (f x) :=
  integralMapToComplex_commutes_conj h₁ h₂ f.toIntLinearMap x

/-- Preservation of a filtration step in submodule-map form. -/
theorem map_F_le (f : Hom source target) (p : ℤ) :
    (source.F p).map f.toLinearMap ≤ target.F p := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.map_mem_F p x hx

/-- A Hodge morphism preserves the conjugate Hodge filtration. -/
theorem map_conjF_le (f : Hom source target) (p : ℤ) :
    (source.conjF p).map f.toLinearMap ≤ target.conjF p := by
  rintro _ ⟨x, hx, rfl⟩
  rw [target.mem_conjF_iff, latticeConjugation_toEquiv_apply, ← f.commutes_conj]
  have hx' : (latticeConjugation h₁).toEquiv x ∈ source.F p :=
    (source.mem_conjF_iff p x).mp hx
  rw [latticeConjugation_toEquiv_apply] at hx'
  exact f.map_mem_F p _ hx'

/-- Elementwise form of preservation of the conjugate Hodge filtration. -/
theorem map_mem_conjF (f : Hom source target) (p : ℤ) {x : W₁}
    (hx : x ∈ source.conjF p) : f x ∈ target.conjF p :=
  f.map_conjF_le p ⟨x, hx, rfl⟩

/-- A Hodge morphism preserves every Hodge component `H^{p,n-p}`. -/
theorem map_piece_le (f : Hom source target) (p : ℤ) :
    (source.piece p).map f.toLinearMap ≤ target.piece p := by
  rintro _ ⟨x, hx, rfl⟩
  rw [target.mem_piece_iff]
  exact ⟨f.map_mem_F p x (source.piece_le_F p hx),
    f.map_mem_conjF (n - p) (source.piece_le_conjF p hx)⟩

/-- Elementwise form of preservation of Hodge components. -/
theorem map_mem_piece (f : Hom source target) (p : ℤ) {x : W₁}
    (hx : x ∈ source.piece p) : f x ∈ target.piece p :=
  f.map_piece_le p ⟨x, hx, rfl⟩

/-- The identity morphism of an integral pure Hodge structure. -/
noncomputable def id (source : HodgeStructure h₁ n) : Hom source source where
  toIntLinearMap := LinearMap.id
  map_mem_F := by
    rw [integralMapToComplex_id]
    exact fun _ _ hx ↦ hx

/-- The identity Hodge morphism acts as the identity on integral vectors. -/
@[simp]
theorem id_toIntLinearMap : (id source).toIntLinearMap = LinearMap.id :=
  by rw [id]

/-- The identity Hodge morphism acts as the identity on complex vectors. -/
@[simp]
theorem id_apply (x : W₁) : id source x = x := by
  simp [toLinearMap, id]

/-- Composition of morphisms of integral pure Hodge structures. -/
noncomputable def comp (g : Hom target third) (f : Hom source target) : Hom source third where
  toIntLinearMap := g.toIntLinearMap ∘ₗ f.toIntLinearMap
  map_mem_F := by
    intro p x hx
    rw [integralMapToComplex_comp h₁ h₂ ι₃]
    exact g.map_mem_F p _ (f.map_mem_F p x hx)

/-- The integral map underlying a composite is the composite of the integral maps. -/
@[simp]
theorem comp_toIntLinearMap (g : Hom target third) (f : Hom source target) :
    (g.comp f).toIntLinearMap = g.toIntLinearMap ∘ₗ f.toIntLinearMap :=
  by rw [comp]

/-- Composition of Hodge morphisms is pointwise composition on complex vectors. -/
@[simp]
theorem comp_apply (g : Hom target third) (f : Hom source target) (x : W₁) :
    g.comp f x = g (f x) := by
  change integralMapToComplex h₁ ι₃ (g.comp f).toIntLinearMap x =
    integralMapToComplex h₂ ι₃ g.toIntLinearMap
      (integralMapToComplex h₁ ι₂ f.toIntLinearMap x)
  rw [comp_toIntLinearMap,
    integralMapToComplex_comp h₁ h₂ ι₃ f.toIntLinearMap g.toIntLinearMap]
  rfl

/-- Left identity law for Hodge morphisms. -/
@[simp]
theorem id_comp (f : Hom source target) : (id target).comp f = f := by
  ext x
  rfl

/-- Right identity law for Hodge morphisms. -/
@[simp]
theorem comp_id (f : Hom source target) : f.comp (id source) = f := by
  ext x
  rfl

/-- Associativity of composition of Hodge morphisms. -/
theorem comp_assoc {V₄ W₄ : Type*} [AddCommGroup V₄]
    [AddCommGroup W₄] [Module ℂ W₄] {ι₄ : V₄ →ₗ[ℤ] W₄}
    {h₄ : IsBaseChange ℂ ι₄} {fourth : HodgeStructure h₄ n}
    (h : Hom third fourth) (g : Hom target third) (f : Hom source target) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

/-- The zero morphism between two integral pure Hodge structures. -/
noncomputable instance instZero : Zero (Hom source target) where
  zero :=
    { toIntLinearMap := 0
      map_mem_F := by simp }

/-- Addition of Hodge morphisms, defined on their integral maps. -/
noncomputable instance instAdd : Add (Hom source target) where
  add f g :=
    { toIntLinearMap := f.toIntLinearMap + g.toIntLinearMap
      map_mem_F := by
        intro p x hx
        rw [integralMapToComplex_add, LinearMap.add_apply]
        exact (target.F p).add_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Negation of a Hodge morphism, defined on its integral map. -/
noncomputable instance instNeg : Neg (Hom source target) where
  neg f :=
    { toIntLinearMap := -f.toIntLinearMap
      map_mem_F := by
        intro p x hx
        rw [integralMapToComplex_neg, LinearMap.neg_apply]
        exact (target.F p).neg_mem (f.map_mem_F p x hx) }

/-- Subtraction of Hodge morphisms, defined on their integral maps. -/
noncomputable instance instSub : Sub (Hom source target) where
  sub f g :=
    { toIntLinearMap := f.toIntLinearMap - g.toIntLinearMap
      map_mem_F := by
        intro p x hx
        rw [integralMapToComplex_sub, LinearMap.sub_apply]
        exact (target.F p).sub_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Natural-number multiples of a Hodge morphism, defined on its integral map. -/
noncomputable instance instSMulNat : SMul ℕ (Hom source target) where
  smul k f :=
    { toIntLinearMap := k • f.toIntLinearMap
      map_mem_F := by
        intro p x hx
        rw [integralMapToComplex_nsmul, LinearMap.smul_apply]
        exact nsmul_mem (f.map_mem_F p x hx) k }

/-- Integer multiples of a Hodge morphism, defined on its integral map. -/
noncomputable instance instSMulInt : SMul ℤ (Hom source target) where
  smul k f :=
    { toIntLinearMap := k • f.toIntLinearMap
      map_mem_F := by
        intro p x hx
        rw [integralMapToComplex_zsmul, LinearMap.smul_apply]
        exact zsmul_mem (f.map_mem_F p x hx) k }

/-- Integral Hodge morphisms form an additive commutative group, transported along the injection
sending a morphism to its underlying integral linear map. -/
noncomputable instance : AddCommGroup (Hom source target) :=
  Function.Injective.addCommGroup (fun f : Hom source target ↦ f.toIntLinearMap)
    (fun _ _ h ↦ ext (LinearMap.congr_fun h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The zero Hodge morphism has the zero integral linear map underneath. -/
@[simp]
theorem zero_toIntLinearMap : (0 : Hom source target).toIntLinearMap = 0 :=
  rfl

/-- Addition of Hodge morphisms is addition of their underlying integral linear maps. -/
@[simp]
theorem add_toIntLinearMap (f g : Hom source target) :
    (f + g).toIntLinearMap = f.toIntLinearMap + g.toIntLinearMap :=
  rfl

/-- Negation of a Hodge morphism is negation of its underlying integral linear map. -/
@[simp]
theorem neg_toIntLinearMap (f : Hom source target) :
    (-f).toIntLinearMap = -f.toIntLinearMap :=
  rfl

/-- Subtraction of Hodge morphisms is subtraction of their underlying integral linear maps. -/
@[simp]
theorem sub_toIntLinearMap (f g : Hom source target) :
    (f - g).toIntLinearMap = f.toIntLinearMap - g.toIntLinearMap :=
  rfl

/-- Natural-number multiples of Hodge morphisms pass to their underlying integral linear maps. -/
@[simp]
theorem nsmul_toIntLinearMap (k : ℕ) (f : Hom source target) :
    (k • f).toIntLinearMap = k • f.toIntLinearMap :=
  rfl

/-- Integer multiples of Hodge morphisms pass to their underlying integral linear maps. -/
@[simp]
theorem zsmul_toIntLinearMap (k : ℤ) (f : Hom source target) :
    (k • f).toIntLinearMap = k • f.toIntLinearMap :=
  rfl

/-- The zero Hodge morphism acts as zero on complex vectors. -/
@[simp]
theorem zero_apply (x : W₁) : (0 : Hom source target) x = 0 := by
  change integralMapToComplex h₁ ι₂ (0 : V₁ →ₗ[ℤ] V₂) x = 0
  rw [integralMapToComplex_zero]
  rfl

/-- Addition of Hodge morphisms is pointwise addition on complex vectors. -/
@[simp]
theorem add_apply (f g : Hom source target) (x : W₁) : (f + g) x = f x + g x := by
  change integralMapToComplex h₁ ι₂ (f.toIntLinearMap + g.toIntLinearMap) x =
    integralMapToComplex h₁ ι₂ f.toIntLinearMap x +
      integralMapToComplex h₁ ι₂ g.toIntLinearMap x
  rw [integralMapToComplex_add, LinearMap.add_apply]

/-- Negation of Hodge morphisms is pointwise negation on complex vectors. -/
@[simp]
theorem neg_apply (f : Hom source target) (x : W₁) : (-f) x = -f x := by
  change integralMapToComplex h₁ ι₂ (-f.toIntLinearMap) x =
    -integralMapToComplex h₁ ι₂ f.toIntLinearMap x
  rw [integralMapToComplex_neg, LinearMap.neg_apply]

/-- Subtraction of Hodge morphisms is pointwise subtraction on complex vectors. -/
@[simp]
theorem sub_apply (f g : Hom source target) (x : W₁) : (f - g) x = f x - g x := by
  change integralMapToComplex h₁ ι₂ (f.toIntLinearMap - g.toIntLinearMap) x =
    integralMapToComplex h₁ ι₂ f.toIntLinearMap x -
      integralMapToComplex h₁ ι₂ g.toIntLinearMap x
  rw [integralMapToComplex_sub, LinearMap.sub_apply]

/-- Natural-number multiples of Hodge morphisms are evaluated pointwise on complex vectors. -/
@[simp]
theorem nsmul_apply (k : ℕ) (f : Hom source target) (x : W₁) :
    (k • f) x = k • f x := by
  change integralMapToComplex h₁ ι₂ (k • f.toIntLinearMap) x =
    k • integralMapToComplex h₁ ι₂ f.toIntLinearMap x
  rw [integralMapToComplex_nsmul, LinearMap.smul_apply]

/-- Integer multiples of Hodge morphisms are evaluated pointwise on complex vectors. -/
@[simp]
theorem zsmul_apply (k : ℤ) (f : Hom source target) (x : W₁) :
    (k • f) x = k • f x := by
  change integralMapToComplex h₁ ι₂ (k • f.toIntLinearMap) x =
    k • integralMapToComplex h₁ ι₂ f.toIntLinearMap x
  rw [integralMapToComplex_zsmul, LinearMap.smul_apply]

/-- Composition is additive in the morphism applied second. -/
@[simp]
theorem add_comp (g h : Hom target third) (f : Hom source target) :
    (g + h).comp f = g.comp f + h.comp f := by
  ext x
  rfl

/-- Composition is additive in the morphism applied first. -/
@[simp]
theorem comp_add (g : Hom target third) (f h : Hom source target) :
    g.comp (f + h) = g.comp f + g.comp h := by
  ext x
  exact g.toIntLinearMap.map_add (f.toIntLinearMap x) (h.toIntLinearMap x)

/-- Composing with a zero morphism on the left gives zero. -/
@[simp]
theorem zero_comp (f : Hom source target) : (0 : Hom target third).comp f = 0 := by
  ext x
  rfl

/-- Composing with a zero morphism on the right gives zero. -/
@[simp]
theorem comp_zero (g : Hom target third) : g.comp (0 : Hom source target) = 0 := by
  ext x
  exact g.toIntLinearMap.map_zero

end Hom

end HodgeStructure

end TauCeti.Hodge
