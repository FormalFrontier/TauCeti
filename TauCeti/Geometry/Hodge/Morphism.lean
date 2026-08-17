/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Structure

/-!
# Morphisms of pure Hodge structures

A morphism between pure Hodge structures of the same weight is a complex-linear map which
preserves the Hodge filtration and commutes with the specified conjugations.  The conjugation
condition records that the complex-linear map comes from the underlying real or rational
structure; without it, preservation of the Hodge filtration alone is not the usual notion of a
Hodge morphism.

This file develops the elementary morphism calculus.  Morphisms are closed under identities,
composition, zero, addition, and negation.  Preservation of the filtration and compatibility with
conjugation imply preservation of the conjugate filtration and hence of every Hodge component
`H^{p,n-p}`.

The definitions are stated for `HodgeStructureOn`, so they apply equally to integral, rational,
and real structures through their chosen complexifications. Constructing a morphism from a map
of lattices or rational spaces is separate base-change infrastructure: the present interface is the
target such constructions must satisfy.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.Hom`: morphisms of pure Hodge structures of a fixed weight.
* `TauCeti.Hodge.HodgeStructureOn.Hom.id` and `Hom.comp`: identity and composition.
* `TauCeti.Hodge.HodgeStructureOn.Hom.map_conjF_le`: morphisms preserve the conjugate filtration.
* `TauCeti.Hodge.HodgeStructureOn.Hom.map_piece_le`: morphisms preserve every Hodge component.

This supplies the morphism companion in Layer L0 of
`TauCetiRoadmap/HodgeStructures/README.md`.  It follows the opposed-filtration convention of
Deligne, *Théorie de Hodge II*, §1.2.1, and the usual morphism convention in Voisin,
*Hodge Theory and Complex Algebraic Geometry I*, §7.
-/

public section

namespace TauCeti.Hodge.HodgeStructureOn

universe u₁ u₂ u₃

variable {W₁ : Type u₁} {W₂ : Type u₂} {W₃ : Type u₃}
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]
variable [AddCommGroup W₃] [Module ℂ W₃]
variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {ω₃ : Conjugation W₃}
variable {n : ℤ}

/-- A morphism between pure Hodge structures of the same weight.

It is a complex-linear map preserving every step of the decreasing Hodge filtration and commuting
with the conjugations which encode the underlying real or rational forms. -/
structure Hom (source : HodgeStructureOn W₁ ω₁ n) (target : HodgeStructureOn W₂ ω₂ n) where
  /-- The complex-linear map underlying a Hodge morphism. -/
  toLinearMap : W₁ →ₗ[ℂ] W₂
  /-- The underlying map preserves every step of the Hodge filtration. -/
  map_mem_F : ∀ p x, x ∈ source.F p → toLinearMap x ∈ target.F p
  /-- The underlying map commutes with the conjugations. -/
  commutes_conj : ∀ x, toLinearMap (ω₁.toEquiv x) = ω₂.toEquiv (toLinearMap x)

namespace Hom

variable {source : HodgeStructureOn W₁ ω₁ n} {target : HodgeStructureOn W₂ ω₂ n}
variable {third : HodgeStructureOn W₃ ω₃ n}

/-- A Hodge morphism acts on vectors through its underlying complex-linear map. -/
instance : CoeFun (Hom source target) fun _ ↦ W₁ → W₂ :=
  ⟨fun f ↦ f.toLinearMap⟩

/-- Two Hodge morphisms are equal when they agree on every vector. -/
@[ext]
theorem ext {f g : Hom source target} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hF hf =>
    cases g with
    | mk g hG hg =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl


/-- Preservation of a filtration step in submodule-map form. -/
theorem map_F_le (f : Hom source target) (p : ℤ) :
    (source.F p).map f.toLinearMap ≤ target.F p := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.map_mem_F p x hx

/-- A Hodge morphism preserves the conjugate Hodge filtration.

This is where compatibility with conjugation is used: membership in a conjugate filtration step is
tested after applying conjugation, where it reduces to preservation of the original filtration. -/
theorem map_conjF_le (f : Hom source target) (p : ℤ) :
    (source.conjF p).map f.toLinearMap ≤ target.conjF p := by
  rintro _ ⟨x, hx, rfl⟩
  rw [target.mem_conjF_iff, ← f.commutes_conj]
  exact f.map_mem_F p _ ((source.mem_conjF_iff p x).mp hx)

/-- A Hodge morphism preserves every Hodge component `H^{p,n-p}`. -/
theorem map_piece_le (f : Hom source target) (p : ℤ) :
    (source.piece p).map f.toLinearMap ≤ target.piece p := by
  rintro _ ⟨x, hx, rfl⟩
  rw [target.mem_piece_iff]
  refine ⟨f.map_mem_F p x (source.piece_le_F p hx), ?_⟩
  rw [target.mem_conjF_iff, ← f.commutes_conj]
  exact f.map_mem_F (n - p) _
    ((source.mem_conjF_iff (n - p) x).mp (source.piece_le_conjF p hx))

/-- Elementwise form of preservation of Hodge components. -/
theorem map_mem_piece (f : Hom source target) (p : ℤ) {x : W₁}
    (hx : x ∈ source.piece p) : f x ∈ target.piece p :=
  f.map_piece_le p ⟨x, hx, rfl⟩

/-- The identity morphism of a pure Hodge structure. -/
@[expose] def id (source : HodgeStructureOn W₁ ω₁ n) : Hom source source where
  toLinearMap := LinearMap.id
  map_mem_F := fun _ _ hx ↦ hx
  commutes_conj := fun _ ↦ rfl

/-- The identity Hodge morphism acts as the identity. -/
@[simp]
theorem id_apply (x : W₁) : id source x = x :=
  rfl

/-- Composition of morphisms of pure Hodge structures. -/
@[expose] def comp (g : Hom target third) (f : Hom source target) : Hom source third where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_mem_F := fun p x hx ↦ g.map_mem_F p _ (f.map_mem_F p x hx)
  commutes_conj := fun x ↦ by
    rw [LinearMap.comp_apply, f.commutes_conj, LinearMap.comp_apply, g.commutes_conj]

/-- Composition of Hodge morphisms is pointwise composition. -/
@[simp]
theorem comp_apply (g : Hom target third) (f : Hom source target) (x : W₁) :
    g.comp f x = g (f x) :=
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
theorem comp_assoc {W₄ : Type*} [AddCommGroup W₄] [Module ℂ W₄]
    {ω₄ : Conjugation W₄} {fourth : HodgeStructureOn W₄ ω₄ n}
    (h : Hom third fourth) (g : Hom target third) (f : Hom source target) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

/-- The zero morphism between two pure Hodge structures. -/
instance : Zero (Hom source target) where
  zero :=
    { toLinearMap := 0
      map_mem_F := fun _ _ _ ↦ Submodule.zero_mem _
      commutes_conj := fun _ ↦ by simp }

/-- Addition of Hodge morphisms, defined pointwise. -/
instance : Add (Hom source target) where
  add f g :=
    { toLinearMap := f.toLinearMap + g.toLinearMap
      map_mem_F := fun p x hx ↦
        (target.F p).add_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx)
      commutes_conj := fun x ↦ by simp [f.commutes_conj, g.commutes_conj] }

/-- Negation of a Hodge morphism, defined pointwise. -/
instance : Neg (Hom source target) where
  neg f :=
    { toLinearMap := -f.toLinearMap
      map_mem_F := fun p x hx ↦ (target.F p).neg_mem (f.map_mem_F p x hx)
      commutes_conj := fun x ↦ by simp [f.commutes_conj] }

/-- The zero Hodge morphism acts as the zero map. -/
@[simp]
theorem zero_apply (x : W₁) : (0 : Hom source target) x = 0 :=
  rfl

/-- Addition of Hodge morphisms is pointwise addition. -/
@[simp]
theorem add_apply (f g : Hom source target) (x : W₁) : (f + g) x = f x + g x :=
  rfl

/-- Negation of Hodge morphisms is pointwise negation. -/
@[simp]
theorem neg_apply (f : Hom source target) (x : W₁) : (-f) x = -f x :=
  rfl

/-- Hodge morphisms form an additive commutative group under pointwise operations. -/
instance : AddCommGroup (Hom source target) where
  add_assoc f g h := by ext x; exact add_assoc (f x) (g x) (h x)
  zero_add f := by ext x; exact zero_add (f x)
  add_zero f := by ext x; exact add_zero (f x)
  nsmul := nsmulRec
  neg_add_cancel f := by ext x; exact neg_add_cancel (f x)
  zsmul := zsmulRec
  add_comm f g := by ext x; exact add_comm (f x) (g x)

/-- Natural-number multiples of Hodge morphisms are evaluated pointwise. -/
@[simp]
theorem nsmul_apply (k : ℕ) (f : Hom source target) (x : W₁) :
    (k • f) x = k • f x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, zero_apply]
  | succ k ih => simp only [succ_nsmul, add_apply, ih]

/-- Integer multiples of Hodge morphisms are evaluated pointwise. -/
@[simp]
theorem zsmul_apply (k : ℤ) (f : Hom source target) (x : W₁) :
    (k • f) x = k • f x := by
  cases k with
  | ofNat k => simp
  | negSucc k => simp

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
  exact g.toLinearMap.map_add (f x) (h x)

/-- Composing with a zero morphism on the left gives zero. -/
@[simp]
theorem zero_comp (f : Hom source target) : (0 : Hom target third).comp f = 0 := by
  ext x
  rfl

/-- Composing with a zero morphism on the right gives zero. -/
@[simp]
theorem comp_zero (g : Hom target third) : g.comp (0 : Hom source target) = 0 := by
  ext x
  exact g.toLinearMap.map_zero

end Hom

end TauCeti.Hodge.HodgeStructureOn
