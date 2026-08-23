/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Basic
public import TauCeti.Geometry.Hodge.Morphism

/-!
# Morphisms of mixed Hodge structures

A morphism of mixed Hodge structures is a single rational linear map preserving the weight
filtration, whose complexification preserves the Hodge filtration. Only the rational map is
datum: the complex action is the canonical scalar extension
`TauCeti.Hodge.rationalMapToComplex`, so compatibility with the complexified weight filtration
and with lattice conjugation are theorems rather than axioms.

The conjugation-equivariance of the complex action is proved for an *arbitrary* complex
base-change model in `TauCeti.Hodge.rationalMapToComplex_commutes_conj`; it is what lets a
geometric instance, whose complex space is not literally a tensor product, use this morphism
calculus.

The principal construction here is the passage to the weight-graded pieces: a morphism of mixed
Hodge structures induces, for each `k`, a morphism of the *pure* weight-`k` Hodge structures
carried by the graded pieces `grᵂ_k`. This is functorial, and it is the form in which the mixed
theory feeds Deligne's bigrading and the strictness theorem.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.Hom`: morphisms of mixed Hodge structures.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.id`, `…comp`: identity and composition.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.map_WC_le`: the complex action preserves the
  complexified weight filtration.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.commutes_conj`: the complex action commutes with lattice
  conjugation.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.gradedMap`: the induced map on the rational graded piece
  `grᵂ_k`.
* `TauCeti.Hodge.MixedHodgeStructure.Hom.gradedHom`: that induced map as a morphism of the pure
  weight-`k` Hodge structures, together with its functoriality.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters–Steenbrink, *Mixed Hodge Structures*, Ch. 3. The
morphism convention — a single rational map with the complex action derived — is the one
specified for Layer L2 of the Hodge structures roadmap.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w u' v' w' u'' v'' w''

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'ℤ] [AddCommGroup V'ℚ] [Module ℚ V'ℚ] [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ} {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}

namespace MixedHodgeStructure

/-- A morphism of mixed Hodge structures.

Its only datum is a rational linear map, required to preserve every step of the weight
filtration. The complex action is the canonical scalar extension of that map, and is required to
preserve every step of the Hodge filtration. -/
structure Hom (source : MixedHodgeStructure hℚ hℂ) (target : MixedHodgeStructure h'ℚ h'ℂ) where
  /-- The rational linear map underlying a morphism of mixed Hodge structures. -/
  toRatLinearMap : Vℚ →ₗ[ℚ] V'ℚ
  /-- The underlying rational map preserves every step of the weight filtration. -/
  map_mem_WQ : ∀ k x, x ∈ source.WQ k → toRatLinearMap x ∈ target.WQ k
  /-- The complexification of the underlying map preserves every Hodge filtration step. -/
  map_mem_F : ∀ p x, x ∈ source.F p →
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ toRatLinearMap x ∈ target.F p

namespace Hom

variable {source : MixedHodgeStructure hℚ hℂ} {target : MixedHodgeStructure h'ℚ h'ℂ}
variable {V''ℤ : Type u''} {V''ℚ : Type v''} {V''ℂ : Type w''}
variable [AddCommGroup V''ℤ] [AddCommGroup V''ℚ] [Module ℚ V''ℚ]
variable [AddCommGroup V''ℂ] [Module ℂ V''ℂ]
variable {ι''ℚ : V''ℤ →ₗ[ℤ] V''ℚ} {ι''ℂ : V''ℤ →ₗ[ℤ] V''ℂ}
variable {h''ℚ : IsBaseChange ℚ ι''ℚ} {h''ℂ : IsBaseChange ℂ ι''ℂ}
variable {third : MixedHodgeStructure h''ℚ h''ℂ}

/-- The complex-linear map induced by a morphism of mixed Hodge structures. -/
noncomputable def toLinearMap (f : Hom source target) : Vℂ →ₗ[ℂ] V'ℂ :=
  rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap

/-- A morphism of mixed Hodge structures acts on complex vectors through the complexification of
its rational map. -/
noncomputable instance : CoeFun (Hom source target) fun _ ↦ Vℂ → V'ℂ :=
  ⟨fun f ↦ f.toLinearMap⟩

/-- The complex action of a morphism is the complexification of its rational map. This is the
bridge to the whole `TauCeti.Hodge.rationalMapToComplex` API. -/
theorem toLinearMap_def (f : Hom source target) :
    f.toLinearMap = rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap :=
  (rfl)

/-- Two morphisms of mixed Hodge structures are equal when their rational maps agree. -/
@[ext]
theorem ext {f g : Hom source target} (h : ∀ x, f.toRatLinearMap x = g.toRatLinearMap x) :
    f = g := by
  cases f with
  | mk f hW hF =>
    cases g with
    | mk g hW' hF' =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

/-- A morphism acts on the image of a pure tensor through its rational map. -/
@[simp]
theorem apply_rationalToComplexLinearEquiv_tmul (f : Hom source target) (z : ℂ) (x : Vℚ) :
    f (rationalToComplexLinearEquiv hℚ hℂ (z ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv h'ℚ h'ℂ (z ⊗ₜ[ℚ] f.toRatLinearMap x) :=
  rationalMapToComplex_rationalToComplexLinearEquiv_tmul hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap z x

/-- The complex action of a morphism of mixed Hodge structures commutes with lattice-induced
conjugation. -/
@[simp]
theorem commutes_conj (f : Hom source target) (x : Vℂ) :
    f (latticeConj hℂ x) = latticeConj h'ℂ (f x) :=
  rationalMapToComplex_commutes_conj hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap x

/-- Preservation of a weight step in submodule-map form. -/
theorem map_WQ_le (f : Hom source target) (k : ℤ) :
    (source.WQ k).map f.toRatLinearMap ≤ target.WQ k := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.map_mem_WQ k x hx

/-- Preservation of a Hodge step in submodule-map form. -/
theorem map_F_le (f : Hom source target) (p : ℤ) :
    (source.F p).map f.toLinearMap ≤ target.F p := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.map_mem_F p x hx

/-- A morphism of mixed Hodge structures preserves the complexified weight filtration. -/
theorem map_WC_le (f : Hom source target) (k : ℤ) :
    (source.WC k).map f.toLinearMap ≤ target.WC k := by
  simp only [WC_def, toLinearMap_def]
  exact map_rationalToComplexSubmodule_le hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap (f.map_WQ_le k)

/-- Elementwise form of preservation of the complexified weight filtration. -/
theorem map_mem_WC (f : Hom source target) (k : ℤ) {x : Vℂ} (hx : x ∈ source.WC k) :
    f x ∈ target.WC k :=
  f.map_WC_le k ⟨x, hx, rfl⟩

/-- The identity morphism of a mixed Hodge structure. -/
noncomputable def id (source : MixedHodgeStructure hℚ hℂ) : Hom source source where
  toRatLinearMap := LinearMap.id
  map_mem_WQ := fun _ _ hx ↦ hx
  map_mem_F := by
    rw [rationalMapToComplex_id]
    exact fun _ _ hx ↦ hx

/-- The identity morphism has the identity rational linear map underneath. -/
@[simp]
theorem id_toRatLinearMap : (id source).toRatLinearMap = LinearMap.id := by rw [id]

/-- The identity morphism acts as the identity on complex vectors. -/
@[simp]
theorem id_apply (x : Vℂ) : id source x = x := by
  simp [toLinearMap_def]

/-- Composition of morphisms of mixed Hodge structures. -/
noncomputable def comp (g : Hom target third) (f : Hom source target) : Hom source third where
  toRatLinearMap := g.toRatLinearMap ∘ₗ f.toRatLinearMap
  map_mem_WQ := fun k x hx ↦ g.map_mem_WQ k _ (f.map_mem_WQ k x hx)
  map_mem_F := by
    intro p x hx
    rw [rationalMapToComplex_comp hℚ hℂ h'ℚ h'ℂ h''ℚ h''ℂ]
    exact g.map_mem_F p _ (f.map_mem_F p x hx)

/-- The rational map underlying a composite is the composite of the rational maps. -/
@[simp]
theorem comp_toRatLinearMap (g : Hom target third) (f : Hom source target) :
    (g.comp f).toRatLinearMap = g.toRatLinearMap ∘ₗ f.toRatLinearMap := by rw [comp]

/-- Composition of morphisms is pointwise composition on complex vectors. -/
@[simp]
theorem comp_apply (g : Hom target third) (f : Hom source target) (x : Vℂ) :
    g.comp f x = g (f x) := by
  simp only [toLinearMap_def, comp_toRatLinearMap]
  rw [rationalMapToComplex_comp hℚ hℂ h'ℚ h'ℂ h''ℚ h''ℂ]
  rfl

/-- Left identity law for morphisms of mixed Hodge structures. -/
@[simp]
theorem id_comp (f : Hom source target) : (id target).comp f = f := by
  ext x
  rfl

/-- Right identity law for morphisms of mixed Hodge structures. -/
@[simp]
theorem comp_id (f : Hom source target) : f.comp (id source) = f := by
  ext x
  rfl

/-- Associativity of composition of morphisms of mixed Hodge structures. -/
@[simp]
theorem comp_assoc {V₄ℤ V₄ℚ V₄ℂ : Type*} [AddCommGroup V₄ℤ] [AddCommGroup V₄ℚ] [Module ℚ V₄ℚ]
    [AddCommGroup V₄ℂ] [Module ℂ V₄ℂ]
    {ι₄ℚ : V₄ℤ →ₗ[ℤ] V₄ℚ} {ι₄ℂ : V₄ℤ →ₗ[ℤ] V₄ℂ}
    {h₄ℚ : IsBaseChange ℚ ι₄ℚ} {h₄ℂ : IsBaseChange ℂ ι₄ℂ}
    {fourth : MixedHodgeStructure h₄ℚ h₄ℂ}
    (h : Hom third fourth) (g : Hom target third) (f : Hom source target) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

/-- The zero morphism between two mixed Hodge structures. -/
noncomputable instance instZero : Zero (Hom source target) where
  zero :=
    { toRatLinearMap := 0
      map_mem_WQ := by simp
      map_mem_F := by simp }

/-- Addition of morphisms of mixed Hodge structures, defined on their rational maps. -/
noncomputable instance instAdd : Add (Hom source target) where
  add f g :=
    { toRatLinearMap := f.toRatLinearMap + g.toRatLinearMap
      map_mem_WQ := fun k x hx ↦
        (target.WQ k).add_mem (f.map_mem_WQ k x hx) (g.map_mem_WQ k x hx)
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_add, LinearMap.add_apply]
        exact (target.F p).add_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Negation of a morphism of mixed Hodge structures, defined on its rational map. -/
noncomputable instance instNeg : Neg (Hom source target) where
  neg f :=
    { toRatLinearMap := -f.toRatLinearMap
      map_mem_WQ := fun k x hx ↦ (target.WQ k).neg_mem (f.map_mem_WQ k x hx)
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_neg, LinearMap.neg_apply]
        exact (target.F p).neg_mem (f.map_mem_F p x hx) }

/-- Subtraction of morphisms of mixed Hodge structures, defined on their rational maps. -/
noncomputable instance instSub : Sub (Hom source target) where
  sub f g :=
    { toRatLinearMap := f.toRatLinearMap - g.toRatLinearMap
      map_mem_WQ := fun k x hx ↦
        (target.WQ k).sub_mem (f.map_mem_WQ k x hx) (g.map_mem_WQ k x hx)
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_sub, LinearMap.sub_apply]
        exact (target.F p).sub_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Natural-number multiples of a morphism of mixed Hodge structures. -/
noncomputable instance instSMulNat : SMul ℕ (Hom source target) where
  smul k f :=
    { toRatLinearMap := k • f.toRatLinearMap
      map_mem_WQ := fun j x hx ↦ nsmul_mem (f.map_mem_WQ j x hx) k
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_nsmul, LinearMap.smul_apply]
        exact nsmul_mem (f.map_mem_F p x hx) k }

/-- Integer multiples of a morphism of mixed Hodge structures. -/
noncomputable instance instSMulInt : SMul ℤ (Hom source target) where
  smul k f :=
    { toRatLinearMap := k • f.toRatLinearMap
      map_mem_WQ := fun j x hx ↦ zsmul_mem (f.map_mem_WQ j x hx) k
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_zsmul, LinearMap.smul_apply]
        exact zsmul_mem (f.map_mem_F p x hx) k }

/-- Rational multiples of a morphism of mixed Hodge structures. -/
noncomputable instance instSMulRat : SMul ℚ (Hom source target) where
  smul q f :=
    { toRatLinearMap := q • f.toRatLinearMap
      map_mem_WQ := fun j x hx ↦ Submodule.smul_mem _ q (f.map_mem_WQ j x hx)
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_smul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ (q : ℂ) (f.map_mem_F p x hx) }

/-- Morphisms of mixed Hodge structures form an additive commutative group, transported along the
injection sending a morphism to its underlying rational linear map. -/
noncomputable instance : AddCommGroup (Hom source target) :=
  Function.Injective.addCommGroup (fun f : Hom source target ↦ f.toRatLinearMap)
    (fun _ _ h ↦ ext (LinearMap.congr_fun h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Morphisms of mixed Hodge structures form a `ℚ`-vector space, transported along the same
injection: the datum of a morphism is a `ℚ`-linear map, and both filtrations are stable under
rational scalars. -/
noncomputable instance : Module ℚ (Hom source target) :=
  Function.Injective.module ℚ
    { toFun := fun f : Hom source target ↦ f.toRatLinearMap
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ ext (LinearMap.congr_fun h)) (fun _ _ ↦ rfl)

/-- The zero morphism has the zero rational linear map underneath. -/
@[simp]
theorem zero_toRatLinearMap : (0 : Hom source target).toRatLinearMap = 0 :=
  rfl

/-- Addition of morphisms is addition of their underlying rational linear maps. -/
@[simp]
theorem add_toRatLinearMap (f g : Hom source target) :
    (f + g).toRatLinearMap = f.toRatLinearMap + g.toRatLinearMap :=
  rfl

/-- Negation of a morphism is negation of its underlying rational linear map. -/
@[simp]
theorem neg_toRatLinearMap (f : Hom source target) :
    (-f).toRatLinearMap = -f.toRatLinearMap :=
  rfl

/-- Subtraction of morphisms is subtraction of their underlying rational linear maps. -/
@[simp]
theorem sub_toRatLinearMap (f g : Hom source target) :
    (f - g).toRatLinearMap = f.toRatLinearMap - g.toRatLinearMap :=
  rfl

/-- The zero morphism acts by zero on complex vectors. -/
@[simp]
theorem zero_apply (x : Vℂ) : (0 : Hom source target) x = 0 := by
  simp [toLinearMap_def]

/-- Addition of morphisms is pointwise addition on complex vectors. -/
@[simp]
theorem add_apply (f g : Hom source target) (x : Vℂ) : (f + g) x = f x + g x := by
  simp [toLinearMap_def]

/-- Natural-number multiples of morphisms pass to their underlying rational linear maps. -/
@[simp]
theorem nsmul_toRatLinearMap (k : ℕ) (f : Hom source target) :
    (k • f).toRatLinearMap = k • f.toRatLinearMap :=
  rfl

/-- Integer multiples of morphisms pass to their underlying rational linear maps. -/
@[simp]
theorem zsmul_toRatLinearMap (k : ℤ) (f : Hom source target) :
    (k • f).toRatLinearMap = k • f.toRatLinearMap :=
  rfl

/-- Rational multiples of morphisms pass to their underlying rational linear maps. -/
@[simp]
theorem smul_toRatLinearMap (q : ℚ) (f : Hom source target) :
    (q • f).toRatLinearMap = q • f.toRatLinearMap :=
  rfl

/-- Negation of morphisms is pointwise negation on complex vectors. -/
@[simp]
theorem neg_apply (f : Hom source target) (x : Vℂ) : (-f) x = -f x := by
  simp [toLinearMap_def]

/-- Subtraction of morphisms is pointwise subtraction on complex vectors. -/
@[simp]
theorem sub_apply (f g : Hom source target) (x : Vℂ) : (f - g) x = f x - g x := by
  simp [toLinearMap_def]

/-- Natural-number multiples of morphisms are evaluated pointwise on complex vectors. -/
@[simp]
theorem nsmul_apply (k : ℕ) (f : Hom source target) (x : Vℂ) : (k • f) x = k • f x := by
  simp [toLinearMap_def]

/-- Integer multiples of morphisms are evaluated pointwise on complex vectors. -/
@[simp]
theorem zsmul_apply (k : ℤ) (f : Hom source target) (x : Vℂ) : (k • f) x = k • f x := by
  simp [toLinearMap_def]

/-- Rational multiples of morphisms are evaluated pointwise on complex vectors, the scalar acting
through `ℚ → ℂ`. -/
@[simp]
theorem smul_apply (q : ℚ) (f : Hom source target) (x : Vℂ) : (q • f) x = (q : ℂ) • f x := by
  simp [toLinearMap_def]

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
  exact g.toRatLinearMap.map_add (f.toRatLinearMap x) (h.toRatLinearMap x)

/-- A rational multiple in the outer factor can be pulled out of a composition. -/
@[simp]
theorem smul_comp (q : ℚ) (g : Hom target third) (f : Hom source target) :
    (q • g).comp f = q • g.comp f := by
  ext x
  rfl

/-- A rational multiple in the inner factor can be pulled out of a composition. -/
@[simp]
theorem comp_smul (g : Hom target third) (q : ℚ) (f : Hom source target) :
    g.comp (q • f) = q • g.comp f := by
  ext x
  exact g.toRatLinearMap.map_smul q (f.toRatLinearMap x)

/-- Composing with a zero morphism on the left gives zero. -/
@[simp]
theorem zero_comp (f : Hom source target) : (0 : Hom target third).comp f = 0 := by
  ext x
  rfl

/-- Composing with a zero morphism on the right gives zero. -/
@[simp]
theorem comp_zero (g : Hom target third) : g.comp (0 : Hom source target) = 0 := by
  ext x
  exact g.toRatLinearMap.map_zero

section Graded

/-- The map induced on the `k`-th rational graded piece `grᵂ_k` of the weight filtration. -/
noncomputable def gradedMap (f : Hom source target) (k : ℤ) :
    weightGradedRat source.WQ k →ₗ[ℚ] weightGradedRat target.WQ k :=
  weightGradedRatMap source.WQ target.WQ f.toRatLinearMap f.map_mem_WQ k

/-- The graded map sends the class of a vector to the class of its image. -/
@[simp]
theorem gradedMap_mk (f : Hom source target) (k : ℤ) (x : source.WQ k) :
    f.gradedMap k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f.toRatLinearMap x, f.map_mem_WQ k x x.2⟩ :=
  weightGradedRatMap_mk source.WQ target.WQ f.toRatLinearMap f.map_mem_WQ k x

/-- The restriction of the complex action to a step of the complexified weight filtration. -/
noncomputable def restrictWC (f : Hom source target) (k : ℤ) :
    rationalToComplexSubmodule hℚ hℂ (source.WQ k) →ₗ[ℂ]
      rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ k) :=
  f.toLinearMap.restrict fun x hx ↦
    map_rationalToComplexSubmodule_le hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap (f.map_WQ_le k) ⟨x, hx, rfl⟩

/-- The restriction to a step of the complexified weight filtration acts by the complex action. -/
@[simp]
theorem coe_restrictWC_apply (f : Hom source target) (k : ℤ)
    (x : rationalToComplexSubmodule hℚ hℂ (source.WQ k)) :
    (f.restrictWC k x : V'ℂ) = f x :=
  (rfl)

/-- The map induced on the `k`-th graded piece of the complexified weight filtration
`TauCeti.Hodge.MixedHodgeStructure.WC`, spelled out in the unfolded form in which
`TauCeti.Hodge.gradedComplexEquiv` presents that filtration. -/
noncomputable def complexGradedMap (f : Hom source target) (k : ℤ) :
    weightGradedComplex (fun j ↦ rationalToComplexSubmodule hℚ hℂ (source.WQ j)) k →ₗ[ℂ]
      weightGradedComplex (fun j ↦ rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ j)) k :=
  weightGradedComplexMap _ _ f.toLinearMap (fun j x hx ↦ (f.restrictWC j ⟨x, hx⟩).2) k

/-- The complex graded map sends the class of a vector to the class of its image. -/
@[simp]
theorem complexGradedMap_mk (f : Hom source target) (k : ℤ)
    (x : rationalToComplexSubmodule hℚ hℂ (source.WQ k)) :
    f.complexGradedMap k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.restrictWC k x) :=
  weightGradedComplexMap_mk _ _ f.toLinearMap (fun j x hx ↦ (f.restrictWC j ⟨x, hx⟩).2) k x

/-- **The comparison `TauCeti.Hodge.gradedComplexEquiv` is natural in the morphism**: the square
formed by the two induced maps and that comparison commutes. -/
theorem gradedComplexEquiv_baseChange_gradedMap (f : Hom source target) (k : ℤ)
    (t : ℂ ⊗[ℚ] weightGradedRat source.WQ k) :
    gradedComplexEquiv h'ℚ h'ℂ target.WQ target.WQ_monotone k
        ((f.gradedMap k).baseChange ℂ t) =
      f.complexGradedMap k
        (gradedComplexEquiv hℚ hℂ source.WQ source.WQ_monotone k t) :=
  gradedComplexEquiv_baseChange_weightGradedRatMap hℚ hℂ h'ℚ h'ℂ source.WQ source.WQ_monotone
    target.WQ target.WQ_monotone f.toRatLinearMap f.map_mem_WQ k t

/-- **A morphism of mixed Hodge structures induces a morphism of the pure Hodge structures carried
by the weight-graded pieces.** -/
noncomputable def gradedHom (f : Hom source target) (k : ℤ) :
    HodgeStructure.Hom (source.gradedHodgeStructure k) (target.gradedHodgeStructure k) where
  toIntLinearMap := (f.gradedMap k).restrictScalars ℤ
  map_mem_F := by
    intro p x hx
    rw [gradedHodgeStructure_F, mem_gradedF_iff] at hx
    obtain ⟨y, hy, hmk⟩ := hx
    rw [integralMapToComplex_ratTensorMap, gradedHodgeStructure_F, mem_gradedF_iff]
    refine ⟨f.restrictWC k y, f.map_mem_F p _ hy, ?_⟩
    rw [gradedComplexEquiv_baseChange_gradedMap, ← hmk, complexGradedMap_mk]

/-- The integral map underlying the induced morphism of pure Hodge structures is the graded
map. -/
@[simp]
theorem gradedHom_toIntLinearMap (f : Hom source target) (k : ℤ) :
    (f.gradedHom k).toIntLinearMap = (f.gradedMap k).restrictScalars ℤ := by rw [gradedHom]

/-- The graded map of an identity morphism is the identity. -/
@[simp]
theorem gradedMap_id (source : MixedHodgeStructure hℚ hℂ) (k : ℤ) :
    (id source).gradedMap k = LinearMap.id :=
  weightGradedRatMap_id source.WQ k

/-- The graded map of a composite is the composite of the graded maps. -/
@[simp]
theorem gradedMap_comp (g : Hom target third) (f : Hom source target) (k : ℤ) :
    (g.comp f).gradedMap k = (g.gradedMap k) ∘ₗ (f.gradedMap k) :=
  weightGradedRatMap_comp source.WQ target.WQ third.WQ f.toRatLinearMap f.map_mem_WQ
    g.toRatLinearMap g.map_mem_WQ k

/-- The complex graded map of an identity morphism is the identity. -/
@[simp]
theorem complexGradedMap_id (source : MixedHodgeStructure hℚ hℂ) (k : ℤ) :
    (id source).complexGradedMap k = LinearMap.id := by
  simpa only [complexGradedMap, toLinearMap_def, id_toRatLinearMap,
    rationalMapToComplex_id] using weightGradedComplexMap_id
      (fun j ↦ rationalToComplexSubmodule hℚ hℂ (source.WQ j)) k

/-- The complex graded map of a composite is the composite of the complex graded maps. -/
@[simp]
theorem complexGradedMap_comp (g : Hom target third) (f : Hom source target) (k : ℤ) :
    (g.comp f).complexGradedMap k = (g.complexGradedMap k) ∘ₗ (f.complexGradedMap k) := by
  simpa only [complexGradedMap, toLinearMap_def, comp_toRatLinearMap,
    rationalMapToComplex_comp hℚ hℂ h'ℚ h'ℂ h''ℚ h''ℂ] using
      weightGradedComplexMap_comp
        (fun j ↦ rationalToComplexSubmodule hℚ hℂ (source.WQ j))
        (fun j ↦ rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ j))
        (fun j ↦ rationalToComplexSubmodule h''ℚ h''ℂ (third.WQ j))
        f.toLinearMap (fun j x hx ↦ (f.restrictWC j ⟨x, hx⟩).2)
        g.toLinearMap (fun j x hx ↦ (g.restrictWC j ⟨x, hx⟩).2) k

/-- Passage to the weight-graded pieces sends identities to identities. -/
@[simp]
theorem gradedHom_id (source : MixedHodgeStructure hℚ hℂ) (k : ℤ) :
    (id source).gradedHom k = HodgeStructure.Hom.id (source.gradedHodgeStructure k) := by
  refine HodgeStructure.Hom.ext fun x ↦ ?_
  rw [gradedHom_toIntLinearMap, HodgeStructure.Hom.id_toIntLinearMap,
    LinearMap.restrictScalars_apply, gradedMap_id, LinearMap.id_apply, LinearMap.id_apply]

/-- Passage to the weight-graded pieces is compatible with composition. -/
@[simp]
theorem gradedHom_comp (g : Hom target third) (f : Hom source target) (k : ℤ) :
    (g.comp f).gradedHom k = (g.gradedHom k).comp (f.gradedHom k) := by
  refine HodgeStructure.Hom.ext fun x ↦ ?_
  rw [gradedHom_toIntLinearMap, HodgeStructure.Hom.comp_toIntLinearMap, LinearMap.comp_apply,
    gradedHom_toIntLinearMap, gradedHom_toIntLinearMap, LinearMap.restrictScalars_apply,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, gradedMap_comp,
    LinearMap.comp_apply]

end Graded

end Hom

end MixedHodgeStructure

end TauCeti.Hodge
