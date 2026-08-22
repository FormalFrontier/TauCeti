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
base-change model in `TauCeti.Hodge.rationalMapToComplex_latticeConj`; it is what lets a
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
theorem apply_rational (f : Hom source target) (z : ℂ) (x : Vℚ) :
    f (rationalToComplexLinearEquiv hℚ hℂ (z ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv h'ℚ h'ℂ (z ⊗ₜ[ℚ] f.toRatLinearMap x) :=
  rationalMapToComplex_rationalToComplexLinearEquiv_tmul hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap z x

/-- The complex action of a morphism of mixed Hodge structures commutes with lattice-induced
conjugation. -/
@[simp]
theorem commutes_conj (f : Hom source target) (x : Vℂ) :
    f (latticeConj hℂ x) = latticeConj h'ℂ (f x) :=
  rationalMapToComplex_latticeConj hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap x

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
  simp only [WC_def, toLinearMap]
  exact map_rationalToComplexSubmodule_le hℚ hℂ h'ℚ h'ℂ f.toRatLinearMap (f.map_WQ_le k)

/-- Elementwise form of preservation of the complexified weight filtration. -/
theorem map_mem_WC (f : Hom source target) (k : ℤ) {x : Vℂ} (hx : x ∈ source.WC k) :
    f x ∈ target.WC k :=
  f.map_WC_le k ⟨x, hx, rfl⟩

/-- Preservation of the complexified weight filtration, with
`TauCeti.Hodge.MixedHodgeStructure.WC` spelled out. This is the form the weight-graded quotients
of `TauCeti.Hodge.gradedComplexEquiv` are stated in. -/
theorem map_mem_rationalToComplexSubmodule (f : Hom source target) (k : ℤ) {x : Vℂ}
    (hx : x ∈ rationalToComplexSubmodule hℚ hℂ (source.WQ k)) :
    f x ∈ rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ k) := by
  rw [← WC_def]
  exact f.map_mem_WC k (by rw [WC_def]; exact hx)

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
  simp [toLinearMap]

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
  simp only [toLinearMap, comp_toRatLinearMap]
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

/-- Morphisms of mixed Hodge structures form an additive commutative group, transported along the
injection sending a morphism to its underlying rational linear map. -/
noncomputable instance : AddCommGroup (Hom source target) :=
  Function.Injective.addCommGroup (fun f : Hom source target ↦ f.toRatLinearMap)
    (fun _ _ h ↦ ext (LinearMap.congr_fun h)) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

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
  simp [toLinearMap]

/-- Addition of morphisms is pointwise addition on complex vectors. -/
@[simp]
theorem add_apply (f g : Hom source target) (x : Vℂ) : (f + g) x = f x + g x := by
  simp [toLinearMap]

section Graded

/-- The restriction of the underlying rational map to a step of the weight filtration. -/
noncomputable def restrictWQ (f : Hom source target) (k : ℤ) :
    source.WQ k →ₗ[ℚ] target.WQ k :=
  f.toRatLinearMap.restrict fun x hx ↦ f.map_mem_WQ k x hx

/-- The restriction to a weight step acts by the underlying rational map. -/
@[simp]
theorem coe_restrictWQ (f : Hom source target) (k : ℤ) (x : source.WQ k) :
    (f.restrictWQ k x : V'ℚ) = f.toRatLinearMap x :=
  (rfl)

/-- The map induced on the `k`-th rational graded piece `grᵂ_k` of the weight filtration. -/
noncomputable def gradedMap (f : Hom source target) (k : ℤ) :
    weightGradedRat source.WQ k →ₗ[ℚ] weightGradedRat target.WQ k :=
  Submodule.mapQ _ _ (f.restrictWQ k) fun x hx ↦ f.map_mem_WQ (k - 1) x hx

/-- The graded map sends the class of a vector to the class of its image. -/
@[simp]
theorem gradedMap_mk (f : Hom source target) (k : ℤ) (x : source.WQ k) :
    f.gradedMap k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.restrictWQ k x) :=
  (rfl)

/-- The map induced on the `k`-th graded piece of the complexified weight filtration
`TauCeti.Hodge.MixedHodgeStructure.WC`, spelled out in the unfolded form in which
`TauCeti.Hodge.gradedComplexEquiv` presents that filtration. -/
noncomputable def complexGradedMap (f : Hom source target) (k : ℤ) :
    weightGradedComplex (fun j ↦ rationalToComplexSubmodule hℚ hℂ (source.WQ j)) k →ₗ[ℂ]
      weightGradedComplex (fun j ↦ rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ j)) k :=
  Submodule.mapQ _ _
    (f.toLinearMap.restrict (p := rationalToComplexSubmodule hℚ hℂ (source.WQ k))
      (q := rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ k))
      fun _ hx ↦ f.map_mem_rationalToComplexSubmodule k hx)
    fun _ hx ↦ f.map_mem_rationalToComplexSubmodule (k - 1) hx

/-- The complex graded map sends the class of a vector to the class of its image. -/
@[simp]
theorem complexGradedMap_mk (f : Hom source target) (k : ℤ)
    (x : rationalToComplexSubmodule hℚ hℂ (source.WQ k)) :
    f.complexGradedMap k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.toLinearMap.restrict
        (p := rationalToComplexSubmodule hℚ hℂ (source.WQ k))
        (q := rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ k))
        (fun _ hx ↦ f.map_mem_rationalToComplexSubmodule k hx) x) :=
  (rfl)

/-- **Complexification commutes with passage to the weight-graded pieces**: the square formed by
the two induced maps and the comparison `TauCeti.Hodge.gradedComplexEquiv` commutes. -/
theorem gradedComplexEquiv_baseChange_gradedMap (f : Hom source target) (k : ℤ)
    (t : ℂ ⊗[ℚ] weightGradedRat source.WQ k) :
    gradedComplexEquiv h'ℚ h'ℂ target.WQ target.WQ_monotone k
        ((f.gradedMap k).baseChange ℂ t) =
      f.complexGradedMap k
        (gradedComplexEquiv hℚ hℂ source.WQ source.WQ_monotone k t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [LinearMap.baseChange_tmul, gradedMap_mk, gradedComplexEquiv_tmul_mk,
          gradedComplexEquiv_tmul_mk, complexGradedMap_mk]
        refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
        rw [LinearMap.coe_restrict_apply, coe_rationalToComplexSubmoduleEquiv,
          coe_rationalToComplexSubmoduleEquiv, LinearMap.baseChange_tmul,
          LinearMap.baseChange_tmul, Submodule.subtype_apply, Submodule.subtype_apply,
          coe_restrictWQ, apply_rational]
  | add x y hx hy => simp only [map_add, hx, hy]

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
    refine ⟨f.toLinearMap.restrict (p := rationalToComplexSubmodule hℚ hℂ (source.WQ k))
      (q := rationalToComplexSubmodule h'ℚ h'ℂ (target.WQ k))
      (fun _ hz ↦ f.map_mem_rationalToComplexSubmodule k hz) y, f.map_mem_F p _ hy, ?_⟩
    rw [gradedComplexEquiv_baseChange_gradedMap, ← hmk, complexGradedMap_mk]

/-- The integral map underlying the induced morphism of pure Hodge structures is the graded
map. -/
@[simp]
theorem gradedHom_toIntLinearMap (f : Hom source target) (k : ℤ) :
    (f.gradedHom k).toIntLinearMap = (f.gradedMap k).restrictScalars ℤ := by rw [gradedHom]

/-- The graded map of an identity morphism is the identity. -/
@[simp]
theorem gradedMap_id (source : MixedHodgeStructure hℚ hℂ) (k : ℤ) :
    (id source).gradedMap k = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- The graded map of a composite is the composite of the graded maps. -/
@[simp]
theorem gradedMap_comp (g : Hom target third) (f : Hom source target) (k : ℤ) :
    (g.comp f).gradedMap k = (g.gradedMap k) ∘ₗ (f.gradedMap k) := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

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
