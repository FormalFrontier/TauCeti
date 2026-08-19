/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Simple objects of `FDRep k G` are the irreducible representations

`CategoryTheory.Simple` is the categorical notion of irreducibility, phrased with monomorphisms
into an object, while `Representation.IsIrreducible` is the lattice-theoretic one, phrased with
the subrepresentations of a representation.  For a finite-dimensional representation the two say
the same thing, and this file proves it.

The translation is carried by the space of intertwiners: a morphism of `FDRep k G` is exactly a
linear map between the underlying spaces commuting with the two actions, so
`FDRep.homLinearEquivIntertwiningMap` identifies a morphism space of `FDRep k G` with a space of
intertwiners.  Through that identification a monomorphism is an injective map and an isomorphism a
bijective one, while the subobjects of an object are its subrepresentations; the dictionary between
the two notions of irreducibility follows.

## Main definitions

* `FDRep.homLinearEquivIntertwiningMap`: the morphism space `V ⟶ W` of `FDRep k G` is the space of
  intertwiners from `V.ρ` to `W.ρ`.

## Main results

* `FDRep.mono_iff_injective` and `FDRep.isIso_iff_bijective`: monomorphisms and isomorphisms of
  `FDRep k G` are the injective and the bijective intertwiners.
* `FDRep.simple_iff_isIrreducible`: **an object of `FDRep k G` is simple exactly when its
  representation is irreducible**.
* `FDRep.finrank_hom_eq_finrank_intertwiningMap`: the two morphism spaces have the same dimension.

## References

* Aristotle added this layer of abstraction: general infrastructure about FDRep k G.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4: completeness and irreducibility (the classification)
-/

public section

open CategoryTheory Representation

namespace FDRep

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The linear map underlying a morphism of `FDRep k G`. -/
@[expose]
def homLinearMap {V W : FDRep k G} (f : V ⟶ W) : V →ₗ[k] W := f.hom.hom.hom

theorem homLinearMap_comm {V W : FDRep k G} (f : V ⟶ W) (g : G) (v : V) :
    homLinearMap f (V.ρ g v) = W.ρ g (homLinearMap f v) := by
  have h := f.comm g
  have hv := congrArg (fun φ : V.V ⟶ W.V => φ.hom.hom v) h
  simp only [homLinearMap]
  simpa using hv

theorem hom_ext {V W : FDRep k G} {f f' : V ⟶ W}
    (h : ∀ v : V, homLinearMap f v = homLinearMap f' v) : f = f' := by
  ext v
  exact h v

@[simp]
theorem homLinearMap_zero (V W : FDRep k G) : homLinearMap (0 : V ⟶ W) = 0 := rfl

@[simp]
theorem homLinearMap_id (V : FDRep k G) (v : V) : homLinearMap (𝟙 V) v = v := rfl

@[simp]
theorem homLinearMap_comp {V W X : FDRep k G} (f : V ⟶ W) (g : W ⟶ X) (v : V) :
    homLinearMap (f ≫ g) v = homLinearMap g (homLinearMap f v) := rfl

theorem eq_zero_iff {V W : FDRep k G} (f : V ⟶ W) : f = 0 ↔ ∀ v : V, homLinearMap f v = 0 :=
  ⟨fun h v => by rw [h]; rfl, fun h => hom_ext fun v => by rw [h v]; rfl⟩

/-- A morphism of `FDRep k G`, read as an intertwiner of the underlying representations. -/
@[expose]
noncomputable def homIntertwiningMap {V W : FDRep k G} (f : V ⟶ W) :
    Representation.IntertwiningMap V.ρ W.ρ :=
  (homLinearMap f).intertwiningMap_of_isIntertwiningMap V.ρ W.ρ (homLinearMap_comm f)

/-- The kernel of `homIntertwiningMap f`, as a submodule, is the kernel of the underlying linear
map.  Stating this once keeps the proofs independent of how the intertwiner wrapper unfolds. -/
@[simp]
theorem toSubmodule_ker_homIntertwiningMap {V W : FDRep k G} (f : V ⟶ W) :
    (homIntertwiningMap f).ker.toSubmodule = LinearMap.ker (homLinearMap f) := rfl

/-- The range of `homIntertwiningMap f`, as a submodule, is the range of the underlying linear
map.  The companion of `toSubmodule_ker_homIntertwiningMap`. -/
@[simp]
theorem toSubmodule_range_homIntertwiningMap {V W : FDRep k G} (f : V ⟶ W) :
    (homIntertwiningMap f).range.toSubmodule = LinearMap.range (homLinearMap f) := rfl

/-- An intertwiner of the underlying representations, read as a morphism of `FDRep k G`. -/
@[expose]
noncomputable def ofIntertwiningMap {V W : FDRep k G}
    (f : Representation.IntertwiningMap V.ρ W.ρ) : V ⟶ W where
  hom := InducedCategory.homMk (ModuleCat.ofHom f.toLinearMap)
  comm g := by
    ext v
    simpa using IntertwiningMap.isIntertwining V.ρ W.ρ f g v

@[simp]
theorem homLinearMap_ofIntertwiningMap {V W : FDRep k G}
    (f : Representation.IntertwiningMap V.ρ W.ρ) (v : V) :
    homLinearMap (ofIntertwiningMap f) v = f v := rfl

/-- **A morphism of `FDRep k G` is an intertwiner**: the morphism space `V ⟶ W` is linearly
isomorphic to the space of intertwiners from `V.ρ` to `W.ρ`. -/
@[expose]
noncomputable def homLinearEquivIntertwiningMap (V W : FDRep k G) :
    (V ⟶ W) ≃ₗ[k] Representation.IntertwiningMap V.ρ W.ρ where
  toFun := homIntertwiningMap
  invFun := ofIntertwiningMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem homLinearEquivIntertwiningMap_apply {V W : FDRep k G} (f : V ⟶ W) (v : V) :
    homLinearEquivIntertwiningMap V W f v = homLinearMap f v := rfl

@[simp]
theorem homLinearMap_homLinearEquivIntertwiningMap_symm {V W : FDRep k G}
    (f : Representation.IntertwiningMap V.ρ W.ρ) (v : V) :
    homLinearMap ((homLinearEquivIntertwiningMap V W).symm f) v = f v := rfl

/-- The morphism space of `FDRep k G` and the space of intertwiners have the same dimension. -/
theorem finrank_hom_eq_finrank_intertwiningMap (V W : FDRep k G) :
    Module.finrank k (V ⟶ W) = Module.finrank k (Representation.IntertwiningMap V.ρ W.ρ) :=
  (homLinearEquivIntertwiningMap V W).finrank_eq

/-! ### Monomorphisms and isomorphisms -/

/-- The inclusion of a subrepresentation, as a morphism of `FDRep k G`. -/
@[expose]
noncomputable def subtypeHom {V : FDRep k G} (U : Subrepresentation V.ρ) :
    FDRep.of U.toRepresentation ⟶ V :=
  ofIntertwiningMap (V := FDRep.of U.toRepresentation)
    (U.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
      U.toRepresentation V.ρ fun _ _ => rfl)

@[simp]
theorem homLinearMap_subtypeHom {V : FDRep k G} (U : Subrepresentation V.ρ)
    (u : U.toSubmodule) : homLinearMap (subtypeHom U) u = (u : V) := rfl

/-- **A morphism of `FDRep k G` is a monomorphism exactly when it is injective**: monicity in the
category is detected on the underlying linear map. -/
theorem mono_iff_injective {V W : FDRep k G} (f : V ⟶ W) :
    Mono f ↔ Function.Injective (homLinearMap f) := by
  constructor
  · intro hmono
    rw [← LinearMap.ker_eq_bot]
    set K : Subrepresentation V.ρ := (homIntertwiningMap f).ker with hK
    have hKsub : K.toSubmodule = LinearMap.ker (homLinearMap f) := by
      rw [hK]; exact toSubmodule_ker_homIntertwiningMap f
    have hcomp : subtypeHom K ≫ f = 0 := by
      refine (eq_zero_iff _).mpr fun u => ?_
      have hu : (u : V) ∈ LinearMap.ker (homLinearMap f) := by rw [← hKsub]; exact u.2
      rw [homLinearMap_comp, homLinearMap_subtypeHom]
      simpa using hu
    have hzero : subtypeHom K = 0 :=
      hmono.right_cancellation _ _ (by rw [hcomp, Limits.zero_comp])
    rw [← hKsub, Submodule.eq_bot_iff]
    intro x hx
    have hx0 := (eq_zero_iff (subtypeHom K)).mp hzero ⟨x, hx⟩
    exact hx0
  · intro hinj
    constructor
    intro Z a b hab
    refine hom_ext fun z => hinj ?_
    have := congrArg (fun φ : Z ⟶ W => homLinearMap φ z) hab
    simpa using this

/-- **A morphism of `FDRep k G` is an isomorphism exactly when it is bijective**: an intertwiner
with a set-theoretic inverse has an inverse in the category, the inverse being automatically
equivariant. -/
theorem isIso_iff_bijective {V W : FDRep k G} (f : V ⟶ W) :
    IsIso f ↔ Function.Bijective (homLinearMap f) := by
  constructor
  · intro hiso
    refine ⟨fun x y hxy => ?_, fun w => ⟨homLinearMap (inv f) w, ?_⟩⟩
    · have hx := congrArg (fun φ : V ⟶ V => homLinearMap φ x) (IsIso.hom_inv_id f)
      have hy := congrArg (fun φ : V ⟶ V => homLinearMap φ y) (IsIso.hom_inv_id f)
      simp only [homLinearMap_comp, homLinearMap_id] at hx hy
      rw [← hx, ← hy, hxy]
    · have hw := congrArg (fun φ : W ⟶ W => homLinearMap φ w) (IsIso.inv_hom_id f)
      exact hw
  · intro hbij
    let e : V ≃ₗ[k] W := LinearEquiv.ofBijective (homLinearMap f) hbij
    have hinv : ∀ w : W, homLinearMap f (e.symm w) = w := fun w => e.apply_symm_apply w
    let g : W ⟶ V := ofIntertwiningMap
      ((e.symm : W →ₗ[k] V).intertwiningMap_of_isIntertwiningMap W.ρ V.ρ (by
        intro g w
        apply hbij.injective
        simp only [LinearEquiv.coe_coe]
        rw [hinv, homLinearMap_comm, hinv]))
    refine ⟨g, hom_ext fun v => ?_, hom_ext fun w => ?_⟩
    · have hv : homLinearMap f (e.symm (homLinearMap f v)) = homLinearMap f v := hinv _
      have := hbij.injective hv
      simpa [g] using this
    · simpa [g] using hinv w

/-! ### Simplicity -/

/-- **Simple objects of `FDRep k G` are the irreducible representations.** -/
theorem simple_iff_isIrreducible (V : FDRep k G) :
    Simple V ↔ Representation.IsIrreducible V.ρ := by
  constructor
  · intro hsimple
    have hne : (⊥ : Subrepresentation V.ρ) ≠ ⊤ := by
      intro hbot
      have hzero : ∀ v : V, v = 0 := by
        intro v
        have hv : v ∈ (⊤ : Subrepresentation V.ρ).toSubmodule := by
          rw [Subrepresentation.toSubmodule_top]; exact Submodule.mem_top
        rw [← hbot, Subrepresentation.toSubmodule_bot] at hv
        simpa using hv
      exact id_nonzero V ((eq_zero_iff (𝟙 V)).mpr fun v => by
        simpa using hzero v)
    have hnontriv : Nontrivial (Subrepresentation V.ρ) := ⟨⊥, ⊤, hne⟩
    refine ⟨fun U => ?_⟩
    by_cases hU : U = ⊥
    · exact Or.inl hU
    · refine Or.inr ?_
      have hmono : Mono (subtypeHom U) :=
        (mono_iff_injective _).mpr fun _ _ hxy => Subtype.ext hxy
      have hne0 : subtypeHom U ≠ 0 := by
        intro h0
        apply hU
        refine Subrepresentation.toSubmodule_injective ?_
        rw [Subrepresentation.toSubmodule_bot, Submodule.eq_bot_iff]
        intro x hx
        exact (eq_zero_iff (subtypeHom U)).mp h0 ⟨x, hx⟩
      have hiso : IsIso (subtypeHom U) := (Simple.mono_isIso_iff_nonzero _).mpr hne0
      have hsurj := ((isIso_iff_bijective _).mp hiso).2
      refine Subrepresentation.toSubmodule_injective ?_
      rw [Subrepresentation.toSubmodule_top, Submodule.eq_top_iff']
      intro v
      obtain ⟨u, hu⟩ := hsurj v
      rw [← hu]
      exact u.2
  · intro hirr
    have hsimpleOrder : IsSimpleOrder (Subrepresentation V.ρ) := hirr
    refine ⟨fun {W} f _ => ⟨fun hiso h0 => ?_, fun hne => ?_⟩⟩
    · have hbij := (isIso_iff_bijective f).mp hiso
      have hbot : (⊥ : Subrepresentation V.ρ) = ⊤ := by
        refine Subrepresentation.toSubmodule_injective ?_
        rw [Subrepresentation.toSubmodule_bot, Subrepresentation.toSubmodule_top,
          eq_comm, Submodule.eq_bot_iff]
        intro x _
        obtain ⟨w, hw⟩ := hbij.2 x
        rw [← hw, h0]
        rfl
      exact absurd hbot bot_ne_top
    · have hinj := (mono_iff_injective f).mp ‹Mono f›
      set R : Subrepresentation V.ρ := (homIntertwiningMap f).range with hR
      have hRsub : R.toSubmodule = LinearMap.range (homLinearMap f) := by
        rw [hR]; exact toSubmodule_range_homIntertwiningMap f
      have hRne : R ≠ ⊥ := by
        intro hbot
        apply hne
        refine (eq_zero_iff f).mpr fun w => ?_
        have hmem : homLinearMap f w ∈ R.toSubmodule := by
          rw [hRsub]; exact ⟨w, rfl⟩
        rw [hbot, Subrepresentation.toSubmodule_bot] at hmem
        simpa using hmem
      have hRtop : R = ⊤ := (eq_bot_or_eq_top R).resolve_left hRne
      have hsurj : Function.Surjective (homLinearMap f) := by
        intro v
        have hv : v ∈ R.toSubmodule := by
          rw [hRtop, Subrepresentation.toSubmodule_top]; exact Submodule.mem_top
        rw [hRsub] at hv
        exact hv
      exact (isIso_iff_bijective f).mpr ⟨hinj, hsurj⟩

end FDRep
