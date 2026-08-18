/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Isomorphism of representations and of the modules they carry

Mathlib's `Representation.IntertwiningMap.equivLinearMapAsModule` identifies the intertwining maps
`ρ → σ` with the `k[G]`-linear maps `ρ.asModule → σ.asModule`, but not the *isomorphisms* with the
*isomorphisms*: an equivalence of representations is a bijective intertwining map, while a linear
equivalence of modules carries its inverse as data. This file supplies the missing dictionary, in
both directions and in the form that is usually wanted, an equivalence of `Nonempty`s.

The point of the dictionary is that classification statements are naturally proved on one side and
used on the other. The isomorphism classes of simple `k[G]`-modules are what the semisimple-algebra
theory counts, while the objects being classified are representations.

## Main results

* `TauCeti.Representation.equivOfAsModuleLinearEquiv`: a `k[G]`-linear isomorphism
  `ρ.asModule ≃ₗ σ.asModule` is an equivalence of representations.
* `TauCeti.Representation.asModuleLinearEquivOfEquiv`: the converse.
* `TauCeti.Representation.nonempty_equiv_iff`: the two notions of isomorphism agree.
* `TauCeti.fdRepIsoOfAsModuleLinearEquiv`: over a commutative ring, and for module-finite carriers,
  such an isomorphism of modules is an isomorphism of the objects of `FDRep k G` that the
  representations name.
* `FDRep.of_ρ_eq_self`: rebundling the representation carried by an object of `FDRep k G`
  returns that object.
* `TauCeti.nonempty_fdRepIso_iff`: the two notions of isomorphism agree on `FDRep k G`, so a
  classification proved for representations reads off as a classification of objects.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable {ρ : _root_.Representation k G V} {σ : _root_.Representation k G W}

/-- **A `k[G]`-linear isomorphism of the attached modules is an equivalence of representations.**
This reads `Representation.IntertwiningMap.equivLinearMapAsModule` backwards: the `k[G]`-linear map
underlying `f` is an intertwining map, and it is bijective. -/
noncomputable def equivOfAsModuleLinearEquiv (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) : ρ.Equiv σ :=
  _root_.Representation.IntertwiningMap.ofBijective
    ((_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm f.toLinearMap)
    f.bijective

@[simp]
theorem equivOfAsModuleLinearEquiv_apply (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) (v : V) :
    equivOfAsModuleLinearEquiv f v = σ.asModuleEquiv (f (ρ.asModuleEquiv.symm v)) :=
  (rfl)

/-- **An equivalence of representations is a `k`[G]`-linear isomorphism of the attached modules.**
The inverse of `TauCeti.Representation.equivOfAsModuleLinearEquiv`; the underlying map is the one
`Representation.IntertwiningMap.equivLinearMapAsModule` attaches to the intertwining map. -/
noncomputable def asModuleLinearEquivOfEquiv (φ : ρ.Equiv σ) : ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap)
    φ.bijective

@[simp]
theorem asModuleLinearEquivOfEquiv_apply (φ : ρ.Equiv σ) (x : ρ.asModule) :
    asModuleLinearEquivOfEquiv φ x = σ.asModuleEquiv.symm (φ (ρ.asModuleEquiv x)) :=
  (rfl)

@[simp]
theorem equivOfAsModuleLinearEquiv_asModuleLinearEquivOfEquiv (φ : ρ.Equiv σ) :
    equivOfAsModuleLinearEquiv (asModuleLinearEquivOfEquiv φ) = φ := by
  ext v
  simp

@[simp]
theorem asModuleLinearEquivOfEquiv_equivOfAsModuleLinearEquiv
    (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    asModuleLinearEquivOfEquiv (equivOfAsModuleLinearEquiv f) = f := by
  ext x
  simp

/-- **The two notions of isomorphism agree.** Two representations are equivalent exactly when the
`k[G]`-modules they carry are isomorphic. -/
theorem nonempty_equiv_iff :
    Nonempty (ρ.Equiv σ) ↔ Nonempty (ρ.asModule ≃ₗ[k[G]] σ.asModule) :=
  ⟨fun ⟨φ⟩ ↦ ⟨asModuleLinearEquivOfEquiv φ⟩, fun ⟨f⟩ ↦ ⟨equivOfAsModuleLinearEquiv f⟩⟩

end Representation

universe u v

variable {k V W : Type u} {G : Type v} [CommRing k] [Monoid G]
variable [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [AddCommGroup W] [Module k W] [Module.Finite k W]
variable {ρ : Representation k G V} {σ : Representation k G W}

/-- **A `k[G]`-linear isomorphism of the attached modules is an isomorphism in `FDRep k G`.** The
finitely generated representations are a full subcategory of `Rep k G`, where an equivalence of
representations is already an isomorphism. -/
noncomputable def fdRepIsoOfAsModuleLinearEquiv (f : ρ.asModule ≃ₗ[k[G]] σ.asModule) :
    FDRep.of ρ ≅ FDRep.of σ :=
  (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).preimageIso
    (Rep.mkIso (Representation.equivOfAsModuleLinearEquiv f))

/-- Rebundling the representation carried by an object of `FDRep k G` returns that object. -/
theorem _root_.FDRep.of_ρ_eq_self (X : FDRep k G) : FDRep.of X.ρ = X := rfl

/-- **The two notions of isomorphism agree on `FDRep k G`.** Two objects are isomorphic exactly when
the representations they carry are equivalent, so a classification of representations up to
equivalence is a classification of the objects of `FDRep k G` up to isomorphism. -/
theorem nonempty_fdRepIso_iff {X Y : FDRep k G} :
    Nonempty (X ≅ Y) ↔ Nonempty (_root_.Representation.Equiv X.ρ Y.ρ) :=
  by
    constructor
    · rintro ⟨i⟩
      have e := _root_.Representation.equivOfIso
        ((CategoryTheory.forget₂ (FDRep k G) (Rep k G)).mapIso i)
      -- Transport the equivalence along the forgetful functor's representation comparison.
      rw [FDRep.forget₂_ρ, FDRep.forget₂_ρ] at e
      exact ⟨e⟩
    · rintro ⟨φ⟩
      have i := fdRepIsoOfAsModuleLinearEquiv
        (Representation.asModuleLinearEquivOfEquiv φ)
      -- `FDRep.of_ρ_eq_self` records the definitional object identifications here.
      exact ⟨i⟩

end TauCeti
