/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Galois.Basic
public import TauCeti.CategoryTheory.Action.Transitive

/-!
# Connected `G`-sets are the transitive ones

An object of a category is *connected* in the sense of
`CategoryTheory.PreGaloisCategory.IsConnected` when it is not initial and admits no nontrivial
subobject. This file identifies that condition for `G`-sets: an object of `Action (Type u) G` is
connected exactly when it is nonempty and `G` acts transitively on it, which is
`TauCeti.isTransitiveAction`.

Mathlib proves the same statement for *finite* `G`-sets in
`CategoryTheory.Action.isConnected_iff_transitive`, but that proof runs through the fibre functor
of the Galois category `Action FintypeCat G`, machinery unavailable here: `Action (Type u) G` has
objects with infinite underlying type and is not a Galois category. The argument is instead run
directly, over the two facts about the forgetful functor `Action (Type u) G ⥤ Type u` that replace
it: it preserves and reflects monomorphisms, because it preserves and reflects finite limits, and a
`G`-set is initial exactly when its underlying type is empty.

## Main declarations

* `TauCeti.isInitialActionOfIsEmpty` and `TauCeti.isEmpty_of_isInitial_action`: a `G`-set is
  initial exactly when its underlying type is empty.
* `TauCeti.mono_action_iff_injective`: a map of `G`-sets is a monomorphism exactly when it is
  injective.
* `TauCeti.isConnected_action_iff_isTransitiveAction`: **a `G`-set is connected exactly when it is
  transitive.**
-/

public section
noncomputable section

universe u v

namespace TauCeti

open CategoryTheory Limits

variable {G : Type v} [Monoid G]

/-- A `G`-set whose underlying type is empty is an initial object. -/
def isInitialActionOfIsEmpty {A : Action (Type u) G} (h : IsEmpty (ToType A)) : IsInitial A :=
  IsInitial.ofUniqueHom (fun _ => ⟨↾(fun a => h.elim a), fun _ => by ext a; exact h.elim a⟩)
    fun _ _ => Action.hom_ext _ _ (by ext a; exact h.elim a)

/-- A `G`-set that is an initial object has empty underlying type. -/
theorem isEmpty_of_isInitial_action {A : Action (Type u) G} (h : IsInitial A) :
    IsEmpty (ToType A) :=
  Function.isEmpty (β := PEmpty.{u + 1}) (h.to ⟨PEmpty.{u + 1}, 1⟩).hom

/-- A `G`-set fails to be an initial object exactly when its underlying type is nonempty. -/
theorem nonempty_iff_not_isInitial_action (A : Action (Type u) G) :
    Nonempty (ToType A) ↔ (IsInitial A → False) :=
  ⟨fun h hi => (isEmpty_of_isInitial_action hi).elim h.some,
    fun h => not_isEmpty_iff.mp fun he => h (isInitialActionOfIsEmpty he)⟩

/-- A map of `G`-sets is a monomorphism exactly when the underlying map of types is injective.
Both directions come from the forgetful functor to types, which preserves and reflects finite
limits and hence monomorphisms. -/
theorem mono_action_iff_injective {A B : Action (Type u) G} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f.hom := by
  constructor
  · intro _
    have hf : Mono ((Action.forget (Type u) G).map f) := (Action.forget (Type u) G).map_mono f
    exact (CategoryTheory.mono_iff_injective f.hom).mp hf
  · intro hf
    have hm : Mono ((Action.forget (Type u) G).map f) :=
      (CategoryTheory.mono_iff_injective f.hom).mpr hf
    exact (Action.forget (Type u) G).mono_of_mono_map hm

/-- **A `G`-set is connected exactly when it is transitive**, that is, exactly when its underlying
type is nonempty and `G` acts transitively on it. -/
theorem isConnected_action_iff_isTransitiveAction (A : Action (Type u) G) :
    PreGaloisCategory.IsConnected A ↔ isTransitiveAction G A := by
  constructor
  · intro hA
    refine (isTransitiveAction_iff A).mpr
      ⟨⟨fun x y => ?_⟩, (nonempty_iff_not_isInitial_action A).mpr hA.notInitial⟩
    -- The orbit of `x` is a subobject of `A` with nonempty underlying type, hence all of `A`.
    let T : Action (Type u) G := Action.ofMulAction G (MulAction.orbit G x)
    let i : T ⟶ A := ⟨↾Subtype.val, fun _ => rfl⟩
    have _ : Mono i := (mono_action_iff_injective i).mpr Subtype.val_injective
    have hne : IsInitial T → False := fun h =>
      (isEmpty_of_isInitial_action h).elim ⟨x, MulAction.mem_orbit_self x⟩
    have _ : IsIso i := hA.noTrivialComponent T i hne
    have hiso : IsIso i.hom := inferInstanceAs (IsIso ((Action.forget (Type u) G).map i))
    obtain ⟨⟨y', ⟨g, hg⟩⟩, hy⟩ :=
      ((CategoryTheory.isIso_iff_bijective i.hom).mp hiso).surjective y
    exact ⟨g, hg.trans hy⟩
  · intro hA
    obtain ⟨htrans, hne⟩ := (isTransitiveAction_iff A).mp hA
    refine ⟨fun h => (nonempty_iff_not_isInitial_action A).mp hne h, fun Y i hm hni => ?_⟩
    have _ : Mono i := hm
    obtain ⟨y₀⟩ := (nonempty_iff_not_isInitial_action Y).mpr hni
    have hbij : Function.Bijective i.hom := by
      refine ⟨(mono_action_iff_injective i).mp hm, fun a => ?_⟩
      obtain ⟨g, hg⟩ := htrans.exists_smul_eq (i.hom y₀) a
      refine ⟨g • y₀, ?_⟩
      rw [← hg, smul_eq_ρ_apply, smul_eq_ρ_apply]
      simpa using ConcreteCategory.congr_hom (i.comm g) y₀
    have _ : IsIso i.hom := (CategoryTheory.isIso_iff_bijective i.hom).mpr hbij
    infer_instance

end TauCeti

end
