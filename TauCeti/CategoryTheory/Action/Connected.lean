/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
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
it: it preserves and reflects monomorphisms, and a `G`-set is initial exactly when its underlying
type is empty.

Both facts are Mathlib's, once the concrete-category forgetful functor of `Action (Type u) G` is
known to preserve and reflect the empty colimit; that is what the two instances below record, and
with them `CategoryTheory.Concrete.initial_iff_empty_of_preserves_of_reflects` applies verbatim to
`G`-sets.

## Main declarations

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

/-- The concrete-category forgetful functor of `Action (Type u) G` preserves initial objects: it
is the composite of `Action.forget`, which preserves all colimits of shape `Discrete PEmpty`, with
the forgetful functor of `Type u`. -/
instance preservesColimit_empty_forget_action :
    PreservesColimit (Functor.empty.{0} (Action (Type u) G)) (forget (Action (Type u) G)) := by
  change PreservesColimit _ (Action.forget (Type u) G ⋙ forget (Type u))
  infer_instance

/-- The concrete-category forgetful functor of `Action (Type u) G` reflects initial objects. -/
instance reflectsColimit_empty_forget_action :
    ReflectsColimit (Functor.empty.{0} (Action (Type u) G)) (forget (Action (Type u) G)) := by
  change ReflectsColimit _ (Action.forget (Type u) G ⋙ forget (Type u))
  infer_instance

/-- A map of `G`-sets is a monomorphism exactly when the underlying map of types is injective.
Both directions come from the forgetful functor to types, which preserves and reflects finite
limits and hence monomorphisms. -/
@[simp]
theorem mono_action_iff_injective {A B : Action (Type u) G} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f.hom :=
  ((Action.forget (Type u) G).mono_map_iff_mono f).symm.trans (mono_iff_injective _)

/-- **A `G`-set is connected exactly when it is transitive**, that is, exactly when its underlying
type is nonempty and `G` acts transitively on it. -/
@[simp]
theorem isConnected_action_iff_isTransitiveAction (A : Action (Type u) G) :
    PreGaloisCategory.IsConnected A ↔ isTransitiveAction G A := by
  have hinit (B : Action (Type u) G) : Nonempty (ToType B) ↔ (IsInitial B → False) := by
    constructor
    · exact fun h hi =>
        ((Concrete.initial_iff_empty_of_preserves_of_reflects B).mp ⟨hi⟩).elim h.some
    · exact fun h => not_isEmpty_iff.mp fun he =>
        h ((Concrete.initial_iff_empty_of_preserves_of_reflects B).mpr he).some
  constructor
  · intro hA
    refine (isTransitiveAction_iff A).mpr ⟨⟨fun x y => ?_⟩, (hinit A).mpr hA.notInitial⟩
    -- The orbit of `x` is a subobject of `A` with nonempty underlying type, hence all of `A`.
    let T : Action (Type u) G := Action.ofMulAction G (MulAction.orbit G x)
    let i : T ⟶ A := ⟨↾Subtype.val, fun _ => rfl⟩
    have _ : Mono i := (mono_action_iff_injective i).mpr Subtype.val_injective
    have hne : IsInitial T → False :=
      (hinit T).mp ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
    have _ : IsIso i := hA.noTrivialComponent T i hne
    have hiso : IsIso i.hom := inferInstanceAs (IsIso ((Action.forget (Type u) G).map i))
    obtain ⟨⟨y', ⟨g, hg⟩⟩, hy⟩ :=
      ((CategoryTheory.isIso_iff_bijective i.hom).mp hiso).surjective y
    exact ⟨g, hg.trans hy⟩
  · intro hA
    obtain ⟨htrans, hne⟩ := (isTransitiveAction_iff A).mp hA
    refine ⟨fun h => (hinit A).mp hne h, fun Y i hm hni => ?_⟩
    have _ : Mono i := hm
    obtain ⟨y₀⟩ := (hinit Y).mpr hni
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
