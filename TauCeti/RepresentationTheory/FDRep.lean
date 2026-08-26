/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RepresentationTheory.Character

/-!
# Finite-dimensional representations

This file records how the forgetful functor `FDRep R G ⥤ Rep R G` preserves module-finiteness,
finrank and characters. These facts let results proved for representation carriers transfer back to
`FDRep`, in particular in `TauCeti.RepresentationTheory.Induction.FiniteDimensional`. In the same
spirit it records that rebundling the representation an object carries returns that object, which
is the identification a construction phrased as `FDRep.of ρ` needs in order to be read as a
statement about the object it started from.

It also records the character of a trivial representation, the constant `finrank`, in both the
`Representation` and the `FDRep.of` spellings in which consumers meet it.

An object of `FDRep k G` carries a module in the universe of `k`, so `FDRep.of` accepts a
representation only when its carrier already lies there. A module-finite carrier is however always
*equivalent* to one that does, because it is spanned by finitely many vectors over `k`;
`FDRep.ofShrink` performs that transport, and the lemmas beside it say that the transport changes
neither the dimension nor the character. Only the character transfer needs `k` to be a field, `k`
being a commutative ring throughout otherwise.

Finally it records the two structural properties of the character that Mathlib's
`RepresentationTheory/Character.lean` leaves out beside `FDRep.char_iso` and `FDRep.char_tensor`:
the character is **additive on biproducts**, and the character of the **tensor unit** is the
constant function `1`. Those are what is still missing before the character can be read as a ring
homomorphism out of the representation ring, `TauCeti.repRingCharacter`.

## Main definitions

* `FDRep.ofShrink`: a module-finite representation on a carrier in an arbitrary universe, as an
  object of `FDRep k G`.

## Main statements

* `Representation.char_trivial`: the character of a trivial representation is the dimension of its
  carrier, whence `FDRep.character_of_trivial` for the trivial representation on `k` itself.
* `FDRep.moduleFinite_forget₂_obj`: the forgotten carrier is module-finite.
* `FDRep.finrank_forget₂_obj`: forgetting does not change finrank.
* `FDRep.character_forget₂_obj`: forgetting does not change the character.
* `FDRep.of_ρ_eq_self`: rebundling the representation carried by an object returns that object.
* `FDRep.ofShrinkEquiv`: `FDRep.ofShrink ρ` carries a representation equivalent to `ρ`, whence
  `FDRep.finrank_ofShrink` and `FDRep.character_ofShrink`.
* `FDRep.char_biprod`: the character is additive on biproducts.
* `FDRep.char_tensorUnit`: the character of the tensor unit is the constant function `1`.
-/

public section

universe u v w

namespace Representation

/-- **The character of a trivial representation is the dimension of its carrier**: every group
element acts as the identity, whose trace is that dimension. -/
@[simp]
theorem char_trivial {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (g : G) :
    (trivial k G V).character g = Module.finrank k V := by
  have hone : trivial k G V g = 1 :=
    LinearMap.ext fun v => by rw [trivial_apply, Module.End.one_apply]
  rw [character, hone, LinearMap.trace_one]

end Representation

namespace FDRep

open CategoryTheory

/-- **The character of the trivial one-dimensional representation is constantly `1`**, that
dimension being `1`. This is the form in which the trivial character enters a pairing or a
Frobenius reciprocity computation, both of which are phrased for objects of `FDRep k G`. -/
@[simp]
theorem character_of_trivial {k : Type u} {G : Type v} [Field k] [Monoid G] (g : G) :
    (FDRep.of (Representation.trivial k G k)).character g = 1 := by
  rw [FDRep.character, FDRep.of_ρ']
  -- the carrier of `FDRep.of ρ` is the module that `ρ` acts on, here `k` itself
  exact (Representation.char_trivial g).trans (by simp)

/-- Forgetting finite-dimensionality keeps the finite-generation instance on the carrier. -/
instance moduleFinite_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A)

/-- Forgetting finite-dimensionality does not change the dimension of the carrier. -/
@[simp]
theorem finrank_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

/-- Forgetting finite-dimensionality does not change the character of the carrier. -/
@[simp]
theorem character_forget₂_obj {k : Type u} {G : Type v} [Field k] [Monoid G] (A : FDRep k G)
    (g : G) : ((forget₂ (FDRep k G) (Rep k G)).obj A).ρ.character g = A.character g := by
  rw [FDRep.character, Representation.character, FDRep.forget₂_ρ]
  -- The remaining `rfl` only identifies the two names of the single underlying module, the same
  -- definitional identification that lets `FDRep.forget₂_ρ` be stated at all.
  rfl

/-- Rebundling the representation carried by an object of `FDRep R G` returns that object. -/
@[simp]
theorem of_ρ_eq_self {R : Type u} {G : Type v} [CommRing R] [Monoid G] (A : FDRep R G) :
    FDRep.of A.ρ = A := (rfl)

section Shrink

variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Monoid G] [AddCommGroup V]
  [Module k V] [Module.Finite k V] (ρ : Representation k G V)

/-- **A module-finite representation as an object of `FDRep k G`**, whatever universe its carrier
lives in. A module-finite `k`-module is `Small.{u}` for `k : Type u`, so the carrier may be
replaced by `Shrink V` and the action conjugated across; `FDRep.ofShrinkEquiv` compares the result
with `ρ`. -/
noncomputable def ofShrink : FDRep k G :=
  have : Small.{u} V := Module.Finite.small k V
  FDRep.of ((Shrink.linearEquiv k V).symm.conjRingEquiv.toMonoidHom.comp ρ)

/-- The representation carried by `FDRep.ofShrink ρ` is equivalent to `ρ`: shrinking the carrier
loses nothing. -/
noncomputable def ofShrinkEquiv : Representation.Equiv (ofShrink ρ).ρ ρ := by
  have : Small.{u} V := Module.Finite.small k V
  apply Representation.Equiv.mk (Shrink.linearEquiv k V)
  intro g
  ext x
  simp [ofShrink]

/-- Shrinking the carrier does not change the dimension. -/
@[simp]
theorem finrank_ofShrink : Module.finrank k (ofShrink ρ) = Module.finrank k V := by
  have : Small.{u} V := Module.Finite.small k V
  exact LinearEquiv.finrank_eq (Shrink.linearEquiv k V)

end Shrink

section ShrinkCharacter

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Monoid G] [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)

/-- Shrinking the carrier does not change the character: the shrunk representation is equivalent
to the original one, by `FDRep.ofShrinkEquiv`. -/
@[simp]
theorem character_ofShrink (g : G) : (ofShrink ρ).character g = ρ.character g :=
  congrFun (Representation.char_iso (ofShrinkEquiv ρ)) g

end ShrinkCharacter

section Biproduct

open CategoryTheory Limits

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The trace of `ρ g` cut down to a retract: if `p ∘ i` is the identity of `X`, then the trace of
`ρ g` composed with the idempotent `i ∘ p` is the character of `X`.

This is the one computation behind `FDRep.char_biprod`: cyclicity of the trace moves `p` past
`ρ g ∘ i`, equivariance of `i` moves `ρ g` past it in the other direction, and what is left is
`p ∘ i = 𝟙` applied to `X.ρ g`. -/
private theorem trace_comp_of_retraction {X B : FDRep k G} (i : X ⟶ B) (p : B ⟶ X)
    (h : i ≫ p = 𝟙 X) (g : G) :
    LinearMap.trace k B ((B.ρ g ∘ₗ i.hom.hom.hom) ∘ₗ p.hom.hom.hom) = X.character g := by
  -- equivariance of `i`, namely `CategoryTheory.Action.Hom.comm`, read through the two layers of
  -- bundling: `simp` strips the morphisms of `FGModuleCat k` and of `ModuleCat k` down to their
  -- underlying linear maps, so no definitional unfolding is involved
  have hcomm : i.hom.hom.hom ∘ₗ X.ρ g = B.ρ g ∘ₗ i.hom.hom.hom := by
    simpa using congrArg (fun t : X.V ⟶ B.V => t.hom.hom) (i.comm g)
  -- the retraction `h`, read the same way; here `simp` also rewrites the underlying map of `𝟙 X`
  have hpi : p.hom.hom.hom ∘ₗ i.hom.hom.hom = LinearMap.id := by
    simpa using congrArg (fun t : X ⟶ X => t.hom.hom.hom) h
  rw [LinearMap.trace_comp_comm', ← hcomm, ← LinearMap.comp_assoc, hpi]
  simp [FDRep.character]

/-- **The character is additive on biproducts.** Together with `FDRep.char_iso` and
`FDRep.char_tensor` this is what makes the character a ring homomorphism out of the representation
ring; see `TauCeti.repRingCharacter`.

The proof splits the identity of `X ⊞ Y` as the sum of the two idempotents
`biprod.inl ∘ biprod.fst` and `biprod.inr ∘ biprod.snd` (`CategoryTheory.Limits.biprod.total`) and
evaluates the trace of `ρ g` against each summand with `FDRep.trace_comp_of_retraction`. -/
@[simp]
theorem char_biprod (X Y : FDRep k G) : (X ⊞ Y).character = X.character + Y.character := by
  ext g
  have htot : (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom ∘ₗ (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom
      + (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom ∘ₗ (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom
      = LinearMap.id := by
    have h := congrArg (fun t : (X ⊞ Y) ⟶ (X ⊞ Y) => t.hom.hom.hom)
      (biprod.total (X := X) (Y := Y))
    simp only [Action.id_hom] at h
    exact h
  have hsplit : (X ⊞ Y).ρ g
      = ((X ⊞ Y).ρ g ∘ₗ (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom)
          ∘ₗ (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom
        + ((X ⊞ Y).ρ g ∘ₗ (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom)
          ∘ₗ (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add, htot,
      LinearMap.comp_id]
  rw [FDRep.character, hsplit, map_add,
    trace_comp_of_retraction biprod.inl biprod.fst biprod.inl_fst,
    trace_comp_of_retraction biprod.inr biprod.snd biprod.inr_snd, Pi.add_apply]

end Biproduct

section TensorUnit

open CategoryTheory MonoidalCategory

/-- **The character of the tensor unit of `FDRep k G` is the constant function `1`**, the unit
being the trivial representation on `k` itself. Beside `FDRep.char_tensor` this is what makes the
character multiplicative out of the representation ring, see `TauCeti.repRingCharacter`. -/
@[simp]
theorem char_tensorUnit (k : Type u) (G : Type v) [Field k] [Monoid G] :
    (𝟙_ (FDRep k G)).character = 1 := by
  ext g
  -- the two sides are the same object, not merely isomorphic ones: `Action.instMonoidalCategory`
  -- takes the unit of `Action V G` to be the unit of `V` with the trivial action, and the unit of
  -- `FGModuleCat k` is `k` itself, which is what `FDRep.of` bundles here
  have hunit : 𝟙_ (FDRep k G) = FDRep.of (Representation.trivial k G k) := rfl
  rw [hunit, Pi.one_apply, character_of_trivial]

end TensorUnit

end FDRep
