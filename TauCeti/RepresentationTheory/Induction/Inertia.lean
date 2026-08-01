/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Induction.Conjugate

/-!
# The inertia group of a representation of a normal subgroup

Let `N` be a normal subgroup of `G`.  Conjugation makes `G` act on `FDRep k N`
(`TauCeti.conjNormalFDRepMulAction`), and the *inertia group* of `A : FDRep k N` is the stabilizer
of the isomorphism class of `A`,

`inertia A = {g : G | {}^g A ≅ A}`.

This is not `MulAction.stabilizer G A`, which asks for `{}^g A = A` on the nose; the two are
compared in `TauCeti.stabilizer_le_inertia`.  That the isomorphism-class stabilizer is a subgroup
at all is the content of the definition: conjugation by `g` is a *functor*
(`TauCeti.conjNormalFDRepFunctor`), so it carries an isomorphism `{}^h A ≅ A` to an isomorphism
`{}^{gh} A ≅ {}^g A`, and the group axioms of the action do the rest.

The inertia group contains `N` (`TauCeti.le_inertia`), because conjugating by an element `n` of `N`
itself is an inner twist: `A.ρ n` intertwines `{}^n A` with `A`
(`TauCeti.conjNormalFDRepSelfIso`).  Together with the normality of `N` inside `inertia A`, which
Mathlib's `Subgroup.normal_subgroupOf` instance supplies for any subgroup of `G`, this is what makes
the quotient `inertia A / N` — where the Clifford-theory obstruction lives — available.

The conjugation file `TauCeti.RepresentationTheory.Induction.Conjugate` deliberately stops at the
action of `G` on `FDRep k N` itself and leaves the induced action on isomorphism classes to a later
file; this is that file, so the two isomorphisms feeding the subgroup axioms are stated here rather
than there.

Nothing here needs `A` to be irreducible: the inertia group is defined for every
finite-dimensional representation of `N`, and irreducibility only enters later, when Clifford's
theorem identifies the constituents of a restriction with a single `G`-orbit.

## Main definitions

* `TauCeti.conjNormalFDRepMapIso`: conjugation carries isomorphisms to isomorphisms.
* `TauCeti.conjNormalFDRepSelfIso`: conjugating by an element of `N` gives an isomorphic
  representation.
* `TauCeti.inertia`: the inertia group of a representation of a normal subgroup.

## Main statements

* `TauCeti.mem_inertia_iff`: membership in the inertia group is the existence of an isomorphism
  `{}^g A ≅ A`.
* `TauCeti.le_inertia`: the inertia group contains `N`.
* `TauCeti.inertia_congr`: isomorphic representations have the same inertia group, so the inertia
  group is an invariant of the isomorphism class.
* `TauCeti.inertia_conjNormalFDRep`: conjugating the representation conjugates its inertia group.
* `TauCeti.character_conj_eq_of_mem_inertia`: the character of `A` is invariant under conjugation
  by an element of the inertia group.

## References

This file builds the inertia group of Layer 5 (Clifford theory over a normal subgroup) of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks for
"the **inertia (stabilizer) group** `inertia V ≤ G` of an irreducible `V : FDRep k N` is
`{g : G | {}^g V ≅ V}`, a subgroup containing `N`", and pins `inertia`, `mem_inertia_iff` and
`le_inertia` in the accompanying `Suggested.lean`.
-/

public section

open CategoryTheory
open scoped Pointwise

universe u v

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G] {N : Subgroup G} [hN : N.Normal]

section Ring

variable [Ring k]

/-- Conjugation carries isomorphic representations to isomorphic representations: this is
`CategoryTheory.Functor.mapIso` for `TauCeti.conjNormalFDRepFunctor`, phrased in terms of
`TauCeti.conjNormalFDRep` so that the coherence equalities `TauCeti.conjNormalFDRep_one` and
`TauCeti.conjNormalFDRep_mul` rewrite in its type.  It is what makes the inertia group a
subgroup. -/
def conjNormalFDRepMapIso (g : G) {A B : FDRep k N} (e : A ≅ B) :
    conjNormalFDRep g A ≅ conjNormalFDRep g B :=
  (conjNormalFDRepFunctor g).mapIso e

/-- Conjugation changes only the action, not the underlying map: the intertwiner underlying
`conjNormalFDRepMapIso g e` is the one underlying `e`. -/
@[simp]
theorem conjNormalFDRepMapIso_hom_hom (g : G) {A B : FDRep k N} (e : A ≅ B) :
    (conjNormalFDRepMapIso g e).hom.hom = e.hom.hom :=
  (rfl)

/-- Conjugating a representation of a normal subgroup `N` by an element `n` **of `N` itself**
does not change its isomorphism class: the action of `n` is an isomorphism `{}^n A ≅ A`.

The intertwining property is the computation `n · (n⁻¹xn) = xn` in `N`. -/
def conjNormalFDRepSelfIso (A : FDRep k N) (n : N) : conjNormalFDRep (n : G) A ≅ A :=
  Action.mkIso (A.ρAut n) fun x => by
    -- `{}^n A` has the same underlying object as `A`, and its action is by definition
    -- `Action.ρ A` at the conjugated element, but there is no restatement of that at the level
    -- of `Action.ρ` to rewrite with, so `change` is what puts the commutation square into
    -- `End A.V`.  There composition is multiplication in the other order, so each side
    -- collapses to a single value of `Action.ρ A`.
    change Action.ρ A _ ≫ Action.ρ A _ = Action.ρ A _ ≫ Action.ρ A _
    rw [← End.mul_def, ← End.mul_def, ← map_mul, ← map_mul]
    exact congrArg (Action.ρ A) (Subtype.ext (by simp [mul_assoc]))

/-- The isomorphism `{}^n A ≅ A` for `n : N` is the action of `n`. -/
@[simp]
theorem conjNormalFDRepSelfIso_hom_hom (A : FDRep k N) (n : N) :
    (conjNormalFDRepSelfIso A n).hom.hom = Action.ρ A n :=
  (rfl)

/-- The **inertia group** of `A : FDRep k N`, for `N` a normal subgroup of `G`: the elements of
`G` whose conjugate representation `{}^g A` is isomorphic to `A`.

This is the stabilizer of the isomorphism class of `A` for the conjugation action of `G` on
`FDRep k N`; see `TauCeti.stabilizer_le_inertia` for the comparison with the stabilizer of `A`
itself. -/
def inertia (A : FDRep k N) : Subgroup G where
  carrier := {g | Nonempty (conjNormalFDRep g A ≅ A)}
  one_mem' := ⟨eqToIso (conjNormalFDRep_one A)⟩
  mul_mem' := fun {a b} ⟨e⟩ ⟨f⟩ =>
    ⟨eqToIso (conjNormalFDRep_mul a b A) ≪≫ conjNormalFDRepMapIso a f ≪≫ e⟩
  inv_mem' := fun {a} ⟨e⟩ =>
    ⟨conjNormalFDRepMapIso a⁻¹ e.symm ≪≫
      eqToIso (by rw [← conjNormalFDRep_mul, inv_mul_cancel, conjNormalFDRep_one])⟩

/-- An element lies in the inertia group exactly when it conjugates the representation to an
isomorphic one. -/
@[simp]
theorem mem_inertia_iff {A : FDRep k N} {g : G} :
    g ∈ inertia A ↔ Nonempty (conjNormalFDRep g A ≅ A) :=
  (Iff.rfl)

/-- The inertia group of `A` contains the elements fixing `A` on the nose. -/
theorem stabilizer_le_inertia (A : FDRep k N) :
    MulAction.stabilizer G A ≤ inertia A :=
  fun _ hg => ⟨eqToIso hg⟩

/-- **The inertia group contains the normal subgroup**: conjugating by an element of `N` is an
inner twist, so it fixes the isomorphism class. -/
theorem le_inertia (A : FDRep k N) : N ≤ inertia A :=
  fun n hn => ⟨conjNormalFDRepSelfIso A ⟨n, hn⟩⟩

/-- Isomorphic representations have the same inertia group: the inertia group depends only on the
isomorphism class, which is what makes it the stabilizer of a point of `Irr(N)`. -/
theorem inertia_congr {A B : FDRep k N} (e : A ≅ B) : inertia A = inertia B := by
  ext g
  simp only [mem_inertia_iff]
  exact ⟨fun ⟨f⟩ => ⟨conjNormalFDRepMapIso g e.symm ≪≫ f ≪≫ e⟩,
    fun ⟨f⟩ => ⟨conjNormalFDRepMapIso g e ≪≫ f ≪≫ e.symm⟩⟩

/-- **Conjugating the representation conjugates the inertia group**: `I({}^g A) = g I(A) g⁻¹`.

Equivalently the inertia groups along a `G`-orbit in `Irr(N)` are all conjugate, so they share an
index; that index is the number of constituents in Clifford's theorem. -/
theorem inertia_conjNormalFDRep (g : G) (A : FDRep k N) :
    inertia (conjNormalFDRep g A) = MulAut.conj g • inertia A := by
  ext h
  rw [mem_conj_smul, mem_inertia_iff, mem_inertia_iff]
  constructor
  · rintro ⟨e⟩
    -- Conjugating the isomorphism `{}^{hg} A ≅ {}^g A` by `g⁻¹` gives `{}^{g⁻¹hg} A ≅ A`.
    have e' := conjNormalFDRepMapIso g⁻¹ e
    rw [← conjNormalFDRep_mul, ← conjNormalFDRep_mul, ← conjNormalFDRep_mul, inv_mul_cancel,
      conjNormalFDRep_one] at e'
    exact ⟨e'⟩
  · rintro ⟨e⟩
    -- Conjugating the isomorphism `{}^{g⁻¹hg} A ≅ A` by `g` gives `{}^{hg} A ≅ {}^g A`.
    have e' := conjNormalFDRepMapIso g e
    rw [← conjNormalFDRep_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      conjNormalFDRep_mul] at e'
    exact ⟨e'⟩

end Ring

section Field

variable [Field k]

/-- The character of `A` is invariant under conjugation by an element of its inertia group:
`χ(g⁻¹xg) = χ(x)` for `g ∈ inertia A` and `x : N`.

This is the character shadow of `mem_inertia_iff`, and the form in which Clifford's theorem uses
the inertia group. -/
theorem character_conj_eq_of_mem_inertia {A : FDRep k N} {g : G} (hg : g ∈ inertia A) (x : N) :
    A.character ⟨g⁻¹ * (x : G) * g, hN.conj_mem' (x : G) x.2 g⟩ = A.character x := by
  obtain ⟨e⟩ := hg
  rw [← char_conjNormalFDRep_mk, FDRep.char_iso e]

end Field

end TauCeti
