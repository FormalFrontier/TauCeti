/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RepresentationTheory.Character

/-!
# Class functions

This file defines functions on a group that are constant on conjugacy classes. It identifies
their module with the module of functions on `ConjClasses G`, computes its dimension for finite
groups, pulls class functions back along a group homomorphism, shows that characters of
representations are class functions, and evaluates a sum over a finite group one conjugacy class
at a time.

The indicator function of a conjugacy class, `TauCeti.ClassFunction.classIndicator`, is the class
function pulled back from the indicator of a single point of `ConjClasses G`; pairing a class
function against it is how a class function is read off an expansion in a basis of class functions.

These are the indexing foundations for character tables.

This implementation follows the
[Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and its
[suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean).
-/

public section

/-
The definitions below are deliberately not `@[expose]`d: the characteristic lemmas in this file
are the intended interface, so nothing downstream needs to unfold them. Those lemmas are proved
by `(rfl)` rather than `rfl`, since the parentheses stop them from being exported as
definitional equalities, which would in turn require exposing the definitions.
-/

namespace TauCeti

universe u v w w'

/-- Conjugacy is inherited by inverses in both directions.

Not `@[simp]`: Mathlib's `isConj_iff` is itself `simp`, so the left-hand side simplifies to
`∃ c, c * x⁻¹ * c⁻¹ = y⁻¹` and the simp normal form linter rejects the pair. -/
theorem isConj_inv_iff {G : Type v} [Group G] {x y : G} :
    IsConj x⁻¹ y⁻¹ ↔ IsConj x y := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have := congrArg Inv.inv hc
    simpa [mul_assoc] using this

/-- The submodule of functions on `G` that are constant under conjugation. -/
def ClassFunction (k : Type u) (G : Type v) [Semiring k] [Group G] : Submodule k (G → k) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' _ _ := rfl
  add_mem' hf₁ hf₂ g h := by rw [Pi.add_apply, Pi.add_apply, hf₁ g h, hf₂ g h]
  smul_mem' c f hf g h := by rw [Pi.smul_apply, Pi.smul_apply, hf g h]

namespace ClassFunction

variable {k : Type u} {G : Type v} [Semiring k] [Group G]

/-- A function is a class function exactly when it is invariant under conjugation. -/
@[simp]
theorem mem_iff {f : G → k} :
    f ∈ ClassFunction k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl

/-- Class functions take the same value on conjugate elements. -/
theorem eq_of_isConj (f : ClassFunction k G) {g h : G} (hgh : IsConj g h) :
    f.1 g = f.1 h := by
  obtain ⟨x, rfl⟩ := isConj_iff.mp hgh
  exact (f.2 g x).symm

/-- Evaluate a class function on a conjugacy class. -/
noncomputable def toConjClasses (f : ClassFunction k G) : ConjClasses G → k :=
  Quotient.lift f.1 fun _ _ h => eq_of_isConj f h

/-- Evaluating the induced function on the class of `g` gives the value at `g`. -/
@[simp]
theorem toConjClasses_mk (f : ClassFunction k G) (g : G) :
    toConjClasses f (ConjClasses.mk g) = f.1 g :=
  (rfl)

/-- Pull a function on conjugacy classes back to a class function on the group. -/
def ofConjClasses (f : ConjClasses G → k) : ClassFunction k G :=
  ⟨fun g => f (ConjClasses.mk g), fun g h => by
    apply congrArg f
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      (IsConj.symm (isConj_iff.mpr ⟨h, rfl⟩))⟩

/-- Pulling back a function on conjugacy classes evaluates it on the class of `g`. -/
@[simp]
theorem ofConjClasses_apply (f : ConjClasses G → k) (g : G) :
    (ofConjClasses f).1 g = f (ConjClasses.mk g) :=
  (rfl)

/-- Pull a class function back along a group homomorphism.  Restriction of a class function to a
subgroup is the case `φ = S.subtype`. -/
def comap {H : Type w} [Group H] (φ : H →* G) :
    ClassFunction k G →ₗ[k] ClassFunction k H where
  toFun f := ⟨fun x => f.1 (φ x), fun g h => by
    simp only [map_mul, map_inv]
    exact f.2 (φ g) (φ h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A pulled-back class function is the composite with the homomorphism. -/
@[simp]
theorem comap_apply {H : Type w} [Group H] (φ : H →* G) (f : ClassFunction k G) (x : H) :
    (comap φ f).1 x = f.1 (φ x) :=
  (rfl)

/-- Pulling back along the identity homomorphism changes nothing. -/
@[simp]
theorem comap_id : comap (MonoidHom.id G) = LinearMap.id (R := k) (M := ClassFunction k G) :=
  (rfl)

/-- Pullback is contravariantly functorial: pulling back along a composite is pulling back along
each factor in turn. -/
@[simp]
theorem comap_comp {H : Type w} {J : Type w'} [Group H] [Group J] (φ : H →* G) (ψ : J →* H) :
    comap (k := k) (φ.comp ψ) = (comap ψ).comp (comap φ) :=
  (rfl)

/-- Class functions on `G` are linearly equivalent to functions on its conjugacy classes. -/
noncomputable def equivConjClasses : ClassFunction k G ≃ₗ[k] (ConjClasses G → k) where
  toFun := toConjClasses
  invFun := ofConjClasses
  map_add' f g := by
    ext C
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
    rfl
  map_smul' c f := by
    ext C
    obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
    rfl
  left_inv f := by
    ext g
    rfl
  right_inv f := by
    ext C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rfl

/-- The linear equivalence is given by `toConjClasses`. -/
@[simp]
theorem equivConjClasses_apply (f : ClassFunction k G) :
    equivConjClasses f = toConjClasses f :=
  (rfl)

/-- The inverse linear equivalence is given by `ofConjClasses`. -/
@[simp]
theorem equivConjClasses_symm_apply (f : ConjClasses G → k) :
    equivConjClasses.symm f = ofConjClasses f :=
  (rfl)

/-- The indicator class function of the conjugacy class of `x`: it takes the value `1` on the
conjugates of `x` and `0` elsewhere.

`Set.indicator` rather than `Pi.single` so that the definition carries no decidability instance of
its own, and `TauCeti.ClassFunction.classIndicator_apply` can be stated with whichever instance is
in scope where it is used. -/
noncomputable def classIndicator (x : G) : ClassFunction k G :=
  ofConjClasses (({ConjClasses.mk x} : Set (ConjClasses G)).indicator fun _ => 1)

/-- The defining values of `TauCeti.ClassFunction.classIndicator`. -/
@[simp]
theorem classIndicator_apply [DecidableEq (ConjClasses G)] (x y : G) :
    (classIndicator (k := k) x).1 y =
      if ConjClasses.mk y = ConjClasses.mk x then 1 else 0 := by
  rw [classIndicator, ofConjClasses_apply]
  by_cases h : ConjClasses.mk y = ConjClasses.mk x
  · rw [if_pos h, Set.indicator_of_mem (Set.mem_singleton_iff.mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun hm => h (Set.mem_singleton_iff.mp hm))]

/-- **Summing a class function one conjugacy class at a time.** The conjugacy classes partition
the group and a class function is constant on each of them, so each class contributes its size
times the single value the class function takes there.

This is the substitution that turns a sum over the group, such as the one pairing two characters,
into a sum over the columns of a character table. -/
theorem sum_eq_sum_conjClasses [Fintype G] [Fintype (ConjClasses G)] (f : ClassFunction k G) :
    ∑ g : G, f.1 g = ∑ C : ConjClasses G, (Nat.card C.carrier : k) * toConjClasses f C := by
  classical
  rw [← Fintype.sum_fiberwise (ConjClasses.mk (α := G)) fun g => f.1 g]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hconst : ∀ x : {g : G // ConjClasses.mk g = C}, f.1 x.1 = toConjClasses f C := by
    rintro ⟨x, rfl⟩
    exact (toConjClasses_mk f x).symm
  have hcard : Nat.card C.carrier = Fintype.card {g : G // ConjClasses.mk g = C} :=
    (Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => ConjClasses.mem_carrier_iff_mk_eq)).trans
      (Nat.card_eq_fintype_card)
  rw [Finset.sum_congr rfl fun x _ => hconst x, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]

end ClassFunction

namespace ClassFunction

variable {k : Type u} {G : Type v} [DivisionRing k] [Group G]

/-- The dimension of the space of class functions is the number of conjugacy classes. -/
theorem finrank_eq_card_conjClasses [Finite (ConjClasses G)] :
    Module.finrank k (ClassFunction k G) = Nat.card (ConjClasses G) := by
  let := Fintype.ofFinite (ConjClasses G)
  rw [LinearEquiv.finrank_eq equivConjClasses, Module.finrank_pi_fintype]
  simp

end ClassFunction

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The character of a representation is a class function. -/
noncomputable def ofCharacter {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ClassFunction k G :=
  ⟨ρ.character, fun g h => ρ.char_conj g h⟩

/-- The class function of a representation evaluates to its character. -/
@[simp]
theorem ofCharacter_apply {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (g : G) : (ofCharacter ρ).1 g = ρ.character g :=
  (rfl)

/-- The character of a finite-dimensional bundled representation is a class function. -/
noncomputable def ofFDRep (V : FDRep k G) : ClassFunction k G :=
  ⟨V.character, fun g h => V.char_conj g h⟩

/-- The class function of a bundled finite-dimensional representation evaluates to its character. -/
@[simp]
theorem ofFDRep_apply (V : FDRep k G) (g : G) : (ofFDRep V).1 g = V.character g :=
  (rfl)

end ClassFunction

end TauCeti
