import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RepresentationTheory.Character

/-!
# Class functions

This file defines functions on a group that are constant on conjugacy classes. It identifies
their module with the module of functions on `ConjClasses G`, computes its dimension for finite
groups, and shows that characters of representations are class functions.

These are the indexing foundations for character tables.
-/

namespace TauCeti

universe u v w

/-- The submodule of functions on `G` that are constant under conjugation. -/
def ClassFunction (k : Type u) (G : Type v) [CommRing k] [Group G] : Submodule k (G → k) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' _ _ := rfl
  add_mem' hf₁ hf₂ g h := by rw [Pi.add_apply, Pi.add_apply, hf₁ g h, hf₂ g h]
  smul_mem' c f hf g h := by rw [Pi.smul_apply, Pi.smul_apply, hf g h]

namespace ClassFunction

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

/-- A function is a class function exactly when it is invariant under conjugation. -/
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

@[simp]
theorem toConjClasses_mk (f : ClassFunction k G) (g : G) :
    toConjClasses f (ConjClasses.mk g) = f.1 g :=
  rfl

/-- Pull a function on conjugacy classes back to a class function on the group. -/
def ofConjClasses (f : ConjClasses G → k) : ClassFunction k G :=
  ⟨fun g => f (ConjClasses.mk g), fun g h => by
    apply congrArg f
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      (IsConj.symm (isConj_iff.mpr ⟨h, rfl⟩))⟩

@[simp]
theorem ofConjClasses_apply (f : ConjClasses G → k) (g : G) :
    (ofConjClasses f).1 g = f (ConjClasses.mk g) :=
  rfl

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

@[simp]
theorem equivConjClasses_apply_mk (f : ClassFunction k G) (g : G) :
    equivConjClasses f (ConjClasses.mk g) = f.1 g :=
  rfl

@[simp]
theorem equivConjClasses_symm_apply (f : ConjClasses G → k) (g : G) :
    (equivConjClasses.symm f).1 g = f (ConjClasses.mk g) :=
  rfl

end ClassFunction

namespace ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The dimension of the space of class functions is the number of conjugacy classes. -/
theorem finrank_eq_card_conjClasses [Finite G] :
    Module.finrank k (ClassFunction k G) = Nat.card (ConjClasses G) := by
  letI := Fintype.ofFinite G
  letI := Classical.decEq G
  rw [LinearEquiv.finrank_eq equivConjClasses, Module.finrank_pi_fintype]
  simp

/-- The character of a representation is a class function. -/
noncomputable def ofCharacter {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) : ClassFunction k G :=
  ⟨ρ.character, fun g h => ρ.char_conj g h⟩

@[simp]
theorem ofCharacter_apply {V : Type w} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) :
    (ofCharacter ρ).1 g = ρ.character g :=
  rfl

/-- The character of a finite-dimensional bundled representation is a class function. -/
noncomputable def ofFDRep (V : FDRep k G) : ClassFunction k G :=
  ⟨V.character, fun g h => V.char_conj g h⟩

@[simp]
theorem ofFDRep_apply (V : FDRep k G) (g : G) :
    (ofFDRep V).1 g = V.character g :=
  rfl

end ClassFunction

end TauCeti
