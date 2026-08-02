/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Subcoalgebras

This file defines subcoalgebras of a coalgebra as submodules whose elements have
comultiplication in the tensor square of the submodule. It is deliberately a lightweight
predicate-style API: over a general commutative semiring, the map `D ⊗ D → C ⊗ C` need not be
known injective, so the induced coalgebra structure on `D` is not registered here.

This is a Layer 1 prerequisite for the reductive-groups roadmap target on
finite-dimensional subcoalgebras and the fundamental theorem of comodules. Later work can use
`Module.Finite R D.toSubmodule` to state finitely generated subcoalgebras.

## Main definitions

* `TauCeti.Subcoalgebra`: a submodule stable under comultiplication.
* `TauCeti.Subcoalgebra.toSubmodule`: the underlying submodule.
* `⊤` and `⊥`: the full and zero subcoalgebras.

## References

This follows the standard coalgebra definition: a subcoalgebra `D ≤ C` satisfies
`Δ(D) ⊆ D ⊗ D`. See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A subcoalgebra of an `R`-coalgebra `C`.

It is an `R`-submodule `carrier` such that the comultiplication of every element of
`carrier` lies in the range of `carrier ⊗ carrier → C ⊗ C`. -/
structure Subcoalgebra where
  /-- The underlying submodule of a subcoalgebra. -/
  carrier : Submodule R C
  /-- The comultiplication of an element of the submodule lies in its tensor square. -/
  comul_mem' :
    ∀ ⦃c : C⦄, c ∈ carrier →
      Coalgebra.comul (R := R) c ∈
        LinearMap.range (TensorProduct.map carrier.subtype carrier.subtype)

namespace Subcoalgebra

variable {R C}

instance : SetLike (Subcoalgebra R C) C where
  coe D := D.carrier
  coe_injective D E h := by
    cases D with
    | mk carrier hD =>
    cases E with
    | mk carrier' hE =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (Subcoalgebra R C) C where
  add_mem {D} := D.carrier.add_mem
  zero_mem D := D.carrier.zero_mem

instance : SMulMemClass (Subcoalgebra R C) R C where
  smul_mem {D} r {_} hc := D.carrier.smul_mem r hc

instance : PartialOrder (Subcoalgebra R C) :=
  .ofSetLike (Subcoalgebra R C) C

/-- The underlying submodule of a subcoalgebra. -/
@[expose] def toSubmodule (D : Subcoalgebra R C) : Submodule R C :=
  D.carrier

@[simp]
theorem mem_carrier {D : Subcoalgebra R C} {c : C} : c ∈ D.carrier ↔ c ∈ D :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {D : Subcoalgebra R C} {c : C} : c ∈ D.toSubmodule ↔ c ∈ D :=
  Iff.rfl

theorem toSubmodule_carrier (D : Subcoalgebra R C) : D.toSubmodule = D.carrier :=
  rfl

theorem le_def {D E : Subcoalgebra R C} : D ≤ E ↔ ∀ ⦃c : C⦄, c ∈ D → c ∈ E :=
  Iff.rfl

theorem toSubmodule_le_toSubmodule {D E : Subcoalgebra R C} :
    D.toSubmodule ≤ E.toSubmodule ↔ D ≤ E :=
  Iff.rfl

/-- Two subcoalgebras are equal when they contain the same elements. -/
@[ext]
theorem ext {D E : Subcoalgebra R C} (h : ∀ c : C, c ∈ D ↔ c ∈ E) : D = E :=
  SetLike.ext h

/-- The comultiplication of an element of a subcoalgebra belongs to its tensor square. -/
theorem comul_mem (D : Subcoalgebra R C) {c : C} (hc : c ∈ D) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range (TensorProduct.map D.carrier.subtype D.carrier.subtype) :=
  D.comul_mem' hc

/-- Constructor from a submodule and the tensor-square stability condition. -/
@[expose] def ofSubmodule (D : Submodule R C) (hD :
      ∀ ⦃c : C⦄, c ∈ D →
        Coalgebra.comul (R := R) (A := C) c ∈
          LinearMap.range (TensorProduct.map D.subtype D.subtype)) :
    Subcoalgebra R C where
  carrier := D
  comul_mem' := hD

@[simp]
theorem ofSubmodule_carrier (D : Submodule R C) (hD) :
    (ofSubmodule (R := R) (C := C) D hD).carrier = D :=
  rfl

@[simp]
theorem mem_ofSubmodule {D : Submodule R C} {hD} {c : C} :
    c ∈ ofSubmodule (R := R) (C := C) D hD ↔ c ∈ D :=
  Iff.rfl

/-- The full coalgebra as a subcoalgebra. -/
instance instTop : Top (Subcoalgebra R C) where
  top :=
    { carrier := ⊤
      comul_mem' := by
        intro c hc
        refine TensorProduct.induction_on (Coalgebra.comul (R := R) (A := C) c) ?_ ?_ ?_
        · exact ⟨0, by simp⟩
        · intro x y
          exact ⟨⟨x, Submodule.mem_top⟩ ⊗ₜ[R] ⟨y, Submodule.mem_top⟩, by simp⟩
        · intro x y hx hy
          rcases hx with ⟨x', rfl⟩
          rcases hy with ⟨y', rfl⟩
          exact ⟨x' + y', by simp⟩ }

@[simp]
theorem top_toSubmodule : (⊤ : Subcoalgebra R C).toSubmodule = (⊤ : Submodule R C) :=
  rfl

@[simp]
theorem mem_top (c : C) : c ∈ (⊤ : Subcoalgebra R C) :=
  Submodule.mem_top

instance : OrderTop (Subcoalgebra R C) where
  top := ⊤
  le_top _ _ _ := Submodule.mem_top

/-- The zero submodule as a subcoalgebra. -/
instance instBot : Bot (Subcoalgebra R C) where
  bot :=
    { carrier := ⊥
      comul_mem' := by
        intro c hc
        rw [Submodule.mem_bot] at hc
        subst c
        exact ⟨0, by simp⟩ }

@[simp]
theorem bot_toSubmodule : (⊥ : Subcoalgebra R C).toSubmodule = (⊥ : Submodule R C) :=
  rfl

@[simp]
theorem mem_bot {c : C} : c ∈ (⊥ : Subcoalgebra R C) ↔ c = 0 :=
  Submodule.mem_bot (R := R) (M := C)

/-- The zero subcoalgebra is contained in every subcoalgebra. -/
instance : OrderBot (Subcoalgebra R C) where
  bot := ⊥
  bot_le D c hc := by
    rw [mem_bot] at hc
    rw [hc]
    exact zero_mem D

end Subcoalgebra

end TauCeti
