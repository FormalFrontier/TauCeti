/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice
public import TauCeti.Algebra.Coalgebra.Subcomodule.Lattice

/-!
# Subcoalgebras as subcomodules of the regular comodule

Every subcoalgebra of a coalgebra is, by the same underlying submodule, a subcomodule of the
regular right comodule. This file records that bridge and its basic order and finiteness API.

This is a Layer 1 prerequisite for the reductive-groups roadmap target on finite-dimensional
subcoalgebras and subcomodules: once an element is placed in a finite-dimensional subcoalgebra,
the same object is available as a finite-dimensional subcomodule of the regular comodule.

## Main declarations

* `TauCeti.Subcoalgebra.toRegularSubcomodule`: a subcoalgebra as a subcomodule of the regular
  comodule.
* `TauCeti.Subcoalgebra.toRegularSubcomoduleOrderEmbedding`: the construction is order
  reflecting.
* Compatibility with `⊥`, `⊤`, binary joins, arbitrary joins, and finite generation.

## References

This follows immediately from the standard definitions: if `Δ(D) ⊆ D ⊗ D`, then certainly
`Δ(D) ⊆ D ⊗ C`, so `D` is a subcomodule of the regular comodule. The definitions of
subcoalgebra and subcomodule follow Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

open Comodule

private theorem tensorSquare_range_le_regular_range (D : Subcoalgebra R C) :
    LinearMap.range (TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype) ≤
      LinearMap.range
        (TensorProduct.map D.toSubmodule.subtype (LinearMap.id : C →ₗ[R] C)) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨TensorProduct.map (LinearMap.id : D.toSubmodule →ₗ[R] D.toSubmodule)
      D.toSubmodule.subtype t, ?_⟩
  induction t with
  | zero => simp only [map_zero]
  | tmul d e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A subcoalgebra as a subcomodule of the regular right comodule.

The underlying submodule is unchanged; the map `D ⊗ D → C ⊗ C` factors through
`D ⊗ C → C ⊗ C` by including the second tensor factor. -/
@[expose] def toRegularSubcomodule (D : Subcoalgebra R C) : Subcomodule R C C where
  carrier := D.toSubmodule
  coact_mem' := by
    intro c hc
    exact tensorSquare_range_le_regular_range D (D.comul_mem hc)

/-- The underlying submodule is unchanged when a subcoalgebra is viewed as a subcomodule of
the regular comodule. -/
@[simp]
theorem toRegularSubcomodule_toSubmodule (D : Subcoalgebra R C) :
    D.toRegularSubcomodule.toSubmodule = D.toSubmodule :=
  rfl

/-- Membership is unchanged when a subcoalgebra is viewed as a subcomodule of the regular
comodule. -/
@[simp]
theorem mem_toRegularSubcomodule {D : Subcoalgebra R C} {c : C} :
    c ∈ D.toRegularSubcomodule ↔ c ∈ D :=
  Iff.rfl

/-- Viewing a subcoalgebra as a regular subcomodule is monotone. -/
theorem toRegularSubcomodule_mono {D E : Subcoalgebra R C} (hDE : D ≤ E) :
    D.toRegularSubcomodule ≤ E.toRegularSubcomodule := by
  intro c hc
  exact mem_toRegularSubcomodule.2 (hDE (mem_toRegularSubcomodule.1 hc))

/-- Viewing subcoalgebras as regular subcomodules is an order embedding. -/
@[expose] def toRegularSubcomoduleOrderEmbedding :
    Subcoalgebra R C ↪o Subcomodule R C C where
  toFun := toRegularSubcomodule
  inj' D E h := by
    ext c
    exact SetLike.ext_iff.1 h c
  map_rel_iff' := by
    intro D E
    constructor
    · intro h c hc
      exact mem_toRegularSubcomodule.1 (h (mem_toRegularSubcomodule.2 hc))
    · intro h c hc
      exact mem_toRegularSubcomodule.2 (h (mem_toRegularSubcomodule.1 hc))

/-- Applying the order embedding from subcoalgebras to regular subcomodules gives
`toRegularSubcomodule`. -/
@[simp]
theorem toRegularSubcomoduleOrderEmbedding_apply (D : Subcoalgebra R C) :
    toRegularSubcomoduleOrderEmbedding (R := R) (C := C) D = D.toRegularSubcomodule :=
  rfl

/-- The bottom subcoalgebra is the bottom regular subcomodule. -/
@[simp]
theorem toRegularSubcomodule_bot :
    (⊥ : Subcoalgebra R C).toRegularSubcomodule = (⊥ : Subcomodule R C C) := by
  ext c
  simp

/-- The top subcoalgebra is the top regular subcomodule. -/
@[simp]
theorem toRegularSubcomodule_top :
    (⊤ : Subcoalgebra R C).toRegularSubcomodule = (⊤ : Subcomodule R C C) := by
  ext c
  simp

/-- Viewing subcoalgebras as regular subcomodules preserves binary joins. -/
@[simp]
theorem toRegularSubcomodule_sup (D E : Subcoalgebra R C) :
    (D ⊔ E).toRegularSubcomodule = D.toRegularSubcomodule ⊔ E.toRegularSubcomodule := by
  ext c
  rw [mem_toRegularSubcomodule, Subcomodule.mem_sup, mem_sup]
  constructor
  · rintro ⟨d, hd, e, he, hde⟩
    exact ⟨d, hd, e, he, hde⟩
  · rintro ⟨d, hd, e, he, hde⟩
    exact ⟨d, hd, e, he, hde⟩

/-- Viewing subcoalgebras as regular subcomodules preserves arbitrary joins. -/
@[simp]
theorem toRegularSubcomodule_iSup {ι : Sort*} (D : ι → Subcoalgebra R C) :
    (⨆ i, D i).toRegularSubcomodule = ⨆ i, (D i).toRegularSubcomodule := by
  ext c
  rw [← Subcomodule.mem_toSubmodule
      (N := (⨆ i, D i).toRegularSubcomodule),
    ← Subcomodule.mem_toSubmodule
      (N := ⨆ i, (D i).toRegularSubcomodule)]
  rw [Subcomodule.iSup_toSubmodule, toRegularSubcomodule_toSubmodule, iSup_toSubmodule]
  simp_rw [toRegularSubcomodule_toSubmodule]

/-- Viewing subcoalgebras as regular subcomodules preserves set-indexed suprema. -/
@[simp]
theorem toRegularSubcomodule_sSup (S : Set (Subcoalgebra R C)) : (sSup S).toRegularSubcomodule =
      ⨆ D : S, (D : Subcoalgebra R C).toRegularSubcomodule := by
  ext c
  rw [← Subcomodule.mem_toSubmodule
      (N := (sSup S).toRegularSubcomodule),
    ← Subcomodule.mem_toSubmodule
      (N := ⨆ D : S, (D : Subcoalgebra R C).toRegularSubcomodule)]
  rw [Subcomodule.iSup_toSubmodule, toRegularSubcomodule_toSubmodule, sSup_toSubmodule]
  simp_rw [toRegularSubcomodule_toSubmodule]

/-- Viewing subcoalgebras as regular subcomodules preserves finite joins. -/
@[simp]
theorem toRegularSubcomodule_finset_sup {ι : Type*} (s : Finset ι) (D : ι → Subcoalgebra R C) :
    (s.sup D).toRegularSubcomodule = s.sup fun i => (D i).toRegularSubcomodule := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [ih]

/-- A finite subcoalgebra is finite as a regular subcomodule. -/
theorem toRegularSubcomodule_finite (D : Subcoalgebra R C) [Module.Finite R D.toSubmodule] :
    Module.Finite R D.toRegularSubcomodule.toSubmodule := by
  rw [toRegularSubcomodule_toSubmodule]
  infer_instance

/-- A finite subcoalgebra is finite as a regular subcomodule. -/
instance instFiniteToRegularSubcomodule (D : Subcoalgebra R C) [Module.Finite R D.toSubmodule] :
    Module.Finite R D.toRegularSubcomodule.toSubmodule :=
  D.toRegularSubcomodule_finite

end Subcoalgebra

end TauCeti
