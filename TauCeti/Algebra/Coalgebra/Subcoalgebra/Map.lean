/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice

/-!
# Images of subcoalgebras

This file proves that coalgebra morphisms send subcoalgebras to subcoalgebras. The underlying
submodule of the image is the ordinary image of the underlying submodule.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on
finite-dimensional subcoalgebras and the fundamental theorem of comodules: finite
subcoalgebras need to be movable along maps of coordinate coalgebras.

## Main declarations

* `TauCeti.Subcoalgebra.map`: the image of a subcoalgebra under a coalgebra morphism.
* `TauCeti.Subcoalgebra.mem_map`: membership in an image subcoalgebra.
* `TauCeti.Subcoalgebra.map_finite`: finite generation is preserved by image.

## References

This uses the standard fact that a coalgebra morphism preserves comultiplication, so the
image of a subcoalgebra is again a subcoalgebra. See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

variable {R : Type u} {C : Type v} {D : Type w} {E : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]

namespace Subcoalgebra

private def mapSubtype (f : C →ₗc[R] D) (A : Subcoalgebra R C) :
    A.carrier →ₗ[R] A.carrier.map f.toLinearMap where
  toFun a := ⟨f a, Submodule.mem_map_of_mem a.2⟩
  map_add' a b := Subtype.ext (map_add f.toLinearMap (a : C) (b : C))
  map_smul' r a := Subtype.ext (map_smul f.toLinearMap r (a : C))

private theorem image_tensorSquare_apply (f : C →ₗc[R] D) (A : Subcoalgebra R C)
    (t : A.carrier ⊗[R] A.carrier) :
    TensorProduct.map (A.carrier.map f.toLinearMap).subtype
        (A.carrier.map f.toLinearMap).subtype
        (TensorProduct.map (mapSubtype f A) (mapSubtype f A) t) =
      TensorProduct.map f.toLinearMap f.toLinearMap
        (TensorProduct.map A.carrier.subtype A.carrier.subtype t) := by
  induction t with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image of a subcoalgebra under a coalgebra morphism. -/
@[expose] def map (f : C →ₗc[R] D) (A : Subcoalgebra R C) : Subcoalgebra R D where
  carrier := A.carrier.map f.toLinearMap
  comul_mem' := by
    rintro d hd
    rcases Submodule.mem_map.mp hd with ⟨c, hc, rfl⟩
    rcases A.comul_mem hc with ⟨t, ht⟩
    refine ⟨TensorProduct.map (mapSubtype f A) (mapSubtype f A) t, ?_⟩
    rw [image_tensorSquare_apply, ht]
    exact CoalgHomClass.map_comp_comul_apply f c

/-- The underlying submodule of the image subcoalgebra is the image of the underlying
submodule. -/
@[simp]
theorem map_toSubmodule (f : C →ₗc[R] D) (A : Subcoalgebra R C) :
    (A.map f).toSubmodule = A.toSubmodule.map f.toLinearMap :=
  rfl

/-- Membership in the image subcoalgebra. -/
theorem mem_map {f : C →ₗc[R] D} {A : Subcoalgebra R C} {d : D} :
    d ∈ A.map f ↔ ∃ c ∈ A, f c = d := by
  rw [← mem_toSubmodule, map_toSubmodule, Submodule.mem_map]
  rfl

/-- The image of an element of a subcoalgebra belongs to the image subcoalgebra. -/
theorem mem_map_of_mem (f : C →ₗc[R] D) {A : Subcoalgebra R C} {c : C} (hc : c ∈ A) :
    f c ∈ A.map f :=
  (mem_map (f := f) (A := A)).2 ⟨c, hc, rfl⟩

/-- The image subcoalgebra is contained in `B` exactly when each image of an element of the
source subcoalgebra belongs to `B`. -/
theorem map_le_iff {f : C →ₗc[R] D} {A : Subcoalgebra R C} {B : Subcoalgebra R D} :
    A.map f ≤ B ↔ ∀ ⦃c⦄, c ∈ A → f c ∈ B := by
  constructor
  · intro h c hc
    exact h (mem_map_of_mem f hc)
  · intro h d hd
    rcases (mem_map (f := f) (A := A)).1 hd with ⟨c, hc, rfl⟩
    exact h hc

/-- The image construction is monotone in the source subcoalgebra. -/
theorem map_mono (f : C →ₗc[R] D) {A B : Subcoalgebra R C} (hAB : A ≤ B) :
    A.map f ≤ B.map f := by
  intro d hd
  rcases (mem_map (f := f) (A := A)).1 hd with ⟨c, hc, rfl⟩
  exact mem_map_of_mem f (hAB hc)

/-- The image of the bottom subcoalgebra is bottom. -/
@[simp]
theorem map_bot (f : C →ₗc[R] D) : (⊥ : Subcoalgebra R C).map f = ⊥ := by
  ext d
  rw [mem_map, mem_bot]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [mem_bot] at hc
    rw [hc, map_zero]
  · intro hd
    exact ⟨0, by rw [mem_bot], by rw [hd, map_zero]⟩

/-- The image of the top subcoalgebra is the range of the coalgebra morphism as a submodule. -/
@[simp]
theorem map_top_toSubmodule (f : C →ₗc[R] D) :
    ((⊤ : Subcoalgebra R C).map f).toSubmodule = LinearMap.range f.toLinearMap := by
  rw [map_toSubmodule, top_toSubmodule, Submodule.map_top]

/-- The identity coalgebra morphism leaves a subcoalgebra unchanged. -/
@[simp]
theorem map_id (A : Subcoalgebra R C) : A.map (CoalgHom.id R C) = A := by
  ext c
  rw [mem_map]
  constructor
  · rintro ⟨c', hc', h⟩
    exact h ▸ hc'
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- Images of subcoalgebras compose with coalgebra morphisms. -/
@[simp]
theorem map_map (A : Subcoalgebra R C) (f : C →ₗc[R] D) (g : D →ₗc[R] E) :
    (A.map f).map g = A.map (g.comp f) := by
  ext e
  constructor
  · rw [mem_map, mem_map]
    rintro ⟨d, ⟨c, hc, hcd⟩, hde⟩
    refine ⟨c, hc, ?_⟩
    calc
      (g.comp f) c = g (f c) := by simp only [CoalgHom.coe_comp, Function.comp_apply]
      _ = g d := congrArg g hcd
      _ = e := hde
  · rw [mem_map]
    rintro ⟨c, hc, rfl⟩
    exact mem_map_of_mem g (mem_map_of_mem f hc)

/-- The image of a binary join is the binary join of the images. -/
@[simp]
theorem map_sup (f : C →ₗc[R] D) (A B : Subcoalgebra R C) : (A ⊔ B).map f = A.map f ⊔ B.map f := by
  ext d
  rw [← mem_toSubmodule, map_toSubmodule, sup_toSubmodule, Submodule.map_sup,
    ← map_toSubmodule f A, ← map_toSubmodule f B, ← sup_toSubmodule, mem_toSubmodule]

/-- The image of a supremum is the supremum of the images. -/
@[simp]
theorem map_iSup {ι : Sort*} (f : C →ₗc[R] D) (A : ι → Subcoalgebra R C) :
    (⨆ i, A i).map f = ⨆ i, (A i).map f := by
  ext d
  rw [← mem_toSubmodule, map_toSubmodule, iSup_toSubmodule, Submodule.map_iSup]
  simp_rw [← map_toSubmodule f]
  rw [← iSup_toSubmodule, mem_toSubmodule]

/-- The image of a finite join is the finite join of the images. -/
@[simp]
theorem map_finset_sup {ι : Type*} (s : Finset ι) (f : C →ₗc[R] D) (A : ι → Subcoalgebra R C) :
    (s.sup A).map f = s.sup fun i => (A i).map f := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sup_empty, Finset.sup_empty, map_bot]
  | cons i s hi ih => rw [Finset.sup_cons, Finset.sup_cons, map_sup, ih]

/-- The image of a finitely generated subcoalgebra is finitely generated as an `R`-module. -/
theorem map_finite (f : C →ₗc[R] D) (A : Subcoalgebra R C)
    [Module.Finite R A.toSubmodule] : Module.Finite R (A.map f).toSubmodule := by
  rw [map_toSubmodule]
  infer_instance

end Subcoalgebra

end TauCeti
