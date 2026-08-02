/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

/-!
# Subcomodules

This file defines subcomodules of a right comodule as submodules whose elements have
coaction in the tensor product of the submodule with the coalgebra. It is deliberately a
lightweight predicate-style API: over a general commutative semiring, the map
`N ⊗ C → M ⊗ C` need not be known injective, so the induced comodule structure on `N` is
not registered here.

This is a Layer 1 prerequisite for the reductive-groups roadmap target on finite-dimensional
subcomodules and the fundamental theorem of comodules. Later work can use
`Module.Finite R N.toSubmodule` to state finitely generated subcomodules.

## Main definitions

* `TauCeti.Subcomodule`: a submodule stable under the coaction.
* `TauCeti.Subcomodule.toSubmodule`: the underlying submodule.
* `TauCeti.Subcomodule.finite`: subcomodules of noetherian modules are finite.
* `⊤` and `⊥`: the full and zero subcomodules.
* `TauCeti.Subcomodule.map`: the image of a subcomodule under a comodule morphism.
* `TauCeti.Subcomodule.map_finite`: images preserve finite generation of the underlying
  submodule.
* `TauCeti.Comodule.Hom.range`: the image subcomodule of a comodule morphism.
* `TauCeti.Comodule.Hom.range_finite`: ranges of morphisms out of finite modules are finite.

## References

This follows the standard definition of a subcomodule: `N ≤ M` satisfies
`ρ(N) ⊆ N ⊗ C`. See Sweedler, *Hopf Algebras*, Chapter 2.

The lightweight range-based API follows the pattern of `TauCeti.Subcoalgebra`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) (C : Type v) (M : Type w)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A subcomodule of a right `C`-comodule `M`.

It is an `R`-submodule `carrier` such that the coaction of every element of `carrier` lies in
the range of `carrier ⊗ C → M ⊗ C`. -/
structure Subcomodule where
  /-- The underlying submodule of a subcomodule. -/
  carrier : Submodule R M
  /-- The coaction of an element of the submodule lies in its tensor product with `C`. -/
  coact_mem' :
    ∀ ⦃m : M⦄, m ∈ carrier →
      Comodule.coact (R := R) (C := C) (M := M) m ∈
        LinearMap.range (TensorProduct.map carrier.subtype (LinearMap.id : C →ₗ[R] C))

namespace Subcomodule

variable {R C M}

instance : SetLike (Subcomodule R C M) M where
  coe N := N.carrier
  coe_injective N P h := by
    cases N with
    | mk carrier hN =>
    cases P with
    | mk carrier' hP =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (Subcomodule R C M) M where
  add_mem {N} := N.carrier.add_mem
  zero_mem N := N.carrier.zero_mem

instance : SMulMemClass (Subcomodule R C M) R M where
  smul_mem {N} r {_} hm := N.carrier.smul_mem r hm

instance : PartialOrder (Subcomodule R C M) :=
  .ofSetLike (Subcomodule R C M) M

/-- The underlying submodule of a subcomodule. -/
@[expose] def toSubmodule (N : Subcomodule R C M) : Submodule R M :=
  N.carrier

@[simp]
theorem mem_carrier {N : Subcomodule R C M} {m : M} : m ∈ N.carrier ↔ m ∈ N :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {N : Subcomodule R C M} {m : M} : m ∈ N.toSubmodule ↔ m ∈ N :=
  Iff.rfl

theorem toSubmodule_carrier (N : Subcomodule R C M) : N.toSubmodule = N.carrier :=
  rfl

/-- A subcomodule of a noetherian module is finitely generated as an `R`-module. -/
theorem finite (N : Subcomodule R C M) [IsNoetherian R M] :
    Module.Finite R N.toSubmodule := by
  infer_instance

theorem le_def {N P : Subcomodule R C M} : N ≤ P ↔ ∀ ⦃m : M⦄, m ∈ N → m ∈ P :=
  Iff.rfl

theorem toSubmodule_le_toSubmodule {N P : Subcomodule R C M} :
    N.toSubmodule ≤ P.toSubmodule ↔ N ≤ P :=
  Iff.rfl

/-- Two subcomodules are equal when they contain the same elements. -/
@[ext]
theorem ext {N P : Subcomodule R C M} (h : ∀ m : M, m ∈ N ↔ m ∈ P) : N = P :=
  SetLike.ext h

/-- The coaction of an element of a subcomodule belongs to its tensor product with the
coalgebra. -/
theorem coact_mem (N : Subcomodule R C M) {m : M} (hm : m ∈ N) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range (TensorProduct.map N.carrier.subtype (LinearMap.id : C →ₗ[R] C)) :=
  N.coact_mem' hm

/-- Constructor from a submodule and the tensor-product stability condition. -/
@[expose] def ofSubmodule (N : Submodule R M) (hN :
      ∀ ⦃m : M⦄, m ∈ N →
        Comodule.coact (R := R) (C := C) (M := M) m ∈
          LinearMap.range (TensorProduct.map N.subtype (LinearMap.id : C →ₗ[R] C))) :
    Subcomodule R C M where
  carrier := N
  coact_mem' := hN

@[simp]
theorem ofSubmodule_carrier (N : Submodule R M) (hN) :
    (ofSubmodule (R := R) (C := C) (M := M) N hN).carrier = N :=
  rfl

@[simp]
theorem mem_ofSubmodule {N : Submodule R M} {hN} {m : M} :
    m ∈ ofSubmodule (R := R) (C := C) (M := M) N hN ↔ m ∈ N :=
  Iff.rfl

omit [Coalgebra R C] [Comodule R C M] in
private theorem tensor_mem_range_top (t : M ⊗[R] C) :
    t ∈ LinearMap.range
      (TensorProduct.map (⊤ : Submodule R M).subtype (LinearMap.id : C →ₗ[R] C)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m c => exact ⟨⟨m, Submodule.mem_top⟩ ⊗ₜ[R] c, by simp⟩
  | add x y hx hy =>
      rcases hx with ⟨x', rfl⟩
      rcases hy with ⟨y', rfl⟩
      exact ⟨x' + y', by simp⟩

/-- The full module as a subcomodule. -/
instance instTop : Top (Subcomodule R C M) where
  top :=
    { carrier := ⊤
      coact_mem' := by
        intro m hm
        exact tensor_mem_range_top (R := R) (C := C) (M := M)
          (Comodule.coact (R := R) (C := C) (M := M) m) }

@[simp]
theorem top_toSubmodule : (⊤ : Subcomodule R C M).toSubmodule = (⊤ : Submodule R M) :=
  rfl

@[simp]
theorem mem_top (m : M) : m ∈ (⊤ : Subcomodule R C M) :=
  Submodule.mem_top

instance : OrderTop (Subcomodule R C M) where
  top := ⊤
  le_top _ _ _ := Submodule.mem_top

/-- The zero submodule as a subcomodule. -/
instance instBot : Bot (Subcomodule R C M) where
  bot :=
    { carrier := ⊥
      coact_mem' := by
        intro m hm
        rw [Submodule.mem_bot] at hm
        subst m
        exact ⟨0, by simp⟩ }

@[simp]
theorem bot_toSubmodule : (⊥ : Subcomodule R C M).toSubmodule = (⊥ : Submodule R M) :=
  rfl

@[simp]
theorem mem_bot {m : M} : m ∈ (⊥ : Subcomodule R C M) ↔ m = 0 :=
  Submodule.mem_bot (R := R) (M := M)

/-- The zero subcomodule is contained in every subcomodule. -/
instance : OrderBot (Subcomodule R C M) where
  bot := ⊥
  bot_le N m hm := by
    rw [mem_bot] at hm
    rw [hm]
    exact zero_mem N

variable {N : Type x} [AddCommMonoid N] [Module R N] [Comodule R C N]

private def mapSubtype (f : Comodule.Hom R C M N) (A : Subcomodule R C M) :
    A.carrier →ₗ[R] A.carrier.map f.toLinearMap where
  toFun a := ⟨f a, Submodule.mem_map_of_mem a.2⟩
  map_add' a b := Subtype.ext (map_add f.toLinearMap (a : M) (b : M))
  map_smul' r a := Subtype.ext (map_smul f.toLinearMap r (a : M))

private theorem image_tensor_apply (f : Comodule.Hom R C M N) (A : Subcomodule R C M)
    (t : A.carrier ⊗[R] C) :
    TensorProduct.map (A.carrier.map f.toLinearMap).subtype (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map (mapSubtype f A) (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map f.toLinearMap (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map A.carrier.subtype (LinearMap.id : C →ₗ[R] C) t) := by
  induction t with
  | zero => simp only [map_zero]
  | tmul a c => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image of a subcomodule under a comodule morphism. -/
@[expose] def map (A : Subcomodule R C M) (f : Comodule.Hom R C M N) : Subcomodule R C N where
  carrier := A.carrier.map f.toLinearMap
  coact_mem' := by
    intro n hn
    rcases Submodule.mem_map.mp hn with ⟨m, hm, rfl⟩
    rcases A.coact_mem hm with ⟨t, ht⟩
    refine ⟨TensorProduct.map (mapSubtype f A) (LinearMap.id : C →ₗ[R] C) t, ?_⟩
    rw [image_tensor_apply, ht]
    exact Comodule.Hom.map_coact_apply f m

/-- The underlying submodule of the image subcomodule is the image of the underlying
submodule. -/
@[simp]
theorem map_toSubmodule (A : Subcomodule R C M) (f : Comodule.Hom R C M N) :
    (A.map f).toSubmodule = A.toSubmodule.map f.toLinearMap :=
  rfl

/-- The image of a finitely generated subcomodule is finitely generated as an `R`-module. -/
theorem map_finite (f : Comodule.Hom R C M N) (A : Subcomodule R C M)
    [Module.Finite R A.toSubmodule] : Module.Finite R (A.map f).toSubmodule := by
  rw [map_toSubmodule]
  infer_instance

/-- Membership in the image subcomodule. -/
theorem mem_map {A : Subcomodule R C M} {f : Comodule.Hom R C M N} {n : N} :
    n ∈ A.map f ↔ ∃ m ∈ A, f m = n := by
  rw [← mem_toSubmodule, map_toSubmodule, Submodule.mem_map]
  rfl

/-- The image of an element of a subcomodule belongs to the image subcomodule. -/
theorem mem_map_of_mem (f : Comodule.Hom R C M N) {A : Subcomodule R C M} {m : M}
    (hm : m ∈ A) : f m ∈ A.map f :=
  (mem_map (A := A) (f := f)).2 ⟨m, hm, rfl⟩

/-- The image subcomodule is contained in `B` exactly when each image of an element of the
source subcomodule belongs to `B`. -/
theorem map_le_iff {A : Subcomodule R C M} {f : Comodule.Hom R C M N} {B : Subcomodule R C N} :
    A.map f ≤ B ↔ ∀ ⦃m⦄, m ∈ A → f m ∈ B := by
  constructor
  · intro h m hm
    exact h (mem_map_of_mem f hm)
  · intro h n hn
    rcases (mem_map (A := A) (f := f)).1 hn with ⟨m, hm, rfl⟩
    exact h hm

/-- The image construction is monotone in the source subcomodule. -/
theorem map_mono (f : Comodule.Hom R C M N) {A B : Subcomodule R C M} (hAB : A ≤ B) :
    A.map f ≤ B.map f := by
  intro n hn
  rcases (mem_map (A := A) (f := f)).1 hn with ⟨m, hm, rfl⟩
  exact mem_map_of_mem f (hAB hm)

/-- The image of the bottom subcomodule is bottom. -/
@[simp]
theorem map_bot (f : Comodule.Hom R C M N) : (⊥ : Subcomodule R C M).map f = ⊥ := by
  ext n
  rw [mem_map, mem_bot]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [mem_bot] at hm
    rw [hm]
    exact f.toLinearMap.map_zero
  · intro hn
    refine ⟨0, by rw [mem_bot], ?_⟩
    rw [hn]
    exact f.toLinearMap.map_zero

/-- The image of the top subcomodule is the range of the comodule morphism as a submodule. -/
@[simp]
theorem map_top_toSubmodule (f : Comodule.Hom R C M N) :
    ((⊤ : Subcomodule R C M).map f).toSubmodule = LinearMap.range f.toLinearMap := by
  rw [map_toSubmodule, top_toSubmodule, Submodule.map_top]

/-- The identity comodule morphism leaves a subcomodule unchanged. -/
@[simp]
theorem map_id (A : Subcomodule R C M) : A.map (Comodule.Hom.id R C M) = A := by
  ext m
  rw [mem_map]
  constructor
  · rintro ⟨m', hm', h⟩
    exact h ▸ hm'
  · intro hm
    exact ⟨m, hm, rfl⟩

variable {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- Images of subcomodules compose with comodule morphisms. -/
@[simp]
theorem map_map (A : Subcomodule R C M) (f : Comodule.Hom R C M N)
    (g : Comodule.Hom R C N P) : (A.map f).map g = A.map (g.comp f) := by
  ext p
  constructor
  · rw [mem_map, mem_map]
    rintro ⟨n, ⟨m, hm, hmn⟩, hnp⟩
    refine ⟨m, hm, ?_⟩
    calc
      (g.comp f) m = g (f m) := by simp only [Comodule.Hom.comp_apply]
      _ = g n := congrArg g hmn
      _ = p := hnp
  · rw [mem_map]
    rintro ⟨m, hm, rfl⟩
    exact mem_map_of_mem g (mem_map_of_mem f hm)

end Subcomodule

namespace Comodule

namespace Hom

variable {R C M}
variable {N : Type x} [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- The image of a comodule morphism as a subcomodule of the codomain. -/
def range (f : Hom R C M N) : Subcomodule R C N :=
  (⊤ : Subcomodule R C M).map f

@[simp]
theorem range_toSubmodule (f : Hom R C M N) :
    (range (R := R) (C := C) f).toSubmodule = LinearMap.range f.toLinearMap := by
  rw [range, Subcomodule.map_top_toSubmodule]

/-- The range of a comodule morphism out of a finitely generated module is finitely generated
as an `R`-module. -/
theorem range_finite (f : Hom R C M N) [Module.Finite R M] :
    Module.Finite R (range (R := R) (C := C) f).toSubmodule := by
  rw [range_toSubmodule]
  infer_instance

@[simp]
theorem mem_range {f : Hom R C M N} {n : N} :
    n ∈ range (R := R) (C := C) f ↔ ∃ m, f m = n := by
  rw [← Subcomodule.mem_toSubmodule, range_toSubmodule]
  rfl

/-- A comodule morphism lands in its image subcomodule. -/
theorem mem_range_self (f : Hom R C M N) (m : M) :
    f m ∈ range (R := R) (C := C) f :=
  (Subcomodule.mem_map (A := (⊤ : Subcomodule R C M)) (f := f)).2
    ⟨m, Subcomodule.mem_top m, rfl⟩

/-- The range of a comodule morphism is contained in `P` exactly when each value of the
morphism belongs to `P`. -/
theorem range_le_iff {f : Hom R C M N} {P : Subcomodule R C N} :
    range (R := R) (C := C) f ≤ P ↔ ∀ m, f m ∈ P := by
  rw [range]
  simpa using
    (Subcomodule.map_le_iff (A := (⊤ : Subcomodule R C M)) (f := f) (B := P))

end Hom

end Comodule

end TauCeti
