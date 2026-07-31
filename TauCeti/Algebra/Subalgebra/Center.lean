/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Transporting and decomposing the center of an algebra

Constructions on `Subalgebra.center` that Mathlib states only for `Subring.center`, or only
as an equality of subalgebras, and that are needed whenever a structure theorem presents an algebra
up to an algebra equivalence, together with the criterion for a commutative algebra to be central.

* `TauCeti.centerCongr` transports the center along an algebra equivalence. It is the
  `Subalgebra` counterpart of Mathlib's `Subring.centerCongr`, which sees only the ring
  structure and therefore cannot record `R`-linearity.
* `TauCeti.centerPiAlgEquiv` splits the center of a product of algebras as the product of the
  centers, upgrading Mathlib's `Subalgebra.center_pi` from an equality of subalgebras of
  `Π i, S i` to an algebra equivalence with `Π i, Subalgebra.center R (S i)`.
* `TauCeti.centerAlgEquivOfIsCentral` identifies the center of a central algebra with the base
  field, so that its dimension is one (`TauCeti.finrank_center_of_isCentral`).
* `TauCeti.isCentral_iff_surjective_algebraMap` records that a commutative algebra is central
  exactly when its structure map is surjective, the precise sense in which centrality is a strong
  condition on a field extension.
-/

public section

namespace TauCeti

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- An algebra equivalence carries the center onto the center. -/
theorem map_center_eq_center (e : A ≃ₐ[R] B) :
    (Subalgebra.center R A).map (e : A →ₐ[R] B) = Subalgebra.center R B := by
  refine le_antisymm ?_ ?_
  · rintro _ hx
    obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp hx
    rw [Subalgebra.mem_center_iff] at ha ⊢
    intro b'
    obtain ⟨a', rfl⟩ := e.surjective b'
    simp only [AlgEquiv.coe_toAlgHom]
    rw [← map_mul, ← map_mul, ha a']
  · intro b hb
    rw [Subalgebra.mem_center_iff] at hb
    refine Subalgebra.mem_map.mpr ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    rw [Subalgebra.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hb (e a)

/-- The center of an algebra, transported along an algebra equivalence. -/
def centerCongr (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (map_center_eq_center e))

@[simp]
theorem centerCongr_apply_coe (e : A ≃ₐ[R] B) (x : Subalgebra.center R A) :
    (centerCongr e x : B) = e (x : A) := by
  simp [centerCongr]

/-- The inverse of `centerCongr e` transports the center back along `e.symm`. -/
@[simp]
theorem centerCongr_symm_apply_coe (e : A ≃ₐ[R] B) (y : Subalgebra.center R B) :
    ((centerCongr e).symm y : A) = e.symm (y : B) := by
  apply e.injective
  rw [e.apply_symm_apply, ← centerCongr_apply_coe e, (centerCongr e).apply_symm_apply]

section Pi

variable {ι : Type*} {S : ι → Type*} [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]

/-- The center of a product of algebras is the product of their centers. -/
def centerPiAlgEquiv :
    Subalgebra.center R (Π i, S i) ≃ₐ[R] Π i, Subalgebra.center R (S i) :=
  have mem_iff : ∀ x : Π i, S i,
      x ∈ Subalgebra.center R (Π i, S i) ↔ ∀ i, x i ∈ Subalgebra.center R (S i) := fun _ => by
    rw [Subalgebra.center_pi]; simp
  { toFun := fun x i => ⟨x.1 i, (mem_iff _).mp x.2 i⟩
    invFun := fun y => ⟨fun i => (y i).1, (mem_iff _).mpr fun i => (y i).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

-- This and `centerPiAlgEquiv_symm_apply_coe` are the defining equations of `centerPiAlgEquiv`:
-- its `toFun` is literally `fun x i => ⟨x.1 i, _⟩` and its `invFun` is `fun y => ⟨fun i => (y i).1,
-- _⟩`, so both sides differ only by the subtype coercion and hold by `rfl`.  The definition is
-- deliberately not `@[expose]`d, so the pre-bump `simp [centerPiAlgEquiv]` has nothing to unfold;
-- the parentheses in `(rfl)` keep the definitional step inside this module, leaving these two
-- lemmas as the whole interface for importers.
@[simp]
theorem centerPiAlgEquiv_apply_coe (x : Subalgebra.center R (Π i, S i)) (i : ι) :
    (centerPiAlgEquiv x i : S i) = (x : Π i, S i) i := (rfl)

/-- The inverse of `centerPiAlgEquiv` assembles a tuple of central elements componentwise. -/
@[simp]
theorem centerPiAlgEquiv_symm_apply_coe (y : Π i, Subalgebra.center R (S i)) (i : ι) :
    (centerPiAlgEquiv.symm y : Π i, S i) i = (y i : S i) := (rfl)

end Pi

section IsCentral

variable (K D : Type*) [Field K] [Semiring D] [Nontrivial D] [Algebra K D]
  [Algebra.IsCentral K D]

/-- The center of a central algebra is the base field. -/
noncomputable def centerAlgEquivOfIsCentral : Subalgebra.center K D ≃ₐ[K] K :=
  (Subalgebra.equivOfEq _ _ (Algebra.IsCentral.center_eq_bot K D)).trans (Algebra.botEquiv K D)

/-- The inverse of `centerAlgEquivOfIsCentral` is the structure map of the algebra. -/
@[simp]
theorem coe_centerAlgEquivOfIsCentral_symm (r : K) :
    ((centerAlgEquivOfIsCentral K D).symm r : D) = algebraMap K D r := by
  simp [centerAlgEquivOfIsCentral]

/-- `centerAlgEquivOfIsCentral` sends a central element to the scalar it is the image of. -/
@[simp]
theorem algebraMap_centerAlgEquivOfIsCentral (x : Subalgebra.center K D) :
    algebraMap K D (centerAlgEquivOfIsCentral K D x) = (x : D) := by
  rw [← coe_centerAlgEquivOfIsCentral_symm, AlgEquiv.symm_apply_apply]

/-- A central algebra has a one-dimensional center. -/
@[simp]
theorem finrank_center_of_isCentral : Module.finrank K (Subalgebra.center K D) = 1 :=
  ((centerAlgEquivOfIsCentral K D).toLinearEquiv.finrank_eq).trans (CommSemiring.finrank_self K)

end IsCentral

/-- A commutative `K`-algebra is central over `K` exactly when its structure map is surjective: the
center of a commutative algebra is all of it, so demanding that the center be the image of `K`
demands that everything be in the image of `K`.

This is the precise sense in which centrality is a strong condition on a field extension: `L / K` is
central only when `L = K`. -/
theorem isCentral_iff_surjective_algebraMap (K D : Type*) [CommSemiring K] [CommSemiring D]
    [Algebra K D] : Algebra.IsCentral K D ↔ Function.Surjective (algebraMap K D) := by
  refine ⟨fun _ x ↦ ?_, fun h ↦ ⟨fun x _ ↦ ?_⟩⟩
  · obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff K).mp
      (Subalgebra.mem_center_iff.mpr fun b ↦ mul_comm b x)
    exact ⟨a, ha.symm⟩
  · obtain ⟨a, rfl⟩ := h x
    exact Algebra.mem_bot.mpr ⟨a, rfl⟩

end TauCeti
