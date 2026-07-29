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

Three constructions on `Subalgebra.center` that Mathlib states only for `Subring.center`, or only
as an equality of subalgebras, and that are needed whenever a structure theorem presents an algebra
up to an algebra equivalence.

* `TauCeti.centerCongr` transports the center along an algebra equivalence. It is the
  `Subalgebra` counterpart of Mathlib's `Subring.centerCongr`, which sees only the ring
  structure and therefore cannot record `R`-linearity.
* `TauCeti.centerPiAlgEquiv` splits the center of a product of algebras as the product of the
  centers, upgrading Mathlib's `Subalgebra.center_pi` from an equality of subalgebras of
  `Π i, S i` to an algebra equivalence with `Π i, Subalgebra.center R (S i)`.
* `TauCeti.centerAlgEquivOfIsCentral` identifies the center of a central algebra with the base
  field, so that its dimension is one (`TauCeti.finrank_center_of_isCentral`).
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

section Pi

variable {ι : Type*} {S : ι → Type*} [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]

/-- An element of a product of algebras is central exactly when each of its components is. -/
theorem mem_center_pi_iff {x : Π i, S i} :
    x ∈ Subalgebra.center R (Π i, S i) ↔ ∀ i, x i ∈ Subalgebra.center R (S i) := by
  rw [Subalgebra.center_pi]
  simp

/-- The center of a product of algebras is the product of their centers. -/
def centerPiAlgEquiv :
    Subalgebra.center R (Π i, S i) ≃ₐ[R] Π i, Subalgebra.center R (S i) where
  toFun x i := ⟨x.1 i, mem_center_pi_iff.mp x.2 i⟩
  invFun y := ⟨fun i => (y i).1, mem_center_pi_iff.mpr fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem centerPiAlgEquiv_apply_coe (x : Subalgebra.center R (Π i, S i)) (i : ι) :
    (centerPiAlgEquiv x i : S i) = (x : Π i, S i) i := by
  simp [centerPiAlgEquiv]

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

end TauCeti
