/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.Multilinear

/-!
# Shifted gradings and the suspension of graded operations

This file shifts a family of graded pieces and records what the shift does to the degree of a
homogeneous linear or multilinear map.

The shift of a family `𝒜` by `c` is the regrading `Graded.shift 𝒜 c` whose degree-`p` piece is
`𝒜 (p + c)`; this is the cochain shift `X[c]ᵖ = X^{p + c}`, and at `c = 1` it is the suspension
`sA` of the `A∞` conventions. Suspension does not move any element: the canonical map
`s : A ⟶ sA` is the identity of the underlying module, and all of its content is the degree `-1`
recorded by `LinearMap.isHomogeneous_id_shift`.

The main result is the degree translation for multilinear maps. A map of degree `q` after shifting
the `i`-th input grading by `c i` and the target grading by `r` has degree
`q + r - ∑ i, c i` in the original gradings. Its specialisation
`MultilinearMap.isHomogeneous_suspension_iff` is the degree half of the commuting square

```text
(sA)^⊗n  --bₙ--> sA
    ↑s^⊗n           ↑s
 A^⊗n     --mₙ-->  A
```

that defines the suspended operations of an `A∞` algebra: an arity-`n` operation is homogeneous of
degree one for the suspended grading exactly when it is homogeneous of degree `2 - n` for the
original one.

## Main definitions

* `TauCeti.Graded.shift`: the shift of a family of graded pieces.

## Main results

* `TauCeti.LinearMap.isHomogeneous_shift_source_iff`, `TauCeti.LinearMap.isHomogeneous_shift_iff`,
  and `TauCeti.LinearMap.isHomogeneous_shift_target_iff`: shifting the source raises the degree of
  a linear map, shifting the target lowers it, and shifting both leaves it unchanged.
* `TauCeti.LinearMap.isHomogeneous_id_shift`: the suspension map has degree `-c`.
* `TauCeti.MultilinearMap.isHomogeneous_shift_iff`: shifting the inputs by `c` and the target by
  `r` translates degree `q` in the shifted gradings to degree `q + r - ∑ i, c i` in the original
  gradings.
* `TauCeti.MultilinearMap.isHomogeneous_suspension_iff` and
  `TauCeti.MultilinearMap.isHomogeneous_suspension_fin_iff`: an arity-`n` operation has degree one
  after suspension exactly when it has degree `2 - n` before.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

namespace TauCeti

universe uR uι uκ uM uN

namespace Graded

variable {ι : Type uι} {σM : Type*}

/-- The shift of a family of graded pieces by `c`: the degree-`p` piece of `Graded.shift 𝒜 c` is
the degree-`(p + c)` piece of `𝒜`. This is the cochain regrading `X[c]ᵖ = X^{p + c}`; the case
`c = 1` is the suspension `sA` of the `A∞` conventions. -/
def shift [Add ι] (𝒜 : ι → σM) (c : ι) : ι → σM := fun p ↦ 𝒜 (p + c)

@[simp]
theorem shift_apply [Add ι] (𝒜 : ι → σM) (c p : ι) : shift 𝒜 c p = 𝒜 (p + c) := (rfl)

@[simp]
theorem shift_zero [AddZeroClass ι] (𝒜 : ι → σM) : shift 𝒜 0 = 𝒜 := by
  funext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
@[simp]
theorem shift_shift [AddSemigroup ι] (𝒜 : ι → σM) (c d : ι) :
    shift (shift 𝒜 c) d = shift 𝒜 (d + c) := by
  funext p
  simp [add_assoc]

end Graded

namespace LinearMap

section AddMonoid

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Shifting the target grading by `c` lowers the degree of a homogeneous linear map by `c`. -/
theorem isHomogeneous_shift_target_iff {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q c : ι} :
    IsHomogeneous f 𝒜 (Graded.shift ℬ c) q ↔ IsHomogeneous f 𝒜 ℬ (q + c) := by
  simp only [isHomogeneous_def, Graded.shift_apply, add_assoc]

/-- The unsuspension map `s⁻¹ : sA ⟶ A` is the identity of the underlying module and has
degree `c` for the shift by `c`. -/
theorem isHomogeneous_id_unshift (𝒜 : ι → σM) (c : ι) :
    IsHomogeneous (LinearMap.id : M →ₗ[R] M) (Graded.shift 𝒜 c) 𝒜 c := by
  rw [isHomogeneous_def]
  intro p x hx
  simpa only [_root_.LinearMap.id_coe, id_eq, Graded.shift_apply] using hx

end AddMonoid

section AddCommGroup

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddCommGroup ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Shifting the source grading by `c` raises the degree of a homogeneous linear map by `c`. -/
theorem isHomogeneous_shift_source_iff {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q c : ι} :
    IsHomogeneous f (Graded.shift 𝒜 c) ℬ q ↔ IsHomogeneous f 𝒜 ℬ (q - c) := by
  rw [isHomogeneous_def, isHomogeneous_def]
  constructor
  · intro hf p x hx
    have h := hf (p - c) x (by simpa using hx)
    have heq : p - c + q = p + (q - c) := by abel
    rwa [heq] at h
  · intro hf p x hx
    have h := hf (p + c) x (by simpa using hx)
    have heq : p + c + (q - c) = p + q := by abel
    rwa [heq] at h

/-- Shifting the source and the target grading by the same amount leaves the degree of a
homogeneous linear map unchanged. -/
theorem isHomogeneous_shift_iff {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q c : ι} :
    IsHomogeneous f (Graded.shift 𝒜 c) (Graded.shift ℬ c) q ↔ IsHomogeneous f 𝒜 ℬ q := by
  rw [isHomogeneous_shift_target_iff, isHomogeneous_shift_source_iff, add_sub_cancel_right]

end AddCommGroup

section AddGroup

variable {R : Type uR} {ι : Type uι} {M : Type uM} {σM : Type*}
  [Semiring R] [AddGroup ι] [AddCommMonoid M] [Module R M] [SetLike σM M]

/-- The suspension map `s : A ⟶ sA` is the identity of the underlying module and has degree `-c`
for the shift by `c`. At `c = 1` this is the degree `-1` map of the `A∞` conventions. -/
theorem isHomogeneous_id_shift (𝒜 : ι → σM) (c : ι) :
    IsHomogeneous (LinearMap.id : M →ₗ[R] M) 𝒜 (Graded.shift 𝒜 c) (-c) := by
  rw [isHomogeneous_def]
  intro p x hx
  have hpc : p + -c + c = p := by simp [add_assoc]
  simpa only [_root_.LinearMap.id_coe, id_eq, Graded.shift_apply, hpc] using hx

end AddGroup

section Submodule

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]
  [Semiring S] [Module S N] [SMulCommClass R S N] [AddSubmonoidClass σN N] [SMulMemClass σN S N]

/-- Shifting the target grading by `c` shifts the submodule of homogeneous linear maps of
degree `q` to the one of degree `q + c`. -/
theorem homogeneousSubmodule_shift_target (𝒜 : ι → σM) (ℬ : ι → σN) (q c : ι) :
    homogeneousSubmodule (R := R) (S := S) 𝒜 (Graded.shift ℬ c) q =
      homogeneousSubmodule 𝒜 ℬ (q + c) := by
  ext f
  simp only [mem_homogeneousSubmodule, isHomogeneous_shift_target_iff]

end Submodule

end LinearMap

namespace MultilinearMap

section Shift

variable {R : Type uR} {ι : Type uι} {κ : Type uκ}
  {M : κ → Type uM} {N : Type uN} {σM : κ → Type*} {σN : Type*}
  [Semiring R] [AddCommGroup ι] [Fintype κ]
  [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
  [∀ i, Module R (M i)] [Module R N]
  [∀ i, SetLike (σM i) (M i)] [SetLike σN N]

/-- A multilinear map of degree `q` after shifting the `i`-th input grading by `c i` and the target
grading by `r` has degree `q + r - ∑ i, c i` in the original gradings. -/
theorem isHomogeneous_shift_iff {f : MultilinearMap R M N} {𝒜 : (i : κ) → ι → σM i}
    {ℬ : ι → σN} {q r : ι} {c : κ → ι} :
    IsHomogeneous f (fun i ↦ Graded.shift (𝒜 i) (c i)) (Graded.shift ℬ r) q ↔
      IsHomogeneous f 𝒜 ℬ (q + r - ∑ i, c i) := by
  simp only [isHomogeneous_def, Graded.shift_apply]
  constructor
  · intro hf e x hx
    -- feed the shifted statement the degrees `e i - c i`
    have h := hf (fun i ↦ e i - c i) x fun i ↦ by simpa using hx i
    rw [Finset.sum_sub_distrib] at h
    have heq : (∑ i, e i) - (∑ i, c i) + q + r = (∑ i, e i) + (q + r - ∑ i, c i) := by abel
    rwa [heq] at h
  · intro hf e x hx
    -- feed the unshifted statement the degrees `e i + c i`
    have h := hf (fun i ↦ e i + c i) x fun i ↦ by simpa using hx i
    rw [Finset.sum_add_distrib] at h
    have heq : (∑ i, e i) + (∑ i, c i) + (q + r - ∑ i, c i) = (∑ i, e i) + q + r := by abel
    rwa [heq] at h

/-- Shifting every input grading and the target grading by the same amount `c` changes the degree
of an arity-`Fintype.card κ` operation by `c - Fintype.card κ • c`. -/
theorem isHomogeneous_shift_const_iff {f : MultilinearMap R M N} {𝒜 : (i : κ) → ι → σM i}
    {ℬ : ι → σN} {q c : ι} :
    IsHomogeneous f (fun i ↦ Graded.shift (𝒜 i) c) (Graded.shift ℬ c) q ↔
      IsHomogeneous f 𝒜 ℬ (q + c - Fintype.card κ • c) := by
  rw [isHomogeneous_shift_iff]
  simp only [Finset.sum_const, Finset.card_univ]

end Shift

section Suspension

variable {R : Type uR} {κ : Type uκ} {M : Type uM} {σM : Type*}
  [Semiring R] [Fintype κ] [AddCommMonoid M] [Module R M] [SetLike σM M]

/-- **The suspension degree bridge.** An arity-`n` operation is homogeneous of degree one for the
suspended grading `sA` exactly when it is homogeneous of degree `2 - n` for the original grading.
This is the degree content of the square defining the suspended operations `bₙ` of an `A∞`
algebra from its operations `mₙ`. -/
theorem isHomogeneous_suspension_iff {f : MultilinearMap R (fun _ : κ ↦ M) M} {𝒜 : ℤ → σM} :
    IsHomogeneous f (fun _ ↦ Graded.shift 𝒜 1) (Graded.shift 𝒜 1) 1 ↔
      IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - Fintype.card κ) := by
  rw [isHomogeneous_shift_const_iff]
  norm_num

/-- The suspension degree bridge for an operation of arity `n`. Reading off `n = 1, 2, 3` gives
the familiar degrees `1`, `0` and `-1` of the differential, the multiplication and the first
higher product of an `A∞` algebra. -/
theorem isHomogeneous_suspension_fin_iff {n : ℕ} {f : MultilinearMap R (fun _ : Fin n ↦ M) M}
    {𝒜 : ℤ → σM} :
    IsHomogeneous f (fun _ ↦ Graded.shift 𝒜 1) (Graded.shift 𝒜 1) 1 ↔
      IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - n) := by
  simpa using isHomogeneous_suspension_iff (f := f) (𝒜 := 𝒜)

end Suspension

end MultilinearMap

end TauCeti
