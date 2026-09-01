/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.LinearAlgebra.Graded.Multilinear
import Mathlib.Tactic.Ring

/-!
# Shifted gradings and the suspension of graded operations

This file shifts a family of graded pieces, records what the shift does to the degree of a
homogeneous linear or multilinear map, and defines the sign acquired when a multilinear operation
is suspended.

The shift of a family `𝒜` by `c` is the regrading `Graded.shift 𝒜 c` whose degree-`p` piece is
`𝒜 (p + c)`; this is the cochain shift `X[c]ᵖ = X^{p + c}`, and at `c = 1` it is the suspension
`sA` of the `A∞` conventions. Suspension does not move any element: the canonical map
`s : A ⟶ sA` and its inverse are the two directions of `Graded.shiftEquiv`, the identity
equivalence of the underlying module. All of their content is in the degrees recorded by
`LinearMap.isHomogeneous_shiftEquiv` and
`LinearMap.isHomogeneous_shiftEquiv_symm`.

The degree translation for multilinear maps says that a map of degree `q` after shifting
the `i`-th input grading by `c i` and the target grading by `r` has degree
`q + r - ∑ i, c i` in the original gradings. Its specialisation
`TauCeti.MultilinearMap.isHomogeneous_suspension_iff` is the degree half of the commuting square

```text
(sA)^⊗n  --bₙ--> sA
    ↑s^⊗n           ↑s
 A^⊗n     --mₙ-->  A
```

that defines the suspended operations of an `A∞` algebra: an arity-`n` operation is homogeneous of
degree one for the suspended grading exactly when it is homogeneous of degree `2 - n` for the
original one. The tensor power of suspension is not constructed here; `MultilinearMap.suspend`
adopts its Koszul sign as the evaluation-level definition of the suspended operation.

## Main definitions

* `TauCeti.Graded.shift`: the shift of a family of graded pieces.
* `TauCeti.Graded.shiftEquiv`: the canonical equivalence between the underlying modules of a
  grading and its shift; at a shift by one, its inverse is unsuspension.
* `MultilinearMap.suspExp`: the Koszul exponent for suspending a tuple.
* `MultilinearMap.suspend`: the signed operation obtained by suspension.

## Main results

* `TauCeti.LinearMap.isHomogeneous_shift_source_iff`, `TauCeti.LinearMap.isHomogeneous_shift_iff`,
  and `TauCeti.LinearMap.isHomogeneous_shift_target_iff`: shifting the source raises the degree of
  a linear map, shifting the target lowers it, and shifting both leaves it unchanged.
* `TauCeti.LinearMap.isHomogeneous_shiftEquiv` and
  `TauCeti.LinearMap.isHomogeneous_shiftEquiv_symm`: for a shift by `c`, the forward map has
  degree `-c` and the inverse has degree `c`; at `c = 1` these are suspension and unsuspension.
* `TauCeti.MultilinearMap.isHomogeneous_shift_iff`: shifting the inputs by `c` and the target by
  `r` translates degree `q` in the shifted gradings to degree `q + r - ∑ i, c i` in the original
  gradings.
* `TauCeti.MultilinearMap.isHomogeneous_suspension_iff` and
  `TauCeti.MultilinearMap.isHomogeneous_suspension_fin_iff`: an arity-`n` operation has degree one
  after suspension exactly when it has degree `2 - n` before.
* `MultilinearMap.suspend_suspend`: applying the suspension sign twice restores an operation.
* `TauCeti.MultilinearMap.isHomogeneous_suspend_iff`: suspension preserves the equivalent
  shifted and unshifted homogeneity conditions.

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

section ShiftEquiv

variable (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The canonical equivalence on the underlying module of a grading and its shift. At a shift by
one, its forward map is suspension and its inverse is unsuspension; the grading change and their
respective degrees are recorded by `LinearMap.isHomogeneous_shiftEquiv` and
`LinearMap.isHomogeneous_shiftEquiv_symm`. -/
def shiftEquiv : M ≃ₗ[R] M := LinearEquiv.refl R M

@[simp]
theorem shiftEquiv_apply (x : M) : shiftEquiv R M x = x := by
  simp [shiftEquiv]

@[simp]
theorem shiftEquiv_symm_apply (x : M) : (shiftEquiv R M).symm x = x := by
  simp [shiftEquiv]

end ShiftEquiv

end Graded

namespace LinearMap

section AddMonoid

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Shifting the target grading by `c` lowers the degree of a homogeneous linear map by `c`. -/
@[simp]
theorem isHomogeneous_shift_target_iff {f : M →ₗ[R] N} {𝒜 : ι → σM} {ℬ : ι → σN} {q c : ι} :
    IsHomogeneous f 𝒜 (Graded.shift ℬ c) q ↔ IsHomogeneous f 𝒜 ℬ (q + c) := by
  simp only [isHomogeneous_def, Graded.shift_apply, add_assoc]

/-- The inverse of `Graded.shiftEquiv`, viewed as the inverse of the shift by `c`, is homogeneous
of degree `c`. At `c = 1` this is unsuspension. -/
theorem isHomogeneous_shiftEquiv_symm (𝒜 : ι → σM) (c : ι) :
    IsHomogeneous (Graded.shiftEquiv R M).symm.toLinearMap (Graded.shift 𝒜 c) 𝒜 c := by
  rw [isHomogeneous_def]
  intro p x hx
  simpa only [_root_.LinearEquiv.coe_toLinearMap, Graded.shiftEquiv_symm_apply,
    Graded.shift_apply] using hx

end AddMonoid

section AddCommGroup

variable {R : Type uR} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddCommGroup ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]

/-- Shifting the source grading by `c` raises the degree of a homogeneous linear map by `c`. -/
@[simp]
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

/-- The forward map of `Graded.shiftEquiv`, viewed as the shift by `c`, is homogeneous of
degree `-c`. At `c = 1` this is the degree `-1` suspension map of the `A∞` conventions. -/
theorem isHomogeneous_shiftEquiv (𝒜 : ι → σM) (c : ι) :
    IsHomogeneous (Graded.shiftEquiv R M).toLinearMap 𝒜 (Graded.shift 𝒜 c) (-c) := by
  rw [isHomogeneous_def]
  intro p x hx
  have hpc : p + -c + c = p := by simp [add_assoc]
  simpa only [_root_.LinearEquiv.coe_toLinearMap, Graded.shiftEquiv_apply,
    Graded.shift_apply, hpc] using hx

end AddGroup

section Submodule

variable {R : Type uR} {S : Type*} {ι : Type uι} {M : Type uM} {N : Type uN} {σM σN : Type*}
  [Semiring R] [AddMonoid ι] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [SetLike σM M] [SetLike σN N]
  [Semiring S] [Module S N] [SMulCommClass R S N] [AddSubmonoidClass σN N] [SMulMemClass σN S N]

/-- Shifting the target grading by `c` shifts the submodule of homogeneous linear maps of
degree `q` to the one of degree `q + c`. -/
@[simp]
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
@[simp]
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
  simp

end Suspension

end MultilinearMap

end TauCeti

namespace MultilinearMap

section SignedSuspension

variable {R : Type uR} [CommRing R]

/-- The exponent of the sign prescribed by the Koszul rule for suspending a tuple of inputs with
degrees `d`. The suspension map has degree `-1`, so input `i` contributes its degree once for
every input to its right. -/
def suspExp (k : ℕ) (d : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range k, ((k : ℤ) - 1 - i) * d i

/-- The defining sum for the suspension exponent. -/
theorem suspExp_def (k : ℕ) (d : ℕ → ℤ) :
    suspExp k d = ∑ i ∈ Finset.range k, ((k : ℤ) - 1 - i) * d i := (rfl)

@[simp]
theorem suspExp_zero (d : ℕ → ℤ) : suspExp 0 d = 0 := by simp [suspExp]

@[simp]
theorem suspExp_one (d : ℕ → ℤ) : suspExp 1 d = 0 := by simp [suspExp]

/-- The suspension exponent only reads the first `k` degrees. -/
theorem suspExp_congr {k : ℕ} {d e : ℕ → ℤ} (h : ∀ i < k, d i = e i) :
    suspExp k d = suspExp k e := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.1 hi)]

/-- Split the suspension exponent between an initial block and the block following it. -/
theorem suspExp_add (a b : ℕ) (d : ℕ → ℤ) :
    suspExp (a + b) d =
      (∑ i ∈ Finset.range a, ((a : ℤ) + b - 1 - i) * d i) +
        ∑ j ∈ Finset.range b, ((b : ℤ) - 1 - j) * d (a + j) := by
  rw [suspExp, Finset.sum_range_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    (Finset.sum_congr rfl fun j _ ↦ ?_)
  · rfl
  · push_cast
    ring

/-- Split the suspension exponent into a prefix, a middle block, and a suffix. -/
theorem suspExp_add3 (a b c : ℕ) (d : ℕ → ℤ) :
    suspExp (a + b + c) d =
      ((∑ i ∈ Finset.range a, ((a : ℤ) + b + c - 1 - i) * d i) +
        ∑ j ∈ Finset.range b, ((c : ℤ) + b - 1 - j) * d (a + j)) +
          ∑ j ∈ Finset.range c, ((c : ℤ) - 1 - j) * d (a + b + j) := by
  rw [add_assoc a b c, suspExp_add, Finset.sum_range_add, ← add_assoc]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← add_assoc a b j]
    push_cast
    ring

/-- The signed operation prescribed by the suspension square. The tensor power of the suspension
map is not formalized here; this adopts its Koszul sign as the definition. -/
def suspend {k : ℕ} {M : Fin k → Type uM} {N : Type uN}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R M N) : MultilinearMap R M N :=
  TauCeti.negOnePowCast R (suspExp k d) • f

/-- Suspension scales an operation by the Koszul sign of the supplied degrees. -/
theorem suspend_eq_smul {k : ℕ} {M : Fin k → Type uM} {N : Type uN}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R M N) :
    suspend d f = TauCeti.negOnePowCast R (suspExp k d) • f := (rfl)

/-- Evaluation of a suspended multilinear operation. -/
@[simp]
theorem suspend_apply {k : ℕ} {M : Fin k → Type uM} {N : Type uN}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R M N) (x : ∀ i, M i) :
    suspend d f x = TauCeti.negOnePowCast R (suspExp k d) • f x := by
  rw [suspend_eq_smul, smul_apply]

/-- Suspension for a fixed degree family is an involution, so `suspend d` also computes
unsuspension. -/
@[simp]
theorem suspend_suspend {k : ℕ} {M : Fin k → Type uM} {N : Type uN}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R M N) : suspend d (suspend d f) = f := by
  rw [suspend_eq_smul, suspend_eq_smul, smul_smul, ← TauCeti.negOnePowCast_add, ← two_mul,
    TauCeti.negOnePowCast_two_mul, one_smul]

end SignedSuspension

end MultilinearMap

namespace TauCeti.MultilinearMap

section HomogeneousSuspension

open _root_.MultilinearMap (suspend suspend_suspend)

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]
variable {σ : Type*} [SetLike σ M] [SMulMemClass σ R M]

/-- Suspension gives an equivalence between the degree conditions on suspended and unsuspended
operations. -/
theorem isHomogeneous_suspend_iff {k : ℕ} {𝒜 : ℤ → σ} {d : ℕ → ℤ}
    {f : MultilinearMap R (fun _ : Fin k ↦ M) M} :
    IsHomogeneous (suspend d f) (fun _ ↦ Graded.shift 𝒜 1) (Graded.shift 𝒜 1) 1 ↔
      IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - k) := by
  rw [isHomogeneous_suspension_fin_iff]
  constructor
  · intro hf
    rw [← suspend_suspend d f]
    rw [_root_.MultilinearMap.suspend_eq_smul]
    exact hf.smul _
  · exact fun hf ↦ hf.smul _

/-- Suspending a homogeneous arity-`k` operation of degree `2 - k` produces one of degree one. -/
theorem IsHomogeneous.suspend {k : ℕ} {𝒜 : ℤ → σ} {d : ℕ → ℤ}
    {f : MultilinearMap R (fun _ : Fin k ↦ M) M}
    (hf : IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - k)) :
    IsHomogeneous (suspend d f) (fun _ ↦ Graded.shift 𝒜 1) (Graded.shift 𝒜 1) 1 :=
  isHomogeneous_suspend_iff.2 hf

grind_pattern IsHomogeneous.suspend =>
  IsHomogeneous (suspend d f) (fun _ ↦ Graded.shift 𝒜 1) (Graded.shift 𝒜 1) 1,
  IsHomogeneous f (fun _ ↦ 𝒜) 𝒜 (2 - k)

end HomogeneousSuspension

end TauCeti.MultilinearMap
