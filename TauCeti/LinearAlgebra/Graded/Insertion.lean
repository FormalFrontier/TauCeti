/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Reflection
public import TauCeti.LinearAlgebra.Graded.Multilinear

/-!
# Signed insertion of graded multilinear maps

This file defines one-slot substitution of multilinear maps.  The inputs are split into a prefix,
the block consumed by the inserted map, and a suffix.  Using sum types for these three blocks keeps
the evaluation rule definitional and avoids transports between propositionally equal finite
arities.

For graded maps, inserting a map of degree `q` after homogeneous prefix inputs of degrees `d i`
contributes the Koszul coefficient

`(-1) ^ (q * ∑ i, d i)`.

The signed operation takes the intended degrees of the homogeneous prefix inputs as an explicit
parameter.  The API does not enforce that these degrees correspond to the inputs; on the intended
component the sign is a scalar, so the result is again a multilinear map.  The homogeneity theorem
proves that insertion adds the degrees of the outer and inner operations.

## Main definitions

* `MultilinearMap.evalNat`: evaluate a finite-arity map on a natural-indexed input family.
* `TauCeti.replaceBlock`: collapse a consecutive block in a natural-indexed family.
* `Fin.blockEquiv` and `Fin.oneSlotEquiv`: canonical reindexings for one-slot substitution.
* `MultilinearMap.oneSlot`: substitute one multilinear map into a specified block of another.
* `MultilinearMap.koszulSign`: the sign acquired by crossing the prefix inputs.
* `MultilinearMap.signedOneSlot`: one-slot substitution scaled by the Koszul sign for supplied
  prefix degrees, correct when the prefix inputs have those degrees.

## References

* Ezra Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* Bernhard Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped BigOperators
open TauCeti
open MultilinearMap

universe uR uα uβ uγ uM uN

namespace MultilinearMap

section EvalNat

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Evaluate an arity-`k` operation on the first `k` entries of a family indexed by the naturals. -/
def evalNat {k : ℕ} {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin k ↦ M) N) (x : ℕ → M) : N :=
  f fun i ↦ x i.1

theorem evalNat_def {k : ℕ} {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin k ↦ M) N) (x : ℕ → M) :
    evalNat f x = f (fun i ↦ x i.1) := (rfl)

/-- `evalNat` only reads the entries whose indices are below the operation's arity. -/
theorem evalNat_congr {k : ℕ} {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin k ↦ M) N) {x y : ℕ → M}
    (h : ∀ i < k, x i = y i) : evalNat f x = evalNat f y := by
  rw [evalNat_def, evalNat_def]
  congr 1
  funext i
  exact h i i.isLt

@[simp]
theorem evalNat_smul {k : ℕ} {N : Type uN} [AddCommMonoid N] [Module R N]
    [SMulCommClass R R N]
    (c : R) (f : MultilinearMap R (fun _ : Fin k ↦ M) N) (x : ℕ → M) :
    evalNat (c • f) x = c • evalNat f x := by
  simp [evalNat]

@[simp]
theorem evalNat_one {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin 1 ↦ M) N) (x : ℕ → M) :
    evalNat f x = f ![x 0] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_two {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin 2 ↦ M) N) (x : ℕ → M) :
    evalNat f x = f ![x 0, x 1] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_three {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin 3 ↦ M) N) (x : ℕ → M) :
    evalNat f x = f ![x 0, x 1, x 2] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

@[simp]
theorem evalNat_four {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : Fin 4 ↦ M) N) (x : ℕ → M) :
    evalNat f x = f ![x 0, x 1, x 2, x 3] := by
  exact congrArg f (FinVec.etaExpand_eq _).symm

end EvalNat

section OneSlot

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

private def OneSlotArity (β : Type uβ) : α ⊕ (Unit ⊕ γ) → Type uβ
  | .inl _ => ULift.{uβ} Unit
  | .inr (.inl _) => β
  | .inr (.inr _) => ULift.{uβ} Unit

private def oneSlotIndexEquiv (α : Type uα) (β : Type uβ) (γ : Type uγ) :
    (Σ i, OneSlotArity (α := α) (γ := γ) β i) ≃ α ⊕ (β ⊕ γ) where
  toFun
    | ⟨.inl i, _⟩ => .inl i
    | ⟨.inr (.inl ()), j⟩ => .inr (.inl j)
    | ⟨.inr (.inr i), _⟩ => .inr (.inr i)
  invFun
    | .inl i => ⟨.inl i, ⟨()⟩⟩
    | .inr (.inl j) => ⟨.inr (.inl ()), j⟩
    | .inr (.inr i) => ⟨.inr (.inr i), ⟨()⟩⟩
  left_inv
    | ⟨.inl _, ⟨()⟩⟩ => rfl
    | ⟨.inr (.inl ()), _⟩ => rfl
    | ⟨.inr (.inr _), ⟨()⟩⟩ => rfl
  right_inv x := by rcases x with i | (j | i) <;> rfl

private def unaryId : MultilinearMap R (fun _ : ULift.{uβ} Unit ↦ M) M where
  toFun x := x ⟨()⟩
  map_update_add' _ i := by rcases i with ⟨i⟩; rcases i with ⟨⟩; simp
  map_update_smul' _ i := by rcases i with ⟨i⟩; rcases i with ⟨⟩; simp

private def oneSlotMaps {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (g : MultilinearMap R (fun _ : β ↦ M) M) :
    (i : α ⊕ (Unit ⊕ γ)) → MultilinearMap R (fun _ : OneSlotArity β i ↦ M) M
  | .inl _ => unaryId
  | .inr (.inl _) => g
  | .inr (.inr _) => unaryId

/-- Substitute `g` into the middle input of `f`.

The domain is divided into prefix inputs `α`, the inputs `β` consumed by `g`, and suffix
inputs `γ`.  Correspondingly, `f` has prefix inputs, one middle input, and suffix inputs. -/
def oneSlot {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) :
    MultilinearMap R (fun _ : α ⊕ (β ⊕ γ) ↦ M) N :=
  (f.compMultilinearMap (oneSlotMaps g)).domDomCongr (oneSlotIndexEquiv α β γ)

/-- Evaluating `oneSlot f g` substitutes the value of `g` on the middle block between the
unchanged prefix and suffix inputs of `f`. -/
@[simp]
theorem oneSlot_apply {α : Type uα} {β : Type uβ} {γ : Type uγ}
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) (x : α ⊕ (β ⊕ γ) → M) :
    oneSlot f g x = f (Sum.elim (fun i ↦ x (.inl i)) <|
      Sum.elim (fun _ ↦ g fun j ↦ x (.inr (.inl j))) (fun i ↦ x (.inr (.inr i)))) :=
  by
    rw [oneSlot, _root_.MultilinearMap.domDomCongr_apply,
      _root_.MultilinearMap.compMultilinearMap_apply]
    congr 1
    funext i
    rcases i with i | (i | i)
    · rfl
    · rcases i with ⟨⟩
      congr 1
    · rfl

end OneSlot

end MultilinearMap

namespace TauCeti

/-- Replace the block of `s` entries at position `p` of a natural-indexed family by `v`. -/
def replaceBlock {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) : ℕ → α := fun i ↦
  if i < p then x i else if i = p then v else x (i + s - 1)

@[simp]
theorem replaceBlock_of_lt {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) {i : ℕ} (h : i < p) :
    replaceBlock x p s v i = x i := by simp [replaceBlock, h]

@[simp]
theorem replaceBlock_self {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) :
    replaceBlock x p s v p = v := by simp [replaceBlock]

@[simp]
theorem replaceBlock_of_gt {α : Type*} (x : ℕ → α) (p s : ℕ) (v : α) {i : ℕ} (h : p < i) :
    replaceBlock x p s v i = x (i + s - 1) := by
  simp only [replaceBlock]
  split_ifs with h₁ h₂
  · exact absurd h₁ (by omega)
  · exact absurd h₂ (by omega)
  · rfl

end TauCeti

namespace Fin

/-- Identify a prefix, inserted block, and suffix with their total finite arity. -/
def blockEquiv (p s t : ℕ) : Fin p ⊕ (Fin s ⊕ Fin t) ≃ Fin (p + s + t) :=
  (Equiv.sumCongr (Equiv.refl (Fin p))
      (finSumFinEquiv : Fin s ⊕ Fin t ≃ Fin (s + t))).trans <|
    (finSumFinEquiv : Fin p ⊕ Fin (s + t) ≃ Fin (p + (s + t))).trans
      (finCongr (by omega))

@[simp]
theorem blockEquiv_inl_val (p s t : ℕ) (i : Fin p) :
    (blockEquiv p s t (.inl i) : ℕ) = i := by
  simp [blockEquiv]

@[simp]
theorem blockEquiv_middle_val (p s t : ℕ) (j : Fin s) :
    (blockEquiv p s t (.inr (.inl j)) : ℕ) = p + j := by
  simp [blockEquiv]

@[simp]
theorem blockEquiv_suffix_val (p s t : ℕ) (j : Fin t) :
    (blockEquiv p s t (.inr (.inr j)) : ℕ) = p + s + j := by
  simp [blockEquiv]
  omega

/-- Identify a prefix, one collapsed slot, and suffix with their total finite arity. -/
def oneSlotEquiv (p t : ℕ) : Fin p ⊕ (Unit ⊕ Fin t) ≃ Fin (p + 1 + t) :=
  (Equiv.sumCongr (Equiv.refl (Fin p))
    (Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin t)))).trans (blockEquiv p 1 t)

@[simp]
theorem oneSlotEquiv_inl_val (p t : ℕ) (i : Fin p) :
    (oneSlotEquiv p t (.inl i) : ℕ) = i := by
  simp [oneSlotEquiv]

@[simp]
theorem oneSlotEquiv_middle_val (p t : ℕ) :
    (oneSlotEquiv p t (.inr (.inl ())) : ℕ) = p := by
  simp [oneSlotEquiv]

@[simp]
theorem oneSlotEquiv_suffix_val (p t : ℕ) (j : Fin t) :
    (oneSlotEquiv p t (.inr (.inr j)) : ℕ) = p + 1 + j := by
  simp [oneSlotEquiv]

end Fin

namespace TauCeti.MultilinearMap

section Homogeneous

variable {R : Type uR} {M : Type uM} {N : Type uN} {ι : Type*}
  [Semiring R] [AddCommMonoid ι] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {σM : Type*} {σN : Type*} [SetLike σM M] [SetLike σN N]

/-- One-slot substitution adds the degree of the inserted map to the degree of the outer map. -/
@[grind →]
theorem IsHomogeneous.oneSlot {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [Fintype α] [Fintype β] [Fintype γ]
    {f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N}
    {g : MultilinearMap R (fun _ : β ↦ M) M}
    {A : α → ι → σM} {B : β → ι → σM} {C : γ → ι → σM}
    {D : ι → σM} {E : ι → σN} {p q : ι}
    (hf : IsHomogeneous f (Sum.elim A (Sum.elim (fun _ ↦ D) C)) E p)
    (hg : IsHomogeneous g B D q) :
    IsHomogeneous (f.oneSlot g) (Sum.elim A (Sum.elim B C)) E (q + p) := by
  rw [isHomogeneous_def]
  intro d x hx
  have hgx := hg.map_mem (fun i ↦ d (.inr (.inl i))) (fun i ↦ x (.inr (.inl i)))
    fun i ↦ hx (.inr (.inl i))
  have hfx := hf.map_mem
    (Sum.elim (fun i ↦ d (.inl i)) <| Sum.elim
      (fun _ ↦ (∑ i, d (.inr (.inl i))) + q) (fun i ↦ d (.inr (.inr i))))
    (Sum.elim (fun i ↦ x (.inl i)) <| Sum.elim
      (fun _ ↦ g fun j ↦ x (.inr (.inl j))) (fun i ↦ x (.inr (.inr i)))) <| by
      rintro (i | (_ | i))
      · exact hx (.inl i)
      · exact hgx
      · exact hx (.inr (.inr i))
  rw [← oneSlot_apply] at hfx
  convert hfx using 1
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr]
  ac_rfl

end Homogeneous

end TauCeti.MultilinearMap

namespace MultilinearMap

section Signed

variable {R : Type uR}

section KoszulSign

variable [Ring R]

/-- The Koszul coefficient acquired when a degree-`q` operation crosses homogeneous inputs with
degrees `d i`. -/
def koszulSign {α : Type uα} [Fintype α] (q : ℤ) (d : α → ℤ) : R :=
  TauCeti.negOnePowCast R (q * ∑ i, d i)

/-- The Koszul coefficient is the ground-ring power of negative one. -/
@[simp]
theorem koszulSign_eq_negOnePowCast {α : Type uα} [Fintype α] (q : ℤ) (d : α → ℤ) :
    koszulSign (R := R) q d = TauCeti.negOnePowCast R (q * ∑ i, d i) := (rfl)

theorem koszulSign_add_degree {α : Type uα} [Fintype α] (q q' : ℤ) (d : α → ℤ) :
    koszulSign (R := R) (q + q') d =
      koszulSign (R := R) q d * koszulSign (R := R) q' d := by
  simp only [koszulSign, add_mul, TauCeti.negOnePowCast_add]

end KoszulSign

section SignedOneSlot

variable [CommRing R]

/-- Signed one-slot substitution using `d` as the supplied degrees of the homogeneous prefix
inputs.

The API does not enforce that `d` corresponds to the input components.  On the intended component
the sign is constant, so scalar multiplication preserves multilinearity. -/
def signedOneSlot {M : Type uM} {N : Type uN} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {α : Type uα} [Fintype α] {β : Type uβ} {γ : Type uγ}
    (q : ℤ) (d : α → ℤ)
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) :
    MultilinearMap R (fun _ : α ⊕ (β ⊕ γ) ↦ M) N :=
  koszulSign (R := R) q d • f.oneSlot g

/-- Evaluating `signedOneSlot q d f g` gives the one-slot substitution formula multiplied by the
Koszul sign determined by `q` and the supplied prefix degrees `d`. -/
@[simp]
theorem signedOneSlot_apply {M : Type uM} {N : Type uN} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {α : Type uα} [Fintype α] {β : Type uβ} {γ : Type uγ}
    (q : ℤ) (d : α → ℤ)
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) (x : α ⊕ (β ⊕ γ) → M) :
    signedOneSlot q d f g x = koszulSign (R := R) q d • f (Sum.elim (fun i ↦ x (.inl i)) <|
      Sum.elim (fun _ ↦ g fun j ↦ x (.inr (.inl j))) (fun i ↦ x (.inr (.inr i)))) :=
  by rw [signedOneSlot, smul_apply, oneSlot_apply]

end SignedOneSlot

end Signed

end MultilinearMap

namespace TauCeti.MultilinearMap

section SignedHomogeneous

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {σM : Type*} {σN : Type*} [SetLike σM M] [SetLike σN N] [SMulMemClass σN R N]

/-- Signed one-slot substitution has the sum of the degrees of its two operations. -/
theorem IsHomogeneous.signedOneSlot {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [Fintype α] [Fintype β] [Fintype γ]
    {f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N}
    {g : MultilinearMap R (fun _ : β ↦ M) M}
    {A : α → ℤ → σM} {B : β → ℤ → σM} {C : γ → ℤ → σM}
    {D : ℤ → σM} {E : ℤ → σN} {p q : ℤ} (d : α → ℤ)
    (hf : IsHomogeneous f (Sum.elim A (Sum.elim (fun _ ↦ D) C)) E p)
    (hg : IsHomogeneous g B D q) :
    IsHomogeneous (f.signedOneSlot q d g) (Sum.elim A (Sum.elim B C)) E (q + p) := by
  rw [MultilinearMap.signedOneSlot]
  exact (hf.oneSlot hg).smul (koszulSign q d)

grind_pattern IsHomogeneous.signedOneSlot =>
  IsHomogeneous (MultilinearMap.signedOneSlot q d f g) (Sum.elim A (Sum.elim B C)) E (q + p),
  IsHomogeneous g B D q

end SignedHomogeneous

end TauCeti.MultilinearMap
