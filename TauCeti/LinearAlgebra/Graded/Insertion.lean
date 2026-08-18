/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
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

The signed operation is packaged for a fixed homogeneous component: on such a component its sign
is a scalar, so it is again a multilinear map.  The homogeneity theorem proves that insertion adds
the degrees of the outer and inner operations.

## Main definitions

* `MultilinearMap.oneSlot`: substitute one multilinear map into a specified block of another.
* `MultilinearMap.koszulSign`: the sign acquired by crossing the prefix inputs.
* `MultilinearMap.signedOneSlot`: one-slot substitution on a fixed homogeneous component.

## References

* Ezra Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* Bernhard Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

open scoped BigOperators

universe uR uα uβ uγ uM uN

namespace MultilinearMap

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
    IsHomogeneous (oneSlot f g) (Sum.elim A (Sum.elim B C)) E (q + p) := by
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

section Signed

variable {R : Type uR} [CommRing R]

/-- The Koszul coefficient acquired when a degree-`q` operation crosses homogeneous inputs with
degrees `d i`. -/
def koszulSign {α : Type uα} [Fintype α] (q : ℤ) (d : α → ℤ) : R :=
  (((ComplexShape.up ℤ).ε (q * ∑ i, d i) : ℤ) : R)

/-- The tensor-sign character on cochain degrees is the usual power of negative one. -/
@[simp]
theorem koszulSign_eq_negOnePow {α : Type uα} [Fintype α] (q : ℤ) (d : α → ℤ) :
    koszulSign (R := R) q d = (((q * ∑ i, d i).negOnePow : ℤ) : R) := by
  simp [koszulSign]

@[simp]
theorem koszulSign_zero_degree {α : Type uα} [Fintype α] (d : α → ℤ) :
    koszulSign (R := R) 0 d = 1 := by
  simp [koszulSign]

@[simp]
theorem koszulSign_empty (q : ℤ) (d : Fin 0 → ℤ) :
    koszulSign (R := R) q d = 1 := by
  simp [koszulSign]

theorem koszulSign_add_degree {α : Type uα} [Fintype α] (q q' : ℤ) (d : α → ℤ) :
    koszulSign (R := R) (q + q') d =
      koszulSign (R := R) q d * koszulSign (R := R) q' d := by
  simp only [koszulSign, add_mul, ComplexShape.ε_add, Units.val_mul]
  norm_cast

/-- Signed one-slot substitution on the homogeneous component whose prefix degrees are `d`.

The sign is constant on this component, so scalar multiplication preserves multilinearity. -/
def signedOneSlot {M : Type uM} {N : Type uN} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {α : Type uα} [Fintype α] {β : Type uβ} {γ : Type uγ}
    (q : ℤ) (d : α → ℤ)
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) :
    MultilinearMap R (fun _ : α ⊕ (β ⊕ γ) ↦ M) N :=
  koszulSign (R := R) q d • oneSlot f g

@[simp]
theorem signedOneSlot_apply {M : Type uM} {N : Type uN} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {α : Type uα} [Fintype α] {β : Type uβ} {γ : Type uγ}
    (q : ℤ) (d : α → ℤ)
    (f : MultilinearMap R (fun _ : α ⊕ (Unit ⊕ γ) ↦ M) N)
    (g : MultilinearMap R (fun _ : β ↦ M) M) (x : α ⊕ (β ⊕ γ) → M) :
    signedOneSlot q d f g x = koszulSign (R := R) q d • f (Sum.elim (fun i ↦ x (.inl i)) <|
      Sum.elim (fun _ ↦ g fun j ↦ x (.inr (.inl j))) (fun i ↦ x (.inr (.inr i)))) :=
  by rw [signedOneSlot, smul_apply, oneSlot_apply]

end Signed

section SignedHomogeneous

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
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
    IsHomogeneous (signedOneSlot q d f g) (Sum.elim A (Sum.elim B C)) E (q + p) := by
  rw [TauCeti.MultilinearMap.signedOneSlot]
  exact (hf.oneSlot hg).smul (koszulSign q d)

end SignedHomogeneous

end MultilinearMap

end TauCeti
