/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Permutations preserving the fibers of a map

Given `f : α → ι`, the permutations `σ` of `α` with `f (σ a) = f a` for every `a` form a subgroup
of `Equiv.Perm α`, here called `TauCeti.fiberSubgroup f`.  This file records that subgroup, the
behaviour of the construction under pairing two maps, the criterion for it to be trivial, and the
isomorphism restricting a fiber-preserving permutation to each fiber,

`fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i}`.

Mathlib already studies these permutations, but through the domain action of `Equiv.Perm α` on
`α → ι`: `DomMulAct.stabilizerMulEquiv` is the same isomorphism stated on
`(MulAction.stabilizer (Equiv.Perm α)ᵈᵐᵃ f)ᵐᵒᵖ`.  The `ᵈᵐᵃ`/`ᵐᵒᵖ` wrapping makes it awkward to use
where the object of interest is a subgroup of `Equiv.Perm α` itself, as it is for the row and
column groups of a Young tableau; `fiberSubgroup` is that subgroup, and the isomorphism below is
built from Mathlib's construction of the inverse map, `DomMulAct.stabilizerEquiv_invFun_aux`.
-/

@[expose] public section

namespace TauCeti

variable {α ι κ : Type*}

/-- The subgroup of permutations of `α` that preserve every fiber of `f : α → ι`, that is, those
moving each point within its own fiber. -/
def fiberSubgroup (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  mul_mem' hσ hτ a := (hσ _).trans (hτ a)
  one_mem' _ := rfl
  inv_mem' {σ} hσ a := by
    have h := hσ (σ⁻¹ a)
    rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply, eq_comm] at h

@[simp]
theorem mem_fiberSubgroup {f : α → ι} {σ : Equiv.Perm α} :
    σ ∈ fiberSubgroup f ↔ ∀ a, f (σ a) = f a :=
  Iff.rfl

/-- Preserving the fibers of two maps at once is preserving the fibers of the paired map. -/
theorem fiberSubgroup_inf (f : α → ι) (g : α → κ) :
    fiberSubgroup f ⊓ fiberSubgroup g = fiberSubgroup fun a => (f a, g a) := by
  ext σ
  simp [Subgroup.mem_inf, Prod.ext_iff, forall_and]

/-- Only the identity preserves the fibers of an injective map, its fibers being singletons. -/
theorem fiberSubgroup_eq_bot_of_injective {f : α → ι} (hf : Function.Injective f) :
    fiberSubgroup f = ⊥ :=
  eq_bot_iff.mpr fun _ hσ => Subgroup.mem_bot.mpr (Equiv.ext fun a => hf (hσ a))

/-- If the identity is the only permutation preserving the fibers of `f`, then `f` is injective:
two points in a common fiber would be exchanged by a nontrivial fiber-preserving transposition. -/
theorem injective_of_fiberSubgroup_eq_bot {f : α → ι}
    (h : fiberSubgroup f = ⊥) : Function.Injective f := by
  classical
  intro a b hab
  by_contra hne
  have hswap : Equiv.swap a b ∈ fiberSubgroup f := by
    intro x
    rcases eq_or_ne x a with rfl | hxa
    · simpa using hab.symm
    · rcases eq_or_ne x b with rfl | hxb
      · simpa using hab
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  rw [h, Subgroup.mem_bot, Equiv.Perm.one_def] at hswap
  exact hne (Equiv.swap_eq_refl_iff.mp hswap)

/-- The fibers of `f` are preserved only by the identity exactly when `f` is injective. -/
theorem fiberSubgroup_eq_bot_iff {f : α → ι} :
    fiberSubgroup f = ⊥ ↔ Function.Injective f :=
  ⟨injective_of_fiberSubgroup_eq_bot, fiberSubgroup_eq_bot_of_injective⟩

/-- Restricting a fiber-preserving permutation of `α` to each fiber of `f` is an isomorphism onto
the product of the permutation groups of the fibers.

This is `DomMulAct.stabilizerMulEquiv` transported to the subgroup `fiberSubgroup f` of
`Equiv.Perm α`; the inverse map, assembling a family of permutations of the fibers into a
permutation of `α`, is Mathlib's `DomMulAct.stabilizerEquiv_invFun_aux`. -/
def fiberSubgroupMulEquivPiPerm (f : α → ι) :
    fiberSubgroup f ≃* ∀ i, Equiv.Perm {a // f a = i} where
  toFun σ i := Equiv.Perm.subtypePerm (σ : Equiv.Perm α) fun a => by
    rw [mem_fiberSubgroup.mp σ.2 a]
  invFun g :=
    ⟨DomMulAct.stabilizerEquiv_invFun_aux g, fun a => DomMulAct.comp_stabilizerEquiv_invFun g a⟩
  left_inv σ := Subtype.ext (Equiv.ext fun _ => rfl)
  right_inv g := by
    funext i
    ext a
    exact DomMulAct.stabilizerEquiv_invFun_eq g a.2
  map_mul' _ _ := rfl

@[simp]
theorem fiberSubgroupMulEquivPiPerm_apply_coe (f : α → ι) (σ : fiberSubgroup f) (i : ι)
    (a : {a // f a = i}) :
    (fiberSubgroupMulEquivPiPerm f σ i a : α) = (σ : Equiv.Perm α) a :=
  rfl

end TauCeti
