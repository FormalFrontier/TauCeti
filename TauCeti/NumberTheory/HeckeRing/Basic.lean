/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.NumberTheory.HeckeRing.Defs
public import Mathlib.GroupTheory.Index

/-!
# Hecke rings: the double coset API

Basic API for the double cosets `HeckeCoset` indexing a Hecke coset module, following
[Shimura][shimura1971], Chapter 3. This file provides representatives of double cosets, the
characterisation of when two elements give the same double coset, and the quotient
`Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets inside a double coset `Γ₁gΓ₂`, which is used to
define the Hecke product in later files and is finite for a Hecke triple. It also houses
the basis-element API of the coset module: `HeckeCosetModule.single` with its evaluation,
summation, and additivity laws, the `induction_linear` principle, and the transported
`Module` instance — placed at this layer so every later file (convolution, one, and the
coset actions) can build on one shared vocabulary.

Vendored from the in-review mathlib4 PR
[#41253](https://github.com/leanprover-community/mathlib4/pull/41253) (Chris Birkbeck), per the
ModularForms roadmap's dependency policy; migrate to Mathlib and delete this file when that
stack merges.

## Main definitions

* `HeckeCoset.toSet`: the underlying set `H₁gH₂` of a double coset.
* `HeckeCoset.rep`: a chosen representative in `Δ`.
* `DoubleCoset.DecompQuotient`: the quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets
  in `Γ₁gΓ₂`; finite for a Hecke triple.
* `HeckeCosetModule.single`: the basis element `b • [D]` of the Hecke coset module, with
  `single_apply`, `sum_single_index`, `smul_single_one`, `single_add`, `induction_linear`,
  and the `Module R` instance `HeckeCosetModule.instModule`.

## Main results

* `HeckeCoset.eq_iff`: `mk H₁ H₂ g = mk H₁ H₂ h ↔ H₁gH₂ = H₁hH₂`.
* `HeckeCoset.toSet_injective`: a double coset is determined by its underlying set.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

namespace HeckeCoset

variable {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

/-- The underlying set `H₁gH₂` of a double coset, well-defined on the quotient. -/
def toSet (D : HeckeCoset Δ H₁ H₂) : Set G :=
  Quotient.lift (fun g : Δ ↦ doubleCoset (g : G) H₁ H₂) (fun _ _ h ↦ h) D

/-- A representative `g : Δ` of a double coset (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset Δ H₁ H₂) : Δ := Quotient.out D

@[simp] lemma mk_rep (D : HeckeCoset Δ H₁ H₂) : mk H₁ H₂ D.rep = D := Quotient.out_eq' D

/-- Two elements of `Δ` define the same `HeckeCoset` iff their double cosets coincide. -/
lemma eq_iff {g h : Δ} : mk H₁ H₂ g = mk H₁ H₂ h ↔
    doubleCoset (g : G) H₁ H₂ = doubleCoset (h : G) H₁ H₂ := Quotient.eq''

@[simp] lemma toSet_mk (g : Δ) : toSet (mk H₁ H₂ g) = doubleCoset (g : G) H₁ H₂ := (rfl)

lemma toSet_eq_doubleCoset_rep (D : HeckeCoset Δ H₁ H₂) :
    D.toSet = doubleCoset (D.rep : G) H₁ H₂ := by rw [← toSet_mk, mk_rep]

/-- A double coset is determined by its underlying set. -/
lemma toSet_injective : Function.Injective (toSet : HeckeCoset Δ H₁ H₂ → Set G) := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ fun _ _ h ↦ Quotient.sound' h

lemma rep_mem (D : HeckeCoset Δ H₁ H₂) : (D.rep : G) ∈ D.toSet :=
  D.toSet_eq_doubleCoset_rep ▸ mem_doubleCoset_self H₁ H₂ _

/-- `mk H₁ H₂ g₁ = mk H₁ H₂ g₂` when `g₁` lies in the double coset of `g₂`. -/
lemma mk_eq_mk_of_mem {g₁ g₂ : Δ} (h : (g₁ : G) ∈ doubleCoset (g₂ : G) H₁ H₂) :
    mk H₁ H₂ g₁ = mk H₁ H₂ g₂ :=
  eq_iff.mpr (doubleCoset_eq_of_mem h)

/-- Induction: to prove something for all double cosets, prove it for `mk H₁ H₂ g`. -/
protected lemma induction {motive : HeckeCoset Δ H₁ H₂ → Prop}
    (h : ∀ g : Δ, motive (mk H₁ H₂ g)) :
    ∀ D, motive D :=
  Quotient.ind' h

/-- Two-argument induction for double cosets. -/
protected lemma induction₂ {motive : HeckeCoset Δ H₁ H₂ → HeckeCoset Δ H₁ H₂ → Prop}
    (h : ∀ g₁ g₂ : Δ, motive (mk H₁ H₂ g₁) (mk H₁ H₂ g₂)) : ∀ D₁ D₂, motive D₁ D₂ := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ h

variable {H : Subgroup G}

@[simp] lemma toSet_one : toSet (1 : HeckeCoset Δ H H) = (H : Set G) := by
  -- `toSet 1` unfolds to the set product `↑H * {1} * ↑H`; `change` states it so that the
  -- pointwise set lemmas apply (there is no rewriting lemma through the quotient here)
  change (H : Set G) * {(1 : G)} * H = (H : Set G)
  rw [Subgroup.subgroup_mul_singleton H.one_mem, coe_mul_coe]

lemma rep_one_mem : (rep (1 : HeckeCoset Δ H H) : G) ∈ H := by
  simpa using rep_mem (1 : HeckeCoset Δ H H)

end HeckeCoset

namespace DoubleCoset

/-- The decomposition quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)`, indexing the left cosets of `Γ₂` inside
the double coset `Γ₁gΓ₂`; see `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`. -/
abbrev DecompQuotient (Γ₁ Γ₂ : Subgroup G) (g : G) :=
  Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁

instance (Γ₁ Γ₂ : Subgroup G) (g : G) : Nonempty (DecompQuotient Γ₁ Γ₂ g) :=
  ⟨QuotientGroup.mk 1⟩

/-- The left cosets `σᵢ g Γ₂` of the decomposition of `Γ₁gΓ₂` are pairwise distinct: the map
`i ↦ σᵢ g Γ₂` into `G ⧸ Γ₂` is injective. -/
lemma mk_out_mul_injective (Γ₁ Γ₂ : Subgroup G) (g : G) :
    Function.Injective fun i : DecompQuotient Γ₁ Γ₂ g ↦ (((i.out : G) * g : G) : G ⧸ Γ₂) := by
  intro i j hij
  simp only [QuotientGroup.eq] at hij
  rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv]
  simpa [mul_assoc] using hij

open scoped Pointwise in
/-- The conjugation criterion for the stabilizer subgroup indexing `DecompQuotient`: an
element of the stabilizer conjugates into `H` under `g`. -/
lemma conj_mem_of_stabilizer {H : Subgroup G} (g : G)
    (n : (ConjAct.toConjAct g • H).subgroupOf H) : g⁻¹ * (n : G) * g ∈ H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

end DoubleCoset

namespace IsHeckeTriple

/-- Every member of the double coset `H₁gH₂` of an element of `Δ` lies in `Δ`. -/
theorem mem_of_mem_doubleCoset {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    {g x : G} (hg : g ∈ Δ) (hx : x ∈ doubleCoset g (H₁ : Set G) H₂) : x ∈ Δ := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hx
  exact mul_mem (mul_mem (mem_of_mem_left H₂ hh₁) hg) (mem_of_mem_right H₁ hh₂)

/-- For a Hecke triple, the decomposition quotient of any `g : Δ` is finite: `Δ`
commensurates `H₂`, which is commensurable with `H₁`. -/
noncomputable instance {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    (g : Δ) : Fintype (DecompQuotient H₁ H₂ (g : G)) :=
  Subgroup.fintypeOfIndexNeZero (IsHeckeTriple.commensurable_conjAct_right g).1

end IsHeckeTriple

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

section SingleWrapper

variable (R : Type*) [Zero R]

/-- A basis element of the Hecke coset module: `single R D b` is the formal sum `b • [D]`. As
for `Finsupp` itself, this is the type-correct way to produce elements of
`HeckeCosetModule Δ H₁ H₂ R`. Only `[Zero R]` is assumed, so consumers with coefficient
assumptions below `Semiring` (the left-coset scalar operations) can use it. -/
noncomputable def single (D : HeckeCoset Δ H₁ H₂) (b : R) :
    HeckeCosetModule Δ H₁ H₂ R :=
  Finsupp.single D b

/-- `Finsupp.sum_single_index`, as a wrapper-level equation: summing over a basis element
evaluates the summand at its point. -/
lemma sum_single_index {N : Type*} [AddCommMonoid N] {D : HeckeCoset Δ H₁ H₂} {b : R}
    {F : HeckeCoset Δ H₁ H₂ → R → N} (h : F D 0 = 0) : (single R D b).sum F = F D b :=
  Finsupp.sum_single_index h

/-- Evaluating a basis element: `single R D b` is `b` at `D` and `0` elsewhere. -/
@[simp, grind =]
lemma single_apply {D A : HeckeCoset Δ H₁ H₂} {b : R} [Decidable (D = A)] :
    single R D b A = if D = A then b else 0 :=
  Finsupp.single_apply

end SingleWrapper

section SingleAlgebra

variable (R : Type*) [AddCommMonoid R]

/-- `Finsupp.single_zero`, as a wrapper-level equation. -/
@[simp] lemma single_zero (D : HeckeCoset Δ H₁ H₂) : single R D (0 : R) = 0 :=
  Finsupp.single_zero D

/-- Every element is the sum of its basis components. -/
@[simp]
lemma sum_single (f : HeckeCosetModule Δ H₁ H₂ R) : f.sum (single R) = f :=
  Finsupp.sum_single f

/-- `Finsupp.single_add`, as a wrapper-level equation. -/
@[simp]
lemma single_add (D : HeckeCoset Δ H₁ H₂) (b c : R) :
    single R D (b + c) = single R D b + single R D c :=
  Finsupp.single_add D b c

/-- `Finsupp.induction_linear`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R` in
its basis vocabulary `single`, in the same way that `MonoidAlgebra.induction_linear` restates
it for `MonoidAlgebra`: to prove a property of all elements, prove it for `0`, for sums, and
for basis elements. -/
lemma induction_linear {p : HeckeCosetModule Δ H₁ H₂ R → Prop}
    (f : HeckeCosetModule Δ H₁ H₂ R) (h0 : p 0)
    (hadd : ∀ f g : HeckeCosetModule Δ H₁ H₂ R, p f → p g → p (f + g))
    (hsingle : ∀ (D : HeckeCoset Δ H₁ H₂) (b : R), p (single R D b)) : p f :=
  Finsupp.induction_linear f h0 hadd hsingle

end SingleAlgebra

section SingleModule

variable (R : Type*) [Semiring R]

/-- The `R`-module structure of the Hecke coset module, transporting the standard `Finsupp`
module structure to the wrapper type. -/
noncomputable instance instModule : Module R (HeckeCosetModule Δ H₁ H₂ R) :=
  inferInstanceAs (Module R (HeckeCoset Δ H₁ H₂ →₀ R))

/-- Scaling the unit basis element produces the basis element of the scalar. -/
@[simp]
lemma smul_single_one (D : HeckeCoset Δ H₁ H₂) (b : R) : b • single R D 1 = single R D b :=
  Finsupp.smul_single_one D b

end SingleModule

end HeckeCosetModule
