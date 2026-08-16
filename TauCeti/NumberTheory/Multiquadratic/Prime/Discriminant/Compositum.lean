/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Field
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.Multiquadratic.Degree
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence
import Mathlib.Algebra.BigOperators.Option

/-!
# Discriminants of prime-discriminant composita

Let `D i` be distinct prime discriminants, at most one of which is even, and let `root i` be
chosen square roots of their radicands in a number field. This file computes the absolute value of
the discriminant of their compositum:

`|disc ℚ(root i : i)| = ∏ i, |D i| ^ 2 ^ (n - 1)`.

The proof adjoins one root at a time. Distinct prime discriminants in the family are coprime, so
Mathlib's discriminant formula for the compositum of linearly disjoint number fields applies at
each step. This formula is the finite-place input to the genus-field construction: a rational
prime belonging to one prime-discriminant factor cannot ramify in the compositum of all the other
factors.

The discriminant formula for a compositum is
`NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` from Mathlib. The
prime-discriminant description of genus fields is classical; see D. A. Cox, *Primes of the Form
x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main result

* `TauCeti.Multiquadratic.natAbs_discr_adjoin_range_primeDiscriminantRadicands`: the absolute
  discriminant of a compositum of distinct prime-discriminant quadratic fields.
-/

public section

open IntermediateField
open scoped NumberField

namespace TauCeti.Multiquadratic

universe u v

/-- **Discriminant of a prime-discriminant compositum.** Let `D : ι → ℤ` be an injective
family of prime discriminants containing at most one even member, and let `root i` square to the
radicand attached to `D i`. If `n = |\u03b9|`, then the compositum of these roots has absolute
discriminant `∏ i, |D i| ^ 2 ^ (n - 1)`.

For the empty family both sides are one. For a singleton this recovers that the quadratic field
attached to a prime discriminant `D` has discriminant `D`. -/
theorem natAbs_discr_adjoin_range_primeDiscriminantRadicands
    {ι : Type u} [Fintype ι] {L : Type v} [Field L] [NumberField L]
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
      IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
  (hroot : ∀ i, root i ^ 2 =
      algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ))) :
    (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
      ∏ i, (D i).natAbs ^ (2 ^ (Fintype.card ι - 1)) := by
  classical
  refine (Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      ∀ {L : Type v} [Field L] [NumberField L]
        (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
        (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
          IsEvenPrimeDiscriminant (D j) → D i = D j)
        (root : ι → L),
        (∀ i, root i ^ 2 =
          algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ))) →
        (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
          ∏ i, (D i).natAbs ^ (2 ^ (Fintype.card ι - 1)))
    ?_ ?_ ?_ ι) D hD hinj heven root hroot
  · intro α β _ e ih
    exact by
      intro L _ _ D hD hinj heven root hroot
      let _ := Fintype.ofEquiv β e.symm
      have h := ih (L := L) (D := D ∘ e) (fun i ↦ hD (e i)) (hinj.comp e.injective)
        (fun i j hi hj ↦ heven (e i) (e j) hi hj) (root ∘ e)
        (fun i ↦ hroot (e i))
      rw [EquivLike.range_comp root e, Fintype.card_congr e] at h
      calc
        (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
            ∏ i : α, (D (e i)).natAbs ^ (2 ^ (Fintype.card β - 1)) := by
          simpa only [Function.comp_apply] using h
        _ = ∏ i : β, (D i).natAbs ^ (2 ^ (Fintype.card β - 1)) :=
          Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  · exact by
      intro L _ _ D _ _ _ root _
      have hdisc := NumberField.discr_eq_discr_of_algEquiv _ (botEquiv ℚ L)
      have hrange : Set.range root = ∅ := by
        ext x
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, _⟩
        exact PEmpty.elim i
      rw [hrange, adjoin_empty, hdisc, Rat.numberField_discr]
      simp
  · intro α _ ih
    exact by
      intro L _ _ D hD hinj heven root hroot
      let M : IntermediateField ℚ L := adjoin ℚ (Set.range root)
      let rootM : Option α → M := gen (K := ℚ) root
      let K₁ : IntermediateField ℚ M := adjoin ℚ (Set.range (rootM ∘ some))
      let K₂ : IntermediateField ℚ M := adjoin ℚ {rootM none}
      have hrootM (i : Option α) : rootM i ^ 2 =
          algebraMap ℚ M (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) := by
        exact gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) hroot i
      have hdisc₁ : (NumberField.discr K₁).natAbs =
          ∏ i : α, (D (some i)).natAbs ^ (2 ^ (Fintype.card α - 1)) := by
        exact ih (L := M) (D := D ∘ some) (fun i ↦ hD (some i))
          (hinj.comp (Option.some_injective α))
          (fun i j hi hj ↦ heven (some i) (some j) hi hj)
          (rootM ∘ some) (fun i ↦ hrootM (some i))
      have hrootM_int (i : Option α) : rootM i ^ 2 =
          algebraMap ℤ M (primeDiscriminantRadicand (D i)) := by
        rw [hrootM, IsScalarTower.algebraMap_apply ℤ ℚ M]
        norm_num
      have hdisc₂ : NumberField.discr K₂ = D none :=
        discr_adjoin_singleton_eq_primeDiscriminant (hD none) (hrootM_int none)
      have hcoprime_factor (i : α) : IsCoprime (D (some i)) (D none) := by
        have hnot_even : ¬ (IsEvenPrimeDiscriminant (D (some i)) ∧
            IsEvenPrimeDiscriminant (D none)) := by
          rintro ⟨hi, hn⟩
          exact Option.some_ne_none i (hinj (heven (some i) none hi hn))
        have h := isCoprime_discr_adjoin_singleton_of_primeDiscriminant
          (L := M) (hD (some i)) (hD none)
          (fun h ↦ Option.some_ne_none i (hinj h)) hnot_even
          (hrootM_int (some i)) (hrootM_int none)
        simpa only [K₂, discr_adjoin_singleton_eq_primeDiscriminant (hD (some i))
          (hrootM_int (some i)), discr_adjoin_singleton_eq_primeDiscriminant (hD none)
          (hrootM_int none)] using h
      have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
        rw [Int.isCoprime_iff_nat_coprime, hdisc₁, hdisc₂]
        exact Nat.Coprime.prod_left fun i _ ↦
          (Int.isCoprime_iff_nat_coprime.mp (hcoprime_factor i)).pow_left _
      have : IsGalois ℚ K₁ :=
        isGalois (d := fun i : α ↦ ((primeDiscriminantRadicand (D (some i)) : ℤ) : ℚ))
          (root := rootM ∘ some) (fun i ↦ hrootM (some i))
      have hdisjoint : K₁.LinearDisjoint K₂ :=
        NumberField.linearDisjoint_of_isGalois_isCoprime_discr M K₁ K₂ hcoprime
      have htop : K₁ ⊔ K₂ = ⊤ := by
        change adjoin ℚ (Set.range (rootM ∘ some)) ⊔ adjoin ℚ {rootM none} = ⊤
        rw [← adjoin_union]
        have hrange : Set.range (rootM ∘ some) ∪ {rootM none} = Set.range rootM := by
          ext x
          simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Function.comp_apply]
          constructor
          · rintro (⟨i, rfl⟩ | rfl)
            · exact ⟨some i, rfl⟩
            · exact ⟨none, rfl⟩
          · rintro ⟨i, rfl⟩
            cases i with
            | none => exact Or.inr rfl
            | some i => exact Or.inl ⟨i, rfl⟩
        rw [hrange]
        exact adjoin_gen_eq_top
      have hformula := NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
        M K₁ K₂ hdisjoint htop
          (NumberField.isCoprime_differentIdeal_of_isCoprime_discr M hcoprime)
      have hfinrank₁ : Module.finrank ℚ K₁ = 2 ^ Fintype.card α := by
        have h :=
          finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
          (fun i : α ↦ D (some i)) (fun i ↦ hD (some i))
          (hinj.comp (Option.some_injective α))
          (fun i j hi hj ↦ heven (some i) (some j) hi hj)
          (rootM ∘ some) (fun i ↦ hrootM (some i))
        simpa only [K₁, Nat.card_eq_fintype_card] using h
      have hfinrank₂ : Module.finrank ℚ K₂ = 2 := by
        have h :=
          finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
          (fun _ : Unit ↦ D none) (fun _ ↦ hD none) (fun _ _ _ ↦ Subsingleton.elim _ _)
          (fun _ _ _ _ ↦ rfl) (fun _ : Unit ↦ rootM none) (fun _ ↦ hrootM none)
        have hrange : Set.range (fun _ : Unit ↦ rootM none) = {rootM none} := by
          ext x
          simp
        rw [hrange] at h
        simpa only [K₂, Nat.card_unique, pow_one] using h
      rw [hdisc₁, hdisc₂, hfinrank₁, hfinrank₂] at hformula
      have hprod : (Finset.univ.prod (fun i : α ↦
          (D (some i)).natAbs ^ (2 ^ (Fintype.card α - 1)))) ^ 2 =
          Finset.univ.prod (fun i : α ↦
            (D (some i)).natAbs ^ (2 ^ Fintype.card α)) := by
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro i _
        rw [← pow_mul, ← pow_succ]
        congr 2
        exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)
      rw [hprod] at hformula
      simpa only [M, Fintype.card_option, Fintype.prod_option, Function.comp_apply,
        Nat.add_sub_cancel, mul_comm] using hformula

end TauCeti.Multiquadratic
