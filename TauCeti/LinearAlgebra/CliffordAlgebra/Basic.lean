/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.NoncommRing

/-!
# Basic Clifford algebra API

This file records general scalar properties of a Clifford algebra obtained from Mathlib's
linear equivalence with the exterior algebra.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti.CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- `CliffordAlgebra.equivExterior` sends a scalar to the corresponding scalar of the exterior
algebra. -/
theorem equivExterior_algebraMap (Q : QuadraticForm R M) [Invertible (2 : R)] (r : R) :
    equivExterior Q (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (ExteriorAlgebra R M) r :=
  changeForm_algebraMap changeForm.associated_neg_proof r

/-- **The scalars of a Clifford algebra are a faithful copy of `R`.** -/
theorem algebraMap_injective (Q : QuadraticForm R M) [Invertible (2 : R)] :
    Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s hrs
  have h := congrArg (equivExterior Q) hrs
  rwa [equivExterior_algebraMap, equivExterior_algebraMap,
    ExteriorAlgebra.algebraMap_inj M] at h

/-- The scalar action on a Clifford algebra is faithful when `2` is invertible. With this
instance, Mathlib's scalar `iff` lemmas apply directly. -/
instance faithfulSMul (Q : QuadraticForm R M) [Invertible (2 : R)] :
    FaithfulSMul R (CliffordAlgebra Q) :=
  (faithfulSMul_iff_algebraMap_injective R (CliffordAlgebra Q)).2 (algebraMap_injective Q)

private theorem two_smul_contractLeft_associated [Invertible (2 : R)]
    (Q : QuadraticForm R M) (v : M) (x : CliffordAlgebra Q) :
    (2 : R) • contractLeft (Q.associated v) x =
      ι Q v * x - involute x * ι Q v := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.commutes]
  | add x y hx hy =>
      rw [map_add, smul_add, hx, hy, map_add, mul_add, add_mul]
      abel
  | ι_mul a x hx =>
      rw [contractLeft_ι_mul, smul_sub, smul_smul, ← mul_smul_comm, hx, map_mul, involute_ι]
      simp only [neg_mul, sub_neg_eq_add]
      have hpolar := LinearMap.congr_fun (LinearMap.congr_fun
        (QuadraticMap.two_nsmul_associated R Q) v) x
      simp only [LinearMap.smul_apply, nsmul_eq_mul, QuadraticMap.polarBilin_apply_apply] at hpolar
      have hpolar' : (2 : R) * Q.associated v x = QuadraticMap.polar (⇑Q) v x := by
        simpa only [Nat.cast_ofNat] using hpolar
      rw [hpolar', Algebra.smul_def, ← ι_mul_ι_add_swap]
      noncomm_ring

private theorem contractLeft_associated_eq_zero_of_commute_of_mem_even
    [Invertible (2 : R)] (Q : QuadraticForm R M) {x : CliffordAlgebra Q}
    (hx_even : x ∈ even Q) (hx_comm : ∀ v : M, Commute x (ι Q v)) (v : M) :
    contractLeft (Q.associated v) x = 0 := by
  apply (isUnit_of_invertible (2 : R)).smul_eq_zero.mp
  rw [two_smul_contractLeft_associated Q, involute_eq_of_mem_even hx_even,
    (hx_comm v).eq, sub_self]

section Exterior

private theorem contractLeft_ιMulti_eq_zero {n : ℕ}
    (d : Module.Dual R M) (v : Fin n → M) (h : ∀ i, d (v i) = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R n v) = 0 := by
  induction n with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact contractLeft_one (Q := (0 : QuadraticForm R M)) d
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, h 0, zero_smul,
        ih (Matrix.vecTail v) (fun i => h i.succ), mul_zero, sub_zero]

private theorem contractLeft_basis_eq_zero_of_not_mem {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply]
  apply contractLeft_ιMulti_eq_zero
  intro j
  simp only [Function.comp_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · exfalso
    apply hi
    rw [← h]
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.prodEquiv.symm s).2
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2 j)).mp
      ⟨j, rfl⟩
    exact hj
  · rfl

private noncomputable def exteriorCoordProj {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i))).comp
    (contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i))

private theorem exteriorCoordProj_basis_of_not_mem {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    exteriorCoordProj b i (b.ExteriorAlgebra s) = 0 := by
  rw [exteriorCoordProj, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    contractLeft_basis_eq_zero_of_not_mem b i s hi, mul_zero]

private theorem basis_exteriorAlgebra_singleton_eq_ι {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  let a : Set.powersetCard (Fin n) 1 :=
    Set.powersetCard.ofCard (s := {i}) (Finset.card_singleton i)
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  rw [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    a (Set.powersetCard.ofFinEmbEquiv.symm a 0)).mp ⟨0, rfl⟩
  have hj' : Set.powersetCard.ofFinEmbEquiv.symm a 0 ∈ ({i} : Finset (Fin n)) := hj
  have heq : Set.powersetCard.ofFinEmbEquiv.symm a 0 = i := Finset.eq_of_mem_singleton hj'
  exact congrArg (fun j ↦ ExteriorAlgebra.ι R (b j)) heq

private theorem exteriorCoordProj_basis_of_mem {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s) :
    exteriorCoordProj b i (b.ExteriorAlgebra s) = b.ExteriorAlgebra s := by
  let a : Set.powersetCard (Fin n) 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard (Fin n) (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint a.val t.val := by simp [a, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard (Fin n) (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, a, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b a t hdisj
  rw [hunion] at hprod
  simp only [a, t, Set.powersetCard.val_ofCard] at hprod
  have hfixed : exteriorCoordProj b i
      (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
      b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) := by
    rw [exteriorCoordProj, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      basis_exteriorAlgebra_singleton_eq_ι]
    rw [contractLeft_ι_mul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    rw [contractLeft_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
      mul_zero, sub_zero]
    simp
  rw [hprod] at hfixed
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    (Set.powersetCard.permOfDisjoint hdisj)) with hsign | hsign <;>
    rw [hsign] at hfixed <;> simpa using hfixed

private theorem exteriorCoordProj_repr_of_mem {n : ℕ}
    (b : Module.Basis (Fin n) R M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (x : ExteriorAlgebra R M) :
    b.ExteriorAlgebra.repr (exteriorCoordProj b i x) s =
      b.ExteriorAlgebra.repr x s := by
  have hmap : (b.ExteriorAlgebra.coord s).comp (exteriorCoordProj b i) =
      b.ExteriorAlgebra.coord s := by
    apply b.ExteriorAlgebra.ext
    intro t
    by_cases hit : i ∈ t
    · rw [LinearMap.comp_apply, exteriorCoordProj_basis_of_mem b i t hit]
    · rw [LinearMap.comp_apply, exteriorCoordProj_basis_of_not_mem b i t hit, map_zero]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hts
      · subst t
        exact (hit hi).elim
      · rfl
  exact LinearMap.congr_fun hmap x

private theorem eq_algebraMap_of_all_contractLeft_eq_zero {n : ℕ}
    (b : Module.Basis (Fin n) R M) (x : ExteriorAlgebra R M)
    (hx : ∀ d : Module.Dual R M,
      contractLeft (Q := (0 : QuadraticForm R M)) d x = 0) :
    x = algebraMap R (ExteriorAlgebra R M) (b.ExteriorAlgebra.repr x ∅) := by
  have hbempty : b.ExteriorAlgebra (∅ : Finset (Fin n)) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  apply b.ExteriorAlgebra.repr.injective
  ext s
  rw [Algebra.algebraMap_eq_smul_one, ← hbempty, map_smul,
    Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_apply]
  by_cases hs : s = ∅
  · subst s
    simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hproject : exteriorCoordProj b i x = 0 := by
      rw [exteriorCoordProj, LinearMap.comp_apply, hx, LinearMap.mulLeft_apply, mul_zero]
    have hcoord := exteriorCoordProj_repr_of_mem b i s hi x
    rw [hproject, map_zero, Finsupp.zero_apply] at hcoord
    rw [← hcoord]
    simp [Ne.symm hs]

end Exterior

variable {K : Type u} [Field K] [Module K M] [FiniteDimensional K M]
  [Invertible (2 : K)]

/-- A Clifford element annihilated by every left contraction is a scalar. -/
theorem exists_eq_algebraMap_of_contractLeft_eq_zero (Q : QuadraticForm K M)
    (x : CliffordAlgebra Q) (hx : ∀ d : Module.Dual K M, contractLeft d x = 0) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  let b := Module.finBasis K M
  let y : ExteriorAlgebra K M := equivExterior Q x
  have hycontract (d : Module.Dual K M) :
      contractLeft (Q := (0 : QuadraticForm K M)) d y = 0 := by
    dsimp only [y, equivExterior, changeFormEquiv_apply]
    rw [changeFormEquiv_apply]
    rw [← changeForm_contractLeft changeForm.associated_neg_proof d x, hx, map_zero]
  let r := b.ExteriorAlgebra.repr y ∅
  refine ⟨r, ?_⟩
  apply (equivExterior Q).injective
  simpa only [y, r, equivExterior_algebraMap] using
    eq_algebraMap_of_all_contractLeft_eq_zero b y hycontract

/-- An even Clifford element that commutes with every generating vector is a scalar. -/
theorem exists_eq_algebraMap_of_mem_even_of_commute
    (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q)
    (hx_even : x ∈ even Q) (hx_comm : ∀ v : M, Commute x (ι Q v)) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hB : B.Nondegenerate := by
    simpa only [B] using QuadraticMap.nondegenerate_associated_iff.mpr hQ
  apply exists_eq_algebraMap_of_contractLeft_eq_zero Q x
  intro d
  obtain ⟨v, rfl⟩ := (B.toDual hB).surjective d
  have htoDual : B.toDual hB v = Q.associated v :=
    LinearMap.ext fun w ↦ (LinearMap.BilinForm.toDual_def hB).trans (by rfl)
  rw [htoDual]
  exact contractLeft_associated_eq_zero_of_commute_of_mem_even Q hx_even hx_comm v

end TauCeti.CliffordAlgebra
