/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.BilinearForm.Properties
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The kernel of the Spin double cover

For a positive-dimensional finite nondegenerate quadratic space over a field where `2` is
invertible, the kernel of the Spin action consists of the two scalar elements. The proof first
shows that an even Clifford element commuting with every generating vector is scalar, using
contraction and the exterior-algebra basis. Unitarity then restricts the scalar to `1` or `-1`.

## Main results

* `TauCeti.CliffordAlgebra.mem_ker_spinToSpecialOrthogonal_iff`: a Spin element is in the kernel
exactly when it is `1` or the canonical scalar `-1`.
* `TauCeti.CliffordAlgebra.card_ker_spinToSpecialOrthogonal`: the kernel of the Spin action on
the special orthogonal group has cardinality two.

## References

This completes Layer 2's kernel target, `card_ker_spinToSpecialOrthogonal`, in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`. See H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra

namespace TauCeti.CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

private theorem two_smul_contractLeft_associated [Invertible (2 : R)]
    (v : M) (x : CliffordAlgebra Q) :
    (2 : R) • contractLeft (Q.associated v) x =
      ι Q v * x - involute x * ι Q v := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [Algebra.commutes]
  | add x y hx hy =>
      rw [map_add, smul_add, hx, hy, map_add, mul_add, add_mul]
      abel
  | ι_mul a x hx =>
      rw [contractLeft_ι_mul, smul_sub, smul_smul, ← mul_smul_comm, hx, map_mul, involute_ι]
      simp only [neg_mul, sub_neg_eq_add]
      have hpolar := LinearMap.congr_fun (LinearMap.congr_fun
        (QuadraticMap.two_nsmul_associated R Q) v) x
      simp only [LinearMap.smul_apply, nsmul_eq_mul, QuadraticMap.polarBilin_apply_apply] at hpolar
      have hpolar' : (2 : R) * Q.associated v x =
          QuadraticMap.polar (⇑Q) v x := by
        simpa only [Nat.cast_ofNat] using hpolar
      rw [hpolar']
      rw [Algebra.smul_def, ← ι_mul_ι_add_swap]
      noncomm_ring

private theorem contractLeft_associated_eq_zero_of_commute_of_mem_even
    [Invertible (2 : R)] {x : CliffordAlgebra Q} (hx_even : x ∈ even Q)
    (hx_comm : ∀ v : M, Commute x (ι Q v)) (v : M) :
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
  -- Expose the singleton index hidden by the ordered powerset basis wrapper.
  change ExteriorAlgebra.ι R
    (b (Set.powersetCard.ofFinEmbEquiv.symm a 0)) = ExteriorAlgebra.ι R (b i)
  rw [heq]

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

section Scalar

variable {K : Type u} [Field K] [Module K M] [FiniteDimensional K M]
  (Q : QuadraticForm K M) [Invertible (2 : K)]

/-- A Clifford element annihilated by every left contraction is a scalar. -/
theorem exists_eq_algebraMap_of_contractLeft_eq_zero (x : CliffordAlgebra Q)
    (hx : ∀ d : Module.Dual K M, contractLeft d x = 0) :
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
  simpa [y, r] using eq_algebraMap_of_all_contractLeft_eq_zero b y hycontract

/-- An even Clifford element that commutes with every generating vector is a scalar. -/
theorem exists_eq_algebraMap_of_mem_even_of_commute
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) (hx_even : x ∈ even Q)
    (hx_comm : ∀ v : M, Commute x (ι Q v)) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hB : B.Nondegenerate := by
    simpa only [B] using QuadraticMap.nondegenerate_associated_iff.mpr hQ
  apply exists_eq_algebraMap_of_contractLeft_eq_zero Q x
  intro d
  obtain ⟨v, rfl⟩ := (B.toDual hB).surjective d
  rw [show B.toDual hB v = Q.associated v from
    LinearMap.ext fun w ↦ (LinearMap.BilinForm.toDual_def hB).trans (by rfl)]
  exact contractLeft_associated_eq_zero_of_commute_of_mem_even Q hx_even hx_comm v

omit [FiniteDimensional K M] in
private theorem commute_ι_of_mem_ker_spinToOrthogonal
    (x : spinGroup Q) (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) (v : M) :
    Commute (x : CliffordAlgebra Q) (ι Q v) := by
  rw [MonoidHom.mem_ker] at hx
  have hfix : spinVectorAction Q x v = v := by
    have h := congrArg
      (fun g : QuadraticMap.orthogonalGroup Q => ((g : M ≃ₗ[K] M) v)) hx
    rw [coe_spinToOrthogonal_apply] at h
    simpa using h
  have hconj :
      (x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q) = ι Q v := by
    rw [← ι_spinVectorAction_apply Q x v, hfix]
  rw [commute_iff_eq]
  calc
    (x : CliffordAlgebra Q) * ι Q v =
        ((x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q)) * x := by
          rw [mul_assoc, spinGroup.star_mul_self_of_mem x.2, mul_one]
    _ = ι Q v * x := by rw [hconj]

private theorem exists_coe_eq_algebraMap_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    ∃ r : K, (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r := by
  exact exists_eq_algebraMap_of_mem_even_of_commute Q hQ x (spinGroup.mem_even x.2)
    (commute_ι_of_mem_ker_spinToOrthogonal Q x hx)

private theorem coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  obtain ⟨r, hr⟩ := exists_coe_eq_algebraMap_of_mem_ker_spinToOrthogonal Q hQ x hx
  have hr_sq : r * r = 1 := by
    apply algebraMap_injective Q
    simpa only [hr, star_algebraMap, map_mul, map_one] using
      spinGroup.star_mul_self_of_mem x.2
  rcases (mul_self_eq_one_iff.mp hr_sq) with rfl | rfl
  · left
    simpa using hr
  · right
    simpa using hr

end Scalar

section NegOne

/-- A Spin element whose Clifford value is `-1` lies in the kernel of the Spin action. -/
theorem mem_ker_spinToSpecialOrthogonal_of_coe_eq_neg_one
    [Invertible (2 : R)] (x : spinGroup Q) (h : (x : CliffordAlgebra Q) = -1) :
    x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_spinToSpecialOrthogonal_apply]
  apply ι_injective Q
  rw [ι_spinVectorAction_apply]
  simp [h]

namespace spinGroup

variable {K : Type u} [Field K] [Module K M]

/-- The scalar `-1` lies in the kernel of the Spin action. -/
theorem negOne_mem_ker_spinToSpecialOrthogonal
    (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q ≠ 0) :
    negOne Q hQ ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) :=
  mem_ker_spinToSpecialOrthogonal_of_coe_eq_neg_one Q _ (coe_negOne Q hQ)

/-- The scalar `-1` acts trivially on the quadratic space. -/
@[simp]
theorem spinToSpecialOrthogonal_negOne
    (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q ≠ 0) :
    spinToSpecialOrthogonal Q (negOne Q hQ) = 1 :=
  MonoidHom.mem_ker.mp (negOne_mem_ker_spinToSpecialOrthogonal Q hQ)

end spinGroup

end NegOne

section Kernel

variable {K : Type u} [Field K] [Module K M]

theorem nondegenerate_ne_zero [Nontrivial M]
    (Q : QuadraticForm K M) (hQ : Q.Nondegenerate) : Q ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have hm : v ∈ Q.radical := by
    rw [hzero, QuadraticMap.mem_radical_iff']
    simp
  rwa [hQ.radical_eq_bot, Submodule.mem_bot] at hm

variable [FiniteDimensional K M]

/-- A Spin element lies in the kernel of the special-orthogonal action exactly when it is
the scalar `1` or the canonical scalar `-1`. -/
theorem mem_ker_spinToSpecialOrthogonal_iff
    (Q : QuadraticForm K M) [Invertible (2 : K)] [Nontrivial M]
    (hQ : Q.Nondegenerate)
    (x : spinGroup Q) :
    x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) ↔
      x = 1 ∨ x = spinGroup.negOne Q (nondegenerate_ne_zero Q hQ) := by
  constructor
  · intro hx
    rcases coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal Q hQ x
      (ker_spinToSpecialOrthogonal Q ▸ hx) with h | h
    · left
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      simpa using h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q (nondegenerate_ne_zero Q hQ)

/-- The kernel of the Spin action on a positive-dimensional finite nondegenerate quadratic space
over a field where `2` is invertible has cardinality two. -/
theorem card_ker_spinToSpecialOrthogonal (hM : 0 < Module.finrank K M)
    (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q.Nondegenerate) :
    Nat.card (MonoidHom.ker (spinToSpecialOrthogonal Q)) = 2 := by
  let _ : Nontrivial M := Module.nontrivial_of_finrank_pos hM
  rw [Nat.card_eq_two_iff' (1 : MonoidHom.ker (spinToSpecialOrthogonal Q))]
  have hQ0 := nondegenerate_ne_zero Q hQ
  let z : MonoidHom.ker (spinToSpecialOrthogonal Q) :=
    ⟨spinGroup.negOne Q hQ0, spinGroup.negOne_mem_ker_spinToSpecialOrthogonal Q hQ0⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    exact spinGroup.negOne_ne_one Q hQ0 (congrArg Subtype.val hz)
  · intro y hy
    apply Subtype.ext
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ y).mp y.2 with h | h
    · exfalso
      apply hy
      apply Subtype.ext
      exact h
    · simpa [z] using h

end Kernel

end TauCeti.CliffordAlgebra
