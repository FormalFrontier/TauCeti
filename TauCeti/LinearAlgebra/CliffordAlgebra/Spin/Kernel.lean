/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The kernel of the Spin double cover

For a positive-dimensional finite nondegenerate quadratic space over a field where `2` is
invertible, the kernel of the Spin action consists of the two scalar elements. The proof first
shows that an even Clifford element commuting with every generating vector is scalar, using
contraction and the exterior-algebra basis. Unitarity then restricts the scalar to `1` or `-1`.

## Main result

* `TauCeti.CliffordAlgebra.card_ker_spinToSpecialOrthogonal`: the kernel of the Spin action on
the special orthogonal group has cardinality two.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra

namespace TauCeti.CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private theorem two_smul_contractLeft_associated (v : M) (x : CliffordAlgebra Q) :
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
      have hpolar' : (2 : R) * QuadraticMap.associatedHom R Q v x =
          QuadraticMap.polar (⇑Q) v x := by
        simpa only [Nat.cast_ofNat] using hpolar
      -- Expose scalar multiplication in the induction step before applying the polar identity.
      change ((2 : R) * QuadraticMap.associatedHom R Q v x) • a - _ = _
      rw [hpolar']
      rw [Algebra.smul_def, ← ι_mul_ι_add_swap]
      noncomm_ring

private theorem contractLeft_associated_eq_zero_of_commute_of_mem_even
    {x : CliffordAlgebra Q} (hx_even : x ∈ even Q)
    (hx_comm : ∀ v : M, Commute x (ι Q v)) (v : M) :
    contractLeft (Q.associated v) x = 0 := by
  apply (isUnit_of_invertible (2 : R)).smul_eq_zero.mp
  rw [two_smul_contractLeft_associated Q, involute_eq_of_mem_even hx_even,
    (hx_comm v).eq, sub_self]

section Exterior

variable {K : Type u} [Field K] [Module K M]

private theorem contractLeft_ιMulti_eq_zero {n : ℕ}
    (d : Module.Dual K M) (v : Fin n → M) (h : ∀ i, d (v i) = 0) :
    contractLeft (Q := (0 : QuadraticForm K M)) d (ExteriorAlgebra.ιMulti K n v) = 0 := by
  induction n with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact contractLeft_one (Q := (0 : QuadraticForm K M)) d
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, h 0, zero_smul,
        ih (Matrix.vecTail v) (fun i => h i.succ), mul_zero, sub_zero]

private theorem contractLeft_basis_eq_zero_of_not_mem {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm K M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
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
    -- Unpack membership in the ordered finite embedding used by the basis constructor.
    change Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.prodEquiv.symm s).2 j ∈ s at hj
    exact hj
  · rfl

private noncomputable def coordinateProjector {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) :
    ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  (LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i))).comp
    (contractLeft (Q := (0 : QuadraticForm K M)) (b.coord i))

private theorem coordinateProjector_basis_of_not_mem {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∉ s) :
    coordinateProjector b i (b.ExteriorAlgebra s) = 0 := by
  rw [coordinateProjector, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    contractLeft_basis_eq_zero_of_not_mem b i s hi, mul_zero]

private theorem basis_singleton {n : ℕ} (b : Module.Basis (Fin n) K M) (i : Fin n) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι K (b i) := by
  let a : Set.powersetCard (Fin n) 1 :=
    Set.powersetCard.ofCard (s := {i}) (Finset.card_singleton i)
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  -- Expose the one-vector representative hidden by the exterior basis constructor.
  change ExteriorAlgebra.ιMulti K 1 (b ∘ Set.powersetCard.ofFinEmbEquiv.symm a) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    a (Set.powersetCard.ofFinEmbEquiv.symm a 0)).mp ⟨0, rfl⟩
  -- Unpack the singleton's ordered finite embedding at its unique index.
  change Set.powersetCard.ofFinEmbEquiv.symm a 0 ∈ ({i} : Finset (Fin n)) at hj
  have heq : Set.powersetCard.ofFinEmbEquiv.symm a 0 = i := Finset.eq_of_mem_singleton hj
  simp only [Function.comp_apply, heq]

private theorem coordinateProjector_basis_of_mem {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s) :
    coordinateProjector b i (b.ExteriorAlgebra s) = b.ExteriorAlgebra s := by
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
  -- Reveal the scalar sign in the exterior-basis multiplication theorem.
  change b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
    _ • b.ExteriorAlgebra s at hprod
  have hfixed : coordinateProjector b i
      (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
      b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) := by
    rw [coordinateProjector, LinearMap.comp_apply, LinearMap.mulLeft_apply, basis_singleton]
    rw [contractLeft_ι_mul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    rw [contractLeft_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
      mul_zero, sub_zero]
    simp
  rw [hprod] at hfixed
  rcases Int.units_eq_one_or (Equiv.Perm.sign
    (Set.powersetCard.permOfDisjoint hdisj)) with hsign | hsign <;>
    rw [hsign] at hfixed <;> simpa using hfixed

private theorem coordinateProjector_repr_of_mem {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) (s : Finset (Fin n)) (hi : i ∈ s)
    (x : ExteriorAlgebra K M) :
    b.ExteriorAlgebra.repr (coordinateProjector b i x) s =
      b.ExteriorAlgebra.repr x s := by
  have hmap : (b.ExteriorAlgebra.coord s).comp (coordinateProjector b i) =
      b.ExteriorAlgebra.coord s := by
    apply b.ExteriorAlgebra.ext
    intro t
    by_cases hit : i ∈ t
    · rw [LinearMap.comp_apply, coordinateProjector_basis_of_mem b i t hit]
    · rw [LinearMap.comp_apply, coordinateProjector_basis_of_not_mem b i t hit, map_zero]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hts
      · subst t
        exact (hit hi).elim
      · rfl
  exact LinearMap.congr_fun hmap x

private theorem eq_algebraMap_of_all_contractLeft_eq_zero {n : ℕ}
    (b : Module.Basis (Fin n) K M) (x : ExteriorAlgebra K M)
    (hx : ∀ d : Module.Dual K M,
      contractLeft (Q := (0 : QuadraticForm K M)) d x = 0) :
    x = algebraMap K (ExteriorAlgebra K M) (b.ExteriorAlgebra.repr x ∅) := by
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
    have hproject : coordinateProjector b i x = 0 := by
      rw [coordinateProjector, LinearMap.comp_apply, hx, LinearMap.mulLeft_apply, mul_zero]
    have hcoord := coordinateProjector_repr_of_mem b i s hi x
    rw [hproject, map_zero, Finsupp.zero_apply] at hcoord
    rw [← hcoord]
    simp [Ne.symm hs]

end Exterior

section Scalar

variable {K : Type u} [Field K] [Module K M] [FiniteDimensional K M]
  (Q : QuadraticForm K M) [Invertible (2 : K)]

private theorem eq_algebraMap_of_contractLeft_eq_zero (x : CliffordAlgebra Q)
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

private theorem eq_algebraMap_of_mem_even_of_commute
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) (hx_even : x ∈ even Q)
    (hx_comm : ∀ v : M, Commute x (ι Q v)) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hB : B.Nondegenerate := by
    simpa only [B] using QuadraticMap.nondegenerate_associated_iff.mpr hQ
  apply eq_algebraMap_of_contractLeft_eq_zero Q x
  intro d
  obtain ⟨v, rfl⟩ := (B.toDual hB).surjective d
  -- Unfold the local bilinear-form abbreviation and its `toDual` application.
  change contractLeft (B v) x = 0
  change contractLeft (Q.associated v) x = 0
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
  rw [Commute]
  calc
    (x : CliffordAlgebra Q) * ι Q v =
        ((x : CliffordAlgebra Q) * ι Q v * star (x : CliffordAlgebra Q)) * x := by
          rw [mul_assoc, spinGroup.star_mul_self_of_mem x.2, mul_one]
    _ = ι Q v * x := by rw [hconj]

private theorem coe_eq_algebraMap_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    ∃ r : K, (x : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) r := by
  exact eq_algebraMap_of_mem_even_of_commute Q hQ x (spinGroup.mem_even x.2)
    (commute_ι_of_mem_ker_spinToOrthogonal Q x hx)

private theorem coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal
    (hQ : Q.Nondegenerate) (x : spinGroup Q)
    (hx : x ∈ MonoidHom.ker (spinToOrthogonal Q)) :
    (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  obtain ⟨r, hr⟩ := coe_eq_algebraMap_of_mem_ker_spinToOrthogonal Q hQ x hx
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

variable {K : Type u} [Field K] [Module K M]

/-- The scalar `-1` belongs to the Spin group of a nontrivial
nondegenerate quadratic space. -/
theorem neg_one_mem_spinGroup (Q : QuadraticForm K M) [Invertible (2 : K)]
    [Nontrivial M] (hQ : Q.Nondegenerate) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  let B : LinearMap.BilinForm K M := QuadraticMap.associated Q
  have hB : B.Nondegenerate := by
    simpa only [B] using QuadraticMap.nondegenerate_associated_iff.mpr hQ
  have hBsymm : B.IsSymm :=
    LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB.ne_zero
      (LinearMap.BilinForm.isSymm_iff.mp hBsymm)
  apply neg_one_mem_spinGroup_of_isUnit Q v
  rw [isUnit_iff_ne_zero]
  rwa [QuadraticMap.associated_eq_self_apply] at hv

/-- The scalar `-1` as an element of the Spin group of a nontrivial
nondegenerate quadratic space. -/
def negOneSpin (Q : QuadraticForm K M) [Invertible (2 : K)]
    [Nontrivial M] (hQ : Q.Nondegenerate) : spinGroup Q :=
  ⟨-1, neg_one_mem_spinGroup Q hQ⟩

/-- The underlying Clifford element of `negOneSpin` is the scalar `-1`. -/
@[simp]
theorem coe_negOneSpin (Q : QuadraticForm K M) [Invertible (2 : K)]
    [Nontrivial M] (hQ : Q.Nondegenerate) :
    (negOneSpin Q hQ : CliffordAlgebra Q) = -1 :=
  (rfl)

private theorem mem_ker_spinToOrthogonal_of_mem_ker_spinToSpecialOrthogonal
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    (x : spinGroup Q) (hx : x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q)) :
    x ∈ MonoidHom.ker (spinToOrthogonal Q) := by
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  have hm := congrArg
    (fun g : QuadraticMap.specialOrthogonalGroup Q => ((g : M ≃ₗ[K] M) m)) hx
  simpa using hm

/-- The scalar `-1` lies in the kernel of the Spin action. -/
@[simp high]
theorem negOneSpin_mem_ker_spinToSpecialOrthogonal
    (Q : QuadraticForm K M) [Invertible (2 : K)]
    [Nontrivial M] (hQ : Q.Nondegenerate) :
    negOneSpin Q hQ ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro m
  rw [coe_spinToSpecialOrthogonal_apply]
  apply ι_injective Q
  rw [ι_spinVectorAction_apply]
  simp

end NegOne

section Kernel

variable {K : Type u} [Field K] [Module K M] [FiniteDimensional K M]

/-- A Spin element lies in the kernel of the special-orthogonal action exactly when it is
the scalar `1` or the canonical scalar `-1`. -/
theorem mem_ker_spinToSpecialOrthogonal_iff
    (Q : QuadraticForm K M) [Invertible (2 : K)] [Nontrivial M]
    (hQ : Q.Nondegenerate)
    (x : spinGroup Q) :
    x ∈ MonoidHom.ker (spinToSpecialOrthogonal Q) ↔
      x = 1 ∨ x = negOneSpin Q hQ := by
  constructor
  · intro hx
    rcases coe_eq_one_or_eq_neg_one_of_mem_ker_spinToOrthogonal Q hQ x
      (mem_ker_spinToOrthogonal_of_mem_ker_spinToSpecialOrthogonal Q x hx) with h | h
    · left
      apply Subtype.ext
      exact h
    · right
      apply Subtype.ext
      simpa using h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact negOneSpin_mem_ker_spinToSpecialOrthogonal Q hQ

/-- The kernel of the Spin action on a positive-dimensional finite nondegenerate quadratic space
over a field where `2` is invertible has cardinality two. -/
theorem card_ker_spinToSpecialOrthogonal (hM : 0 < Module.finrank K M)
    (Q : QuadraticForm K M) [Invertible (2 : K)] (hQ : Q.Nondegenerate) :
    Nat.card (MonoidHom.ker (spinToSpecialOrthogonal Q)) = 2 := by
  let _ : Nontrivial M := Module.nontrivial_of_finrank_pos hM
  rw [Nat.card_eq_two_iff' (1 : MonoidHom.ker (spinToSpecialOrthogonal Q))]
  let z : MonoidHom.ker (spinToSpecialOrthogonal Q) :=
    ⟨negOneSpin Q hQ, negOneSpin_mem_ker_spinToSpecialOrthogonal Q hQ⟩
  refine ⟨z, ?_, ?_⟩
  · intro hz
    have hcoe := congrArg
      (fun y : MonoidHom.ker (spinToSpecialOrthogonal Q) =>
        ((y : spinGroup Q) : CliffordAlgebra Q)) hz
    have hK : (-1 : K) = 1 := by
      apply algebraMap_injective Q
      simpa [z] using hcoe
    apply Invertible.ne_zero (2 : K)
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 1 - 1 := by rw [hK]
      _ = 0 := sub_self 1
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
