/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Herbrand quotients of finite cyclic group representations

For a representation `M` of a finite cyclic group, its Herbrand quotient is the quotient of the
orders of `H-hat^0(G, M)` and `H-hat^(-1)(G, M)`. This file first supplies the missing generic
degree `-1` description

`H-hat^(-1)(G, M) = ker(N) / I_G M`,

where `I_G M` is the kernel of the coinvariants quotient. It then defines the Herbrand quotient
directly on Mathlib's Tate-cohomology carrier and proves its two base calculations: it is `1` for
a finite module, and it is `|G|` for the trivial integral representation.

The proofs are adapted to Mathlib's current Tate complex from the corresponding explicit models
and calculations in `ClassFieldTheory/Cohomology/FiniteCyclic/ExplicitTate.lean` and
`ClassFieldTheory/Cohomology/FiniteCyclic/HerbrandQuotient/{Defs,Finite,Trivial}.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `TauCeti.TateCohomology.HNegOneIsoNormKernelQuotient` identifies degree `-1` Tate cohomology
  with the kernel of the norm modulo the augmentation submodule.
* `TauCeti.TateCohomology.herbrandQuotient` is the Herbrand quotient.
* `TauCeti.TateCohomology.herbrandQuotient_of_finite` computes it for a finite module.
* `TauCeti.TateCohomology.herbrandQuotient_trivial_int_eq_card` computes it for trivial integral
  coefficients.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, section 4.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IX, section 4.
-/

public noncomputable section

universe u

open CategoryTheory groupCohomology groupHomology LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

namespace NegOne

variable (M : Rep R G)

/-- The concrete short complex computing degree `-1` Tate cohomology. -/
private def shortComplex : ShortComplex (ModuleCat R) :=
  .mk (d₁₀ M) M.norm.toModuleCatHom (Rep.comp_eq_zero M)

/-- The degree `-1` part of the Tate complex is the augmentation-to-norm short complex. -/
private def isoShortComplex : (tateComplex M).sc (-1) ≅ shortComplex M := by
  have hnorm :
      (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom =
        M.tateNorm ≫ (cochainsIso₀ M).hom := by
    simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (tateComplex M).isoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.isoMk (chainsIso₁ M) (chainsIso₀ M) (cochainsIso₀ M)
      (comp_d₁₀_eq M) hnorm

end NegOne

/-- Degree `-1` Tate cohomology is the kernel of the norm modulo the augmentation submodule,
namely the kernel of the quotient to coinvariants. -/
def HNegOneIsoNormKernelQuotient (M : Rep R G) :
    tateCohomology M (-1) ≅ ModuleCat.of R
      (ker M.ρ.norm ⧸
        (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) := calc
  tateCohomology M (-1) ≅ (NegOne.shortComplex M).homology :=
    ShortComplex.homologyMapIso (NegOne.isoShortComplex M)
  _ ≅ ModuleCat.of R (ker M.ρ.norm ⧸ _) :=
    ShortComplex.moduleCatHomologyIso _
  _ ≅ ModuleCat.of R
      (ker M.ρ.norm ⧸
        (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) := by
    refine (Submodule.Quotient.equiv _ _ (LinearEquiv.refl R _) ?_).toModuleIso
    rw [← range_d₁₀_eq_coinvariantsKer]
    refine Submodule.ext fun ⟨x, hx⟩ ↦ ⟨?_, ?_⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      exact ⟨y, congr(Subtype.val $hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨d₁₀ M y,
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Rep.comp_eq_zero M)) y⟩,
        ⟨_, rfl⟩, rfl⟩

/-- The quotient map from norm-zero representatives to degree `-1` Tate cohomology. -/
def HNegOneπ (M : Rep R G) : ModuleCat.of R (ker M.ρ.norm) ⟶ tateCohomology M (-1) :=
  ModuleCat.ofHom
      (Submodule.mkQ ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm))) ≫
    (HNegOneIsoNormKernelQuotient M).inv

instance (M : Rep R G) : Epi (HNegOneπ M) :=
  have : Epi (ModuleCat.ofHom
      (Submodule.mkQ ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)))) :=
    (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  inferInstanceAs <| Epi (_ ≫ _)

/-- Under the degree `-1` identification, `HNegOneπ` is the quotient map by the augmentation
submodule. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom (M : Rep R G) :
    HNegOneπ M ≫ (HNegOneIsoNormKernelQuotient M).hom =
      ModuleCat.ofHom
        (Submodule.mkQ
          ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm))) := by
  simp [HNegOneπ]

/-- A norm-zero element represents zero in degree `-1` Tate cohomology exactly when it belongs to
the augmentation submodule. -/
@[simp]
theorem HNegOneπ_eq_zero_iff {M : Rep R G} (x : ker M.ρ.norm) :
    HNegOneπ M x = 0 ↔ x ∈
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm) := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← HNegOneπ_comp_HNegOneIsoNormKernelQuotient_hom_apply]
  exact ((HNegOneIsoNormKernelQuotient M).toLinearEquiv.map_eq_zero_iff).symm

/-- Two norm-zero elements represent the same degree `-1` Tate class exactly when their
difference belongs to the augmentation submodule. -/
@[simp]
theorem HNegOneπ_eq_iff {M : Rep R G} (x y : ker M.ρ.norm) :
    HNegOneπ M x = HNegOneπ M y ↔ x - y ∈
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm) := by
  rw [← sub_eq_zero, ← map_sub, HNegOneπ_eq_zero_iff]

/-- The Herbrand quotient, with the usual convention that it is zero if either Tate group is
infinite. The definition makes sense for any finite group; periodicity makes it useful for cyclic
groups. -/
def herbrandQuotient (M : Rep R G) : ℚ :=
  Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1))

/-- The Herbrand quotient vanishes exactly when one of its two defining Tate groups is infinite. -/
theorem herbrandQuotient_eq_zero_iff {M : Rep R G} :
    herbrandQuotient M = 0 ↔
      Infinite (tateCohomology M 0) ∨ Infinite (tateCohomology M (-1)) := by
  simp [herbrandQuotient, Nat.card_eq_zero]

/-- The Herbrand quotient is nonzero exactly when its two defining Tate groups are finite. -/
theorem herbrandQuotient_ne_zero_iff {M : Rep R G} :
    herbrandQuotient M ≠ 0 ↔
      Finite (tateCohomology M 0) ∧ Finite (tateCohomology M (-1)) := by
  simp [herbrandQuotient, Nat.card_eq_zero]

/-- The Herbrand quotient of a finite representation of a finite cyclic group is one. -/
theorem herbrandQuotient_of_finite [IsCyclic G] (M : Rep R G) [Finite M] :
    herbrandQuotient M = 1 := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦
    hgen.choose_spec.ge (Subgroup.mem_top x)
  let D : Module.End R M := M.ρ g - LinearMap.id
  have hinv : M.ρ.invariants = ker D := by
    ext x
    simpa only [D, mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using
      (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x)
  have hcoinv : Representation.Coinvariants.ker M.ρ = range D := by
    simpa only [D] using Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg
  have hnorm_le : range M.ρ.norm ≤ M.ρ.invariants := by
    rintro _ ⟨x, rfl⟩
    exact fun a ↦ M.ρ.self_norm_apply a x
  have hzero :
      Nat.card M.ρ.invariants =
        Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
    calc
      Nat.card M.ρ.invariants =
          Nat.card ((range M.ρ.norm).submoduleOf M.ρ.invariants) *
            Nat.card (M.ρ.invariants ⧸
              (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe hnorm_le).toEquiv,
          ← Nat.card_congr (H0IsoNormQuotient M).toLinearEquiv.toEquiv]
  have hnegone :
      Nat.card (ker M.ρ.norm) =
        Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
    calc
      Nat.card (ker M.ρ.norm) =
          Nat.card ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) *
            Nat.card (ker M.ρ.norm ⧸
              (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe (by
          rw [← range_d₁₀_eq_coinvariantsKer]
          exact LinearMap.range_le_ker_iff.mpr
            (ModuleCat.hom_ext_iff.mp (Rep.comp_eq_zero M)))).toEquiv,
          ← Nat.card_congr (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv]
  have hnorm :
      Nat.card M = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := by
    calc
      Nat.card M = Nat.card (ker M.ρ.norm) * Nat.card (M ⧸ ker M.ρ.norm) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := by
        rw [Nat.card_congr M.ρ.norm.quotKerEquivRange.toEquiv]
  have hdiff : Nat.card M = Nat.card (ker D) * Nat.card (range D) := by
    calc
      Nat.card M = Nat.card (ker D) * Nat.card (M ⧸ ker D) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (ker D) * Nat.card (range D) := by
        rw [Nat.card_congr D.quotKerEquivRange.toEquiv]
  have hrangeNorm : 0 < Nat.card (range M.ρ.norm) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hrangeDiff : 0 < Nat.card (range D) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hcard : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology M (-1)) := by
    apply Nat.mul_right_cancel (Nat.mul_pos hrangeNorm hrangeDiff)
    calc
      Nat.card (tateCohomology M 0) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) =
          (Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0)) *
            Nat.card (range D) := by ac_rfl
      _ = Nat.card (ker D) * Nat.card (range D) := by rw [← hzero, hinv]
      _ = Nat.card M := hdiff.symm
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := hnorm
      _ = (Nat.card (range D) * Nat.card (tateCohomology M (-1))) *
          Nat.card (range M.ρ.norm) := by rw [hnegone, hcoinv]
      _ = Nat.card (tateCohomology M (-1)) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) := by ac_rfl
  have hfiniteQuotient : Finite (ker M.ρ.norm ⧸
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
    Finite.of_surjective (Submodule.mkQ _ ) (Submodule.mkQ_surjective _)
  have hfiniteNegOne : Finite (tateCohomology M (-1)) :=
    (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv.finite_iff.mpr hfiniteQuotient
  rw [herbrandQuotient, hcard]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨0⟩, hfiniteNegOne⟩))

section TrivialInt

variable (H : Type) [Group H] [Fintype H]

/-- For trivial integral coefficients, the norm image is the subgroup generated by the order of
the group. -/
private theorem range_norm_trivial_int :
    range (Rep.trivial ℤ H ℤ).ρ.norm = Ideal.span {(Nat.card H : ℤ)} := by
  ext x
  simp [Representation.norm, Ideal.mem_span_singleton', mul_comm]

/-- Degree-zero Tate cohomology with trivial integral coefficients is `ZMod |G|`. -/
def H0IsoTrivialIntZModCard :
    tateCohomology (Rep.trivial ℤ H ℤ) 0 ≃ₗ[ℤ] ZMod (Nat.card H) := by
  let e : (Rep.trivial ℤ H ℤ).ρ.invariants ≃ₗ[ℤ] ℤ :=
    LinearEquiv.ofEq _ _ (Representation.invariants_eq_top _) ≪≫ₗ Submodule.topEquiv
  refine (H0IsoNormQuotient (Rep.trivial ℤ H ℤ)).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ e ?_ ≪≫ₗ
      (Int.quotientSpanNatEquivZMod _).toIntLinearEquiv
  have he : e.toLinearMap = (Rep.trivial ℤ H ℤ).ρ.invariants.subtype := by
    ext
    rfl
  have hsurjective : Function.Surjective
      (Rep.trivial ℤ H ℤ).ρ.invariants.subtype := by
    rw [← he]
    exact e.surjective
  rw [show (e : _ →ₗ[ℤ] _) = (Rep.trivial ℤ H ℤ).ρ.invariants.subtype from he,
    Submodule.submoduleOf, Submodule.map_comap_eq_of_surjective hsurjective,
    range_norm_trivial_int]

/-- The order of degree-zero Tate cohomology with trivial integral coefficients is the order of
the group. -/
theorem natCard_tateCohomology_zero_trivial_int :
    Nat.card (tateCohomology (Rep.trivial ℤ H ℤ) 0) = Nat.card H := by
  rw [Nat.card_congr (H0IsoTrivialIntZModCard H).toEquiv, Nat.card_zmod]

/-- Degree `-1` Tate cohomology with trivial integral coefficients is trivial. -/
theorem subsingleton_tateCohomology_negOne_trivial_int :
    Subsingleton (tateCohomology (Rep.trivial ℤ H ℤ) (-1)) := by
  let Q := ker (Rep.trivial ℤ H ℤ).ρ.norm ⧸
    (Representation.Coinvariants.ker (Rep.trivial ℤ H ℤ).ρ).submoduleOf
      (ker (Rep.trivial ℤ H ℤ).ρ.norm)
  have hker : ker (Rep.trivial ℤ H ℤ).ρ.norm = ⊥ := by
    ext x
    simp [Representation.norm]
  have hQ : Subsingleton Q := by
    have hkerSubsingleton : Subsingleton (ker (Rep.trivial ℤ H ℤ).ρ.norm) := by
      rw [hker]
      infer_instance
    let _ : Subsingleton (ker (Rep.trivial ℤ H ℤ).ρ.norm) := hkerSubsingleton
    infer_instance
  let _ : Subsingleton Q := hQ
  exact Function.Injective.subsingleton (HNegOneIsoNormKernelQuotient
    (Rep.trivial ℤ H ℤ)).toLinearEquiv.injective

/-- The Herbrand quotient of the trivial integral representation is the order of the finite
group. -/
theorem herbrandQuotient_trivial_int_eq_card :
    herbrandQuotient (Rep.trivial ℤ H ℤ) = Nat.card H := by
  let hsub := subsingleton_tateCohomology_negOne_trivial_int H
  rw [herbrandQuotient, natCard_tateCohomology_zero_trivial_int]
  rw [@Nat.card_of_subsingleton _ 0 hsub]
  simp

end TrivialInt

end TauCeti.TateCohomology
