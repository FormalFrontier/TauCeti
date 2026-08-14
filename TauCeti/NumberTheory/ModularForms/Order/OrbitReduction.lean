/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.Orbits

import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.NumberTheory.Modular.Orbits
import TauCeti.NumberTheory.ModularForms.FiniteZeros

/-!
# Orbit-reduction machinery for the valence formula

The valence formula will be proved as an identity over an arbitrary complete divisor set: for
every finite `S ⊆ 𝒟` catching all nonzero-order points, three sums — over the strict interior,
the left vertical edge, and the left half-arc minus `ρ` — together with the weighted elliptic
and cusp terms equal `k/12`. This file provides the orbit-reduction machinery a future proof of
that theorem will need: a canonical set of representatives for the non-elliptic orbits of
nonzero order, and the rewriting of a `∑ᶠ` over those orbits as the sum over the three
representative families.

The reduction picks one representative per non-elliptic orbit of nonzero order inside the
canonical set `canonicalReps`: interior points represent themselves; a right-vertical-edge point
is moved to the left edge by `z ↦ z - 1`; a right-half-arc point is moved to the left half-arc
by `z ↦ -1/z`. Faithfulness is the injectivity of the orbit map on the left part of `𝒟`
(`TauCeti.ModularGroup.orbit_mk_injOn_fd_left`), and the elliptic orbits are excluded by their
closed-domain descriptions (`orbit_mk_eq_I_iff`, `orbit_mk_eq_ρ_iff`).

## Main declarations

* `TauCeti.ModularForm.fdZeros`: the canonical complete divisor set — the nonzero-order points
  of the closed fundamental domain of a nonzero level-one form.
* `TauCeti.ModularForm.canonicalReps`: one representative per non-elliptic orbit of nonzero
  order — the strict-interior, left-vertical and left-half-arc points of `fdZeros`.
* `TauCeti.ModularForm.exists_mem_canonicalReps_orbit_mk_eq`: every non-elliptic orbit of
  nonzero order has a representative in `canonicalReps`.
* `TauCeti.ModularForm.finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps`: the `∑ᶠ` over the
  non-elliptic orbit space equals the `canonicalReps` sum.
* `TauCeti.ModularForm.sum_canonicalReps_split`: the `canonicalReps` sum splits into the three
  family sums of the core identity.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/Orbits.lean`, `ForMathlib/CanonicalReps.lean` and
  `ForMathlib/ValenceFormula.lean`), ported onto the current Mathlib pin. The denominator
  analysis behind AINTLIB's representative selection is replaced here by Mathlib's
  classification `ModularGroup.cases_of_mem_fd_smul_mem_fd`, through the orbit lemmas of
  `TauCeti.NumberTheory.Modular.Orbits`.
-/

public noncomputable section

open UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- The canonical complete divisor set of a nonzero level-one form: the finitely many points
of the closed fundamental domain `𝒟` carrying nonzero vanishing order, as a `Finset`. -/
def fdZeros [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) : Finset ℍ :=
  (finite_zeros_in_fd hf).toFinset

/-- Membership in the canonical divisor set: a point of `𝒟` of nonzero order. -/
@[simp]
lemma mem_fdZeros [ModularFormClass F 𝒮ℒ k] {f : F} {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} :
    p ∈ fdZeros hf ↔ p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0 :=
  (finite_zeros_in_fd hf).mem_toFinset

/-- One representative per non-elliptic orbit of nonzero order: the points of `fdZeros` in the
strict interior, on the left vertical edge, or on the left half-arc minus `ρ`. The right
vertical edge and right half-arc are omitted — `z ↦ z - 1` and `z ↦ -1/z` move them onto the
left representatives — and the elliptic points are excluded by all three filters. -/
def canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) : Finset ℍ :=
  (fdZeros hf).filter fun p : ℍ ↦
    (1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) ∨
      ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
      ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- Membership in the canonical representatives: a point of `fdZeros` in the strict interior,
on the left vertical edge, or on the left half-arc minus `ρ`. -/
@[simp]
lemma mem_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F} {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} :
    p ∈ canonicalReps hf ↔
      p ∈ fdZeros hf ∧
        ((1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) ∨
          ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
          ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)) :=
  Finset.mem_filter

private lemma ne_elliptic_of_mem_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} (hp : p ∈ canonicalReps hf) :
    p ≠ I ∧ p ≠ ρ ∧ p ≠ (1 : ℝ) +ᵥ ρ := by
  have hcond := (mem_canonicalReps.mp hp).2
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;> subst h <;>
    rcases hcond with ⟨hgt, habs⟩ | ⟨hre, hgt⟩ | ⟨hne, hnorm, hre⟩
  · norm_num at hgt
  · norm_num at hre
  · norm_num at hre
  · norm_num [norm_ρ] at hgt
  · norm_num [norm_ρ] at hgt
  · exact hne rfl
  · norm_num at habs
  · norm_num at hre
  · norm_num at hre

/-- The canonical representatives lie in the non-elliptic orbits. -/
theorem orbit_mk_ne_I_and_ne_ρ_of_mem_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p : ℍ} (hp : p ∈ canonicalReps hf) :
    (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I ∧
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ := by
  obtain ⟨hne_I, hne_ρ, hne_vadd⟩ := ne_elliptic_of_mem_canonicalReps hp
  have hfd : p ∈ 𝒟 := (mem_fdZeros.mp (mem_canonicalReps.mp hp).1).1
  exact ⟨fun h ↦ hne_I ((ModularGroup.orbit_mk_eq_I_iff hfd).mp h),
    fun h ↦ ((ModularGroup.orbit_mk_eq_ρ_iff hfd).mp h).elim hne_ρ hne_vadd⟩

/-- The orbit map is injective on the canonical representatives, which lie left of the
boundary identifications of `𝒟`. -/
theorem orbit_mk_injOn_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.InjOn (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ))
      ↑(canonicalReps hf) := by
  refine ModularGroup.orbit_mk_injOn_fd_left.mono fun p hp ↦ ?_
  obtain ⟨hmem, hcond⟩ := mem_canonicalReps.mp hp
  refine ⟨(mem_fdZeros.mp hmem).1, ?_, ?_⟩
  · rcases hcond with ⟨-, habs⟩ | ⟨hre, -⟩ | ⟨-, -, hre⟩
    · exact lt_of_abs_lt (coe_re p ▸ habs)
    · norm_num [← coe_re, hre]
    · exact (coe_re p ▸ hre).trans (by norm_num)
  · intro hnorm
    rcases hcond with ⟨hgt, -⟩ | ⟨-, hgt⟩ | ⟨-, -, hre⟩
    · norm_num [hnorm] at hgt
    · norm_num [hnorm] at hgt
    · exact coe_re p ▸ hre

private lemma normSq_coe_vadd_neg_one {p : ℍ} (hre : (p : ℂ).re = 1 / 2) :
    Complex.normSq (((-1 : ℝ) +ᵥ p : ℍ) : ℂ) = Complex.normSq (p : ℂ) := by
  rw [coe_re] at hre
  simp [coe_vadd, Complex.normSq_apply, hre]
  ring

private lemma norm_coe_vadd_neg_one {p : ℍ} (hre : (p : ℂ).re = 1 / 2) :
    ‖(((-1 : ℝ) +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [Complex.norm_def, Complex.norm_def, normSq_coe_vadd_neg_one hre]

private lemma vadd_neg_one_mem_fd {p : ℍ} (hp : p ∈ 𝒟) (hre : (p : ℂ).re = 1 / 2) :
    (-1 : ℝ) +ᵥ p ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · rw [normSq_coe_vadd_neg_one hre]
    exact hp.1
  · rw [vadd_re, (coe_re p ▸ hre : p.re = 1 / 2)]
    norm_num

private lemma exists_of_re_eq_half [ModularFormClass F 𝒮ℒ k] {f : F} {hf : (⇑f : ℍ → ℂ) ≠ 0}
    {p₀ : ℍ} (hfd : p₀ ∈ 𝒟) (hord : orderOfVanishingAt f p₀ ≠ 0) (hre : (p₀ : ℂ).re = 1 / 2)
    (hlt : 1 < ‖(p₀ : ℂ)‖) : ∃ p ∈ canonicalReps hf,
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' p₀ := by
  have horb : (Quotient.mk'' ((-1 : ℝ) +ᵥ p₀) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' p₀ := by
    simpa using ModularGroup.orbit_mk_int_vadd (-1) p₀
  have hord' : orderOfVanishingAt f ((-1 : ℝ) +ᵥ p₀) ≠ 0 := by
    rw [← orderOfVanishingOnOrbit_mk (k := k) f, horb, orderOfVanishingOnOrbit_mk]
    exact hord
  refine ⟨(-1 : ℝ) +ᵥ p₀, mem_canonicalReps.mpr ⟨mem_fdZeros.mpr
    ⟨vadd_neg_one_mem_fd hfd hre, hord'⟩, Or.inr (Or.inl ⟨?_, ?_⟩)⟩, horb⟩
  · rw [coe_vadd, Complex.add_re, Complex.ofReal_re, hre]
    norm_num
  · rw [norm_coe_vadd_neg_one hre]
    exact hlt

private lemma exists_of_norm_eq_one_of_re_pos [ModularFormClass F 𝒮ℒ k] {f : F}
    {hf : (⇑f : ℍ → ℂ) ≠ 0} {p₀ : ℍ} (hfd : p₀ ∈ 𝒟) (hord : orderOfVanishingAt f p₀ ≠ 0)
    (hnorm : ‖(p₀ : ℂ)‖ = 1) (hpos : 0 < (p₀ : ℂ).re)
    (hqρ : (Quotient.mk'' p₀ : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    ∃ p ∈ canonicalReps hf,
      (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' p₀ := by
  have horb : (Quotient.mk'' (ModularGroup.S • p₀) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) =
      Quotient.mk'' p₀ := Quotient.sound' ⟨ModularGroup.S, rfl⟩
  have hord' : orderOfVanishingAt f (ModularGroup.S • p₀) ≠ 0 := by
    rw [← orderOfVanishingOnOrbit_mk (k := k) f, horb, orderOfVanishingOnOrbit_mk]
    exact hord
  have hne : ((ModularGroup.S • p₀ : ℍ) : ℂ) ≠ (ρ : ℂ) := fun h ↦
    hqρ (horb ▸ congrArg Quotient.mk'' (UpperHalfPlane.coe_injective h))
  refine ⟨ModularGroup.S • p₀, mem_canonicalReps.mpr ⟨mem_fdZeros.mpr
    ⟨ModularGroup.S_smul_mem_fd_of_norm_eq_one hfd.2 hnorm, hord'⟩,
      Or.inr (Or.inr ⟨hne, ModularGroup.norm_coe_S_smul_of_norm_eq_one hnorm, ?_⟩)⟩, horb⟩
  rw [coe_re, ModularGroup.re_S_smul_of_norm_eq_one hnorm]
  exact neg_lt_zero.mpr (coe_re p₀ ▸ hpos)

/-- Every non-elliptic orbit of nonzero order has a representative among the canonical ones:
a fundamental-domain representative exists, and the boundary identifications move it into
`canonicalReps` when it falls on the omitted right vertical edge or right half-arc. -/
theorem exists_mem_canonicalReps_orbit_mk_eq [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) {q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ}
    (hqI : q ≠ Quotient.mk'' I) (hqρ : q ≠ Quotient.mk'' ρ)
    (hq : orderOfVanishingOnOrbit f q ≠ 0) :
    ∃ p ∈ canonicalReps hf, Quotient.mk'' p = q := by
  obtain ⟨p₀, rfl, hfd⟩ := ModularGroup.exists_rep_mem_fd q
  rw [orderOfVanishingOnOrbit_mk] at hq
  rcases (Complex.one_le_normSq_iff.mp hfd.1).lt_or_eq with hlt | heq
  · rcases hfd.2.lt_or_eq with hre_lt | hre_eq
    · refine ⟨p₀, mem_canonicalReps.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩, Or.inl ⟨hlt, ?_⟩⟩, rfl⟩
      rwa [coe_re]
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hre_eq with h | h
      · exact exists_of_re_eq_half hfd hq ((coe_re p₀).trans h) hlt
      · exact ⟨p₀, mem_canonicalReps.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩,
          Or.inr (Or.inl ⟨(coe_re p₀).trans h, hlt⟩)⟩, rfl⟩
  · rcases lt_trichotomy ((p₀ : ℂ).re) 0 with hneg | hzero | hpos
    · have hne : (p₀ : ℂ) ≠ (ρ : ℂ) := fun h ↦
        hqρ (congrArg Quotient.mk'' (UpperHalfPlane.coe_injective h))
      exact ⟨p₀, mem_canonicalReps.mpr ⟨mem_fdZeros.mpr ⟨hfd, hq⟩,
        Or.inr (Or.inr ⟨hne, heq.symm, hneg⟩)⟩, rfl⟩
    · exact absurd (congrArg Quotient.mk'' (UpperHalfPlane.eq_of_re_of_norm
        (by rw [← coe_re, hzero, ← coe_re, coe_I, Complex.I_re])
        (by rw [heq.symm, coe_I, Complex.norm_I]))) hqI
    · exact exists_of_norm_eq_one_of_re_pos hfd hq heq.symm hpos hqρ

/-- The `∑ᶠ` over the non-elliptic orbit space equals the sum over the canonical
representatives: the orbit map matches `canonicalReps` bijectively with the non-elliptic
orbits of nonzero order, and the order is orbit-constant. -/
theorem finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val =
      ∑ p ∈ canonicalReps hf, orderOfVanishingAt f p := by
  rw [finsum_eq_sum _ (hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf)]
  refine (Finset.sum_bij
    (fun p hp ↦ (⟨Quotient.mk'' p, orbit_mk_ne_I_and_ne_ρ_of_mem_canonicalReps hp⟩ :
      NonEllipticOrbit))
    ?_ ?_ ?_ ?_).symm
  · intro p hp
    refine (hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf).mem_toFinset.mpr ?_
    simpa using (mem_fdZeros.mp (mem_canonicalReps.mp hp).1).2
  · intro p₁ h₁ p₂ h₂ h
    exact orbit_mk_injOn_canonicalReps hf h₁ h₂ (congrArg Subtype.val h)
  · intro q hq
    obtain ⟨p, hp, hporb⟩ := exists_mem_canonicalReps_orbit_mk_eq hf q.2.1 q.2.2
      ((hasFiniteSupport_orderOfVanishingOnOrbit_nonElliptic hf).mem_toFinset.mp hq)
    exact ⟨p, hp, Subtype.ext hporb⟩
  · intro p hp
    exact (orderOfVanishingOnOrbit_mk f p).symm

/-- The canonical-representative sum splits into the three family sums of the core identity:
strict interior, left vertical edge, and left half-arc minus `ρ`. -/
theorem sum_canonicalReps_split [ModularFormClass F 𝒮ℒ k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∑ p ∈ canonicalReps hf, orderOfVanishingAt f p =
      ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
          orderOfVanishingAt f p +
        ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p +
        ∑ p ∈ (fdZeros hf).filter (fun p : ℍ ↦
          (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt f p := by
  classical
  have hd₂ : Disjoint
      ((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖)
      ((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) :=
    Finset.disjoint_left.mpr fun p hp hq ↦
      (Finset.mem_filter.mp hp).2.2.ne' (Finset.mem_filter.mp hq).2.2.1
  have hd₁ : Disjoint
      ((fdZeros hf).filter fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)
      (((fdZeros hf).filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∪
        (fdZeros hf).filter fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
    refine Finset.disjoint_left.mpr fun p hp hq ↦ ?_
    obtain ⟨hgt, habs⟩ := (Finset.mem_filter.mp hp).2
    rcases Finset.mem_union.mp hq with hq | hq
    · norm_num [← coe_re, (Finset.mem_filter.mp hq).2.1] at habs
    · norm_num [(Finset.mem_filter.mp hq).2.2.1] at hgt
  unfold canonicalReps
  rw [Finset.filter_or, Finset.filter_or, Finset.sum_union hd₁, Finset.sum_union hd₂,
    ← add_assoc]

end ModularForm

end TauCeti

end
