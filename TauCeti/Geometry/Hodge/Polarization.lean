/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import TauCeti.Geometry.Hodge.BilinearForm
public import TauCeti.Geometry.Hodge.Structure

/-!
# Polarizations of pure Hodge structures

A polarization of a weight-`n` Hodge structure on a lattice `V` is an integral bilinear form on
`V` satisfying the Hodge–Riemann bilinear relations. This file states those relations as a
predicate on a *fixed* form, `TauCeti.Hodge.IsPolarization`, so that a form can be required to
polarize a structure without being carried twice; bundling the form with a proof gives
`TauCeti.Hodge.Polarization`, and forgetting the form gives the property
`TauCeti.Hodge.IsPolarizable`.

The complex form is derived rather than postulated: it is the complexification
`TauCeti.Hodge.integralFormBaseChange` of the integral form, so the integral-to-complex link is a
computation rather than an axiom.

## Conventions

The weight sign is `Q y x = (-1)^n Q x y`, written with `Int.negOnePow`, and the positivity
relation is `0 < i^(p-q) * Q x (conj x)` for `0 ≠ x` in the Hodge component `H^{p,q}`, in the
partial order on `ℂ` available as `open scoped ComplexOrder`. Requiring positivity in that order
also requires the value to be real, which is part of the classical statement. A geometric
polarization built from a cup product carries an extra sign `(-1)^(n(n-1)/2)`, which an instance
realized that way must insert to match this convention.

## Main declarations

* `TauCeti.Hodge.IsPolarization`: the Hodge–Riemann relations for a fixed integral form.
* `TauCeti.Hodge.IsPolarization.orthogonal_piece`: distinct Hodge components pair to zero unless
  their degrees add up to the weight.
* `TauCeti.Hodge.IsPolarization.complex_nondegenerate`: the complexified form of a polarization is
  nondegenerate.
* `TauCeti.Hodge.IsPolarization.exists_pairing_ne_zero`: conjugate Hodge components pair
  nondegenerately.
* `TauCeti.Hodge.Polarization`: a polarized Hodge structure's form, bundled with its relations.
* `TauCeti.Hodge.IsPolarizable`: existence of some polarizing form.

The Hodge–Riemann relations follow Voisin, *Hodge Theory and Complex Algebraic Geometry I*,
§7.1.2, and Peters–Steenbrink, *Mixed Hodge Structures*, §2. This is the definition layer of
Layer L1 of `TauCetiRoadmap/HodgeStructures/README.md`.
-/

public section

namespace TauCeti.Hodge

open scoped ComplexOrder

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ}

/-- The **Hodge–Riemann bilinear relations** for a fixed integral bilinear form `Q` on the lattice
of a weight-`n` Hodge structure.

The form is `(-1)^n`-symmetric and nondegenerate; its complexification annihilates
`F p × F (n + 1 - p)`; and `i^(p-q) Q x (conj x)` is a positive real number for every nonzero `x`
in the Hodge component `H^{p,q}`, where `q = n - p`. -/
structure IsPolarization (hℂ : IsBaseChange ℂ ιℂ) {n : ℤ} (hs : HodgeStructure hℂ n)
    (Q : LinearMap.BilinForm ℤ V) : Prop where
  /-- The form is symmetric in even weight and antisymmetric in odd weight. -/
  symm_weight : ∀ x y, Q y x = (n.negOnePow : ℤ) * Q x y
  /-- The form has no radical. -/
  nondegenerate : Q.Nondegenerate
  /-- The first Hodge–Riemann relation: `F p` and `F (n + 1 - p)` are orthogonal. -/
  orthogonal : ∀ p, ∀ x ∈ hs.F p, ∀ y ∈ hs.F (n + 1 - p),
    integralFormBaseChange hℂ Q x y = 0
  /-- The second Hodge–Riemann relation: `i^(p-q) Q x (conj x)` is positive on `H^{p,q}`. -/
  positive : ∀ p, ∀ x ∈ hs.piece p, x ≠ 0 →
    0 < Complex.I ^ (2 * p - n) * integralFormBaseChange hℂ Q x (latticeConj hℂ x)

namespace IsPolarization

variable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n}
variable {Q : LinearMap.BilinForm ℤ V}

/-- A polarization of an even-weight Hodge structure is a symmetric form. -/
theorem symm_of_even (h : IsPolarization hℂ hs Q) (hn : Even n) (x y : V) : Q y x = Q x y := by
  simpa [Int.negOnePow_even n hn] using h.symm_weight x y

/-- A polarization of an odd-weight Hodge structure is an antisymmetric form. -/
theorem eq_neg_of_odd (h : IsPolarization hℂ hs Q) (hn : Odd n) (x y : V) : Q y x = -Q x y := by
  simpa [Int.negOnePow_odd n hn] using h.symm_weight x y

/-- The flip of a polarizing form is its `(-1)^n`-multiple. -/
theorem flip_eq (h : IsPolarization hℂ hs Q) : Q.flip = (n.negOnePow : ℤ) • Q := by
  ext x y
  simpa using h.symm_weight x y

/-- The complexification of a polarizing form obeys the same weight symmetry. -/
theorem complex_symm_weight (h : IsPolarization hℂ hs Q) (x y : Vℂ) :
    integralFormBaseChange hℂ Q y x = (n.negOnePow : ℤ) * integralFormBaseChange hℂ Q x y := by
  have hforms : (integralFormBaseChange hℂ Q).flip =
      (n.negOnePow : ℤ) • integralFormBaseChange hℂ Q := by
    rw [integralFormBaseChange_flip, h.flip_eq, integralFormBaseChange_zsmul]
  have hxy := DFunLike.congr_fun (DFunLike.congr_fun hforms x) y
  simpa only [LinearMap.BilinForm.flip_apply, LinearMap.smul_apply, zsmul_eq_mul] using hxy

/-- The complexification of a polarizing form is nondegenerate. -/
theorem complex_nondegenerate (h : IsPolarization hℂ hs Q) :
    LinearMap.BilinForm.Nondegenerate (integralFormBaseChange hℂ Q) :=
  integralFormBaseChange_nondegenerate hℂ h.nondegenerate

/-- The first Hodge–Riemann relation transported to the conjugate filtration. -/
theorem orthogonal_conjF (h : IsPolarization hℂ hs Q) (p : ℤ) {x y : Vℂ}
    (hx : x ∈ hs.conjF p) (hy : y ∈ hs.conjF (n + 1 - p)) :
    integralFormBaseChange hℂ Q x y = 0 := by
  have hx' : latticeConj hℂ x ∈ hs.F p := by
    simpa using (hs.mem_conjF_iff p x).mp hx
  have hy' : latticeConj hℂ y ∈ hs.F (n + 1 - p) := by
    simpa using (hs.mem_conjF_iff (n + 1 - p) y).mp hy
  have hzero := h.orthogonal p _ hx' _ hy'
  rw [integralFormBaseChange_conj] at hzero
  simpa using congrArg (starRingEnd ℂ) hzero

/-- **Orthogonality of the Hodge components.** Two Hodge components pair to zero under a
polarization unless their degrees add up to the weight. -/
theorem orthogonal_piece (h : IsPolarization hℂ hs Q) {p p' : ℤ} (hpp : p + p' ≠ n)
    {x y : Vℂ} (hx : x ∈ hs.piece p) (hy : y ∈ hs.piece p') :
    integralFormBaseChange hℂ Q x y = 0 := by
  rcases lt_or_gt_of_ne hpp with hlt | hgt
  · -- Below the weight: conjugate both arguments into complementary filtration steps.
    refine h.orthogonal_conjF (n - p) (hs.piece_le_conjF p hx) ?_
    exact hs.conjF_antitone (by omega) (hs.piece_le_conjF p' hy)
  · -- Above the weight: the second argument already lies deep enough in the filtration.
    refine h.orthogonal p x (hs.piece_le_F p hx) y ?_
    exact hs.F_antitone (by omega) (hs.piece_le_F p' hy)

/-- Under a polarization the Hodge–Riemann pairing of a nonzero component vector with its
conjugate is nonzero. -/
theorem pairing_conj_ne_zero (h : IsPolarization hℂ hs Q) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) (hx0 : x ≠ 0) :
    integralFormBaseChange hℂ Q x (latticeConj hℂ x) ≠ 0 := by
  intro hzero
  have hpos := h.positive p x hx hx0
  rw [hzero, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **Nondegeneracy of the Hodge–Riemann pairing between conjugate components.** Every nonzero
vector of `H^{p,q}` pairs nontrivially with a vector of `H^{q,p}`, namely with its conjugate. -/
theorem exists_pairing_ne_zero (h : IsPolarization hℂ hs Q) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) (hx0 : x ≠ 0) :
    ∃ y ∈ hs.piece (n - p), integralFormBaseChange hℂ Q x y ≠ 0 :=
  ⟨latticeConj hℂ x, by simpa using hs.conj_mem_piece hx, h.pairing_conj_ne_zero hx hx0⟩

end IsPolarization

/-- A **polarization** of a pure Hodge structure: an integral bilinear form on its lattice
together with the Hodge–Riemann relations. -/
structure Polarization (hℂ : IsBaseChange ℂ ιℂ) {n : ℤ} (hs : HodgeStructure hℂ n) where
  /-- The underlying integral bilinear form. -/
  Qint : LinearMap.BilinForm ℤ V
  /-- The Hodge–Riemann relations for that form. -/
  isPolarization : IsPolarization hℂ hs Qint

namespace Polarization

variable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n}

/-- The complex bilinear form of a polarization, derived by complexifying the integral form. -/
noncomputable def Q (P : Polarization hℂ hs) : LinearMap.BilinForm ℂ Vℂ :=
  integralFormBaseChange hℂ P.Qint

/-- The complex form of a polarization obeys the weight symmetry. -/
theorem Q_symm_weight (P : Polarization hℂ hs) (x y : Vℂ) :
    P.Q y x = (n.negOnePow : ℤ) * P.Q x y :=
  P.isPolarization.complex_symm_weight x y

/-- The complex form of a polarization is nondegenerate. -/
theorem Q_nondegenerate (P : Polarization hℂ hs) :
    LinearMap.BilinForm.Nondegenerate P.Q :=
  P.isPolarization.complex_nondegenerate

/-- The complex form of a polarization satisfies the first Hodge–Riemann relation. -/
theorem Q_orthogonal (P : Polarization hℂ hs) (p : ℤ) {x y : Vℂ} (hx : x ∈ hs.F p)
    (hy : y ∈ hs.F (n + 1 - p)) : P.Q x y = 0 :=
  P.isPolarization.orthogonal p x hx y hy

/-- The complex form of a polarization satisfies the second Hodge–Riemann relation. -/
theorem Q_positive (P : Polarization hℂ hs) (p : ℤ) {x : Vℂ} (hx : x ∈ hs.piece p)
    (hx0 : x ≠ 0) :
    0 < Complex.I ^ (2 * p - n) * P.Q x (latticeConj hℂ x) :=
  P.isPolarization.positive p x hx hx0

/-- The complex form of a polarization restricts to the integral form on integral vectors. -/
@[simp]
theorem Q_ι (P : Polarization hℂ hs) (x y : V) : P.Q (ιℂ x) (ιℂ y) = (P.Qint x y : ℂ) :=
  integralFormBaseChange_ι hℂ P.Qint x y

/-- The complex bilinear form is the complexification of the integral form. -/
theorem Q_def (P : Polarization hℂ hs) : P.Q = integralFormBaseChange hℂ P.Qint :=
  integralFormBaseChange_unique hℂ P.Qint P.Q P.Q_ι

/-- The complex form of a polarization takes conjugate values on conjugate arguments. -/
@[simp]
theorem Q_conj (P : Polarization hℂ hs) (x y : Vℂ) :
    P.Q (latticeConj hℂ x) (latticeConj hℂ y) = starRingEnd ℂ (P.Q x y) :=
  integralFormBaseChange_conj hℂ P.Qint x y

/-- Two polarizations of the same Hodge structure agree as soon as their integral forms do. -/
@[ext]
theorem ext {P P' : Polarization hℂ hs} (h : P.Qint = P'.Qint) : P = P' := by
  cases P
  cases P'
  simp_all

end Polarization

/-- A pure Hodge structure is **polarizable** when some integral form polarizes it. This, rather
than a chosen polarization, is the property under which the category of rational Hodge structures
is semisimple. -/
def IsPolarizable (hℂ : IsBaseChange ℂ ιℂ) {n : ℤ} (hs : HodgeStructure hℂ n) : Prop :=
  ∃ Q : LinearMap.BilinForm ℤ V, IsPolarization hℂ hs Q

/-- A chosen polarization exhibits a Hodge structure as polarizable. -/
theorem Polarization.isPolarizable {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n}
    (P : Polarization hℂ hs) : IsPolarizable hℂ hs :=
  ⟨P.Qint, P.isPolarization⟩

/-- Polarizability is exactly the existence of a bundled polarization. -/
theorem isPolarizable_iff_nonempty {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n} :
    IsPolarizable hℂ hs ↔ Nonempty (Polarization hℂ hs) :=
  ⟨fun ⟨Q, hQ⟩ ↦ ⟨⟨Q, hQ⟩⟩, fun ⟨P⟩ ↦ P.isPolarizable⟩

end TauCeti.Hodge
