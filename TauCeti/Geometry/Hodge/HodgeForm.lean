/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Hodge.WeilOperator

/-!
# The Hodge form of a polarization

The second Hodge–Riemann relation says that `i^(p-q) Q x (conj x)` is positive on the Hodge
component `H^{p,q}`. That expression is not defined on an inhomogeneous vector, because the
scalar `i^(p-q)` depends on the component. Inserting the Weil operator repairs this: the **Hodge
form**

`h u v = Q (C (conj u)) v`

is defined on all of the ambient complex vector space, is conjugate-linear in its first argument
and linear in its second. On the diagonal of `H^{p,q}` it gives the classical expression
`i^(p-q) Q x (conj x)`. This file constructs it and proves that it is a positive definite
Hermitian form.

The two inputs are the Weil operator's compatibilities with the polarizing form: `C` is an
isometry of `Q`, and `C` commutes with conjugation. These compatibilities enter the Hermitian and
Weil-operator invariance identities. Sesquilinearity itself comes directly from composing the
complex-bilinear form with the conjugate-linear map `latticeConj`. Positive definiteness comes
from the Hodge decomposition: distinct Hodge components are `h`-orthogonal, so `h x x` is the sum
of the positive contributions of the components of `x`.

## Conventions

Following Mathlib's `LinearMap.IsSymm`, the Hodge form is taken conjugate-linear in the first
argument and linear in the second, whereas Hodge theory usually writes `Q (C u) (conj v)`, which
is conjugate-linear in the second. The two conventions are exchanged by conjugating, which is
`TauCeti.Hodge.Polarization.hodgeForm_eq_conj`; the choice made here is the one for which
Mathlib's `IsSymm`, `IsNonneg` and `IsPosSemidef` are stated. The sign conventions for the form
itself are those pinned in `TauCeti.Hodge.IsPolarization`.

## Main declarations

* `TauCeti.Hodge.Polarization.hodgeForm`: the Hodge form of a polarization.
* `TauCeti.Hodge.Polarization.hodgeForm_eq_conj`: it is the conjugate of the alternate-convention
  whole-space form `Q (C u) (conj v)`.
* `TauCeti.Hodge.Polarization.isSymm_hodgeForm`: it is Hermitian.
* `TauCeti.Hodge.Polarization.hodgeForm_eq_zero_of_mem_piece`: distinct Hodge components are
  orthogonal for it.
* `TauCeti.Hodge.Polarization.hodgeForm_self_pos`: it is positive definite.
* `TauCeti.Hodge.Polarization.isPosSemidef_hodgeForm` and
  `TauCeti.Hodge.Polarization.hodgeForm_nondegenerate`: the packaged consequences.
* `TauCeti.Hodge.tate_hodgeForm_apply`: the Hodge form of the polarized Tate structure `ℤ(m)` is the
  standard Hermitian form of the complex line.

This is the Hermitian carrier targeted in Layer L1 of
`TauCetiRoadmap/HodgeStructures/README.md`, the form through which the polarization is used in
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink, *Mixed
Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge

open scoped ComplexOrder

universe u v

variable {V : Type u} {Vℂ : Type v}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {hs : HodgeStructure hℂ n}

/-! ### Sign and power-of-`i` bookkeeping -/

/-- The cast of `(-1)^n` from the units of the integers is the complex power. -/
private theorem negOnePow_cast (k : ℤ) : ((k.negOnePow : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [Int.negOnePow_even _ hk, hk.neg_one_zpow]
    norm_num
  · rw [Int.negOnePow_odd _ hk, hk.neg_one_zpow]
    norm_num

/-- A power of `-1` is the corresponding even power of `i`. -/
private theorem negOne_zpow_eq_I_zpow (k : ℤ) : (-1 : ℂ) ^ k = Complex.I ^ (2 * k) := by
  have h : Complex.I ^ (2 : ℤ) = -1 := by
    have htwo : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [htwo, zpow_natCast, Complex.I_sq]
  rw [zpow_mul, h]

/-- The exponent bookkeeping behind the value of the Hodge form on a Hodge component: the scalar
`i^(2(k-p)-k)` by which the Weil operator acts on the conjugate component, corrected by the
weight sign `(-1)^k`, is the scalar `i^(2p-k)` of the second Hodge–Riemann relation. -/
private theorem I_zpow_conj_piece (p k : ℤ) :
    Complex.I ^ (2 * (k - p) - k) * (-1 : ℂ) ^ k = Complex.I ^ (2 * p - k) := by
  have hexp : 2 * (k - p) - k + 2 * k = 2 * p - k + 4 * (k - p) := by ring
  rw [negOne_zpow_eq_I_zpow, ← zpow_add₀ Complex.I_ne_zero,
    hexp, zpow_add₀ Complex.I_ne_zero, Complex.I_zpow_eq_zpow_mod (4 * (k - p)),
    Int.mul_emod_right, zpow_zero, mul_one]

namespace Polarization

/-! ### The Hodge form -/

/-- **The Hodge form** of a polarization: the sesquilinear form `h u v = Q (C (conj u)) v`,
conjugate-linear in its first argument and linear in its second. For `x` in `H^{p,q}`, conjugation
moves `x` to `H^{q,p}`; the action of `C` there, together with the weight symmetry of `Q`, gives
`h x x = i^(p-q) Q x (conj x)`, whose positivity is the second Hodge–Riemann relation. -/
noncomputable def hodgeForm (P : Polarization hℂ hs) :
    Vℂ →ₛₗ[starRingEnd ℂ] Vℂ →ₗ[ℂ] ℂ :=
  (P.Q ∘ₗ hs.weilOperator) ∘ₛₗ latticeConj hℂ

/-- The value of the Hodge form, in terms of the complex form of the polarization. -/
theorem hodgeForm_apply (P : Polarization hℂ hs) (u v : Vℂ) :
    P.hodgeForm u v = P.Q (hs.weilOperator (latticeConj hℂ u)) v :=
  (rfl)

/-- The Hodge form is the conjugate of the alternate-convention whole-space form
`Q (C u) (conj v)`. For homogeneous `u ∈ H^{p,q}`, the latter becomes
`i^(p-q) Q u (conj v)`. -/
theorem hodgeForm_eq_conj (P : Polarization hℂ hs) (u v : Vℂ) :
    P.hodgeForm u v = starRingEnd ℂ (P.Q (hs.weilOperator u) (latticeConj hℂ v)) := by
  have hconj : latticeConj hℂ (hs.weilOperator u) =
      hs.weilOperator (latticeConj hℂ u) := by
    simpa only [latticeConjugation_toEquiv_apply] using hs.conj_weilOperator u
  rw [← P.Q_conj, hconj, latticeConj_apply_apply, hodgeForm_apply]

/-- **The Hodge form is Hermitian.** -/
theorem isSymm_hodgeForm (P : Polarization hℂ hs) : P.hodgeForm.IsSymm where
  eq u v := by
    have hconj : starRingEnd ℂ (P.hodgeForm u v) =
        P.Q (hs.weilOperator u) (latticeConj hℂ v) := by
      rw [hodgeForm_eq_conj, Complex.conj_conj]
    rw [hconj, hodgeForm_apply]
    have hsquare : hs.weilOperator (hs.weilOperator u) = ((-1 : ℂ) ^ n) • u := by
      simpa using DFunLike.congr_fun hs.weilOperator_comp_weilOperator u
    calc P.Q (hs.weilOperator u) (latticeConj hℂ v)
        = P.Q (hs.weilOperator (hs.weilOperator u))
            (hs.weilOperator (latticeConj hℂ v)) := (P.Q_weilOperator _ _).symm
      _ = ((-1 : ℂ) ^ n) * P.Q u (hs.weilOperator (latticeConj hℂ v)) := by
          rw [hsquare, map_smul, LinearMap.smul_apply, smul_eq_mul]
      _ = P.Q (hs.weilOperator (latticeConj hℂ v)) u := by
          rw [P.Q_symm_weight u (hs.weilOperator (latticeConj hℂ v)), negOnePow_cast]

/-- Conjugating both arguments of the Hodge form conjugates its value. -/
@[simp]
theorem hodgeForm_latticeConj (P : Polarization hℂ hs) (u v : Vℂ) :
    P.hodgeForm (latticeConj hℂ u) (latticeConj hℂ v) = starRingEnd ℂ (P.hodgeForm u v) := by
  rw [hodgeForm_apply, latticeConj_apply_apply, hodgeForm_eq_conj, Complex.conj_conj]

/-- The Weil operator is unitary for the Hodge form. -/
@[simp]
theorem hodgeForm_weilOperator (P : Polarization hℂ hs) (u v : Vℂ) :
    P.hodgeForm (hs.weilOperator u) (hs.weilOperator v) = P.hodgeForm u v := by
  have hconj : latticeConj hℂ (hs.weilOperator u) =
      hs.weilOperator (latticeConj hℂ u) := by
    simpa only [latticeConjugation_toEquiv_apply] using hs.conj_weilOperator u
  rw [hodgeForm_apply, hodgeForm_apply, hconj, P.Q_weilOperator]

/-! ### Positive definiteness -/

/-- On the Hodge component `H^{p,q}` the Hodge form is the expression `i^(p-q) Q x (conj x)` of
the second Hodge–Riemann relation. -/
theorem hodgeForm_self_of_mem_piece (P : Polarization hℂ hs) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) :
    P.hodgeForm x x = Complex.I ^ (2 * p - n) * P.Q x (latticeConj hℂ x) := by
  have hconj_mem : latticeConj hℂ x ∈ hs.piece (n - p) := by
    simpa using hs.conj_mem_piece hx
  rw [hodgeForm_apply, hs.weilOperator_apply_of_mem hconj_mem]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [P.Q_symm_weight x (latticeConj hℂ x), negOnePow_cast, ← mul_assoc, I_zpow_conj_piece]

/-- The Hodge form is positive on every nonzero vector of a Hodge component. -/
theorem hodgeForm_pos_of_mem_piece (P : Polarization hℂ hs) {p : ℤ} {x : Vℂ}
    (hx : x ∈ hs.piece p) (hx0 : x ≠ 0) : 0 < P.hodgeForm x x := by
  rw [P.hodgeForm_self_of_mem_piece hx]
  exact P.Q_positive p hx hx0

/-- **Distinct Hodge components are orthogonal for the Hodge form.** Conjugation carries the
`p`-th component to the `(n-p)`-th and the Weil operator preserves it, so the pairing is the
pairing of the `(n-p)`-th and `p'`-th components under `Q`. -/
theorem hodgeForm_eq_zero_of_mem_piece (P : Polarization hℂ hs) {p p' : ℤ} (hpp : p ≠ p')
    {x y : Vℂ} (hx : x ∈ hs.piece p) (hy : y ∈ hs.piece p') : P.hodgeForm x y = 0 := by
  have hconj_mem : latticeConj hℂ x ∈ hs.piece (n - p) := by
    simpa using hs.conj_mem_piece hx
  rw [hodgeForm_apply, P.Q_def]
  exact P.isPolarization.orthogonal_piece (by omega)
    (hs.weilOperator_mem_piece hconj_mem) hy

/-- **The Hodge form is positive definite.** Expanding a nonzero vector into its Hodge components
and using their orthogonality, the value on the diagonal is a sum of positive contributions, one
for each nonzero component. -/
theorem hodgeForm_self_pos (P : Polarization hℂ hs) {x : Vℂ} (hx : x ≠ 0) :
    0 < P.hodgeForm x x := by
  have hmem : x ∈ ⨆ p, hs.piece p := by
    rw [hs.iSup_piece_eq_top]
    exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp hs.piece x).mp hmem
  rw [Finsupp.sum] at hx ⊢
  have hexpand : P.hodgeForm (∑ p ∈ f.support, f p) (∑ p ∈ f.support, f p) =
      ∑ p ∈ f.support, P.hodgeForm (f p) (f p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_single q (fun p _ hpq ↦ ?_) fun hq' ↦ absurd hq hq'
    exact P.hodgeForm_eq_zero_of_mem_piece hpq (hf p) (hf q)
  rw [hexpand]
  refine Finset.sum_pos' (fun p _ ↦ ?_) ?_
  · rcases eq_or_ne (f p) 0 with h0 | h0
    · simp [h0]
    · exact (P.hodgeForm_pos_of_mem_piece (hf p) h0).le
  · obtain ⟨p, hp, hfp⟩ : ∃ p ∈ f.support, f p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (Finset.sum_eq_zero hcon)
    exact ⟨p, hp, P.hodgeForm_pos_of_mem_piece (hf p) hfp⟩

/-- The Hodge form is nonnegative on the diagonal. -/
theorem hodgeForm_self_nonneg (P : Polarization hℂ hs) (x : Vℂ) : 0 ≤ P.hodgeForm x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (P.hodgeForm_self_pos hx).le

/-- The Hodge form is nonnegative, in Mathlib's packaging. -/
theorem isNonneg_hodgeForm (P : Polarization hℂ hs) : P.hodgeForm.IsNonneg :=
  ⟨P.hodgeForm_self_nonneg⟩

/-- The Hodge form is positive semidefinite, in Mathlib's packaging. -/
theorem isPosSemidef_hodgeForm (P : Polarization hℂ hs) : P.hodgeForm.IsPosSemidef where
  isSymm := P.isSymm_hodgeForm
  isNonneg := P.isNonneg_hodgeForm

/-- The Hodge form vanishes on the diagonal only at zero. -/
@[simp]
theorem hodgeForm_self_eq_zero_iff (P : Polarization hℂ hs) {x : Vℂ} :
    P.hodgeForm x x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hx
  exact absurd h (P.hodgeForm_self_pos hx).ne'

/-- A positive definite form is nondegenerate: a vector orthogonal to everything is orthogonal to
itself. -/
theorem hodgeForm_nondegenerate (P : Polarization hℂ hs) :
    LinearMap.Nondegenerate P.hodgeForm :=
  ⟨fun x hx ↦ P.hodgeForm_self_eq_zero_iff.mp (hx x),
    fun y hy ↦ P.hodgeForm_self_eq_zero_iff.mp (hy y)⟩

end Polarization

/-- The Hodge form of the polarized Tate structure `ℤ(m)` is the standard Hermitian form of the
complex line: its Weil operator is the identity and its conjugation is complex conjugation. -/
@[simp]
theorem tate_hodgeForm_apply (m : ℤ) (x y : ℂ) :
    (tatePolarization m).hodgeForm x y = starRingEnd ℂ x * y := by
  rw [Polarization.hodgeForm_apply, latticeConj_tateLatticeMap, tate_weilOperator,
    tatePolarization_Q]
  simp

end TauCeti.Hodge
