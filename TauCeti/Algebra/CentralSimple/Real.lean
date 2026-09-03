/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.CentralSimple.Degree` is imported publicly: `TauCeti.Algebra.deg` occurs in the
-- degree bound below, and `TauCeti.Algebra.deg_sq` is what turns that bound into a dimension
-- count. It re-exports `Mathlib.Algebra.Central.Basic`, hence `Algebra.IsCentral`.
public import TauCeti.Algebra.CentralSimple.Degree
-- `Mathlib.Algebra.Quaternion` is imported publicly because `ℍ[ℝ]` occurs in the statement of the
-- classification.
public import Mathlib.Algebra.Quaternion
-- Non-public: the maximal subfield supplying the degree bound
-- (`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`), the quaternion basis that builds
-- the isomorphism (`QuaternionAlgebra.Basis`), and the classification of the algebraic extensions
-- of `ℝ` are all used only inside proofs.
import TauCeti.Algebra.CentralSimple.MaximalSubfield
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Frobenius' theorem: the real central division algebras are `ℝ` and `ℍ[ℝ]`

A finite-dimensional division algebra over `ℝ` whose centre is `ℝ` is `ℝ`-isomorphic either to `ℝ`
itself or to the Hamilton quaternions `ℍ[ℝ]`. This is the classification the Brauer group of `ℝ`
needs: it says that the two Brauer classes already known -- the identity and the class of `ℍ[ℝ]` --
are all there are.

The proof runs in three steps, and only the first uses anything about central simple algebras.

*The degree is at most two.* A central division algebra has a subfield of degree `deg ℝ D`
(`TauCeti.Algebra.exists_subalgebra_isField_finrank_eq_deg`), and a finite extension of `ℝ` is `ℝ`
or `ℂ` (Mathlib's `Real.nonempty_algEquiv_or`), so that degree is `1` or `2` and `finrank ℝ D` is
`1` or `4`.

*Every element satisfies a real quadratic.* For `y : D` the subalgebra `ℝ[y]` is commutative and
finite-dimensional over `ℝ`, hence a field, hence `ℝ` or `ℂ` again; in either case `y * y` is a real
combination of `1` and `y` (`TauCeti.exists_mul_self_eq_algebraMap_add_smul`). Completing the square
and rescaling turn any `y` outside `ℝ` into an `i` with `i * i = -1`
(`TauCeti.exists_mul_self_eq_neg_one`).

*A second imaginary unit anticommutes with the first.* Centrality gives an `x` not commuting with
`i`, and then `j = x + i * x * i` satisfies `i * j = i * x - x * i = -(j * i)`, so it is nonzero and
anticommutes with `i`. Anticommutation forces `j * j` to be a real scalar, necessarily negative
because a nonnegative one would factor in the division ring `D` and put `j` in `ℝ`; rescaling `j`
makes `j * j = -1`. The pair `(i, j)` is a `QuaternionAlgebra.Basis`, so `ℍ[ℝ]` maps to `D`, and the
map is injective because `ℍ[ℝ]` is a division ring and surjective because both sides have
dimension `4`.

Beyond the degree bound no maximal subfield, centralizer theorem or Skolem-Noether argument is
needed; the rest is the elementary Frobenius argument.

## Main results

* `TauCeti.exists_mul_self_eq_algebraMap_add_smul`: every element of a finite-dimensional real
  algebra that is a domain satisfies a monic real quadratic.
* `TauCeti.exists_mul_self_eq_neg_one`: such an algebra other than `ℝ` contains a square root
  of `-1`.
* `TauCeti.exists_mul_self_eq_neg_one_and_mul_eq_neg_mul`: a square root of `-1` that is not
  central has an anticommuting partner, again a square root of `-1`.
* `TauCeti.Algebra.deg_le_two`: **a real central division algebra has degree at most `2`.**
* `TauCeti.nonempty_algEquiv_quaternion_of_finrank_eq_four`: a four-dimensional real central
  division algebra is `ℍ[ℝ]`.
* `TauCeti.nonempty_algEquiv_real_or_quaternion`: **Frobenius' theorem**, a real central division
  algebra is `ℝ` or `ℍ[ℝ]`.

## Implementation notes

Mathlib's `NormedAlgebra.Real.exists_isMonicOfDegree_two_and_aeval_eq_zero` is the same quadratic
relation, but it is stated for an element of a normed `ℝ`-algebra whose norm is multiplicative.
That hypothesis is not available here, `D` carrying no norm; the relation is therefore reproved
from the finite-dimensionality of `ℝ[y]`.

The three quadratic lemmas are stated for a domain rather than a division ring: no inverse in `D`
is ever taken, only inverses of real scalars, so `[Ring D] [IsDomain D]` is what the arguments
use. The division algebras of Frobenius' theorem supply those instances.

## References

This is the classification of "the finite-dimensional real division algebras with center `ℝ`"
listed as a prerequisite of the real base field target in Layer 6 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13, and P. Gille, T. Szamuely, *Central
Simple Algebras and Galois Cohomology*, CUP (2006), §1.1.
-/

public section

namespace TauCeti

open Module

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-! ### Real quadratics -/

section Quadratic

variable {D : Type*} [Ring D] [IsDomain D] [Algebra ℝ D] [FiniteDimensional ℝ D]

/-- **Every element of a finite-dimensional real algebra that is a domain satisfies a monic real
quadratic**: `y * y = a + b * y` for real `a` and `b`.

The subalgebra `ℝ[y]` is a commutative domain of finite dimension over `ℝ`, hence a field, hence
`ℝ`-isomorphic to `ℝ` or to `ℂ` by Mathlib's `Real.nonempty_algEquiv_or`. In the first case `y` is
already real; in the second `y` corresponds to a complex number `z`, which satisfies
`z * z = -normSq z + (2 * z.re) * z`. -/
theorem exists_mul_self_eq_algebraMap_add_smul (y : D) :
    ∃ a b : ℝ, y * y = algebraMap ℝ D a + b • y := by
  have hy : y ∈ Algebra.adjoin ℝ ({y} : Set D) := Algebra.self_mem_adjoin_singleton ℝ y
  set S := Algebra.adjoin ℝ ({y} : Set D)
  have hfield : IsField S := IsField.of_isDomain_of_finite ℝ S
  let _ : Field S := hfield.toField
  have _ : Algebra.IsAlgebraic ℝ S := Algebra.IsAlgebraic.of_finite ℝ S
  -- It suffices to prove the identity inside `S` and push it forward along the algebra map
  -- `S.val : S →ₐ[ℝ] D`, which is the inclusion.
  suffices h : ∃ a b : ℝ, (⟨y, hy⟩ : S) * ⟨y, hy⟩ = algebraMap ℝ S a + b • ⟨y, hy⟩ by
    obtain ⟨a, b, hab⟩ := h
    refine ⟨a, b, ?_⟩
    simpa only [map_mul, map_add, map_smul, AlgHom.commutes, Subalgebra.coe_val] using
      congrArg S.val hab
  rcases _root_.Real.nonempty_algEquiv_or S with hS | hS
  · -- `S ≃ₐ[ℝ] ℝ`: the element is a real scalar, so the linear coefficient is `0`.
    have e := hS.some
    refine ⟨e ⟨y, hy⟩ * e ⟨y, hy⟩, 0, ?_⟩
    -- An `ℝ`-algebra map to `ℝ` is injective, and it sends both sides to `e ⟨y, hy⟩`.
    have hyS : (⟨y, hy⟩ : S) = algebraMap ℝ S (e ⟨y, hy⟩) :=
      e.injective (by rw [AlgEquiv.commutes, Algebra.algebraMap_self_apply])
    rw [zero_smul, add_zero, map_mul]
    exact congrArg₂ (· * ·) hyS hyS
  · -- `S ≃ₐ[ℝ] ℂ`: a complex number is a root of `X ^ 2 - 2 * re z * X + normSq z`.
    have e := hS.some
    refine ⟨-Complex.normSq (e ⟨y, hy⟩), 2 * (e ⟨y, hy⟩).re, ?_⟩
    have hz : e ⟨y, hy⟩ * e ⟨y, hy⟩ =
        algebraMap ℝ ℂ (-Complex.normSq (e ⟨y, hy⟩)) + (2 * (e ⟨y, hy⟩).re) • e ⟨y, hy⟩ := by
      apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
    apply e.injective
    rw [map_mul, map_add, map_smul, AlgEquiv.commutes]
    exact hz

omit [FiniteDimensional ℝ D] in
/-- **A non-real element whose square is a real scalar rescales to a square root of `-1`**: if
`u * u = algebraMap ℝ D r` and `u` is not itself a real scalar, then `c • u` squares to `-1` for
some real `c`.

The scalar `r` is negative, since `r ≥ 0` would make `u` and the scalar `√r` two commuting elements
with the same square, which in a domain forces `u = ±√r`
(`Commute.mul_self_eq_mul_self_iff`) and so puts `u` in `ℝ`. Then `c = (√(-r))⁻¹` normalises the
square.

This is the private engine shared by the two square roots of `-1` built below,
`TauCeti.exists_mul_self_eq_neg_one` and
`TauCeti.exists_mul_self_eq_neg_one_and_mul_eq_neg_mul`. -/
private theorem exists_smul_mul_self_eq_neg_one {u : D} {r : ℝ}
    (hu : u * u = algebraMap ℝ D r) (hbot : u ∉ (⊥ : Subalgebra ℝ D)) :
    ∃ c : ℝ, (c • u) * (c • u) = -1 := by
  -- A nonnegative square would factor and force `u` into `ℝ`.
  have hr : r < 0 := by
    by_contra hge
    have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (not_lt.1 hge)
    -- `u` and the scalar `√r` commute and have the same square, so `u = ±√r`.
    have hcomm : Commute u (algebraMap ℝ D (Real.sqrt r)) := (Algebra.commutes _ _).symm
    have hsquares : u * u = algebraMap ℝ D (Real.sqrt r) * algebraMap ℝ D (Real.sqrt r) := by
      rw [hu, ← map_mul, hs]
    rcases hcomm.mul_self_eq_mul_self_iff.1 hsquares with h0 | h0
    · exact hbot (h0 ▸ Subalgebra.algebraMap_mem _ _)
    · exact hbot (h0 ▸ neg_mem (Subalgebra.algebraMap_mem _ _))
  -- Rescale so that the square becomes `-1`.
  have hsq : Real.sqrt (-r) * Real.sqrt (-r) = -r := Real.mul_self_sqrt (by linarith)
  have hne : Real.sqrt (-r) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hscal : (Real.sqrt (-r))⁻¹ * (Real.sqrt (-r))⁻¹ * r = -1 := by
    field_simp
    linarith [hsq]
  exact ⟨(Real.sqrt (-r))⁻¹, by
    rw [smul_mul_smul_comm, hu, Algebra.smul_def, ← map_mul, hscal, map_neg, map_one]⟩

/-- **A finite-dimensional real algebra that is a domain and is not `ℝ` contains a square root
of `-1`.**

Take any `y` outside the copy of `ℝ`, write `y * y = a + b * y`, and complete the square: the
element `u = y - b / 2` has `u * u` a real scalar, and `u` is again outside `ℝ`, so
`exists_smul_mul_self_eq_neg_one` rescales it to a square root of `-1`. -/
theorem exists_mul_self_eq_neg_one (h : finrank ℝ D ≠ 1) : ∃ i : D, i * i = -1 := by
  -- Some `y` is not a real scalar.
  obtain ⟨y, hy⟩ : ∃ y : D, y ∉ (⊥ : Subalgebra ℝ D) := by
    by_contra hc
    refine h (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 (top_le_iff.1 fun x _ ↦ ?_))
    by_contra hx
    exact hc ⟨x, hx⟩
  obtain ⟨a, b, hab⟩ := exists_mul_self_eq_algebraMap_add_smul y
  obtain ⟨u, hudef⟩ : ∃ u : D, u = y - algebraMap ℝ D (b / 2) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = a + b / 2 * (b / 2) := ⟨_, rfl⟩
  have hcy : algebraMap ℝ D (b / 2) * y = (b / 2) • y := (Algebra.smul_def _ _).symm
  have hyc : y * algebraMap ℝ D (b / 2) = (b / 2) • y := by rw [← Algebra.commutes, hcy]
  have hu : u * u = algebraMap ℝ D r :=
    calc u * u
        = y * y - y * algebraMap ℝ D (b / 2) - algebraMap ℝ D (b / 2) * y
            + algebraMap ℝ D (b / 2) * algebraMap ℝ D (b / 2) := by
          rw [hudef]; noncomm_ring
      _ = algebraMap ℝ D a + b • y - (b / 2) • y - (b / 2) • y
            + algebraMap ℝ D (b / 2 * (b / 2)) := by rw [hab, hyc, hcy, map_mul]
      _ = algebraMap ℝ D r := by rw [hrdef, map_add]; module
  -- `u` is not a real scalar either, since `y = u + b / 2` is not.
  have hune : u ∉ (⊥ : Subalgebra ℝ D) := fun hmem ↦ by
    have hyu : y = u + algebraMap ℝ D (b / 2) := by rw [hudef]; abel
    exact hy (hyu ▸ add_mem hmem (Subalgebra.algebraMap_mem _ _))
  obtain ⟨c, hc⟩ := exists_smul_mul_self_eq_neg_one hu hune
  exact ⟨c • u, hc⟩

/-- **A square root of `-1` that does not commute with everything has an anticommuting partner**:
if `i * i = -1` and some `x` fails to commute with `i`, then there is a `j` with `j * j = -1` and
`i * j = -(j * i)`.

The partner is built from `x` as follows. The element `j₀ = x + i * x * i` satisfies
`i * j₀ = i * x - x * i = -(j₀ * i)`, so it is nonzero and anticommutes with `i`. Its square
commutes with `i`, so in the quadratic `j₀ * j₀ = a + b * j₀` the linear coefficient `b` must
vanish, `i * j₀` being nonzero. So `j₀ * j₀` is a real scalar while `j₀` itself is not, `j₀` being a
scalar only if it commuted with `i`; `exists_smul_mul_self_eq_neg_one` then rescales `j₀` to a
square root of `-1`, and rescaling keeps the anticommutation. -/
theorem exists_mul_self_eq_neg_one_and_mul_eq_neg_mul {i x : D} (hi : i * i = -1)
    (hx : x * i ≠ i * x) : ∃ j : D, j * j = -1 ∧ i * j = -(j * i) := by
  -- Two elements below come out equal to their own negatives; `CharZero.eq_neg_self_iff` then makes
  -- them zero, `D` being of characteristic zero as a faithful `ℝ`-algebra.
  have : CharZero D := Algebra.charZero_of_charZero ℝ D
  obtain ⟨j, hjdef⟩ : ∃ j : D, j = x + i * x * i := ⟨_, rfl⟩
  have hij : i * j = i * x - x * i := by
    have hstep : i * (i * x * i) = -(x * i) := by
      rw [← mul_assoc, ← mul_assoc, hi, neg_one_mul, neg_mul]
    rw [hjdef, mul_add, hstep, ← sub_eq_add_neg]
  have hji : j * i = x * i - i * x := by
    have hstep : i * x * i * i = -(i * x) := by rw [mul_assoc, hi, mul_neg_one]
    rw [hjdef, add_mul, hstep, ← sub_eq_add_neg]
  have hanti : i * j = -(j * i) := by rw [hij, hji]; abel
  have hjii : j * i = -(i * j) := by rw [hij, hji]; abel
  have hijne : i * j ≠ 0 := by rw [hij]; exact sub_ne_zero.2 (Ne.symm hx)
  -- `j * j` commutes with `i`: moving `i` past `j` twice restores the sign.
  have hcomm : i * (j * j) = j * j * i :=
    calc i * (j * j) = i * j * j := (mul_assoc _ _ _).symm
      _ = -(j * i) * j := by rw [hanti]
      _ = -(j * (i * j)) := by rw [neg_mul, mul_assoc]
      _ = -(j * -(j * i)) := by rw [hanti]
      _ = j * j * i := by rw [mul_neg, neg_neg, ← mul_assoc]
  obtain ⟨a, b, hab⟩ := exists_mul_self_eq_algebraMap_add_smul j
  -- Multiplying the quadratic by `i` on either side flips the sign of its linear term, so that
  -- term is its own negative and hence zero; `i * j ≠ 0` then forces `b = 0`.
  have hb : b = 0 := by
    have h1 : i * (j * j) = algebraMap ℝ D a * i + b • (i * j) := by
      rw [hab, mul_add, mul_smul_comm, ← Algebra.commutes]
    have h2 : j * j * i = algebraMap ℝ D a * i - b • (i * j) := by
      rw [hab, add_mul, smul_mul_assoc, hjii, smul_neg, ← sub_eq_add_neg]
    rw [h1, h2, sub_eq_add_neg] at hcomm
    have hz : b • (i * j) = -(b • (i * j)) := add_left_cancel hcomm
    exact (smul_eq_zero.1 (CharZero.eq_neg_self_iff.1 hz)).resolve_right hijne
  rw [hb, zero_smul, add_zero] at hab
  -- A real scalar would commute with `i`, so `j` is not one: `i * j` would be its own negative.
  have hjnotbot : j ∉ (⊥ : Subalgebra ℝ D) := by
    intro hmem
    obtain ⟨t, ht⟩ := Algebra.mem_bot.1 hmem
    have hcomm' : i * j = j * i := by rw [← ht]; exact (Algebra.commutes t i).symm
    exact hijne (CharZero.eq_neg_self_iff.1 (hanti.trans (by rw [hcomm'])))
  -- Rescale so that the square becomes `-1`; rescaling preserves anticommutation with `i`.
  obtain ⟨c, hc⟩ := exists_smul_mul_self_eq_neg_one hab hjnotbot
  exact ⟨c • j, hc, by rw [mul_smul_comm, smul_mul_assoc, hanti, smul_neg]⟩

end Quadratic

/-! ### The degree of a real central division algebra -/

namespace Algebra

/-- **A real central division algebra has degree at most `2`.** It has a subfield of degree
`deg ℝ D`, and a finite extension of `ℝ` is `ℝ` or `ℂ`, so that degree is `1` or `2`. -/
theorem deg_le_two (D : Type*) [DivisionRing D] [Algebra ℝ D] [Algebra.IsCentral ℝ D]
    [FiniteDimensional ℝ D] : deg ℝ D ≤ 2 := by
  obtain ⟨L, hL, hdeg⟩ := exists_subalgebra_isField_finrank_eq_deg ℝ D
  let _ : Field L := hL.toField
  have _ : Algebra.IsAlgebraic ℝ L := Algebra.IsAlgebraic.of_finite ℝ L
  rw [← hdeg]
  rcases _root_.Real.nonempty_algEquiv_or L with hL' | hL'
  · rw [hL'.some.toLinearEquiv.finrank_eq, finrank_self]
    norm_num
  · rw [hL'.some.toLinearEquiv.finrank_eq, Complex.finrank_real_complex]

end Algebra

/-! ### Frobenius' theorem -/

/-- A four-dimensional central `ℝ`-algebra without zero divisors is `ℝ`-isomorphic to the Hamilton
quaternions `ℍ[ℝ]`. Such an algebra is automatically a division algebra, being a domain of finite
dimension over a field.

This is the substantive half of Frobenius' theorem, and the form to reach for once the dimension is
known: `TauCeti.nonempty_algEquiv_real_or_quaternion` re-derives the degree bound and hands back a
disjunction that still has to be eliminated. The absence of zero divisors is what rules out the
split central simple algebra `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem nonempty_algEquiv_quaternion_of_finrank_eq_four (D : Type*) [Ring D] [IsDomain D]
    [Algebra ℝ D] [Algebra.IsCentral ℝ D] (h4 : finrank ℝ D = 4) :
    Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  have : FiniteDimensional ℝ D := .of_finrank_pos (by omega)
  obtain ⟨i, hi⟩ := exists_mul_self_eq_neg_one (D := D) (by omega)
  -- `i` is not central, because `-1` is not a square in `ℝ`.
  have hinotbot : i ∉ (⊥ : Subalgebra ℝ D) := by
    intro hmem
    obtain ⟨t, ht⟩ := Algebra.mem_bot.1 hmem
    have ht2 : algebraMap ℝ D (t * t) = algebraMap ℝ D (-1) := by
      rw [map_mul, ht, hi, map_neg, map_one]
    nlinarith [mul_self_nonneg t, (algebraMap ℝ D).injective ht2]
  obtain ⟨x, hx⟩ : ∃ x : D, x * i ≠ i * x := by
    by_contra hc
    refine hinotbot ?_
    have hmem : i ∈ Subalgebra.center ℝ D := Subalgebra.mem_center_iff.2 fun c ↦ by
      by_contra hcc
      exact hc ⟨c, hcc⟩
    rwa [Algebra.IsCentral.center_eq_bot] at hmem
  -- The anticommuting partner, and the quaternion basis the pair forms.
  obtain ⟨j, hj, hanti⟩ := exists_mul_self_eq_neg_one_and_mul_eq_neg_mul hi hx
  have hanti' : j * i = -(i * j) := by rw [hanti]; abel
  let q : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1) :=
    { i := i, j := j, k := i * j
      i_mul_i := by rw [hi]; simp
      j_mul_j := by rw [hj]; simp
      i_mul_j := rfl
      j_mul_i := by rw [hanti']; simp }
  have f : ℍ[ℝ] →ₐ[ℝ] D := q.liftHom
  have hinj : Function.Injective f := f.toRingHom.injective
  have hfr : finrank ℝ ℍ[ℝ] = finrank ℝ D := by
    rw [_root_.Quaternion.finrank_eq_four, h4]
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hfr).1 hinj
  exact ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

/-- **Frobenius' theorem.** A finite-dimensional division algebra over `ℝ` with centre `ℝ` is
`ℝ`-isomorphic either to `ℝ` or to the Hamilton quaternions `ℍ[ℝ]`.

This is the classification to use when nothing is known about `D` beyond the hypotheses. If
`finrank ℝ D = 4` is already in hand, `TauCeti.nonempty_algEquiv_quaternion_of_finrank_eq_four`
gives the quaternion isomorphism directly, with no disjunction to discharge. -/
theorem nonempty_algEquiv_real_or_quaternion (D : Type*) [DivisionRing D] [Algebra ℝ D]
    [Algebra.IsCentral ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  have hsq : Algebra.deg ℝ D ^ 2 = finrank ℝ D := Algebra.deg_sq ℝ D
  have hcases : Algebra.deg ℝ D = 1 ∨ Algebra.deg ℝ D = 2 := by
    have h1 := Algebra.deg_pos ℝ D
    have h2 := Algebra.deg_le_two D
    omega
  rcases hcases with hd | hd
  · -- `finrank ℝ D = 1`: the base field is everything.
    left
    rw [hd] at hsq
    have h1 : finrank ℝ D = 1 := by omega
    have hbot : (⊥ : Subalgebra ℝ D) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    exact ⟨Subalgebra.topEquiv.symm.trans
      ((Subalgebra.equivOfEq _ _ hbot.symm).trans (Algebra.botEquiv ℝ D))⟩
  · -- `finrank ℝ D = 4`: the quaternions.
    right
    rw [hd] at hsq
    exact nonempty_algEquiv_quaternion_of_finrank_eq_four D (by omega)

end TauCeti
