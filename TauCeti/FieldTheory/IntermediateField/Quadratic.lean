/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Quadratic normal forms in intermediate fields

This file contains normal-form lemmas for adjoining one element whose square already lies in an
intermediate field, together with the corresponding quadratic finrank and degree-doubling API.
The finrank lemmas live here because they combine the normal form with intermediate-field
scalar restriction for one quadratic tower step.

## Provenance

`exists_add_mul_of_mem_sup_adjoin_sq` is migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where it was a
step in the square-class descent for multiquadratic fields; here it is stated for an arbitrary
field extension.
-/

public section

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `a` and `b` lie in `F`, then `a + b * x` lies in `F ⊔ K⟮x⟯`. -/
theorem mem_sup_adjoin_sq_of_exists {F : IntermediateField K L} {x y : L}
    (hy : ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x) :
    y ∈ F ⊔ IntermediateField.adjoin K {x} := by
  rcases hy with ⟨a, b, ha, hb, rfl⟩
  have hF : F ≤ F ⊔ IntermediateField.adjoin K {x} := le_sup_left
  have hx : IntermediateField.adjoin K {x} ≤ F ⊔ IntermediateField.adjoin K {x} :=
    le_sup_right
  exact add_mem (hF ha)
    (mul_mem (hF hb) (hx (IntermediateField.mem_adjoin_of_mem K (Set.mem_singleton x))))

/-- If `x² ∈ F`, then `x` is integral over `F` (it is a root of `X² - x²`). -/
private theorem isIntegral_of_sq_mem {F : IntermediateField K L} {x : L} (hx2 : x ^ 2 ∈ F) :
    IsIntegral F x := by
  have hx2_int : IsIntegral F (x ^ 2) := by
    simpa using isIntegral_algebraMap (R := F) (A := L) (x := (⟨x ^ 2, hx2⟩ : F))
  exact IsIntegral.of_pow (by norm_num : 0 < 2) hx2_int

/-- If `x² ∈ F`, then the minimal polynomial of `x` over `F` has degree at most `2`, since it
divides the nonzero polynomial `X² - x²`. -/
private theorem minpoly_natDegree_le_two_of_sq_mem {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) : (minpoly F x).natDegree ≤ 2 := by
  have hpoly_ne : ((Polynomial.X : Polynomial F) ^ 2 - Polynomial.C ⟨x ^ 2, hx2⟩) ≠ 0 := by
    intro hzero; have hdeg := congrArg Polynomial.natDegree hzero; norm_num at hdeg
  have hdeg := minpoly.degree_le_of_ne_zero F x hpoly_ne (by simp)
  rw [Polynomial.degree_X_pow_sub_C (n := 2) (by norm_num)] at hdeg
  exact Polynomial.natDegree_le_iff_degree_le.mpr hdeg

/-- If `x² ∈ F`, every element of `F ⊔ K⟮x⟯` has the form `a + b * x` with
`a, b ∈ F`. -/
theorem exists_add_mul_of_mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x := by
  -- Since `x² ∈ F`, the element `x` is integral over `F` and the minimal polynomial of `x`
  -- over `F` divides `X² - x²`, so `F⟮x⟯` carries a power basis `1, x` of dimension `≤ 2`.
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  -- View `y` as an element of `F⟮x⟯` and write it on the power basis: `y = c₁ * x + c₀`
  -- with `c₀ c₁ ∈ F`, the coefficients of a polynomial of degree `< dim ≤ 2`.
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L),
    mem_restrictScalars] at hy
  set pb := IntermediateField.adjoin.powerBasis hx_int with hpb
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨y, hy⟩
  have hdim : pb.dim ≤ 2 := by
    rw [hpb, IntermediateField.adjoin.powerBasis_dim]
    exact minpoly_natDegree_le_two_of_sq_mem hx2
  have hfle : f.natDegree ≤ 1 := by
    have := hfdeg.trans_le hdim
    omega
  rw [hpb, Polynomial.eq_X_add_C_of_natDegree_le_one hfle,
    IntermediateField.adjoin.powerBasis_gen] at hf
  refine ⟨algebraMap F L (f.coeff 0), algebraMap F L (f.coeff 1),
    (f.coeff 0).2, (f.coeff 1).2, ?_⟩
  have hfeq := congrArg (Subtype.val (p := (· ∈ adjoin F {x}))) hf
  rw [AdjoinSimple.coe_aeval_gen_apply] at hfeq
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X] at hfeq
  linear_combination hfeq

/-- Membership in `F ⊔ K⟮x⟯`, for `x² ∈ F`, is equivalent to having the form `a + b * x`
with `a, b ∈ F`. -/
@[simp]
theorem mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) {y : L} :
    y ∈ F ⊔ IntermediateField.adjoin K {x} ↔
      ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x :=
  ⟨exists_add_mul_of_mem_sup_adjoin_sq hx2, mem_sup_adjoin_sq_of_exists⟩

omit K [Field K] [Algebra K L] in
/-- **Vanishing cross term in a quadratic step.** If `x² ∈ F` but `x ∉ F`, then a square
`(a + b * x) ^ 2` of a normal-form element that lands back in `F` has no cross term: `a * b = 0`.
This is where characteristic not two enters, through `2 ≠ 0` in `L`. It holds for an arbitrary
subfield `F` of `L`; no ambient base field or algebra tower is needed. -/
theorem mul_eq_zero_of_add_mul_sq_mem {S : Type*} [SetLike S L] [SubfieldClass S L] {F : S} {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) [NeZero (2 : L)] {a b : L}
    (ha : a ∈ F) (hb : b ∈ F) (hab_mem : (a + b * x) ^ 2 ∈ F) :
    a * b = 0 := by
  by_contra hab
  refine hxF ?_
  -- Expanding `(a + b * x) ^ 2` and using `x² ∈ F`, the cross term `2 * a * b * x` lies in `F`.
  have hcross_mem : 2 * a * b * x ∈ F := by
    have hEq : 2 * a * b * x = (a + b * x) ^ 2 - a ^ 2 - b ^ 2 * x ^ 2 := by ring
    rw [hEq]
    exact sub_mem (sub_mem hab_mem (pow_mem ha 2)) (mul_mem (pow_mem hb 2) hx2)
  -- The coefficient `2 * a * b` lies in `F` and is nonzero, so `x` is recovered by dividing it out.
  have hcoef_mem : 2 * a * b ∈ F := mul_mem (mul_mem (natCast_mem (s := F) 2) ha) hb
  have hcoef_ne : 2 * a * b ≠ 0 := by
    have h2ab : (2 : L) * (a * b) ≠ 0 := mul_ne_zero (NeZero.ne (2 : L)) hab
    simpa [mul_assoc] using h2ab
  have hxeq : (2 * a * b)⁻¹ * (2 * a * b * x) = x := by
    rw [← mul_assoc, inv_mul_cancel₀ hcoef_ne, one_mul]
  rw [← hxeq]
  exact mul_mem (inv_mem hcoef_mem) hcross_mem

/-- If `x² ∈ F` but `x ∉ F`, then the simple extension `F⟮x⟯` has finrank two over `F`. -/
theorem finrank_adjoin_simple_eq_two_of_sq_mem_notMem (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank F (IntermediateField.adjoin F {x}) = 2 := by
  have hx_int : IsIntegral F x := isIntegral_of_sq_mem hx2
  have hfin := IntermediateField.adjoin.finrank hx_int
  have hle : (minpoly F x).natDegree ≤ 2 := minpoly_natDegree_le_two_of_sq_mem hx2
  have hpos : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx_int
  have hne1 : (minpoly F x).natDegree ≠ 1 := by
    intro hdeg1
    have hfin1 : Module.finrank F (IntermediateField.adjoin F {x}) = 1 := by
      simpa [hfin] using hdeg1
    have hxbot : x ∈ (⊥ : IntermediateField F L) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff).mp hfin1
    rw [IntermediateField.mem_bot] at hxbot
    obtain ⟨y, hy⟩ := hxbot
    exact hxF (hy ▸ y.2)
  omega

-- `restrictScalars` keeps the same carrier and inherited `K`-module structure, so a `K`-finrank is
-- unchanged by it. Mathlib's `Submodule.restrictScalarsEquiv` proves the analogue for submodules,
-- but only as an `F`-linear equivalence, and restricting it to `K` needs `IsScalarTower`/
-- `CompatibleSMul` instances that the tower `K → F → F⟮x⟯` does not provide for
-- `Submodule.restrictScalars K`; so we name the definitional equality here instead.
private theorem finrank_restrictScalars_eq (F : IntermediateField K L)
    (E : IntermediateField F L) :
    Module.finrank K (E.restrictScalars K) = Module.finrank K E := rfl

/-- If `x² ∈ F` but `x ∉ F`, then adjoining `x` doubles the degree:
`[F ⊔ K⟮x⟯ : K] = 2 · [F : K]`. -/
theorem finrank_sup_adjoin_simple_eq_mul_two (F : IntermediateField K L) {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) :
    Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K F * 2 := by
  have hL : (IntermediateField.adjoin F {x}).restrictScalars K
      = F ⊔ IntermediateField.adjoin K {x} :=
    IntermediateField.restrictScalars_adjoin_eq_sup K F ({x} : Set L)
  have hfinL : Module.finrank F (IntermediateField.adjoin F {x}) = 2 :=
    finrank_adjoin_simple_eq_two_of_sq_mem_notMem F hx2 hxF
  calc Module.finrank K ((F ⊔ IntermediateField.adjoin K {x}) : IntermediateField K L)
      = Module.finrank K ((IntermediateField.adjoin F {x}).restrictScalars K) := by rw [hL]
    _ = Module.finrank K (IntermediateField.adjoin F {x}) := by
        rw [finrank_restrictScalars_eq]
    _ = Module.finrank K F * Module.finrank F (IntermediateField.adjoin F {x}) := by
        rw [Module.finrank_mul_finrank]
    _ = Module.finrank K F * 2 := by rw [hfinL]

/-- **Same square class from a shared simple quadratic field.** Let `x` and `y` be square roots of
`a` and `c` in a field extension `L / K` with `2 ≠ 0`. If `x ∉ K` and the simple extensions `K(x)`
and `K(y)` coincide, then `a · c` is a square in `K`: two square roots generate the same quadratic
subfield only when their radicands lie in the same square class. -/
theorem isSquare_mul_of_adjoin_simple_eq [NeZero (2 : K)] {a c : K} {x y : L}
    (hx : x ^ 2 = algebraMap K L a) (hy : y ^ 2 = algebraMap K L c)
    (hxb : x ∉ (⊥ : IntermediateField K L))
    (hxy : IntermediateField.adjoin K {x} = IntermediateField.adjoin K {y}) :
    IsSquare (a * c) := by
  haveI : NeZero (2 : L) :=
    NeZero.nat_of_injective (n := 2) (f := algebraMap K L) (algebraMap K L).injective
  -- Write `y` in the base-field normal form `algebraMap p₀ + algebraMap q₀ * x`.
  have hx2 : x ^ 2 ∈ (⊥ : IntermediateField K L) := by
    rw [hx]; exact IntermediateField.algebraMap_mem _ _
  have hy_mem : y ∈ (⊥ : IntermediateField K L) ⊔ IntermediateField.adjoin K {x} := by
    rw [bot_sup_eq, hxy]; exact IntermediateField.mem_adjoin_simple_self K y
  obtain ⟨p, q, hp, hq, hy_eq⟩ := (mem_sup_adjoin_sq hx2).mp hy_mem
  rw [IntermediateField.mem_bot] at hp hq
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  -- The square `y² = c` lands in `⊥`, so the shared cross-term lemma forces `p₀ * q₀ = 0`.
  have hab_mem :
      (algebraMap K L p₀ + algebraMap K L q₀ * x) ^ 2 ∈ (⊥ : IntermediateField K L) := by
    rw [← hy_eq, hy]; exact IntermediateField.algebraMap_mem _ _
  have hpq : algebraMap K L p₀ * algebraMap K L q₀ = 0 :=
    mul_eq_zero_of_add_mul_sq_mem hx2 hxb (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.algebraMap_mem _ _) hab_mem
  have hpq0 : p₀ * q₀ = 0 := by
    apply FaithfulSMul.algebraMap_injective K L
    rw [map_mul, map_zero]
    exact hpq
  -- The vanishing cross term forces `c = p₀² + q₀² * a`.
  have hc : c = p₀ ^ 2 + q₀ ^ 2 * a := by
    have hy2 : (algebraMap K L p₀ + algebraMap K L q₀ * x) ^ 2 = algebraMap K L c := by
      rw [← hy_eq]; exact hy
    apply FaithfulSMul.algebraMap_injective K L
    rw [map_add, map_pow, map_mul, map_pow]
    linear_combination -hy2 + (algebraMap K L q₀) ^ 2 * hx + 2 * x * hpq
  -- Either `p₀ = 0`, giving `a * c = (q₀ * a)²`, or `q₀ = 0`, forcing `x ∈ K`, a contradiction.
  rcases mul_eq_zero.mp hpq0 with hp0 | hq0
  · -- `p₀ = 0`, so `c = q₀² * a` and `a * c = (q₀ * a)²`.
    exact ⟨q₀ * a, by rw [hc, hp0]; ring⟩
  · -- `q₀ = 0` puts `y` in the base field, forcing `x ∈ K`, a contradiction.
    refine absurd ?_ hxb
    have hyb : y ∈ (⊥ : IntermediateField K L) := by
      rw [hy_eq, hq0, map_zero, zero_mul, add_zero]
      exact IntermediateField.algebraMap_mem _ _
    exact IntermediateField.adjoin_simple_eq_bot_iff.mp
      (hxy.trans (IntermediateField.adjoin_simple_eq_bot_iff.mpr hyb))

end TauCeti.IntermediateField
