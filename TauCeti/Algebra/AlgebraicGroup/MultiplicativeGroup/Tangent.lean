/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic

/-!
# The tangent Lie algebra of the multiplicative group

The tangent space at the identity of the multiplicative group is one-dimensional. A tangent
derivation of the Laurent polynomial Hopf algebra `R[T;T⁻¹]` is determined by its value on `T`,
and every value occurs. The resulting linear equivalence with the coefficient algebra `B`
identifies the tangent Lie bracket with the zero bracket.

## Main declarations

* `TauCeti.MultiplicativeGroup.tangentLinearEquiv`: the tangent space of `𝔾ₘ` is linearly
  equivalent to `B`.
* `TauCeti.MultiplicativeGroup.tangent_bracket_eq_zero`: the tangent Lie bracket of `𝔾ₘ`
  vanishes.

## References

The construction follows the formal pattern of
`TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent`.
Laurent-polynomial induction and the formulas for the counit and comultiplication of `T` come from
Mathlib's `Mathlib.Algebra.Polynomial.Laurent` and
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`.

This realizes the `𝔾ₘ` item in the ReductiveGroups roadmap's "Worked examples" section using
its Layer 2 tangent/Lie algebra infrastructure.
-/

public section

open scoped LaurentPolynomial

namespace TauCeti

namespace MultiplicativeGroup

open TauCeti.Bialgebra TrivSqZeroExt WithConv

universe u w

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {B : Type w} [CommRing B] [Algebra R B]

local notation "H" => R[T;T⁻¹]
local notation "C" => CounitAlgebra R H B

private lemma derivation_T_add (d : Derivation R H C) (m n : ℤ) :
    d (LaurentPolynomial.T (m + n)) =
      d (LaurentPolynomial.T m) + d (LaurentPolynomial.T n) := by
  rw [LaurentPolynomial.T_add, Derivation.leibniz]
  simp only [Algebra.smul_def, CounitAlgebra.algebraMap_apply,
    LaurentPolynomial.counit_T, map_one]
  -- Simplification leaves `1 : B` multiplying a value in the coefficient synonym `C`, so the
  -- target is not type-correct at implicit transparency and no propositional rewrite applies.
  change (1 : C) * d (LaurentPolynomial.T n) +
      (1 : C) * d (LaurentPolynomial.T m) =
    d (LaurentPolynomial.T m) + d (LaurentPolynomial.T n)
  simp only [one_mul, add_comm]

/-- Two tangent derivations of the Laurent polynomial algebra are equal if they agree on `T`. -/
@[ext]
theorem derivation_ext {d e : Derivation R H C}
    (h : d (LaurentPolynomial.T 1) = e (LaurentPolynomial.T 1)) : d = e := by
  have hT : ∀ n : ℤ, d (LaurentPolynomial.T n) = e (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n hn =>
        rw [derivation_T_add d n 1, derivation_T_add e n 1, hn, h]
    | pred n hn =>
        calc
          d (LaurentPolynomial.T (-(n : ℤ) - 1)) =
              d (LaurentPolynomial.T (-(n : ℤ))) - d (LaurentPolynomial.T 1) := by
                rw [eq_sub_iff_add_eq, ← derivation_T_add]
                norm_num
          _ = e (LaurentPolynomial.T (-(n : ℤ))) - e (LaurentPolynomial.T 1) := by
                rw [hn, h]
          _ = e (LaurentPolynomial.T (-(n : ℤ) - 1)) := by
                rw [sub_eq_iff_eq_add, ← derivation_T_add]
                norm_num
  apply Derivation.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n a =>
      rw [Derivation.leibniz, Derivation.leibniz, hT]
      rw [LaurentPolynomial.C_eq_algebraMap, Derivation.map_algebraMap,
        Derivation.map_algebraMap]

private noncomputable def tangentCoordinate : Derivation R H C →ₗ[B] B where
  toFun d := CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1))
  map_add' _d _e := (CounitAlgebra.algEquivSelf R H B).map_add _ _
  map_smul' b d := algEquivSelf_derivation_smul_apply b d _

private lemma tangentCoordinate_apply (d : Derivation R H C) :
    tangentCoordinate d =
      CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1)) :=
  rfl

private noncomputable def infinitesimalUnit (c : C) : (DualNumber C)ˣ :=
  have h : IsUnit (inl 1 + inr c : DualNumber C) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp
  h.unit

private lemma infinitesimalUnit_map_fst (c : C) :
    Units.map (fstHom R C C).toMonoidHom (infinitesimalUnit c) = 1 := by
  ext
  simp [infinitesimalUnit]

private theorem tangentCoordinate_surjective :
    Function.Surjective (tangentCoordinate (R := R) (B := B)) := by
  intro b
  let c : C := (CounitAlgebra.algEquivSelf R H B).symm b
  let g : (DualNumber C)ˣ := infinitesimalUnit c
  let q : WithConv (H →ₐ[R] DualNumber C) :=
    (pointsMulEquiv (R := R) (A := DualNumber C)).symm g
  have hq : q ∈ tangentKer R H B := by
    rw [tangentKer_def, MonoidHom.mem_ker, dualNumberReduction_def]
    apply (pointsMulEquiv (R := R) (A := C)).injective
    rw [pointsMulEquiv_mapValue]
    simp only [q, MulEquiv.apply_symm_apply, map_one]
    exact infinitesimalUnit_map_fst c
  let d : Derivation R H C :=
    ((derivationMulEquivTangentKer R H B).symm ⟨q, hq⟩).toAdd
  refine ⟨d, ?_⟩
  have hd : d (LaurentPolynomial.T 1) = snd (q.ofConv (LaurentPolynomial.T 1)) := by
    dsimp only [d]
    rw [derivationMulEquivTangentKer_symm_apply]
  rw [tangentCoordinate_apply, hd]
  have hval : q.ofConv (LaurentPolynomial.T 1) = (g : DualNumber C) := by
    rw [← unitOfPoint_val (R := R) (A := DualNumber C)]
    exact congrArg Units.val
      ((pointsMulEquiv (R := R) (A := DualNumber C)).apply_symm_apply g)
  rw [hval]
  simp only [g, infinitesimalUnit, IsUnit.unit_spec, snd_add, snd_inl, snd_inr, zero_add, c]
  exact (CounitAlgebra.algEquivSelf R H B).apply_symm_apply b

/-- **The tangent space at the identity of `𝔾ₘ` is one-dimensional.** The equivalence sends
a counit-valued derivation to its value on the Laurent generator `T`. -/
noncomputable def tangentLinearEquiv : Derivation R H C ≃ₗ[B] B :=
  LinearEquiv.ofBijective tangentCoordinate
    ⟨fun _ _ h => derivation_ext ((CounitAlgebra.algEquivSelf R H B).injective h),
      tangentCoordinate_surjective⟩

/-- The tangent equivalence evaluates a derivation on the Laurent generator `T`. -/
@[simp]
theorem tangentLinearEquiv_apply (d : Derivation R H C) :
    tangentLinearEquiv d =
      CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1)) := by
  rfl

/-- The derivation corresponding to `b : B` takes the Laurent generator `T` to `b`. -/
@[simp]
theorem tangentLinearEquiv_symm_apply_T (b : B) :
    (tangentLinearEquiv (R := R) (B := B)).symm b (LaurentPolynomial.T 1) = b := by
  have h : CounitAlgebra.algEquivSelf R H B
      ((tangentLinearEquiv (R := R) (B := B)).symm b (LaurentPolynomial.T 1)) = b := by
    simpa only [tangentLinearEquiv_apply] using
      (tangentLinearEquiv (R := R) (B := B)).apply_symm_apply b
  have h' := congrArg (CounitAlgebra.algEquivSelf R H B).symm h
  simpa only [AlgEquiv.symm_apply_apply, CounitAlgebra.algEquivSelf_symm_apply] using h'

/-- **The tangent Lie algebra of `𝔾ₘ` is abelian.** -/
@[simp]
theorem tangent_bracket_eq_zero (d e : Derivation R H C) : ⁅d, e⁆ = 0 := by
  apply derivation_ext
  rw [TauCeti.Derivation.bracket_apply, LaurentPolynomial.comul_T]
  simp [mul_comm]

end

end MultiplicativeGroup

end TauCeti
