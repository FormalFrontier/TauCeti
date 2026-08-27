/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.Height.EllipticCurve
public import Mathlib.NumberTheory.Height.Northcott

/-!
# The naïve height on an elliptic curve, and the approximate parallelogram law

For an affine point `P` of a Weierstrass curve over a field `K` with a theory of heights, the
*naïve height* is `h(P) = logHeight (x(P))`, the logarithmic height of the projective
`x`-coordinate `P.xRep`. The main result is the **approximate parallelogram law**,

```text
∃ C, ∀ P Q, |h(P + Q) + h(P - Q) - 2 * (h(P) + h(Q))| ≤ C,
```

which is the height half of the descent proving the Mordell–Weil theorem. Together with the
Northcott property it gives finiteness of the sets of points of bounded naïve height.

The route is the one the source takes: the unordered pair `{P, Q}` is recorded by the symmetric
function `sym2x P Q` of the two `x`-coordinates, the map `{P, Q} ↦ {P + Q, P - Q}` is induced on
those symmetric functions by the quadratic `addSubMap`, and the height of a value of a
homogeneous polynomial map is controlled by the height of its argument. The
`sym2x (P + Q) (P - Q) = addSubMap ∘ sym2x P Q` identity holds only up to a nonzero scalar, which
is harmless because `logHeight` is scale-invariant.

## Main results

* `WeierstrassCurve.Affine.Point.naiveHeight` : the naïve height `logHeight P.xRep`.
* `WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x` : the commuting square above,
  up to a nonzero scalar.
* `WeierstrassCurve.Affine.approx_parallelogram_law` : the approximate parallelogram law.
* `WeierstrassCurve.Affine.finite_naiveHeight_le` : finiteness of points of bounded naïve height.

## Relation to Mathlib, and the duplication risk, weighed

The infrastructure this file stands on is Mathlib's and is *consumed*, not restated:
`Point.xRep` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`), `addSubMap`,
`addSubMapCoeff`, `isHomogeneous_addSubMap` and `sym2x`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean`), the height API
(`Mathlib/NumberTheory/Height/*`), and in particular
`abs_logHeight_addSubMap_sub_two_mul_logHeight_le`, which is the polynomial-map height bound the
parallelogram law consumes.

That last lemma lives in `Mathlib/NumberTheory/Height/EllipticCurve.lean`, a file by the same
author as this development's source, whose module docstring is titled "The naïve height and the
approximate parallelogram law" and whose `TODO` list names three items: define the naïve height,
add the further ingredients for the approximate parallelogram law, and add the law itself. The
source also brackets the `xRep`/duplication block below with a reference to Mathlib PR `#40303`.
So the material here is work the upstream author has slotted but not landed: at the Mathlib
version this repository pins, all of the declarations below are absent, which is why they are
stated here rather than imported.

This is a deliberate, temporary duplication with a defined end. If a later pin bump lands that
upstream work, the superseded declarations here must be deleted and their uses repointed at
Mathlib in the same pull request, per this repository's no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

open Height MvPolynomial Nat

namespace WeierstrassCurve

namespace Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

/-! ### The duplication numerator and denominator -/

/-- The denominator of the duplication formula is a square on the curve. -/
lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

/-- The duplication denominator vanishes exactly at the points of order dividing `2`. -/
lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

variable {F : Type*} [Field F] {W : Affine F}

/-- At a nonsingular point the duplication numerator and denominator do not both vanish. -/
lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! H
    rw [b₂, b₄, b₆] at H
    grobner

section Decidable

variable [DecidableEq F]

/-- The duplication formula for the `x`-coordinate, as a quotient. -/
lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h

/-- The addition formula for the `x`-coordinate at points with distinct `x`, as a quotient. -/
lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
     W.addX xP xQ (W.slope xP xQ yP yQ) =
       ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2 := by
  have hxPQ' : xP - xQ ≠ 0 := by grind only
  simp [addX, slope, hn, div_pow]
  field

/-- The projective `x`-coordinate of `P + P` when `2 • P ≠ 0`. -/
lemma Point.xRep_add_self_of_Y_ne {x y : F} (h : W.Nonsingular x y) (hn : y ≠ W.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]

/-- The projective `x`-coordinate of `P + P` when `P ≠ 0` and `2 • P = 0`. -/
lemma Point.xRep_add_self_of_Y_eq {x y : F} (h : W.Nonsingular x y) (hn : y = W.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]

/-- The projective `x`-coordinate of `P + Q` when `P ≠ ±Q`. -/
lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) - (W.a₂ + xP + xQ) * (xP - xQ) ^2) /
         (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some, addX_of_X_ne hn]

/-- The projective `x`-coordinate of `P - Q` when `P ≠ ±Q`. -/
lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 + W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ)
           - (W.a₂ + xP + xQ) * (xP - xQ) ^2) / (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn, xRep_some,
    addX_of_X_ne hn]
  grind only [negY]

end Decidable

/-- Only finitely many points share a given projective `x`-coordinate. -/
lemma finite_preimage_xRep (x : F) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_ofPred_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

/-- Only finitely many points share a given affine `x`-coordinate. -/
lemma finite_preimage_xRep0 (x : F) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this

/-! ### `sym2x` and the addition-and-multiplication map -/

/-- `sym2x` in terms of the projective `xRep` coordinates. Mathlib provides only the
per-constructor `@[simp]` lemmas and does not expose `sym2x`, so this general unfolding is stated
here. -/
lemma Point.sym2x_eq (P Q : W.Point) :
    P.sym2x Q = ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
      P.xRep 1 * Q.xRep 1] := by
  match P, Q with
  | 0, 0 => simp [Point.xRep_zero]
  | 0, .some x y h => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, 0 => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, .some x' y' h' => simp [Point.xRep_some]

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, sym2x_zero_zero, one_smul, addSubMap]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Heq := (W.equation_iff x y).mp h.1
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [Hrs]
    by_cases! H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      refine ⟨_, H', ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma Point.sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some xP yP hP).sym2x (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
          (xP - xQ) ^ 2] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap]
      ring
    have : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 this, ?_⟩
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [Hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ, Point.xRep_sub_of_X_ne hP hQ hxPQ,
      b₂, b₄, b₆, b₈]
    ext i : 1
    fin_cases i <;> simp [field] <;> grobner

end Decidable

/-! ### The naïve height -/

section AAV

variable [AdmissibleAbsValues F]

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep := by
  simp [Point.naiveHeight]

lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

/-- The height of `sym2x P Q` differs from `h(P) + h(Q)` by a bounded amount. -/
lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x_eq]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

/-- **The approximate parallelogram law** for the naïve height on an elliptic curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- Reduce to the essentials before `grind`.
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end AAV

/-! ### Northcott finiteness -/

section Northcott

variable [AdmissibleAbsValues F]

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in
/-- The set of `K`-points on `W` with naïve height bounded by `B` is finite. This is the
Northcott ingredient of the Mordell–Weil theorem. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott

end Affine

end WeierstrassCurve

end
