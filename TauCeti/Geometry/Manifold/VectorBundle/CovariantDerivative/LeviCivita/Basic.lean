/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The Koszul formula and uniqueness of the Levi-Civita connection

A covariant derivative `∇` on the tangent bundle of a Riemannian manifold is a *Levi-Civita
connection*, or *Riemannian connection*, if it is torsion free and compatible with the metric.
This file introduces that predicate, proves the Koszul formula

`2 ⟪∇_X Y, Z⟫ = X ⟪Y, Z⟫ + Y ⟪Z, X⟫ - Z ⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫`

characterising it, and deduces that a Levi-Civita connection is unique.

The right-hand side of the Koszul formula involves the metric only, so it is packaged as a
standalone function `TauCeti.Manifold.koszul`. Since the inner product on a fibre is
nondegenerate, the formula pins `∇_X Y` down completely: this is `IsLeviCivita.unique`, whose
tensorial repackaging is `IsLeviCivita.difference_eq_zero`. The converse direction
`isLeviCivita_iff` shows nothing is lost in the passage to `koszul`: a connection satisfying the
Koszul formula is automatically torsion free and metric. Since `koszul I X Y · x` is moreover
tensorial in its last slot, the Koszul formula is also the shape in which the Levi-Civita
connection gets constructed; that construction, together with the tensoriality in the first slot
and the Leibniz rule in the second which it needs, is carried out in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Existence`.

Two covariant derivatives can only be compared through sections that are differentiable at the
point under consideration, because `CovariantDerivative` puts no constraint whatsoever on the
value of `∇ σ` for a nowhere differentiable section `σ`. Uniqueness is therefore stated as
`∇ Y x = ∇' Y x` for `Y` differentiable at `x`, which is exactly the statement that the
endomorphism-valued one-form `CovariantDerivative.difference ∇ ∇'` vanishes.

## Main definitions and results

* `TauCeti.Manifold.koszul` and `TauCeti.Manifold.koszul_apply`: the right-hand side of the Koszul
  formula, a function of the Riemannian metric alone, and its defining formula.
* `CovariantDerivative.IsLeviCivita`: a covariant derivative on the tangent bundle is
  torsion free and compatible with the metric.
* `CovariantDerivative.IsLeviCivita.two_inner_eq_koszul`: the Koszul formula.
* `CovariantDerivative.isLeviCivita_iff`: the Koszul formula characterises the
  Levi-Civita connections.
* `CovariantDerivative.IsLeviCivita.unique` and
  `CovariantDerivative.IsLeviCivita.difference_eq_zero`: uniqueness of the Levi-Civita
  connection.
* `TauCeti.Manifold.koszul_sub_koszul_swap_first_two` and
  `TauCeti.Manifold.koszul_add_koszul_swap_last_two`: the two symmetries of the Koszul expression
  from which the converse direction is read off.
* `TauCeti.Manifold.tensorialAt_koszul_third` and `TauCeti.Manifold.tensorialAt_koszul_first`: the
  Koszul expression is tensorial in its last argument and in its first.
* `TauCeti.Manifold.koszul_add_second` and `TauCeti.Manifold.koszul_smul_second`: additivity and
  the Leibniz rule in the middle argument, the slot which the connection differentiates.
* `TauCeti.eq_of_forall_inner_section_eq`: a vector in a fibre of a Riemannian bundle is
  determined by its inner products against the differentiable sections.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The Levi-Civita connection".
* [mathlib4#36845](https://github.com/leanprover-community/mathlib4/pull/36845): the first-slot
  tensoriality and second-slot Leibniz identities follow its design.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Thm. 5.10.
-/

public section

open Bundle FiberBundle NormedSpace VectorField
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Nondegeneracy of the metric along differentiable sections -/

section Nondegenerate

variable {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V]

variable (F) in
/-- A vector in a fibre of a Riemannian vector bundle is determined by its inner products against
the sections that are differentiable at the base point: every vector of the fibre is the value at
that point of such a section, by `FiberBundle.extend`. -/
theorem eq_of_forall_inner_section_eq {x : M} {u v : V x}
    (h : ∀ τ : Π y : M, V y, MDiffAt (T% τ) x → inner ℝ u (τ x) = inner ℝ v (τ x)) : u = v := by
  refine ext_inner_right ℝ fun w ↦ ?_
  simpa using h (extend F w) (mdifferentiableAt_extend I F w)

variable {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, NormedAddCommGroup (V' x)] [∀ x, NormedSpace ℝ (V' x)] [FiberBundle F' V']

variable (F F') in
/-- Two continuous linear maps between fibres are equal if their values on differentiable sections
have the same inner products against every differentiable section of the target bundle. -/
theorem continuousLinearMap_ext_of_forall_inner_section_eq {x : M} {A B : V' x →L[ℝ] V x}
    (h : ∀ σ : ∀ y : M, V' y, MDiffAt (T% σ) x → ∀ τ : ∀ y : M, V y,
      MDiffAt (T% τ) x → inner ℝ (A (σ x)) (τ x) = inner ℝ (B (σ x)) (τ x)) : A = B := by
  refine VectorBundle.injective_eval_mdifferentiableAt_sec I F' V' (V x) x ?_
  ext σ hσ
  exact eq_of_forall_inner_section_eq (I := I) (V := V) F fun τ hτ ↦ h σ hσ τ hτ

end Nondegenerate

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-! ### The Koszul expression -/

namespace Manifold

variable (I) in
/-- The right-hand side of the Koszul formula,

`X ⟪Y, Z⟫ + Y ⟪Z, X⟫ - Z ⟪X, Y⟫ + ⟪[X, Y], Z⟫ - ⟪[X, Z], Y⟫ - ⟪[Y, Z], X⟫`,

evaluated at `x`. It depends on the Riemannian metric alone; for the Levi-Civita connection `∇` of
that metric it computes `2 ⟪∇_X Y, Z⟫`, by
`CovariantDerivative.IsLeviCivita.two_inner_eq_koszul`. -/
def koszul (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x)
    + mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x)
    - mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)
    + inner ℝ (mlieBracket I X Y x) (Z x)
    - inner ℝ (mlieBracket I X Z x) (Y x)
    - inner ℝ (mlieBracket I Y Z x) (X x)

/-- The defining formula for the Koszul expression, available outside the module where
`TauCeti.Manifold.koszul` is defined. -/
theorem koszul_apply (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    koszul I X Y Z x =
      mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)
        + inner ℝ (mlieBracket I X Y x) (Z x)
        - inner ℝ (mlieBracket I X Z x) (Y x)
        - inner ℝ (mlieBracket I Y Z x) (X x) := (rfl)

variable {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- Swapping the two inner arguments of a pointwise inner product of sections. -/
private theorem inner_section_comm (Y Z : Π x : M, TangentSpace I x) :
    (fun y ↦ inner ℝ (Y y) (Z y)) = fun y ↦ inner ℝ (Z y) (Y y) :=
  funext fun _ ↦ real_inner_comm _ _

/-- Antisymmetrising the Koszul expression in its first two arguments returns twice the inner
product of the Lie bracket with the third argument. This is the identity behind the torsion-free
half of `CovariantDerivative.isLeviCivita_iff`. -/
theorem koszul_sub_koszul_swap_first_two :
    koszul I X Y Z x - koszul I Y X Z x = 2 * inner ℝ (mlieBracket I X Y x) (Z x) := by
  rw [koszul, koszul, inner_section_comm Z Y, inner_section_comm Y X, inner_section_comm X Z,
    mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [inner_neg_left]
  ring

/-- Symmetrising the Koszul expression in its last two arguments returns twice the derivative of
their inner product along the first argument. This is the identity behind the metric half of
`CovariantDerivative.isLeviCivita_iff`. -/
theorem koszul_add_koszul_swap_last_two :
    koszul I Z X Y x + koszul I Z Y X x =
      2 * mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x) := by
  rw [koszul, koszul, inner_section_comm Y X, inner_section_comm Y Z, inner_section_comm X Z,
    mlieBracket_swap_apply (V := Y) (W := X)]
  simp only [inner_neg_left]
  ring

section InnerDifferentiability

variable [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The pointwise inner product of two sections of the tangent bundle that are differentiable at
`x` is differentiable at `x`. This is the tangent-bundle specialisation of
`MDifferentiableAt.inner_bundle`, whose bundle argument Lean cannot infer from hypotheses phrased
through `TangentSpace`. -/
theorem mdifferentiableAt_inner (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (fun y ↦ inner ℝ (Y y) (Z y)) x :=
  MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := id) hY hZ

end InnerDifferentiability

section Tensorial

variable [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [CompleteSpace E]

/-! ### Behaviour in the first two arguments

The Koszul expression is tensorial in its first argument, just as it is in its third, and obeys a
Leibniz rule in its second. These are the identities which turn
`CovariantDerivative.isLeviCivita_iff` into a construction of the Levi-Civita connection, carried
out in `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Existence`.
-/

variable {X' Y' : Π x : M, TangentSpace I x} {f : M → ℝ}

/-- The Koszul expression is additive in its second argument. -/
theorem koszul_add_second (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszul I X (Y + Y') Z x = koszul I X Y Z x + koszul I X Y' Z x := by
  have e₁ : (fun y ↦ inner ℝ ((Y + Y') y) (Z y)) =
      fun y ↦ inner ℝ (Y y) (Z y) + inner ℝ (Y' y) (Z y) := funext fun _ ↦ inner_add_left ..
  have e₂ : (fun y ↦ inner ℝ (X y) ((Y + Y') y)) =
      fun y ↦ inner ℝ (X y) (Y y) + inner ℝ (X y) (Y' y) := funext fun _ ↦ inner_add_right ..
  have e₃ : (Y + Y') x = Y x + Y' x := rfl
  rw [koszul, koszul, koszul, e₁, e₂, e₃,
    mvfderiv_fun_add (mdifferentiableAt_inner hY hZ) (mdifferentiableAt_inner hY' hZ),
    mvfderiv_fun_add (mdifferentiableAt_inner hX hY) (mdifferentiableAt_inner hX hY'),
    mlieBracket_add_right hY hY', mlieBracket_add_left hY hY']
  simp only [add_apply, map_add, inner_add_left, inner_add_right]
  ring

/-- The Leibniz rule for the Koszul expression in its second argument: replacing `Y` by `f • Y`
multiplies the expression by `f x` and adds `2 (df X) ⟪Y, Z⟫`. This is the identity behind the
Leibniz axiom of the connection built from the Koszul formula. -/
theorem koszul_smul_second (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszul I X (f • Y) Z x =
      f x * koszul I X Y Z x + 2 * d% f x (X x) * inner ℝ (Y x) (Z x) := by
  have e₁ : (fun y ↦ inner ℝ ((f • Y) y) (Z y)) = fun y ↦ f y * inner ℝ (Y y) (Z y) :=
    funext fun _ ↦ real_inner_smul_left ..
  have e₂ : (fun y ↦ inner ℝ (X y) ((f • Y) y)) = fun y ↦ f y * inner ℝ (X y) (Y y) :=
    funext fun _ ↦ real_inner_smul_right ..
  have e₃ : (f • Y) x = f x • Y x := rfl
  rw [koszul, koszul, e₁, e₂, e₃, mvfderiv_fun_mul hf (mdifferentiableAt_inner hY hZ),
    mvfderiv_fun_mul hf (mdifferentiableAt_inner hX hY),
    mlieBracket_smul_right hf hY, mlieBracket_smul_left (W := Z) hf hY]
  simp only [add_apply, smul_apply, smul_eq_mul, map_smul, inner_add_left, neg_smul,
    inner_neg_left, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (Y x) (X x)]
  ring

/-- The Koszul expression is additive in its first argument. -/
theorem koszul_add_first (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul I (X + X') Y Z x = koszul I X Y Z x + koszul I X' Y Z x := by
  have hsum := koszul_add_second (I := I) (X := Y) (Y := X) (Y' := X') (Z := Z)
    hY hX hX' hZ
  have hswap := koszul_sub_koszul_swap_first_two
    (I := I) (X := X + X') (Y := Y) (Z := Z) (x := x)
  have hswapX := koszul_sub_koszul_swap_first_two
    (I := I) (X := X) (Y := Y) (Z := Z) (x := x)
  have hswapX' := koszul_sub_koszul_swap_first_two
    (I := I) (X := X') (Y := Y) (Z := Z) (x := x)
  rw [mlieBracket_add_left hX hX', inner_add_left] at hswap
  linarith

/-- The Koszul expression is tensorial in its first argument: replacing `X` by `f • X` multiplies
it by `f x`. This follows from the second-slot Leibniz rule and the swap identity. -/
theorem koszul_smul_first (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) : koszul I (f • X) Y Z x = f x * koszul I X Y Z x := by
  have hsmul := koszul_smul_second (I := I) (X := Y) (Y := X) (Z := Z) hf hY hX hZ
  have hswap := koszul_sub_koszul_swap_first_two
    (I := I) (X := f • X) (Y := Y) (Z := Z) (x := x)
  have hswapX := koszul_sub_koszul_swap_first_two
    (I := I) (X := X) (Y := Y) (Z := Z) (x := x)
  rw [mlieBracket_smul_left hf hX] at hswap
  simp only [inner_add_left, neg_smul, inner_neg_left, real_inner_smul_left] at hswap
  linear_combination hswap + hsmul - f x * hswapX

/-- The Koszul expression is tensorial in its first argument. Together with
`TauCeti.Manifold.tensorialAt_koszul_third` this presents it as a continuous bilinear form on the
tangent fibre, which is the shape in which the Levi-Civita connection gets built. -/
theorem tensorialAt_koszul_first (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X : Π y : M, TangentSpace I y ↦ koszul I X Y Z x) x where
  smul hf hX := by simpa using koszul_smul_first hf hX hY hZ
  add hX hX' := koszul_add_first hX hX' hY hZ

/-- The Koszul expression is tensorial in its third argument: replacing `Z` by `f • Z` multiplies
it by `f x`, and it is additive in `Z`. Together with
`CovariantDerivative.isLeviCivita_iff` this is what turns the Koszul formula from a
characterisation of the Levi-Civita connection into a construction of it. -/
theorem tensorialAt_koszul_third (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z : Π y : M, TangentSpace I y ↦ koszul I X Y Z x) x where
  smul {f Z} hf hZ := by
    have e₁ : (fun y ↦ inner ℝ (Y y) ((f • Z) y)) = fun y ↦ f y * inner ℝ (Y y) (Z y) :=
      funext fun _ ↦ real_inner_smul_right ..
    have e₂ : (fun y ↦ inner ℝ ((f • Z) y) (X y)) = fun y ↦ f y * inner ℝ (Z y) (X y) :=
      funext fun _ ↦ real_inner_smul_left ..
    have e₃ : (f • Z) x = f x • Z x := rfl
    rw [koszul, koszul, e₁, e₂, e₃, mvfderiv_fun_mul hf (mdifferentiableAt_inner hY hZ),
      mvfderiv_fun_mul hf (mdifferentiableAt_inner hZ hX),
      mlieBracket_smul_right hf hZ, mlieBracket_smul_right (V := Y) hf hZ]
    simp only [add_apply, smul_apply, smul_eq_mul, map_smul, inner_add_left,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (Z x) (Y x)]
    ring
  add {Z Z'} hZ hZ' := by
    have e₁ : (fun y ↦ inner ℝ (Y y) ((Z + Z') y)) =
        fun y ↦ inner ℝ (Y y) (Z y) + inner ℝ (Y y) (Z' y) := funext fun _ ↦ inner_add_right ..
    have e₂ : (fun y ↦ inner ℝ ((Z + Z') y) (X y)) =
        fun y ↦ inner ℝ (Z y) (X y) + inner ℝ (Z' y) (X y) := funext fun _ ↦ inner_add_left ..
    have e₃ : (Z + Z') x = Z x + Z' x := rfl
    rw [koszul, koszul, koszul, e₁, e₂, e₃,
      mvfderiv_fun_add (mdifferentiableAt_inner hY hZ) (mdifferentiableAt_inner hY hZ'),
      mvfderiv_fun_add (mdifferentiableAt_inner hZ hX) (mdifferentiableAt_inner hZ' hX),
      mlieBracket_add_right hZ hZ', mlieBracket_add_right (V := Y) hZ hZ']
    simp only [add_apply, map_add, inner_add_left, inner_add_right]
    ring

end Tensorial

end Manifold

end TauCeti

/-! ### The Levi-Civita connection -/

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))

/-- A covariant derivative on the tangent bundle of a Riemannian manifold is a *Levi-Civita
connection* if it is torsion free and compatible with the metric. -/
structure IsLeviCivita : Prop where
  /-- A Levi-Civita connection is torsion free. -/
  torsion_eq_zero : cov.torsion = 0
  /-- A Levi-Civita connection is compatible with the Riemannian metric. -/
  isMetricCompatible :
    CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov

variable {cov} {cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-- Freedom from torsion of a Levi-Civita connection, in the usable form
`∇_X Y - ∇_Y X = [X, Y]`: this is `CovariantDerivative.torsion_eq_zero_iff` read off the first
defining property. -/
theorem IsLeviCivita.sub_eq_mlieBracket (h : IsLeviCivita cov) (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
  cov.torsion_eq_zero_iff.mp h.torsion_eq_zero hX hY

/-- Metric compatibility of a Levi-Civita connection, in the usable form
`X ⟪Y, Z⟫ = ⟪∇_X Y, Z⟫ + ⟪Y, ∇_X Z⟫`: this is
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` read off the second defining
property. -/
theorem IsLeviCivita.mvfderiv_inner_eq (h : IsLeviCivita cov) (X : Π x : M, TangentSpace I x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) =
      inner ℝ (cov Y x (X x)) (Z x) + inner ℝ (Y x) (cov Z x (X x)) :=
  h.isMetricCompatible.mvfderiv_inner_eq X hY hZ

/-- **The Koszul formula**: for the Levi-Civita connection, `2 ⟪∇_X Y, Z⟫` is the Koszul
expression of the metric. -/
theorem IsLeviCivita.two_inner_eq_koszul (h : IsLeviCivita cov) (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (cov Y x (X x)) (Z x) = TauCeti.Manifold.koszul I X Y Z x := by
  rw [TauCeti.Manifold.koszul, ← h.sub_eq_mlieBracket hX hY, ← h.sub_eq_mlieBracket hX hZ,
    ← h.sub_eq_mlieBracket hY hZ, h.mvfderiv_inner_eq X hY hZ, h.mvfderiv_inner_eq Y hZ hX,
    h.mvfderiv_inner_eq Z hX hY]
  simp only [inner_sub_left]
  rw [real_inner_comm (Y x) (cov Z x (X x)), real_inner_comm (Z x) (cov X x (Y x)),
    real_inner_comm (X x) (cov Y x (Z x))]
  ring

/-- A covariant derivative on the tangent bundle is a Levi-Civita connection exactly when it
satisfies the Koszul formula. -/
theorem isLeviCivita_iff :
    IsLeviCivita cov ↔ ∀ ⦃x : M⦄ ⦃X Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% X) x →
      MDiffAt (T% Y) x → MDiffAt (T% Z) x →
      2 * inner ℝ (cov Y x (X x)) (Z x) = TauCeti.Manifold.koszul I X Y Z x := by
  refine ⟨fun h _ _ _ _ hX hY hZ ↦ h.two_inner_eq_koszul hX hY hZ, fun h ↦ ⟨?_, ?_⟩⟩
  · refine cov.torsion_eq_zero_iff.mpr fun {X Y x} hX hY ↦ ?_
    refine TauCeti.eq_of_forall_inner_section_eq (I := I) (V := fun x : M ↦ TangentSpace I x) E
      fun Z hZ ↦ ?_
    have hXY := h hX hY hZ
    have hYX := h hY hX hZ
    have key := TauCeti.Manifold.koszul_sub_koszul_swap_first_two
      (I := I) (X := X) (Y := Y) (Z := Z) (x := x)
    rw [inner_sub_left]
    linarith
  · rw [CovariantDerivative.isMetricCompatible_iff]
    intro x X Y Z hX hY hZ
    have hXY := h hX hY hZ
    have hYX := h hX hZ hY
    have key := TauCeti.Manifold.koszul_add_koszul_swap_last_two
      (I := I) (X := Y) (Y := Z) (Z := X) (x := x)
    -- Normalize the beta-redexes introduced by the local notations in `isMetricCompatible_iff`.
    simp only
    rw [real_inner_comm (cov Z x (X x)) (Y x)]
    linarith

/-! ### Uniqueness -/

/-- **Uniqueness of the Levi-Civita connection**: two Levi-Civita connections agree on every
section that is differentiable at the point under consideration. -/
theorem IsLeviCivita.unique (h : IsLeviCivita cov) (h' : IsLeviCivita cov')
    (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x := by
  refine TauCeti.continuousLinearMap_ext_of_forall_inner_section_eq (I := I)
    (V := fun x : M ↦ TangentSpace I x) E E fun _ hX _ hZ ↦ ?_
  have h1 := h.two_inner_eq_koszul hX hY hZ
  have h2 := h'.two_inner_eq_koszul hX hY hZ
  linarith

/-- **Uniqueness of the Levi-Civita connection**, as the vanishing of the endomorphism-valued
one-form measuring the difference of two connections. -/
theorem IsLeviCivita.difference_eq_zero (h : IsLeviCivita cov) (h' : IsLeviCivita cov') :
    cov.difference cov' = 0 := by
  ext x v
  have hv : MDiffAt (T% (extend E v : Π y : M, TangentSpace I y)) x :=
    mdifferentiableAt_extend I E v
  have hd := IsCovariantDerivativeOn.difference_apply cov.isCovariantDerivativeOnUniv
    cov'.isCovariantDerivativeOnUniv (x := x) (Set.mem_univ x) hv
  rw [extend_apply_self] at hd
  simp [CovariantDerivative.difference, hd, h.unique h' hv]

end CovariantDerivative
