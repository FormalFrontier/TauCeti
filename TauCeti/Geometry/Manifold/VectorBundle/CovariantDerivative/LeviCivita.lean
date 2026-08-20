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
connection gets constructed; existence is left to a later file.

Two covariant derivatives can only be compared through sections that are differentiable at the
point under consideration, because `CovariantDerivative` puts no constraint whatsoever on the
value of `∇ σ` for a nowhere differentiable section `σ`. Uniqueness is therefore stated as
`∇ Y x = ∇' Y x` for `Y` differentiable at `x`, which is exactly the statement that the
endomorphism-valued one-form `CovariantDerivative.difference ∇ ∇'` vanishes.

## Main definitions and results

* `TauCeti.Manifold.koszul`: the right-hand side of the Koszul formula, a function of the
  Riemannian metric alone.
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
* `TauCeti.Manifold.tensorialAt_koszul`: the Koszul expression is tensorial in its last
  argument.
* `TauCeti.eq_of_forall_inner_section_eq`: a vector in a fibre of a Riemannian bundle is
  determined by its inner products against the differentiable sections.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The Levi-Civita connection".
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

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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

/-- The Koszul expression is tensorial in its third argument: replacing `Z` by `f • Z` multiplies
it by `f x`, and it is additive in `Z`. Together with
`CovariantDerivative.isLeviCivita_iff` this is what turns the Koszul formula from a
characterisation of the Levi-Civita connection into a construction of it. -/
theorem tensorialAt_koszul (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
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
  refine VectorBundle.injective_eval_mdifferentiableAt_sec I E (fun x : M ↦ TangentSpace I x)
    (TangentSpace I x) x ?_
  ext X hX
  refine TauCeti.eq_of_forall_inner_section_eq (I := I) (V := fun x : M ↦ TangentSpace I x) E
    fun Z hZ ↦ ?_
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
