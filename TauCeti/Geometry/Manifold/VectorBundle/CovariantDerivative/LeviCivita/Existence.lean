/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz

/-!
# Existence of the Levi-Civita connection

The Koszul formula `2 ⟪∇_X Y, Z⟫ = koszul I X Y Z` characterises the Levi-Civita connection of a
Riemannian metric, and its right-hand side involves the metric alone. This file turns that
characterisation into a construction: on a finite-dimensional Riemannian manifold there *is* a
torsion-free metric covariant derivative on the tangent bundle, so that together with
`CovariantDerivative.IsLeviCivita.difference_eq_zero` the Levi-Civita connection exists and is
unique.

The construction has three steps. The Koszul expression is tensorial in its first argument as
well as in its third, so Mathlib's `TensorialAt.mkHom₂` packages `(X, Z) ↦ koszul I X Y Z x` as a
continuous bilinear form `TauCeti.Manifold.koszulHom` on the fibre `T_x M`. The fibrewise
Fréchet–Riesz equivalence `Riemannian.Tensor.rieszDual` then converts the last slot of that
bilinear form into a vector, giving the unbundled candidate. Finally the covariant-derivative
axioms for the candidate are read off the behaviour of the Koszul expression in its *second*
argument: `TauCeti.Manifold.koszul_add_second` gives additivity, and
`TauCeti.Manifold.koszul_smul_second` — which says that replacing `Y` by `f • Y` adds
`2 (df X) ⟪Y, Z⟫` — gives the Leibniz rule.

Since a covariant derivative in Mathlib is a *total* function on sections, constrained only at
sections which are differentiable at the point under consideration, the unbundled candidate is
given by the Koszul recipe when `Y` is differentiable at `x` and is the junk value `0` otherwise.
Every theorem about its value accordingly carries a differentiability hypothesis, and uniqueness
is the vanishing of `CovariantDerivative.difference` rather than equality of bundled connections.

## Main definitions and results

* `TauCeti.Manifold.koszulHom`: the Koszul expression of a section differentiable at `x`, as a
  continuous bilinear form on `T_x M`.
* `CovariantDerivative.leviCivita`: the Levi-Civita connection of the supplied Riemannian bundle
  instance.
* `CovariantDerivative.two_inner_leviCivita_eq_koszul`: it obeys the Koszul formula.
* `CovariantDerivative.isLeviCivita_leviCivita`: it is torsion free and metric.
* `CovariantDerivative.exists_isLeviCivita`: **existence of the Levi-Civita connection**.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The Levi-Civita connection".
* [mathlib4#36845](https://github.com/leanprover-community/mathlib4/pull/36845): this construction
  follows its tensoriality-and-Riesz design, adapted to the APIs in Tau Ceti's Mathlib pin.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Thm. 5.10.
-/

public section

open Bundle FiberBundle NormedSpace VectorField
open TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-! ### The Koszul form of a section -/

/-- The Koszul expression of a section `Y` differentiable at `x`, as a continuous bilinear form on
the tangent fibre at `x`. For sections `X` and `Z` differentiable at `x`, its value at
`(X x, Z x)` is `koszul I X Y Z x`; see `koszulHom_apply`. -/
def koszulHom (Y : Π y : M, TangentSpace I y) {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z ↦ koszul I X Y Z x) x
    (fun _ hZ ↦ tensorialAt_koszul_first hY hZ) (fun _ hX ↦ tensorialAt_koszul_third hX hY)

@[simp]
theorem koszulHom_apply (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x)
    (hZ : MDiffAt (T% Z) x) : koszulHom Y hY (X x) (Z x) = koszul I X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hZ

/-- The Koszul form evaluated at arbitrary tangent vectors, expressed using their canonical local
extensions. -/
theorem koszulHom_apply_eq_extend (Y : Π y : M, TangentSpace I y)
    (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    koszulHom Y hY v w = koszul I (extend E v) Y (extend E w) x :=
  TensorialAt.mkHom₂_apply_eq_extend _ _ v w

end TauCeti.Manifold

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable {X Y Z : Π x : M, TangentSpace I x} {x : M}

/-! ### The connection -/

open scoped Classical in
/-- The Levi-Civita connection of the supplied Riemannian bundle instance, as a function on
sections. At a section `Y` differentiable at `x` its value is the vector representing half the
Koszul form, in accordance with the Koszul formula `2 ⟪∇_X Y, Z⟫ = koszul I X Y Z`; elsewhere it is
the junk value `0`, which the covariant-derivative axioms never see. -/
private def leviCivitaFun (Y : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then
    (2 : ℝ)⁻¹ • ((Riemannian.Tensor.rieszDual (I := I) x).toLinearIsometry.toContinuousLinearMap ∘L
      TauCeti.Manifold.koszulHom Y hY)
  else 0

private theorem two_inner_leviCivitaFun_eq_koszul (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (leviCivitaFun Y x (X x)) (Z x) = koszul I X Y Z x := by
  rw [leviCivitaFun, dite_eq_left hY]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    real_inner_smul_left, Riemannian.Tensor.inner_rieszDual,
    TauCeti.Manifold.koszulHom_apply hY hX hZ]
  ring

/-- The Koszul recipe defines a covariant derivative on the tangent bundle: additivity comes from
`TauCeti.Manifold.koszul_add_second` and the Leibniz rule from
`TauCeti.Manifold.koszul_smul_second`. -/
private theorem isCovariantDerivativeOn_leviCivitaFun :
    IsCovariantDerivativeOn (I := I) E (leviCivitaFun (M := M)) Set.univ := by
  constructor
  · intro σ σ' x hσ hσ' _
    refine continuousLinearMap_ext_of_forall_inner_section_eq (I := I)
      (V := fun x : M ↦ TangentSpace I x) E E fun W hW Z hZ ↦ ?_
    have h₁ := two_inner_leviCivitaFun_eq_koszul hW (mdifferentiableAt_add_section hσ hσ') hZ
    have h₂ := two_inner_leviCivitaFun_eq_koszul hW hσ hZ
    have h₃ := two_inner_leviCivitaFun_eq_koszul hW hσ' hZ
    have h₄ := koszul_add_second (X := W) (Y := σ) (Y' := σ') (Z := Z) hW hσ hσ' hZ
    simp only [add_apply, inner_add_left]
    linarith
  · intro σ g x hσ hg _
    refine continuousLinearMap_ext_of_forall_inner_section_eq (I := I)
      (V := fun x : M ↦ TangentSpace I x) E E fun W hW Z hZ ↦ ?_
    have h₁ := two_inner_leviCivitaFun_eq_koszul hW (hg.smul_section hσ) hZ
    have h₂ := two_inner_leviCivitaFun_eq_koszul hW hσ hZ
    have h₃ := koszul_smul_second (X := W) (Y := σ) (Z := Z) hg hW hσ hZ
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_left,
      real_inner_smul_left]
    linear_combination h₁ / 2 - (g x / 2) * h₂ + h₃ / 2

variable (I M) in
/-- **The Levi-Civita connection** of the supplied Riemannian bundle instance: the torsion-free
covariant derivative on the tangent bundle which is compatible with the metric. -/
def leviCivita : CovariantDerivative I E (fun x : M ↦ TangentSpace I x) where
  toFun := leviCivitaFun
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_leviCivitaFun

private theorem leviCivita_apply (Y : Π y : M, TangentSpace I y) (x : M) :
    leviCivita I M Y x = leviCivitaFun Y x := rfl

/-- The defining identity for the Levi-Civita connection at arbitrary tangent vectors. -/
theorem two_inner_leviCivita_apply (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    2 * inner ℝ (leviCivita I M Y x v) w = TauCeti.Manifold.koszulHom Y hY v w := by
  rw [leviCivita_apply, leviCivitaFun, dite_eq_left hY]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    real_inner_smul_left, Riemannian.Tensor.inner_rieszDual]
  ring

/-- **The Koszul formula** for the Levi-Civita connection. -/
theorem two_inner_leviCivita_eq_koszul (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (leviCivita I M Y x (X x)) (Z x) = koszul I X Y Z x := by
  rw [two_inner_leviCivita_apply hY, TauCeti.Manifold.koszulHom_apply hY hX hZ]

/-! ### Existence -/

/-- **Existence of the Levi-Civita connection**: the connection built from the Koszul formula is
torsion free and compatible with the metric. -/
theorem isLeviCivita_leviCivita : IsLeviCivita (leviCivita I M) := by
  refine isLeviCivita_iff.mpr fun x X Y Z hX hY hZ ↦ ?_
  exact two_inner_leviCivita_eq_koszul hX hY hZ

variable (I M) in
/-- **Existence of the Levi-Civita connection**, in existential form. -/
theorem exists_isLeviCivita :
    ∃ cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x), IsLeviCivita cov :=
  ⟨leviCivita I M, isLeviCivita_leviCivita⟩

end CovariantDerivative
