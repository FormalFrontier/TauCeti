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
continuous bilinear form `CovariantDerivative.koszulHom` on the fibre `T_x M`. The fibrewise
Fréchet–Riesz equivalence `Riemannian.Tensor.rieszDual` then converts the last slot of that
bilinear form into a vector, giving the candidate `CovariantDerivative.leviCivitaFun`. Finally the
covariant-derivative axioms for the candidate are read off the behaviour of the Koszul expression
in its *second* argument: `TauCeti.Manifold.koszul_add_second` gives additivity, and
`TauCeti.Manifold.koszul_smul_second` — which says that replacing `Y` by `f • Y` adds
`2 (df X) ⟪Y, Z⟫` — gives the Leibniz rule.

Since a covariant derivative in Mathlib is a *total* function on sections, constrained only at
sections which are differentiable at the point under consideration, `leviCivitaFun Y x` is given by
the Koszul recipe when `Y` is differentiable at `x` and is the junk value `0` otherwise. Every
theorem about its value accordingly carries a differentiability hypothesis, and uniqueness is the
vanishing of `CovariantDerivative.difference` rather than equality of bundled connections.

## Main definitions and results

* `CovariantDerivative.koszulHom`: the Koszul expression of a section differentiable at `x`, as a
  continuous bilinear form on `T_x M`.
* `CovariantDerivative.leviCivitaFun` and `CovariantDerivative.leviCivita`: the Levi-Civita
  connection of the canonical Riemannian bundle instance, unbundled and bundled.
* `CovariantDerivative.two_inner_leviCivitaFun_eq_koszul`: it obeys the Koszul formula.
* `CovariantDerivative.isLeviCivita_leviCivita`: it is torsion free and metric.
* `CovariantDerivative.exists_isLeviCivita` and
  `CovariantDerivative.existsUnique_isLeviCivita`: **existence and uniqueness of the Levi-Civita
  connection**, the second in the form "a Levi-Civita connection exists, and every Levi-Civita
  connection differs from it by the zero endomorphism-valued one-form".

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, Thm. 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Thm. 5.10.
-/

public section

open Bundle FiberBundle NormedSpace VectorField
open TauCeti TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace CovariantDerivative

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
the tangent fibre at `x`: it sends `(X x, Z x)` to `koszul I X Y Z x`. -/
def koszulHom (Y : Π y : M, TangentSpace I y) {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z ↦ koszul I X Y Z x) x
    (fun _ hZ ↦ tensorialAt_koszul_first hY hZ) (fun _ hX ↦ tensorialAt_koszul hX hY)

@[simp]
theorem koszulHom_apply (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x)
    (hZ : MDiffAt (T% Z) x) : koszulHom Y hY (X x) (Z x) = koszul I X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hZ

/-! ### The connection -/

open scoped Classical in
/-- The Levi-Civita connection of the canonical Riemannian bundle instance, as a function on
sections. At a section `Y` differentiable at `x` its value is the vector representing half the
Koszul form, in accordance with the Koszul formula `2 ⟪∇_X Y, Z⟫ = koszul I X Y Z`; elsewhere it is
the junk value `0`, which the covariant-derivative axioms never see. -/
def leviCivitaFun (Y : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then
    (2 : ℝ)⁻¹ • ((Riemannian.Tensor.rieszDual (I := I) x).toLinearIsometry.toContinuousLinearMap ∘L
      koszulHom Y hY)
  else 0

/-- **The Koszul formula** for the connection under construction. -/
theorem two_inner_leviCivitaFun_eq_koszul (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (leviCivitaFun Y x (X x)) (Z x) = koszul I X Y Z x := by
  rw [leviCivitaFun, dite_eq_left hY]
  simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    real_inner_smul_left, Riemannian.Tensor.inner_rieszDual, koszulHom_apply hY hX hZ]
  ring

omit [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Two endomorphisms of a tangent fibre which agree on all inner products of values at sections
differentiable at the base point are equal. -/
private theorem ext_of_forall_inner_eq {A B : TangentSpace I x →L[ℝ] TangentSpace I x}
    (h : ∀ ⦃W Z : Π y : M, TangentSpace I y⦄, MDiffAt (T% W) x → MDiffAt (T% Z) x →
      inner ℝ (A (W x)) (Z x) = inner ℝ (B (W x)) (Z x)) : A = B := by
  refine VectorBundle.injective_eval_mdifferentiableAt_sec I E (fun x : M ↦ TangentSpace I x)
    (TangentSpace I x) x ?_
  ext W hW
  exact eq_of_forall_inner_section_eq (I := I) (V := fun x : M ↦ TangentSpace I x) E
    fun Z hZ ↦ h hW hZ

/-- The Koszul recipe defines a covariant derivative on the tangent bundle: additivity comes from
`TauCeti.Manifold.koszul_add_second` and the Leibniz rule from
`TauCeti.Manifold.koszul_smul_second`. -/
theorem isCovariantDerivativeOn_leviCivitaFun :
    IsCovariantDerivativeOn (I := I) E (leviCivitaFun (M := M)) Set.univ := by
  constructor
  · intro σ σ' x hσ hσ' _
    refine ext_of_forall_inner_eq fun W Z hW hZ ↦ ?_
    have h₁ := two_inner_leviCivitaFun_eq_koszul hW (mdifferentiableAt_add_section hσ hσ') hZ
    have h₂ := two_inner_leviCivitaFun_eq_koszul hW hσ hZ
    have h₃ := two_inner_leviCivitaFun_eq_koszul hW hσ' hZ
    have h₄ := koszul_add_second (X := W) (Y := σ) (Y' := σ') (Z := Z) hW hσ hσ' hZ
    simp only [add_apply, inner_add_left]
    linarith
  · intro σ g x hσ hg _
    refine ext_of_forall_inner_eq fun W Z hW hZ ↦ ?_
    have h₁ := two_inner_leviCivitaFun_eq_koszul hW (hg.smul_section hσ) hZ
    have h₂ := two_inner_leviCivitaFun_eq_koszul hW hσ hZ
    have h₃ := koszul_smul_second (X := W) (Y := σ) (Z := Z) hg hW hσ hZ
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_left,
      real_inner_smul_left]
    linear_combination h₁ / 2 - (g x / 2) * h₂ + h₃ / 2

variable (I M) in
/-- **The Levi-Civita connection** of the canonical Riemannian bundle instance: the torsion-free
covariant derivative on the tangent bundle which is compatible with the metric. -/
def leviCivita : CovariantDerivative I E (fun x : M ↦ TangentSpace I x) where
  toFun := leviCivitaFun
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_leviCivitaFun

@[simp]
theorem leviCivita_apply (Y : Π y : M, TangentSpace I y) (x : M) :
    leviCivita I M Y x = leviCivitaFun Y x := (rfl)

/-! ### Existence and uniqueness -/

/-- **Existence of the Levi-Civita connection**: the connection built from the Koszul formula is
torsion free and compatible with the metric. -/
theorem isLeviCivita_leviCivita : IsLeviCivita (leviCivita I M) := by
  refine isLeviCivita_iff.mpr fun x X Y Z hX hY hZ ↦ ?_
  rw [leviCivita_apply]
  exact two_inner_leviCivitaFun_eq_koszul hX hY hZ

variable (I M) in
/-- **Existence of the Levi-Civita connection**, in existential form. -/
theorem exists_isLeviCivita :
    ∃ cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x), IsLeviCivita cov :=
  ⟨leviCivita I M, isLeviCivita_leviCivita⟩

variable {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}

/-- Every Levi-Civita connection agrees with the canonical one on the sections which are
differentiable at the point under consideration. -/
theorem IsLeviCivita.eq_leviCivita (h : IsLeviCivita cov) (hY : MDiffAt (T% Y) x) :
    cov Y x = leviCivita I M Y x :=
  h.unique isLeviCivita_leviCivita hY

/-- Every Levi-Civita connection differs from the canonical one by the zero endomorphism-valued
one-form. -/
theorem IsLeviCivita.difference_leviCivita_eq_zero (h : IsLeviCivita cov) :
    cov.difference (leviCivita I M) = 0 :=
  h.difference_eq_zero isLeviCivita_leviCivita

variable (I M) in
/-- **Existence and uniqueness of the Levi-Civita connection**: a torsion-free metric covariant
derivative on the tangent bundle exists, and every one differs from it by the zero
endomorphism-valued one-form. Uniqueness cannot be phrased as equality of the bundled connections,
since a covariant derivative is unconstrained at sections which are nowhere differentiable. -/
theorem existsUnique_isLeviCivita :
    ∃ cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x), IsLeviCivita cov ∧
      ∀ cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x), IsLeviCivita cov' →
        cov'.difference cov = 0 :=
  ⟨leviCivita I M, isLeviCivita_leviCivita, fun _ h ↦ h.difference_leviCivita_eq_zero⟩

end CovariantDerivative
