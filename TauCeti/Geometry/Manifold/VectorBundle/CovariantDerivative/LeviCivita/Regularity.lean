/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Regularity of the Levi-Civita connection

On a `C^∞` manifold carrying a `C^∞` Riemannian metric, the Levi-Civita connection
`CovariantDerivative.leviCivita` is `C^∞`: it sends a `C^∞` section of the tangent bundle to a
`C^∞` section of `Hom(TM, TM)`. This file proves that, in the class form
`ContMDiffCovariantDerivative` which Mathlib's covariant-derivative API consumes, together with
the set-local form on an arbitrary open set.

The proof follows the Koszul formula `2 ⟪∇_X Y, Z⟫ = koszul I X Y Z`. The right-hand side is built
from derivatives of pointwise inner products and from Lie brackets, so it loses one degree of
smoothness; that is why the metric and the manifold are assumed `C^∞` rather than `C^k` for the
`C^k` conclusion. Concretely:

* `TauCeti.Manifold.contMDiffOn_koszul` reads the Koszul expression as a sum of directional
  derivatives of inner products (`ContMDiffOn.contMDiffOn_mvfderiv_apply`) and of inner products
  with Lie brackets (`ContMDiffOn.mlieBracketWithin_vectorField`);
* the fibrewise Riesz dual of `Riemannian.Tensor.contMDiffAt_rieszDual` turns smoothness of the
  numbers `⟪∇_{e_j} σ, e_k⟫` into smoothness of the vector fields `∇_{e_j} σ`, for `e` the
  chart-local frame;
* `TauCeti.Manifold.contMDiffOn_hom_of_localFrame` assembles those directions into the hom-bundle
  section `∇σ` demanded by `ContMDiffCovariantDerivativeOn`.

With the class instance available, the local Christoffel data of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame` becomes unconditional for
the Levi-Civita connection: its scalar Christoffel symbols and its model-space Christoffel map are
`C^∞` on the base set of every trivialization in the atlas.

## Main results

* `TauCeti.Manifold.contMDiffOn_koszul`: the Koszul expression of three `C^∞` sections is `C^∞`.
* `CovariantDerivative.contMDiffOn_leviCivita`: on an open set, the Levi-Civita connection carries
  a `C^∞` section to a `C^∞` section of `Hom(TM, TM)`.
* `CovariantDerivative.contMDiffCovariantDerivativeOn_leviCivita` and the instance
  `CovariantDerivative.instContMDiffCovariantDerivativeLeviCivita`: **the Levi-Civita connection
  is `C^∞`.**
* `CovariantDerivative.contMDiffOn_christoffelSymbol_leviCivita` and
  `CovariantDerivative.contMDiffOn_christoffelMap_leviCivita`: its Christoffel symbols and its
  model-space Christoffel map are `C^∞` on a trivialization base set.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Thm. 5.10.
-/

public section

open Bundle FiberBundle Module NormedSpace Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Koszul expression of three `C^∞` sections is `C^∞`.** Both the derivative terms and the
Lie-bracket terms lose one degree of smoothness, which is why the statement is made at `∞`. -/
theorem contMDiffOn_koszul {s : Set M} (hs : IsOpen s) {X Y Z : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (X y)) s)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (Y y)) s)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (Z y)) s) :
    ContMDiffOn I 𝓘(ℝ) ∞ (koszul I X Y Z) s := by
  have hbracket {U V : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (V y)) s) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y ↦ TotalSpace.mk' E y (mlieBracket I U V y)) s := by
    -- The two smoothness levels that Mathlib's Lie-bracket regularity asks of the manifold; over
    -- `ℝ` the `minSmoothness` guard is the identity.
    have hmin : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
    have hsucc : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
    refine (ContMDiffOn.mlieBracketWithin_vectorField (I := I) (m := ⊤) (n := ⊤) hU hV
      hs.uniqueMDiffOn (by simp)).congr fun y hy ↦ ?_
    rw [mlieBracketWithin_of_isOpen hs hy]
  have hinner {U V : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (V y)) s) :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ (inner ℝ (U y) (V y) : ℝ)) s :=
    ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
      (b := id) hU hV
  have hderiv {U V W : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (V y)) s)
      (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (W y)) s) :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y ↦ mvfderiv I (fun z ↦ (inner ℝ (U z) (V z) : ℝ)) y (W y)) s :=
    ContMDiffOn.contMDiffOn_mvfderiv_apply (hinner hU hV) hs hW (by simp)
  refine ContMDiffOn.congr ?_ fun y _ ↦ koszul_apply X Y Z y
  exact (((hderiv hY hZ hX).add (hderiv hZ hX hY)).sub (hderiv hX hY hZ)).add
    (hinner (hbracket hX hY) hZ) |>.sub (hinner (hbracket hX hZ) hY)
      |>.sub (hinner (hbracket hY hZ) hX)

end TauCeti.Manifold

namespace CovariantDerivative

open TauCeti TauCeti.Manifold Riemannian.Tensor

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Levi-Civita connection differentiates smoothly.** On an open set `u`, a section of the
tangent bundle which is `C^∞` on `u` has a covariant derivative which is `C^∞` on `u` as a section
of `Hom(TM, TM)`. -/
theorem contMDiffOn_leviCivita {u : Set M} (hu : IsOpen u) {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)) y (leviCivita I M σ y)) u := by
  have hmetric : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  have hplus : IsManifold I ((∞ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  intro x hx
  -- Work on the intersection of `u` with the chart domain at `x`, where the chart-local frame
  -- and the fibrewise Riesz dual are available.
  set s : Set M := u ∩ (chartAt H x).source
  have hsopen : IsOpen s := hu.inter (chartAt H x).open_source
  have hsub : s ⊆ (chartAt H x).source := inter_subset_right
  have hxs : x ∈ s := ⟨hx, mem_chart_source H x⟩
  have hσs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E y (σ y)) s := hσ.mono inter_subset_left
  have hframe (i : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) x i y)) s :=
    (contMDiffOn_chartLocalFrame (I := I) (n := ∞) x i).mono
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hsub)
  have hσd {y : M} (hy : y ∈ s) : MDiffAt (T% σ) y :=
    (hσs.mdifferentiableOn (by simp)).mdifferentiableAt (hsopen.mem_nhds hy)
  have hframed (i : Fin (finrank ℝ E)) {y : M} (hy : y ∈ s) :
      MDiffAt (T% (chartLocalFrame (I := I) x i)) y :=
    ((hframe i).mdifferentiableOn (by simp)).mdifferentiableAt (hsopen.mem_nhds hy)
  -- Each direction of the connection is the Riesz dual of half the Koszul functional.
  have hdir (j : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E y (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) s := by
    have hrepr (y : M) : rieszDual (I := I) y ((rieszDual (I := I) y).symm
        (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) =
        leviCivita I M σ y (chartLocalFrame (I := I) x j y) :=
      LinearIsometryEquiv.apply_symm_apply _ _
    have hval (y : M) (w : TangentSpace I y) :
        ((rieszDual (I := I) y).symm (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) w =
          inner ℝ (leviCivita I M σ y (chartLocalFrame (I := I) x j y)) w :=
      (eq_rieszDual_iff_inner_eq.1 (hrepr y).symm w).symm
    have heval (k : Fin (finrank ℝ E)) : ContMDiffOn I 𝓘(ℝ) ∞
        (fun y ↦ ((rieszDual (I := I) y).symm
          (leviCivita I M σ y (chartLocalFrame (I := I) x j y)))
            (chartLocalFrame (I := I) x k y)) s := by
      have hmul : ContMDiffOn I 𝓘(ℝ) ∞ (fun y ↦ (2 : ℝ)⁻¹ *
          koszul I (chartLocalFrame (I := I) x j) σ (chartLocalFrame (I := I) x k) y) s :=
        contMDiffOn_const.mul (contMDiffOn_koszul hsopen (hframe j) hσs (hframe k))
      refine hmul.congr fun y hy ↦ ?_
      have h := two_inner_leviCivita_eq_koszul (I := I) (M := M)
        (hframed j hy) (hσd hy) (hframed k hy)
      rw [hval y]
      linarith
    have hfun : (fun y : M ↦ TotalSpace.mk' E y
        (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) =
        fun y : M ↦ TotalSpace.mk' E y (rieszDual (I := I) y
          ((rieszDual (I := I) y).symm
            (leviCivita I M σ y (chartLocalFrame (I := I) x j y)))) := by
      funext y
      rw [hrepr y]
    rw [hfun]
    exact fun y hy ↦ (contMDiffAt_rieszDual (I := I) (n := ∞) x (hsub hy)
      (Φ := fun y ↦ (rieszDual (I := I) y).symm
        (leviCivita I M σ y (chartLocalFrame (I := I) x j y)))
      fun k ↦ (heval k).contMDiffAt (hsopen.mem_nhds hy)).contMDiffWithinAt
  -- Testing the hom-bundle section on the chart-local frame gives smoothness at `x`.
  have hhom := contMDiffOn_hom_of_localFrame (I := I) (n := ∞)
    (e := trivializationAt E (TangentSpace I) x) (e' := trivializationAt E (TangentSpace I) x)
    (finBasis ℝ E) hsopen
    (by rw [TangentBundle.trivializationAt_baseSet, inter_self]; exact hsub)
    (A := fun y ↦ leviCivita I M σ y)
    (fun j ↦ by simpa only [← chartLocalFrame_eq] using hdir j)
  exact (hhom.contMDiffAt (hsopen.mem_nhds hxs)).contMDiffWithinAt

/-- **The Levi-Civita connection is `C^∞`**, in the set-local form used to read it in a local
frame. -/
theorem contMDiffCovariantDerivativeOn_leviCivita {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E ∞ (leviCivita I M).toFun u where
  contMDiff hσ := contMDiffOn_leviCivita hu hσ

/-- **The Levi-Civita connection is `C^∞`.** -/
instance instContMDiffCovariantDerivativeLeviCivita :
    ContMDiffCovariantDerivative (leviCivita I M) ∞ where
  contMDiff := contMDiffCovariantDerivativeOn_leviCivita isOpen_univ

variable {ι : Type*} (b : Basis ι ℝ E)
  {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]

/-- The scalar Christoffel symbols of the Levi-Civita connection in a local frame are `C^∞` on
the base set of the trivialization defining the frame. -/
theorem contMDiffOn_christoffelSymbol_leviCivita (i j k : ι) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (christoffelSymbol I b e (leviCivita I M).toFun i j k) e.baseSet := by
  have := contMDiffCovariantDerivativeOn_leviCivita (I := I) (M := M) e.open_baseSet
  have : ContMDiffVectorBundle ((∞ : ℕ∞ω) + 1) E (TangentSpace I : M → Type _) I :=
    inferInstanceAs (ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I)
  exact contMDiffOn_christoffelSymbol b i j k

/-- The model-space Christoffel map of the Levi-Civita connection is `C^∞` on the base set of the
trivialization defining its coordinates. -/
theorem contMDiffOn_christoffelMap_leviCivita [Fintype ι] :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) ∞
      (christoffelMap b ((leviCivita I M).isCovariantDerivativeOn (s := e.baseSet)))
      e.baseSet := by
  have := contMDiffCovariantDerivativeOn_leviCivita (I := I) (M := M) e.open_baseSet
  have : ContMDiffVectorBundle ((∞ : ℕ∞ω) + 1) E (TangentSpace I : M → Type _) I :=
    inferInstanceAs (ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I)
  exact contMDiffOn_christoffelMap b _

end CovariantDerivative
