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

On a `C^m` manifold carrying a `C^k` Riemannian metric, the Levi-Civita connection
`CovariantDerivative.leviCivita` is `C^n` as soon as `n + 2 ≤ m` and `n + 1 ≤ k`: it sends a
`C^(n+1)` section of the tangent bundle to a `C^n` section of `Hom(TM, TM)`. This file proves
that, in the class form `ContMDiffCovariantDerivative` which Mathlib's covariant-derivative API
consumes — a class which already carries that one-derivative loss, asking a `C^(n+1)` section to
produce a `C^n` one — together with the set-local form on an arbitrary open set. Taking
`n = m = k = ∞` the loss is invisible and **the Levi-Civita connection of a `C^∞` metric on a
`C^∞` manifold is `C^∞`**, which is the instance
`CovariantDerivative.instContMDiffCovariantDerivativeLeviCivita`.

The proof follows the Koszul formula `2 ⟪∇_X Y, Z⟫ = koszul I X Y Z`. The right-hand side is built
from derivatives of pointwise inner products and from Lie brackets, so it loses exactly one degree
of smoothness; that is where `n + 1 ≤ k` comes from, and the extra degree in `n + 2 ≤ m` is the
one Mathlib's Lie-bracket regularity asks of the manifold. Concretely:

* `TauCeti.Manifold.contMDiffOn_koszul` reads the Koszul expression as a sum of directional
  derivatives of inner products (`ContMDiffOn.contMDiffOn_mvfderiv_apply`) and of inner products
  with Lie brackets (`ContMDiffWithinAt.mlieBracketWithin_vectorField`);
* the fibrewise Riesz dual of `Riemannian.Tensor.contMDiffAt_rieszDual` turns smoothness of the
  numbers `⟪∇_{e_j} σ, e_k⟫` into smoothness of the vector fields `∇_{e_j} σ`, for `e` the
  chart-local frame;
* `TauCeti.Manifold.contMDiffOn_hom_of_localFrame` assembles those directions into the hom-bundle
  section `∇σ` demanded by `ContMDiffCovariantDerivativeOn`.

With the class available, the local Christoffel data of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame` becomes unconditional for
the Levi-Civita connection: its scalar Christoffel symbols and its model-space Christoffel map are
`C^n` on the base set of every trivialization in the atlas.

The ambient orders `m` and `k` are carried as instance arguments and compared to the conclusion by
the hypotheses `n + 2 ≤ m` and `n + 1 ≤ k`, rather than being spelled `n + 2` and `n + 1`
outright, so that the `C^∞` case remains an instantiation: Mathlib's instance search derives
`IsManifold I m M` from `IsManifold I ∞ M` for `m = ∞`, but not `IsManifold I (n + 2) M` for a
variable `n`. The low-order hypotheses `[IsManifold I 2 M]` and
`[IsContMDiffRiemannianBundle I 1 E _]`, which `CovariantDerivative.leviCivita` needs merely to be
written down, are carried for the same reason.

## Main results

* `TauCeti.Manifold.contMDiffOn_koszul`: the Koszul expression of three `C^(n+1)` sections is
  `C^n`.
* `CovariantDerivative.contMDiffOn_leviCivita`: on an open set, the Levi-Civita connection carries
  a `C^(n+1)` section to a `C^n` section of `Hom(TM, TM)`.
* `CovariantDerivative.contMDiffCovariantDerivativeOn_leviCivita` and the instance
  `CovariantDerivative.instContMDiffCovariantDerivativeLeviCivita`: **the Levi-Civita connection
  is of class `C^n`**, and in particular `C^∞` for a `C^∞` metric.
* `CovariantDerivative.contMDiffOn_christoffelSymbol_leviCivita` and
  `CovariantDerivative.contMDiffOn_christoffelMap_leviCivita`: its Christoffel symbols and its
  model-space Christoffel map are `C^n` on a trivialization base set.

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
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {n m k : ℕ∞ω}
  [IsManifold I 1 M] [IsManifold I m M]
  [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]

/-- **The Koszul expression of three `C^(n+1)` sections is `C^n`.** Both the derivative terms and
the Lie-bracket terms lose one degree of smoothness, whence the two hypotheses on the smoothness
of the manifold and of the metric. -/
theorem contMDiffOn_koszul {s : Set M} (hs : IsOpen s) (hm : n + 2 ≤ m) (hk : n + 1 ≤ k)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (X y)) s)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Y y)) s)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (Z y)) s) :
    ContMDiffOn I 𝓘(ℝ) n (koszul I X Y Z) s := by
  -- The two smoothness levels that Mathlib's Lie-bracket regularity asks of the manifold; over
  -- `ℝ` the `minSmoothness` guard is the identity.
  have hmin : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := m) (by simpa using le_add_self.trans hm)
  have hsucc : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  -- The metric at the level of the sections, and at the level of the conclusion for the inner
  -- products against a Lie bracket.
  have hmetric : IsContMDiffRiemannianBundle I (n + 1) E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) hk
  have hmetric' : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) (le_self_add.trans hk)
  have hbracket {U V : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (V y)) s) :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
        (fun y ↦ TotalSpace.mk' E y (mlieBracket I U V y)) s := by
    have hbr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
        (fun y ↦ TotalSpace.mk' E y (mlieBracketWithin I U V s y)) s := fun y hy ↦
      (hU y hy).mlieBracketWithin_vectorField (hV y hy) hs.uniqueMDiffOn hy (by simp)
    refine hbr.congr fun y hy ↦ ?_
    rw [mlieBracketWithin_of_isOpen hs hy]
  have hinner {j : ℕ∞ω} [IsContMDiffRiemannianBundle I j E (fun x : M ↦ TangentSpace I x)]
      {U V : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) j (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) j (fun y ↦ TotalSpace.mk' E y (V y)) s) :
      ContMDiffOn I 𝓘(ℝ) j (fun y ↦ (inner ℝ (U y) (V y) : ℝ)) s :=
    ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
      (b := id) hU hV
  have hderiv {U V W : Π x : M, TangentSpace I x}
      (hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (U y)) s)
      (hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (V y)) s)
      (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (W y)) s) :
      ContMDiffOn I 𝓘(ℝ) n
        (fun y ↦ mvfderiv I (fun z ↦ (inner ℝ (U z) (V z) : ℝ)) y (W y)) s :=
    ContMDiffOn.contMDiffOn_mvfderiv_apply (hinner hU hV) hs (hW.of_le le_self_add) le_rfl
  refine ContMDiffOn.congr ?_ fun y _ ↦ koszul_apply X Y Z y
  exact (((hderiv hY hZ hX).add (hderiv hZ hX hY)).sub (hderiv hX hY hZ)).add
    (hinner (hbracket hX hY) (hZ.of_le le_self_add))
      |>.sub (hinner (hbracket hX hZ) (hY.of_le le_self_add))
      |>.sub (hinner (hbracket hY hZ) (hX.of_le le_self_add))

end TauCeti.Manifold

namespace CovariantDerivative

open TauCeti TauCeti.Manifold Riemannian.Tensor

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

section Finite

variable {n m k : ℕ∞ω} [IsManifold I m M]
  [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]

/-- **The Levi-Civita connection differentiates with one derivative lost.** On an open set `u`, a
section of the tangent bundle which is `C^(n+1)` on `u` has a covariant derivative which is `C^n`
on `u` as a section of `Hom(TM, TM)`. -/
theorem contMDiffOn_leviCivita {u : Set M} (hu : IsOpen u) (hm : n + 2 ≤ m) (hk : n + 1 ≤ k)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun y ↦ TotalSpace.mk' E y (σ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ (TangentSpace I y →L[ℝ] TangentSpace I y)) y (leviCivita I M σ y)) u := by
  have hone : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  have hsucc : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  have hmetric : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) (le_self_add.trans hk)
  have hbundle : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  intro x hx
  -- Work on the intersection of `u` with the chart domain at `x`, where the chart-local frame
  -- and the fibrewise Riesz dual are available.
  set s : Set M := u ∩ (chartAt H x).source
  have hsopen : IsOpen s := hu.inter (chartAt H x).open_source
  have hsub : s ⊆ (chartAt H x).source := inter_subset_right
  have hxs : x ∈ s := ⟨hx, mem_chart_source H x⟩
  have hσs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1)
      (fun y ↦ TotalSpace.mk' E y (σ y)) s := hσ.mono inter_subset_left
  have hframe (i : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1)
      (fun y ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) x i y)) s :=
    (contMDiffOn_chartLocalFrame (I := I) (n := n + 1) x i).mono
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hsub)
  have hσd {y : M} (hy : y ∈ s) : MDiffAt (T% σ) y :=
    (hσs.mdifferentiableOn (by simp)).mdifferentiableAt (hsopen.mem_nhds hy)
  have hframed (i : Fin (finrank ℝ E)) {y : M} (hy : y ∈ s) :
      MDiffAt (T% (chartLocalFrame (I := I) x i)) y :=
    ((hframe i).mdifferentiableOn (by simp)).mdifferentiableAt (hsopen.mem_nhds hy)
  -- Each direction of the connection is the Riesz dual of half the Koszul functional.
  have hdir (j : Fin (finrank ℝ E)) : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y ↦ TotalSpace.mk' E y (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) s := by
    have hrepr (y : M) : rieszDual (I := I) y ((rieszDual (I := I) y).symm
        (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) =
        leviCivita I M σ y (chartLocalFrame (I := I) x j y) :=
      LinearIsometryEquiv.apply_symm_apply _ _
    have hval (y : M) (w : TangentSpace I y) :
        ((rieszDual (I := I) y).symm (leviCivita I M σ y (chartLocalFrame (I := I) x j y))) w =
          inner ℝ (leviCivita I M σ y (chartLocalFrame (I := I) x j y)) w := by
      conv_rhs => rw [← hrepr y]
      exact (inner_rieszDual _ w).symm
    have heval (l : Fin (finrank ℝ E)) : ContMDiffOn I 𝓘(ℝ) n
        (fun y ↦ ((rieszDual (I := I) y).symm
          (leviCivita I M σ y (chartLocalFrame (I := I) x j y)))
            (chartLocalFrame (I := I) x l y)) s := by
      have hmul : ContMDiffOn I 𝓘(ℝ) n (fun y ↦ (2 : ℝ)⁻¹ *
          koszul I (chartLocalFrame (I := I) x j) σ (chartLocalFrame (I := I) x l) y) s :=
        contMDiffOn_const.mul
          (contMDiffOn_koszul hsopen hm hk (hframe j) hσs (hframe l))
      refine hmul.congr fun y hy ↦ ?_
      have h := two_inner_leviCivita_eq_koszul (I := I) (M := M)
        (hframed j hy) (hσd hy) (hframed l hy)
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
    exact fun y hy ↦ (contMDiffAt_rieszDual (I := I) (n := n) x (hsub hy)
      (Φ := fun y ↦ (rieszDual (I := I) y).symm
        (leviCivita I M σ y (chartLocalFrame (I := I) x j y)))
      fun l ↦ (heval l).contMDiffAt (hsopen.mem_nhds hy)).contMDiffWithinAt
  -- Testing the hom-bundle section on the chart-local frame gives smoothness at `x`.
  have hhom := contMDiffOn_hom_of_localFrame (I := I) (n := n)
    (e := trivializationAt E (TangentSpace I) x) (e' := trivializationAt E (TangentSpace I) x)
    (finBasis ℝ E) hsopen
    (by rw [TangentBundle.trivializationAt_baseSet, inter_self]; exact hsub)
    (A := fun y ↦ leviCivita I M σ y)
    (fun j ↦ by simpa only [← chartLocalFrame_def] using hdir j)
  exact (hhom.contMDiffAt (hsopen.mem_nhds hxs)).contMDiffWithinAt

/-- **The Levi-Civita connection is of class `C^n`**, in the set-local form used to read it in a
local frame. -/
theorem contMDiffCovariantDerivativeOn_leviCivita {u : Set M} (hu : IsOpen u)
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) :
    ContMDiffCovariantDerivativeOn E n (leviCivita I M).toFun u where
  contMDiff hσ := contMDiffOn_leviCivita hu hm hk hσ

variable {ι : Type*} (b : Basis ι ℝ E)
  {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]

/-- The scalar Christoffel symbols of the Levi-Civita connection in a local frame are `C^n` on
the base set of the trivialization defining the frame. -/
theorem contMDiffOn_christoffelSymbol_leviCivita (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) (i j l : ι) :
    ContMDiffOn I 𝓘(ℝ) n
      (christoffelSymbol I b e (leviCivita I M).toFun i j l) e.baseSet := by
  have := contMDiffCovariantDerivativeOn_leviCivita (I := I) (M := M) e.open_baseSet hm hk
  have hone : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  have hsucc : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact contMDiffOn_christoffelSymbol b i j l

/-- The model-space Christoffel map of the Levi-Civita connection is `C^n` on the base set of the
trivialization defining its coordinates. -/
theorem contMDiffOn_christoffelMap_leviCivita [Fintype ι] (hm : n + 2 ≤ m) (hk : n + 1 ≤ k) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (christoffelMap b ((leviCivita I M).isCovariantDerivativeOn (s := e.baseSet)))
      e.baseSet := by
  have := contMDiffCovariantDerivativeOn_leviCivita (I := I) (M := M) e.open_baseSet hm hk
  have hone : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  have hsucc : IsManifold I (n + 1 + 1) M :=
    IsManifold.of_le (n := m) (by rwa [add_assoc, one_add_one_eq_two])
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact contMDiffOn_christoffelMap b _

end Finite

/-- **The Levi-Civita connection of a `C^∞` metric on a `C^∞` manifold is `C^∞`.** -/
instance instContMDiffCovariantDerivativeLeviCivita [IsManifold I ∞ M]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] :
    ContMDiffCovariantDerivative (leviCivita I M) ∞ where
  contMDiff := contMDiffCovariantDerivativeOn_leviCivita (n := ∞) (m := ∞) (k := ∞)
    isOpen_univ le_rfl le_rfl

end CovariantDerivative
