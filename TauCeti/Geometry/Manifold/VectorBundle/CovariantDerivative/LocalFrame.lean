/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Covariant derivatives read in a local frame

Let `V → M` be a finite-rank smooth vector bundle and let `e` be a trivialization of `V` with
`b` a basis of the model fibre, so that `e.localFrame b` is a smooth frame of `V` over
`e.baseSet`. This file reads a covariant derivative on `V` in that frame.

Writing `σ = ∑ i, σⁱ • eᵢ` over `e.baseSet`, any covariant derivative `∇` satisfies

`∇ σ = ∑ i, dσⁱ ⊗ eᵢ + ∑ i, σⁱ • ∇ eᵢ`

on `e.baseSet`. The first summand is itself a covariant derivative over `e.baseSet`, the *flat*
one attached to the frame; it is `frameCovariantDerivative`, and it witnesses that covariant
derivatives always exist locally. The second summand is tensorial in `σ`, and is the Christoffel
form `christoffelForm` of `∇` in the frame: `∇` is the flat derivative plus `christoffelForm`.

Specializing to the tangent bundle and expanding `∇_{eᵢ} eⱼ` again in the frame gives the scalar
Christoffel symbols `christoffelSymbol`; they are `C^∞` on `e.baseSet` for a `C^∞` covariant
derivative, and they give the classical coordinate formula for `∇ σ` along a frame direction.

## Main definitions and results

* `TauCeti.Manifold.frameCovariantDerivative`: the flat covariant derivative attached to a local
  frame, and `TauCeti.Manifold.isCovariantDerivativeOn_frameCovariantDerivative`, the proof that
  it is a covariant derivative over the trivialization base set.
* `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum`: the local frame
  formula for an arbitrary covariant derivative.
* `TauCeti.Manifold.covariantDerivative_eq_of_localFrame_eq`: two covariant derivatives which
  agree on the frame sections at a point agree at that point on every section differentiable
  there.
* `TauCeti.Manifold.christoffelForm`: the Christoffel form of a covariant derivative in a local
  frame, with `TauCeti.Manifold.christoffelForm_apply` computing it and
  `TauCeti.Manifold.covariantDerivative_eq_add_christoffelForm` expressing the covariant
  derivative as the flat one plus it.
* `TauCeti.Manifold.christoffelSymbol`: the scalar Christoffel symbols of a covariant derivative
  on the tangent bundle in a local frame, with
  `TauCeti.Manifold.covariantDerivative_localFrame_eq_sum_christoffelSymbol` expanding
  `∇_{eᵢ} eⱼ`, `TauCeti.Manifold.contMDiffOn_christoffelSymbol` their smoothness, and
  `TauCeti.Manifold.christoffelForm_localFrame_apply` identifying them with the frame components
  of the Christoffel form.
* `TauCeti.Manifold.christoffelMap`: the Christoffel form transported to a continuous bilinear map
  on the model space, with `TauCeti.Manifold.contMDiffOn_christoffelMap` proving its smoothness.
* `TauCeti.Manifold.covariantDerivative_apply_localFrame_eq_sum`: the classical coordinate
  formula `(∇_{eᵢ} σ)ᵏ = dσᵏ(eᵢ) + ∑ j, σʲ Γᵏᵢⱼ`.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 2, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle FiberBundle Module Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.Manifold

section GeneralFibre

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {x : M} {σ : Π x : M, V x}
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

variable [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-! ### The flat covariant derivative of a local frame -/

variable (I) in
/-- The flat covariant derivative attached to the local frame induced by a trivialization `e` of
`V` and a basis `b` of the model fibre: it differentiates the coefficient functions of a section
and keeps the frame fixed. It is a covariant derivative over `e.baseSet`, by
`isCovariantDerivativeOn_frameCovariantDerivative`; outside that set it carries a junk value. -/
def frameCovariantDerivative (b : Basis ι 𝕜 F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[𝕜] V x :=
  ∑ i, (mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
    (e.localFrame b i x)

/-- The flat covariant derivative of the frame, evaluated on a tangent vector. -/
theorem frameCovariantDerivative_apply (v : TangentSpace I x) :
    frameCovariantDerivative I b e σ x v =
      ∑ i, mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
        e.localFrame b i x := by
  simp [frameCovariantDerivative]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- The flat frame derivative satisfies the covariant-derivative axioms on the base set of the
trivialization defining the frame. -/
theorem isCovariantDerivativeOn_frameCovariantDerivative :
    IsCovariantDerivativeOn F (frameCovariantDerivative I b e) e.baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    have key (i : ι) :
        mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) (σ + σ')) x =
          mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x +
            mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ') x := by
      have hsplit : (LinearMap.piApply (e.localFrameCoeff I b i)) (σ + σ') =
          (LinearMap.piApply (e.localFrameCoeff I b i)) σ +
            (LinearMap.piApply (e.localFrameCoeff I b i)) σ' := by
        ext y; simp
      rw [hsplit, mvfderiv_add (mdifferentiableAt_localFrameCoeff b hx hσ i)
        (mdifferentiableAt_localFrameCoeff b hx hσ' i)]
    ext v
    simp only [frameCovariantDerivative_apply, add_apply, key, add_smul,
      Finset.sum_add_distrib]
  leibniz {σ g x} hσ hg hx := by
    have hcoeff (i : ι) : MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x :=
      mdifferentiableAt_localFrameCoeff b hx hσ i
    have key (i : ι) (v : TangentSpace I x) :
        mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ)) x v =
          g x * mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v +
            mvfderiv I g x v * e.localFrameCoeff I b i x (σ x) := by
      have hsplit : (LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ) =
          g * (LinearMap.piApply (e.localFrameCoeff I b i)) σ := by
        ext y; simp
      rw [hsplit, mvfderiv_mul hg (hcoeff i)]
      simp [mul_comm]
    ext v
    simp only [frameCovariantDerivative_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, key, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum]
    rw [← e.eq_sum_localFrameCoeff_smul (s := σ) hx]

/-! ### The local frame formula -/

/-- The local frame formula: over the base set of a trivialization, a covariant derivative is the
flat derivative of the frame coefficients plus the coefficients times the covariant derivatives
of the frame sections. -/
theorem covariantDerivative_eq_frameCovariantDerivative_add_sum
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = frameCovariantDerivative I b e σ x +
      ∑ i, e.localFrameCoeff I b i x (σ x) • cov (e.localFrame b i) x := by
  classical
  have hcoeff (i : ι) : MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x :=
    mdifferentiableAt_localFrameCoeff b hx hσ i
  have hfr : IsLocalFrameOn I F 1 (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I 1 b
  have hframe (i : ι) : MDiffAt (T% (e.localFrame b i)) x :=
    ((hfr.contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt
      (e.open_baseSet.mem_nhds hx)
  have hterm (i : ι) :
      MDiffAt (T% ((LinearMap.piApply (e.localFrameCoeff I b i)) σ • e.localFrame b i)) x :=
    (hcoeff i).smul_section (hframe i)
  have hτdiff : MDiffAt
      (T% (∑ i, (LinearMap.piApply (e.localFrameCoeff I b i)) σ • e.localFrame b i)) x := by
    simpa [Finset.sum_apply] using MDifferentiableAt.sum_section
      (t := fun i (y : M) ↦ (LinearMap.piApply (e.localFrameCoeff I b i)) σ y • e.localFrame b i y)
      (s := (Finset.univ : Finset ι)) fun i _ ↦ hterm i
  have hexp : ∀ᶠ y in 𝓝 x, σ y = ∑ i, e.localFrameCoeff I b i y (σ y) • e.localFrame b i y :=
    e.eventually_eq_localFrame_sum_coeff_smul (s := σ) b hx
  have hστ : ∀ᶠ y in 𝓝 x,
      σ y = (∑ i, (LinearMap.piApply (e.localFrameCoeff I b i)) σ • e.localFrame b i) y :=
    hexp.mono fun y hy ↦ by simpa [Finset.sum_apply] using hy
  have hleib (i : ι) :
      cov ((LinearMap.piApply (e.localFrameCoeff I b i)) σ • e.localFrame b i) x =
        e.localFrameCoeff I b i x (σ x) • cov (e.localFrame b i) x +
          (mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
            (e.localFrame b i x) :=
    hcov.leibniz (hframe i) (hcoeff i) hx
  rw [hcov.congr_of_eventuallyEq hσ hτdiff (e.open_baseSet.mem_nhds hx) hστ,
    covariantDerivative_sum hcov hx (fun i _ ↦ hterm i)]
  simp only [hleib, Finset.sum_add_distrib]
  rw [add_comm]
  rw [frameCovariantDerivative]

omit [Fintype ι] in
/-- Two covariant derivatives over the base set of a trivialization which agree on the frame
sections at a point agree there on every section differentiable at that point. -/
theorem covariantDerivative_eq_of_localFrame_eq [Finite ι]
    {cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    (hcov' : IsCovariantDerivativeOn F cov' e.baseSet) (hx : x ∈ e.baseSet)
    (hframe : ∀ i, cov (e.localFrame b i) x = cov' (e.localFrame b i) x)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov' σ x := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hσ,
    covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov' hx hσ]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hframe i]

/-! ### The Christoffel form -/

/-- The Christoffel form of a covariant derivative in a local frame: the endomorphism-valued
one-form by which the covariant derivative differs from the flat derivative
`frameCovariantDerivative` of the frame. -/
def christoffelForm (hcov : IsCovariantDerivativeOn F cov e.baseSet) :
    Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  hcov.difference (isCovariantDerivativeOn_frameCovariantDerivative b)

/-- A covariant derivative is the flat derivative of its frame plus its Christoffel form. -/
theorem covariantDerivative_eq_add_christoffelForm
    (hcov : IsCovariantDerivativeOn F cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = frameCovariantDerivative I b e σ x + christoffelForm b hcov x (σ x) := by
  rw [christoffelForm, IsCovariantDerivativeOn.difference_apply _ _ hx hσ]
  abel

/-- The Christoffel form is the frame expansion of the covariant derivatives of the frame
sections. -/
theorem christoffelForm_apply (hcov : IsCovariantDerivativeOn F cov e.baseSet)
    (hx : x ∈ e.baseSet) (v : V x) :
    christoffelForm b hcov x v = ∑ i, e.localFrameCoeff I b i x v • cov (e.localFrame b i) x := by
  have hext : MDiffAt (T% (extend F v)) x := mdifferentiableAt_extend I F v
  have hv : (extend F v) x = v := extend_apply_self F v
  have h := covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hext
  rw [covariantDerivative_eq_add_christoffelForm b hcov hx hext, hv] at h
  exact add_right_injective _ h

end GeneralFibre

/-! ### Christoffel symbols on the tangent bundle -/

section TangentBundle

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {ι : Type*} (b : Basis ι 𝕜 E)
  {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]
  {x : M}
  {cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}

variable (I) in
/-- The Christoffel symbols of a covariant derivative on the tangent bundle, in the local frame
induced by a trivialization `e` and a basis `b` of the model space: `christoffelSymbol I b e cov
i j k x` is the `k`-th coefficient of `∇_{eᵢ} eⱼ` at `x`. Outside `e.baseSet` it carries a junk
value. -/
def christoffelSymbol (b : Basis ι 𝕜 E)
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))
    (i j k : ι) (x : M) : 𝕜 :=
  e.localFrameCoeff I b k x (cov (e.localFrame b j) x (e.localFrame b i x))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The defining formula for the Christoffel symbols. -/
@[simp]
theorem christoffelSymbol_apply (i j k : ι) :
    christoffelSymbol I b e cov i j k x =
      e.localFrameCoeff I b k x (cov (e.localFrame b j) x (e.localFrame b i x)) :=
  (rfl)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The Christoffel symbols expand the covariant derivative of a frame section along a frame
direction back in the frame. -/
theorem covariantDerivative_localFrame_eq_sum_christoffelSymbol [Fintype ι] (hx : x ∈ e.baseSet)
    (i j : ι) :
    cov (e.localFrame b j) x (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  have hexp : extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x =
      ∑ k, e.localFrameCoeff I b k x
          (extend E (cov (e.localFrame b j) x (e.localFrame b i x)) x) • e.localFrame b k x :=
    e.eq_sum_localFrameCoeff_smul hx
  rw [extend_apply_self] at hexp
  exact hexp

variable (I) in
private def christoffelMapOfSymbols [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))
    (x : M) : E →L[𝕜] E →L[𝕜] E :=
  ∑ j, ∑ i, ∑ k, christoffelSymbol I b e cov i j k x •
    (b.coord j).toContinuousLinearMap.smulRight
      ((b.coord i).toContinuousLinearMap.smulRight (b k))

private theorem christoffelMapOfSymbols_apply_basis [Fintype ι] (i j : ι) :
    christoffelMapOfSymbols I b e cov x (b j) (b i) =
      ∑ k, christoffelSymbol I b e cov i j k x • b k := by
  classical
  simp [christoffelMapOfSymbols, Basis.coord_apply, Finsupp.single_apply]

/-- The Christoffel form transported through the tangent-bundle trivialization to a
model-space-valued continuous bilinear map. -/
def christoffelMap [Fintype ι] (hcov : IsCovariantDerivativeOn E cov e.baseSet) (x : M) :
    E →L[𝕜] E →L[𝕜] E :=
  ((e.continuousLinearMap (RingHom.id 𝕜)
      (e.continuousLinearMap (RingHom.id 𝕜) e))
    ⟨x, christoffelForm b hcov x⟩).2

/-- The Christoffel symbols of a `C^n` covariant derivative are `C^n` on the base set of the
trivialization defining the frame. -/
theorem contMDiffOn_christoffelSymbol {n : ℕ∞ω}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] (i j k : ι) :
    CMDiff[e.baseSet] n (christoffelSymbol I b e cov i j k) := by
  have hj : CMDiff[e.baseSet] (n + 1) (T% (e.localFrame b j)) :=
    e.contMDiffOn_localFrame_baseSet (n + 1) b j
  have hi : CMDiff[e.baseSet] n (T% (e.localFrame b i)) :=
    e.contMDiffOn_localFrame_baseSet n b i
  have hcov : ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E)
        (E := fun y : M ↦ (TangentSpace I y →L[𝕜] TangentSpace I y)) y
        (cov (e.localFrame b j) y)) e.baseSet :=
    ContMDiffCovariantDerivativeOn.contMDiff hj
  have happ : CMDiff[e.baseSet] n
      (T% (fun y ↦ cov (e.localFrame b j) y (e.localFrame b i y))) :=
    ContMDiffOn.clm_bundle_apply hcov hi
  exact contMDiffOn_baseSet_localFrameCoeff b happ k

variable {σ : Π x : M, TangentSpace I x}

/-- The frame components of the Christoffel form are the Christoffel symbols. -/
theorem christoffelForm_localFrame_apply [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j : ι) :
    christoffelForm b hcov x (e.localFrame b j x) (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x := by
  classical
  rw [christoffelForm_apply b hcov hx]
  have hcollapse : ∑ l, e.localFrameCoeff I b l x (e.localFrame b j x) • cov (e.localFrame b l) x
      = cov (e.localFrame b j) x := by
    simp [localFrameCoeff_localFrame b hx]
  rw [hcollapse]
  exact covariantDerivative_localFrame_eq_sum_christoffelSymbol b hx i j

/-- The basis coefficients of the model-space Christoffel map are the scalar Christoffel
symbols. -/
@[simp]
theorem christoffelMap_apply_basis [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j : ι) :
    christoffelMap b hcov x (b j) (b i) =
      ∑ k, christoffelSymbol I b e cov i j k x • b k := by
  classical
  simp only [christoffelMap, Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [e.symmL_apply hx]
  have hxe : x ∈ (e.continuousLinearMap (RingHom.id 𝕜) e).baseSet := by simp [hx]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := 𝕜) (e.continuousLinearMap (RingHom.id 𝕜) e) hxe]
  simp only [Bundle.Trivialization.continuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]
  rw [e.symmL_apply hx]
  have hframe (l : ι) : e.symm x (b l) = e.localFrame b l x := by
    simp [Bundle.Trivialization.localFrame_apply_of_mem_baseSet,
      Bundle.Trivialization.basisAt, hx]
  rw [hframe j, hframe i]
  rw [christoffelForm_localFrame_apply b hcov hx i j]
  simp [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem, hx,
    Bundle.Trivialization.localFrame_apply_of_mem_baseSet, Bundle.Trivialization.basisAt]

/-- The scalar basis coefficients of the model-space Christoffel map are precisely the
Christoffel symbols. -/
theorem coord_christoffelMap_apply_basis [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) (i j k : ι) :
    b.coord k (christoffelMap b hcov x (b j) (b i)) =
      christoffelSymbol I b e cov i j k x := by
  classical
  rw [christoffelMap_apply_basis b hcov hx i j]
  simp [Basis.coord_apply, Finsupp.single_apply]

private theorem christoffelMap_eq_of_mem [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet) :
    christoffelMap b hcov x = christoffelMapOfSymbols I b e cov x := by
  -- Both sides are continuous linear maps, so they are determined by their underlying linear
  -- maps (`ContinuousLinearMap.coe_injective`), hence by their values on the basis `b`; the
  -- coercion is transparent on applications by `ContinuousLinearMap.coe_coe`.
  refine ContinuousLinearMap.coe_injective (b.ext fun j ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [christoffelMap_apply_basis b hcov hx i j, christoffelMapOfSymbols_apply_basis b i j]

/-- The model-space Christoffel map of a `C^n` covariant derivative is `C^n` on the base set of
the trivialization defining its coordinates. -/
theorem contMDiffOn_christoffelMap [Fintype ι] {n : ℕ∞ω}
    (hcov : IsCovariantDerivativeOn E cov e.baseSet)
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    [ContMDiffCovariantDerivativeOn E n cov e.baseSet] :
    CMDiff[e.baseSet] n (christoffelMap b hcov) := by
  classical
  have hsymbols : CMDiff[e.baseSet] n (christoffelMapOfSymbols I b e cov) := by
    unfold christoffelMapOfSymbols
    apply contMDiffOn_finsetSum
    intro j _
    apply contMDiffOn_finsetSum
    intro i _
    apply contMDiffOn_finsetSum
    intro k _
    exact (contMDiffOn_christoffelSymbol b i j k).smul contMDiffOn_const
  exact hsymbols.congr fun y hy ↦ christoffelMap_eq_of_mem b hcov hy

/-- The classical coordinate formula for a covariant derivative on the tangent bundle: along the
frame direction `eᵢ`, the `k`-th component of `∇ σ` is the derivative of the `k`-th coefficient of
`σ` plus the Christoffel contraction `∑ j, σʲ Γᵏᵢⱼ`. -/
theorem covariantDerivative_apply_localFrame_eq_sum [Fintype ι]
    (hcov : IsCovariantDerivativeOn E cov e.baseSet) (hx : x ∈ e.baseSet)
    (hσ : MDiffAt (T% σ) x) (i : ι) :
    cov σ x (e.localFrame b i x) =
      ∑ k, (mvfderiv I ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x (e.localFrame b i x) +
        ∑ j, e.localFrameCoeff I b j x (σ x) * christoffelSymbol I b e cov i j k x) •
          e.localFrame b k x := by
  have hΓ (j : ι) : cov (e.localFrame b j) x (e.localFrame b i x) =
      ∑ k, christoffelSymbol I b e cov i j k x • e.localFrame b k x :=
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b hx i j
  rw [covariantDerivative_eq_frameCovariantDerivative_add_sum b hcov hx hσ]
  simp only [add_apply, frameCovariantDerivative_apply, sum_apply, smul_apply, hΓ,
    Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm]

end TangentBundle

end TauCeti.Manifold
