/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex

/-!
# Pseudoholomorphic maps between almost complex manifolds

A map `u : M → M'` between manifolds carrying smooth almost complex structures `j` and `J` is
*pseudoholomorphic* (a `J`-holomorphic curve, when `M` is a Riemann surface) at `x` when it has a
manifold Fréchet derivative there which intertwines the two structures:
`du_x ∘ j(x) = J(u x) ∘ du_x`. This is the nonlinear Cauchy--Riemann equation of Lane F2.1 of the
analytic Heegaard Floer roadmap, and the first predicate of that roadmap whose target structure
genuinely varies over a manifold rather than over a normed space.

## Why the name is not `IsJHolomorphic`

`TauCeti.IsJHolomorphic` is already the varying-structure predicate for maps between *normed
spaces* (`TauCeti/Geometry/Symplectic/JHolomorphic/Varying.lean`), which is the local coordinate
model of this one, and `TauCeti.IsConstStructureJHolomorphic` is the flat, single-structure model
below that. The manifold-level predicate therefore takes the equally standard name
*pseudoholomorphic* (Gromov's term, used interchangeably with `J`-holomorphic in
McDuff--Salamon). `isPseudoholomorphicAt_iff_isJHolomorphicAt` below identifies the two on a
model vector space, so the naming records a difference of setting, not of mathematics.

## Main declarations

* `TauCeti.IsPseudoholomorphicWithinAt`, `TauCeti.IsPseudoholomorphicAt`: the Cauchy--Riemann
  equation for the derivative within a set, respectively at a point.
* `TauCeti.IsPseudoholomorphicOn`, `TauCeti.IsPseudoholomorphic`: the setwise and global
  predicates.
* `TauCeti.IsPseudoholomorphicAt.mfderiv_apply_commute` and
  `TauCeti.IsPseudoholomorphicAt.mfderiv_isComplexLinear`: the manifold derivative of a
  pseudoholomorphic map intertwines the two structures, and their within-set analogues.
* `TauCeti.IsPseudoholomorphicAt.comp`: pseudoholomorphic maps compose.
* `TauCeti.isPseudoholomorphicAt_neg_neg_iff` and its within-set, setwise, and global analogues:
  reversing both structures changes nothing.
* `TauCeti.isPseudoholomorphicAt_stdComplexLine_iff`: for a curve out of the standard complex
  line the equation reduces to the single coordinate identity `∂_t w = J(w) ∂_s w`.
* `TauCeti.isPseudoholomorphicAt_iff_isJHolomorphicAt` and its within-set, setwise, and global
  analogues: on model vector spaces the predicate is the existing normed-space one.
* `TauCeti.isPseudoholomorphicAt_constSmooth_iff` and its within-set, setwise, and global
  analogues: for constant structures on model vector spaces it is the flat, constant-structure
  predicate.

No regularity beyond the existence of a derivative is imposed: as with the normed-space
predicates, smoothness of `u` is a separate hypothesis for the results that need it, and taming
or compatibility with a symplectic form is not part of the definition. This keeps the analytic
hypotheses unbundled, as the roadmap's standing conventions require.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the Cauchy--Riemann equation is `du ∘ j = J ∘ du`.
-/

public section

open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E H M E' H' M' E'' H'' M'' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
variable [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' ∞ M'']

/-- A map between almost complex manifolds is pseudoholomorphic within a set at a point when it
has a manifold derivative within that set intertwining the source structure at the point with the
target structure at the image point. -/
def IsPseudoholomorphicWithinAt (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (s : Set M) (x : M) : Prop :=
  ∃ u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x),
    HasMFDerivWithinAt I I' u s x u' ∧ ∀ w, u' (j x w) = J (u x) (u' w)

/-- A map between almost complex manifolds is pseudoholomorphic at a point when it has a manifold
derivative there intertwining the source structure at the point with the target structure at the
image point. -/
def IsPseudoholomorphicAt (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) : Prop :=
  ∃ u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x),
    HasMFDerivAt I I' u x u' ∧ ∀ w, u' (j x w) = J (u x) (u' w)

/-- A map is pseudoholomorphic on a set when it is pseudoholomorphic within that set at each of
its points. -/
def IsPseudoholomorphicOn (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (s : Set M) : Prop :=
  ∀ x ∈ s, IsPseudoholomorphicWithinAt j J u s x

/-- A map is pseudoholomorphic when it is pseudoholomorphic at every point. -/
def IsPseudoholomorphic (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') : Prop :=
  ∀ x, IsPseudoholomorphicAt j J u x

variable {j : SmoothAlmostComplexStructure I M} {J : SmoothAlmostComplexStructure I' M'}
  {K : SmoothAlmostComplexStructure I'' M''} {u : M → M'} {v : M' → M''} {s t : Set M}
  {x : M}

/-! ### Building and unfolding the predicates -/

/-- Build pseudoholomorphicity at a point from a manifold derivative satisfying the pointwise
Cauchy--Riemann equation. -/
theorem isPseudoholomorphicAt_of_hasMFDerivAt
    {u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x)} (hu : HasMFDerivAt I I' u x u')
    (hlin : ∀ w, u' (j x w) = J (u x) (u' w)) : IsPseudoholomorphicAt j J u x :=
  ⟨u', hu, hlin⟩

/-- Build pseudoholomorphicity within a set from a manifold derivative within that set satisfying
the pointwise Cauchy--Riemann equation. -/
theorem isPseudoholomorphicWithinAt_of_hasMFDerivWithinAt
    {u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x)}
    (hu : HasMFDerivWithinAt I I' u s x u')
    (hlin : ∀ w, u' (j x w) = J (u x) (u' w)) : IsPseudoholomorphicWithinAt j J u s x :=
  ⟨u', hu, hlin⟩

/-- The Cauchy--Riemann equation of the definition says exactly that the derivative is a
complex-linear map from the source tangent space at the point to the target tangent space at the
image point. -/
theorem isPseudoholomorphicAt_iff_isComplexLinearMap :
    IsPseudoholomorphicAt j J u x ↔
      ∃ u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x),
        HasMFDerivAt I I' u x u' ∧
          IsComplexLinearMap (j.almostComplexStructureAt x)
            (J.almostComplexStructureAt (u x)) u'.toLinearMap := by
  refine exists_congr fun u' ↦ and_congr_right fun _ ↦ ?_
  rw [isComplexLinearMap_iff_apply]
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ContinuousLinearMap.coe_coe]

/-- The within-set Cauchy--Riemann equation of the definition says exactly that the derivative
within the set is complex-linear. -/
theorem isPseudoholomorphicWithinAt_iff_isComplexLinearMap :
    IsPseudoholomorphicWithinAt j J u s x ↔
      ∃ u' : TangentSpace I x →L[ℝ] TangentSpace I' (u x),
        HasMFDerivWithinAt I I' u s x u' ∧
          IsComplexLinearMap (j.almostComplexStructureAt x)
            (J.almostComplexStructureAt (u x)) u'.toLinearMap := by
  refine exists_congr fun u' ↦ and_congr_right fun _ ↦ ?_
  rw [isComplexLinearMap_iff_apply]
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ContinuousLinearMap.coe_coe]

/-- Restate setwise pseudoholomorphicity as the pointwise within-set condition. -/
theorem isPseudoholomorphicOn_iff :
    IsPseudoholomorphicOn j J u s ↔ ∀ x ∈ s, IsPseudoholomorphicWithinAt j J u s x :=
  Iff.rfl

/-- Restate global pseudoholomorphicity as pointwise pseudoholomorphicity everywhere. -/
theorem isPseudoholomorphic_iff :
    IsPseudoholomorphic j J u ↔ ∀ x, IsPseudoholomorphicAt j J u x :=
  Iff.rfl

/-- The continuous-linear manifold derivative witnessing pseudoholomorphicity at a point. -/
theorem IsPseudoholomorphicAt.hasMFDerivAt (hu : IsPseudoholomorphicAt j J u x) :
    HasMFDerivAt I I' u x
      (Classical.choose (isPseudoholomorphicAt_iff_isComplexLinearMap.mp hu)) :=
  (Classical.choose_spec (isPseudoholomorphicAt_iff_isComplexLinearMap.mp hu)).1

/-- The chosen manifold derivative at a pseudoholomorphic point is complex-linear. -/
theorem IsPseudoholomorphicAt.derivative_isComplexLinear
    (hu : IsPseudoholomorphicAt j J u x) :
    IsComplexLinearMap (j.almostComplexStructureAt x) (J.almostComplexStructureAt (u x))
      (Classical.choose (isPseudoholomorphicAt_iff_isComplexLinearMap.mp hu)).toLinearMap :=
  (Classical.choose_spec (isPseudoholomorphicAt_iff_isComplexLinearMap.mp hu)).2

/-- The continuous-linear manifold derivative witnessing pseudoholomorphicity within a set. -/
theorem IsPseudoholomorphicWithinAt.hasMFDerivWithinAt
    (hu : IsPseudoholomorphicWithinAt j J u s x) :
    HasMFDerivWithinAt I I' u s x
      (Classical.choose (isPseudoholomorphicWithinAt_iff_isComplexLinearMap.mp hu)) :=
  (Classical.choose_spec (isPseudoholomorphicWithinAt_iff_isComplexLinearMap.mp hu)).1

/-- The chosen within-set manifold derivative is complex-linear. -/
theorem IsPseudoholomorphicWithinAt.derivative_isComplexLinear
    (hu : IsPseudoholomorphicWithinAt j J u s x) :
    IsComplexLinearMap (j.almostComplexStructureAt x) (J.almostComplexStructureAt (u x))
      (Classical.choose
        (isPseudoholomorphicWithinAt_iff_isComplexLinearMap.mp hu)).toLinearMap :=
  (Classical.choose_spec (isPseudoholomorphicWithinAt_iff_isComplexLinearMap.mp hu)).2

/-! ### Differentiability and continuity -/

/-- A map pseudoholomorphic at a point is differentiable there. -/
theorem IsPseudoholomorphicAt.mdifferentiableAt (hu : IsPseudoholomorphicAt j J u x) :
    MDifferentiableAt I I' u x := by
  obtain ⟨u', hu', -⟩ := hu
  exact hu'.mdifferentiableAt

/-- A map pseudoholomorphic within a set at a point is differentiable within that set. -/
theorem IsPseudoholomorphicWithinAt.mdifferentiableWithinAt
    (hu : IsPseudoholomorphicWithinAt j J u s x) : MDifferentiableWithinAt I I' u s x := by
  obtain ⟨u', hu', -⟩ := hu
  exact hu'.mdifferentiableWithinAt

/-- A map pseudoholomorphic at a point is continuous there. -/
theorem IsPseudoholomorphicAt.continuousAt (hu : IsPseudoholomorphicAt j J u x) :
    ContinuousAt u x :=
  hu.mdifferentiableAt.continuousAt

/-- A map pseudoholomorphic within a set at a point is continuous within that set. -/
theorem IsPseudoholomorphicWithinAt.continuousWithinAt
    (hu : IsPseudoholomorphicWithinAt j J u s x) : ContinuousWithinAt u s x :=
  hu.mdifferentiableWithinAt.continuousWithinAt

/-- A map pseudoholomorphic on a set is differentiable on it. -/
theorem IsPseudoholomorphicOn.mdifferentiableOn (hu : IsPseudoholomorphicOn j J u s) :
    MDifferentiableOn I I' u s :=
  fun x hx ↦ (hu x hx).mdifferentiableWithinAt

/-- A map pseudoholomorphic on a set is continuous on it. -/
theorem IsPseudoholomorphicOn.continuousOn (hu : IsPseudoholomorphicOn j J u s) :
    ContinuousOn u s :=
  fun x hx ↦ (hu x hx).continuousWithinAt

/-- A pseudoholomorphic map is differentiable. -/
theorem IsPseudoholomorphic.mdifferentiable (hu : IsPseudoholomorphic j J u) :
    MDifferentiable I I' u :=
  fun x ↦ (hu x).mdifferentiableAt

/-- A pseudoholomorphic map is continuous. -/
theorem IsPseudoholomorphic.continuous (hu : IsPseudoholomorphic j J u) : Continuous u :=
  hu.mdifferentiable.continuous

/-! ### The Cauchy--Riemann equation for the canonical derivative -/

/-- The manifold derivative of a map pseudoholomorphic at a point intertwines the two almost
complex structures: this is the nonlinear Cauchy--Riemann equation. -/
theorem IsPseudoholomorphicAt.mfderiv_apply_commute (hu : IsPseudoholomorphicAt j J u x)
    (w : TangentSpace I x) :
    mfderiv I I' u x (j x w) = J (u x) (mfderiv I I' u x w) := by
  obtain ⟨u', hu', hlin⟩ := hu
  rw [hu'.mfderiv]
  exact hlin w

/-- The manifold derivative of a map pseudoholomorphic at a point is complex-linear. -/
theorem IsPseudoholomorphicAt.mfderiv_isComplexLinear (hu : IsPseudoholomorphicAt j J u x) :
    IsComplexLinearMap (j.almostComplexStructureAt x) (J.almostComplexStructureAt (u x))
      (mfderiv I I' u x).toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ContinuousLinearMap.coe_coe]
  exact hu.mfderiv_apply_commute

/-- Pseudoholomorphicity at a point is exactly differentiability together with the
Cauchy--Riemann equation for the canonical manifold derivative. -/
theorem isPseudoholomorphicAt_iff_mfderiv :
    IsPseudoholomorphicAt j J u x ↔
      MDifferentiableAt I I' u x ∧
        ∀ w, mfderiv I I' u x (j x w) = J (u x) (mfderiv I I' u x w) := by
  refine ⟨fun hu ↦ ⟨hu.mdifferentiableAt, hu.mfderiv_apply_commute⟩, fun hu ↦ ?_⟩
  exact isPseudoholomorphicAt_of_hasMFDerivAt hu.1.hasMFDerivAt hu.2

/-- The derivative within a set of a map pseudoholomorphic there intertwines the two almost
complex structures, provided the set has unique manifold derivatives at the point. -/
theorem IsPseudoholomorphicWithinAt.mfderivWithin_apply_commute
    (hu : IsPseudoholomorphicWithinAt j J u s x) (hs : UniqueMDiffWithinAt I s x)
    (w : TangentSpace I x) :
    mfderivWithin I I' u s x (j x w) = J (u x) (mfderivWithin I I' u s x w) := by
  obtain ⟨u', hu', hlin⟩ := hu
  rw [hu'.mfderivWithin hs]
  exact hlin w

/-- The derivative within a set of a map pseudoholomorphic there is complex-linear, provided the
set has unique manifold derivatives at the point. -/
theorem IsPseudoholomorphicWithinAt.mfderivWithin_isComplexLinear
    (hu : IsPseudoholomorphicWithinAt j J u s x) (hs : UniqueMDiffWithinAt I s x) :
    IsComplexLinearMap (j.almostComplexStructureAt x) (J.almostComplexStructureAt (u x))
      (mfderivWithin I I' u s x).toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    ContinuousLinearMap.coe_coe]
  exact hu.mfderivWithin_apply_commute hs

/-! ### Relations between the four predicates -/

/-- A map pseudoholomorphic at a point is pseudoholomorphic within every set there. -/
theorem IsPseudoholomorphicAt.isPseudoholomorphicWithinAt
    (hu : IsPseudoholomorphicAt j J u x) : IsPseudoholomorphicWithinAt j J u s x := by
  obtain ⟨u', hu', hlin⟩ := hu
  exact ⟨u', hu'.hasMFDerivWithinAt, hlin⟩

/-- Pseudoholomorphicity within a set that is a neighbourhood of the point upgrades to
pseudoholomorphicity at the point. -/
theorem IsPseudoholomorphicWithinAt.isPseudoholomorphicAt_of_mem_nhds
    (hu : IsPseudoholomorphicWithinAt j J u s x) (hs : s ∈ nhds x) :
    IsPseudoholomorphicAt j J u x := by
  obtain ⟨u', hu', hlin⟩ := hu
  exact ⟨u', hu'.hasMFDerivAt hs, hlin⟩

/-- Pseudoholomorphicity within a set passes to smaller sets. -/
theorem IsPseudoholomorphicWithinAt.mono (hu : IsPseudoholomorphicWithinAt j J u t x)
    (hst : s ⊆ t) : IsPseudoholomorphicWithinAt j J u s x := by
  obtain ⟨u', hu', hlin⟩ := hu
  exact ⟨u', hu'.mono hst, hlin⟩

/-- A map pseudoholomorphic on a set is pseudoholomorphic within that set at each of its
points. -/
theorem IsPseudoholomorphicOn.isPseudoholomorphicWithinAt (hu : IsPseudoholomorphicOn j J u s)
    (hx : x ∈ s) : IsPseudoholomorphicWithinAt j J u s x :=
  hu x hx

/-- A pseudoholomorphic map is pseudoholomorphic at every point. -/
theorem IsPseudoholomorphic.isPseudoholomorphicAt (hu : IsPseudoholomorphic j J u) (x : M) :
    IsPseudoholomorphicAt j J u x :=
  hu x

/-- Pseudoholomorphicity on a set passes to smaller sets. -/
theorem IsPseudoholomorphicOn.mono (hu : IsPseudoholomorphicOn j J u t) (hst : s ⊆ t) :
    IsPseudoholomorphicOn j J u s :=
  fun x hx ↦ (hu x (hst hx)).mono hst

/-- A pseudoholomorphic map is pseudoholomorphic on every set. -/
theorem IsPseudoholomorphic.isPseudoholomorphicOn (hu : IsPseudoholomorphic j J u) (s : Set M) :
    IsPseudoholomorphicOn j J u s :=
  fun x _ ↦ (hu x).isPseudoholomorphicWithinAt

/-- Pseudoholomorphicity within the whole space is pseudoholomorphicity at the point. -/
@[simp]
theorem isPseudoholomorphicWithinAt_univ :
    IsPseudoholomorphicWithinAt j J u Set.univ x ↔ IsPseudoholomorphicAt j J u x :=
  ⟨fun hu ↦ hu.isPseudoholomorphicAt_of_mem_nhds Filter.univ_mem,
    fun hu ↦ hu.isPseudoholomorphicWithinAt⟩

/-- Pseudoholomorphicity on the whole space is global pseudoholomorphicity. -/
@[simp]
theorem isPseudoholomorphicOn_univ :
    IsPseudoholomorphicOn j J u Set.univ ↔ IsPseudoholomorphic j J u := by
  refine ⟨fun hu x ↦ ?_, fun hu ↦ hu.isPseudoholomorphicOn _⟩
  exact isPseudoholomorphicWithinAt_univ.1 (hu x (Set.mem_univ x))

/-! ### The identity, constants, and composition -/

/-- The identity map is pseudoholomorphic at every point, for every smooth almost complex
structure. -/
@[simp]
theorem isPseudoholomorphicAt_id (j : SmoothAlmostComplexStructure I M) (x : M) :
    IsPseudoholomorphicAt j j id x :=
  isPseudoholomorphicAt_of_hasMFDerivAt (hasMFDerivAt_id x) fun _ ↦ rfl

/-- The identity map is pseudoholomorphic within every set at every point. -/
@[simp]
theorem isPseudoholomorphicWithinAt_id (j : SmoothAlmostComplexStructure I M) (s : Set M)
    (x : M) : IsPseudoholomorphicWithinAt j j id s x :=
  (isPseudoholomorphicAt_id j x).isPseudoholomorphicWithinAt

/-- The identity map is pseudoholomorphic on every set. -/
@[simp]
theorem isPseudoholomorphicOn_id (j : SmoothAlmostComplexStructure I M) (s : Set M) :
    IsPseudoholomorphicOn j j id s :=
  fun x _ ↦ isPseudoholomorphicWithinAt_id j s x

/-- The identity map is pseudoholomorphic. -/
@[simp]
theorem isPseudoholomorphic_id (j : SmoothAlmostComplexStructure I M) :
    IsPseudoholomorphic j j id :=
  isPseudoholomorphicAt_id j

/-- A constant map is pseudoholomorphic at every point, for arbitrary source and target
structures. -/
@[simp]
theorem isPseudoholomorphicAt_const (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (c : M') (x : M) :
    IsPseudoholomorphicAt j J (fun _ ↦ c) x :=
  isPseudoholomorphicAt_of_hasMFDerivAt (hasMFDerivAt_const c x) fun _ ↦ by simp

/-- A constant map is pseudoholomorphic within every set at every point. -/
@[simp]
theorem isPseudoholomorphicWithinAt_const (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (c : M') (s : Set M) (x : M) :
    IsPseudoholomorphicWithinAt j J (fun _ ↦ c) s x :=
  (isPseudoholomorphicAt_const j J c x).isPseudoholomorphicWithinAt

/-- A constant map is pseudoholomorphic on every set. -/
@[simp]
theorem isPseudoholomorphicOn_const (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (c : M') (s : Set M) :
    IsPseudoholomorphicOn j J (fun _ ↦ c) s :=
  fun x _ ↦ isPseudoholomorphicWithinAt_const j J c s x

/-- A constant map is pseudoholomorphic. -/
@[simp]
theorem isPseudoholomorphic_const (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (c : M') :
    IsPseudoholomorphic j J (fun _ ↦ c) :=
  isPseudoholomorphicAt_const j J c

/-- The composition of pseudoholomorphic maps is pseudoholomorphic at a point: the chain rule for
the nonlinear Cauchy--Riemann equation. -/
theorem IsPseudoholomorphicAt.comp (hv : IsPseudoholomorphicAt J K v (u x))
    (hu : IsPseudoholomorphicAt j J u x) : IsPseudoholomorphicAt j K (v ∘ u) x := by
  obtain ⟨u', hu', hulin⟩ := hu
  obtain ⟨v', hv', hvlin⟩ := hv
  refine isPseudoholomorphicAt_of_hasMFDerivAt (hv'.comp x hu') fun w ↦ ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hulin w, hvlin (u' w)]

/-- The composition of pseudoholomorphic maps is pseudoholomorphic within a set at a point. -/
theorem IsPseudoholomorphicWithinAt.comp {r : Set M'}
    (hv : IsPseudoholomorphicWithinAt J K v r (u x))
    (hu : IsPseudoholomorphicWithinAt j J u s x) (hst : Set.MapsTo u s r) :
    IsPseudoholomorphicWithinAt j K (v ∘ u) s x := by
  obtain ⟨u', hu', hulin⟩ := hu
  obtain ⟨v', hv', hvlin⟩ := hv
  refine isPseudoholomorphicWithinAt_of_hasMFDerivWithinAt (hv'.comp x hu' hst) fun w ↦ ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [hulin w, hvlin (u' w)]

/-- The composition of pseudoholomorphic maps is pseudoholomorphic on the source set. -/
theorem IsPseudoholomorphicOn.comp {r : Set M'} (hv : IsPseudoholomorphicOn J K v r)
    (hu : IsPseudoholomorphicOn j J u s) (hst : Set.MapsTo u s r) :
    IsPseudoholomorphicOn j K (v ∘ u) s :=
  fun x hx ↦ (hv (u x) (hst hx)).comp (hu x hx) hst

/-- The composition of pseudoholomorphic maps is pseudoholomorphic. -/
theorem IsPseudoholomorphic.comp (hv : IsPseudoholomorphic J K v)
    (hu : IsPseudoholomorphic j J u) : IsPseudoholomorphic j K (v ∘ u) :=
  fun x ↦ (hv (u x)).comp (hu x)

/-! ### Reversing the structures -/

/-- Reversing both almost complex structures preserves pseudoholomorphicity within a set: a map is
`(j, J)`-holomorphic there exactly when it is `(-j, -J)`-holomorphic. -/
@[simp]
theorem isPseudoholomorphicWithinAt_neg_neg_iff :
    IsPseudoholomorphicWithinAt (-j) (-J) u s x ↔ IsPseudoholomorphicWithinAt j J u s x := by
  rw [isPseudoholomorphicWithinAt_iff_isComplexLinearMap,
    isPseudoholomorphicWithinAt_iff_isComplexLinearMap]
  simp only [SmoothAlmostComplexStructure.neg_almostComplexStructureAt]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ isComplexLinearMap_neg_neg_iff

/-- Reversing both almost complex structures preserves pseudoholomorphicity: a map is
`(j, J)`-holomorphic exactly when it is `(-j, -J)`-holomorphic. -/
@[simp]
theorem isPseudoholomorphicAt_neg_neg_iff :
    IsPseudoholomorphicAt (-j) (-J) u x ↔ IsPseudoholomorphicAt j J u x := by
  rw [isPseudoholomorphicAt_iff_isComplexLinearMap, isPseudoholomorphicAt_iff_isComplexLinearMap]
  simp only [SmoothAlmostComplexStructure.neg_almostComplexStructureAt]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ isComplexLinearMap_neg_neg_iff

/-- Reversing both almost complex structures preserves pseudoholomorphicity on a set. -/
@[simp]
theorem isPseudoholomorphicOn_neg_neg_iff :
    IsPseudoholomorphicOn (-j) (-J) u s ↔ IsPseudoholomorphicOn j J u s :=
  forall₂_congr fun _ _ ↦ isPseudoholomorphicWithinAt_neg_neg_iff

/-- Reversing both almost complex structures preserves global pseudoholomorphicity. -/
@[simp]
theorem isPseudoholomorphic_neg_neg_iff :
    IsPseudoholomorphic (-j) (-J) u ↔ IsPseudoholomorphic j J u :=
  forall_congr' fun _ ↦ isPseudoholomorphicAt_neg_neg_iff

/-! ### Curves from the standard complex line -/

section StandardLine

/-- A curve from the standard complex line -- that is, `ℝ × ℝ` with the smooth almost complex
structure `SmoothAlmostComplexStructure.product ℝ` -- into an almost complex manifold is
pseudoholomorphic at a point exactly when it has a manifold derivative there satisfying the
single coordinate Cauchy--Riemann equation `∂_t w = J(w) ∂_s w`. This is the classical form of
the equation for a `J`-holomorphic curve. -/
theorem isPseudoholomorphicAt_stdComplexLine_iff (J : SmoothAlmostComplexStructure I' M')
    (w : ℝ × ℝ → M') (z : ℝ × ℝ) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.product ℝ) J w z ↔
      ∃ w' : TangentSpace (modelWithCornersSelf ℝ (ℝ × ℝ)) z →L[ℝ] TangentSpace I' (w z),
        HasMFDerivAt (modelWithCornersSelf ℝ (ℝ × ℝ)) I' w z w' ∧
          w' stdComplexLineImag = J (w z) (w' stdComplexLineReal) := by
  rw [isPseudoholomorphicAt_iff_isComplexLinearMap]
  refine exists_congr fun w' ↦ and_congr_right fun _ ↦ ?_
  rw [SmoothAlmostComplexStructure.product_almostComplexStructureAt]
  refine Iff.trans (isComplexLinearMap_stdComplexLine_iff _) ?_
  simp only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  exact Iff.rfl

/-- The manifold derivative of a `J`-holomorphic curve from the standard complex line sends the
imaginary coordinate vector to `J` applied to the image of the real coordinate vector. -/
theorem IsPseudoholomorphicAt.mfderiv_stdComplexLineImag {J : SmoothAlmostComplexStructure I' M'}
    {w : ℝ × ℝ → M'} {z : ℝ × ℝ}
    (hw : IsPseudoholomorphicAt (SmoothAlmostComplexStructure.product ℝ) J w z) :
    mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' w z stdComplexLineImag =
      J (w z) (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' w z stdComplexLineReal) := by
  have hz : SmoothAlmostComplexStructure.product ℝ z stdComplexLineReal = stdComplexLineImag := by
    simp only [SmoothAlmostComplexStructure.product_apply, stdComplexLineReal_fst,
      stdComplexLineReal_snd, neg_zero, stdComplexLineImag]
    rfl
  simpa only [hz] using hw.mfderiv_apply_commute stdComplexLineReal

end StandardLine

/-! ### Comparison with the normed-space predicates -/

section ModelSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- On model vector spaces, pseudoholomorphicity at a point is the existing varying-structure
predicate for maps between normed spaces, applied to the pointwise almost complex structures on
the tangent spaces. -/
theorem isPseudoholomorphicAt_iff_isJHolomorphicAt
    (j : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V)
    (J : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ W) W) (u : V → W) (x : V) :
    IsPseudoholomorphicAt j J u x ↔
      IsJHolomorphicAt j.almostComplexStructureAt J.almostComplexStructureAt u x := by
  refine Iff.trans ?_ (isJHolomorphicAt_iff _ _ _ _).symm
  rw [isPseudoholomorphicAt_iff_isComplexLinearMap]
  exact exists_congr fun _ ↦ and_congr_left' hasMFDerivAt_iff_hasFDerivAt

/-- On model vector spaces, pseudoholomorphicity within a set at a point is the existing
varying-structure predicate for maps between normed spaces. -/
theorem isPseudoholomorphicWithinAt_iff_isJHolomorphicWithinAt
    (j : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V)
    (J : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ W) W) (u : V → W) (s : Set V)
    (x : V) :
    IsPseudoholomorphicWithinAt j J u s x ↔
      IsJHolomorphicWithinAt j.almostComplexStructureAt J.almostComplexStructureAt u s x := by
  refine Iff.trans ?_ (isJHolomorphicWithinAt_iff _ _ _ _ _).symm
  rw [isPseudoholomorphicWithinAt_iff_isComplexLinearMap]
  exact exists_congr fun _ ↦ and_congr_left' hasMFDerivWithinAt_iff_hasFDerivWithinAt

/-- On model vector spaces, pseudoholomorphicity on a set is the existing varying-structure
predicate for maps between normed spaces. -/
theorem isPseudoholomorphicOn_iff_isJHolomorphicOn
    (j : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V)
    (J : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ W) W) (u : V → W) (s : Set V) :
    IsPseudoholomorphicOn j J u s ↔
      IsJHolomorphicOn j.almostComplexStructureAt J.almostComplexStructureAt u s := by
  refine Iff.trans ?_ (isJHolomorphicOn_iff _ _ _ _).symm
  exact forall₂_congr fun x _ ↦ isPseudoholomorphicWithinAt_iff_isJHolomorphicWithinAt j J u s x

/-- On model vector spaces, pseudoholomorphicity is the existing varying-structure predicate for
maps between normed spaces. -/
theorem isPseudoholomorphic_iff_isJHolomorphic
    (j : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V)
    (J : SmoothAlmostComplexStructure (modelWithCornersSelf ℝ W) W) (u : V → W) :
    IsPseudoholomorphic j J u ↔
      IsJHolomorphic j.almostComplexStructureAt J.almostComplexStructureAt u := by
  refine Iff.trans ?_ (isJHolomorphic_iff _ _ _).symm
  exact forall_congr' fun x ↦ isPseudoholomorphicAt_iff_isJHolomorphicAt j J u x

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

/-- For the constant smooth structures of two pointwise almost complex structures on model vector
spaces, pseudoholomorphicity at a point is the flat, constant-structure predicate. This is the
check that the manifold-level Cauchy--Riemann equation restricts to the linear one. -/
@[simp]
theorem isPseudoholomorphicAt_constSmooth_iff (Jv : AlmostComplexStructure V)
    (Jw : AlmostComplexStructure W) (u : V → W) (x : V) :
    IsPseudoholomorphicAt Jv.constSmooth Jw.constSmooth u x ↔
      IsConstStructureJHolomorphicAt Jv Jw u x := by
  rw [isPseudoholomorphicAt_iff_isComplexLinearMap]
  refine Iff.trans ?_ (isConstStructureJHolomorphicAt_iff Jv Jw u x).symm
  simp only [AlmostComplexStructure.constSmooth_almostComplexStructureAt]
  exact exists_congr fun _ ↦ and_congr_left' hasMFDerivAt_iff_hasFDerivAt

/-- For the constant smooth structures of two pointwise almost complex structures on model vector
spaces, pseudoholomorphicity within a set at a point is the flat, constant-structure predicate. -/
@[simp]
theorem isPseudoholomorphicWithinAt_constSmooth_iff (Jv : AlmostComplexStructure V)
    (Jw : AlmostComplexStructure W) (u : V → W) (s : Set V) (x : V) :
    IsPseudoholomorphicWithinAt Jv.constSmooth Jw.constSmooth u s x ↔
      IsConstStructureJHolomorphicWithinAt Jv Jw u s x := by
  rw [isPseudoholomorphicWithinAt_iff_isComplexLinearMap]
  refine Iff.trans ?_ (isConstStructureJHolomorphicWithinAt_iff Jv Jw u s x).symm
  simp only [AlmostComplexStructure.constSmooth_almostComplexStructureAt]
  exact exists_congr fun _ ↦ and_congr_left' hasMFDerivWithinAt_iff_hasFDerivWithinAt

/-- For the constant smooth structures of two pointwise almost complex structures on model vector
spaces, pseudoholomorphicity on a set is the flat, constant-structure predicate. -/
@[simp]
theorem isPseudoholomorphicOn_constSmooth_iff (Jv : AlmostComplexStructure V)
    (Jw : AlmostComplexStructure W) (u : V → W) (s : Set V) :
    IsPseudoholomorphicOn Jv.constSmooth Jw.constSmooth u s ↔
      IsConstStructureJHolomorphicOn Jv Jw u s := by
  refine Iff.trans ?_ (isConstStructureJHolomorphicOn_iff Jv Jw u s).symm
  refine forall₂_congr fun x _ ↦
    Iff.trans (isPseudoholomorphicWithinAt_constSmooth_iff Jv Jw u s x) ?_
  exact isConstStructureJHolomorphicWithinAt_iff Jv Jw u s x

/-- For the constant smooth structures of two pointwise almost complex structures on model vector
spaces, global pseudoholomorphicity is the flat, constant-structure predicate. -/
@[simp]
theorem isPseudoholomorphic_constSmooth_iff (Jv : AlmostComplexStructure V)
    (Jw : AlmostComplexStructure W) (u : V → W) :
    IsPseudoholomorphic Jv.constSmooth Jw.constSmooth u ↔
      IsConstStructureJHolomorphic Jv Jw u := by
  refine Iff.trans ?_ (isConstStructureJHolomorphic_iff Jv Jw u).symm
  refine forall_congr' fun x ↦ Iff.trans (isPseudoholomorphicAt_constSmooth_iff Jv Jw u x) ?_
  exact isConstStructureJHolomorphicAt_iff Jv Jw u x

end ModelSpace

end TauCeti

end
