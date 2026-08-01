/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Constant-structure `J`-holomorphic maps

This file adds the first map-level definition for the analytic Heegaard Floer roadmap:
a map between real normed spaces, each carrying a single *fixed* almost complex structure,
is holomorphic at a point when it has a Frechet derivative there and that derivative commutes
with the two structures.

## Scope: the constant-structure (flat) model only

The predicates here are named `IsConstStructureJHolomorphic*` on purpose. They fix one almost
complex structure `J` on the source `V` and one `J'` on the target `W`, both constant across the
whole space, and ask that `df ∘ J = J' ∘ df`. This is ordinary several-variable holomorphy read
in linear complex coordinates -- the integrable, flat model -- not a genuine `J`-holomorphic
curve.

A genuine `J`-holomorphic curve `u : Σ → M` into an almost complex manifold satisfies
`du ∘ j = J(u(z)) ∘ du`, with the target structure `J` *varying* along the map, evaluated at the
image point `u(z)`. The constant-structure predicate cannot express that: its target structure
`J'` does not depend on the point. This whole `IsConstStructureJHolomorphic*` family, and the
downstream Neg/Transport/Congruence/Prod/Line/energy calculus built on it, therefore lives
entirely in the flat model.

The `ConstStructure` stem is a deliberate reservation. The plain name `IsJHolomorphic` is left
free for the eventual varying-structure curve definition (roadmap `HeegaardFloer/README.md`,
Lane F2.1's `J`-holomorphic maps and the manifold/bundle layer built on them), so that layer
does not silently collide with -- or get mistaken for -- the flat model recorded here. Those
later versions should still use this file as their local model on coordinate charts and tangent
fibers, matching the same Cauchy--Riemann convention. This settles the design choice raised in
`https://github.com/TauCetiProject/TauCeti/issues/797`, Task 1: rename (rather than
point-parametrize `J'`), and document the scope.

## Main declarations

* `IsConstStructureJHolomorphicAt`: a map has a complex-linear Frechet derivative at a point.
* `IsConstStructureJHolomorphicWithinAt`: a map has a complex-linear Frechet derivative within a
set.
* `IsConstStructureJHolomorphicOn` and `IsConstStructureJHolomorphic`: setwise and global versions.

It also records the immediate differentiability and continuity consequences of these predicates.

The Cauchy--Riemann equation `df ∘ J = J' ∘ df` is real-linear in `df`, so a continuous
real-linear map is holomorphic in this sense exactly when it is complex-linear, and such maps are
closed under pointwise sums, differences, and real scalar multiples:

* `isConstStructureJHolomorphicAt_continuousLinearMap_iff` and
  `isConstStructureJHolomorphic_continuousLinearMap_iff`: a continuous real-linear map is
  `IsConstStructureJHolomorphic` iff it is complex-linear.
* `IsConstStructureJHolomorphicAt.add`, `IsConstStructureJHolomorphicAt.neg`,
`IsConstStructureJHolomorphicAt.sub`,
  `IsConstStructureJHolomorphicAt.const_smul` and their within-set, setwise, and global analogues.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the Cauchy--Riemann equation is `df ∘ J = J' ∘ df`.
-/

public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section JHolomorphic

/-- A map is constant-structure `J`-holomorphic at a point if its Frechet derivative exists there
and
intertwines the source and target almost complex structures. -/
def IsConstStructureJHolomorphicAt (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is constant-structure `J`-holomorphic within a set at a point if its Frechet derivative
within the
set exists there and intertwines the source and target almost complex structures. -/
def IsConstStructureJHolomorphicWithinAt (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x : V) : Prop :=
  ∃ f' : V →L[ℝ] W, HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap

/-- A map is constant-structure `J`-holomorphic on a set if it is constant-structure `J`-holomorphic
within that set at every
point of the set. -/
def IsConstStructureJHolomorphicOn (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) (s : Set V) : Prop :=
  ∀ x ∈ s, IsConstStructureJHolomorphicWithinAt J J' f s x

/-- A globally constant-structure `J`-holomorphic map is constant-structure `J`-holomorphic at every
point. -/
def IsConstStructureJHolomorphic (J : AlmostComplexStructure V) (J' : AlmostComplexStructure W)
    (f : V → W) : Prop :=
  ∀ x, IsConstStructureJHolomorphicAt J J' f x

/-- Restate pointwise constant-structure `J`-holomorphicity as existence of a complex-linear Frechet
derivative. -/
lemma isConstStructureJHolomorphicAt_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (x : V) :
    IsConstStructureJHolomorphicAt J J' f x ↔
      ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate within-set constant-structure `J`-holomorphicity as existence of a complex-linear
Frechet
derivative within the set. -/
lemma isConstStructureJHolomorphicWithinAt_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate setwise constant-structure `J`-holomorphicity as the within-set derivative condition at
each
point of the set. -/
lemma isConstStructureJHolomorphicOn_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) (s : Set V) :
    IsConstStructureJHolomorphicOn J J' f s ↔
      ∀ x ∈ s, ∃ f' : V →L[ℝ] W,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Restate global constant-structure `J`-holomorphicity as the pointwise derivative condition at
every point. -/
lemma isConstStructureJHolomorphic_iff (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) :
    IsConstStructureJHolomorphic J J' f ↔
      ∀ x, ∃ f' : V →L[ℝ] W, HasFDerivAt f f' x ∧
        IsComplexLinearMap J J' f'.toLinearMap :=
  Iff.rfl

/-- Build pointwise constant-structure `J`-holomorphicity from a complex-linear Frechet
derivative. -/
lemma isConstStructureJHolomorphicAt_of_hasFDerivAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V} {f' : V →L[ℝ] W}
    (hf' : HasFDerivAt f f' x) (hlin : IsComplexLinearMap J J' f'.toLinearMap) :
    IsConstStructureJHolomorphicAt J J' f x :=
  (isConstStructureJHolomorphicAt_iff J J' f x).mpr ⟨f', hf', hlin⟩

/-- Build within-set constant-structure `J`-holomorphicity from a complex-linear Frechet
derivative within the set. -/
lemma isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    {f' : V →L[ℝ] W} (hf' : HasFDerivWithinAt f f' s x)
    (hlin : IsComplexLinearMap J J' f'.toLinearMap) :
    IsConstStructureJHolomorphicWithinAt J J' f s x :=
  (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mpr ⟨f', hf', hlin⟩

/-- Extract the within-set predicate at a point of a setwise constant-structure
`J`-holomorphic map. -/
lemma IsConstStructureJHolomorphicOn.isConstStructureJHolomorphicWithinAt
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {f : V → W}
    {s : Set V} (hf : IsConstStructureJHolomorphicOn J J' f s) {x : V} (hx : x ∈ s) :
    IsConstStructureJHolomorphicWithinAt J J' f s x :=
  (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mpr
    ((isConstStructureJHolomorphicOn_iff J J' f s).mp hf x hx)

/-- Build setwise constant-structure `J`-holomorphicity from its pointwise-within-set form. -/
lemma isConstStructureJHolomorphicOn_of_forall {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V}
    (hf : ∀ x ∈ s, IsConstStructureJHolomorphicWithinAt J J' f s x) :
    IsConstStructureJHolomorphicOn J J' f s :=
  (isConstStructureJHolomorphicOn_iff J J' f s).mpr fun x hx =>
    (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp (hf x hx)

/-- Extract pointwise constant-structure `J`-holomorphicity from a global one. -/
lemma IsConstStructureJHolomorphic.isConstStructureJHolomorphicAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) (x : V) :
    IsConstStructureJHolomorphicAt J J' f x :=
  (isConstStructureJHolomorphicAt_iff J J' f x).mpr
    ((isConstStructureJHolomorphic_iff J J' f).mp hf x)

/-- Build global constant-structure `J`-holomorphicity from its pointwise form. -/
lemma isConstStructureJHolomorphic_of_forall {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : ∀ x, IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphic J J' f :=
  (isConstStructureJHolomorphic_iff J J' f).mpr fun x =>
    (isConstStructureJHolomorphicAt_iff J J' f x).mp (hf x)

/-- On the whole space, setwise constant-structure `J`-holomorphicity is the same as global
constant-structure `J`-holomorphicity. -/
@[simp]
lemma isConstStructureJHolomorphicOn_univ (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (f : V → W) :
    IsConstStructureJHolomorphicOn J J' f Set.univ ↔ IsConstStructureJHolomorphic J J' f := by
  simp [IsConstStructureJHolomorphicOn, IsConstStructureJHolomorphicWithinAt,
    IsConstStructureJHolomorphic, IsConstStructureJHolomorphicAt, hasFDerivWithinAt_univ]

/-- The continuous-linear derivative witnessing constant-structure `J`-holomorphicity at a point. -/
lemma IsConstStructureJHolomorphicAt.hasFDerivAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    HasFDerivAt f (Classical.choose ((isConstStructureJHolomorphicAt_iff J J' f x).mp hf)) x :=
  (Classical.choose_spec ((isConstStructureJHolomorphicAt_iff J J' f x).mp hf)).1

/-- The chosen derivative at a constant-structure `J`-holomorphic point is complex-linear. -/
lemma IsConstStructureJHolomorphicAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J'
      (Classical.choose ((isConstStructureJHolomorphicAt_iff J J' f x).mp hf)).toLinearMap :=
  (Classical.choose_spec ((isConstStructureJHolomorphicAt_iff J J' f x).mp hf)).2

/-- A constant-structure `J`-holomorphic map is differentiable at the point. -/
lemma IsConstStructureJHolomorphicAt.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    DifferentiableAt ℝ f x :=
  hf.hasFDerivAt.differentiableAt

/-- A pointwise constant-structure `J`-holomorphic map is continuous at the point. -/
lemma IsConstStructureJHolomorphicAt.continuousAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt

/-- A pointwise constant-structure `J`-holomorphic map is continuous within any source set at the
point. -/
lemma IsConstStructureJHolomorphicAt.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    ContinuousWithinAt f s x :=
  hf.continuousAt.continuousWithinAt

/-- The Frechet derivative of a constant-structure `J`-holomorphic map is complex-linear. -/
lemma IsConstStructureJHolomorphicAt.fderiv_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsComplexLinearMap J J' (fderiv ℝ f x).toLinearMap := by
  simpa [hf.hasFDerivAt.fderiv] using hf.derivative_isComplexLinear

/-- The Frechet derivative of a constant-structure `J`-holomorphic map commutes with the almost
complex
structures pointwise. -/
lemma IsConstStructureJHolomorphicAt.fderiv_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {x v : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    fderiv ℝ f x (J v) = J' (fderiv ℝ f x v) :=
  (isComplexLinearMap_iff_apply J J' (fderiv ℝ f x).toLinearMap).mp
    hf.fderiv_isComplexLinear v

/-- A pointwise constant-structure `J`-holomorphic map is constant-structure `J`-holomorphic within
any set. -/
lemma IsConstStructureJHolomorphicAt.isConstStructureJHolomorphicWithinAt
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphicWithinAt J J' f s x :=
  ⟨_, hf.hasFDerivAt.hasFDerivWithinAt, hf.derivative_isComplexLinear⟩

/-- The continuous-linear derivative witnessing constant-structure `J`-holomorphicity within
a set. -/
lemma IsConstStructureJHolomorphicWithinAt.hasFDerivWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    HasFDerivWithinAt f
      (Classical.choose ((isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf)) s x :=
  (Classical.choose_spec ((isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf)).1

/-- The chosen within-set derivative is complex-linear. -/
lemma IsConstStructureJHolomorphicWithinAt.derivative_isComplexLinear {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    IsComplexLinearMap J J'
      (Classical.choose
        ((isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf)).toLinearMap :=
  (Classical.choose_spec ((isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf)).2

/-- A map that is constant-structure `J`-holomorphic within a set is differentiable within
that set. -/
lemma IsConstStructureJHolomorphicWithinAt.differentiableWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    DifferentiableWithinAt ℝ f s x :=
  hf.hasFDerivWithinAt.differentiableWithinAt

/-- A map that is constant-structure `J`-holomorphic within a set is continuous within that set at
the point. -/
lemma IsConstStructureJHolomorphicWithinAt.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    ContinuousWithinAt f s x :=
  hf.hasFDerivWithinAt.continuousWithinAt

/-- The within-set Frechet derivative is complex-linear when the set has unique derivatives. -/
lemma IsConstStructureJHolomorphicWithinAt.fderivWithin_isComplexLinear
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    IsComplexLinearMap J J' (fderivWithin ℝ f s x).toLinearMap := by
  simpa [hf.hasFDerivWithinAt.fderivWithin hs] using hf.derivative_isComplexLinear

/-- The within-set Frechet derivative commutes with the almost complex structures pointwise. -/
lemma IsConstStructureJHolomorphicWithinAt.fderivWithin_apply_commute {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x v : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x (J v) = J' (fderivWithin ℝ f s x v) :=
  (isComplexLinearMap_iff_apply J J' (fderivWithin ℝ f s x).toLinearMap).mp
    (hf.fderivWithin_isComplexLinear hs) v

/-- A within-set constant-structure `J`-holomorphic map is pointwise constant-structure
`J`-holomorphic when the set is a
neighborhood of the point. -/
lemma IsConstStructureJHolomorphicWithinAt.isConstStructureJHolomorphicAt_of_mem_nhds
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    IsConstStructureJHolomorphicAt J J' f x :=
  ⟨_, (hasFDerivWithinAt_of_mem_nhds hs).mp hf.hasFDerivWithinAt,
    hf.derivative_isComplexLinear⟩

/-- A map that is constant-structure `J`-holomorphic within a neighborhood of the point is
continuous at the
point. -/
lemma IsConstStructureJHolomorphicWithinAt.continuousAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    ContinuousAt f x :=
  hf.continuousWithinAt.continuousAt hs

/-- A map that is constant-structure `J`-holomorphic within a neighborhood of the point is
differentiable at the
point. -/
lemma IsConstStructureJHolomorphicWithinAt.differentiableAt_of_mem_nhds
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    DifferentiableAt ℝ f x :=
  (hf.isConstStructureJHolomorphicAt_of_mem_nhds hs).differentiableAt

/-- A map that is constant-structure `J`-holomorphic within a set is continuous within every smaller
source set at
the point. -/
lemma IsConstStructureJHolomorphicWithinAt.continuousWithinAt_mono {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s t : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hts : t ⊆ s) :
    ContinuousWithinAt f t x :=
  hf.continuousWithinAt.mono hts

/-- A constant map is constant-structure `J`-holomorphic at every point. -/
@[simp]
lemma isConstStructureJHolomorphicAt_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (c : W) (x : V) : IsConstStructureJHolomorphicAt J J' (fun _ : V => c) x :=
  ⟨0, hasFDerivAt_const c x, by simp⟩

/-- The identity map is constant-structure `J`-holomorphic for any fixed almost complex structure
`J`. -/
@[simp]
lemma isConstStructureJHolomorphicAt_id (J : AlmostComplexStructure V) (x : V) :
    IsConstStructureJHolomorphicAt J J id x :=
  ⟨ContinuousLinearMap.id ℝ V, hasFDerivAt_id x, by simp⟩

/-- Eta-expanded form of `isConstStructureJHolomorphicAt_id`. -/
@[simp]
lemma isConstStructureJHolomorphicAt_id' (J : AlmostComplexStructure V) (x : V) :
    IsConstStructureJHolomorphicAt J J (fun y : V => y) x :=
  isConstStructureJHolomorphicAt_id J x

/-- Chain rule for pointwise constant-structure `J`-holomorphic maps. -/
lemma IsConstStructureJHolomorphicAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X} {f : V → W} {g : W → X} {x : V}
    (hg : IsConstStructureJHolomorphicAt J' J'' g (f x))
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphicAt J J'' (g ∘ f) x := by
  refine ⟨_, hg.hasFDerivAt.comp x hf.hasFDerivAt, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- A constant map is constant-structure `J`-holomorphic within every set at every point. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (c : W) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J J' (fun _ : V => c) s x :=
  (isConstStructureJHolomorphicAt_const J J' c x).isConstStructureJHolomorphicWithinAt

/-- The identity map is constant-structure `J`-holomorphic within every set at every point. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_id (J : AlmostComplexStructure V) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J J id s x :=
  (isConstStructureJHolomorphicAt_id J x).isConstStructureJHolomorphicWithinAt

/-- Eta-expanded form of `isConstStructureJHolomorphicWithinAt_id`. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_id' (J : AlmostComplexStructure V) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J J (fun y : V => y) s x :=
  isConstStructureJHolomorphicWithinAt_id J s x

/-- A constant map is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W)
    (c : W) (s : Set V) : IsConstStructureJHolomorphicOn J J' (fun _ : V => c) s :=
  fun x _ => isConstStructureJHolomorphicWithinAt_const J J' c s x

/-- The identity map is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_id (J : AlmostComplexStructure V) (s : Set V) :
    IsConstStructureJHolomorphicOn J J id s :=
  fun x _ => isConstStructureJHolomorphicWithinAt_id J s x

/-- Eta-expanded form of `isConstStructureJHolomorphicOn_id`. -/
@[simp]
lemma isConstStructureJHolomorphicOn_id' (J : AlmostComplexStructure V) (s : Set V) :
    IsConstStructureJHolomorphicOn J J (fun y : V => y) s :=
  isConstStructureJHolomorphicOn_id J s

/-- Chain rule for within-set constant-structure `J`-holomorphic maps. -/
lemma IsConstStructureJHolomorphicWithinAt.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W} {x : V}
    (hg : IsConstStructureJHolomorphicWithinAt J' J'' g t (f x))
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hst : Set.MapsTo f s t) :
    IsConstStructureJHolomorphicWithinAt J J'' (g ∘ f) s x := by
  refine ⟨_, hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt hst, ?_⟩
  exact IsComplexLinearMap.comp hg.derivative_isComplexLinear hf.derivative_isComplexLinear

/-- Chain rule for setwise constant-structure `J`-holomorphic maps. -/
lemma IsConstStructureJHolomorphicOn.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X}
    {f : V → W} {g : W → X} {s : Set V} {t : Set W}
    (hg : IsConstStructureJHolomorphicOn J' J'' g t) (hf : IsConstStructureJHolomorphicOn J J' f s)
    (hst : Set.MapsTo f s t) :
    IsConstStructureJHolomorphicOn J J'' (g ∘ f) s :=
  fun x hx => (hg (f x) (hst hx)).comp (hf x hx) hst

/-- Restrict the domain set of a setwise constant-structure `J`-holomorphic map. -/
lemma IsConstStructureJHolomorphicOn.mono
    {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
    {f : V → W} {s t : Set V} (hf : IsConstStructureJHolomorphicOn J J' f t) (hst : s ⊆ t) :
    IsConstStructureJHolomorphicOn J J' f s :=
  fun x hx =>
    let hfx := hf x (hst hx)
    ⟨_, hfx.hasFDerivWithinAt.mono hst, hfx.derivative_isComplexLinear⟩

/-- A map that is constant-structure `J`-holomorphic on a set is differentiable on that set. -/
lemma IsConstStructureJHolomorphicOn.differentiableOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) :
    DifferentiableOn ℝ f s :=
  fun x hx => (hf x hx).differentiableWithinAt

/-- A map that is constant-structure `J`-holomorphic on a set is differentiable within that set at
each of its
points. -/
lemma IsConstStructureJHolomorphicOn.differentiableWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hx : x ∈ s) :
    DifferentiableWithinAt ℝ f s x :=
  (hf x hx).differentiableWithinAt

/-- A map that is constant-structure `J`-holomorphic on a set is continuous on that set. -/
lemma IsConstStructureJHolomorphicOn.continuousOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousWithinAt

/-- A map that is constant-structure `J`-holomorphic on a set is continuous within that set at each
of its points. -/
lemma IsConstStructureJHolomorphicOn.continuousWithinAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  (hf x hx).continuousWithinAt

/-- A map that is constant-structure `J`-holomorphic on a neighborhood of a point is differentiable
at that point. -/
lemma IsConstStructureJHolomorphicOn.differentiableAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hs : s ∈ nhds x) :
    DifferentiableAt ℝ f x :=
  (hf x (mem_of_mem_nhds hs)).differentiableAt_of_mem_nhds hs

/-- A map that is constant-structure `J`-holomorphic on a neighborhood of a point is continuous at
that point. -/
lemma IsConstStructureJHolomorphicOn.continuousAt_of_mem_nhds {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hs : s ∈ nhds x) :
    ContinuousAt f x :=
  (hf x (mem_of_mem_nhds hs)).continuousAt_of_mem_nhds hs

/-- A map that is constant-structure `J`-holomorphic on an open set is pointwise differentiable at
each point of
that set. -/
lemma IsConstStructureJHolomorphicOn.differentiableAt_of_isOpen {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hs : IsOpen s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x :=
  hf.differentiableAt_of_mem_nhds (hs.mem_nhds hx)

/-- A map that is constant-structure `J`-holomorphic on an open set is continuous at each point of
that set. -/
lemma IsConstStructureJHolomorphicOn.continuousAt_of_isOpen {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hs : IsOpen s) (hx : x ∈ s) :
    ContinuousAt f x :=
  hf.continuousAt_of_mem_nhds (hs.mem_nhds hx)

/-- A globally constant-structure `J`-holomorphic map is constant-structure `J`-holomorphic on every
set. -/
lemma IsConstStructureJHolomorphic.isConstStructureJHolomorphicOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstStructureJHolomorphic J J' f) (s : Set V) :
    IsConstStructureJHolomorphicOn J J' f s :=
  fun x _ => (hf x).isConstStructureJHolomorphicWithinAt

/-- A globally constant-structure `J`-holomorphic map is differentiable. -/
lemma IsConstStructureJHolomorphic.differentiable {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) :
    Differentiable ℝ f :=
  fun x => (hf x).differentiableAt

/-- A globally constant-structure `J`-holomorphic map is differentiable at every point. -/
lemma IsConstStructureJHolomorphic.differentiableAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) (x : V) :
    DifferentiableAt ℝ f x :=
  (hf x).differentiableAt

/-- A globally constant-structure `J`-holomorphic map is continuous. -/
lemma IsConstStructureJHolomorphic.continuous {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt

/-- A globally constant-structure `J`-holomorphic map is continuous at every point. -/
lemma IsConstStructureJHolomorphic.continuousAt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) (x : V) :
    ContinuousAt f x :=
  (hf x).continuousAt

/-- A globally constant-structure `J`-holomorphic map is differentiable on every source set. -/
lemma IsConstStructureJHolomorphic.differentiableOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstStructureJHolomorphic J J' f) (s : Set V) :
    DifferentiableOn ℝ f s :=
  (hf.isConstStructureJHolomorphicOn s).differentiableOn

/-- A globally constant-structure `J`-holomorphic map is continuous on every source set. -/
lemma IsConstStructureJHolomorphic.continuousOn {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {f : V → W}
    (hf : IsConstStructureJHolomorphic J J' f) (s : Set V) :
    ContinuousOn f s :=
  (hf.isConstStructureJHolomorphicOn s).continuousOn

/-- A constant map is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_const (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (c : W) : IsConstStructureJHolomorphic J J' (fun _ : V => c) :=
  fun x => isConstStructureJHolomorphicAt_const J J' c x

/-- The identity map is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_id (J : AlmostComplexStructure V) :
    IsConstStructureJHolomorphic J J id :=
  fun x => isConstStructureJHolomorphicAt_id J x

/-- Eta-expanded form of `isConstStructureJHolomorphic_id`. -/
@[simp]
lemma isConstStructureJHolomorphic_id' (J : AlmostComplexStructure V) :
    IsConstStructureJHolomorphic J J (fun y : V => y) :=
  isConstStructureJHolomorphic_id J

/-- Chain rule for global constant-structure `J`-holomorphic maps. -/
lemma IsConstStructureJHolomorphic.comp {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {J'' : AlmostComplexStructure X} {f : V → W} {g : W → X}
    (hg : IsConstStructureJHolomorphic J' J'' g) (hf : IsConstStructureJHolomorphic J J' f) :
    IsConstStructureJHolomorphic J J'' (g ∘ f) :=
  fun x => (hg (f x)).comp (hf x)

end JHolomorphic

section LinearStructure

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}

/-- A continuous real-linear map is constant-structure `J`-holomorphic at a point iff it is
complex-linear: its
derivative is the map itself, so the Cauchy--Riemann condition becomes complex-linearity. -/
lemma isConstStructureJHolomorphicAt_continuousLinearMap_iff (F : V →L[ℝ] W) (x : V) :
    IsConstStructureJHolomorphicAt J J' (⇑F) x ↔ IsComplexLinearMap J J' F.toLinearMap := by
  refine ⟨fun hF => ?_, fun h => ⟨F, F.hasFDerivAt, h⟩⟩
  obtain ⟨f', hf', hcl⟩ := hF
  rwa [hf'.unique F.hasFDerivAt] at hcl

/-- A continuous real-linear map is globally constant-structure `J`-holomorphic iff it is
complex-linear. -/
lemma isConstStructureJHolomorphic_continuousLinearMap_iff (F : V →L[ℝ] W) :
    IsConstStructureJHolomorphic J J' (⇑F) ↔ IsComplexLinearMap J J' F.toLinearMap :=
  ⟨fun h => (isConstStructureJHolomorphicAt_continuousLinearMap_iff F 0).mp (h 0),
    fun h x => (isConstStructureJHolomorphicAt_continuousLinearMap_iff F x).mpr h⟩

/-- The pointwise sum of two constant-structure `J`-holomorphic maps is constant-structure
`J`-holomorphic. -/
lemma IsConstStructureJHolomorphicAt.add {f g : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) (hg : IsConstStructureJHolomorphicAt J J' g x) :
    IsConstStructureJHolomorphicAt J J' (f + g) x := by
  refine ⟨_, hf.hasFDerivAt.add hg.hasFDerivAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_add]
  exact hf.derivative_isComplexLinear.add hg.derivative_isComplexLinear

/-- The pointwise negation of a constant-structure `J`-holomorphic map is constant-structure
`J`-holomorphic. -/
lemma IsConstStructureJHolomorphicAt.neg {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphicAt J J' (-f) x := by
  refine ⟨_, hf.hasFDerivAt.neg, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_neg]
  exact hf.derivative_isComplexLinear.neg

/-- The pointwise difference of two constant-structure `J`-holomorphic maps is constant-structure
`J`-holomorphic. -/
lemma IsConstStructureJHolomorphicAt.sub {f g : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) (hg : IsConstStructureJHolomorphicAt J J' g x) :
    IsConstStructureJHolomorphicAt J J' (f - g) x := by
  refine ⟨_, hf.hasFDerivAt.sub hg.hasFDerivAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_sub]
  exact hf.derivative_isComplexLinear.sub hg.derivative_isComplexLinear

/-- A real scalar multiple of a constant-structure `J`-holomorphic map is constant-structure
`J`-holomorphic. -/
lemma IsConstStructureJHolomorphicAt.const_smul {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x)
    (c : ℝ) : IsConstStructureJHolomorphicAt J J' (c • f) x := by
  refine ⟨_, hf.hasFDerivAt.const_smul c, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_smul]
  exact hf.derivative_isComplexLinear.smul c

/-- The pointwise sum of two maps constant-structure `J`-holomorphic within a set is
constant-structure `J`-holomorphic within it. -/
lemma IsConstStructureJHolomorphicWithinAt.add {f g : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hg : IsConstStructureJHolomorphicWithinAt J J' g s x) :
    IsConstStructureJHolomorphicWithinAt J J' (f + g) s x := by
  refine ⟨_, hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_add]
  exact hf.derivative_isComplexLinear.add hg.derivative_isComplexLinear

/-- The pointwise negation of a map constant-structure `J`-holomorphic within a set is
constant-structure `J`-holomorphic within it. -/
lemma IsConstStructureJHolomorphicWithinAt.neg {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    IsConstStructureJHolomorphicWithinAt J J' (-f) s x := by
  refine ⟨_, hf.hasFDerivWithinAt.neg, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_neg]
  exact hf.derivative_isComplexLinear.neg

/-- The pointwise difference of two maps constant-structure `J`-holomorphic within a set is
constant-structure `J`-holomorphic
within it. -/
lemma IsConstStructureJHolomorphicWithinAt.sub {f g : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hg : IsConstStructureJHolomorphicWithinAt J J' g s x) :
    IsConstStructureJHolomorphicWithinAt J J' (f - g) s x := by
  refine ⟨_, hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_sub]
  exact hf.derivative_isComplexLinear.sub hg.derivative_isComplexLinear

/-- A real scalar multiple of a map constant-structure `J`-holomorphic within a set is
constant-structure `J`-holomorphic within
it. -/
lemma IsConstStructureJHolomorphicWithinAt.const_smul {f : V → W} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (c : ℝ) :
    IsConstStructureJHolomorphicWithinAt J J' (c • f) s x := by
  refine ⟨_, hf.hasFDerivWithinAt.const_smul c, ?_⟩
  rw [ContinuousLinearMap.toLinearMap_smul]
  exact hf.derivative_isComplexLinear.smul c

/-- The pointwise sum of two maps constant-structure `J`-holomorphic on a set is constant-structure
`J`-holomorphic on it. -/
lemma IsConstStructureJHolomorphicOn.add {f g : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hg : IsConstStructureJHolomorphicOn J J' g s) :
    IsConstStructureJHolomorphicOn J J' (f + g) s :=
  fun x hx => (hf x hx).add (hg x hx)

/-- The pointwise negation of a map constant-structure `J`-holomorphic on a set is
constant-structure `J`-holomorphic on it. -/
lemma IsConstStructureJHolomorphicOn.neg {f : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) :
    IsConstStructureJHolomorphicOn J J' (-f) s :=
  fun x hx => (hf x hx).neg

/-- The pointwise difference of two maps constant-structure `J`-holomorphic on a set is
constant-structure `J`-holomorphic on it. -/
lemma IsConstStructureJHolomorphicOn.sub {f g : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (hg : IsConstStructureJHolomorphicOn J J' g s) :
    IsConstStructureJHolomorphicOn J J' (f - g) s :=
  fun x hx => (hf x hx).sub (hg x hx)

/-- A real scalar multiple of a map constant-structure `J`-holomorphic on a set is
constant-structure `J`-holomorphic on it. -/
lemma IsConstStructureJHolomorphicOn.const_smul {f : V → W} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J' f s)
    (c : ℝ) : IsConstStructureJHolomorphicOn J J' (c • f) s :=
  fun x hx => (hf x hx).const_smul c

/-- The pointwise sum of two globally constant-structure `J`-holomorphic maps is constant-structure
`J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.add {f g : V → W}
    (hf : IsConstStructureJHolomorphic J J' f) (hg : IsConstStructureJHolomorphic J J' g) :
    IsConstStructureJHolomorphic J J' (f + g) :=
  fun x => (hf x).add (hg x)

/-- The pointwise negation of a globally constant-structure `J`-holomorphic map is
constant-structure `J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.neg {f : V → W} (hf : IsConstStructureJHolomorphic J J' f) :
    IsConstStructureJHolomorphic J J' (-f) :=
  fun x => (hf x).neg

/-- The pointwise difference of two globally constant-structure `J`-holomorphic maps is
constant-structure `J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.sub {f g : V → W}
    (hf : IsConstStructureJHolomorphic J J' f) (hg : IsConstStructureJHolomorphic J J' g) :
    IsConstStructureJHolomorphic J J' (f - g) :=
  fun x => (hf x).sub (hg x)

/-- A real scalar multiple of a globally constant-structure `J`-holomorphic map is
constant-structure `J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.const_smul {f : V → W} (hf : IsConstStructureJHolomorphic J J' f)
    (c : ℝ) :
    IsConstStructureJHolomorphic J J' (c • f) :=
  fun x => (hf x).const_smul c

end LinearStructure

end TauCeti
