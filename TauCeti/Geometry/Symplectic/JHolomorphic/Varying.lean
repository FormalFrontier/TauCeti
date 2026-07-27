/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic

/-!
# J-holomorphic maps for varying almost complex structures

This file defines J-holomorphic maps between real normed spaces equipped with point-dependent
almost complex structures. At `x`, the Cauchy--Riemann equation is
`dfₓ ∘ J(x) = J'(f(x)) ∘ dfₓ`; in particular, the target structure is evaluated at the image
point. This is the local-coordinate model for J-holomorphic curves in Lane F2.1 of the analytic
Heegaard Floer roadmap.

The almost complex structures remain unbundled functions. No regularity is imposed on them by
the definition: continuity or smoothness belongs among the separate hypotheses of analytic
results that need it. The existing constant-structure API is recovered by specializing both
functions to constants.

## Main declarations

* `TauCeti.IsJHolomorphicAt`: J-holomorphicity at a point for varying structures.
* `TauCeti.IsJHolomorphicWithinAt`: the corresponding within-set predicate.
* `TauCeti.IsJHolomorphicOn` and `TauCeti.IsJHolomorphic`: setwise and global predicates.
* `TauCeti.IsJHolomorphicAt.comp`: composition of J-holomorphic maps.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1.
-/

public section

namespace TauCeti

variable {U V W : Type*}
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A map is J-holomorphic at a point when it has a Fréchet derivative there which intertwines
the source structure at that point with the target structure at the image point. -/
def IsJHolomorphicAt (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (x : U) : Prop :=
  IsConstStructureJHolomorphicAt (J x) (J' (f x)) f x

/-- A map is J-holomorphic within a set at a point when its derivative within the set
intertwines the structures at that point and its image. -/
def IsJHolomorphicWithinAt (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) : Prop :=
  IsConstStructureJHolomorphicWithinAt (J x) (J' (f x)) f s x

/-- A map is J-holomorphic on a set when it is J-holomorphic within that set at every point
of the set. -/
def IsJHolomorphicOn (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) : Prop :=
  ∀ x ∈ s, IsJHolomorphicWithinAt J J' f s x

/-- A map is globally J-holomorphic when it is J-holomorphic at every point. -/
def IsJHolomorphic (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) : Prop :=
  ∀ x, IsJHolomorphicAt J J' f x

/-- Restate pointwise J-holomorphicity as the existence of a complex-linear derivative. -/
lemma isJHolomorphicAt_iff (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (x : U) :
    IsJHolomorphicAt J J' f x ↔
      ∃ f' : U →L[ℝ] V,
        HasFDerivAt f f' x ∧ IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap :=
  isConstStructureJHolomorphicAt_iff (J x) (J' (f x)) f x

/-- Restate within-set J-holomorphicity as the existence of a complex-linear derivative
within the set. -/
lemma isJHolomorphicWithinAt_iff (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt J J' f s x ↔
      ∃ f' : U →L[ℝ] V,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap :=
  isConstStructureJHolomorphicWithinAt_iff (J x) (J' (f x)) f s x

/-- Restate setwise J-holomorphicity as the pointwise within-set condition. -/
lemma isJHolomorphicOn_iff (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) :
    IsJHolomorphicOn J J' f s ↔
      ∀ x ∈ s, IsJHolomorphicWithinAt J J' f s x :=
  Iff.rfl

/-- Restate global J-holomorphicity as pointwise J-holomorphicity everywhere. -/
lemma isJHolomorphic_iff (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) :
    IsJHolomorphic J J' f ↔ ∀ x, IsJHolomorphicAt J J' f x :=
  Iff.rfl

/-- Build pointwise J-holomorphicity from a complex-linear Fréchet derivative. -/
lemma isJHolomorphicAt_of_hasFDerivAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U} {f' : U →L[ℝ] V}
    (hf : HasFDerivAt f f' x) (hlin : IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap) :
    IsJHolomorphicAt J J' f x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt hf hlin

/-- Build within-set J-holomorphicity from a complex-linear derivative within the set. -/
lemma isJHolomorphicWithinAt_of_hasFDerivWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    {f' : U →L[ℝ] V} (hf : HasFDerivWithinAt f f' s x)
    (hlin : IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap) :
    IsJHolomorphicWithinAt J J' f s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt hf hlin

/-- The continuous-linear derivative witnessing J-holomorphicity at a point. -/
lemma IsJHolomorphicAt.hasFDerivAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) :
    HasFDerivAt f (Classical.choose ((isJHolomorphicAt_iff J J' f x).mp hf)) x :=
  IsConstStructureJHolomorphicAt.hasFDerivAt hf

/-- The chosen derivative at a J-holomorphic point is complex-linear. -/
lemma IsJHolomorphicAt.derivative_isComplexLinear {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap (J x) (J' (f x))
      (Classical.choose ((isJHolomorphicAt_iff J J' f x).mp hf)).toLinearMap :=
  IsConstStructureJHolomorphicAt.derivative_isComplexLinear hf

/-- A J-holomorphic map at a point is differentiable there. -/
lemma IsJHolomorphicAt.differentiableAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) : DifferentiableAt ℝ f x :=
  IsConstStructureJHolomorphicAt.differentiableAt hf

/-- The continuous-linear derivative witnessing within-set J-holomorphicity. -/
lemma IsJHolomorphicWithinAt.hasFDerivWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) :
    HasFDerivWithinAt f
      (Classical.choose ((isJHolomorphicWithinAt_iff J J' f s x).mp hf)) s x :=
  IsConstStructureJHolomorphicWithinAt.hasFDerivWithinAt hf

/-- A map J-holomorphic within a set at a point is differentiable within that set. -/
lemma IsJHolomorphicWithinAt.differentiableWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) : DifferentiableWithinAt ℝ f s x :=
  IsConstStructureJHolomorphicWithinAt.differentiableWithinAt hf

/-- A J-holomorphic map at a point is continuous there. -/
lemma IsJHolomorphicAt.continuousAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) : ContinuousAt f x :=
  IsConstStructureJHolomorphicAt.continuousAt hf

/-- A map J-holomorphic within a set at a point is continuous within that set. -/
lemma IsJHolomorphicWithinAt.continuousWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) : ContinuousWithinAt f s x :=
  IsConstStructureJHolomorphicWithinAt.continuousWithinAt hf

/-- The Fréchet derivative of a J-holomorphic map is complex-linear. -/
lemma IsJHolomorphicAt.fderiv_isComplexLinear {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) :
    IsComplexLinearMap (J x) (J' (f x)) (fderiv ℝ f x).toLinearMap :=
  IsConstStructureJHolomorphicAt.fderiv_isComplexLinear hf

/-- The Fréchet derivative of a J-holomorphic map commutes with the structures. -/
lemma IsJHolomorphicAt.fderiv_apply_commute {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x v : U}
    (hf : IsJHolomorphicAt J J' f x) :
    fderiv ℝ f x (J x v) = J' (f x) (fderiv ℝ f x v) :=
  IsConstStructureJHolomorphicAt.fderiv_apply_commute hf

/-- Pointwise J-holomorphicity implies J-holomorphicity within any set. -/
lemma IsJHolomorphicAt.isJHolomorphicWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicAt J J' f x) : IsJHolomorphicWithinAt J J' f s x :=
  IsConstStructureJHolomorphicAt.isConstStructureJHolomorphicWithinAt hf

/-- The chosen within-set derivative is complex-linear. -/
lemma IsJHolomorphicWithinAt.derivative_isComplexLinear {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) :
    IsComplexLinearMap (J x) (J' (f x))
      (Classical.choose ((isJHolomorphicWithinAt_iff J J' f s x).mp hf)).toLinearMap :=
  IsConstStructureJHolomorphicWithinAt.derivative_isComplexLinear hf

/-- The within-set Fréchet derivative is complex-linear when derivatives are unique. -/
lemma IsJHolomorphicWithinAt.fderivWithin_isComplexLinear
    {J : U → AlmostComplexStructure U} {J' : V → AlmostComplexStructure V}
    {f : U → V} {s : Set U} {x : U} (hf : IsJHolomorphicWithinAt J J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    IsComplexLinearMap (J x) (J' (f x)) (fderivWithin ℝ f s x).toLinearMap :=
  IsConstStructureJHolomorphicWithinAt.fderivWithin_isComplexLinear hf hs

/-- The within-set Fréchet derivative commutes with the structures. -/
lemma IsJHolomorphicWithinAt.fderivWithin_apply_commute
    {J : U → AlmostComplexStructure U} {J' : V → AlmostComplexStructure V}
    {f : U → V} {s : Set U} {x v : U} (hf : IsJHolomorphicWithinAt J J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x (J x v) = J' (f x) (fderivWithin ℝ f s x v) :=
  IsConstStructureJHolomorphicWithinAt.fderivWithin_apply_commute hf hs

/-- Within-set J-holomorphicity on a neighborhood implies pointwise J-holomorphicity. -/
lemma IsJHolomorphicWithinAt.isJHolomorphicAt_of_mem_nhds {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) (hs : s ∈ nhds x) :
    IsJHolomorphicAt J J' f x :=
  IsConstStructureJHolomorphicWithinAt.isConstStructureJHolomorphicAt_of_mem_nhds hf hs

/-- A setwise J-holomorphic map is J-holomorphic within the set at each member. -/
lemma IsJHolomorphicOn.isJHolomorphicWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U}
    (hf : IsJHolomorphicOn J J' f s) {x : U} (hx : x ∈ s) :
    IsJHolomorphicWithinAt J J' f s x :=
  hf x hx

/-- Restrict the domain set of a setwise J-holomorphic map. -/
lemma IsJHolomorphicOn.mono
    {J : U → AlmostComplexStructure U} {J' : V → AlmostComplexStructure V}
    {f : U → V} {s t : Set U} (hf : IsJHolomorphicOn J J' f t) (hst : s ⊆ t) :
    IsJHolomorphicOn J J' f s :=
  fun x hx ↦
    let hfx := hf x (hst hx)
    isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
      (hfx.hasFDerivWithinAt.mono hst) hfx.derivative_isComplexLinear

/-- A setwise J-holomorphic map is differentiable on its domain. -/
lemma IsJHolomorphicOn.differentiableOn {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U}
    (hf : IsJHolomorphicOn J J' f s) : DifferentiableOn ℝ f s :=
  fun x hx ↦ (hf x hx).differentiableWithinAt

/-- A setwise J-holomorphic map is continuous on its domain. -/
lemma IsJHolomorphicOn.continuousOn {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U}
    (hf : IsJHolomorphicOn J J' f s) : ContinuousOn f s :=
  fun x hx ↦ (hf x hx).continuousWithinAt

/-- A globally J-holomorphic map is J-holomorphic on every set. -/
lemma IsJHolomorphic.isJHolomorphicOn {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V}
    (hf : IsJHolomorphic J J' f) (s : Set U) : IsJHolomorphicOn J J' f s :=
  fun x _ ↦ (hf x).isJHolomorphicWithinAt

/-- A globally J-holomorphic map is differentiable. -/
lemma IsJHolomorphic.differentiable {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V}
    (hf : IsJHolomorphic J J' f) : Differentiable ℝ f :=
  fun x ↦ (hf x).differentiableAt

/-- A globally J-holomorphic map is continuous. -/
lemma IsJHolomorphic.continuous {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V}
    (hf : IsJHolomorphic J J' f) : Continuous f :=
  hf.differentiable.continuous

/-- J-holomorphicity on the whole space is equivalent to global J-holomorphicity. -/
@[simp]
lemma isJHolomorphicOn_univ (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) :
    IsJHolomorphicOn J J' f Set.univ ↔ IsJHolomorphic J J' f := by
  constructor
  · intro hf x
    exact (hf x (Set.mem_univ x)).isJHolomorphicAt_of_mem_nhds (by simp)
  · intro hf x _
    exact (hf x).isJHolomorphicWithinAt

/-- For constant structure functions, varying-structure pointwise J-holomorphicity is exactly
the existing constant-structure predicate. -/
@[simp]
lemma isJHolomorphicAt_constStructure_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (x : U) :
    IsJHolomorphicAt (fun _ ↦ J) (fun _ ↦ J') f x ↔
      IsConstStructureJHolomorphicAt J J' f x :=
  Iff.rfl

/-- For constant structure functions, varying-structure within-set J-holomorphicity is exactly
the existing constant-structure predicate. -/
@[simp]
lemma isJHolomorphicWithinAt_constStructure_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt (fun _ ↦ J) (fun _ ↦ J') f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f s x :=
  Iff.rfl

/-- For constant structure functions, setwise J-holomorphicity is exactly the existing
constant-structure predicate. -/
@[simp]
lemma isJHolomorphicOn_constStructure_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (s : Set U) :
    IsJHolomorphicOn (fun _ ↦ J) (fun _ ↦ J') f s ↔
      IsConstStructureJHolomorphicOn J J' f s := by
  constructor
  · intro hf
    exact isConstStructureJHolomorphicOn_of_forall hf
  · intro hf x hx
    exact hf.isConstStructureJHolomorphicWithinAt hx

/-- For constant structure functions, global J-holomorphicity is exactly the existing
constant-structure predicate. -/
@[simp]
lemma isJHolomorphic_constStructure_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) :
    IsJHolomorphic (fun _ ↦ J) (fun _ ↦ J') f ↔
      IsConstStructureJHolomorphic J J' f := by
  constructor
  · intro hf
    exact isConstStructureJHolomorphic_of_forall hf
  · intro hf x
    exact hf.isConstStructureJHolomorphicAt x

/-- The identity map is J-holomorphic at every point for every varying almost complex
structure. -/
@[simp]
lemma isJHolomorphicAt_id (J : U → AlmostComplexStructure U) (x : U) :
    IsJHolomorphicAt J J id x :=
  isConstStructureJHolomorphicAt_id (J x) x

/-- A constant map is J-holomorphic at every point for arbitrary source and target structures. -/
@[simp]
lemma isJHolomorphicAt_const (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (c : V) (x : U) :
    IsJHolomorphicAt J J' (fun _ ↦ c) x :=
  isConstStructureJHolomorphicAt_const (J x) (J' c) c x

/-- The identity map is J-holomorphic within every set at every point. -/
@[simp]
lemma isJHolomorphicWithinAt_id (J : U → AlmostComplexStructure U) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt J J id s x :=
  (isJHolomorphicAt_id J x).isJHolomorphicWithinAt

/-- A constant map is J-holomorphic within every set at every point. -/
@[simp]
lemma isJHolomorphicWithinAt_const (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (c : V) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt J J' (fun _ ↦ c) s x :=
  (isJHolomorphicAt_const J J' c x).isJHolomorphicWithinAt

/-- The identity map is J-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_id (J : U → AlmostComplexStructure U) (s : Set U) :
    IsJHolomorphicOn J J id s :=
  fun x _ ↦ isJHolomorphicWithinAt_id J s x

/-- A constant map is J-holomorphic on every set. -/
@[simp]
lemma isJHolomorphicOn_const (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (c : V) (s : Set U) :
    IsJHolomorphicOn J J' (fun _ ↦ c) s :=
  fun x _ ↦ isJHolomorphicWithinAt_const J J' c s x

/-- The identity map is J-holomorphic for every varying almost complex structure. -/
@[simp]
lemma isJHolomorphic_id (J : U → AlmostComplexStructure U) :
    IsJHolomorphic J J id := by
  intro x
  exact isConstStructureJHolomorphicAt_id (J x) x

/-- A constant map is J-holomorphic for arbitrary source and target structures. -/
@[simp]
lemma isJHolomorphic_const (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (c : V) :
    IsJHolomorphic J J' (fun _ ↦ c) := by
  intro x
  exact isConstStructureJHolomorphicAt_const (J x) (J' c) c x

/-- The composition of two J-holomorphic maps is J-holomorphic at a point. -/
lemma IsJHolomorphicAt.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} {x : U}
    (hg : IsJHolomorphicAt J' J'' g (f x)) (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt J J'' (g ∘ f) x :=
  IsConstStructureJHolomorphicAt.comp hg hf

/-- The composition of two within-set J-holomorphic maps is J-holomorphic within the source set. -/
lemma IsJHolomorphicWithinAt.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} {s : Set U} {t : Set V} {x : U}
    (hg : IsJHolomorphicWithinAt J' J'' g t (f x))
    (hf : IsJHolomorphicWithinAt J J' f s x) (hst : Set.MapsTo f s t) :
    IsJHolomorphicWithinAt J J'' (g ∘ f) s x :=
  IsConstStructureJHolomorphicWithinAt.comp hg hf hst

/-- The composition of two setwise J-holomorphic maps is J-holomorphic on the source set. -/
lemma IsJHolomorphicOn.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} {s : Set U} {t : Set V}
    (hg : IsJHolomorphicOn J' J'' g t) (hf : IsJHolomorphicOn J J' f s)
    (hst : Set.MapsTo f s t) : IsJHolomorphicOn J J'' (g ∘ f) s :=
  fun x hx ↦ (hg (f x) (hst hx)).comp (hf x hx) hst

/-- The composition of two globally J-holomorphic maps is globally J-holomorphic. -/
lemma IsJHolomorphic.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} (hg : IsJHolomorphic J' J'' g)
    (hf : IsJHolomorphic J J' f) : IsJHolomorphic J J'' (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

end TauCeti
