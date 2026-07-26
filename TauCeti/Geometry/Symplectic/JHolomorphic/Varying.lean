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
  ∃ f' : U →L[ℝ] V, HasFDerivAt f f' x ∧ IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap

/-- A map is J-holomorphic within a set at a point when its derivative within the set
intertwines the structures at that point and its image. -/
def IsJHolomorphicWithinAt (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) : Prop :=
  ∃ f' : U →L[ℝ] V,
    HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap

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
  Iff.rfl

/-- Restate within-set J-holomorphicity as the existence of a complex-linear derivative
within the set. -/
lemma isJHolomorphicWithinAt_iff (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt J J' f s x ↔
      ∃ f' : U →L[ℝ] V,
        HasFDerivWithinAt f f' s x ∧ IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap :=
  Iff.rfl

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
  ⟨f', hf, hlin⟩

/-- Build within-set J-holomorphicity from a complex-linear derivative within the set. -/
lemma isJHolomorphicWithinAt_of_hasFDerivWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    {f' : U →L[ℝ] V} (hf : HasFDerivWithinAt f f' s x)
    (hlin : IsComplexLinearMap (J x) (J' (f x)) f'.toLinearMap) :
    IsJHolomorphicWithinAt J J' f s x :=
  ⟨f', hf, hlin⟩

/-- A J-holomorphic map at a point is differentiable there. -/
lemma IsJHolomorphicAt.differentiableAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) : DifferentiableAt ℝ f x :=
  hf.choose_spec.1.differentiableAt

/-- A map J-holomorphic within a set at a point is differentiable within that set. -/
lemma IsJHolomorphicWithinAt.differentiableWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) : DifferentiableWithinAt ℝ f s x :=
  hf.choose_spec.1.differentiableWithinAt

/-- A J-holomorphic map at a point is continuous there. -/
lemma IsJHolomorphicAt.continuousAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {x : U}
    (hf : IsJHolomorphicAt J J' f x) : ContinuousAt f x :=
  hf.differentiableAt.continuousAt

/-- A map J-holomorphic within a set at a point is continuous within that set. -/
lemma IsJHolomorphicWithinAt.continuousWithinAt {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {f : U → V} {s : Set U} {x : U}
    (hf : IsJHolomorphicWithinAt J J' f s x) : ContinuousWithinAt f s x :=
  hf.differentiableWithinAt.continuousWithinAt

/-- J-holomorphicity on the whole space is equivalent to global J-holomorphicity. -/
@[simp]
lemma isJHolomorphicOn_univ (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (f : U → V) :
    IsJHolomorphicOn J J' f Set.univ ↔ IsJHolomorphic J J' f := by
  simp only [IsJHolomorphicOn, IsJHolomorphicWithinAt, IsJHolomorphic,
    IsJHolomorphicAt, Set.mem_univ, forall_const, hasFDerivWithinAt_univ]

/-- For constant structure functions, varying-structure pointwise J-holomorphicity is exactly
the existing constant-structure predicate. -/
@[simp]
lemma isJHolomorphicAt_const_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (x : U) :
    IsJHolomorphicAt (fun _ ↦ J) (fun _ ↦ J') f x ↔
      IsConstStructureJHolomorphicAt J J' f x := by
  rw [isConstStructureJHolomorphicAt_iff]
  rfl

/-- For constant structure functions, varying-structure within-set J-holomorphicity is exactly
the existing constant-structure predicate. -/
@[simp]
lemma isJHolomorphicWithinAt_const_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (s : Set U) (x : U) :
    IsJHolomorphicWithinAt (fun _ ↦ J) (fun _ ↦ J') f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f s x := by
  rw [isConstStructureJHolomorphicWithinAt_iff]
  rfl

/-- For constant structure functions, setwise J-holomorphicity is exactly the existing
constant-structure predicate. -/
@[simp]
lemma isJHolomorphicOn_const_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) (s : Set U) :
    IsJHolomorphicOn (fun _ ↦ J) (fun _ ↦ J') f s ↔
      IsConstStructureJHolomorphicOn J J' f s := by
  rw [isConstStructureJHolomorphicOn_iff]
  rfl

/-- For constant structure functions, global J-holomorphicity is exactly the existing
constant-structure predicate. -/
@[simp]
lemma isJHolomorphic_const_iff (J : AlmostComplexStructure U)
    (J' : AlmostComplexStructure V) (f : U → V) :
    IsJHolomorphic (fun _ ↦ J) (fun _ ↦ J') f ↔
      IsConstStructureJHolomorphic J J' f := by
  rw [isConstStructureJHolomorphic_iff]
  rfl

/-- The identity map is J-holomorphic for every varying almost complex structure. -/
lemma isJHolomorphic_id (J : U → AlmostComplexStructure U) :
    IsJHolomorphic J J id := by
  intro x
  refine ⟨ContinuousLinearMap.id ℝ U, hasFDerivAt_id x, ?_⟩
  exact isComplexLinearMap_id (J x)

/-- A constant map is J-holomorphic for arbitrary source and target structures. -/
lemma isJHolomorphic_const (J : U → AlmostComplexStructure U)
    (J' : V → AlmostComplexStructure V) (c : V) :
    IsJHolomorphic J J' (fun _ ↦ c) := by
  intro x
  exact ⟨0, hasFDerivAt_const c x, isComplexLinearMap_zero (J x) (J' c)⟩

/-- The composition of two J-holomorphic maps is J-holomorphic at a point. -/
lemma IsJHolomorphicAt.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} {x : U}
    (hg : IsJHolomorphicAt J' J'' g (f x)) (hf : IsJHolomorphicAt J J' f x) :
    IsJHolomorphicAt J J'' (g ∘ f) x := by
  obtain ⟨g', hg', hglin⟩ := hg
  obtain ⟨f', hf', hflin⟩ := hf
  refine ⟨g'.comp f', hg'.comp x hf', ?_⟩
  rw [ContinuousLinearMap.toLinearMap_comp]
  exact hglin.comp hflin

/-- The composition of two globally J-holomorphic maps is globally J-holomorphic. -/
lemma IsJHolomorphic.comp {J : U → AlmostComplexStructure U}
    {J' : V → AlmostComplexStructure V} {J'' : W → AlmostComplexStructure W}
    {f : U → V} {g : V → W} (hg : IsJHolomorphic J' J'' g)
    (hf : IsJHolomorphic J J' f) : IsJHolomorphic J J'' (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

end TauCeti
