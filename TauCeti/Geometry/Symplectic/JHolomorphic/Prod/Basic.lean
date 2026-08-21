/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic
public import TauCeti.Geometry.Symplectic.Prod.Basic

/-!
# Product operations for constant-structure `J`-holomorphic maps

This file adds the product calculus for the map-level constant-structure `J`-holomorphic predicate
used by the
analytic Heegaard Floer roadmap. The target product carries the direct-sum almost complex
structure from `TauCeti.Geometry.Symplectic.Prod.Basic`, and a map into that product is
constant-structure `J`-holomorphic exactly when its two coordinate maps are.

The API is deliberately local and linear: it packages Mathlib's Frechet-derivative product
rules with the existing linear direct-sum almost-complex API. Later strip, disk, product, and
symmetric-product targets can use these lemmas without unfolding the Cauchy--Riemann equation.

The file also records the source-and-target product calculus. When the source is itself a
product, the affine coordinate inclusions `v ↦ (v, w₀)` and `w ↦ (v₀, w)` are constant-structure
`J`-holomorphic, restriction of a product-source map along either inclusion preserves the
predicate, and the product map `Prod.map f g : V × W → V' × W'` is constant-structure
`J`-holomorphic for the direct-sum almost complex structures, both on arbitrary product-source
subsets and on rectangular product sets. These are the local product-chart facts needed before
strip, disk, product, and symmetric-product constructions can use the Cauchy--Riemann equation
without unfolding it.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.prodMk`, `IsConstStructureJHolomorphicWithinAt.prodMk`,
  `IsConstStructureJHolomorphicOn.prodMk`, and `IsConstStructureJHolomorphic.prodMk`: product maps
  of
  constant-structure `J`-holomorphic maps.
* `TauCeti.isConstStructureJHolomorphicAt_fst` and `isConstStructureJHolomorphicAt_snd`, with
within-set, setwise, and
  global variants: the coordinate projections are constant-structure `J`-holomorphic.
* `TauCeti.isConstStructureJHolomorphicAt_prod_iff`,
`isConstStructureJHolomorphicWithinAt_prod_iff`,
  `isConstStructureJHolomorphicOn_prod_iff`, and `isConstStructureJHolomorphic_prod_iff`:
  coordinatewise
  characterizations of constant-structure `J`-holomorphic maps into a product.
* `TauCeti.isConstStructureJHolomorphicAt_prodMk_left` and `..._prodMk_right`, with within-set,
  setwise, and global variants: the affine coordinate inclusions into a product.
* `TauCeti.IsConstStructureJHolomorphicAt.comp_prodMk_left` and `..._prodMk_right`, with within-set
  variants: restriction of a product-source map along a fixed coordinate inclusion.
* `TauCeti.IsConstStructureJHolomorphicAt.prodMap`, `IsConstStructureJHolomorphicWithinAt.prodMap`,
  `IsConstStructureJHolomorphicWithinAt.prodMap_prod`, `IsConstStructureJHolomorphicOn.prodMap`, and
  `IsConstStructureJHolomorphic.prodMap`: the product map `Prod.map f g`.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: product almost complex structures act componentwise and the Cauchy--Riemann equation
is preserved by products and coordinate inclusions.
-/

public section

namespace TauCeti

variable {V W X : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

section Projections

variable (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)

/-- The first coordinate projection is constant-structure `J`-holomorphic at every point. -/
@[simp]
lemma isConstStructureJHolomorphicAt_fst (p : V × W) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) J₁ Prod.fst p :=
  (isConstStructureJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.fst ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_fst J₁ J₂)

/-- The second coordinate projection is constant-structure `J`-holomorphic at every point. -/
@[simp]
lemma isConstStructureJHolomorphicAt_snd (p : V × W) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) J₂ Prod.snd p :=
  (isConstStructureJHolomorphicAt_continuousLinearMap_iff (ContinuousLinearMap.snd ℝ V W) p).mpr
    (AlmostComplexStructure.isComplexLinearMap_snd J₁ J₂)

/-- The first coordinate projection is constant-structure `J`-holomorphic within every set. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_fst (s : Set (V × W)) (p : V × W) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) J₁ Prod.fst s p :=
  (isConstStructureJHolomorphicAt_fst J₁ J₂ p).isConstStructureJHolomorphicWithinAt

/-- The second coordinate projection is constant-structure `J`-holomorphic within every set. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_snd (s : Set (V × W)) (p : V × W) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) J₂ Prod.snd s p :=
  (isConstStructureJHolomorphicAt_snd J₁ J₂ p).isConstStructureJHolomorphicWithinAt

/-- The first coordinate projection is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_fst (s : Set (V × W)) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) J₁ Prod.fst s :=
  isConstStructureJHolomorphicOn_of_forall fun p _ =>
    isConstStructureJHolomorphicWithinAt_fst J₁ J₂ s p

/-- The second coordinate projection is constant-structure `J`-holomorphic on every set. -/
@[simp]
lemma isConstStructureJHolomorphicOn_snd (s : Set (V × W)) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) J₂ Prod.snd s :=
  isConstStructureJHolomorphicOn_of_forall fun p _ =>
    isConstStructureJHolomorphicWithinAt_snd J₁ J₂ s p

/-- The first coordinate projection is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_fst :
    IsConstStructureJHolomorphic (J₁.prod J₂) J₁ Prod.fst :=
  isConstStructureJHolomorphic_of_forall fun p =>
    isConstStructureJHolomorphicAt_fst J₁ J₂ p

/-- The second coordinate projection is globally constant-structure `J`-holomorphic. -/
@[simp]
lemma isConstStructureJHolomorphic_snd :
    IsConstStructureJHolomorphic (J₁.prod J₂) J₂ Prod.snd :=
  isConstStructureJHolomorphic_of_forall fun p =>
    isConstStructureJHolomorphicAt_snd J₁ J₂ p

end Projections

section ProductMaps

variable {J : AlmostComplexStructure V} {J₁ : AlmostComplexStructure W}
variable {J₂ : AlmostComplexStructure X}

/-- Pairing two pointwise constant-structure `J`-holomorphic maps gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicAt.prodMk {f : V → W} {g : V → X} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J₁ f x) (hg : IsConstStructureJHolomorphicAt J J₂ g x) :
    IsConstStructureJHolomorphicAt J (J₁.prod J₂) (fun y => (f y, g y)) x := by
  refine isConstStructureJHolomorphicAt_of_hasFDerivAt
    (hf.hasFDerivAt.prodMk hg.hasFDerivAt) ?_
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps constant-structure `J`-holomorphic within a set gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMk {f : V → W} {g : V → X} {s : Set V} {x : V}
    (hf : IsConstStructureJHolomorphicWithinAt J J₁ f s x)
    (hg : IsConstStructureJHolomorphicWithinAt J J₂ g s x) :
    IsConstStructureJHolomorphicWithinAt J (J₁.prod J₂) (fun y => (f y, g y)) s x := by
  refine isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.prodMk hg.hasFDerivWithinAt) ?_
  exact hf.derivative_isComplexLinear.prod hg.derivative_isComplexLinear

/-- Pairing two maps constant-structure `J`-holomorphic on a set gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphicOn.prodMk {f : V → W} {g : V → X} {s : Set V}
    (hf : IsConstStructureJHolomorphicOn J J₁ f s) (hg : IsConstStructureJHolomorphicOn J J₂ g s) :
    IsConstStructureJHolomorphicOn J (J₁.prod J₂) (fun y => (f y, g y)) s :=
  isConstStructureJHolomorphicOn_of_forall fun _ hx =>
    (hf.isConstStructureJHolomorphicWithinAt hx).prodMk
      (hg.isConstStructureJHolomorphicWithinAt hx)

/-- Pairing two globally constant-structure `J`-holomorphic maps gives a constant-structure
`J`-holomorphic map into the direct-sum
almost complex structure. -/
lemma IsConstStructureJHolomorphic.prodMk {f : V → W} {g : V → X}
    (hf : IsConstStructureJHolomorphic J J₁ f) (hg : IsConstStructureJHolomorphic J J₂ g) :
    IsConstStructureJHolomorphic J (J₁.prod J₂) (fun y => (f y, g y)) :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).prodMk (hg.isConstStructureJHolomorphicAt x)

/-- A map into a direct-sum target is pointwise constant-structure `J`-holomorphic iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicAt_prod_iff (f : V → W × X) (x : V) :
    IsConstStructureJHolomorphicAt J (J₁.prod J₂) f x ↔
      IsConstStructureJHolomorphicAt J J₁ (fun y => (f y).1) x ∧
        IsConstStructureJHolomorphicAt J J₂ (fun y => (f y).2) x := by
  constructor
  · intro hf
    exact ⟨(isConstStructureJHolomorphicAt_fst J₁ J₂ (f x)).comp hf,
      (isConstStructureJHolomorphicAt_snd J₁ J₂ (f x)).comp hf⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is constant-structure `J`-holomorphic within a set iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_prod_iff (f : V → W × X) (s : Set V) (x : V) :
    IsConstStructureJHolomorphicWithinAt J (J₁.prod J₂) f s x ↔
      IsConstStructureJHolomorphicWithinAt J J₁ (fun y => (f y).1) s x ∧
        IsConstStructureJHolomorphicWithinAt J J₂ (fun y => (f y).2) s x := by
  constructor
  · intro hf
    exact ⟨(isConstStructureJHolomorphicWithinAt_fst J₁ J₂ Set.univ (f x)).comp hf (by simp),
      (isConstStructureJHolomorphicWithinAt_snd J₁ J₂ Set.univ (f x)).comp hf (by simp)⟩
  · intro h
    simpa using h.1.prodMk h.2

/-- A map into a direct-sum target is constant-structure `J`-holomorphic on a set iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphicOn_prod_iff (f : V → W × X) (s : Set V) :
    IsConstStructureJHolomorphicOn J (J₁.prod J₂) f s ↔
      IsConstStructureJHolomorphicOn J J₁ (fun y => (f y).1) s ∧
        IsConstStructureJHolomorphicOn J J₂ (fun y => (f y).2) s := by
  constructor
  · intro hf
    refine ⟨isConstStructureJHolomorphicOn_of_forall fun x hx => ?_,
      isConstStructureJHolomorphicOn_of_forall fun x hx => ?_⟩
    · exact ((isConstStructureJHolomorphicWithinAt_prod_iff f s x).mp
        (hf.isConstStructureJHolomorphicWithinAt hx)).1
    · exact ((isConstStructureJHolomorphicWithinAt_prod_iff f s x).mp
        (hf.isConstStructureJHolomorphicWithinAt hx)).2
  · intro h
    exact h.1.prodMk h.2

/-- A map into a direct-sum target is globally constant-structure `J`-holomorphic iff both
coordinate maps are. -/
@[simp]
lemma isConstStructureJHolomorphic_prod_iff (f : V → W × X) :
    IsConstStructureJHolomorphic J (J₁.prod J₂) f ↔
      IsConstStructureJHolomorphic J J₁ (fun y => (f y).1) ∧
        IsConstStructureJHolomorphic J J₂ (fun y => (f y).2) := by
  constructor
  · intro hf
    refine ⟨isConstStructureJHolomorphic_of_forall fun x => ?_,
      isConstStructureJHolomorphic_of_forall fun x => ?_⟩
    · exact ((isConstStructureJHolomorphicAt_prod_iff f x).mp
        (hf.isConstStructureJHolomorphicAt x)).1
    · exact ((isConstStructureJHolomorphicAt_prod_iff f x).mp
        (hf.isConstStructureJHolomorphicAt x)).2
  · intro h
    exact h.1.prodMk h.2

end ProductMaps

variable {V' W' : Type*}
variable [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup W'] [NormedSpace ℝ W']

section CoordinateInclusions

variable (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic. -/
lemma isConstStructureJHolomorphicAt_prodMk_left (w₀ : W) (v : V) :
    IsConstStructureJHolomorphicAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) v :=
  (isConstStructureJHolomorphicAt_id J₁ v).prodMk (isConstStructureJHolomorphicAt_const J₁ J₂ w₀ v)

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic. -/
lemma isConstStructureJHolomorphicAt_prodMk_right (v₀ : V) (w : W) :
    IsConstStructureJHolomorphicAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) w :=
  (isConstStructureJHolomorphicAt_const J₂ J₁ v₀ w).prodMk (isConstStructureJHolomorphicAt_id J₂ w)

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic within
every set. -/
lemma isConstStructureJHolomorphicWithinAt_prodMk_left (w₀ : W) (s : Set V) (v : V) :
    IsConstStructureJHolomorphicWithinAt J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s v :=
  (isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w₀ v).isConstStructureJHolomorphicWithinAt

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic within
every set. -/
lemma isConstStructureJHolomorphicWithinAt_prodMk_right (v₀ : V) (s : Set W) (w : W) :
    IsConstStructureJHolomorphicWithinAt J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s w :=
  (isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v₀ w).isConstStructureJHolomorphicWithinAt

/-- The affine inclusion of the first coordinate into a product is constant-structure
`J`-holomorphic on every
set. -/
lemma isConstStructureJHolomorphicOn_prodMk_left (w₀ : W) (s : Set V) :
    IsConstStructureJHolomorphicOn J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) s :=
  isConstStructureJHolomorphicOn_of_forall fun v _ =>
    isConstStructureJHolomorphicWithinAt_prodMk_left J₁ J₂ w₀ s v

/-- The affine inclusion of the second coordinate into a product is constant-structure
`J`-holomorphic on every
set. -/
lemma isConstStructureJHolomorphicOn_prodMk_right (v₀ : V) (s : Set W) :
    IsConstStructureJHolomorphicOn J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) s :=
  isConstStructureJHolomorphicOn_of_forall fun w _ =>
    isConstStructureJHolomorphicWithinAt_prodMk_right J₁ J₂ v₀ s w

/-- The affine inclusion of the first coordinate into a product is globally
constant-structure `J`-holomorphic. -/
lemma isConstStructureJHolomorphic_prodMk_left (w₀ : W) :
    IsConstStructureJHolomorphic J₁ (J₁.prod J₂) (fun v' : V => (v', w₀)) :=
  isConstStructureJHolomorphic_of_forall fun v =>
    isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w₀ v

/-- The affine inclusion of the second coordinate into a product is globally
constant-structure `J`-holomorphic. -/
lemma isConstStructureJHolomorphic_prodMk_right (v₀ : V) :
    IsConstStructureJHolomorphic J₂ (J₁.prod J₂) (fun w' : W => (v₀, w')) :=
  isConstStructureJHolomorphic_of_forall fun w =>
    isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v₀ w

end CoordinateInclusions

section CoordinateRestrictions

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K : AlmostComplexStructure X}

/-- Restricting a product-source constant-structure `J`-holomorphic map to a fixed second coordinate
preserves
constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicAt.comp_prodMk_left {f : V × W → X} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsConstStructureJHolomorphicAt J₁ K (fun v' : V => f (v', w)) v := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (x := v) hf
      (isConstStructureJHolomorphicAt_prodMk_left J₁ J₂ w v)

/-- Restricting a product-source constant-structure `J`-holomorphic map to a fixed first coordinate
preserves
constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicAt.comp_prodMk_right {f : V × W → X} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicAt (J₁.prod J₂) K f (v, w)) :
    IsConstStructureJHolomorphicAt J₂ K (fun w' : W => f (v, w')) w := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (x := w) hf
      (isConstStructureJHolomorphicAt_prodMk_right J₁ J₂ v w)

/-- Restricting a product-source map along a fixed second-coordinate inclusion preserves
within-set constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicWithinAt.comp_prodMk_left {f : V × W → X}
    {u : Set (V × W)} {s : Set V} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (hsu : Set.MapsTo (fun v' : V => (v', w)) s u) :
    IsConstStructureJHolomorphicWithinAt J₁ K (fun v' : V => f (v', w)) s v := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp (J := J₁) (J' := J₁.prod J₂) (J'' := K)
      (f := fun v' : V => (v', w)) (g := f) (s := s) (t := u) (x := v) hf
      (isConstStructureJHolomorphicWithinAt_prodMk_left J₁ J₂ w s v) hsu

/-- Restricting a product-source map along a fixed first-coordinate inclusion preserves
within-set constant-structure `J`-holomorphicity. -/
lemma IsConstStructureJHolomorphicWithinAt.comp_prodMk_right {f : V × W → X}
    {u : Set (V × W)} {t : Set W} {v : V} {w : W}
    (hf : IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) K f u (v, w))
    (htu : Set.MapsTo (fun w' : W => (v, w')) t u) :
    IsConstStructureJHolomorphicWithinAt J₂ K (fun w' : W => f (v, w')) t w := by
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp (J := J₂) (J' := J₁.prod J₂) (J'' := K)
      (f := fun w' : W => (v, w')) (g := f) (s := t) (t := u) (x := w) hf
      (isConstStructureJHolomorphicWithinAt_prodMk_right J₁ J₂ v t w) htu

end CoordinateRestrictions

section ProductMap

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
variable {K₁ : AlmostComplexStructure V'} {K₂ : AlmostComplexStructure W'}

/-- The product map of two pointwise constant-structure `J`-holomorphic maps is constant-structure
`J`-holomorphic for the
direct-sum almost complex structures. -/
lemma IsConstStructureJHolomorphicAt.prodMap {f : V → V'} {g : W → W'} {p : V × W}
    (hf : IsConstStructureJHolomorphicAt J₁ K₁ f p.1)
    (hg : IsConstStructureJHolomorphicAt J₂ K₂ g p.2) :
    IsConstStructureJHolomorphicAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) p := by
  refine isConstStructureJHolomorphicAt_of_hasFDerivAt
    (HasFDerivAt.prodMap (p := p) hf.hasFDerivAt hg.hasFDerivAt) ?_
  exact hf.derivative_isComplexLinear.prodMap hg.derivative_isComplexLinear

/-- The product map of two maps constant-structure `J`-holomorphic within the coordinate images of a
product-source
set is constant-structure `J`-holomorphic within that set. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMap {f : V → V'} {g : W → W'} {u : Set (V × W)}
    {p : V × W} (hf : IsConstStructureJHolomorphicWithinAt J₁ K₁ f (Prod.fst '' u) p.1)
    (hg : IsConstStructureJHolomorphicWithinAt J₂ K₂ g (Prod.snd '' u) p.2) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) u p := by
  refine isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (HasFDerivWithinAt.prodMap (p := p) (s := u) hf.hasFDerivWithinAt
      hg.hasFDerivWithinAt) ?_
  exact hf.derivative_isComplexLinear.prodMap hg.derivative_isComplexLinear

/-- The product map of two maps constant-structure `J`-holomorphic within sets is constant-structure
`J`-holomorphic within the
product set. -/
lemma IsConstStructureJHolomorphicWithinAt.prodMap_prod
    {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    {p : V × W} (hf : IsConstStructureJHolomorphicWithinAt J₁ K₁ f s p.1)
    (hg : IsConstStructureJHolomorphicWithinAt J₂ K₂ g t p.2) :
    IsConstStructureJHolomorphicWithinAt (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) p := by
  simpa [Prod.map] using
    ((hf.comp (isConstStructureJHolomorphicWithinAt_fst J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.1)).prodMk
      (hg.comp (isConstStructureJHolomorphicWithinAt_snd J₁ J₂ (s ×ˢ t) p) (fun q hq => hq.2)))

/-- The product map of two maps constant-structure `J`-holomorphic on sets is constant-structure
`J`-holomorphic on the product set. -/
lemma IsConstStructureJHolomorphicOn.prodMap {f : V → V'} {g : W → W'} {s : Set V} {t : Set W}
    (hf : IsConstStructureJHolomorphicOn J₁ K₁ f s)
    (hg : IsConstStructureJHolomorphicOn J₂ K₂ g t) :
    IsConstStructureJHolomorphicOn (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) (s ×ˢ t) := by
  exact isConstStructureJHolomorphicOn_of_forall fun p hp => by
    simpa [Prod.map] using
      (hf.isConstStructureJHolomorphicWithinAt hp.1).prodMap_prod
        (hg.isConstStructureJHolomorphicWithinAt hp.2)

/-- The product map of two globally constant-structure `J`-holomorphic maps is globally
constant-structure `J`-holomorphic. -/
lemma IsConstStructureJHolomorphic.prodMap {f : V → V'} {g : W → W'}
    (hf : IsConstStructureJHolomorphic J₁ K₁ f) (hg : IsConstStructureJHolomorphic J₂ K₂ g) :
    IsConstStructureJHolomorphic (J₁.prod J₂) (K₁.prod K₂) (Prod.map f g) :=
  isConstStructureJHolomorphic_of_forall fun p =>
    (hf.isConstStructureJHolomorphicAt p.1).prodMap
      (hg.isConstStructureJHolomorphicAt p.2)

end ProductMap

end TauCeti
