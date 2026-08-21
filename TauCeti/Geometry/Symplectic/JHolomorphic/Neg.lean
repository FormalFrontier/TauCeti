/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic

/-!
# Negating both almost complex structures

This file records the elementary sign-change invariance of the pointwise Cauchy--Riemann
equation used by the analytic Heegaard Floer roadmap. A real-linear map satisfies
`F ∘ J = J' ∘ F` exactly when it satisfies the same equation after both almost complex
structures are negated:

`F ∘ (-J) = (-J') ∘ F`.

The same invariance is packaged for the pointwise, within-set, setwise, and global
constant-structure `J`-holomorphic predicates. These lemmas are useful bookkeeping before the local
theory of
constant-structure `J`-holomorphic curves starts reflecting domains or changing orientation
conventions: the
analytic content stays in the Frechet derivative, while the simultaneous sign change is only
linear algebra.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.neg_neg`,
  `TauCeti.IsConstStructureJHolomorphicWithinAt.neg_neg`,
  `TauCeti.IsConstStructureJHolomorphicOn.neg_neg`, and
  `TauCeti.IsConstStructureJHolomorphic.neg_neg`: the four map-level forms.
* `TauCeti.isConstStructureJHolomorphicAt_neg_neg_iff` and its within-set, setwise, and global
analogues:
  rewrite-friendly equivalences.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: constant-structure `J`-holomorphicity is the equation `df ∘ J = J' ∘ df`.
-/

public section

namespace TauCeti

variable {V W : Type*}

section JHolomorphic

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x : V}

namespace IsConstStructureJHolomorphicAt

/-- Pointwise constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphicAt (-J) (-J') f x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt hf.hasFDerivAt
    hf.derivative_isComplexLinear.neg_neg

end IsConstStructureJHolomorphicAt

/-- Negating both almost complex structures leaves pointwise constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicAt_neg_neg_iff :
    IsConstStructureJHolomorphicAt (-J) (-J') f x ↔ IsConstStructureJHolomorphicAt J J' f x :=
  ⟨fun hf => isConstStructureJHolomorphicAt_of_hasFDerivAt hf.hasFDerivAt
      hf.derivative_isComplexLinear.of_neg_neg,
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphicWithinAt

/-- Within-set constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    IsConstStructureJHolomorphicWithinAt (-J) (-J') f s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt hf.hasFDerivWithinAt
    hf.derivative_isComplexLinear.neg_neg

end IsConstStructureJHolomorphicWithinAt

/-- Negating both almost complex structures leaves within-set constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_neg_neg_iff :
    IsConstStructureJHolomorphicWithinAt (-J) (-J') f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f s x :=
  ⟨fun hf => isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt hf.hasFDerivWithinAt
      hf.derivative_isComplexLinear.of_neg_neg,
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphicOn

/-- Setwise constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicOn J J' f s) :
    IsConstStructureJHolomorphicOn (-J) (-J') f s :=
  isConstStructureJHolomorphicOn_of_forall fun _ hx =>
    (hf.isConstStructureJHolomorphicWithinAt hx).neg_neg

end IsConstStructureJHolomorphicOn

/-- Negating both almost complex structures leaves setwise constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicOn_neg_neg_iff :
    IsConstStructureJHolomorphicOn (-J) (-J') f s ↔ IsConstStructureJHolomorphicOn J J' f s :=
  ⟨fun hf => isConstStructureJHolomorphicOn_of_forall fun _ hx =>
      (isConstStructureJHolomorphicWithinAt_neg_neg_iff).mp
        (hf.isConstStructureJHolomorphicWithinAt hx),
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphic

/-- Global constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg
    (hf : IsConstStructureJHolomorphic J J' f) : IsConstStructureJHolomorphic (-J) (-J') f :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).neg_neg

end IsConstStructureJHolomorphic

/-- Negating both almost complex structures leaves global constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphic_neg_neg_iff :
    IsConstStructureJHolomorphic (-J) (-J') f ↔ IsConstStructureJHolomorphic J J' f :=
  ⟨fun hf => isConstStructureJHolomorphic_of_forall fun x =>
      (isConstStructureJHolomorphicAt_neg_neg_iff).mp (hf.isConstStructureJHolomorphicAt x),
    fun hf => hf.neg_neg⟩

end JHolomorphic

end TauCeti
