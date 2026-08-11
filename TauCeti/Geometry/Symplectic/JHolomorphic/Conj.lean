/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line

/-!
# Conjugation of the standard complex line

This file records the flat reflection map on the standard complex line `ℝ × ℝ`,
`(s, t) ↦ (s, -t)`, and its interaction with the constant-structure Cauchy--Riemann
predicate. Conjugation anticommutes with the standard almost complex structure
`AlmostComplexStructure.product ℝ`, hence it is complex-linear from the standard structure to
the negated one, and conversely from the negated structure back to the standard one.

This is local-model bookkeeping for the analytic Heegaard Floer roadmap. The Schwarz-reflection
and boundary-regularity targets in Lane F1.2, and the flat `J`-holomorphic map layer in Lane F2.1,
need a reusable formal statement that reflecting the source changes the sign of the domain
complex structure while preserving the Cauchy--Riemann equation.

## Main declarations

* `TauCeti.stdComplexLineConj`: the real-linear reflection `(s, t) ↦ (s, -t)`.
* `TauCeti.stdComplexLineConjCLM`: the same map as a continuous linear map.
* `TauCeti.isComplexLinearMap_stdComplexLineConj` and
  `TauCeti.isComplexLinearMap_neg_stdComplexLineConj`: conjugation is complex-linear after
  negating exactly one of the source or target standard structures.
* `TauCeti.isConstStructureJHolomorphic_stdComplexLineConj` and
  `TauCeti.isConstStructureJHolomorphic_neg_stdComplexLineConj`: the corresponding
  constant-structure `J`-holomorphic statements.
* `TauCeti.IsConstStructureJHolomorphicAt.comp_stdComplexLineConj` and
  `TauCeti.IsConstStructureJHolomorphicAt.comp_neg_stdComplexLineConj`: precomposition by
  reflection changes the source complex structure by a sign.
* `TauCeti.IsConstStructureJHolomorphicWithinAt.comp_stdComplexLineConj`,
  `TauCeti.IsConstStructureJHolomorphicOn.comp_stdComplexLineConj`, and their negated variants:
  the within-set and setwise forms of the same precomposition, taking the reflection's
  `Set.MapsTo` hypothesis needed for boundary/domain-restricted reflection arguments.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: `du ∘ j = J ∘ du`. Since conjugation satisfies `dc ∘ j = (-j) ∘ dc`, reflected
source coordinates carry the negated domain structure.
-/

public section

namespace TauCeti

/-- Complex conjugation on the standard complex line `ℝ × ℝ`, written in real coordinates as
`(s, t) ↦ (s, -t)`. -/
@[expose]
def stdComplexLineConj : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun z := (z.1, -z.2)
  map_add' z w := by
    ext <;> simp [add_comm]
  map_smul' c z := by
    ext <;> simp

/-- Complex conjugation on `ℝ × ℝ` as a continuous linear map. -/
@[expose]
def stdComplexLineConjCLM : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-(ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp]
lemma stdComplexLineConj_apply (z : ℝ × ℝ) :
    stdComplexLineConj z = (z.1, -z.2) :=
  rfl

@[simp]
lemma stdComplexLineConjCLM_apply (z : ℝ × ℝ) :
    stdComplexLineConjCLM z = (z.1, -z.2) :=
  rfl

@[simp]
lemma stdComplexLineConjCLM_toLinearMap :
    stdComplexLineConjCLM.toLinearMap = stdComplexLineConj := by
  apply LinearMap.ext
  intro z
  rfl

/-- Conjugation fixes the real coordinate vector. -/
lemma stdComplexLineConj_apply_real :
    stdComplexLineConj stdComplexLineReal = stdComplexLineReal := by
  ext <;> simp [stdComplexLineReal]

/-- Conjugation negates the imaginary coordinate vector. -/
lemma stdComplexLineConj_apply_imag :
    stdComplexLineConj stdComplexLineImag = -stdComplexLineImag := by
  ext <;> simp [stdComplexLineImag]

/-- Applying standard-line conjugation twice is the identity. -/
@[simp]
lemma stdComplexLineConj_comp_self :
    stdComplexLineConj.comp stdComplexLineConj = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp [stdComplexLineConj]

/-- Pointwise form of `stdComplexLineConj_comp_self`. -/
lemma stdComplexLineConj_apply_apply (z : ℝ × ℝ) :
    stdComplexLineConj (stdComplexLineConj z) = z := by
  simp

/-- Conjugation anticommutes with the standard complex structure on `ℝ × ℝ`. -/
lemma stdComplexLineConj_apply_product (z : ℝ × ℝ) :
    stdComplexLineConj (AlmostComplexStructure.product ℝ z) =
      -(AlmostComplexStructure.product ℝ) (stdComplexLineConj z) := by
  ext <;> simp [stdComplexLineConj, AlmostComplexStructure.product_apply]

/-- Equivalently, applying the standard structure after conjugation is the negative of conjugating
after the standard structure. -/
lemma product_apply_stdComplexLineConj (z : ℝ × ℝ) :
    AlmostComplexStructure.product ℝ (stdComplexLineConj z) =
      -stdComplexLineConj (AlmostComplexStructure.product ℝ z) := by
  rw [stdComplexLineConj_apply_product]
  simp

/-- Standard-line conjugation is complex-linear from the standard structure to the negated
standard structure. -/
lemma isComplexLinearMap_stdComplexLineConj :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (-(AlmostComplexStructure.product ℝ))
      stdComplexLineConj := by
  rw [isComplexLinearMap_iff_apply]
  exact stdComplexLineConj_apply_product

/-- Standard-line conjugation is complex-linear from the negated standard structure back to the
standard structure. -/
lemma isComplexLinearMap_neg_stdComplexLineConj :
    IsComplexLinearMap (-(AlmostComplexStructure.product ℝ)) (AlmostComplexStructure.product ℝ)
      stdComplexLineConj := by
  rw [isComplexLinearMap_iff_apply]
  intro z
  rw [product_apply_stdComplexLineConj]
  simp

/-- Standard-line conjugation, as a continuous linear map, is constant-structure
`J`-holomorphic from the standard structure to the negated standard structure. -/
lemma isConstStructureJHolomorphic_stdComplexLineConj :
    IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ)
      (-(AlmostComplexStructure.product ℝ)) stdComplexLineConjCLM :=
  (isConstStructureJHolomorphic_continuousLinearMap_iff stdComplexLineConjCLM).mpr
    (by simpa using isComplexLinearMap_stdComplexLineConj)

/-- Standard-line conjugation, as a continuous linear map, is constant-structure
`J`-holomorphic from the negated standard structure back to the standard structure. -/
lemma isConstStructureJHolomorphic_neg_stdComplexLineConj :
    IsConstStructureJHolomorphic (-(AlmostComplexStructure.product ℝ))
      (AlmostComplexStructure.product ℝ) stdComplexLineConjCLM :=
  (isConstStructureJHolomorphic_continuousLinearMap_iff stdComplexLineConjCLM).mpr
    (by simpa using isComplexLinearMap_neg_stdComplexLineConj)

namespace IsConstStructureJHolomorphicAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {f : ℝ × ℝ → W} {x : ℝ × ℝ}

/-- Precomposing a pointwise constant-structure `J`-holomorphic map by standard-line conjugation
changes the source structure from the standard one to its negation. -/
lemma comp_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f
      (stdComplexLineConjCLM x)) :
    IsConstStructureJHolomorphicAt (-(AlmostComplexStructure.product ℝ)) J
      (fun z => f (stdComplexLineConjCLM z)) x :=
  hf.comp (isConstStructureJHolomorphic_neg_stdComplexLineConj.isConstStructureJHolomorphicAt x)

/-- Precomposing a pointwise constant-structure `J`-holomorphic map whose source has the negated
standard structure by standard-line conjugation restores the standard source structure. -/
lemma comp_neg_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicAt (-(AlmostComplexStructure.product ℝ)) J f
      (stdComplexLineConjCLM x)) :
    IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J
      (fun z => f (stdComplexLineConjCLM z)) x :=
  hf.comp (isConstStructureJHolomorphic_stdComplexLineConj.isConstStructureJHolomorphicAt x)

end IsConstStructureJHolomorphicAt

namespace IsConstStructureJHolomorphic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {f : ℝ × ℝ → W}

/-- Precomposing a global constant-structure `J`-holomorphic map by standard-line conjugation
changes the source structure from the standard one to its negation. -/
lemma comp_stdComplexLineConj
    (hf : IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ) J f) :
    IsConstStructureJHolomorphic (-(AlmostComplexStructure.product ℝ)) J
      (fun z => f (stdComplexLineConjCLM z)) :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt (stdComplexLineConjCLM x)).comp_stdComplexLineConj

/-- Precomposing a global constant-structure `J`-holomorphic map whose source has the negated
standard structure by standard-line conjugation restores the standard source structure. -/
lemma comp_neg_stdComplexLineConj
    (hf : IsConstStructureJHolomorphic (-(AlmostComplexStructure.product ℝ)) J f) :
    IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ) J
      (fun z => f (stdComplexLineConjCLM z)) :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt (stdComplexLineConjCLM x)).comp_neg_stdComplexLineConj

end IsConstStructureJHolomorphic

namespace IsConstStructureJHolomorphicWithinAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {f : ℝ × ℝ → W} {s t : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- Precomposing a within-set constant-structure `J`-holomorphic map by standard-line conjugation
changes the source structure from the standard one to its negation, provided reflection maps the
reflected source set into the original one. -/
lemma comp_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f t
      (stdComplexLineConjCLM x)) (hst : Set.MapsTo stdComplexLineConjCLM s t) :
    IsConstStructureJHolomorphicWithinAt (-(AlmostComplexStructure.product ℝ)) J
      (fun z => f (stdComplexLineConjCLM z)) s x :=
  hf.comp
    (isConstStructureJHolomorphic_neg_stdComplexLineConj.isConstStructureJHolomorphicAt
      x).isConstStructureJHolomorphicWithinAt hst

/-- Precomposing a within-set constant-structure `J`-holomorphic map whose source has the negated
standard structure by standard-line conjugation restores the standard source structure, provided
reflection maps the reflected source set into the original one. -/
lemma comp_neg_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicWithinAt (-(AlmostComplexStructure.product ℝ)) J f t
      (stdComplexLineConjCLM x)) (hst : Set.MapsTo stdComplexLineConjCLM s t) :
    IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J
      (fun z => f (stdComplexLineConjCLM z)) s x :=
  hf.comp
    (isConstStructureJHolomorphic_stdComplexLineConj.isConstStructureJHolomorphicAt
      x).isConstStructureJHolomorphicWithinAt hst

end IsConstStructureJHolomorphicWithinAt

namespace IsConstStructureJHolomorphicOn

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {f : ℝ × ℝ → W} {s t : Set (ℝ × ℝ)}

/-- Precomposing a setwise constant-structure `J`-holomorphic map by standard-line conjugation
changes the source structure from the standard one to its negation, provided reflection maps the
reflected source set into the original one. -/
lemma comp_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicOn (AlmostComplexStructure.product ℝ) J f t)
    (hst : Set.MapsTo stdComplexLineConjCLM s t) :
    IsConstStructureJHolomorphicOn (-(AlmostComplexStructure.product ℝ)) J
      (fun z => f (stdComplexLineConjCLM z)) s :=
  hf.comp (isConstStructureJHolomorphic_neg_stdComplexLineConj.isConstStructureJHolomorphicOn s) hst

/-- Precomposing a setwise constant-structure `J`-holomorphic map whose source has the negated
standard structure by standard-line conjugation restores the standard source structure, provided
reflection maps the reflected source set into the original one. -/
lemma comp_neg_stdComplexLineConj
    (hf : IsConstStructureJHolomorphicOn (-(AlmostComplexStructure.product ℝ)) J f t)
    (hst : Set.MapsTo stdComplexLineConjCLM s t) :
    IsConstStructureJHolomorphicOn (AlmostComplexStructure.product ℝ) J
      (fun z => f (stdComplexLineConjCLM z)) s :=
  hf.comp (isConstStructureJHolomorphic_stdComplexLineConj.isConstStructureJHolomorphicOn s) hst

end IsConstStructureJHolomorphicOn

end TauCeti
