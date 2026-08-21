/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# The ambient-isotopy equivalence relation

Building on `TauCeti.AmbientIsotopy` (an ambient isotopy of a space `Y`: a homotopy from the
identity whose level-preserving total map `I × Y → I × Y` is a homeomorphism), this file makes
ambient isotopy a relation between maps and shows it is an equivalence relation. Two maps
`f g : C(X, Y)` are **ambient isotopic** when some ambient isotopy `Φ` of `Y` carries `f` to `g`,
meaning its final homeomorphism postcomposes `f` to `g`. This is the continuous topological
relation the geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology`, encoding conventions)
intends to specialise to smooth embeddings `S¹ ↪ M` to underlie knot equivalence: "isotopy is
defined generally, then specialised".

The reflexivity, symmetry, and transitivity of the relation are powered by three closure
operations on ambient isotopies themselves, which live beside the `AmbientIsotopy` structure in
`TauCeti.Topology.Homotopy.Isotopy.Basic`: the constant ambient isotopy `AmbientIsotopy.refl`, the
pointwise composition `AmbientIsotopy.trans`, and the pointwise inverse `AmbientIsotopy.symm`.
Because each of their total maps is a composition or inverse of homeomorphisms, none of the
closure operations needs a separate gluing argument. This is a continuous topological
generalization of the point-set ambient-isotopy condition in Burde--Zieschang, *Knots*, Chapter 1,
Definition 1.2, intended for later specialization to embeddings such as knots.

## Main definitions

* `TauCeti.AmbientIsotopic f g`: the proposition that some ambient isotopy of `Y` carries `f` to
  `g`.
* `TauCeti.AmbientIsotopic.setoid`: the equivalence relation packaged as a `Setoid`.

## Main results

* `TauCeti.AmbientIsotopic.refl` / `symm` / `trans` and `TauCeti.AmbientIsotopic.equivalence`:
  ambient isotopy is an equivalence relation on `C(X, Y)`.
* `TauCeti.AmbientIsotopic.isotopic`: ambient isotopic embeddings are isotopic, specialising the
  ambient relation to the general isotopy relation of `Isotopy.lean`.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two maps `f g : C(X, Y)` are **ambient isotopic** if some ambient isotopy of the codomain `Y`
carries `f` to `g`, that is, its final homeomorphism postcomposes `f` to `g`. This is the
continuous topological ambient-isotopy relation intended to underlie later knot-equivalence
specialisations (ambient isotopy of smooth embeddings `S¹ ↪ M`); it does not itself encode the
smooth or PL structure those specialisations add. -/
def AmbientIsotopic (f g : C(X, Y)) : Prop :=
  ∃ Φ : AmbientIsotopy Y, Φ.final.comp f = g

/-- `f` and `g` are ambient isotopic exactly when some ambient isotopy's final homeomorphism
postcomposes `f` to `g`; this restates the definition without unfolding it. -/
theorem ambientIsotopic_def {f g : C(X, Y)} :
    AmbientIsotopic f g ↔ ∃ Φ : AmbientIsotopy Y, Φ.final.comp f = g := Iff.rfl

namespace AmbientIsotopic

variable {f g h : C(X, Y)}

/-- An ambient isotopy carrying `f` to `g` witnesses that `f` and `g` are ambient isotopic. -/
theorem of_ambientIsotopy (Φ : AmbientIsotopy Y) {f : C(X, Y)} :
    AmbientIsotopic f (Φ.final.comp f) := ⟨Φ, rfl⟩

/-- Ambient isotopy is reflexive: the constant ambient isotopy fixes every map. -/
@[refl]
theorem refl (f : C(X, Y)) : AmbientIsotopic f f :=
  ⟨AmbientIsotopy.refl Y, by ext x; exact AmbientIsotopy.final_refl (f x)⟩

/-- Ambient isotopy is symmetric, via the inverse ambient isotopy. -/
@[symm]
theorem symm (hfg : AmbientIsotopic f g) : AmbientIsotopic g f := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact ⟨Φ.symm, by ext x; exact Φ.symm_final_final (f x)⟩

/-- Ambient isotopy is transitive, via the composite ambient isotopy. -/
@[trans]
theorem trans (hfg : AmbientIsotopic f g) (hgh : AmbientIsotopic g h) : AmbientIsotopic f h := by
  obtain ⟨Φ, rfl⟩ := hfg
  obtain ⟨Ψ, rfl⟩ := hgh
  exact ⟨Φ.trans Ψ, by ext x; exact Φ.final_trans Ψ (f x)⟩

/-- Ambient isotopic embeddings are isotopic: this specialises the ambient relation to the general
isotopy relation, the "ambient isotopy implies isotopy" direction at the level of maps. -/
theorem isotopic (hfg : AmbientIsotopic f g) (hf : IsEmbedding f) : Isotopic f g := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact Φ.isotopic hf

/-- Ambient isotopy is an equivalence relation on `C(X, Y)`. -/
theorem equivalence : Equivalence (AmbientIsotopic (X := X) (Y := Y)) :=
  ⟨refl, fun hfg => hfg.symm, fun hfg hgh => hfg.trans hgh⟩

/-- The ambient-isotopy equivalence relation on `C(X, Y)`, packaged as a `Setoid`. -/
def setoid (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid (C(X, Y)) where
  r := AmbientIsotopic
  iseqv := equivalence

@[simp]
theorem setoid_r_iff {f g : C(X, Y)} : (setoid X Y).r f g ↔ AmbientIsotopic f g := Iff.rfl

end AmbientIsotopic

end TauCeti
