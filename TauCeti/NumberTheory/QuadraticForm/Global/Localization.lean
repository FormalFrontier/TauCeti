/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Localization of quadratic forms over number fields

This file defines scalar extension of a quadratic form from a number field to its canonical
finite completions and to the real or complex field selected by an infinite place.  The
definitions use `QuadraticForm.baseChange`; in particular, their underlying spaces are genuine
tensor products over the global field rather than independently chosen local spaces.

The evaluation and algebraic-compatibility lemmas make the local forms usable without unfolding
the localization definitions.  They are the common input for local isotropy, representation,
and invariant comparisons over number fields.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped TensorProduct

namespace TauCeti.NumberField.QuadraticForm

universe u v

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar extension of `V` to the finite completion of `K` at `v`. -/
abbrev FiniteScalarExtension (v : HeightOneSpectrum (𝓞 K)) := v.adicCompletion K ⊗[K] V

/-- The scalar extension of `V` to `ℝ` through the embedding belonging to a real place. -/
abbrev RealScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :=
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  ℝ ⊗[K] V

/-- The scalar extension of `V` to `ℂ` through the chosen embedding of an infinite place. -/
abbrev ComplexScalarExtension (w : InfinitePlace K) :=
  letI : Algebra K ℂ := w.embedding.toAlgebra
  ℂ ⊗[K] V

/-- The localization of a quadratic form at a finite place of a number field. -/
def atFinitePlace (Q : _root_.QuadraticForm K V) (v : HeightOneSpectrum (𝓞 K)) :
    _root_.QuadraticForm (v.adicCompletion K) (FiniteScalarExtension (V := V) v) :=
  Q.baseChange (v.adicCompletion K)

/-- The localization of a quadratic form at a real place of a number field. -/
def atRealPlace (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    _root_.QuadraticForm ℝ (RealScalarExtension (V := V) w) := by
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact Q.baseChange ℝ

/-- The localization of a quadratic form at an infinite place using its chosen complex
embedding. -/
def atComplexPlace (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    _root_.QuadraticForm ℂ (ComplexScalarExtension (V := V) w) := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact Q.baseChange ℂ

section Evaluation

variable (Q : _root_.QuadraticForm K V)

/-- A finite localization evaluates on a pure tensor by applying the completion map to the
coefficient of the original form. -/
@[simp]
theorem atFinitePlace_tmul (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K) (x : V) :
    atFinitePlace Q v (a ⊗ₜ x) = algebraMap K (v.adicCompletion K) (Q x) * a ^ 2 := by
  simp [atFinitePlace, Algebra.smul_def, pow_two, mul_comm]

/-- A real localization evaluates on a pure tensor by applying the real embedding to the
coefficient of the original form. -/
@[simp]
theorem atRealPlace_tmul (w : {w : InfinitePlace K // w.IsReal}) (a : ℝ) (x : V) :
    let _ : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
    atRealPlace Q w (a ⊗ₜ x) = embedding_of_isReal w.2 (Q x) * a ^ 2 := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  simp [atRealPlace, Algebra.smul_def, RingHom.algebraMap_toAlgebra, pow_two, mul_comm]

/-- A complex localization evaluates on a pure tensor by applying the chosen complex embedding
to the coefficient of the original form. -/
@[simp]
theorem atComplexPlace_tmul (w : InfinitePlace K) (a : ℂ) (x : V) :
    let _ : Algebra K ℂ := w.embedding.toAlgebra
    atComplexPlace Q w (a ⊗ₜ x) = w.embedding (Q x) * a ^ 2 := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  simp [atComplexPlace, Algebra.smul_def, RingHom.algebraMap_toAlgebra, pow_two, mul_comm]

end Evaluation

section Operations

variable (v : HeightOneSpectrum (𝓞 K))

/-- Finite localization sends the zero form to the zero form. -/
@[simp]
theorem atFinitePlace_zero :
    atFinitePlace (0 : _root_.QuadraticForm K V) v = 0 :=
  TauCeti.QuadraticForm.baseChange_zero

/-- Finite localization commutes with addition of forms. -/
@[simp]
theorem atFinitePlace_add (Q Q' : _root_.QuadraticForm K V) :
    atFinitePlace (Q + Q') v = atFinitePlace Q v + atFinitePlace Q' v :=
  TauCeti.QuadraticForm.baseChange_add Q Q'

/-- Finite localization commutes with negation of forms. -/
@[simp]
theorem atFinitePlace_neg (Q : _root_.QuadraticForm K V) :
    atFinitePlace (-Q) v = -(atFinitePlace Q v) :=
  TauCeti.QuadraticForm.baseChange_neg Q

/-- Finite localization commutes with subtraction of forms. -/
@[simp]
theorem atFinitePlace_sub (Q Q' : _root_.QuadraticForm K V) :
    atFinitePlace (Q - Q') v = atFinitePlace Q v - atFinitePlace Q' v :=
  TauCeti.QuadraticForm.baseChange_sub Q Q'

/-- Scaling before finite localization agrees with scaling by the image in the completion. -/
@[simp]
theorem atFinitePlace_smul (r : K) (Q : _root_.QuadraticForm K V) :
    atFinitePlace (r • Q) v =
      algebraMap K (v.adicCompletion K) r • atFinitePlace Q v :=
  TauCeti.QuadraticForm.baseChange_smul r Q

/-- Real localization sends the zero form to the zero form. -/
@[simp]
theorem atRealPlace_zero (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (0 : _root_.QuadraticForm K V) w = 0 := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChange_zero

/-- Real localization commutes with addition of forms. -/
@[simp]
theorem atRealPlace_add (Q Q' : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (Q + Q') w = atRealPlace Q w + atRealPlace Q' w := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChange_add Q Q'

/-- Real localization commutes with negation of forms. -/
@[simp]
theorem atRealPlace_neg (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (-Q) w = -(atRealPlace Q w) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChange_neg Q

/-- Real localization commutes with subtraction of forms. -/
@[simp]
theorem atRealPlace_sub (Q Q' : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (Q - Q') w = atRealPlace Q w - atRealPlace Q' w := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChange_sub Q Q'

/-- Scaling before real localization agrees with scaling by the corresponding real embedding. -/
@[simp]
theorem atRealPlace_smul (r : K) (Q : _root_.QuadraticForm K V)
    (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace (r • Q) w = embedding_of_isReal w.2 r • atRealPlace Q w := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChange_smul r Q

/-- Complex localization sends the zero form to the zero form. -/
@[simp]
theorem atComplexPlace_zero (w : InfinitePlace K) :
    atComplexPlace (0 : _root_.QuadraticForm K V) w = 0 := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChange_zero

/-- Complex localization commutes with addition of forms. -/
@[simp]
theorem atComplexPlace_add (Q Q' : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexPlace (Q + Q') w = atComplexPlace Q w + atComplexPlace Q' w := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChange_add Q Q'

/-- Complex localization commutes with negation of forms. -/
@[simp]
theorem atComplexPlace_neg (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexPlace (-Q) w = -(atComplexPlace Q w) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChange_neg Q

/-- Complex localization commutes with subtraction of forms. -/
@[simp]
theorem atComplexPlace_sub (Q Q' : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexPlace (Q - Q') w = atComplexPlace Q w - atComplexPlace Q' w := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChange_sub Q Q'

/-- Scaling before complex localization agrees with scaling by the chosen complex embedding. -/
@[simp]
theorem atComplexPlace_smul (r : K) (Q : _root_.QuadraticForm K V) (w : InfinitePlace K) :
    atComplexPlace (r • Q) w = w.embedding r • atComplexPlace Q w := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChange_smul r Q

end Operations

section Isometries

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}

/-- An isometry of global quadratic forms extends to every finite localization. -/
def Isometry.atFinitePlace (f : Q →qᵢ R) (v : HeightOneSpectrum (𝓞 K)) :
    atFinitePlace Q v →qᵢ atFinitePlace R v :=
  TauCeti.QuadraticForm.Isometry.baseChange f (v.adicCompletion K)

/-- An isometry of global quadratic forms extends to every real localization. -/
def Isometry.atRealPlace (f : Q →qᵢ R) (w : {w : InfinitePlace K // w.IsReal}) :
    atRealPlace Q w →qᵢ atRealPlace R w := by
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.Isometry.baseChange f ℝ

/-- An isometry of global quadratic forms extends to every complex localization. -/
def Isometry.atComplexPlace (f : Q →qᵢ R) (w : InfinitePlace K) :
    atComplexPlace Q w →qᵢ atComplexPlace R w := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.Isometry.baseChange f ℂ

/-- A global isometric equivalence extends to every finite localization. -/
def IsometryEquiv.atFinitePlace (f : Q.IsometryEquiv R)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace Q v).IsometryEquiv (atFinitePlace R v) :=
  TauCeti.QuadraticForm.IsometryEquiv.baseChange f (v.adicCompletion K)

/-- A global isometric equivalence extends to every real localization. -/
def IsometryEquiv.atRealPlace (f : Q.IsometryEquiv R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace Q w).IsometryEquiv (atRealPlace R w) := by
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.IsometryEquiv.baseChange f ℝ

/-- A global isometric equivalence extends to every complex localization. -/
def IsometryEquiv.atComplexPlace (f : Q.IsometryEquiv R) (w : InfinitePlace K) :
    (atComplexPlace Q w).IsometryEquiv (atComplexPlace R w) := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.IsometryEquiv.baseChange f ℂ

/-- Equivalent global quadratic forms remain equivalent at every finite place. -/
theorem Equivalent.atFinitePlace (h : Q.Equivalent R) (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace Q v).Equivalent (atFinitePlace R v) :=
  TauCeti.QuadraticForm.Equivalent.baseChange h (v.adicCompletion K)

/-- Equivalent global quadratic forms remain equivalent at every real place. -/
theorem Equivalent.atRealPlace (h : Q.Equivalent R)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace Q w).Equivalent (atRealPlace R w) := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.Equivalent.baseChange h ℝ

/-- Equivalent global quadratic forms remain equivalent at every complex place. -/
theorem Equivalent.atComplexPlace (h : Q.Equivalent R) (w : InfinitePlace K) :
    (atComplexPlace Q w).Equivalent (atComplexPlace R w) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.Equivalent.baseChange h ℂ

/-- The finite localization of an orthogonal sum is canonically isometric to the orthogonal sum
of the finite localizations. -/
def prodAtFinitePlace (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace (Q.prod R) v).IsometryEquiv
      ((atFinitePlace Q v).prod (atFinitePlace R v)) :=
  TauCeti.QuadraticForm.baseChangeProd Q R

/-- The real localization of an orthogonal sum is canonically isometric to the orthogonal sum of
the real localizations. -/
def prodAtRealPlace (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace (Q.prod R) w).IsometryEquiv
      ((atRealPlace Q w).prod (atRealPlace R w)) := by
  letI : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.baseChangeProd Q R

/-- The complex localization of an orthogonal sum is canonically isometric to the orthogonal sum
of the complex localizations. -/
def prodAtComplexPlace (Q : _root_.QuadraticForm K V) (R : _root_.QuadraticForm K W)
    (w : InfinitePlace K) :
    (atComplexPlace (Q.prod R) w).IsometryEquiv
      ((atComplexPlace Q w).prod (atComplexPlace R w)) := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.baseChangeProd Q R

end Isometries

section FiniteDimensional

variable {Q : _root_.QuadraticForm K V}

/-- Finite localization preserves the rank of a quadratic space. -/
@[simp]
theorem finrank_finiteScalarExtension (v : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (v.adicCompletion K) (FiniteScalarExtension (V := V) v) =
      Module.finrank K V :=
  Module.finrank_baseChange

omit [NumberField K] in
/-- Real localization preserves the rank of a quadratic space. -/
@[simp]
theorem finrank_realScalarExtension (w : {w : InfinitePlace K // w.IsReal}) :
    Module.finrank ℝ (RealScalarExtension (V := V) w) = Module.finrank K V := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact Module.finrank_baseChange

omit [NumberField K] in
/-- Complex localization preserves the rank of a quadratic space. -/
@[simp]
theorem finrank_complexScalarExtension (w : InfinitePlace K) :
    Module.finrank ℂ (ComplexScalarExtension (V := V) w) = Module.finrank K V := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact Module.finrank_baseChange

/-- A regular quadratic form stays regular at every finite place. -/
theorem Nondegenerate.atFinitePlace [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) : (atFinitePlace Q v).Nondegenerate := by
  have htwoK : (2 : K) ≠ 0 := by norm_num
  have htwo : (2 : v.adicCompletion K) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero_iff (algebraMap K (v.adicCompletion K)) (RingHom.injective _)).mpr
        htwoK
  let : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero htwo
  exact TauCeti.QuadraticForm.Nondegenerate.baseChange hQ

/-- A regular quadratic form stays regular at every real place. -/
theorem Nondegenerate.atRealPlace [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) : (atRealPlace Q w).Nondegenerate := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  exact TauCeti.QuadraticForm.Nondegenerate.baseChange hQ

/-- A regular quadratic form stays regular at every complex place. -/
theorem Nondegenerate.atComplexPlace [FiniteDimensional K V]
    (hQ : Q.Nondegenerate) (w : InfinitePlace K) :
    (atComplexPlace Q w).Nondegenerate := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  exact TauCeti.QuadraticForm.Nondegenerate.baseChange hQ

end FiniteDimensional

end TauCeti.NumberField.QuadraticForm
