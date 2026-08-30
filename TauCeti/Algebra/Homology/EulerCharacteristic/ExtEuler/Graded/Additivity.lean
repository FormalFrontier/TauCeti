/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Additivity of the graded Ext-Euler characteristic

The graded Ext-Euler characteristic is additive on short exact sequences in either variable.
The proof reads each Laurent coefficient as an ordinary Ext-Euler characteristic: the coefficient
of `q^j` is the Euler characteristic against the target shifted by `-j`.  Ordinary Ext-Euler
additivity then applies, after mapping a short exact sequence through the grading shift when the
sequence occurs in the second variable.

This file also proves that the separate internal-finiteness and uniform cohomological-boundedness
conditions are closed under extensions.  In particular, the middle term of a short exact sequence
is graded Euler-admissible whenever both outer terms are.

## Main results

* `TauCeti.IsGradedEulerAdmissible.of_shortExact₂` and
  `TauCeti.IsGradedEulerAdmissible.of_shortExact₂'`: closure under extensions in the second and
  first variables.
* `TauCeti.coeff_gradedExtEuler_eq_extEuler`: a Laurent coefficient is an ordinary Ext-Euler
  characteristic against one shifted target.
* `TauCeti.gradedExtEuler_shortExact₂` and `TauCeti.gradedExtEuler_shortExact₁`: additivity on
  short exact sequences in either variable.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for the long
  exact Ext sequences underlying ordinary Euler additivity.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2, for the
  Laurent-polynomial-valued Ext-Euler form.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 5, "Graded Ext and graded descent".
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C}

/-! ### Passage to one internal degree -/

/-- Finite internal support gives ordinary Ext-finiteness against every fixed target shift. -/
theorem IsGradedExtInternallyFinite.isExtFinite {X Y : C}
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (j : ℤ) :
    IsExtFinite.{w} k X ((e ^ j).functor.obj Y) :=
  ⟨fun n ↦ (h.finiteLaurentSupport n).finiteDimensional j⟩

/-- A uniform graded Ext bound gives the same ordinary Ext bound against every fixed target
shift. -/
theorem IsGradedExtBoundedBy.isExtBoundedBy {X Y : C} {N : ℕ}
    (h : IsGradedExtBoundedBy.{w} e X Y N) (j : ℤ) :
    IsExtBoundedBy.{w} X ((e ^ j).functor.obj Y) N :=
  ⟨fun _ hn ↦ h.subsingleton hn j⟩

/-- A graded Euler-admissible pair is ordinarily Euler-admissible against each fixed target
shift. -/
theorem IsGradedEulerAdmissible.isEulerAdmissible {X Y : C}
    (h : IsGradedEulerAdmissible.{w} k e X Y) (j : ℤ) :
    IsEulerAdmissible.{w} k X ((e ^ j).functor.obj Y) :=
  ⟨h.internallyFinite.isExtFinite j,
    ⟨h.bounded.exists_bound.choose,
      h.bounded.exists_bound.choose_spec.isExtBoundedBy j⟩⟩

/-! ### Closure under extensions -/

variable {S : ShortComplex C}

/-- Finite internal support is closed under extensions in the second variable. -/
theorem IsGradedExtInternallyFinite.of_shortExact₂ (hS : S.ShortExact) {X : C}
    (h₁ : IsGradedExtInternallyFinite.{w} k e X S.X₁)
    (h₃ : IsGradedExtInternallyFinite.{w} k e X S.X₃) :
    IsGradedExtInternallyFinite.{w} k e X S.X₂ :=
  ⟨fun n ↦ (h₁.finiteLaurentSupport n).of_exact (h₃.finiteLaurentSupport n)
    (fun j ↦ Ext.postcompOfLinear (Ext.mk₀ ((e ^ j).functor.map S.f)) k X (add_zero n))
    (fun j ↦ Ext.postcompOfLinear (Ext.mk₀ ((e ^ j).functor.map S.g)) k X (add_zero n))
    (fun j ↦ exact_postcompOfLinear k (hS.map_of_exact (e ^ j).functor) X n)⟩

/-- Finite internal support is closed under extensions in the first variable. -/
theorem IsGradedExtInternallyFinite.of_shortExact₂' (hS : S.ShortExact) {Y : C}
    (h₁ : IsGradedExtInternallyFinite.{w} k e S.X₁ Y)
    (h₃ : IsGradedExtInternallyFinite.{w} k e S.X₃ Y) :
    IsGradedExtInternallyFinite.{w} k e S.X₂ Y :=
  ⟨fun n ↦ (h₃.finiteLaurentSupport n).of_exact (h₁.finiteLaurentSupport n)
    (fun j ↦ Ext.precompOfLinear (Ext.mk₀ S.g) k ((e ^ j).functor.obj Y) (zero_add n))
    (fun j ↦ Ext.precompOfLinear (Ext.mk₀ S.f) k ((e ^ j).functor.obj Y) (zero_add n))
    (fun j ↦ exact_precompOfLinear k hS ((e ^ j).functor.obj Y) n)⟩

/-- A uniform graded Ext bound is closed under extensions in the second variable. -/
theorem IsGradedExtBoundedBy.of_shortExact₂ (hS : S.ShortExact) {X : C} {N₁ N₃ : ℕ}
    (h₁ : IsGradedExtBoundedBy.{w} e X S.X₁ N₁)
    (h₃ : IsGradedExtBoundedBy.{w} e X S.X₃ N₃) :
    IsGradedExtBoundedBy.{w} e X S.X₂ (max N₁ N₃) :=
  ⟨fun _n hn j ↦
    ((h₁.isExtBoundedBy j).of_shortExact₂ (hS.map_of_exact (e ^ j).functor)
      (h₃.isExtBoundedBy j)).subsingleton hn⟩

/-- A uniform graded Ext bound is closed under extensions in the first variable. -/
theorem IsGradedExtBoundedBy.of_shortExact₂' (hS : S.ShortExact) {Y : C} {N₁ N₃ : ℕ}
    (h₁ : IsGradedExtBoundedBy.{w} e S.X₁ Y N₁)
    (h₃ : IsGradedExtBoundedBy.{w} e S.X₃ Y N₃) :
    IsGradedExtBoundedBy.{w} e S.X₂ Y (max N₁ N₃) :=
  ⟨fun _n hn j ↦
    ((h₁.isExtBoundedBy j).of_shortExact₂' hS
      (h₃.isExtBoundedBy j)).subsingleton hn⟩

/-- Graded Euler-admissibility is closed under extensions in the second variable. -/
theorem IsGradedEulerAdmissible.of_shortExact₂ (hS : S.ShortExact) {X : C}
    (h₁ : IsGradedEulerAdmissible.{w} k e X S.X₁)
    (h₃ : IsGradedEulerAdmissible.{w} k e X S.X₃) :
    IsGradedEulerAdmissible.{w} k e X S.X₂ := by
  obtain ⟨N₁, hN₁⟩ := h₁.bounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.bounded.exists_bound
  exact ⟨h₁.internallyFinite.of_shortExact₂ hS h₃.internallyFinite,
    (hN₁.of_shortExact₂ hS hN₃).isGradedExtBounded⟩

/-- Graded Euler-admissibility is closed under extensions in the first variable. -/
theorem IsGradedEulerAdmissible.of_shortExact₂' (hS : S.ShortExact) {Y : C}
    (h₁ : IsGradedEulerAdmissible.{w} k e S.X₁ Y)
    (h₃ : IsGradedEulerAdmissible.{w} k e S.X₃ Y) :
    IsGradedEulerAdmissible.{w} k e S.X₂ Y := by
  obtain ⟨N₁, hN₁⟩ := h₁.bounded.exists_bound
  obtain ⟨N₃, hN₃⟩ := h₃.bounded.exists_bound
  exact ⟨h₁.internallyFinite.of_shortExact₂' hS h₃.internallyFinite,
    (hN₁.of_shortExact₂' hS hN₃).isGradedExtBounded⟩

/-! ### Coefficients and additivity -/

/-- The coefficient of `q^j` in the graded Ext-Euler characteristic is the ordinary Ext-Euler
characteristic against the target shifted by `-j`. -/
theorem coeff_gradedExtEuler_eq_extEuler {X Y : C}
    (h : IsGradedEulerAdmissible.{w} k e X Y) (j : ℤ) :
    (gradedExtEuler k e h).coeff j = extEuler.{w} k (h.isEulerAdmissible (-j)) := by
  obtain ⟨N, hN⟩ := h.bounded.exists_bound
  rw [coeff_gradedExtEuler k e h hN j,
    extEuler_eq k (h.isEulerAdmissible (-j)) (hN.isExtBoundedBy (-j))]
  have htrunc : ∀ M : ℕ,
      (∑ n ∈ Finset.range M,
        (-1 : ℤ) ^ n * (Module.finrank k (GradedExt.{w} e X Y n (-j)) : ℤ)) =
        truncatedExtEuler.{w} k X ((e ^ (-j)).functor.obj Y) M := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, truncatedExtEuler_succ, ih]
  exact htrunc N

/-- The graded Ext-Euler characteristic is additive on a short exact sequence in its second
variable. -/
theorem gradedExtEuler_shortExact₂ (hS : S.ShortExact) (X : C)
    (h₁ : IsGradedEulerAdmissible.{w} k e X S.X₁)
    (h₃ : IsGradedEulerAdmissible.{w} k e X S.X₃) :
    gradedExtEuler k e (h₁.of_shortExact₂ hS h₃) =
      gradedExtEuler k e h₁ + gradedExtEuler k e h₃ := by
  ext j
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_gradedExtEuler_eq_extEuler h₁,
    coeff_gradedExtEuler_eq_extEuler (h₁.of_shortExact₂ hS h₃),
    coeff_gradedExtEuler_eq_extEuler h₃]
  exact extEuler_shortExact₂ (hS.map_of_exact (e ^ (-j)).functor) X
    (h₁.isEulerAdmissible (-j)) ((h₁.of_shortExact₂ hS h₃).isEulerAdmissible (-j))
    (h₃.isEulerAdmissible (-j))

/-- The graded Ext-Euler characteristic is additive on a short exact sequence in its first
variable. -/
theorem gradedExtEuler_shortExact₁ (hS : S.ShortExact) (Y : C)
    (h₁ : IsGradedEulerAdmissible.{w} k e S.X₁ Y)
    (h₃ : IsGradedEulerAdmissible.{w} k e S.X₃ Y) :
    gradedExtEuler k e (h₁.of_shortExact₂' hS h₃) =
      gradedExtEuler k e h₁ + gradedExtEuler k e h₃ := by
  ext j
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_gradedExtEuler_eq_extEuler h₁,
    coeff_gradedExtEuler_eq_extEuler (h₁.of_shortExact₂' hS h₃),
    coeff_gradedExtEuler_eq_extEuler h₃]
  exact extEuler_shortExact₁ hS ((e ^ (-j)).functor.obj Y)
    (h₁.isEulerAdmissible (-j)) ((h₁.of_shortExact₂' hS h₃).isEulerAdmissible (-j))
    (h₃.isEulerAdmissible (-j))

end TauCeti
