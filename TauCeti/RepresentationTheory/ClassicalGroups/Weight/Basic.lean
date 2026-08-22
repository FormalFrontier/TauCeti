/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The diagonal torus `TauCeti.diagGL`, the standard representation and its action at a diagonal
-- matrix; this module also re-exports `Mathlib.RepresentationTheory.Character`, hence
-- `Representation`.
public import TauCeti.RepresentationTheory.ClassicalGroups.Torus
-- The determinant powers, the worked one-dimensional example at the end of the file.
public import TauCeti.RepresentationTheory.ClassicalGroups.Determinant
-- The characters `TauCeti.weightChar` of a split torus, and their injectivity in weight.
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
-- The independence of the joint eigenspaces of a representation, indexed by characters.
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Weights of the diagonal torus of the general linear group

A vector `w` of a representation `ρ` of `GL n k` has **weight** `l : Fin n → ℤ` when every
invertible diagonal matrix `diagGL t` scales it by `∏ i, tᵢ ^ lᵢ`. The vectors of weight `l` form
the **weight space** `TauCeti.weightSpace ρ l`, and this file builds that space and the two facts
that make weights a decomposition rather than a labelling: the weight spaces are independent, and
the standard representation is the internal direct sum of its weight spaces, which are its
coordinate lines.

The scalar `∏ i, tᵢ ^ lᵢ` is the split-torus character `TauCeti.weightChar k l`, built in
`TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic`. The weight space is an intersection of
eigenspaces, one for each point of the torus, so independence is that of the joint eigenspaces of a
representation indexed by characters — `TauCeti.iSupIndep_iInf_eigenspace_unitHom` — transported
along `l ↦ TauCeti.weightChar k l`. That transport needs the map to be injective, and that is
where the coefficients enter: over `𝔽₂` the torus is trivial
(`TauCeti.diagonalTorus_eq_bot`), every `l` gives the same character, and the whole module is a
weight space for every weight at once, so nothing is independent. Rather than fix the coefficients,
every statement below that separates weights takes `Function.Injective (weightChar k)` as a
hypothesis, and `TauCeti.weightChar_injective` discharges it over an infinite field.

The definitions themselves need only a commutative ring, and are stated there.

## Main definitions

* `TauCeti.weightSpace`: the space of vectors on which the diagonal torus acts through
  `TauCeti.weightChar`.

## Main results

* `TauCeti.iSupIndep_weightSpace`: **the weight spaces of a representation of `GL n k` are
  independent**, as soon as distinct weights give distinct characters.
* `TauCeti.weightSpace_stdRep_single` and `TauCeti.weightSpace_stdRep_eq_bot`: the weight spaces of
  the standard representation are exactly its coordinate lines, the line `k ∙ eᵢ` carrying the
  weight `Pi.single i 1` and every other weight space vanishing.
* `TauCeti.isInternal_weightSpace_of_iSup_eq_top`: **a representation whose weight spaces span it
  is their internal direct sum**, as soon as distinct weights give distinct characters.
* `TauCeti.isInternal_weightSpace_stdRep`: **the standard representation is the internal direct sum
  of its weight spaces.**
* `TauCeti.weightSpace_detPowerRep`: all of `det ^ m` has the constant weight `m`, that is, its
  weight space at the constant sequence `m` is `⊤`. Over a general commutative ring this says
  nothing about the other weight spaces — over `𝔽₂` all of them are `⊤` as well.

## Implementation notes

The weight space is indexed by `l : Fin n → ℤ`, not by a character of the torus, because that is
the index the highest-weight theory of the roadmap runs on; `TauCeti.weightChar` is the translation
between the two, and the separation hypothesis says the translation is faithful.

The intersection defining `TauCeti.weightSpace` runs over `t : Fin n → kˣ` rather than over
`TauCeti.diagonalTorus k n` itself: `TauCeti.diagGL` is onto the torus
(`TauCeti.mem_diagonalTorus_iff_exists_diagGL`), so the two conditions agree, and the
coordinatewise form is the one every computation below uses.

Weight spaces are intersections of honest eigenspaces, not of generalised ones: a torus element
acts on a weight vector by an honest scalar, and independence is available in that form already.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u v

namespace TauCeti

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module k W]

/-! ## The weight spaces of a representation -/

/-- The **weight space** of weight `l : Fin n → ℤ`: the vectors that every invertible diagonal
matrix `diagGL t` scales by `∏ i, tᵢ ^ lᵢ`. -/
def weightSpace (ρ : Representation k (GL (Fin n) k) W) (l : Fin n → ℤ) : Submodule k W :=
  ⨅ t : Fin n → kˣ, Module.End.eigenspace (ρ (diagGL t)) ((weightChar k l t : kˣ) : k)

/-- Membership in a weight space is the eigen-relation at every point of the torus. -/
@[simp]
theorem mem_weightSpace_iff (ρ : Representation k (GL (Fin n) k) W) (l : Fin n → ℤ) (w : W) :
    w ∈ weightSpace ρ l ↔
      ∀ t : Fin n → kˣ, ρ (diagGL t) w = ((weightChar k l t : kˣ) : k) • w := by
  simp [weightSpace]

/-- A weight vector is an eigenvector for each individual point of the torus. -/
theorem weightSpace_le_eigenspace (ρ : Representation k (GL (Fin n) k) W) (l : Fin n → ℤ)
    (t : Fin n → kˣ) :
    weightSpace ρ l ≤ Module.End.eigenspace (ρ (diagGL t)) ((weightChar k l t : kˣ) : k) :=
  iInf_le _ t

/-- The action of a torus element on a weight vector. -/
theorem apply_of_mem_weightSpace {ρ : Representation k (GL (Fin n) k) W} {l : Fin n → ℤ} {w : W}
    (hw : w ∈ weightSpace ρ l) (t : Fin n → kˣ) :
    ρ (diagGL t) w = ((weightChar k l t : kˣ) : k) • w :=
  (mem_weightSpace_iff ρ l w).mp hw t

/-! ## The standard representation and the determinant powers -/

/-- The `i`-th standard basis vector has weight `Pi.single i 1`: a diagonal matrix scales it by its
`i`-th entry. -/
theorem basisFun_mem_weightSpace_stdRep (i : Fin n) :
    Pi.basisFun k (Fin n) i ∈ weightSpace (stdRep k n) (Pi.single i 1) := by
  rw [mem_weightSpace_iff]
  intro t
  rw [stdRep_diagGL_apply_basisFun, weightChar_single]

/-- The coordinate line `k ∙ eᵢ` consists of vectors of weight `Pi.single i 1`. -/
theorem span_basisFun_le_weightSpace_stdRep (i : Fin n) :
    Submodule.span k {Pi.basisFun k (Fin n) i} ≤ weightSpace (stdRep k n) (Pi.single i 1) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact basisFun_mem_weightSpace_stdRep i

/-- The weight spaces of the standard representation span it, being its coordinate lines. -/
theorem iSup_weightSpace_stdRep_eq_top :
    ⨆ l : Fin n → ℤ, weightSpace (stdRep k n) l = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact le_iSup (fun l : Fin n → ℤ ↦ weightSpace (stdRep k n) l) (Pi.single i 1)
    (basisFun_mem_weightSpace_stdRep i)

/-- **All of `det ^ m` has weight the constant sequence `m`**: a diagonal matrix acts on it by the
`m`-th power of the product of its entries. Over a commutative ring this leaves the other weight
spaces of `det ^ m` unconstrained — over `𝔽₂` the torus is trivial, so every one of them is `⊤`
too. -/
@[simp]
theorem weightSpace_detPowerRep (m : ℤ) :
    weightSpace (detPowerRep k n m) (fun _ ↦ m) = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  rw [mem_weightSpace_iff]
  intro t
  rw [detPowerRep_apply, weightChar_const, smul_eq_mul, det_diagGL]

end CommRing

/-! ## The weight spaces of the standard representation

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section Domain

variable {k : Type u} [CommRing k] [IsDomain k] {n : ℕ}

/-- **A nonzero coordinate pins the weight.** If a vector of weight `l` in the standard
representation has a nonzero `j`-th coordinate then `l = Pi.single j 1`. -/
theorem eq_single_of_mem_weightSpace_stdRep
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ} {w : Fin n → k}
    (hw : w ∈ weightSpace (stdRep k n) l) {j : Fin n} (hj : w j ≠ 0) :
    l = Pi.single j 1 := by
  refine hchar (MonoidHom.ext fun t ↦ ?_)
  have h := congrFun (apply_of_mem_weightSpace hw t) j
  rw [stdRep_diagGL_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [weightChar_single]
  exact Units.ext (mul_right_cancel₀ hj h).symm

/-- Off the weights `Pi.single i 1` the standard representation has no weight vectors. -/
theorem weightSpace_stdRep_eq_bot (hchar : Function.Injective (weightChar k (κ := Fin n)))
    {l : Fin n → ℤ} (hl : ∀ i : Fin n, l ≠ Pi.single i 1) :
    weightSpace (stdRep k n) l = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun w hw ↦ funext fun j ↦ ?_
  by_contra hj
  exact hl j (eq_single_of_mem_weightSpace_stdRep hchar hw hj)

/-- **The weight spaces of the standard representation are its coordinate lines.** -/
theorem weightSpace_stdRep_single (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (i : Fin n) :
    weightSpace (stdRep k n) (Pi.single i 1) = Submodule.span k {Pi.basisFun k (Fin n) i} := by
  refine le_antisymm (fun w hw ↦ ?_) (span_basisFun_le_weightSpace_stdRep i)
  rw [Submodule.mem_span_singleton]
  refine ⟨w i, funext fun j ↦ ?_⟩
  by_cases hji : j = i
  · subst hji
    simp
  · have hzero : w j = 0 := by
      by_contra hj
      have hsingle := eq_single_of_mem_weightSpace_stdRep hchar hw hj
      have hone : (Pi.single i 1 : Fin n → ℤ) j = 1 := by rw [hsingle, Pi.single_eq_same]
      rw [Pi.single_eq_of_ne hji] at hone
      exact one_ne_zero hone.symm
    simp [hzero, Pi.basisFun_apply, hji]

end Domain

section Field

variable {k : Type u} [Field k] {n : ℕ}
variable {W : Type v} [AddCommGroup W] [Module k W]

/-- **The weight spaces of a representation of `GL n k` are independent**, as soon as distinct
weights give distinct characters of the torus. The weight spaces are the joint eigenspaces of the
representation `t ↦ ρ (diagGL t)` of the torus indexed by the characters `weightChar k l`, and
those are independent; the hypothesis makes the weight recoverable from its character, so indexing
by weights keeps them distinct. -/
theorem iSupIndep_weightSpace (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (ρ : Representation k (GL (Fin n) k) W) :
    iSupIndep fun l : Fin n → ℤ ↦ weightSpace ρ l :=
  (iSupIndep_iInf_eigenspace_unitHom
      (ρ := (ρ : GL (Fin n) k →* Module.End k W).comp diagGL)).comp hchar

/-- **Spanning is the whole of the weight-space decomposition.** Once distinct weights give
distinct characters, the weight spaces are independent for free, so a representation whose weight
spaces span it is their internal direct sum. -/
theorem isInternal_weightSpace_of_iSup_eq_top
    (hchar : Function.Injective (weightChar k (κ := Fin n)))
    {ρ : Representation k (GL (Fin n) k) W} (h : ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤) :
    DirectSum.IsInternal fun l : Fin n → ℤ ↦ weightSpace ρ l :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_weightSpace hchar _, h⟩

/-- **The standard representation is the internal direct sum of its weight spaces**: the
weight-space decomposition in its smallest instance. -/
theorem isInternal_weightSpace_stdRep (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ ↦ weightSpace (stdRep k n) l :=
  isInternal_weightSpace_of_iSup_eq_top hchar iSup_weightSpace_stdRep_eq_top

end Field

end TauCeti
