/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.weightChar`, the characters of the split torus, and `TauCeti.weightChar_injective`.
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus
-- The `Subalgebra` structure the span of the characters is upgraded to.
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
-- Non-public: Artin's independence of characters, used only inside the proof of
-- `TauCeti.linearIndependent_weightCharHom`.
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Laurent functions on a split torus

The characters of the split torus `𝔾ₘ^κ` span a subalgebra of the `R`-valued functions on its
points, the **Laurent functions** `TauCeti.laurentFunctions R κ`: over a field these are exactly
the functions given by a Laurent polynomial in the coordinates. This file builds that subalgebra
and proves that the characters spanning it are linearly independent.

Independence is what makes the construction useful. Distinct characters of a monoid with values in
a domain are linearly independent (Artin), so `TauCeti.linearIndependent_weightCharHom` turns an
identity between two Laurent expansions into an identity between their coefficients. This is the
mechanism by which a weight is read off an expansion, and it is why the weight spaces of a
rational representation of `GL n k` are what they are; the restriction of a rational function to
the diagonal torus, which is where that argument starts, is in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LaurentFunctions`.

The value ring is a commutative ring throughout, except where separating characters forces an
infinite field: over `𝔽₂` the torus has a single point and all characters coincide.

## Main definitions

* `TauCeti.weightCharHom`: a character of the split torus, with values read in `R` rather than in
  `Rˣ`.
* `TauCeti.laurentFunctions`: the subalgebra of functions on the torus spanned by the characters.

## Main results

* `TauCeti.linearIndependent_weightCharHom`: over an infinite field the characters of the split
  torus are linearly independent, so a Laurent expansion determines its coefficients.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

universe u v

namespace TauCeti

section WeightCharHom

variable (R : Type u) [CommRing R] {κ : Type v} [Fintype κ]

/-- A character of the split torus `𝔾ₘ^κ` with its values read in `R` rather than in `Rˣ`. This
is the form in which a character is a *function* on the torus, so that families of characters can
be asked to be linearly independent and their span can be taken. -/
def weightCharHom (μ : κ → ℤ) : (κ → Rˣ) →* R :=
  (Units.coeHom R).comp (weightChar R μ)

@[simp]
theorem weightCharHom_apply (μ : κ → ℤ) (s : κ → Rˣ) :
    weightCharHom R μ s = ((weightChar R μ s : Rˣ) : R) :=
  (rfl)

/-- The trivial character is the constant function `1`. -/
@[simp]
theorem coe_weightCharHom_zero : ⇑(weightCharHom R (0 : κ → ℤ)) = 1 := by
  funext s
  rw [weightCharHom_apply, weightChar_zero]
  simp

/-- Characters multiply as their weights add. -/
theorem coe_weightCharHom_add (μ ν : κ → ℤ) :
    ⇑(weightCharHom R (μ + ν)) = ⇑(weightCharHom R μ) * ⇑(weightCharHom R ν) := by
  funext s
  rw [Pi.mul_apply, weightCharHom_apply, weightCharHom_apply, weightCharHom_apply,
    weightChar_add]
  simp

/-- The character of `Pi.single c 1` is the `c`-th coordinate function. Not a `simp` lemma:
`TauCeti.weightCharHom_apply` and `TauCeti.weightChar_single` already reduce the left-hand side,
so tagging it would make it simp-redundant. -/
theorem weightCharHom_single [DecidableEq κ] (c : κ) (s : κ → Rˣ) :
    weightCharHom R (Pi.single c 1) s = (s c : R) := by
  rw [weightCharHom_apply, weightChar_single]

/-- The character of a constant weight is the corresponding power of the product of the
coordinates. -/
theorem weightCharHom_const (z : ℤ) (s : κ → Rˣ) :
    weightCharHom R (fun _ ↦ z) s = (((∏ j, s j) ^ z : Rˣ) : R) := by
  rw [weightCharHom_apply, weightChar_const]

variable (κ)

/-- The span of the characters, as a submodule; `TauCeti.laurentFunctions` upgrades it to a
subalgebra once the two closure lemmas below are available. -/
private def charSpan : Submodule R ((κ → Rˣ) → R) :=
  Submodule.span R (Set.range fun μ : κ → ℤ ↦ ⇑(weightCharHom R μ))

variable {κ}

private theorem coe_weightCharHom_mem_charSpan (μ : κ → ℤ) :
    ⇑(weightCharHom R μ) ∈ charSpan R κ :=
  Submodule.subset_span ⟨μ, rfl⟩

private theorem one_mem_charSpan : (1 : (κ → Rˣ) → R) ∈ charSpan R κ :=
  coe_weightCharHom_zero R (κ := κ) ▸ coe_weightCharHom_mem_charSpan R (0 : κ → ℤ)

private theorem mul_coe_weightCharHom_mem_charSpan (μ : κ → ℤ) {f : (κ → Rˣ) → R}
    (hf : f ∈ charSpan R κ) : ⇑(weightCharHom R μ) * f ∈ charSpan R κ := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨ν, rfl⟩ := h
    exact (coe_weightCharHom_add R μ ν) ▸ coe_weightCharHom_mem_charSpan R (μ + ν)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
  | smul a _ _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ a h

private theorem mul_mem_charSpan {f g : (κ → Rˣ) → R} (hf : f ∈ charSpan R κ)
    (hg : g ∈ charSpan R κ) : f * g ∈ charSpan R κ := by
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨μ, rfl⟩ := h
    exact mul_coe_weightCharHom_mem_charSpan R μ hg
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  | smul a _ _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a h

variable (κ)

/-- **The Laurent functions on the split torus `𝔾ₘ^κ`**: the `R`-subalgebra of functions on its
points spanned by the characters. Over a field these are the functions given by a Laurent
polynomial in the coordinates; the characters are the Laurent monomials. -/
def laurentFunctions : Subalgebra R ((κ → Rˣ) → R) where
  carrier := ↑(charSpan R κ)
  mul_mem' := fun hf hg ↦ mul_mem_charSpan R hf hg
  one_mem' := one_mem_charSpan R
  add_mem' := fun hf hg ↦ Submodule.add_mem _ hf hg
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun r ↦ by
    have h : algebraMap R ((κ → Rˣ) → R) r = r • (1 : (κ → Rˣ) → R) := by
      funext s
      simp
    rw [h]
    exact Submodule.smul_mem _ r (one_mem_charSpan R)

/-- **Membership in the Laurent functions** is membership in the span of the characters: every
Laurent function is a finite `R`-linear combination of characters. -/
theorem mem_laurentFunctions_iff {f : (κ → Rˣ) → R} :
    f ∈ laurentFunctions R κ ↔
      f ∈ Submodule.span R (Set.range fun μ : κ → ℤ ↦ ⇑(weightCharHom R μ)) :=
  Iff.rfl

variable {κ}

/-- Every character is a Laurent function. -/
@[simp]
theorem weightCharHom_mem_laurentFunctions (μ : κ → ℤ) :
    ⇑(weightCharHom R μ) ∈ laurentFunctions R κ :=
  coe_weightCharHom_mem_charSpan R μ

end WeightCharHom

section LinearIndependent

variable (K : Type u) [Field K] [Infinite K] {κ : Type v} [Fintype κ]

/-- Distinct weights give distinct `K`-valued characters of the split torus, over an infinite
field. -/
theorem weightCharHom_injective : Function.Injective (weightCharHom K (κ := κ)) := by
  intro μ ν h
  have hval : ∀ s : κ → Kˣ, ((weightChar K μ s : Kˣ) : K) = ((weightChar K ν s : Kˣ) : K) :=
    fun s ↦ DFunLike.congr_fun h s
  exact weightChar_injective (K := K) (κ := κ)
    (MonoidHom.ext fun s ↦ Units.ext (hval s))

/-- **Artin's independence of characters for a split torus**: over an infinite field the
characters of `𝔾ₘ^κ`, read as `K`-valued functions on its points, are linearly independent. This
is what makes the coefficients of a Laurent expansion well defined, and hence what makes a weight
readable off the action of the torus. -/
theorem linearIndependent_weightCharHom :
    LinearIndependent K fun μ : κ → ℤ ↦ ⇑(weightCharHom K μ) := by
  have h : LinearIndependent K fun f : (κ → Kˣ) →* K ↦ (f : (κ → Kˣ) → K) :=
    linearIndependent_monoidHom (κ → Kˣ) K
  exact h.comp (fun μ : κ → ℤ ↦ weightCharHom K μ) (weightCharHom_injective K)

end LinearIndependent

end TauCeti
