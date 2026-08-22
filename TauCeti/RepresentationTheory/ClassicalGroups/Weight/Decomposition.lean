/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.weightSpace` and `TauCeti.iSupIndep_weightSpace`; this module also re-exports
-- `TauCeti.diagGL` and the characters `TauCeti.weightChar` of the diagonal torus.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic
-- `TauCeti.IsRationalRep` and its basis-free coordinate-entry form.
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
-- The restriction of a rational function to the diagonal torus; this module also re-exports
-- `TauCeti.laurentFunctions` and `TauCeti.linearIndependent_weightCharHom`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LaurentFunctions

/-!
# The weight-space decomposition of a rational representation

A rational representation of `GL n ℂ` is the internal direct sum of its weight spaces: the
diagonal torus is simultaneously diagonalizable on it, and every joint eigencharacter occurring in
it is among the monomial characters `t ↦ ∏ i, tᵢ ^ lᵢ` of the torus. Which of those characters
actually occur — equivalently, which weight spaces are nonzero — is not determined here; the
decomposition is indexed by all of `Fin n → ℤ`. This file proves that
(`TauCeti.IsRationalRep.isInternal_weightSpace`), completing the decomposition that
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic` establishes only for the standard
representation.

Rationality is what carries the argument, and it cannot be dropped: an abstract representation of
the torus `(ℂˣ)ⁿ` on a finite-dimensional space need not be diagonalizable at all, and even a
diagonalizable one has joint eigencharacters that are arbitrary homomorphisms `(ℂˣ)ⁿ → ℂˣ`,
almost none of which is a monomial `t ↦ ∏ tᵢ ^ lᵢ`. Rationality forces both.

The proof is the **Laurent expansion** of the torus action. Restricted along `TauCeti.diagGL`, the
matrix entries of `ρ` are Laurent functions on the torus
(`TauCeti.comp_diagGL_mem_laurentFunctions`), so `ρ (diagGL t)` is a finite sum
`∑_l (∏ i, tᵢ ^ lᵢ) • A l` with coefficients `A l` in `Module.End ℂ W` that do not depend on `t`
(`TauCeti.IsRationalRep.exists_forall_diagGL_eq_sum_smul`). Comparing the expansion of
`ρ (diagGL (s * t))` with that of `ρ (diagGL s) ∘ ρ (diagGL t)` and using the linear independence
of distinct characters
(`TauCeti.linearIndependent_weightCharHom`) identifies the coefficients term by term: `ρ (diagGL s)`
acts on the image of `A l` by the character of `l`, so that image lies in the weight space of `l`
(`TauCeti.apply_mem_weightSpace_of_forall_diagGL_eq_sum_smul`). Evaluating the expansion at `t = 1`
writes the identity as `∑_l A l`, so every vector is a sum of weight vectors.

The tensor, symmetric and exterior powers of the standard representation are polynomial
(`TauCeti.isPolynomialRep_tensorPowerRep` and its companions), hence rational
(`TauCeti.IsPolynomialRep.isRationalRep`), so their decompositions are instances of the theorem
below and are not restated as separate declarations.

The pinned roadmap signature carries `[FiniteDimensional ℂ W]` as well. It is dropped here: it is
implied by `TauCeti.IsRationalRep.finite`, and an unused hypothesis on the statement would be both
weaker and flagged by the linter.

## Main results

* `TauCeti.IsRationalRep.exists_forall_diagGL_eq_sum_smul`: the Laurent expansion of a rational
  representation on the diagonal torus.
* `TauCeti.apply_mem_weightSpace_of_forall_diagGL_eq_sum_smul`: the coefficients of such an
  expansion take their values in the weight space of their exponent. This step mentions no
  rationality, so it is stated over an arbitrary infinite field; only the three results whose
  hypothesis is the `ℂ`-pinned `TauCeti.IsRationalRep` are stated over `ℂ`.
* `TauCeti.IsRationalRep.iSup_weightSpace_eq_top` and
  `TauCeti.IsRationalRep.isInternal_weightSpace`: **a rational representation of `GL n ℂ` is the
  internal direct sum of its weight spaces.**

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 1.5.
-/

public section

open Matrix

universe u v

namespace TauCeti

variable {n : ℕ}

section Expansion

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The Laurent expansion of a rational representation on the diagonal torus.** The action of
`diagGL t` is a finite sum `∑ l ∈ S, (∏ i, tᵢ ^ lᵢ) • A l` whose coefficients `A l` do not depend
on `t`: the matrix entries of `ρ` restrict to Laurent functions on the torus, and a Laurent
function is a finite combination of characters. -/
theorem IsRationalRep.exists_forall_diagGL_eq_sum_smul (h : IsRationalRep ρ) :
    ∃ (S : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → Module.End ℂ W),
      ∀ t : Fin n → ℂˣ, ρ (diagGL t) = ∑ l ∈ S, weightCharHom ℂ l t • A l := by
  classical
  obtain ⟨b, -, -, -⟩ := (isRationalRep_iff ρ).mp h
  have hlaurent : ∀ q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W),
      (fun t : Fin n → ℂˣ ↦ LinearMap.toMatrix b b (ρ (diagGL t)) q.1 q.2)
        ∈ laurentFunctions ℂ (Fin n) := fun q ↦
    comp_diagGL_mem_laurentFunctions
      ((isRationalRep_iff_forall_mem_rationalFunctions b).mp h q.1 q.2)
  choose c hc using fun q ↦
    Finsupp.mem_span_range_iff_exists_finsupp.mp
      ((mem_laurentFunctions_iff ℂ (Fin n)).mp (hlaurent q))
  refine ⟨Finset.univ.biUnion fun q ↦ (c q).support,
    fun l ↦ (LinearMap.toMatrix b b).symm (Matrix.of fun i j ↦ c (i, j) l), fun t ↦ ?_⟩
  refine (LinearMap.toMatrix b b).injective ?_
  rw [map_sum]
  ext i j
  have hsub : (c (i, j)).support ⊆ Finset.univ.biUnion fun q ↦ (c q).support :=
    fun l hl ↦ Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, hl⟩
  have hleft : LinearMap.toMatrix b b (ρ (diagGL t)) i j
      = ∑ l ∈ Finset.univ.biUnion fun q ↦ (c q).support, c (i, j) l * weightCharHom ℂ l t := by
    rw [← congrFun (hc (i, j)) t, Finsupp.sum]
    rw [Finset.sum_apply]
    refine Finset.sum_subset hsub fun l _ hl ↦ ?_
    rw [Finsupp.notMem_support_iff.mp hl, zero_smul, Pi.zero_apply]
  rw [hleft, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smul, LinearEquiv.apply_symm_apply]
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_comm]

end Expansion

section Coefficients

variable {K : Type v} [Field K] [Infinite K]
variable {W : Type u} [AddCommGroup W] [Module K W]
variable {ρ : Representation K (GL (Fin n) K) W}

/-- **The coefficients of a Laurent expansion take their values in the weight spaces.** If the
torus acts through a finite sum `∑ l ∈ S, (∏ i, tᵢ ^ lᵢ) • A l`, then every value of `A l` is a
weight vector of weight `l`. Nothing is claimed here about `A l` being idempotent, or acting as
the identity on the weight space of `l`; only its image is located.

Nothing in this statement refers to rationality, so the base field is an arbitrary infinite field:
the argument only needs distinct characters of the torus to stay linearly independent.

The proof compares the expansion of `ρ (diagGL (s * t))` with the composite
`ρ (diagGL s) ∘ ρ (diagGL t)`: both are combinations of the characters with `End`-valued
coefficients, and distinct characters are linearly independent
(`TauCeti.linearIndependent_weightCharHom`), so the coefficients agree term by term. -/
theorem apply_mem_weightSpace_of_forall_diagGL_eq_sum_smul {S : Finset (Fin n → ℤ)}
    {A : (Fin n → ℤ) → Module.End K W}
    (hA : ∀ t : Fin n → Kˣ, ρ (diagGL t) = ∑ l ∈ S, weightCharHom K l t • A l)
    {l : Fin n → ℤ} (hl : l ∈ S) (w : W) : A l w ∈ weightSpace ρ l := by
  have hψ : ∀ (ψ : W →ₗ[K] K) (t : Fin n → Kˣ) (v : W),
      ψ (ρ (diagGL t) v) = ∑ l' ∈ S, weightCharHom K l' t * ψ (A l' v) := by
    intro ψ t v
    rw [hA t, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun l' _ ↦ by
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
  have hcoeff : ∀ (ψ : W →ₗ[K] K) (s : Fin n → Kˣ),
      ψ (ρ (diagGL s) (A l w)) = weightCharHom K l s * ψ (A l w) := by
    intro ψ s
    have hli := linearIndependent_weightCharHom (K := K) (κ := Fin n)
    rw [linearIndependent_iff'] at hli
    have hsum : ∑ l' ∈ S,
        (ψ (ρ (diagGL s) (A l' w)) - weightCharHom K l' s * ψ (A l' w)) •
          ⇑(weightCharHom K l') = 0 := by
      funext t
      have e1 := hψ (ψ ∘ₗ ρ (diagGL s)) t w
      have e2 := hψ ψ (s * t) w
      have e3 : ρ (diagGL (s * t)) w = ρ (diagGL s) (ρ (diagGL t) w) := by
        rw [map_mul, map_mul, Module.End.mul_apply]
      rw [e3] at e2
      simp only [LinearMap.coe_comp, Function.comp_apply] at e1
      have e4 : ∑ l' ∈ S, weightCharHom K l' t * ψ (ρ (diagGL s) (A l' w))
          = ∑ l' ∈ S, weightCharHom K l' s * weightCharHom K l' t * ψ (A l' w) := by
        rw [← e1, e2]
        exact Finset.sum_congr rfl fun l' _ ↦ by rw [map_mul, mul_assoc]
      rw [Finset.sum_apply, Pi.zero_apply]
      have e5 : ∀ l' : Fin n → ℤ,
          ((ψ (ρ (diagGL s) (A l' w)) - weightCharHom K l' s * ψ (A l' w)) •
            ⇑(weightCharHom K l')) t
            = weightCharHom K l' t * ψ (ρ (diagGL s) (A l' w))
              - weightCharHom K l' s * weightCharHom K l' t * ψ (A l' w) := by
        intro l'
        rw [Pi.smul_apply, smul_eq_mul, sub_mul]
        ring
      rw [Finset.sum_congr rfl fun l' _ ↦ e5 l', Finset.sum_sub_distrib, e4, sub_self]
    exact sub_eq_zero.mp (hli S _ hsum l hl)
  set b := Module.Basis.ofVectorSpace K W
  refine (mem_weightSpace_iff ρ l (A l w)).mpr fun s ↦ b.ext_elem fun i ↦ ?_
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, map_smul, smul_eq_mul,
    ← weightCharHom_apply K l s]
  exact hcoeff (b.coord i) s

end Coefficients

section Decomposition

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The weight spaces of a rational representation span it.** Evaluating the Laurent expansion
at the identity of the torus writes the identity endomorphism as the sum of the expansion
coefficients, and each of those takes its values in a weight space. -/
theorem IsRationalRep.iSup_weightSpace_eq_top (h : IsRationalRep ρ) :
    ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤ := by
  obtain ⟨S, A, hA⟩ := h.exists_forall_diagGL_eq_sum_smul
  have hone : (1 : Module.End ℂ W) = ∑ l ∈ S, A l := by
    have h1 := hA 1
    rw [map_one, map_one] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [map_one, one_smul]
  refine top_le_iff.mp fun w _ ↦ ?_
  have hw : w = ∑ l ∈ S, A l w := by
    have hval := congrArg (fun f : Module.End ℂ W ↦ f w) hone
    simpa only [Module.End.one_apply, LinearMap.sum_apply] using hval
  rw [hw]
  exact Submodule.sum_mem _ fun l hl ↦ Submodule.mem_iSup_of_mem l
    (apply_mem_weightSpace_of_forall_diagGL_eq_sum_smul hA hl w)

/-- **The weight-space decomposition.** A rational representation of `GL n ℂ` is the internal
direct sum of its weight spaces: the diagonal torus is simultaneously diagonalizable on it, and the
decomposition is indexed by the integer weights `l`, the summand at `l` being the joint eigenspace
of the character `t ↦ ∏ i, tᵢ ^ lᵢ`. The sum runs over all of `Fin n → ℤ`; which weights actually
occur — that is, for which `l` the summand is nonzero — is not part of the statement. The roadmap
pins this statement
as `weightSpace_isInternal`; it is named for its conclusion here, matching the standard-
representation case `TauCeti.isInternal_weightSpace_stdRep`. -/
theorem IsRationalRep.isInternal_weightSpace (h : IsRationalRep ρ) :
    DirectSum.IsInternal fun l : Fin n → ℤ ↦ weightSpace ρ l :=
  isInternal_weightSpace_of_iSup_eq_top weightChar_injective h.iSup_weightSpace_eq_top

end Decomposition

end TauCeti
