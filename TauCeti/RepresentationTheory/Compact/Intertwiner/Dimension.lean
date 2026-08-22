/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.Basic
public import TauCeti.RepresentationTheory.Compact.Invariants

/-!
# The character integral counts the intertwiners

For finite-dimensional continuous representations `π` on `V` and `ρ` on `W` of a compact group,

`∫ g, χ_π(g⁻¹) · χ_ρ(g) ∂(haarProb G) = dim Hom_G(V, W)`,

the dimension being that of Mathlib's `ContIntertwiningMap π ρ`. This is the compact-group form of
the finite-group identity `|G|⁻¹ ∑ g, χ_ρ(g) · χ_π(g⁻¹) = dim Hom_G(V, W)`
(`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`), with the Haar integral in place of
the normalized sum.

The proof is the composition of two facts already available and needs no new analysis. The Hom
representation of `TauCeti/RepresentationTheory/Continuous/LinHom.lean` has the intertwiners as its
invariants and `χ_π(g⁻¹) · χ_ρ(g)` as its character, and Haar averaging counts the invariants of a
representation by integrating its character
(`ContRepresentation.integral_character_eq_finrank_invariants`). Applying the second to the
first is the theorem.

For a **unitary** `π` the character at an inverse is the conjugate of the character
(`TauCeti.ContRepresentation.character_apply_inv`), so the integrand becomes `conj χ_π · χ_ρ`, the
`L²` pairing of the two characters. In that form the theorem is the quantitative statement behind
Schur orthogonality: the pairing of the characters of two irreducibles is the dimension of the
space of intertwiners between them. That dimension is `0` when the two admit no nonzero
intertwiner, and for an irreducible against itself it is the dimension of its endomorphism
division algebra — which Schur's lemma makes `1` only over algebraically closed scalars, and which
over `ℝ` is `1`, `2` or `4`. This is why `TauCeti.ContRepresentation.character_orthonormal_self`
carries `[IsAlgClosed 𝕜]` while `character_orthonormal_distinct` does not.

## Main statements

* `ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap`: the character
  integral is the dimension of the space of continuous intertwiners.
* `ContRepresentation.integral_star_character_mul_eq_finrank_contIntertwiningMap`: the same
  with the conjugate character, for a unitary representation.
* `ContRepresentation.inner_characterLp_eq_finrank_contIntertwiningMap`: the same read as
  the `L²` inner product of the two characters.
* `ContRepresentation.integral_character_mul_eq_zero_iff`: the integral vanishes exactly
  when every continuous intertwiner is zero.

## References

This supplies the counting theorem that Layer 6 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
reads off the character orthogonality relations, the compact analogue of Mathlib's
`FDRep.scalar_product_char_eq_finrank_equivariant`. The mathematical development follows Daniel
Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of
Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory TauCeti TauCeti.ContRepresentation
open scoped InnerProductSpace

namespace ContRepresentation

section Counting

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
  (hπ : Continuous π) (hρ : Continuous ρ)

include hπ hρ

omit [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] in
/-- The integral of the character of the Hom representation is the integral of the product of
characters. This is the pointwise character identity `ContRepresentation.character_linHom` under
the integral sign, and is what both theorems below rewrite along. -/
private theorem integral_character_linHom :
    ∫ g, character (linHom π ρ) (continuous_linHom π ρ hπ hρ) g ∂haarProb G
      = ∫ g, character π hπ g⁻¹ * character ρ hρ g ∂haarProb G := by
  simp_rw [character_linHom π ρ hπ hρ]

/-- **The character integral counts the intertwiners**:
`∫ g, χ_π(g⁻¹) · χ_ρ(g) ∂(haarProb G) = dim Hom_G(V, W)`.

Both sides read the Hom representation on `V →L[𝕜] W`: its character is the integrand, and its
invariants are the continuous intertwiners, which Haar averaging counts. -/
theorem integral_character_mul_eq_finrank_contIntertwiningMap :
    ∫ g, character π hπ g⁻¹ * character ρ hρ g ∂haarProb G
      = (Module.finrank 𝕜 (ContIntertwiningMap π ρ) : 𝕜) := by
  rw [← integral_character_linHom π ρ hπ hρ,
    integral_character_eq_finrank_invariants _ (continuous_linHom π ρ hπ hρ),
    (invariantsEquivContIntertwiningMap π ρ).finrank_eq]

/-- **The character integral vanishes exactly when there is no nonzero intertwiner.** This is the
hypothesis under which the second Schur orthogonality relation
(`TauCeti.ContRepresentation.schur_orthogonality_distinct`) is stated, now detected by the
characters. -/
theorem integral_character_mul_eq_zero_iff :
    ∫ g, character π hπ g⁻¹ * character ρ hρ g ∂haarProb G = 0
      ↔ ∀ f : ContIntertwiningMap π ρ, f.toContinuousLinearMap = 0 := by
  rw [← integral_character_linHom π ρ hπ hρ,
    integral_character_eq_zero_iff _ (continuous_linHom π ρ hπ hρ), Submodule.eq_bot_iff]
  constructor
  · exact fun h f ↦ h _ (toContinuousLinearMap_mem_invariants_linHom π ρ f)
  · intro h T hT
    exact h ⟨T, (mem_linHom_invariants_iff_isIntertwining π ρ T).1 hT⟩

end Counting

section Unitary

variable {𝕜 G V W : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]
  (π : ContRepresentation 𝕜 G V) (ρ : ContRepresentation 𝕜 G W)
  (hπ : Continuous π) (hρ : Continuous ρ)

include hπ hρ

/-- **The `L²` pairing of the characters counts the intertwiners.** For a unitary `π` the character
at an inverse is the conjugate of the character, so the integrand of
`ContRepresentation.integral_character_mul_eq_finrank_contIntertwiningMap` is
`conj χ_π · χ_ρ`, the integrand of the `L²` inner product of the two characters. -/
theorem integral_star_character_mul_eq_finrank_contIntertwiningMap (hunitary : IsUnitary π) :
    ∫ g, (starRingEnd 𝕜) (character π hπ g) * character ρ hρ g ∂haarProb G
      = (Module.finrank 𝕜 (ContIntertwiningMap π ρ) : 𝕜) := by
  rw [← integral_character_mul_eq_finrank_contIntertwiningMap π ρ hπ hρ]
  simp_rw [character_apply_inv π hπ hunitary]

/-- **The `L²` inner product of the two characters is the dimension of the space of intertwiners.**
This is the compact-group form of Mathlib's `FDRep.scalar_product_char_eq_finrank_equivariant`, and
the quantitative statement of which the two character orthogonality relations are the irreducible
case: `0` when there is no nonzero intertwiner, and `1` for an irreducible against itself once the
scalars are algebraically closed, so that Schur's lemma makes its endomorphism algebra
one-dimensional. -/
theorem inner_characterLp_eq_finrank_contIntertwiningMap (hunitary : IsUnitary π) :
    ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜
      = (Module.finrank 𝕜 (ContIntertwiningMap π ρ) : 𝕜) := by
  rw [characterLp_def, characterLp_def, ContinuousMap.inner_toLp,
    ← integral_star_character_mul_eq_finrank_contIntertwiningMap π ρ hπ hρ hunitary]
  simp_rw [mul_comm]

end Unitary

end ContRepresentation
