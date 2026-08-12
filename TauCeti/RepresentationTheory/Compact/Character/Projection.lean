/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.Basic
public import TauCeti.RepresentationTheory.Compact.Integrated

/-!
# The character projections

The conjugate `conj χ_π` of the character of a continuous representation `π` of a compact group is
a class function, so it acts on a finite-dimensional irreducible representation by a scalar
(`TauCeti.ContRepresentation.integratedOperator_eq_smul_id`, from
`TauCeti/RepresentationTheory/Compact/Integrated.lean`). Its Haar integral against another character
`χ_ρ` is the `L²` inner product of the two characters, so the character orthogonality relations of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` evaluate that scalar. This file records
the two resulting **character projections**, for `π` finite-dimensional irreducible and unitary:

* the kernel `dim V_π · conj χ_π` acts as the identity on `V_π` itself;
* `conj χ_π` acts as zero on a finite-dimensional irreducible `ρ` admitting no nonzero continuous
  intertwiner `ρ → π`.

These are the two blockwise identities from which the isotypic projectors are built; the projector
on a reducible representation, and the isotypic decomposition it cuts out, are not constructed here.

## Main results

* `TauCeti.ContRepresentation.integral_star_character_mul_character`: pairing a character with the
  conjugate of another one is the `L²` inner product of the two characters.
* `TauCeti.ContRepresentation.integratedOperator_star_character_self`: `conj χ_π` acts on `V_π` by
  the scalar `(dim V_π)⁻¹`, so that, by
  `TauCeti.ContRepresentation.finrank_smul_integratedOperator_star_character_self`, the kernel
  `dim V_π · conj χ_π` acts as the identity on `V_π`.
* `TauCeti.ContRepresentation.integratedOperator_star_character_eq_zero`: for `π` unitary,
  `conj χ_π` acts as zero on an irreducible representation admitting no nonzero continuous
  intertwiner into `π`.

## Implementation notes

The scalar in `TauCeti.ContRepresentation.integratedOperator_eq_smul_id` is
`(dim V)⁻¹ · ∫ f · χ_π`, not `∫ f · conj χ_π`: the integrand pairs the acting function with the
character itself, and the conjugation appears only here, where the acting function is specialized
to `conj χ_π` and `TauCeti.ContRepresentation.integral_star_character_mul_character` identifies the
integral with Mathlib's sesquilinear `L²` inner product of the two characters.

## References

This is the block-projection item of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
"averaging against `dim V_π · conj χ_π`", and the operator half of its Layer 6 item "characters span
the class functions". The mathematical development follows Daniel Bump, *Lie Groups*, second
edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*,
Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Projection

variable {𝕜 G V W : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W]
  [FiniteDimensional 𝕜 W]

local instance instCompleteSpaceProjectionSource : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

local instance instCompleteSpaceProjectionTarget : CompleteSpace W :=
  FiniteDimensional.complete 𝕜 W

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
  (ρ : ContRepresentation 𝕜 G W) (hρ : Continuous ρ)

include hπ

omit [IsAlgClosed 𝕜] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] in
/-- The conjugate of a character is a class function: the hypothesis in the shape that
`TauCeti.ContRepresentation.integratedOperator_eq_smul_id` takes. -/
private theorem star_character_conj (g h : G) :
    (star (character π hπ)) (h * g * h⁻¹) = (star (character π hπ)) g := by
  rw [ContinuousMap.star_apply, ContinuousMap.star_apply, character_conj π hπ g h]

include hρ

omit [IsAlgClosed 𝕜] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [NormedSpace ℝ W]
  [SMulCommClass ℝ 𝕜 W] in
/-- Pairing a representation's character with the conjugate of another one's is the `L²` inner
product of the two characters, in Mathlib's convention `⟪F, H⟫ = ∫ H · conj F`. This is what turns
the character orthogonality relations into statements about
`TauCeti.ContRepresentation.integratedOperator`. -/
theorem integral_star_character_mul_character :
    ∫ g, (star (character π hπ)) g * character ρ hρ g ∂haarProb G
      = ⟪characterLp π hπ, characterLp ρ hρ⟫_𝕜 := by
  rw [characterLp_def, characterLp_def, ContinuousMap.inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  rw [ContinuousMap.star_apply, RCLike.star_def, mul_comm]

/-- **The character projection kills an inequivalent representation.** If `π` is unitary and there
is no nonzero continuous intertwiner `ρ → π`, the conjugate character of `π` acts as zero on the
irreducible representation `ρ`.

Schur's lemma is not invoked for the intertwiner hypothesis; it is what supplies it for a pair of
inequivalent irreducibles. Irreducibility of `ρ` is still needed, since it is `ρ` on which the class
function acts. -/
theorem integratedOperator_star_character_eq_zero (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible ρ.toRepresentation)
    (hdistinct : ∀ φ : ContIntertwiningMap ρ π, φ.toContinuousLinearMap = 0) :
    integratedOperator ρ hρ (star (character π hπ)) = 0 :=
  integratedOperator_eq_zero ρ hρ (star_character_conj π hπ) hirr <| by
    rw [integral_star_character_mul_character π hπ ρ hρ,
      character_orthonormal_distinct π hπ ρ hρ hunitary hdistinct]

omit hρ

/-- **The conjugate character acts on its own representation by the inverse dimension.** For a
finite-dimensional irreducible unitary representation of dimension `d`, the integrated operator of
`conj χ_π` on `V_π` is `d⁻¹ • id`.

The scalar is `d⁻¹` rather than `1` exactly because the character has `L²` norm one: the projection
kernel that acts as the identity is `d · conj χ_π`, which is
`TauCeti.ContRepresentation.finrank_smul_integratedOperator_star_character_self`. -/
theorem integratedOperator_star_character_self (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    integratedOperator π hπ (star (character π hπ))
      = (Module.finrank 𝕜 V : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 V := by
  rw [integratedOperator_eq_smul_id π hπ (star_character_conj π hπ) hirr,
    integral_star_character_mul_character π hπ π hπ,
    character_orthonormal_self π hπ hunitary hirr, mul_one]

/-- **The block projection, normalized.** For a finite-dimensional irreducible unitary `π`, the
kernel `dim V_π · conj χ_π` acts as the identity on `V_π`; together with
`TauCeti.ContRepresentation.integratedOperator_star_character_eq_zero`, which makes it act as zero
on an irreducible representation with no nonzero intertwiner into `π`, these are the two blockwise
identities that characterize the isotypic projector attached to `π`. Assembling them into a
projector on a reducible representation is not done here. -/
theorem finrank_smul_integratedOperator_star_character_self (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    (Module.finrank 𝕜 V : 𝕜) • integratedOperator π hπ (star (character π hπ))
      = ContinuousLinearMap.id 𝕜 V := by
  let : Representation.IsIrreducible π.toRepresentation := hirr
  have : Nontrivial π.toRepresentation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra 𝕜 G) π.toRepresentation.asModule
  -- Nontriviality lives on the `Representation.asModule` type synonym; transport it along
  -- `Representation.asModuleEquiv` rather than through the synonym's definitional unfolding.
  have : Nontrivial V := π.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := 𝕜) (M := V)).ne'
  rw [integratedOperator_star_character_self π hπ hunitary hirr, smul_smul,
    mul_inv_cancel₀ hdim, one_smul]

end Projection

end ContRepresentation

end TauCeti
