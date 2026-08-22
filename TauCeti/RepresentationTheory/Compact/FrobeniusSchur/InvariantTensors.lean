/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Symmetric
public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.Compact.Invariants
public import TauCeti.RepresentationTheory.Continuous.Subrepresentation
public import TauCeti.RepresentationTheory.Continuous.TensorProduct

/-!
# The Frobenius-Schur indicator counts invariant tensors

For a finite-dimensional continuous representation `π` of a compact group `G`, the Frobenius-Schur
indicator `ν₂(π) = ∫_G χ_π(g²) dμ` of
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Basic.lean` is the **signed count of invariant
tensors**,

`ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`,

the compact-group form of the finite-group identity
`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`.

The two squares are realized *inside* the tensor square `V ⊗[ℂ] V`, as the two eigenspaces of the
flip `x ⊗ y ↦ y ⊗ x` (`TauCeti.symmetricTensors` and `TauCeti.antisymmetricTensors`). That is not
a matter of taste: Haar averaging counts the invariants of a *continuous* representation, so the
carrier has to be a topological vector space, and the tensor square of a complex inner product
space is one, whereas `Sym[ℂ]^2 V` and `⋀[ℂ]^2 V` — a quotient and a subobject of a
`PiTensorProduct` — carry no topology. In characteristic zero the eigenspaces are the symmetric and
exterior squares, so nothing is lost.

With the squares realized that way the proof is short. The tensor square of `π` is
`TauCeti.ContRepresentation.tprod π π`, the flip commutes with it, so each eigenspace is a
subrepresentation, and their characters differ by `χ_π(g²)`: this is
`TauCeti.trace_restrict_symmetricTensors_sub`, whose linear-algebra content is that composing
`f ⊗ f` with the flip has trace `tr (f ∘ f)`. Integrating that pointwise identity and reading each
character integral as a dimension of invariants
(`ContRepresentation.integral_character_eq_finrank_invariants`) is the theorem.

## Main definitions

* `ContRepresentation.symmetricSquare`: the symmetric square of a continuous representation, its
  restriction to the symmetric tensors of `V ⊗[ℂ] V`.
* `ContRepresentation.antisymmetricSquare`: its restriction to the antisymmetric tensors.

## Main statements

* `ContRepresentation.character_symmetricSquare_sub_character_antisymmetricSquare`: the two square
  characters differ by the character at the square, `χ_{Sym²}(g) - χ_{Λ²}(g) = χ_π(g²)`.
* `ContRepresentation.frobeniusSchurIndicator_eq_sub_finrank_invariants`: **the Frobenius-Schur
  indicator is the signed count of invariant tensors**,
  `ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.
* `ContRepresentation.frobeniusSchurIndicator_eq_intCast`: it is therefore an integer, the first
  half of the reality trichotomy.

## Implementation notes

The carrier of `TauCeti.ContRepresentation.character` is pinned by name at every use below, as
`character (𝕜 := ℂ) (V := symmetricTensors ℂ V) ...`. It has to be: the carrier is an implicit
argument that the elaborator would have to read off the coercion `⇑(symmetricSquare π)`, and a
submodule of `V ⊗[ℂ] V` receives its topology both as a subtype and through the norm its
`NormedAddCommGroup` instance carries, so that unification stalls between the two instance paths.
Pinning the carrier costs a few characters and makes every statement below elaborate on the first
try.

## References

This is the reading of `ν₂(π)` as a difference of invariant counts that Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
asks for, and that `TauCeti/RepresentationTheory/Compact/Invariants.lean` was built to supply; the
trichotomy `ν₂ ∈ {1, 0, -1}` is the next step and is not proved here. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck,
*Representations of Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory

open TauCeti TauCeti.ContRepresentation

open scoped TensorProduct

namespace ContRepresentation

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [FiniteDimensional ℂ V] in
/-- The tensor square of a continuous representation acts on the tensor square by `f ⊗ f`, so the
symmetric tensors are one of its invariant submodules. -/
theorem tprod_self_mem_symmetricTensors (g : G) {x : V ⊗[ℂ] V}
    (hx : x ∈ symmetricTensors ℂ V) : tprod π π g x ∈ symmetricTensors ℂ V := by
  rw [ContRepresentation.tprod_apply, TensorProduct.mapL_apply]
  exact map_self_mem_symmetricTensors _ hx

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [FiniteDimensional ℂ V] in
/-- The antisymmetric tensors are the other invariant submodule of the tensor square. -/
theorem tprod_self_mem_antisymmetricTensors (g : G) {x : V ⊗[ℂ] V}
    (hx : x ∈ antisymmetricTensors ℂ V) : tprod π π g x ∈ antisymmetricTensors ℂ V := by
  rw [ContRepresentation.tprod_apply, TensorProduct.mapL_apply]
  exact map_self_mem_antisymmetricTensors _ hx

/-- **The symmetric square** of a continuous representation: its tensor square restricted to the
symmetric tensors. -/
@[expose] noncomputable def symmetricSquare : ContRepresentation ℂ G (symmetricTensors ℂ V) :=
  subrepresentation (tprod π π) (symmetricTensors ℂ V)
    fun g _ hx ↦ tprod_self_mem_symmetricTensors π g hx

/-- **The antisymmetric square** of a continuous representation: its tensor square restricted to
the antisymmetric tensors. In characteristic zero this is the exterior square. -/
@[expose] noncomputable def antisymmetricSquare :
    ContRepresentation ℂ G (antisymmetricTensors ℂ V) :=
  subrepresentation (tprod π π) (antisymmetricTensors ℂ V)
    fun g _ hx ↦ tprod_self_mem_antisymmetricTensors π g hx

variable (hπ : Continuous π)

include hπ

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [FiniteDimensional ℂ V] in
/-- The symmetric square of a continuous representation is continuous. -/
theorem continuous_symmetricSquare : Continuous (symmetricSquare π) :=
  continuous_subrepresentation (continuous_tprod π π hπ hπ)

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [FiniteDimensional ℂ V] in
/-- The antisymmetric square of a continuous representation is continuous. -/
theorem continuous_antisymmetricSquare : Continuous (antisymmetricSquare π) :=
  continuous_subrepresentation (continuous_tprod π π hπ hπ)

omit hπ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [FiniteDimensional ℂ V] in
/-- The symmetric square acts by the restriction of `π g ⊗ π g`. -/
theorem coe_symmetricSquare_apply (g : G) :
    ((symmetricSquare π g : symmetricTensors ℂ V →L[ℂ] symmetricTensors ℂ V) :
        symmetricTensors ℂ V →ₗ[ℂ] symmetricTensors ℂ V)
      = symmetricTensorsRestrict (π g : V →ₗ[ℂ] V) := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [symmetricSquare, ContRepresentation.tprod_apply]

omit hπ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [FiniteDimensional ℂ V] in
/-- The antisymmetric square acts by the restriction of `π g ⊗ π g`. -/
theorem coe_antisymmetricSquare_apply (g : G) :
    ((antisymmetricSquare π g : antisymmetricTensors ℂ V →L[ℂ] antisymmetricTensors ℂ V) :
        antisymmetricTensors ℂ V →ₗ[ℂ] antisymmetricTensors ℂ V)
      = antisymmetricTensorsRestrict (π g : V →ₗ[ℂ] V) := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simp [antisymmetricSquare, ContRepresentation.tprod_apply]

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- **The two square characters differ by the character at the square**,
`χ_{Sym²π}(g) - χ_{Λ²π}(g) = χ_π(g²)`.

This is `TauCeti.trace_restrict_symmetricTensors_sub` applied to the operator `π g`, whose square
is `π (g * g)`. -/
theorem character_symmetricSquare_sub_character_antisymmetricSquare (g : G) :
    character (𝕜 := ℂ) (V := symmetricTensors ℂ V) (symmetricSquare π)
          (continuous_symmetricSquare π hπ) g
        - character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V) (antisymmetricSquare π)
          (continuous_antisymmetricSquare π hπ) g
      = character π hπ (g * g) := by
  rw [character_apply, character_apply, character_apply, coe_symmetricSquare_apply π g,
    coe_antisymmetricSquare_apply π g, trace_restrict_symmetricTensors_sub (π g : V →ₗ[ℂ] V)]
  congr 1
  rw [map_mul]
  rfl

/-- **The Frobenius-Schur indicator is the signed count of invariant tensors**,
`ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.

Integrate `ContRepresentation.character_symmetricSquare_sub_character_antisymmetricSquare` and read
each of the two character integrals as the dimension of the invariants of its representation
(`ContRepresentation.integral_character_eq_finrank_invariants`). This is the compact-group form of
the finite-group `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`, with
the Haar integral in place of the average over the group. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariants :
    frobeniusSchurIndicator π hπ
      = (Module.finrank ℂ (symmetricSquare π).invariants : ℂ)
        - (Module.finrank ℂ (antisymmetricSquare π).invariants : ℂ) := by
  have hs := integral_character_eq_finrank_invariants (𝕜 := ℂ) (V := symmetricTensors ℂ V)
    (symmetricSquare π) (continuous_symmetricSquare π hπ)
  have ha := integral_character_eq_finrank_invariants (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
    (antisymmetricSquare π) (continuous_antisymmetricSquare π hπ)
  have hIs : Integrable (fun g : G ↦ character (𝕜 := ℂ) (V := symmetricTensors ℂ V)
      (symmetricSquare π) (continuous_symmetricSquare π hπ) g) (haarProb G) := by
    exact integrable_continuousMap G (character (𝕜 := ℂ) (V := symmetricTensors ℂ V)
      (symmetricSquare π) (continuous_symmetricSquare π hπ))
  have hIa : Integrable (fun g : G ↦ character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
      (antisymmetricSquare π) (continuous_antisymmetricSquare π hπ) g) (haarProb G) := by
    exact integrable_continuousMap G (character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
      (antisymmetricSquare π) (continuous_antisymmetricSquare π hπ))
  calc frobeniusSchurIndicator π hπ
      = ∫ g, (character (𝕜 := ℂ) (V := symmetricTensors ℂ V) (symmetricSquare π)
            (continuous_symmetricSquare π hπ) g
          - character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V) (antisymmetricSquare π)
            (continuous_antisymmetricSquare π hπ) g) ∂(haarProb G) := by
        rw [frobeniusSchurIndicator_def]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦
          (character_symmetricSquare_sub_character_antisymmetricSquare π hπ g).symm)
    _ = (Module.finrank ℂ (symmetricSquare π).invariants : ℂ)
          - (Module.finrank ℂ (antisymmetricSquare π).invariants : ℂ) := by
        rw [integral_sub hIs hIa, hs, ha]

/-- **The Frobenius-Schur indicator of a compact group is an integer**, being the difference of two
dimensions. This is the first half of the reality trichotomy `ν₂ ∈ {1, 0, -1}`, and the
compact-group form of the finite-group
`TauCeti.Representation.frobeniusSchurIndicator_eq_intCast`; that the integer is one of `1`, `0`,
`-1` for an irreducible needs Schur's lemma and is not proved here. -/
theorem frobeniusSchurIndicator_eq_intCast :
    frobeniusSchurIndicator π hπ
      = ((Module.finrank ℂ (symmetricSquare π).invariants
          - Module.finrank ℂ (antisymmetricSquare π).invariants : ℤ) : ℂ) := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  push_cast
  ring

end CompactGroup

end ContRepresentation
