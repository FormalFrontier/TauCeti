/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.Continuous.Schur

/-!
# A class function acts on an irreducible representation by a scalar

A continuous function `f` on a compact group `G` acts on a continuous representation `π` on `V`
by the **integrated operator**

`integratedOperator π hπ f = ∫ g, f g • π g ∂(haarProb G)`,

the Haar average of the action operators weighted by `f`. Its trace is the Haar integral of
`f · χ_π`, with no hypothesis on `f`.

When `f` is a **class function** — constant on conjugacy classes — the integrated operator commutes
with the action, because conjugating the integrand by `π h` translates its group variable by
`g ↦ h⁻¹ g h`, which normalized Haar measure does not see and which `f` does not see either. So for
an irreducible `π` over an algebraically closed field Schur's lemma makes it a scalar, and the trace
computation fixes that scalar:

`integratedOperator π hπ f = (dim V)⁻¹ · (∫ g, f g · χ_π g) • id`.

Specializing `f` to `conj χ_π` turns the character orthogonality relations into the character
projections; that is done in `TauCeti/RepresentationTheory/Compact/Character/Projection.lean`,
which is the only consumer of this file so far.

## Main definitions

* `TauCeti.ContRepresentation.integratedOperator`: the operator `∫ g, f g • π g` by which a
  continuous scalar function acts on a continuous representation.
* `TauCeti.ContRepresentation.integratedOperatorₗ`: the same, linear in the acting function.
* `TauCeti.ContRepresentation.integratedIntertwiner`: the integrated operator of a class function,
  packaged as a continuous self-intertwiner.

## Main results

* `TauCeti.ContRepresentation.trace_integratedOperator`: the trace of the integrated operator is
  `∫ g, f g · χ_π g`.
* `TauCeti.ContRepresentation.integratedOperator_comp`: a class function acts by an intertwiner.
* `TauCeti.ContRepresentation.integratedOperator_eq_smul_id`: **a class function acts on a
  finite-dimensional irreducible representation by the scalar `(dim V)⁻¹ · ∫ g, f g · χ_π g`.**
* `TauCeti.ContRepresentation.integratedOperator_eq_zero`: it acts as zero when that integral
  vanishes.

## Implementation notes

Being a class function is carried as the bare hypothesis `∀ g h : G, f (h * g * h⁻¹) = f g`, the
same shape as in `TauCeti/RepresentationTheory/Compact/ClassFunctionLp.lean`, rather than as a new
predicate: it is passed directly through this API, and the `L²`-level notion that deserves a
bundling is the almost-everywhere one, `TauCeti.classFunctionLp`, which is already defined.

The definition asks only that `V` be a normed space: it is `TauCeti.haarAverage` of a continuous
family valued in the operator space `V →L[𝕜] V`, so it inherits that average's convention. What the
Bochner integral reads is completeness of that codomain, and `[CompleteSpace V]` is what supplies
it; failing that, the average is the integral's junk value `0` rather than the classical integrated
form `π(f)`. Completeness therefore enters with
`TauCeti.ContRepresentation.integratedOperator_apply`, finite-dimensionality with the trace, and
algebraic closedness of the scalars with Schur's lemma. The integrated operator
of the trivial group action and other structural identities are not developed here: what the
character projections need is linearity in `f`, the trace, and the scalar theorem.

The scalar in `integratedOperator_eq_smul_id` is `(dim V)⁻¹ · ∫ f · χ_π`, not `∫ f · conj χ_π`: the
integrand pairs `f` with the character itself, and the conjugation appears only when the acting
function is specialized to `conj χ_π`.

## References

This is the operator infrastructure for the block-projection item of Layer 5 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
"averaging against `dim V_π · conj χ_π`". The mathematical development follows Daniel Bump, *Lie
Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck, *Representations of Compact Lie
Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory

namespace TauCeti

namespace ContRepresentation

section Conjugation

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugating the group variable, as a continuous self-map of the group. -/
private def conjMap (h : G) : C(G, G) :=
  (ContinuousMap.mulLeft h⁻¹).comp (ContinuousMap.mulRight h)

/-- Conjugation of the group variable, unfolded. -/
private theorem conjMap_apply (h g : G) : conjMap h g = h⁻¹ * (g * h) :=
  (rfl)

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar averaging does not see the conjugation of the group variable: it is a right translation
followed by a left translation. -/
private theorem haarAverage_comp_conjMap {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedSpace ℝ W] [SMulCommClass ℝ 𝕜 W] (F : C(G, W)) (h : G) :
    haarAverage G (𝕜 := 𝕜) (F.comp (conjMap h)) = haarAverage G (𝕜 := 𝕜) F := by
  rw [conjMap, ← ContinuousMap.comp_assoc, haarAverage_comp_mulRight, haarAverage_comp_mulLeft]

end Conjugation

section Integrated

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [CompleteSpace V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

omit [CompleteSpace V] in
/-- The integrand `g ↦ f g • π g` of the integrated operator, as a continuous map on the group.
Continuity is where the continuity hypothesis on the representation is used. -/
private noncomputable def weightFamily (f : C(G, 𝕜)) : C(G, V →L[𝕜] V) where
  toFun g := f g • π g
  continuous_toFun := f.continuous.smul hπ

omit [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- The integrand of the integrated operator, evaluated at a group element. This is the unfolding
lemma that keeps the proofs below from reaching through `weightFamily`'s definition. -/
@[simp]
private theorem weightFamily_apply (f : C(G, 𝕜)) (g : G) :
    weightFamily π hπ f g = f g • π g :=
  (rfl)

omit [CompleteSpace V] in
/-- **The operator by which a continuous scalar function acts on a continuous representation**,
`∫ g, f g • π g ∂(haarProb G)`.

On a complete `V` this is the classical integrated form `π(f)` of the representation, and it is
always defined there: the integrand is continuous and normalized Haar measure is finite. `V` is not
assumed complete. The average is taken in the operator space `V →L[𝕜] V`, so it is
`TauCeti.haarAverage`'s junk value `0` unless that space is complete, which `[CompleteSpace V]`
supplies; that is why the results below that read the operator's actual value carry it. -/
noncomputable def integratedOperator (f : C(G, 𝕜)) : V →L[𝕜] V :=
  haarAverage G (𝕜 := 𝕜) (weightFamily π hπ f)

/-- The integrated operator, evaluated at a vector. -/
theorem integratedOperator_apply (f : C(G, 𝕜)) (v : V) :
    integratedOperator π hπ f v = ∫ g, f g • π g v ∂haarProb G := by
  have h := (ContinuousLinearMap.apply 𝕜 V v).haarAverage_comp_comm (G := G)
    (weightFamily π hπ f)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [integratedOperator, ← h, haarAverage_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, ContinuousLinearMap.apply_apply,
    weightFamily_apply, smul_apply]

/-! ### Linearity in the acting function -/

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_zero : integratedOperator π hπ (0 : C(G, 𝕜)) = 0 := by
  have hzero : weightFamily π hπ (0 : C(G, 𝕜)) = 0 := by
    ext g v
    simp
  rw [integratedOperator, hzero, map_zero]

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_add (f₁ f₂ : C(G, 𝕜)) :
    integratedOperator π hπ (f₁ + f₂)
      = integratedOperator π hπ f₁ + integratedOperator π hπ f₂ := by
  have hadd : weightFamily π hπ (f₁ + f₂) = weightFamily π hπ f₁ + weightFamily π hπ f₂ := by
    ext g v
    simp [add_smul]
  rw [integratedOperator, integratedOperator, integratedOperator, hadd, map_add]

omit [CompleteSpace V] in
@[simp]
theorem integratedOperator_smul (c : 𝕜) (f : C(G, 𝕜)) :
    integratedOperator π hπ (c • f) = c • integratedOperator π hπ f := by
  have hsmul : weightFamily π hπ (c • f) = c • weightFamily π hπ f := by
    ext g v
    simp [mul_smul]
  rw [integratedOperator, integratedOperator, hsmul, map_smul]

omit [CompleteSpace V] in
/-- The integrated operator, bundled as a linear map in the acting function. Bundling supplies the
remaining additive identities (`map_neg`, `map_sub`, `map_sum`) through the `LinearMap` API. -/
noncomputable def integratedOperatorₗ : C(G, 𝕜) →ₗ[𝕜] V →L[𝕜] V where
  toFun := integratedOperator π hπ
  map_add' := integratedOperator_add π hπ
  map_smul' := integratedOperator_smul π hπ

omit [CompleteSpace V] in
@[simp]
theorem integratedOperatorₗ_apply (f : C(G, 𝕜)) :
    integratedOperatorₗ π hπ f = integratedOperator π hπ f :=
  (rfl)

/-! ### A class function acts by an intertwiner

Conjugation by a fixed pair of action operators is a continuous *linear* map on operators, so it
commutes with Haar averaging; on the integrand it acts as the conjugation `g ↦ h⁻¹ g h` of the group
variable, which normalized Haar measure does not see and which a class function does not see
either. -/

/-- Conjugation `S ↦ π h⁻¹ ∘ S ∘ π h`, packaged as a continuous linear map on operators. -/
private noncomputable def conjOp (h : G) : (V →L[𝕜] V) →L[𝕜] V →L[𝕜] V :=
  (ContinuousLinearMap.compL 𝕜 V V V (π h⁻¹)).comp
    ((ContinuousLinearMap.compL 𝕜 V V V).flip (π h))

omit hπ [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- `conjOp` is conjugation, unfolded. -/
private theorem conjOp_apply (h : G) (S : V →L[𝕜] V) :
    conjOp π h S = (π h⁻¹).comp (S.comp (π h)) := by
  simp [conjOp, ContinuousLinearMap.compL_apply]

variable {f : C(G, 𝕜)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)

include hf

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ V]
  [SMulCommClass ℝ 𝕜 V] [CompleteSpace V] in
/-- Conjugating the integrand of a class function by the action at `h` conjugates its group
variable: `π h⁻¹ ∘ (f g • π g) ∘ π h = f (h⁻¹ g h) • π (h⁻¹ g h)`. -/
private theorem conjOp_comp_weightFamily (h : G) :
    (conjOp π h : C(V →L[𝕜] V, V →L[𝕜] V)).comp (weightFamily π hπ f)
      = (weightFamily π hπ f).comp (conjMap h) := by
  ext g v
  have hclass : f (h⁻¹ * (g * h)) = f g := by
    have := hf g h⁻¹
    rwa [inv_inv, mul_assoc] at this
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, conjOp_apply,
    ContinuousLinearMap.comp_apply, weightFamily_apply, conjMap_apply, hclass, smul_apply,
    map_smul, map_mul π, mul_apply_eq_comp]

/-- The integrated operator of a class function is fixed by conjugation:
`π h⁻¹ ∘ π(f) ∘ π h = π(f)`. -/
private theorem conjOp_integratedOperator (h : G) :
    conjOp π h (integratedOperator π hπ f) = integratedOperator π hπ f := by
  rw [integratedOperator, ← ContinuousLinearMap.haarAverage_comp_comm,
    conjOp_comp_weightFamily π hπ hf h, haarAverage_comp_conjMap]

/-- **A class function acts by an intertwiner.** The integrated operator of a function constant on
conjugacy classes commutes with every action operator. -/
theorem integratedOperator_comp (h : G) :
    (integratedOperator π hπ f).comp (π h) = (π h).comp (integratedOperator π hπ f) := by
  have hconj := conjOp_integratedOperator π hπ hf h
  rw [conjOp_apply] at hconj
  have hid : (π h).comp (π h⁻¹) = ContinuousLinearMap.id 𝕜 V := by
    rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_def]
  calc (integratedOperator π hπ f).comp (π h)
      = (ContinuousLinearMap.id 𝕜 V).comp ((integratedOperator π hπ f).comp (π h)) := by
        rw [ContinuousLinearMap.id_comp]
    _ = ((π h).comp (π h⁻¹)).comp ((integratedOperator π hπ f).comp (π h)) := by rw [hid]
    _ = (π h).comp ((π h⁻¹).comp ((integratedOperator π hπ f).comp (π h))) :=
        ContinuousLinearMap.comp_assoc _ _ _
    _ = (π h).comp (integratedOperator π hπ f) := by rw [hconj]

/-- The action of a class function, packaged as a term of Mathlib's `ContIntertwiningMap`. -/
noncomputable def integratedIntertwiner : ContIntertwiningMap π π where
  __ := integratedOperator π hπ f
  isIntertwining' h := integratedOperator_comp π hπ hf h

@[simp]
theorem toContinuousLinearMap_integratedIntertwiner :
    (integratedIntertwiner π hπ hf).toContinuousLinearMap = integratedOperator π hπ f :=
  (rfl)

end Integrated

section Trace

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- Completeness of `V` is not an extra hypothesis on the results below: a finite-dimensional
normed space over an `RCLike` field is already complete. Mathlib keeps `FiniteDimensional.complete`
out of the global instance set, so it is installed here as a local instance instead. -/
local instance instCompleteSpaceIntegrated : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ

/-- **The trace of the integrated operator is the Haar integral of `f · χ_π`.** No hypothesis on
`f` is needed. This is what fixes the normalizing factor in
`TauCeti.ContRepresentation.integratedOperator_eq_smul_id`. -/
theorem trace_integratedOperator (f : C(G, 𝕜)) :
    LinearMap.trace 𝕜 V (integratedOperator π hπ f : V →ₗ[𝕜] V)
      = ∫ g, f g * character π hπ g ∂haarProb G := by
  have h := (traceCLM 𝕜 V).haarAverage_comp_comm (G := G) (weightFamily π hπ f)
  rw [← traceCLM_apply, integratedOperator, ← h, haarAverage_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_coe, weightFamily_apply, map_smul,
    traceCLM_apply, smul_eq_mul, character_apply]

variable [IsAlgClosed 𝕜] {f : C(G, 𝕜)} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)

include hf

/-- **A class function acts on a finite-dimensional irreducible representation by the scalar
`(dim V)⁻¹ · ∫ g, f g · χ_π g`.**

This is the operator form of the statement that the centre of the group algebra acts on an
irreducible by central characters; specialized to `f = conj χ_π` it gives the blockwise identities
of the character projection in
`TauCeti/RepresentationTheory/Compact/Character/Projection.lean`. -/
theorem integratedOperator_eq_smul_id
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    integratedOperator π hπ f
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ * ∫ g, f g * character π hπ g ∂haarProb G) •
        ContinuousLinearMap.id 𝕜 V := by
  let : Representation.IsIrreducible π.toRepresentation := hirr
  have : IsSimpleModule (MonoidAlgebra 𝕜 G) π.toRepresentation.asModule := inferInstance
  have : Nontrivial π.toRepresentation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra 𝕜 G) π.toRepresentation.asModule
  -- Nontriviality lives on the `Representation.asModule` type synonym; transport it along
  -- `Representation.asModuleEquiv` rather than through the synonym's definitional unfolding.
  have : Nontrivial V := π.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_irreducible π hirr (integratedIntertwiner π hπ hf)
  have hc := congrArg ContIntertwiningMap.toContinuousLinearMap hc
  simp only [toContinuousLinearMap_integratedIntertwiner,
    ContIntertwiningMap.toContinuousLinearMap_smul,
    ContIntertwiningMap.toContinuousLinearMap_one, ContinuousLinearMap.one_def] at hc
  have htrace := trace_integratedOperator π hπ f
  rw [hc] at htrace
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := 𝕜) (M := V)).ne'
  have hc' : c = (Module.finrank 𝕜 V : 𝕜)⁻¹ * ∫ g, f g * character π hπ g ∂haarProb G := by
    apply (eq_inv_mul_iff_mul_eq₀ hdim).2
    simpa [mul_comm] using htrace
  rw [hc, hc']

/-- A class function whose Haar integral against the character vanishes acts as zero on an
irreducible representation. -/
theorem integratedOperator_eq_zero
    (hirr : Representation.IsIrreducible π.toRepresentation)
    (hzero : ∫ g, f g * character π hπ g ∂haarProb G = 0) :
    integratedOperator π hπ f = 0 := by
  rw [integratedOperator_eq_smul_id π hπ hf hirr, hzero, mul_zero, zero_smul]

end Trace

end ContRepresentation

end TauCeti
