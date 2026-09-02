/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The local-field structure on a finite extension

A finite extension `L` of a nonarchimedean local field `K` is again a nonarchimedean local
field, for a valuative relation extending the one of `K`. This file constructs that structure
from the spectral norm, together with the analytic bridge on the base field that the spectral
norm consumes. That the extension is the *only* one is a separate statement, and is not proved
here.

Nothing here is a global instance. A field that already carries a compatible valuative relation
and topology would otherwise acquire a second, only propositionally equal, one; every
declaration below is therefore a named definition, installed by the consumer with `letI`.

## Main definitions

* `TauCeti.IsNonarchimedeanLocalField.normalizedRankOne`: the rank-one structure on the
  canonical valuation of `K` that normalizes the absolute value by `q = Nat.card 𝓀[K]`.
* `TauCeti.IsNonarchimedeanLocalField.normalizedNormedField`: the normed-field structure on `K`
  whose norm is the absolute value normalized by the residue cardinality, so that a uniformizer
  has norm `q⁻¹` with `q = Nat.card 𝓀[K]`.
  `TauCeti.IsNonarchimedeanLocalField.normalizedNontriviallyNormedField` is the same structure
  with the nontriviality of the norm recorded, which is what `spectralNorm` consumes.
* `TauCeti.IsNonarchimedeanLocalField.normalizedNormedFieldTopology`: the topology it carries,
  named separately so that every comparison with the ambient topology is explicit.
* `TauCeti.IsNonarchimedeanLocalField.finiteExtensionNormedField`: the spectral norm of a finite
  extension `L/K`, as a normed-field structure on `L`. No topology and no valuative relation on
  `L` is assumed.
* `TauCeti.IsNonarchimedeanLocalField.finiteExtensionNormedFieldTopology` and
  `TauCeti.IsNonarchimedeanLocalField.finiteExtensionValuativeRel`: the topology and the
  valuative relation it induces on `L`.

## Main results

* `TauCeti.IsNonarchimedeanLocalField.normalizedNormedField_topology_eq`: the topology of the
  normalized norm on `K` is the given valuative topology, so no comparison is left implicit
  when the spectral norm is formed over it.
* `TauCeti.IsNonarchimedeanLocalField.normalizedNormedField.norm_isUniformizer`: a uniformizer
  has norm `q⁻¹`. This is the equation that fixes the normalization.
* `TauCeti.IsNonarchimedeanLocalField.finiteExtension_valuativeExtension`,
  `TauCeti.IsNonarchimedeanLocalField.finiteExtension_isValuativeTopology` and
  `TauCeti.IsNonarchimedeanLocalField.finiteExtension_isNonarchimedeanLocalField`: the closed
  chain. The valuative relation on `L` extends the one on `K`, the spectral-norm topology is
  valuative for it, and `L` is a nonarchimedean local field.

## Implementation notes

The value group of a nonarchimedean local field is discrete, so the canonical valuation has a
rank-one structure for any base `> 1`; the normalized norm on `K` is `Valued.toNormedField` for
the one that `Valuation.IsRankOneDiscrete.rankOne` builds from the base `q = Nat.card 𝓀[K]`.
Since `Valued.toNormedField` carries `Valued.toUniformSpace`, its topology is the valuative
topology on the nose, and `normalizedNormedField_topology_eq` is definitional. The uniform
structure used to form `Valued.v` is the right uniformity of the additive group, as in
`Mathlib/NumberTheory/LocalField/Basic.lean`; it is introduced locally in each declaration and is
not part of the exported data.

None of the lemmas below is a `simp` lemma. The structures are named definitions rather than
instances, so every statement carries its own `letI` and could not fire in a general context.

## References

* Serre, *Corps Locaux*, II §2 and III §5.
* Neukirch, *Algebraic Number Theory*, II §6 and II §8.
-/

public section

open ValuativeRel Valuation
open scoped NNReal WithZero

namespace TauCeti.IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [_root_.IsNonarchimedeanLocalField K]

/-! ### The analytic bridge on the base field -/

/-- The rank-one structure on the canonical valuation of a nonarchimedean local field that
normalizes the absolute value by the residue cardinality `q = Nat.card 𝓀[K]`, so that a
uniformizer has absolute value `q⁻¹`. -/
@[expose, instance_reducible]
noncomputable def normalizedRankOne : (valuation K).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _
    (by exact_mod_cast Finite.one_lt_card (α := 𝓀[K]) : 1 < (Nat.card 𝓀[K] : ℝ≥0))

/-- The normalized absolute value of a nonarchimedean local field, as a nontrivially normed
field structure. It is normalized by the residue cardinality `q = Nat.card 𝓀[K]`: a uniformizer
has absolute value `q⁻¹`, by `normalizedNormedField.norm_isUniformizer`.

This is a named definition rather than a global instance, so that a field already carrying a
compatible normed structure does not acquire a second one. -/
@[expose, instance_reducible]
noncomputable def normalizedNontriviallyNormedField : NontriviallyNormedField K :=
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI := normalizedRankOne K
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

/-- The normalized absolute value of a nonarchimedean local field, as a normed field structure.
This is the structure that `spectralNorm` consumes over the base field. -/
@[expose, instance_reducible]
noncomputable def normalizedNormedField : NormedField K :=
  (normalizedNontriviallyNormedField K).toNormedField

/-- The topology carried by `normalizedNormedField`. Naming it separately makes every later
comparison with the ambient topology of `K` explicit. -/
@[expose, instance_reducible]
noncomputable def normalizedNormedFieldTopology : TopologicalSpace K :=
  (normalizedNormedField K).toMetricSpace.toUniformSpace.toTopologicalSpace

/-- The topology of the normalized absolute value is the valuative topology of `K`.

This holds by construction: the uniformity underlying `normalizedNormedField` is the right
uniformity of the additive group of `K`, whose topology is the given one. -/
theorem normalizedNormedField_topology_eq :
    normalizedNormedFieldTopology K = ‹TopologicalSpace K› :=
  (rfl)

namespace normalizedNormedField

/-- The normalized absolute value induces the canonical valuative order of `K`. -/
theorem norm_le_iff (x y : K) :
    letI := normalizedNormedField K
    ‖x‖ ≤ ‖y‖ ↔ valuation K x ≤ valuation K y := by
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let _ := normalizedRankOne K
  exact Valued.toNormedField.norm_le_iff

/-- The closed unit ball of the normalized absolute value is the ring of integers of `K`. -/
theorem norm_le_one_iff {x : K} :
    letI := normalizedNormedField K
    ‖x‖ ≤ 1 ↔ x ∈ 𝒪[K] := by
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let _ := normalizedRankOne K
  rw [Valuation.mem_integer_iff]
  exact Valued.toNormedField.norm_le_one_iff

/-- A uniformizer has normalized absolute value `q⁻¹`, where `q = Nat.card 𝓀[K]` is the
cardinality of the residue field. This is the equation that fixes the normalization. -/
theorem norm_isUniformizer {π : K} (hπ : (valuation K).IsUniformizer π) :
    letI := normalizedNormedField K
    ‖π‖ = (Nat.card 𝓀[K] : ℝ)⁻¹ := by
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let _ := normalizedRankOne K
  rw [Valued.toNormedField.norm_def]
  -- The value of a uniformizer is the distinguished generator of the value group.
  have h1 : (Valued.v (R := K)).restrict π =
      ((Valuation.IsRankOneDiscrete.generator' (valuation K) : _) :
        MonoidWithZeroHom.ValueGroup₀ _) := by
    -- `Valued.v` and `valuation K` are the same valuation (`IsValuativeTopology.v_eq_valuation`),
    -- but the two spellings do not match syntactically, so the hypothesis is restated.
    have hπ' : Valued.v (R := K) π =
        ((Valuation.IsRankOneDiscrete.generator (valuation K) : _) : ValueGroupWithZero K) := hπ
    simp [Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.restrict₀_apply, hπ',
      Valuation.IsRankOneDiscrete.generator']
  -- The order isomorphism of the value group with `ℤᵐ⁰` sends that generator to `exp (-1)`.
  have h2 := Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_apply_zpow
    (valuation K) 1
  rw [zpow_one] at h2
  rw [h1]
  simp only [Valuation.RankOne.hom, Valuation.RankLeOne.hom', MonoidWithZeroHom.coe_comp,
    Function.comp_apply, MonoidWithZeroHom.coe_ofClass, h2]
  -- Finally `WithZeroMulInt.toNNReal q` sends `exp (-1)` to `q ^ (-1)`.
  have hne : (WithZero.exp (-1) : ℤᵐ⁰) ≠ 0 := by simp
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne, WithZero.toAdd_unzero_eq_log hne, WithZero.log_exp]
  simp

end normalizedNormedField

/-! ### The spectral norm of a finite extension -/

variable (L : Type*) [Field L] [Algebra K L] [Module.Finite K L]

/-- The spectral norm of a finite extension of a nonarchimedean local field, as a normed field
structure on `L`. Completeness and ultrametricity of the base come from
`normalizedNormedField`; no topology and no valuative relation on `L` is assumed. -/
@[expose, instance_reducible]
noncomputable def finiteExtensionNormedField : NormedField L :=
  letI := normalizedNontriviallyNormedField K
  spectralNorm.normedField K L

/-- The topology induced by the spectral norm on a finite extension. -/
@[expose, instance_reducible]
noncomputable def finiteExtensionNormedFieldTopology : TopologicalSpace L :=
  (finiteExtensionNormedField K L).toMetricSpace.toUniformSpace.toTopologicalSpace

namespace finiteExtensionNormedField

/-- The norm of `finiteExtensionNormedField` is the spectral norm. -/
theorem norm_def (x : L) :
    letI := normalizedNormedField K
    letI := finiteExtensionNormedField K L
    ‖x‖ = spectralNorm K L x := (rfl)

/-- The spectral norm extends the normalized absolute value of the base field. -/
theorem norm_algebraMap (a : K) :
    letI := normalizedNormedField K
    letI := finiteExtensionNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ :=
  letI := normalizedNontriviallyNormedField K
  spectralNorm_extends a

/-- The spectral norm of a finite extension of a nonarchimedean local field is ultrametric. -/
theorem isUltrametricDist :
    letI := finiteExtensionNormedField K L
    IsUltrametricDist L :=
  letI := normalizedNontriviallyNormedField K
  letI := finiteExtensionNormedField K L
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

end finiteExtensionNormedField

/-- The valuative relation induced on a finite extension by the spectral norm. A particular
`Valuation L ℝ≥0` is a proof witness here, not a second public carrier: the exported object is
the valuative relation. -/
@[expose, instance_reducible]
noncomputable def finiteExtensionValuativeRel : ValuativeRel L :=
  letI := finiteExtensionNormedField K L
  haveI := finiteExtensionNormedField.isUltrametricDist K L
  .ofValuation (NormedField.valuation (K := L))

/-- The valuative relation of a finite extension is the order of the spectral norm. -/
theorem finiteExtension_vle_iff (x y : L) :
    letI := finiteExtensionNormedField K L
    letI := finiteExtensionValuativeRel K L
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  let _ := finiteExtensionNormedField K L
  have := finiteExtensionNormedField.isUltrametricDist K L
  let _ := finiteExtensionValuativeRel K L
  have : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  rw [Valuation.vle_iff_le (NormedField.valuation (K := L)) (x := x) (y := y)]
  simp [NormedField.valuation_apply, ← NNReal.coe_le_coe]

/-- The valuative relation constructed on a finite extension extends the one of the base field. -/
theorem finiteExtension_valuativeExtension :
    letI := finiteExtensionValuativeRel K L
    ValuativeExtension K L := by
  let _ := normalizedNormedField K
  let _ := finiteExtensionNormedField K L
  let _ := finiteExtensionValuativeRel K L
  refine ⟨fun a b ↦ ?_⟩
  rw [finiteExtension_vle_iff K L, finiteExtensionNormedField.norm_algebraMap,
    finiteExtensionNormedField.norm_algebraMap, normalizedNormedField.norm_le_iff]
  exact (Valuation.vle_iff_le (valuation K)).symm

/-- The spectral-norm topology of a finite extension is valuative for the valuative relation the
spectral norm induces. This is the bridge from the analytic construction to the valuative
carrier. -/
theorem finiteExtension_isValuativeTopology :
    @IsValuativeTopology L _ (finiteExtensionValuativeRel K L)
      (finiteExtensionNormedFieldTopology K L) := by
  let _ := finiteExtensionNormedField K L
  have := finiteExtensionNormedField.isUltrametricDist K L
  let _ := finiteExtensionValuativeRel K L
  have : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
    (fun {s} ↦ (NormedField.toValued (K := L)).is_topological_valuation s)

/-- A finite extension of a nonarchimedean local field is locally compact for the
spectral-norm topology: it is a finite-dimensional normed space over a locally compact field. -/
private theorem finiteExtension_locallyCompactSpace :
    @LocallyCompactSpace L (finiteExtensionNormedFieldTopology K L) := by
  let _ := normalizedNontriviallyNormedField K
  let _ := finiteExtensionNormedField K L
  let _ := spectralNorm.normedSpace K L
  have : ProperSpace L := FiniteDimensional.proper K L
  infer_instance

/-- The valuative relation of a finite extension is nontrivial, because it extends the
nontrivial valuative relation of the base field. -/
private theorem finiteExtension_isNontrivial :
    @ValuativeRel.IsNontrivial L _ (finiteExtensionValuativeRel K L) := by
  let _ := normalizedNontriviallyNormedField K
  let _ := finiteExtensionNormedField K L
  have := finiteExtensionNormedField.isUltrametricDist K L
  let _ := finiteExtensionValuativeRel K L
  have : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := L)),
    Valuation.IsNontrivial_iff_exists_one_lt]
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  exact ⟨algebraMap K L x, by
    simpa [finiteExtensionNormedField.norm_algebraMap K L x, ← NNReal.coe_lt_coe] using hx⟩

/-- **A finite extension of a nonarchimedean local field is a nonarchimedean local field**, for
the valuative relation and the topology that the spectral norm constructs on it. Neither a
topology nor a valuative relation on `L` is assumed. -/
theorem finiteExtension_isNonarchimedeanLocalField :
    @_root_.IsNonarchimedeanLocalField L _ (finiteExtensionValuativeRel K L)
      (finiteExtensionNormedFieldTopology K L) :=
  letI := finiteExtensionValuativeRel K L
  letI := finiteExtensionNormedFieldTopology K L
  haveI := finiteExtension_isValuativeTopology K L
  haveI := finiteExtension_locallyCompactSpace K L
  haveI := finiteExtension_isNontrivial K L
  ⟨⟩

end TauCeti.IsNonarchimedeanLocalField
