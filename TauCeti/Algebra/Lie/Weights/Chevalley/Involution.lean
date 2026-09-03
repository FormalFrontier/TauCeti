/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Chevalley.System
public import TauCeti.Algebra.Lie.Weights.StructureConstant.Opposite

/-!
# A Chevalley involution exists exactly when the structure constants are integral

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra, and let `x` be a normalised family
of root vectors, so `⁅x α, x (-α)⁆ = α∨`. A *Chevalley system* asks in addition for a Lie
automorphism `ω` with

```text
ω (x α) = -x (-α).
```

`TauCeti.IsChevalleySystem` carries `ω` as data, and every construction consuming a Chevalley
system therefore has to be handed one. This file removes that obligation: `ω` exists precisely
when the structure constants of `x` are the Chevalley integers `±(p + 1)`, and it is then unique.

The equivalence rests on the rescaling invariant
`TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`, which says that
`N(α, β) N(-α, -β) = -(p + 1)²` for *every* normalised family. Integrality of `N(α, β)` is thus
the same condition as the sign symmetry `N(-α, -β) = -N(α, β)`, and the sign symmetry is exactly
what makes the linear map sending `x α` to `-x (-α)` and acting by `-1` on `H` respect the
bracket.

The map itself is assembled from the weight-space decomposition `L = ⨁ χ, L χ`: on `L χ` for a
root `χ` it is `v ↦ -(B(v, x (-χ)) / B(x χ, x (-χ))) • x (-χ)`, which sends `x χ` to `-x (-χ)`,
and on the zero weight space `H` it is `-1`. Since only its existence is asserted, the
construction stays inside the proof.

## Main definitions

* `TauCeti.IsSl2System.IsChevalleyNormalized`: every genuine root-sum structure constant of the
  normalised family is `±(p + 1)`.

## Main results

* `TauCeti.IsSl2System.exists_isChevalleySystem`: an integrally normalised family carries a
  Chevalley involution.
* `TauCeti.IsChevalleySystem.isChevalleyNormalized`: conversely, a Chevalley system is integrally
  normalised.
* `TauCeti.IsSl2System.isChevalleyNormalized_iff_exists_isChevalleySystem`: the resulting
  characterisation of Chevalley systems among normalised families.
* `TauCeti.IsChevalleySystem.unique`: the Chevalley involution attached to a normalised family is
  unique.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §2, no. 4.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This advances the Chevalley-basis input to the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the `CFSGStatement`
roadmap.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

include hx

/-- A normalised family of root vectors is **integrally normalised** when every genuine root-sum
structure constant is one of the Chevalley integers `±(p + 1)`, with `p = chainBotCoeff α β`.

Only root-sums of two roots are constrained: at a zero weight the family vanishes, so its
structure constants are `0` and carry no information. -/
def IsChevalleyNormalized : Prop :=
  ∀ (α β γ : Weight K H L), α.IsNonZero → β.IsNonZero → ∀ (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β),
    hx.structureConstant α β γ hγ hαβ = ((chainBotCoeff α β + 1 : ℕ) : K) ∨
      hx.structureConstant α β γ hγ hαβ = -((chainBotCoeff α β + 1 : ℕ) : K)

/-- Compute the image of a bracket of root vectors under a linear map. If the map negates the
coroot of `α` and sends the root vector of a root-sum `γ = α + β` to the negative of its opposite,
then integral normalisation determines its value on `⁅x α, x β⁆`.

The two hypotheses are exactly what the two non-trivial cases need: opposite roots bracket to the
coroot, and a root-sum needs the value of the map at the sum alone. This is the only place the
sign symmetry of the structure constants is used, and it is the reason integrality is the right
hypothesis: on a root-sum `γ = α + β` the two sides differ by `N(-α, -β) + N(α, β)`. -/
private theorem map_lie_root_of_isChevalleyNormalized (hn : hx.IsChevalleyNormalized)
    {α β : Weight K H L} (hα : α.IsNonZero) (hβ : β.IsNonZero) (ω : L →ₗ[K] L)
    (hωsum : ∀ γ : Weight K H L, γ.IsNonZero → (γ : H → K) = (α : H → K) + β →
      ω (x γ) = -x (-γ))
    (hωcoroot : ω (coroot α : L) = -(coroot α : L)) :
    ω ⁅x α, x β⁆ = ⁅x (-α), x (-β)⁆ := by
  by_cases hzero : (α : H → K) + β = 0
  · -- The two roots are opposite: the bracket is the coroot, which `ω` negates.
    have hcoe : (β : H → K) = ((-α : Weight K H L) : H → K) := by
      rw [Weight.coe_neg]
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hzero)
    have hβα : β = -α := by
      ext z
      exact congrFun hcoe z
    subst hβα
    rw [neg_neg, hx.lie_neg α hα, hωcoroot, ← lie_skew (x (-α)) (x α),
      hx.lie_neg α hα]
  · by_cases hbot : rootSpace H ((α : H → K) + β) = ⊥
    · -- The sum is not a root, so both brackets vanish.
      have hbot' : rootSpace H (((-α : Weight K H L) : H → K) + (-β : Weight K H L)) = ⊥ := by
        have hrw : ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K) =
            -((α : H → K) + (β : H → K)) := by
          rw [Weight.coe_neg, Weight.coe_neg, neg_add]
        rw [hrw, rootSpace_neg_eq_bot_iff]
        exact hbot
      rw [hx.lie_eq_zero_of_rootSpace_add_eq_bot α β hbot,
        hx.lie_eq_zero_of_rootSpace_add_eq_bot (-α) (-β) hbot', map_zero]
    · -- The sum is a root: the two structure constants are negatives of each other.
      set γ : Weight K H L := ⟨(α : H → K) + β, hbot⟩
      have hγ : γ.IsNonZero := hzero
      have hαβ : (γ : H → K) = (α : H → K) + β := rfl
      have hnegαβ : ((-γ : Weight K H L) : H → K) =
          ((-α : Weight K H L) : H → K) + (-β : Weight K H L) := by
        rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
        abel
      have hsign : hx.structureConstant (-α) (-β) (-γ) hγ.neg hnegαβ =
          -hx.structureConstant α β γ hγ hαβ :=
        (hx.structureConstant_neg_neg_eq_neg_iff α β γ hα hβ hγ hαβ).2
          (hn α β γ hα hβ hγ hαβ)
      rw [hx.lie_eq_structureConstant_smul α β γ hγ hαβ,
        hx.lie_eq_structureConstant_smul (-α) (-β) (-γ) hγ.neg hnegαβ, hsign,
        map_smul, hωsum γ hγ hαβ]
      module

/-- **A Chevalley involution exists for an integrally normalised family.** If every genuine
root-sum structure constant of the normalised family `x` is `±(p + 1)`, then there is a Lie
algebra automorphism exchanging each root vector with the negative of its opposite, so `x` is the
root-vector family of a Chevalley system.

The automorphism is built from the weight-space decomposition of `L`: it is `-1` on the Cartan
subalgebra, and on the root space of `χ` it sends `v` to
`-(B(v, x (-χ)) / B(x χ, x (-χ))) • x (-χ)`. Only its existence is asserted, since
`TauCeti.IsChevalleySystem.unique` shows there is nothing to choose. -/
theorem exists_isChevalleySystem (hn : hx.IsChevalleyNormalized) :
    ∃ ω : L ≃ₗ⁅K⁆ L, IsChevalleySystem ω x := by
  classical
  set A : Weight K H L → Submodule K L := fun χ ↦ (rootSpace H χ).toSubmodule with hA
  have hAzero : ∀ χ : Weight K H L, χ.IsZero → A χ = H.toSubmodule := by
    intro χ hχ
    -- `Weight.IsZero` is the vanishing of the coercion, but only up to unfolding the definition.
    have hχcoe : (χ : H → K) = 0 := hχ
    rw [hA]
    simp only [hχcoe, rootSpace_zero_eq K L H]
    simp
  have hbij : Function.Bijective (DirectSum.coeLinearMap A) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top A).2
      ⟨LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' K H L),
        LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)⟩
  -- The component of the map on the weight space of `χ`.
  set g : ∀ χ : Weight K H L, A χ →ₗ[K] L := fun χ ↦
    if χ.IsNonZero then
      LinearMap.smulRight
        ((-(killingForm K L (x χ) (x (-χ)))⁻¹) •
          (((killingForm K L).flip (x (-χ))).comp (A χ).subtype)) (x (-χ))
    else -(A χ).subtype with hg
  set ω : L →ₗ[K] L := (DirectSum.toModule K _ L g).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hbij).symm.toLinearMap with hωdef
  -- The map restricts to `g χ` on the weight space of `χ`.
  have hmem : ∀ (χ : Weight K H L) (v : L) (hv : v ∈ A χ), ω v = g χ ⟨v, hv⟩ := by
    intro χ v hv
    have hsymm : (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hbij).symm v =
        DirectSum.lof K _ (fun χ ↦ A χ) χ ⟨v, hv⟩ := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply,
        DirectSum.coeLinearMap_lof]
    rw [hωdef]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, DirectSum.toModule_lof]
  -- On the zero weight space the map is `-1`.
  have hzero : ∀ (χ : Weight K H L), χ.IsZero → ∀ (v : L) (hv : v ∈ A χ), ω v = -v := by
    intro χ hχ v hv
    rw [hmem χ v hv, hg]
    simp only [ite_eq_right (fun h : χ.IsNonZero ↦ h hχ), LinearMap.neg_apply,
      Submodule.subtype_apply]
  have hcartan : ∀ h : H, ω (h : L) = -(h : L) := by
    intro h
    by_cases hbot : rootSpace H (0 : H → K) = ⊥
    · have hzero' : (h : L) = 0 := by
        have hmem' : (h : L) ∈ rootSpace H (0 : H → K) := by
          rw [rootSpace_zero_eq K L H]
          exact h.2
        rw [hbot] at hmem'
        simpa using hmem'
      rw [hzero', map_zero, neg_zero]
    · have hχ0 : (⟨(0 : H → K), hbot⟩ : Weight K H L).IsZero := rfl
      refine hzero _ hχ0 _ ?_
      rw [hAzero _ hχ0]
      exact h.2
  -- On the weight space of a root the map is the prescribed rescaling of the opposite root vector.
  have hnonzero : ∀ (χ : Weight K H L), χ.IsNonZero → ∀ (v : L) (hv : v ∈ A χ),
      ω v = (-(killingForm K L (x χ) (x (-χ)))⁻¹ * killingForm K L v (x (-χ))) • x (-χ) := by
    intro χ hχ v hv
    rw [hmem χ v hv, hg]
    simp only [ite_eq_left hχ, LinearMap.smulRight_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, smul_eq_mul]
    rfl
  have hωroot : ∀ χ : Weight K H L, χ.IsNonZero → ω (x χ) = -x (-χ) := by
    intro χ hχ
    have hkill : killingForm K L (x χ) (x (-χ)) ≠ 0 :=
      killingForm_ne_zero_of_mem_rootSpace hχ (hx.mem_rootSpace χ) (hx.ne_zero χ hχ)
        (hx.mem_rootSpace (-χ)) (hx.ne_zero (-χ) hχ.neg)
    rw [hnonzero χ hχ (x χ) (hx.mem_rootSpace χ), neg_mul, inv_mul_cancel₀ hkill, neg_one_smul]
  have hωmem : ∀ (χ : Weight K H L), χ.IsNonZero → ∀ (v : L) (hv : v ∈ A χ),
      ω v ∈ A (-χ) := by
    intro χ hχ v hv
    rw [hnonzero χ hχ v hv]
    exact Submodule.smul_mem _ _ (hx.mem_rootSpace (-χ))
  -- The bracket relation to be proved is symmetric in its two arguments.
  have hswap : ∀ v w : L, ω ⁅v, w⁆ = ⁅ω v, ω w⁆ → ω ⁅w, v⁆ = ⁅ω w, ω v⁆ := by
    intro v w h
    calc ω ⁅w, v⁆ = ω (-⁅v, w⁆) := by rw [lie_skew w v]
      _ = -ω ⁅v, w⁆ := map_neg _ _
      _ = -⁅ω v, ω w⁆ := by rw [h]
      _ = ⁅ω w, ω v⁆ := lie_skew (ω w) (ω v)
  -- The map respects the bracket, first on pairs of weight vectors and then everywhere.
  have hpair : ∀ (χ₁ χ₂ : Weight K H L) (v : L), v ∈ A χ₁ → ∀ w : L, w ∈ A χ₂ →
      ω ⁅v, w⁆ = ⁅ω v, ω w⁆ := by
    -- A Cartan element brackets with a weight vector through its weight.
    have hmix : ∀ (χ₁ χ₂ : Weight K H L), χ₁.IsZero → χ₂.IsNonZero → ∀ (v : L), v ∈ A χ₁ →
        ∀ (w : L), w ∈ A χ₂ → ω ⁅v, w⁆ = ⁅ω v, ω w⁆ := by
      intro χ₁ χ₂ hχ₁ hχ₂ v hv w hw
      have hvH : v ∈ H := by rwa [hAzero χ₁ hχ₁] at hv
      have hlie : ⁅v, w⁆ = (χ₂ : H → K) ⟨v, hvH⟩ • w :=
        lie_eq_smul_of_mem_rootSpace hw ⟨v, hvH⟩
      have hmem' : ω w ∈ rootSpace H ((-χ₂ : Weight K H L) : H → K) := hωmem χ₂ hχ₂ w hw
      have hstep : ⁅v, ω w⁆ = ((-χ₂ : Weight K H L) : H → K) ⟨v, hvH⟩ • ω w :=
        lie_eq_smul_of_mem_rootSpace hmem' ⟨v, hvH⟩
      rw [hlie, map_smul, hzero χ₁ hχ₁ v hv, neg_lie, hstep]
      simp
    intro χ₁ χ₂ v hv w hw
    by_cases hχ₁ : χ₁.IsNonZero
    · by_cases hχ₂ : χ₂.IsNonZero
      · -- Both are roots: rescale to the chosen root vectors and use the sign symmetry.
        obtain ⟨c, rfl⟩ : ∃ c : K, c • x χ₁ = v := by
          refine Submodule.mem_span_singleton.mp ?_
          rw [← hx.toSubmodule_rootSpace_eq_span χ₁ hχ₁]
          exact hv
        obtain ⟨d, rfl⟩ : ∃ d : K, d • x χ₂ = w := by
          refine Submodule.mem_span_singleton.mp ?_
          rw [← hx.toSubmodule_rootSpace_eq_span χ₂ hχ₂]
          exact hw
        rw [smul_lie, lie_smul, map_smul, map_smul, map_smul, map_smul, smul_lie, lie_smul,
          hx.map_lie_root_of_isChevalleyNormalized hn hχ₁ hχ₂ ω
            (fun γ hγ _ ↦ hωroot γ hγ) (hcartan (coroot χ₁)),
          hωroot χ₁ hχ₁, hωroot χ₂ hχ₂]
        simp
      · exact hswap _ _ (hmix χ₂ χ₁ (not_not.mp hχ₂) hχ₁ w hw v hv)
    · by_cases hχ₂ : χ₂.IsNonZero
      · exact hmix χ₁ χ₂ (not_not.mp hχ₁) hχ₂ v hv w hw
      · -- Both lie in the Cartan subalgebra, which is abelian.
        have hvH : v ∈ H := by rwa [hAzero χ₁ (not_not.mp hχ₁)] at hv
        have hwH : w ∈ H := by rwa [hAzero χ₂ (not_not.mp hχ₂)] at hw
        have hlie : ⁅v, w⁆ = 0 :=
          lie_cartan_cartan_eq_zero (⟨v, hvH⟩ : H) (⟨w, hwH⟩ : H)
        rw [hlie, map_zero, hzero χ₁ (not_not.mp hχ₁) v hv, hzero χ₂ (not_not.mp hχ₂) w hw,
          neg_lie, _root_.lie_neg, neg_neg, hlie]
  have htop : ⨆ χ : Weight K H L, A χ = ⊤ :=
    LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top' K H L)
  have hlie : ∀ v w : L, ω ⁅v, w⁆ = ⁅ω v, ω w⁆ := by
    -- Extend from weight vectors by linearity in each argument.
    have hright : ∀ (χ₁ : Weight K H L) (v : L), v ∈ A χ₁ → ∀ w : L, ω ⁅v, w⁆ = ⁅ω v, ω w⁆ := by
      intro χ₁ v hv w
      have hle : (⊤ : Submodule K L) ≤
          LinearMap.eqLocus (ω.comp (LieAlgebra.ad K L v))
            ((LieAlgebra.ad K L (ω v)).comp ω) := by
        rw [← htop]
        exact iSup_le fun χ₂ u hu ↦ hpair χ₁ χ₂ v hv u hu
      exact hle trivial
    intro v w
    have hle : (⊤ : Submodule K L) ≤
        LinearMap.eqLocus (ω.comp (LieAlgebra.ad K L w))
          ((LieAlgebra.ad K L (ω w)).comp ω) := by
      rw [← htop]
      exact iSup_le fun χ₁ u hu ↦ hswap u w (hright χ₁ u hu w)
    exact hswap w v (hle trivial)
  -- The map is an involution, hence bijective.
  have hinvol : Function.Involutive ω := by
    have hweight : ∀ (χ : Weight K H L) (v : L), v ∈ A χ → ω (ω v) = v := by
      intro χ v hv
      by_cases hχ : χ.IsNonZero
      · obtain ⟨c, rfl⟩ : ∃ c : K, c • x χ = v := by
          refine Submodule.mem_span_singleton.mp ?_
          rw [← hx.toSubmodule_rootSpace_eq_span χ hχ]
          exact hv
        rw [map_smul, hωroot χ hχ, map_smul, map_neg, hωroot (-χ) hχ.neg]
        simp
      · rw [hzero χ (not_not.mp hχ) v hv, map_neg, hzero χ (not_not.mp hχ) v hv, neg_neg]
    intro v
    have hle : (⊤ : Submodule K L) ≤ LinearMap.eqLocus (ω.comp ω) LinearMap.id := by
      rw [← htop]
      exact iSup_le fun χ u hu ↦ hweight χ u hu
    exact hle trivial
  refine ⟨LieEquiv.ofBijective ⟨ω, fun {v w} ↦ hlie v w⟩ hinvol.bijective, hx, fun α ↦ ?_⟩
  by_cases hα : α.IsNonZero
  · exact hωroot α hα
  · rw [hx.eq_zero_of_isZero α (not_not.mp hα),
      hx.eq_zero_of_isZero (-α) (not_not.mp hα).neg, map_zero, neg_zero]

end IsSl2System

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L}

/-- A Chevalley system is integrally normalised: the compatibility with `ω` forces every genuine
root-sum structure constant to be `±(p + 1)`. -/
theorem isChevalleyNormalized (hx : IsChevalleySystem ω x) :
    hx.toIsSl2System.IsChevalleyNormalized :=
  fun α β γ hα hβ hγ hαβ ↦ hx.structureConstant_eq_natCast_or_eq_neg_natCast α β γ hα hβ hγ hαβ

/-- **The Chevalley involution is unique.** Two Lie automorphisms exchanging each root vector of
the same normalised family with the negative of its opposite are equal: they agree on the root
vectors by hypothesis and on the Cartan subalgebra because both negate the coroots, and those
span `L`. -/
theorem unique {ω₁ ω₂ : L ≃ₗ⁅K⁆ L}
    (h₁ : IsChevalleySystem ω₁ x) (h₂ : IsChevalleySystem ω₂ x) : ω₁ = ω₂ := by
  have hle : (⊤ : Submodule K L) ≤
      LinearMap.eqLocus (ω₁ : L →ₗ[K] L) (ω₂ : L →ₗ[K] L) := by
    rw [← h₁.toIsSl2System.span_range_sup_toSubmodule_eq_top]
    refine sup_le (Submodule.span_le.2 ?_) fun h hh ↦ ?_
    · rintro _ ⟨α, rfl⟩
      exact (h₁.map_root α).trans (h₂.map_root α).symm
    · exact (h₁.map_cartan ⟨h, hh⟩).trans (h₂.map_cartan ⟨h, hh⟩).symm
  ext v
  exact hle trivial

end IsChevalleySystem

namespace IsSl2System

variable {x : Weight K H L → L} (hx : IsSl2System x)

/-- **Chevalley systems are the integrally normalised families.** A normalised family of root
vectors extends to a Chevalley system exactly when its genuine root-sum structure constants are
the Chevalley integers `±(p + 1)`, and the extending automorphism is then unique.

This turns the Chevalley involution from data that a consumer must supply into a property of the
structure constants that a consumer can check. -/
theorem isChevalleyNormalized_iff_exists_isChevalleySystem :
    hx.IsChevalleyNormalized ↔ ∃ ω : L ≃ₗ⁅K⁆ L, IsChevalleySystem ω x := by
  refine ⟨hx.exists_isChevalleySystem, ?_⟩
  rintro ⟨ω, hω⟩
  exact hω.isChevalleyNormalized

end IsSl2System

end TauCeti
