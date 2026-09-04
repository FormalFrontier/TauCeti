/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Cusps
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Holomorphic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Independence

/-!
# The twisted slash sum descends to the nebentypus character spaces

`HeckeSlash/ModularForm.lean` carries the *unweighted* slash sum from functions to
`ModularForm` and `CuspForm`, and bundles it as a `Module.End ℂ`. This file is the
nebentypus-twisted counterpart, and it lands on a different carrier.

## Why the carrier is the character space

The unweighted sum is invariant for the level it is taken at, so it acts on all of
`ModularForm (G.map (mapGL ℝ)) k`. The twisted sum is not: what is proved is that it preserves
the `χ`-eigenspace (`twistedHeckeSlashSum_mem_functionCharSpace`), which is what the weighting
buys. Whether that eigenspace is the largest subspace preserved is not established here and is
not needed. So the operators here are endomorphisms of
`modFormCharSpace k χ` and `cuspFormCharSpace k χ`, not of the ambient spaces, and the
underlying `ModularForm` is built only for a form already known to lie in the character space.

Invariance for `Γ₁(N)` is read off that same membership: a `Γ₁(N)` matrix lies in `Γ₀(N)` with
lower-right entry `1`, so the character factor it contributes is `χ 1 = 1` and the nebentypus
relation degenerates to plain invariance. Holomorphy is
`mdifferentiable_twistedHeckeSlashSum`, and the two cusp conditions are
`isBoundedAt_twistedHeckeSlashSum` and `isZeroAt_twistedHeckeSlashSum`. As in the untwisted
file the cusp-form case is *derived* from the modular-form one, adding only the vanishing
field, so neither invariance nor holomorphy is proved twice.

## Main definitions

* `HeckeRing.GL2.twistedHeckeSlashModularFormCharEnd`: the twisted operator on
  `modFormCharSpace k χ`.
* `HeckeRing.GL2.twistedHeckeSlashCuspFormCharEnd`: the twisted operator on
  `cuspFormCharSpace k χ` — the statement that the twisted action preserves cuspidality.

## Main results

* `HeckeRing.GL2.coe_twistedHeckeSlashModularFormCharEnd`,
  `HeckeRing.GL2.coe_twistedHeckeSlashCuspFormCharEnd`: both are `twistedHeckeSlashSum` on
  underlying functions.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, file
`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean` lines 166-257, where the
same construction appears as `nebentypusHeckeOpModularForm`, `nebentypusHeckeOp` and
`nebentypusHeckeOpLinear`. The names here follow this repository's `twistedHeckeSlashSum`
prefix instead, the analytic inputs are the reusable statements of the two sibling modules
rather than inlined arguments, and the cusp-form operator is new.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4 and §4.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Manifold Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
  (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))

variable [NeZero N]

-- The enumeration `∑` needs, supplied exactly as in `HeckeSlash/Nebentypus/Independence.lean`
-- so that the sums are the same term. Taken as an attribute rather than a fresh anonymous
-- instance: two sibling modules declaring one independently collide on its generated name when
-- a third imports both.
attribute [local instance] Fintype.ofFinite

/-- **A `χ`-invariant function has `Γ₁(N)`-invariant twisted slash sum.** A `Γ₁(N)` matrix lies
in `Γ₀(N)` with lower-right entry `1`, so the character factor the nebentypus relation
contributes is `χ 1 = 1` and the relation degenerates to plain invariance. This is the field
`slash_action_eq'` of every bundled form below. -/
private lemma twistedHeckeSlashSum_slash_eq_of_mem_Gamma1 {f : ℍ → ℂ}
    (hf : f ∈ functionCharSpace k χ) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    twistedHeckeSlashSum k χ D f ∣[k] γ = twistedHeckeSlashSum k χ D f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  have hσ₀ : σ ∈ Gamma0 N := Gamma1_in_Gamma0 N hσ
  have hone : (Gamma0Map N).toHomUnits ⟨σ, hσ₀⟩ = 1 :=
    Units.ext ((Gamma1_mem N σ).mp hσ).2.1
  have hrel := (mem_functionCharSpace_iff k χ _).mp
    (twistedHeckeSlashSum_mem_functionCharSpace k χ D f hf) ⟨σ, hσ₀⟩
  rwa [hone, map_one, Units.val_one, one_smul] at hrel

/-- **The twisted double coset acting on a modular form of the character space.** Invariance is
`twistedHeckeSlashSum_slash_eq_of_mem_Gamma1`, holomorphy is
`mdifferentiable_twistedHeckeSlashSum`, and boundedness at the cusps is
`isBoundedAt_twistedHeckeSlashSum`. The public interface is the bundled
`twistedHeckeSlashModularFormCharEnd`. -/
private noncomputable def twistedHeckeSlashModularForm
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := twistedHeckeSlashSum k χ D (⇑f)
  slash_action_eq' _ hγ := twistedHeckeSlashSum_slash_eq_of_mem_Gamma1 k χ D
    ((coe_mem_functionCharSpace_iff k χ f).mpr hf) hγ
  holo' := mdifferentiable_twistedHeckeSlashSum k χ D (ModularFormClass.holo f)
  bdd_at_cusps' hc :=
    isBoundedAt_twistedHeckeSlashSum k χ D (fun _ h ↦ f.bdd_at_cusps' h) hc

private lemma coe_twistedHeckeSlashModularForm
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    ⇑(twistedHeckeSlashModularForm k χ D f hf) = twistedHeckeSlashSum k χ D (⇑f) := (rfl)

/-- **The twisted operator stays in the character space.** This is
`twistedHeckeSlashSum_mem_functionCharSpace` read back through the bridge
`coe_mem_functionCharSpace_iff`. -/
private lemma twistedHeckeSlashModularForm_mem
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ modFormCharSpace k χ) :
    twistedHeckeSlashModularForm k χ D f hf ∈ modFormCharSpace k χ :=
  (coe_mem_functionCharSpace_iff k χ _).mp
    (twistedHeckeSlashSum_mem_functionCharSpace k χ D (⇑f)
      ((coe_mem_functionCharSpace_iff k χ f).mpr hf))

/-- **The twisted double coset acting on a cusp form of the character space** — the twisted
action preserves cuspidality. Only the vanishing field is new: invariance and holomorphy come
from `twistedHeckeSlashModularForm` at the underlying modular form, so neither is proved
twice. The hypothesis transports across the coercion by `coe_mem_modFormCharSpace_iff`. -/
private noncomputable def twistedHeckeSlashCuspForm
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  { twistedHeckeSlashModularForm k χ D (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      ((coe_mem_modFormCharSpace_iff k χ f).mpr hf) with
    zero_at_cusps' := fun {_} hc ↦
      isZeroAt_twistedHeckeSlashSum k χ D (fun _ h ↦ f.zero_at_cusps' h) hc }

private lemma coe_twistedHeckeSlashCuspForm
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormCharSpace k χ) :
    ⇑(twistedHeckeSlashCuspForm k χ D f hf) = twistedHeckeSlashSum k χ D (⇑f) :=
  coe_twistedHeckeSlashModularForm k χ D (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    ((coe_mem_modFormCharSpace_iff k χ f).mpr hf)

/-- The twisted operator on a cusp form stays in the cusp-form character space, by
`twistedHeckeSlashModularForm_mem` read back across `coe_mem_modFormCharSpace_iff`. -/
private lemma twistedHeckeSlashCuspForm_mem
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormCharSpace k χ) :
    twistedHeckeSlashCuspForm k χ D f hf ∈ cuspFormCharSpace k χ :=
  (coe_mem_modFormCharSpace_iff k χ _).mp
    (twistedHeckeSlashModularForm_mem k χ D (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      ((coe_mem_modFormCharSpace_iff k χ f).mpr hf))

/-- **The twisted double coset as a `ℂ`-linear endomorphism of `modFormCharSpace k χ`.** This is
the form the twisted Hecke operators are consumed in: bundling is what lets them compose and
later carry the ring structure of `Nebentypus/CharRing.lean`. -/
noncomputable def twistedHeckeSlashModularFormCharEnd :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f := ⟨twistedHeckeSlashModularForm k χ D (f : ModularForm _ k) f.2,
    twistedHeckeSlashModularForm_mem k χ D (f : ModularForm _ k) f.2⟩
  map_add' f g := by
    refine Subtype.ext (ModularForm.ext fun τ ↦ ?_)
    simp [coe_twistedHeckeSlashModularForm, twistedHeckeSlashSum_add]
  map_smul' c f := by
    refine Subtype.ext (ModularForm.ext fun τ ↦ ?_)
    simp [coe_twistedHeckeSlashModularForm, twistedHeckeSlashSum_smul]

/-- **The twisted double coset as a `ℂ`-linear endomorphism of `cuspFormCharSpace k χ`** — the
twisted action preserves cuspidality. -/
noncomputable def twistedHeckeSlashCuspFormCharEnd :
    Module.End ℂ (cuspFormCharSpace k χ) where
  toFun f := ⟨twistedHeckeSlashCuspForm k χ D (f : CuspForm _ k) f.2,
    twistedHeckeSlashCuspForm_mem k χ D (f : CuspForm _ k) f.2⟩
  map_add' f g := by
    refine Subtype.ext (CuspForm.ext fun τ ↦ ?_)
    simp [coe_twistedHeckeSlashCuspForm, twistedHeckeSlashSum_add]
  map_smul' c f := by
    refine Subtype.ext (CuspForm.ext fun τ ↦ ?_)
    simp [coe_twistedHeckeSlashCuspForm, twistedHeckeSlashSum_smul]

/-- The endomorphism is `twistedHeckeSlashSum` on underlying functions. -/
@[simp] lemma coe_twistedHeckeSlashModularFormCharEnd (f : modFormCharSpace k χ) :
    ⇑((twistedHeckeSlashModularFormCharEnd k χ D f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      twistedHeckeSlashSum k χ D (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  coe_twistedHeckeSlashModularForm k χ D (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) f.2

/-- The cusp-form endomorphism is `twistedHeckeSlashSum` on underlying functions. -/
@[simp] lemma coe_twistedHeckeSlashCuspFormCharEnd (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharEnd k χ D f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      twistedHeckeSlashSum k χ D (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  coe_twistedHeckeSlashCuspForm k χ D (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) f.2

/-- **The twisted operator on modular forms is the weighted sum over any decomposition of the
double coset into right cosets**: if the right cosets `Γ₀(N) aᵢ` are pairwise distinct and cover
the double coset, then the operator is
`∑ᵢ delta0NebentypusChar N χ ⟨aᵢ, _⟩ • (f ∣[k] aᵢ)`.

The weight is not `χ` applied to `aᵢ` — `aᵢ : GL (Fin 2) ℚ` is not in the domain of `χ`. It is
`delta0NebentypusChar`, which reads `χ` off the upper-left unit of the `Δ₀(N)` witness that the
cover hypothesis supplies for `aᵢ` through `mem_Delta0_of_cover`.

So the operator is attached to the double coset, not to the representatives
`twistedHeckeSlashSum` happens to choose; the choice-independence itself is
`twistedHeckeSlashSum_eq_sum_of_rightCosets` (`Nebentypus/Independence.lean`). This is the twisted
counterpart of `coe_heckeSlashModularFormEnd_eq_sum`. -/
lemma coe_twistedHeckeSlashModularFormCharEnd_eq_sum {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ i, MulOpposite.op (a i) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
        Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
    (f : modFormCharSpace k χ) :
    ⇑((twistedHeckeSlashModularFormCharEnd k χ D f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ∑ i, (delta0NebentypusChar N χ ⟨a i, mem_Delta0_of_cover D hcover i⟩ : ℂ) •
        (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] a i) :=
  (coe_twistedHeckeSlashModularFormCharEnd k χ D f).trans
    (twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D a hcover hinj _
      ((coe_mem_functionCharSpace_iff k χ _).mpr f.2))

/-- **The twisted operator on cusp forms is the weighted sum over any decomposition of the double
coset into right cosets**, exactly as for modular forms. -/
lemma coe_twistedHeckeSlashCuspFormCharEnd_eq_sum {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ)
    (hcover : doubleCoset (D.out : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ i, MulOpposite.op (a i) • (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) :
        Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) •
      (((Gamma0 N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set (GL (Fin 2) ℚ)))
    (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharEnd k χ D f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ∑ i, (delta0NebentypusChar N χ ⟨a i, mem_Delta0_of_cover D hcover i⟩ : ℂ) •
        (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] a i) :=
    by
  -- The character-space membership is the modular-form one at the underlying form; the two
  -- coercions to `ℍ → ℂ` agree, so naming the statement is what makes them match.
  have hmem : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ functionCharSpace k χ :=
    (coe_mem_functionCharSpace_iff k χ ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
      ((coe_mem_modFormCharSpace_iff k χ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr f.2)
  exact (coe_twistedHeckeSlashCuspFormCharEnd k χ D f).trans
    (twistedHeckeSlashSum_eq_sum_of_rightCosets k χ D a hcover hinj _ hmem)

end HeckeRing.GL2

end
