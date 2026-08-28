/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic
public import TauCeti.NumberTheory.HeckeRing.Normalizer
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The diamond double cosets of the `Γ₁(N)` Hecke ring

The Hecke monoid `Δ₀(N)` asks its elements only to have a *unit* upper-left entry modulo `N`,
which is what puts all of `Γ₀(N)` inside it (`HeckeRing/GL2/Gamma1/Basic.lean`). This file takes
the resulting payoff: for `γ ∈ Γ₀(N)` the double coset `Γ₁(N) γ Γ₁(N)` is a basis element of the
Hecke ring `𝕋 Δ₀(N) Γ₁(N) ℤ`, it is a *single* right coset `Γ₁(N) γ` because `Γ₁(N)` is normal
in `Γ₀(N)`, it depends only on the lower-right entry `d ∈ (ZMod N)ˣ`, and the resulting map

`⟨·⟩ : (ZMod N)ˣ →* 𝕋 Δ₀(N) Γ₁(N) ℤ`

is an injective monoid homomorphism. So the diamond operators are not an extra structure bolted
onto the Hecke algebra: they are honest basis elements of it. That the endomorphism of
`M_k(Γ₁(N))` such a coset induces is the `⟨d⟩` of `ModularForms/DiamondOperators.lean` is the
companion statement, proved in `ModularForms/HeckeSlash/Diamond.lean`.

## Why the double coset collapses, and what that buys

`Γ₁(N)` is normal in `Γ₀(N)` (`CongruenceSubgroup.Gamma0_normalizes_Gamma1`), so `γ` lies in the
normalizer of the image of `Γ₁(N)` in `GL₂(ℚ)`. Everything below is then an instance of the
general theory of `HeckeRing/Normalizer.lean`, which collapses a double coset at a normalizing
element to a single right coset and draws the two consequences that drive this file.

* The double coset has a **single** right coset, so the slash operator attached to it is a
  one-term sum. That is the shape `heckeSlashSum` consumes, through the decomposition
  `doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets` stated at the chosen representative.
* Its decomposition quotients are subsingletons, so the structure constants of a product of two
  diamond cosets are at most `1`: the product of two diamond basis elements is the diamond basis
  element of the product. No counting is needed, which is exactly what distinguishes the
  diamonds from the `Tₚ`.

## Main definitions

* `HeckeRing.GL2.diamondCosetGamma1`: the double coset `Γ₁(N) γ Γ₁(N)` of `γ ∈ Γ₀(N)`.
* `HeckeRing.GL2.diamondHeckeElem` and `HeckeRing.GL2.diamondHeckeElemHom`: the diamond element
  `⟨d⟩` of the Hecke ring, and the monoid homomorphism `(ZMod N)ˣ →* 𝕋 Δ₀(N) Γ₁(N) ℤ` it forms.

## Main results

* `HeckeRing.GL2.diamondCosetGamma1_toSet_eq_rightCoset` and
  `HeckeRing.GL2.doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets`: the double coset is
  the single right coset `Γ₁(N) γ`, in the two spellings the Hecke machinery uses.
* `HeckeRing.GL2.diamondCosetGamma1_eq_iff`: the coset depends exactly on the lower-right entry.
* `HeckeRing.GL2.single_diamondCosetGamma1_mul_single_diamondCosetGamma1`: the basis elements
  multiply, `[Γ₁(N) γ₁ Γ₁(N)] · [Γ₁(N) γ₂ Γ₁(N)] = [Γ₁(N) γ₁γ₂ Γ₁(N)]`.
* `HeckeRing.GL2.diamondHeckeElemHom_injective`: the diamonds form a faithful copy of
  `(ZMod N)ˣ` inside the Hecke ring.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.2.
-/

public section

open Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset MulOpposite
open scoped MatrixGroups Pointwise HeckeCosetModule

namespace HeckeRing.GL2

variable {N : ℕ}

/-- **The diamond double coset** `Γ₁(N) · γ · Γ₁(N)` of an element `γ ∈ Γ₀(N)`, as an element of
the basis of the Hecke ring of the pair `(Γ₁(N), Δ₀(N))`.

It is indexed by an element of `Γ₀(N)` rather than by a unit of `ZMod N` because a double coset
is formed from a matrix; that it depends only on the lower-right entry is
`diamondCosetGamma1_eq_iff`, and `diamondHeckeElem` is the resulting unit-indexed element. -/
noncomputable def diamondCosetGamma1 (N : ℕ) (g : ↥(Gamma0 N)) :
    HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  HeckeCoset.mk _ _ ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_Delta0 N g⟩

/-- Defining equation for the sealed definition `diamondCosetGamma1`. -/
lemma diamondCosetGamma1_def (g : ↥(Gamma0 N)) :
    diamondCosetGamma1 N g = HeckeCoset.mk ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      ⟨mapGL ℚ (g : SL(2, ℤ)), mapGL_mem_Delta0 N g⟩ := (rfl)

/-- The underlying set of a diamond coset is the double coset of `γ`: `HeckeCoset.toSet_mk`
read at the sealed definition `diamondCosetGamma1`, whose body `simp` cannot unfold on its own.
The collapsed form is `diamondCosetGamma1_toSet_eq_rightCoset`. -/
lemma diamondCosetGamma1_toSet (g : ↥(Gamma0 N)) :
    (diamondCosetGamma1 N g).toSet =
      doubleCoset (mapGL ℚ (g : SL(2, ℤ))) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) :=
  HeckeCoset.toSet_mk _

/-- **The diamond double coset is a single right coset**, `Γ₁(N) γ Γ₁(N) = Γ₁(N) γ`, since `γ`
normalizes `Γ₁(N)`. -/
@[simp] lemma diamondCosetGamma1_toSet_eq_rightCoset (g : ↥(Gamma0 N)) :
    (diamondCosetGamma1 N g).toSet =
      op (mapGL ℚ (g : SL(2, ℤ))) • ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) :=
  HeckeCoset.toSet_mk_eq_rightCoset_of_mem_normalizer (mapGL_mem_normalizer_Gamma1_map ℚ g)

/-- The double coset of the chosen representative of `diamondCosetGamma1 N g`, presented as the
one-term union of right cosets — the shape the slash sum of
`ModularForms/HeckeSlash/Independence.lean` consumes. -/
theorem doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets (g : ↥(Gamma0 N)) :
    doubleCoset ((diamondCosetGamma1 N g).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      ⋃ _ : Unit, op (mapGL ℚ (g : SL(2, ℤ))) •
        ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  rw [Set.iUnion_const]
  exact HeckeCoset.doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer
    (mapGL_mem_normalizer_Gamma1_map ℚ g)

/-- The diamond coset of the identity is the identity double coset `Γ₁(N) · 1 · Γ₁(N)`. -/
@[simp] theorem diamondCosetGamma1_one : diamondCosetGamma1 N 1 = 1 := by
  have hone : mapGL ℚ ((1 : ↥(Gamma0 N)) : SL(2, ℤ)) = 1 := by
    rw [Subgroup.coe_one, map_one]
  rw [diamondCosetGamma1_def, HeckeCoset.one_def]
  exact congrArg (HeckeCoset.mk _ _) (Subtype.ext hone)

/-- **The diamond coset sees exactly the lower-right entry.** Two elements of `Γ₀(N)` give the
same double coset precisely when they have the same image in `(ZMod N)ˣ`; the forward direction
uses that `mapGL ℚ` is injective, so a rational coincidence is an integral one. -/
@[simp] theorem diamondCosetGamma1_eq_iff {g₁ g₂ : ↥(Gamma0 N)} :
    diamondCosetGamma1 N g₁ = diamondCosetGamma1 N g₂ ↔
      (Gamma0Map N).toHomUnits g₁ = (Gamma0Map N).toHomUnits g₂ := by
  rw [← HeckeCoset.toSet_injective.eq_iff, diamondCosetGamma1_toSet_eq_rightCoset,
    diamondCosetGamma1_toSet_eq_rightCoset, rightCoset_eq_iff]
  constructor
  · intro hmem
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hmem
    have hσ' : σ = (g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ))⁻¹ :=
      (mapGL_inj (S := ℚ) _ _).mp (by rw [hσeq, map_mul, map_inv])
    have heq := (mul_inv_mem_Gamma1_iff_Gamma0Map_eq g₂ g₁).mp (by rwa [hσ'] at hσ)
    refine Units.ext ?_
    rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits]
    exact heq.symm
  · intro heq
    refine Subgroup.mem_map.mpr ⟨(g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ))⁻¹,
      (mul_inv_mem_Gamma1_iff_Gamma0Map_eq g₂ g₁).mpr (congrArg Units.val heq.symm), ?_⟩
    rw [map_mul, map_inv]

section Product

variable [NeZero N] (g₁ g₂ : ↥(Gamma0 N))

/-- **The diamond basis elements multiply**: `[Γ₁(N) γ₁ Γ₁(N)] · [Γ₁(N) γ₂ Γ₁(N)] =
[Γ₁(N) γ₁γ₂ Γ₁(N)]` in the Hecke ring, over any coefficient semiring.

This is `HeckeCosetModule.single_mul_single_of_mem_normalizer` at the two `Γ₀(N)` matrices,
which normalize `Γ₁(N)`; only the identification of the two products of monoid elements is left
to do here. -/
@[simp] theorem single_diamondCosetGamma1_mul_single_diamondCosetGamma1 (R : Type*)
    [Semiring R] :
    HeckeCosetModule.single R (diamondCosetGamma1 N g₁) 1 *
        HeckeCosetModule.single R (diamondCosetGamma1 N g₂) 1 =
      HeckeCosetModule.single R (diamondCosetGamma1 N (g₁ * g₂)) 1 := by
  have hprod : mapGL ℚ (g₁ : SL(2, ℤ)) * mapGL ℚ (g₂ : SL(2, ℤ)) =
      mapGL ℚ ((g₁ * g₂ : ↥(Gamma0 N)) : SL(2, ℤ)) := by
    rw [Subgroup.coe_mul, map_mul]
  have hcoset : HeckeCoset.mk ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      ((⟨mapGL ℚ (g₁ : SL(2, ℤ)), mapGL_mem_Delta0 N g₁⟩ : ↥(Delta0 N)) *
        ⟨mapGL ℚ (g₂ : SL(2, ℤ)), mapGL_mem_Delta0 N g₂⟩) = diamondCosetGamma1 N (g₁ * g₂) :=
    congrArg (HeckeCoset.mk _ _) (Subtype.ext hprod)
  rw [← hcoset]
  exact HeckeCosetModule.single_mul_single_of_mem_normalizer R
    (mapGL_mem_normalizer_Gamma1_map ℚ g₁) (mapGL_mem_normalizer_Gamma1_map ℚ g₂)

end Product

/-- The diamond element `⟨d⟩` of the Hecke ring, for `d : (ZMod N)ˣ`: the basis element of the
double coset of any `Γ₀(N)` matrix with lower-right entry `d`. Such a matrix exists by
`CongruenceSubgroup.Gamma0Map_toHomUnits_surjective`, and `diamondCosetGamma1_eq_iff` makes the
choice immaterial — `diamondHeckeElem_eq_single` is the resulting evaluation rule, through which
every computation goes. -/
noncomputable def diamondHeckeElem (N : ℕ) (d : (ZMod N)ˣ) :
    𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ :=
  HeckeCosetModule.single ℤ
    (diamondCosetGamma1 N (Gamma0Map_toHomUnits_surjective d).choose) 1

/-- The diamond element is computed at *any* representative with the right lower-right entry.
Not `@[simp]`: the representative `g` occurs only in the hypothesis and the right-hand side,
so `simp` cannot infer it. -/
theorem diamondHeckeElem_eq_single {d : (ZMod N)ˣ} (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) :
    diamondHeckeElem N d = HeckeCosetModule.single ℤ (diamondCosetGamma1 N g) 1 :=
  congrArg (HeckeCosetModule.single ℤ · 1) (diamondCosetGamma1_eq_iff.mpr
    ((Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm))

variable [NeZero N]

/-- **The diamonds inside the Hecke ring.** The map `d ↦ ⟨d⟩` is a monoid homomorphism
`(ZMod N)ˣ →* 𝕋 Δ₀(N) Γ₁(N) ℤ`: this is the sense in which the diamond operators live in the
Hecke algebra of the pair `(Γ₁(N), Δ₀(N))` rather than beside it. -/
noncomputable def diamondHeckeElemHom (N : ℕ) [NeZero N] :
    (ZMod N)ˣ →* 𝕋 (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ℤ where
  toFun := diamondHeckeElem N
  map_one' := by
    rw [diamondHeckeElem_eq_single 1 (map_one _), diamondCosetGamma1_one,
      ← HeckeCosetModule.one_def]
  map_mul' d₁ d₂ := by
    obtain ⟨g₁, hg₁⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₁
    obtain ⟨g₂, hg₂⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₂
    rw [diamondHeckeElem_eq_single (g₁ * g₂) (by rw [map_mul, hg₁, hg₂]),
      diamondHeckeElem_eq_single g₁ hg₁, diamondHeckeElem_eq_single g₂ hg₂]
    exact (single_diamondCosetGamma1_mul_single_diamondCosetGamma1 g₁ g₂ ℤ).symm

@[simp] lemma diamondHeckeElemHom_apply (d : (ZMod N)ˣ) :
    diamondHeckeElemHom N d = diamondHeckeElem N d := (rfl)

/-- **The diamonds are a faithful copy of `(ZMod N)ˣ` in the Hecke ring.** Distinct units give
distinct double cosets (`diamondCosetGamma1_eq_iff`), hence distinct basis elements. -/
theorem diamondHeckeElemHom_injective : Function.Injective (diamondHeckeElemHom N) := by
  classical
  intro d₁ d₂ h
  obtain ⟨g₁, hg₁⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₂
  rw [diamondHeckeElemHom_apply, diamondHeckeElemHom_apply,
    diamondHeckeElem_eq_single g₁ hg₁, diamondHeckeElem_eq_single g₂ hg₂] at h
  have hval := congrArg (fun f ↦ f (diamondCosetGamma1 N g₁)) h
  rw [HeckeCosetModule.single_apply, HeckeCosetModule.single_apply, ite_eq_left rfl] at hval
  rw [← hg₁, ← hg₂, ← diamondCosetGamma1_eq_iff]
  by_contra hne
  exact one_ne_zero (hval.trans (ite_eq_right fun hEq ↦ hne hEq.symm))

end HeckeRing.GL2

end
