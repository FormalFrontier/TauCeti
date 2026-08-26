/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Normalizer
public import TauCeti.NumberTheory.HeckeRing.Multiplication

import Mathlib.Tactic.Group

/-!
# Hecke double cosets at a normalizing element

`GroupTheory/DoubleCoset/Normalizer.lean` collapses a double coset `ΓgΓ` to the single right
coset `Γg` when `g` normalizes `Γ`. This file draws the Hecke-ring consequences, for a Hecke
triple `(Δ, Γ, Γ)` and an `x : Δ` normalizing `Γ`:

* the underlying set of `HeckeCoset.mk Γ Γ x` is `Γx`, and so is the double coset of its chosen
  representative — the shape in which the slash sum of a double coset consumes a decomposition;
* the chosen representative again normalizes `Γ`, so the decomposition quotient
  `Γ ⧸ (Γ ∩ xΓx⁻¹)` is a subsingleton;
* consequently the basis elements multiply with no structure constant to count,
  `[ΓxΓ] · [ΓyΓ] = [Γ(xy)Γ]`, whenever `x` and `y` both normalize `Γ`.

The last statement is what lets a submonoid of the normalizer of `Γ` act on the Hecke ring
through its basis elements. For `Γ₁(N) ⊴ Γ₀(N)` it is the diamond direction of the `Γ₁(N)`
Hecke ring, in `HeckeRing/GL2/Gamma1/DiamondCosets.lean`.

## Main results

* `DoubleCoset.subsingleton_decompQuotient_of_mem_normalizer`: the decomposition quotient at a
  normalizing element is a subsingleton.
* `HeckeCoset.toSet_mk_eq_rightCoset_of_mem_normalizer` and
  `HeckeCoset.doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer`: the double coset of a
  normalizing element is the single right coset `Γx`, at `x` itself and at the chosen
  representative.
* `HeckeCosetModule.single_mul_single_of_mem_normalizer`: the product of the basis elements of
  two normalizing elements is the basis element of their product.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1.
-/

public section

open DoubleCoset MulOpposite

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ : Subgroup G} {g : G}

/-- **The decomposition quotient at a normalizing element is a subsingleton**: the stabilizer
`Γ ∩ gΓg⁻¹` is all of `Γ`. This is `subsingleton_decompQuotient_of_mem` with membership in `Γ`
weakened to membership in its normalizer. -/
lemma subsingleton_decompQuotient_of_mem_normalizer
    (hg : g ∈ Subgroup.normalizer (Γ : Set G)) : Subsingleton (DecompQuotient Γ Γ g) :=
  subsingleton_decompQuotient (Subgroup.conjAct_pointwise_smul_eq_self hg).ge

end DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G} {x y : Δ}

/-- **The double coset of a normalizing element is a single right coset**, `ΓxΓ = Γx`. -/
lemma toSet_mk_eq_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (mk Γ Γ x).toSet = op (x : G) • (Γ : Set G) :=
  (toSet_mk x).trans (DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer hx)

/-- The same collapse read at the chosen representative of `HeckeCoset.mk Γ Γ x`, which is the
shape a decomposition of a double coset into right cosets is stated in. -/
lemma doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    DoubleCoset.doubleCoset (((mk Γ Γ x).out : Δ) : G) Γ Γ = op (x : G) • (Γ : Set G) :=
  (eq_iff.mp (Quotient.out_eq (mk Γ Γ x))).trans
    (DoubleCoset.doubleCoset_eq_rightCoset_of_mem_normalizer hx)

/-- The chosen representative of `HeckeCoset.mk Γ Γ x` lies in the right coset `Γx`. -/
lemma rep_mk_mem_rightCoset_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (((mk Γ Γ x).rep : Δ) : G) ∈ op (x : G) • (Γ : Set G) :=
  toSet_mk_eq_rightCoset_of_mem_normalizer hx ▸ (mk Γ Γ x).rep_mem

/-- The chosen representative of `HeckeCoset.mk Γ Γ x` again normalizes `Γ`: it lies in `ΓxΓ`,
all of whose elements do. -/
lemma rep_mk_mem_normalizer_of_mem_normalizer
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    (((mk Γ Γ x).rep : Δ) : G) ∈ Subgroup.normalizer (Γ : Set G) :=
  DoubleCoset.mem_normalizer_of_mem_doubleCoset hx (toSet_mk x ▸ (mk Γ Γ x).rep_mem)

/-- **Every value of `HeckeCoset.mulMap` on two normalizing elements is the double coset of
their product**: writing each chosen representative as `a · x` with `a ∈ Γ` and pushing the
middle `Γ` factor across `x` — legitimate because `x` normalizes `Γ` — leaves `Γ · xy`. -/
lemma mulMap_rep_mk_eq_of_mem_normalizer [IsHeckeTriple Δ Γ Γ]
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G))
    (hy : (y : G) ∈ Subgroup.normalizer (Γ : Set G))
    (p : DecompQuotient Γ Γ (((mk Γ Γ x).rep : Δ) : G) ×
      DecompQuotient Γ Γ (((mk Γ Γ y).rep : Δ) : G)) :
    mulMap Γ Γ Γ (mk Γ Γ x).rep (mk Γ Γ y).rep p = mk Γ Γ (x * y) := by
  -- name the two representatives as `a x` and `b y`, so that the identity below is an identity
  -- between short words in six atoms
  obtain ⟨a, ha, hA⟩ : ∃ a ∈ Γ, (((mk Γ Γ x).rep : Δ) : G) = a * (x : G) :=
    ⟨_, (mem_rightCoset_iff _).mp (rep_mk_mem_rightCoset_of_mem_normalizer hx),
      (inv_mul_cancel_right _ _).symm⟩
  obtain ⟨b, hb, hB⟩ : ∃ b ∈ Γ, (((mk Γ Γ y).rep : Δ) : G) = b * (y : G) :=
    ⟨_, (mem_rightCoset_iff _).mp (rep_mk_mem_rightCoset_of_mem_normalizer hy),
      (inv_mul_cancel_right _ _).symm⟩
  -- the middle `Γ` factor, conjugated across `x`
  have hc : (x : G) * ((p.2.out : G) * b) * (x : G)⁻¹ ∈ Γ :=
    (Subgroup.mem_normalizer_iff.mp hx _).mp (Subgroup.mul_mem _ p.2.out.2 hb)
  -- the word identity, in six free atoms: quantifying over `u` and `v` keeps `group` away from
  -- the coset representatives, whose types are large
  have key₀ : ∀ u v : G, u * (a * (x : G)) * (v * (b * (y : G))) =
      u * a * ((x : G) * (v * b) * (x : G)⁻¹) * ((x : G) * (y : G)) * 1 := fun u v ↦ by group
  have key := key₀ (p.1.out : G) (p.2.out : G)
  rw [← hA, ← hB] at key
  rw [mulMap_eq_mk]
  exact mk_eq_mk_of_mem (g₂ := x * y) (DoubleCoset.mem_doubleCoset.mpr
    ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ p.1.out.2 ha) hc, 1, Subgroup.one_mem _, key⟩)

end HeckeCoset

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G} {x y : Δ}

/-- **The basis elements of two normalizing elements multiply**, `[ΓxΓ] · [ΓyΓ] = [Γ(xy)Γ]`,
over any coefficient semiring.

There is no structure constant to compute: both decomposition quotients are subsingletons, so
`multiplicity ≤ 1` is automatic, and every pair of representatives multiplies into the same
double coset. -/
theorem single_mul_single_of_mem_normalizer [IsHeckeTriple Δ Γ Γ] (R : Type*) [Semiring R]
    (hx : (x : G) ∈ Subgroup.normalizer (Γ : Set G))
    (hy : (y : G) ∈ Subgroup.normalizer (Γ : Set G)) :
    single R (HeckeCoset.mk Γ Γ x) 1 * single R (HeckeCoset.mk Γ Γ y) 1 =
      single R (HeckeCoset.mk Γ Γ (x * y)) 1 := by
  classical
  rw [mul_def]
  have := DoubleCoset.subsingleton_decompQuotient_of_mem_normalizer
    (HeckeCoset.rep_mk_mem_normalizer_of_mem_normalizer hx)
  have := DoubleCoset.subsingleton_decompQuotient_of_mem_normalizer
    (HeckeCoset.rep_mk_mem_normalizer_of_mem_normalizer hy)
  refine mul_single_single_of_mulMap_eq R _ _ _
    (HeckeCoset.mulMap_rep_mk_eq_of_mem_normalizer hx hy) ?_
  rw [DoubleCoset.multiplicity_def, Nat.card_eq_fintype_card]
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

end HeckeCosetModule

end
