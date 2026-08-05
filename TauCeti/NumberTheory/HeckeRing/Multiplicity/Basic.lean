/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic

/-!
# Hecke rings: the multiplicity function

Shimura's multiplicity (Proposition 3.2 of [Shimura][shimura1971]) counts, for double cosets
`Γ₁gΓ₂`, `Γ₂hΓ₃` and `Γ₁dΓ₃`, the pairs of left-coset representatives `(σᵢ, τⱼ)` with
`σᵢ g τⱼ h Γ₃ = d Γ₃`. These natural numbers are the structure constants of the Hecke product
defined in later files: the diagonal case `Γ₁ = Γ₂ = Γ₃` gives the multiplication of the Hecke
ring, and the general case gives the composition of Hecke coset modules between different
levels. This file defines the multiplicity, the map `mulMap` sending a pair of representatives
to the mixed double coset of their product, and the uniqueness lemmas for the fibres of the
multiplicity.

Vendored from the in-review mathlib4 PR
[#41254](https://github.com/leanprover-community/mathlib4/pull/41254) (Chris Birkbeck), per the
ModularForms roadmap's dependency policy; migrate to Mathlib and delete this file when that
stack merges.

## Main definitions

* `DoubleCoset.multiplicity`: Shimura's multiplicity, a natural number structure constant.
* `HeckeCoset.mulMap`: the double coset `H₁ (σᵢ g₁ τⱼ g₂) H₃` of a pair of coset
  representatives.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open Subgroup
open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- The decomposition quotient collapses when `Γ₁` lies in the conjugate `gΓ₂g⁻¹`. -/
lemma subsingleton_decompQuotient {Γ₁ Γ₂ : Subgroup G} {g : G}
    (h : Γ₁ ≤ ConjAct.toConjAct g • Γ₂) : Subsingleton (DecompQuotient Γ₁ Γ₂ g) := by
  -- unfold the reducible `DecompQuotient` so the subgroup rewrite below applies
  change Subsingleton (Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁)
  rw [Subgroup.subgroupOf_eq_top.mpr h]
  exact QuotientGroup.subsingleton_quotient_top

/-- The diagonal decomposition quotient of an element of `Γ` is a singleton. -/
lemma subsingleton_decompQuotient_of_mem {Γ : Subgroup G} {g : G} (hg : g ∈ Γ) :
    Subsingleton (DecompQuotient Γ Γ g) :=
  subsingleton_decompQuotient
    (Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hg)).ge

/-- The left cosets `σᵢ g Γ₂` of the decomposition of `Γ₁gΓ₂` are pairwise distinct: the map
`i ↦ σᵢ g Γ₂` into `G ⧸ Γ₂` is injective. -/
lemma mk_out_mul_injective (Γ₁ Γ₂ : Subgroup G) (g : G) :
    Function.Injective fun i : DecompQuotient Γ₁ Γ₂ g ↦ (((i.out : G) * g : G) : G ⧸ Γ₂) := by
  intro i j hij
  simp only [QuotientGroup.eq] at hij
  rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv]
  simpa [mul_assoc] using hij

/-- Shimura's multiplicity (Proposition 3.2 of [Shimura][shimura1971]): the number of pairs
`(i, j)` of coset representatives such that `σᵢ g τⱼ h Γ₃ = d Γ₃`. The diagonal case
`Γ₁ = Γ₂ = Γ₃` gives the structure constants of the Hecke ring.

On an infinite fibre `Nat.card` returns `0` — the standard junk-value convention, as for
`Module.finrank`. For a Hecke triple the decomposition quotients are finite (the
`IsHeckeTriple` instances provide `Fintype`), which is the only case the theory uses: the
support results assume finite decomposition quotients, while the identity-coset results
(`Multiplicity/Unit.lean`) prove their fibres are singletons directly and need no finiteness. -/
noncomputable def multiplicity (Γ₁ Γ₂ Γ₃ : Subgroup G) (g h d : G) : ℕ :=
  Nat.card {p : DecompQuotient Γ₁ Γ₂ g × DecompQuotient Γ₂ Γ₃ h |
    ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)}

/-- The defining formula of the multiplicity: the characterisation through which all
computations with `multiplicity` go, keeping the definition itself opaque. -/
theorem multiplicity_def (Γ₁ Γ₂ Γ₃ : Subgroup G) (g h d : G) :
    multiplicity Γ₁ Γ₂ Γ₃ g h d =
      Nat.card {p : DecompQuotient Γ₁ Γ₂ g × DecompQuotient Γ₂ Γ₃ h |
        ((p.1.out : G) * g * ((p.2.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)} :=
  (rfl)

/-- When the first components of two pairs in the fibre of the multiplicity agree, the second
components agree. -/
lemma snd_eq_of_fst_eq {Γ₁ Γ₂ Γ₃ : Subgroup G} {g h d : G} {i : DecompQuotient Γ₁ Γ₂ g}
    {j₁ j₂ : DecompQuotient Γ₂ Γ₃ h}
    (h₁ : ((i.out : G) * g * ((j₁.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃))
    (h₂ : ((i.out : G) * g * ((j₂.out : G) * h) : G ⧸ Γ₃) = (d : G ⧸ Γ₃)) :
    j₁ = j₂ := by
  refine mk_out_mul_injective Γ₂ Γ₃ h ?_
  have h := h₁.trans h₂.symm
  rw [QuotientGroup.eq] at h ⊢
  simpa [mul_assoc] using h

/-- When the common second component of two pairs in the fibre of the multiplicity satisfies
`τⱼ h ∈ Γ₂`, the first components agree. -/
lemma fst_eq_of_mul_snd_mem {Γ₁ Γ₂ : Subgroup G} {g h d : G} {i₁ i₂ : DecompQuotient Γ₁ Γ₂ g}
    {j : DecompQuotient Γ₂ Γ₂ h} (hj : (j.out : G) * h ∈ Γ₂)
    (h₁ : ((i₁.out : G) * g * ((j.out : G) * h) : G ⧸ Γ₂) = (d : G ⧸ Γ₂))
    (h₂ : ((i₂.out : G) * g * ((j.out : G) * h) : G ⧸ Γ₂) = (d : G ⧸ Γ₂)) :
    i₁ = i₂ := by
  rw [QuotientGroup.mk_mul_of_mem _ hj] at h₁ h₂
  exact mk_out_mul_injective Γ₁ Γ₂ g (h₁.trans h₂.symm)

end DoubleCoset

namespace HeckeCoset

open DoubleCoset

variable {G : Type*} [Group G] {Δ : Submonoid G}

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the mixed double coset
`H₁ (σᵢ g₁ τⱼ g₂) H₃` of their product, from bare containments `H₁ ≤ Δ` and `H₂ ≤ Δ`; the
Hecke-triple wrapper is `mulMap`. -/
noncomputable def mulMapOf {H₁ H₂ : Subgroup G} (h₁ : H₁.toSubmonoid ≤ Δ)
    (h₂ : H₂.toSubmonoid ≤ Δ) (H₃ : Subgroup G) (g₁ g₂ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)) : HeckeCoset Δ H₁ H₃ :=
  mk H₁ H₃ ⟨(p.1.out : G) * g₁ * ((p.2.out : G) * g₂),
    Δ.mul_mem (Δ.mul_mem (h₁ p.1.out.2) g₁.2) (Δ.mul_mem (h₂ p.2.out.2) g₂.2)⟩

/-- The map sending a pair of coset representatives `(σᵢ, τⱼ)` to the mixed double coset
`H₁ (σᵢ g₁ τⱼ g₂) H₃` of their product: the Hecke-triple form of `mulMapOf`. -/
noncomputable def mulMap (H₁ H₂ H₃ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g₁ g₂ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)) : HeckeCoset Δ H₁ H₃ :=
  mulMapOf (IsHeckeTriple.left_le (H₂ := H₂)) (IsHeckeTriple.right_le (H₁ := H₁)) H₃ g₁ g₂ p

/-- `mulMap` is `mulMapOf` at the containments provided by the Hecke triple. -/
theorem mulMap_eq_mulMapOf (H₁ H₂ H₃ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g₁ g₂ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)) :
    mulMap H₁ H₂ H₃ g₁ g₂ p =
      mulMapOf (IsHeckeTriple.left_le (H₂ := H₂)) (IsHeckeTriple.right_le (H₁ := H₁))
        H₃ g₁ g₂ p :=
  (rfl)

/-- The value of `mulMapOf` on a pair of representatives, as an explicit `mk`: the
characterisation through which computations with `mulMapOf` go, keeping the definition itself
opaque. -/
theorem mulMapOf_eq_mk {H₁ H₂ : Subgroup G} (h₁ : H₁.toSubmonoid ≤ Δ)
    (h₂ : H₂.toSubmonoid ≤ Δ) (H₃ : Subgroup G) (g₁ g₂ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)) :
    mulMapOf h₁ h₂ H₃ g₁ g₂ p =
      mk H₁ H₃ ⟨(p.1.out : G) * g₁ * ((p.2.out : G) * g₂),
        Δ.mul_mem (Δ.mul_mem (h₁ p.1.out.2) g₁.2) (Δ.mul_mem (h₂ p.2.out.2) g₂.2)⟩ :=
  (rfl)

/-- The value of `mulMap` on a pair of representatives: the Hecke-triple form of
`mulMapOf_eq_mk`. -/
theorem mulMap_eq_mk (H₁ H₂ H₃ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g₁ g₂ : Δ)
    (p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)) :
    mulMap H₁ H₂ H₃ g₁ g₂ p =
      mk H₁ H₃ ⟨(p.1.out : G) * g₁ * ((p.2.out : G) * g₂),
        Δ.mul_mem (Δ.mul_mem (IsHeckeTriple.mem_of_mem_left H₂ p.1.out.2) g₁.2)
          (Δ.mul_mem (IsHeckeTriple.mem_of_mem_right H₁ p.2.out.2) g₂.2)⟩ :=
  mulMapOf_eq_mk _ _ H₃ g₁ g₂ p

/-- If `σᵢ g₁ τⱼ g₂ H₃ = d H₃` then the double coset of `σᵢ g₁ τⱼ g₂` equals that of `d`,
from bare containments. -/
lemma mulMapOf_eq_of_mk_eq {H₁ H₂ H₃ : Subgroup G} {h₁ : H₁.toSubmonoid ≤ Δ}
    {h₂ : H₂.toSubmonoid ≤ Δ} {g₁ g₂ d : Δ}
    {p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)}
    (h : ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂) : G ⧸ H₃) = ((d : G) : G ⧸ H₃)) :
    mulMapOf h₁ h₂ H₃ g₁ g₂ p = mk H₁ H₃ d := by
  rw [QuotientGroup.eq] at h
  rw [mulMapOf_eq_mk]
  exact HeckeCoset.mk_eq_mk_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨1, H₁.one_mem, _, H₃.inv_mem h, by rw [one_mul, mul_inv_rev, inv_inv, mul_inv_cancel_left]⟩)

/-- If `σᵢ g₁ τⱼ g₂ H₃ = d H₃` then the double coset of `σᵢ g₁ τⱼ g₂` equals that of `d`:
the Hecke-triple form of `mulMapOf_eq_of_mk_eq`. -/
lemma mulMap_eq_of_mk_eq {H₁ H₂ H₃ : Subgroup G} [IsHeckeTriple Δ H₁ H₂] {g₁ g₂ d : Δ}
    {p : DecompQuotient H₁ H₂ (g₁ : G) × DecompQuotient H₂ H₃ (g₂ : G)}
    (h : ((p.1.out : G) * g₁ * ((p.2.out : G) * g₂) : G ⧸ H₃) = ((d : G) : G ⧸ H₃)) :
    mulMap H₁ H₂ H₃ g₁ g₂ p = mk H₁ H₃ d :=
  mulMapOf_eq_of_mk_eq h

end HeckeCoset
