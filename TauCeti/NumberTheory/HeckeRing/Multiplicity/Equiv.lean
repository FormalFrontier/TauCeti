/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# Transporting Hecke multiplicities along group equivalences

The double-coset multiplicity is unchanged when the ambient group, its three subgroups, and
the three elements are transported along a group equivalence. This is the naturality needed
when a concrete Hecke action presents the structure constants after applying an automorphism of
the ambient group.

## Main results

* `DoubleCoset.multiplicity_map_equiv`: transport of Shimura's multiplicity along a group
  equivalence.
* `DoubleCoset.multiplicity_doubleCoset_congr_second`: invariance in the second input.
* `DoubleCoset.multiplicity_doubleCoset_congr_first_of_comm`: invariance in the first input when
  the multiplicity is symmetric.
-/

public section

open Subgroup

namespace DoubleCoset

variable {G K : Type*} [Group G] [Group K]

/-- Membership in a double coset is preserved by a group equivalence. -/
lemma mem_doubleCoset_map_equiv_iff (e : G ≃* K) (H₁ H₂ : Subgroup G) (g x : G) :
    (e : G →* K) x ∈ doubleCoset ((e : G →* K) g) (H₁.map (e : G →* K))
        (H₂.map (e : G →* K)) ↔
      x ∈ doubleCoset g H₁ H₂ := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_doubleCoset.mp hx
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine mem_doubleCoset.mpr ⟨a', ha', b', hb', e.injective ?_⟩
    rw [map_mul, map_mul]
    exact hab
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
    exact mem_doubleCoset.mpr ⟨(e : G →* K) a, ⟨a, ha, rfl⟩,
      (e : G →* K) b, ⟨b, hb, rfl⟩, by simp only [map_mul]⟩

/-- A group equivalence carries the decomposition quotient of `g` to that of its image. -/
noncomputable def decompQuotientEquivMap (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) :
    DecompQuotient H₁ H₂ g ≃
      DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) ((e : G →* K) g) := by
  apply Quotient.congr (e.subgroupMap H₁).toEquiv
  intro x y
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv, Subgroup.coe_inv,
    Subgroup.coe_mul]
  change (g⁻¹ * ((x : G)⁻¹ * y) * g ∈ H₂) ↔
    (((e : G →* K) g)⁻¹ * (((e : G →* K) (x : G))⁻¹ * (e : G →* K) (y : G)) *
      (e : G →* K) g ∈ H₂.map (e : G →* K))
  convert
    (Subgroup.mem_map_iff_mem (f := (e : G →* K)) (K := H₂) e.injective
      (x := g⁻¹ * ((x : G)⁻¹ * y) * g)).symm using 1
  simp only [map_inv, map_mul]

/-- The image of a decomposition class represented by `x` is represented by `e x`. -/
lemma decompQuotientEquivMap_mk (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) (x : H₁) :
    decompQuotientEquivMap e H₁ H₂ g (QuotientGroup.mk x) =
      QuotientGroup.mk (e.subgroupMap H₁ x) :=
  (rfl)

/-- The chosen representative after transport differs from the transported representative by
an element of the stabilizer. -/
lemma decompQuotientEquivMap_out (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G)
    (i : DecompQuotient H₁ H₂ g) :
    ((e : G →* K) g)⁻¹ * (((decompQuotientEquivMap e H₁ H₂ g i).out : K)⁻¹ *
      (e : G →* K) (i.out : G)) * (e : G →* K) g ∈ H₂.map (e : G →* K) := by
  have hmk :
      ((decompQuotientEquivMap e H₁ H₂ g i).out :
          DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) ((e : G →* K) g)) =
        (e.subgroupMap H₁ i.out :
          DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) ((e : G →* K) g)) := by
    calc
      _ = decompQuotientEquivMap e H₁ H₂ g i := QuotientGroup.out_eq' _
      _ = decompQuotientEquivMap e H₁ H₂ g (i.out : DecompQuotient H₁ H₂ g) :=
        congrArg (decompQuotientEquivMap e H₁ H₂ g) (QuotientGroup.out_eq' i).symm
      _ = _ := decompQuotientEquivMap_mk e H₁ H₂ g i.out
  exact conj_mem_of_mk_eq ((e : G →* K) g) hmk

/-- Shimura's multiplicity is unchanged when all of its data are transported along a group
equivalence. -/
theorem multiplicity_map_equiv (e : G ≃* K) (H₁ H₂ H₃ : Subgroup G) (g h d : G)
    [Finite (DecompQuotient H₁ H₂ g)] [Finite (DecompQuotient H₂ H₃ h)] :
    multiplicity (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) (H₃.map (e : G →* K))
        (e g) (e h) (e d) =
      multiplicity H₁ H₂ H₃ g h d := by
  change multiplicity (H₁.map (e : G →* K)) (H₂.map (e : G →* K))
      (H₃.map (e : G →* K)) ((e : G →* K) g) ((e : G →* K) h)
        ((e : G →* K) d) = multiplicity H₁ H₂ H₃ g h d
  let eg := decompQuotientEquivMap e H₁ H₂ g
  let eh := decompQuotientEquivMap e H₂ H₃ h
  let : Finite (DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K))
      ((e : G →* K) g)) := Finite.of_equiv _ eg
  let : Finite (DecompQuotient (H₂.map (e : G →* K)) (H₃.map (e : G →* K))
      ((e : G →* K) h)) := Finite.of_equiv _ eh
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv eg fun i ↦ ?_)
  simp only [Set.mem_ofPred_eq]
  symm
  have hn := decompQuotientEquivMap_out e H₁ H₂ g i
  rw [show
    (((eg i).out : K) * (e : G →* K) g)⁻¹ * (e : G →* K) d =
      ((e : G →* K) g)⁻¹ * (((eg i).out : K)⁻¹ * (e : G →* K) (i.out : G)) *
        (e : G →* K) g * (e : G →* K) (((i.out : G) * g)⁻¹ * d) by
      simp only [map_mul, map_inv, mul_inv_rev]
      simp only [mul_assoc, mul_inv_cancel_left],
    mul_mem_doubleCoset_iff hn,
    mem_doubleCoset_map_equiv_iff]

/-- Shimura's multiplicity depends on its second input only through its double coset. -/
theorem multiplicity_doubleCoset_congr_second {Δ : Submonoid G} (H₁ H₂ H₃ : Subgroup G)
    [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] (g : Δ) {h h' : Δ} (d : G)
    (hh : (h' : G) ∈ doubleCoset (h : G) H₂ H₃) :
    multiplicity H₁ H₂ H₃ (g : G) (h' : G) d =
      multiplicity H₁ H₂ H₃ (g : G) (h : G) d := by
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter,
    doubleCoset_eq_of_mem hh]

/-- If the multiplicity is symmetric in its two inputs, it depends on its first input only
through its double coset as well. -/
theorem multiplicity_doubleCoset_congr_first_of_comm {Δ : Submonoid G} (H : Subgroup G)
    [IsHeckeTriple Δ H H]
    (hcomm : ∀ a b d : Δ, multiplicity H H H (a : G) (b : G) (d : G) =
      multiplicity H H H (b : G) (a : G) (d : G))
    {g g' : Δ} (h d : Δ) (hg : (g' : G) ∈ doubleCoset (g : G) H H) :
    multiplicity H H H (g' : G) (h : G) (d : G) =
      multiplicity H H H (g : G) (h : G) (d : G) := by
  calc
    _ = multiplicity H H H (h : G) (g' : G) (d : G) := hcomm g' h d
    _ = multiplicity H H H (h : G) (g : G) (d : G) :=
      multiplicity_doubleCoset_congr_second H H H h d hg
    _ = _ := (hcomm g h d).symm

end DoubleCoset

end
