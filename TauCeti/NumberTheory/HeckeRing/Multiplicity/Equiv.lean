/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity

import TauCeti.NumberTheory.HeckeRing.StabConjugation

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
@[simp] lemma mem_doubleCoset_map_equiv_iff (e : G ≃* K) (H₁ H₂ : Subgroup G) (g x : G) :
    e x ∈ doubleCoset (e g) (e '' (H₁ : Set G)) (e '' (H₂ : Set G)) ↔
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
    exact mem_doubleCoset.mpr ⟨e a, ⟨a, ha, rfl⟩,
      e b, ⟨b, hb, rfl⟩, by simp only [map_mul]⟩

/-- A group equivalence carries the decomposition quotient of `g` to that of its image. -/
noncomputable def decompQuotientEquivMap (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) :
    DecompQuotient H₁ H₂ g ≃
      DecompQuotient (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) (e g) := by
  apply Quotient.congr (e.subgroupMap H₁).toEquiv
  intro x y
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv, Subgroup.coe_inv,
    Subgroup.coe_mul]
  -- `Quotient.congr` exposes the source relation first and the transported relation second;
  -- this ascription only names those two reducible relations so that `mem_map_iff_mem` applies.
  change (g⁻¹ * ((x : G)⁻¹ * y) * g ∈ H₂) ↔
    (((e : G →* K) g)⁻¹ * (((e : G →* K) (x : G))⁻¹ * (e : G →* K) (y : G)) *
      (e : G →* K) g ∈ H₂.map (e : G →* K))
  convert
    (Subgroup.mem_map_iff_mem (f := (e : G →* K)) (K := H₂) e.injective
      (x := g⁻¹ * ((x : G)⁻¹ * y) * g)).symm using 1
  simp only [map_inv, map_mul]

/-- The image of a decomposition class represented by `x` is represented by `e x`. -/
@[simp] lemma decompQuotientEquivMap_mk (e : G ≃* K) (H₁ H₂ : Subgroup G) (g : G) (x : H₁) :
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
equivalence, without any finiteness hypothesis. -/
@[simp] theorem multiplicity_map_equiv (e : G ≃* K) (H₁ H₂ H₃ : Subgroup G) (g h d : G) :
    multiplicity (H₁.map (e : G →* K)) (H₂.map (e : G →* K)) (H₃.map (e : G →* K))
        (e g) (e h) (e d) =
      multiplicity H₁ H₂ H₃ g h d := by
  let eg := decompQuotientEquivMap e H₁ H₂ g
  let eh := decompQuotientEquivMap e H₂ H₃ h
  let c : DecompQuotient H₁ H₂ g → H₂.map (e : G →* K) := fun i ↦
    ⟨((e : G →* K) g)⁻¹ * (((eg i).out : K)⁻¹ * (e : G →* K) (i.out : G)) *
      (e : G →* K) g,
      decompQuotientEquivMap_out e H₁ H₂ g i⟩
  -- Transporting the first representative introduces the middle-subgroup correction `c i`.
  -- Shearing the transported second quotient by it matches the full defining fibres directly.
  let epairs := Equiv.prodShear eg fun i ↦ eh.trans (MulAction.toPerm (c i))
  rw [multiplicity_def, multiplicity_def]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun p ↦ ?_)
  obtain ⟨i, j⟩ := p
  simp only [Set.mem_ofPred_eq]
  let q := c i • eh j
  have hq : (QuotientGroup.mk q.out : DecompQuotient (H₂.map (e : G →* K))
      (H₃.map (e : G →* K)) (e h)) =
      QuotientGroup.mk (c i * (eh j).out) := by
    calc
      _ = q := QuotientGroup.out_eq' q
      _ = c i • eh j := rfl
      _ = c i • QuotientGroup.mk (eh j).out :=
        congrArg (c i • ·) (QuotientGroup.out_eq' (eh j)).symm
      _ = _ := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hqmem := conj_mem_of_mk_eq ((e : G →* K) h) hq
  have hjmem := decompQuotientEquivMap_out e H₂ H₃ h j
  have hprod :
      (((eg i).out : K) * (e : G →* K) g * ((q.out : K) * (e : G →* K) h) :
          K ⧸ (H₃.map (e : G →* K))) =
        ((e : G →* K) ((i.out : G) * g * ((j.out : G) * h)) :
          K ⧸ (H₃.map (e : G →* K))) := by
    rw [QuotientGroup.eq]
    have hm := (H₃.map (e : G →* K)).mul_mem hqmem hjmem
    dsimp only [q, c, eh, Subtype.coe_mk] at hm ⊢
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev] at hm ⊢
    simpa only [mul_assoc, mul_inv_cancel_left] using hm
  -- Unfold only the pair equivalence so its second component is the named quotient `q` above.
  dsimp only [epairs, Equiv.prodShear_apply, Equiv.trans_apply, MulAction.toPerm_apply]
  change
    (((i.out : G) * g * ((j.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
      ((((eg i).out : K) * (e : G →* K) g * ((q.out : K) * (e : G →* K) h) :
          K ⧸ (H₃.map (e : G →* K))) =
        ((e : G →* K) d : K ⧸ (H₃.map (e : G →* K))))
  rw [hprod, QuotientGroup.eq, QuotientGroup.eq]
  convert
    (Subgroup.mem_map_iff_mem (f := (e : G →* K)) (K := H₃) e.injective
      (x := ((i.out : G) * g * ((j.out : G) * h))⁻¹ * d)).symm using 1
  all_goals simp only [map_inv, map_mul]

/-- Shimura's multiplicity depends on its second input only through its double coset, without
any finiteness or Hecke-triple hypothesis. -/
theorem multiplicity_doubleCoset_congr_second (H₁ H₂ H₃ : Subgroup G)
    (g : G) {h h' : G} (d : G) (hh : h' ∈ doubleCoset h H₂ H₃) :
    multiplicity H₁ H₂ H₃ g h' d = multiplicity H₁ H₂ H₃ g h d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hh
  let aN : Subgroup.normalizer (H₂ : Set G) := ⟨a, Subgroup.le_normalizer ha⟩
  let eh := decompQuotientEquivMulLeftRight H₂ H₃ h aN (Subgroup.le_normalizer hb)
  let epairs := Equiv.prodCongr (Equiv.refl (DecompQuotient H₁ H₂ g))
    (eh.trans (MulAction.toPerm (⟨a, ha⟩ : H₂)))
  rw [multiplicity_def, multiplicity_def]
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun p ↦ ?_)
  obtain ⟨i, j⟩ := p
  simp only [Set.mem_ofPred_eq]
  let q := (⟨a, ha⟩ : H₂) • eh j
  have hq : (QuotientGroup.mk q.out : DecompQuotient H₂ H₃ h) =
      QuotientGroup.mk (j.out * (⟨a, ha⟩ : H₂)) := by
    calc
      _ = q := QuotientGroup.out_eq' q
      _ = (⟨a, ha⟩ : H₂) • eh j := rfl
      _ = (⟨a, ha⟩ : H₂) • eh (QuotientGroup.mk j.out) :=
        congrArg (fun x ↦ (⟨a, ha⟩ : H₂) • eh x) (QuotientGroup.out_eq' j).symm
      _ = (⟨a, ha⟩ : H₂) • QuotientGroup.mk
          ((H₂.normalizerMonoidHom aN).symm j.out) := by
        rw [decompQuotientEquivMulLeftRight_mk]
      _ = _ := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
        apply congrArg QuotientGroup.mk
        ext
        dsimp only [aN]
        simp [Subgroup.normalizerMonoidHom, HSMul.hSMul, mul_assoc]
  have hqmem := conj_mem_of_mk_eq h hq
  have hprod :
      ((i.out : G) * g * ((j.out : G) * (a * h * b)) : G ⧸ H₃) =
        ((i.out : G) * g * ((q.out : G) * h) : G ⧸ H₃) := by
    rw [QuotientGroup.eq]
    have hm := H₃.mul_mem (H₃.inv_mem hb) (H₃.inv_mem hqmem)
    simpa [mul_inv_rev, mul_assoc] using hm
  -- As above, expose only the product equivalence and name its transported component `q`.
  dsimp only [epairs, Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.trans_apply,
    MulAction.toPerm_apply]
  change
    (((i.out : G) * g * ((j.out : G) * (a * h * b)) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
      (((i.out : G) * g * ((q.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃))
  rw [hprod]

/-- If the multiplicity is symmetric in its two inputs, it depends on its first input only
through its double coset as well. -/
theorem multiplicity_doubleCoset_congr_first_of_comm (H : Subgroup G)
    (hcomm : ∀ a b d : G, multiplicity H H H a b d = multiplicity H H H b a d)
    {g g' : G} (h d : G) (hg : g' ∈ doubleCoset g H H) :
    multiplicity H H H g' h d = multiplicity H H H g h d := by
  calc
    _ = multiplicity H H H h g' d := hcomm g' h d
    _ = multiplicity H H H h g d :=
      multiplicity_doubleCoset_congr_second H H H h d hg
    _ = _ := (hcomm g h d).symm

end DoubleCoset

end
