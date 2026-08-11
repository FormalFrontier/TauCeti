/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.LeftCosetModule.Basic
public import TauCeti.NumberTheory.HeckeRing.Associativity

import Mathlib.Tactic.Group

/-!
# The action of the Hecke ring on the left-coset module

The scalar operations of `LeftCosetModule` (defined with the module itself) satisfy the
compatibility law of [Shimura][shimura1971], Proposition 3.4: acting by a convolution
product is acting by its factors in sequence. Since `HgH` sends `βH` to `Σᵢ βσᵢgH` by right
multiplication, this is a **right** action, encoded per Mathlib convention as a left action
of the opposite ring `(𝕋 Δ H R)ᵐᵒᵖ` — so the compatibility law is `mul_smul` there, and the
operations become a genuine `Module`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/AbstractHeckeRing/Module.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), on top of the
coset vocabulary vendored from the in-review mathlib4 PR
[#41253](https://github.com/leanprover-community/mathlib4/pull/41253).

## Main results

* `LeftCosetModule.instModuleMulOpposite`: the opposite Hecke ring acts on the left-coset
  module — Shimura's right action through the standard `Module` API.
* `LeftCosetModule.instIsScalarTowerMulOpposite`,
  `LeftCosetModule.instSMulCommClassMulOpposite`: the scalar operations are homogeneous in,
  and commute with, the coefficients.
* `LeftCosetModule.card_filter_orbit_eq_multiplicity` (private): Shimura's pair count, the
  combinatorial core of the compatibility law.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open DoubleCoset Subgroup

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

namespace LeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [CommSemiring R]

/-- The scalar operations are `R`-homogeneous in the Hecke-ring argument; over the
opposite-ring encoding the scalar crosses the reversed product, so commutativity of `R` is
required. Packaged as `instIsScalarTowerMulOpposite`. -/
private lemma op_smul_assoc (r : R) (t : 𝕋 Δ H R) (m : LeftCosetModule Δ H R) :
    MulOpposite.op (r • t) • m = r • (MulOpposite.op t • m) := by
  classical
  simp only [smul_eq_sum]
  refine (Finsupp.sum_smul_index fun D ↦ ?_).trans ?_
  · exact Finsupp.sum_congr (g2 := fun _ _ ↦ 0) (fun q _ ↦ Finset.sum_eq_zero fun i _ ↦ by
      simp) |>.trans (Finsupp.sum_fun_zero m)
  · refine Eq.trans (Finsupp.sum_congr fun D b₁ ↦ ?_) Finsupp.smul_sum.symm
    refine Eq.trans (Finsupp.sum_congr fun q b₂ ↦ ?_) Finsupp.smul_sum.symm
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [Finsupp.smul_single, smul_eq_mul]
      exact congrArg _ (mul_left_comm _ _ _)

/-- The scalar tower `R → (𝕋 Δ H R)ᵐᵒᵖ → LeftCosetModule Δ H R`: the canonical form of the
`R`-homogeneity of the scalar operations. -/
noncomputable instance instIsScalarTowerMulOpposite :
    IsScalarTower R (𝕋 Δ H R)ᵐᵒᵖ (LeftCosetModule Δ H R) where
  smul_assoc r t m := by
    conv_lhs => rw [← MulOpposite.op_unop t, ← MulOpposite.op_smul]
    rw [op_smul_assoc, MulOpposite.op_unop]

end LeftCosetModule

namespace LeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

/-- The scalar operations commute with the `R`-scalars of the module argument. Packaged as
`instSMulCommClassMulOpposite`. -/
private lemma op_smul_comm (r : R) (t : 𝕋 Δ H R) (m : LeftCosetModule Δ H R) :
    MulOpposite.op t • (r • m) = r • (MulOpposite.op t • m) := by
  classical
  simp only [smul_eq_sum]
  refine Eq.trans (Finsupp.sum_congr fun D b₁ ↦ ?_) Finsupp.smul_sum.symm
  refine Eq.trans (Finsupp.sum_smul_index fun q ↦ ?_) ?_
  · exact Finset.sum_eq_zero fun i _ ↦ by simp
  · refine Eq.trans (Finsupp.sum_congr fun q b₂ ↦ ?_) Finsupp.smul_sum.symm
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finsupp.smul_single, smul_eq_mul]
    exact congrArg _ (mul_assoc _ _ _)

/-- The scalar operations of the opposite Hecke ring commute with the `R`-scalars: the
canonical `SMulCommClass` form. -/
noncomputable instance instSMulCommClassMulOpposite :
    SMulCommClass (𝕋 Δ H R)ᵐᵒᵖ R (LeftCosetModule Δ H R) where
  smul_comm t r m := by
    conv_lhs => rw [← MulOpposite.op_unop t]
    rw [op_smul_comm, MulOpposite.op_unop]

end LeftCosetModule

namespace LeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule Pointwise

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

/-- Iterated action of two basis elements of the Hecke ring on a basis element of the
module: the double sum over the two orbit layers. -/
private lemma single_smul_single_smul (D₁ D₂ : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H)
    (a b c : R) :
    MulOpposite.op (HeckeCosetModule.single R D₂ b) •
        (MulOpposite.op (HeckeCosetModule.single R D₁ a) •
          (Finsupp.single q c : LeftCosetModule Δ H R)) =
      ∑ i ∈ smulOrbit H D₁.rep q.rep, ∑ j ∈ smulOrbit H D₂.rep i.rep,
        Finsupp.single j (c * a * b) := by
  rw [single_smul_single, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ single_smul_single D₂ i b (c * a)

/-- Expansion of the action of a structure-constants element: the multiplicity-weighted
orbit sums. -/
private lemma smul_structureConstants_smul_single (D₁ D₂ : HeckeCoset Δ H H)
    (q : HeckeCoset Δ ⊥ H) (r c : R) :
    MulOpposite.op (r • HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep) •
        (Finsupp.single q c : LeftCosetModule Δ H R) =
      (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep).sum fun D mD ↦
        ∑ i ∈ smulOrbit H D.rep q.rep, Finsupp.single i (c * r * mD) := by
  rw [smul_eq_sum]
  refine Eq.trans (Finsupp.sum_smul_index fun D ↦ ?_) ?_
  · exact Finsupp.sum_congr (g2 := fun _ _ ↦ 0) (fun q _ ↦ Finset.sum_eq_zero fun i _ ↦ by
      simp) |>.trans (Finsupp.sum_fun_zero _)
  · refine Finsupp.sum_congr fun D _ ↦ ?_
    rw [Finsupp.sum_single_index (by simp)]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (Finsupp.single i) (mul_assoc c r _).symm

omit [IsHeckeTriple Δ H H] in
open Classical in
/-- Evaluating a sum of distinct basis singles: the indicator coefficient. -/
private lemma sum_single_apply (s : Finset (HeckeCoset Δ ⊥ H)) (v : R)
    (x : HeckeCoset Δ ⊥ H) :
    (∑ i ∈ s, Finsupp.single i v : LeftCosetModule Δ H R) x = if x ∈ s then v else 0 := by
  classical
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' s x fun _ ↦ v]

open Classical in
/-- Coefficient of the double orbit sum at a left coset: the number of intermediate cosets
whose second-layer orbit contains it. -/
private lemma sum_sum_single_apply (g₁ g₂ β : Δ) (c : R) (x : HeckeCoset Δ ⊥ H) :
    (∑ i ∈ smulOrbit H g₁ β, ∑ j ∈ smulOrbit H g₂ i.rep,
        Finsupp.single j c : LeftCosetModule Δ H R) x =
      ((smulOrbit H g₁ β).filter fun i ↦ x ∈ smulOrbit H g₂ i.rep).card • c := by
  rw [Finset.sum_apply']
  calc ∑ i ∈ smulOrbit H g₁ β, (∑ j ∈ smulOrbit H g₂ i.rep, Finsupp.single j c) x
      = ∑ i ∈ smulOrbit H g₁ β, if x ∈ smulOrbit H g₂ i.rep then c else 0 :=
        Finset.sum_congr rfl fun i _ ↦ sum_single_apply _ c x
    _ = _ := by rw [← Finset.sum_filter, Finset.sum_const]

open Classical in
/-- Coefficient of a multiplicity-weighted orbit sum at a left coset: the weight of the
unique double coset whose orbit contains it, if any. -/
private lemma sum_smulOrbit_single_apply (t : 𝕋 Δ H R) (β : Δ) (c : R)
    (x : HeckeCoset Δ ⊥ H) :
    ((t.sum fun D mD ↦ ∑ i ∈ smulOrbit H D.rep β, Finsupp.single i (c * mD)) :
        LeftCosetModule Δ H R) x =
      t.sum fun D mD ↦ if x ∈ smulOrbit H D.rep β then c * mD else 0 := by
  exact Finsupp.sum_apply.trans (Finsupp.sum_congr fun D _ ↦ sum_single_apply _ _ x)

/-- A left coset lies in the orbit of at most one double coset. -/
private lemma eq_of_mem_smulOrbit {g₁ g₂ β : Δ} {x : HeckeCoset Δ ⊥ H}
    (h₁ : x ∈ smulOrbit H g₁ β) (h₂ : x ∈ smulOrbit H g₂ β) :
    HeckeCoset.mk H H g₁ = HeckeCoset.mk H H g₂ := by
  by_contra hne
  exact Finset.disjoint_left.mp (smulOrbit_disjoint β hne) h₁ h₂

open Classical in
/-- The weighted orbit indicator collapses to the containing double coset's weight. -/
private lemma sum_ite_orbit_eq (t : 𝕋 Δ H R) (β : Δ) (c : R) {x : HeckeCoset Δ ⊥ H}
    {D₀ : HeckeCoset Δ H H} (hx : x ∈ smulOrbit H D₀.rep β) :
    (t.sum fun D mD ↦ if x ∈ smulOrbit H D.rep β then c * mD else 0) = c * t D₀ := by
  refine (Finsupp.sum_eq_single D₀ (fun D _ hne ↦ ?_) (fun _ ↦ by simp)).trans (ite_eq_left hx)
  rw [ite_eq_right]
  intro hmem
  exact hne (by
    have h := eq_of_mem_smulOrbit hmem hx
    rwa [HeckeCoset.mk_rep, HeckeCoset.mk_rep] at h)

open Classical in
/-- Membership in the orbit through the canonical representative: `x` lies in the orbit of
`g` on `w` iff `w⁻¹ · x.rep` lies in the double coset `HgH`. -/
private lemma mem_smulOrbit_iff_rep {g w : Δ} {x : HeckeCoset Δ ⊥ H} :
    x ∈ smulOrbit H g w ↔
      ((w : G))⁻¹ * ((x.rep : Δ) : G) ∈ doubleCoset (g : G) (H : Set G) H := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_smulOrbit.mp hx
    have hrep := mk_bot_eq_mk_bot.mp ((HeckeCoset.mk_rep x).trans hi.symm)
    -- hrep : x.rep⁻¹ · (w·σᵢ·g) ∈ H, so w⁻¹·x.rep = σᵢ·g·(w·σᵢ·g)⁻¹·x.rep with σᵢ ∈ H
    refine mem_doubleCoset.mpr ⟨(i.out : G), i.out.2,
      (((x.rep : Δ) : G)⁻¹ * ((w : G) * (i.out : G) * (g : G)))⁻¹, H.inv_mem hrep, by group⟩
  · intro hmem
    obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := mem_doubleCoset.mp hmem
    set i : DecompQuotient H H (g : G) := QuotientGroup.mk ⟨h₁, hh₁⟩ with hi
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g : G) • H).subgroupOf H) (⟨h₁, hh₁⟩ : H)
    have hout : ((i.out : H) : G) = h₁ * n := by
      rw [hi]
      simpa [Subgroup.coe_mul] using congrArg (Subtype.val : H → G) hn
    refine mem_smulOrbit.mpr ⟨i, ?_⟩
    rw [← HeckeCoset.mk_rep x]
    refine mk_bot_eq_mk_bot.mpr ?_
    -- as in `smulOrbit_subset`, the setoid membership is stated through the coercions
    change ((w : G) * ((i.out : H) : G) * (g : G))⁻¹ * ((x.rep : Δ) : G) ∈ H
    have key : ((w : G) * ((i.out : H) : G) * (g : G))⁻¹ * ((x.rep : Δ) : G) =
        ((g : G)⁻¹ * (n : G)⁻¹ * g) * h₂ := by
      have hx : ((x.rep : Δ) : G) = (w : G) * (h₁ * (g : G) * h₂) := by
        rw [← heq]; group
      rw [hout, hx]
      group
    rw [key]
    exact H.mul_mem
      (by simpa [mul_assoc] using H.inv_mem (DoubleCoset.conj_mem_of_stabilizer (g : G) n)) hh₂

open Classical in
/-- **Shimura's pair count** (the heart of Proposition 3.4): for a left coset in the orbit
of `D₀`, the number of intermediate cosets of the `D₁`-orbit whose `D₂`-orbit contains it
is the multiplicity of `D₀` in the product `D₁ * D₂`. -/
private lemma card_filter_orbit_eq_multiplicity {D₁ D₂ D₀ : HeckeCoset Δ H H} {β : Δ}
    {x : HeckeCoset Δ ⊥ H} (hx : x ∈ smulOrbit H D₀.rep β) :
    ((smulOrbit H D₁.rep β).filter fun i ↦ x ∈ smulOrbit H D₂.rep i.rep).card =
      multiplicity H H H (D₁.rep : G) (D₂.rep : G) (D₀.rep : G) := by
  classical
  rw [← multiplicity_doubleCoset_congr (D₁.rep : G) (D₂.rep : G)
      (mem_smulOrbit_iff_rep.mp hx),
    multiplicity_eq_card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype,
    smulOrbit_eq_image, Finset.filter_image,
    Finset.card_image_of_injective _ (smulOrbit_map_injective D₁.rep β)]
  refine congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)
  -- normalize the basepoint: peel `β` off the product so both sides quotient at `i·g₁`
  have hbase : ((β : G) * (i.out : G) * ((D₁.rep : Δ) : G))⁻¹ * ((x.rep : Δ) : G) =
      ((i.out : G) * ((D₁.rep : Δ) : G))⁻¹ * ((β : G)⁻¹ * ((x.rep : Δ) : G)) := by group
  rw [smulOrbit_congr D₂.rep (HeckeCoset.mk_rep _), mem_smulOrbit_iff_rep, hbase]
  exact Iff.rfl

/-- Iterated orbit membership factors through a single orbit at the original base: the
witnessing double coset is that of `β⁻¹ · x.rep`. -/
private lemma exists_orbit_of_mem_orbit_orbit {g₁ g₂ β : Δ} {x i : HeckeCoset Δ ⊥ H}
    (hi : i ∈ smulOrbit H g₁ β) (hx : x ∈ smulOrbit H g₂ i.rep) :
    ∃ D₀ : HeckeCoset Δ H H, x ∈ smulOrbit H D₀.rep β := by
  have hβη := mem_smulOrbit_iff_rep.mp hi
  have hηξ := mem_smulOrbit_iff_rep.mp hx
  -- each leg lies in `Δ` because a double coset of a `Δ`-element is absorbed by `Δ`, and
  -- the two legs compose at `i.rep`
  have hΔ : (β : G)⁻¹ * ((x.rep : Δ) : G) ∈ Δ := by
    rw [show (β : G)⁻¹ * ((x.rep : Δ) : G) =
        ((β : G)⁻¹ * ((i.rep : Δ) : G)) * (((i.rep : Δ) : G)⁻¹ * ((x.rep : Δ) : G)) by group]
    exact Δ.mul_mem (IsHeckeTriple.mem_of_mem_doubleCoset g₁.2 hβη)
      (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 hηξ)
  refine ⟨HeckeCoset.mk H H ⟨(β : G)⁻¹ * ((x.rep : Δ) : G), hΔ⟩, ?_⟩
  rw [mem_smulOrbit_iff_rep]
  have hrep := HeckeCoset.rep_mem (HeckeCoset.mk H H ⟨(β : G)⁻¹ * ((x.rep : Δ) : G), hΔ⟩)
  rw [HeckeCoset.toSet_mk] at hrep
  exact doubleCoset_eq_of_mem hrep ▸
    mem_doubleCoset_self H H ((β : G)⁻¹ * ((x.rep : Δ) : G))

end LeftCosetModule

namespace LeftCosetModule

open HeckeCoset

open scoped HeckeCosetModule Pointwise

variable [IsHeckeTriple Δ H H] {R : Type*} [Semiring R]

open Classical in
/-- **The compatibility law on basis elements** (Shimura, Proposition 3.4, single case):
acting by a product of two basis elements is acting by them in sequence. -/
private lemma single_mul_smul_single (D₁ D₂ : HeckeCoset Δ H H) (q : HeckeCoset Δ ⊥ H)
    (a b c : R) :
    MulOpposite.op (HeckeCosetModule.single R D₁ a * HeckeCosetModule.single R D₂ b) •
        (Finsupp.single q c : LeftCosetModule Δ H R) =
      MulOpposite.op (HeckeCosetModule.single R D₂ b) •
        (MulOpposite.op (HeckeCosetModule.single R D₁ a) •
          (Finsupp.single q c : LeftCosetModule Δ H R)) := by
  classical
  rw [HeckeCosetModule.single_mul_single, smul_smul,
    smul_structureConstants_smul_single, single_smul_single_smul]
  refine Finsupp.ext fun x ↦ ?_
  rw [sum_smulOrbit_single_apply, sum_sum_single_apply]
  by_cases h : ∃ D₀ : HeckeCoset Δ H H, x ∈ smulOrbit H D₀.rep q.rep
  · obtain ⟨D₀, hD₀⟩ := h
    rw [sum_ite_orbit_eq _ _ _ hD₀, card_filter_orbit_eq_multiplicity hD₀,
      HeckeCosetModule.structureConstants_apply]
    simp only [nsmul_eq_mul]
    -- the multiplicity enters as a natural-number cast, which is central
    rw [mul_assoc c a b]
    exact (Nat.cast_commute _ (c * (a * b))).symm.eq
  · have hzero : (HeckeCosetModule.structureConstants R H H H D₁.rep D₂.rep).sum
        (fun D mD ↦ if x ∈ smulOrbit H D.rep q.rep then c * (a * b) * mD else 0) = 0 :=
      (Finsupp.sum_congr fun D _ ↦ ite_eq_right fun hmem ↦ h ⟨D, hmem⟩).trans
        (Finsupp.sum_fun_zero _)
    have hempty : (smulOrbit H D₁.rep q.rep).filter
        (fun i ↦ x ∈ smulOrbit H D₂.rep i.rep) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun i hi hpi ↦
        h (exists_orbit_of_mem_orbit_orbit hi hpi)
    rw [hzero, hempty, Finset.card_empty, zero_nsmul]

/-- **The compatibility law of the left-coset action** (Shimura, Proposition 3.4): acting
by a convolution product is acting by its factors in sequence. -/
private theorem mul_smul' (f g : 𝕋 Δ H R) (m : LeftCosetModule Δ H R) :
    MulOpposite.op (f * g) • m = MulOpposite.op g • (MulOpposite.op f • m) := by
  induction m using Finsupp.induction_linear with
  | zero => rw [smul_zero, smul_zero, smul_zero]
  | add m₁ m₂ h₁ h₂ => rw [smul_add, smul_add, smul_add, h₁, h₂]
  | single q c =>
    induction f using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd f₁ f₂ h₁ h₂ =>
      rw [add_mul, MulOpposite.op_add, MulOpposite.op_add, add_smul, add_smul, h₁, h₂,
        smul_add]
    | hsingle D₁ a =>
      induction g using HeckeCosetModule.induction_linear with
      | h0 => rw [mul_zero, MulOpposite.op_zero, zero_smul, zero_smul]
      | hadd g₁ g₂ h₁ h₂ =>
        rw [mul_add, MulOpposite.op_add, MulOpposite.op_add, add_smul, add_smul, h₁, h₂]
      | hsingle D₂ b => exact single_mul_smul_single D₁ D₂ q a b c

/-- The orbit of the identity double coset is the singleton of the base coset: `H·1·H = H`
decomposes into a single left coset, which absorbs into `βH`. -/
private lemma smulOrbit_one_rep (q : HeckeCoset Δ ⊥ H) :
    smulOrbit H (1 : HeckeCoset Δ H H).rep q.rep = {q} := by
  classical
  rw [smulOrbit_congr_left q.rep
    ((HeckeCoset.mk_rep (1 : HeckeCoset Δ H H)).trans (HeckeCoset.one_def H))]
  -- the tail `σᵢ · 1` lies in `H`, so it absorbs into the left coset of `q.rep`
  have key : ∀ i : DecompQuotient H H ((1 : Δ) : G),
      (((q.rep : Δ) : G) * (i.out : G) * ((1 : Δ) : G))⁻¹ * ((q.rep : Δ) : G) ∈ H := by
    intro i
    have habsorb : (((q.rep : Δ) : G) * (i.out : G) * ((1 : Δ) : G))⁻¹ *
        ((q.rep : Δ) : G) = ((1 : Δ) : G)⁻¹ * (i.out : G)⁻¹ := by group
    rw [habsorb]
    exact H.mul_mem (by simp) (H.inv_mem i.out.2)
  ext x
  simp only [mem_smulOrbit, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    conv_rhs => rw [← HeckeCoset.mk_rep q]
    rw [HeckeCoset.mk_bot_eq_mk_bot]
    exact key i
  · intro hx
    rw [hx]
    obtain ⟨i⟩ : Nonempty (DecompQuotient H H ((1 : Δ) : G)) := inferInstance
    refine ⟨i, ?_⟩
    conv_rhs => rw [← HeckeCoset.mk_rep q]
    rw [HeckeCoset.mk_bot_eq_mk_bot]
    exact key i

/-- The identity of the Hecke ring fixes every basis element of the module. -/
private lemma one_smul_single (q : HeckeCoset Δ ⊥ H) (c : R) :
    MulOpposite.op (1 : 𝕋 Δ H R) • (Finsupp.single q c : LeftCosetModule Δ H R) =
      Finsupp.single q c := by
  classical
  rw [HeckeCosetModule.one_def, single_smul_single, smulOrbit_one_rep,
    Finset.sum_singleton, mul_one]

/-- **The left-coset module is a module over the opposite Hecke ring** (Shimura,
Propositions 3.2 and 3.4): the scalar operations of the defining file, packaged with the
unit and compatibility laws through the standard `Module` API. -/
noncomputable instance instModuleMulOpposite :
    Module (𝕋 Δ H R)ᵐᵒᵖ (LeftCosetModule Δ H R) where
  one_smul m := by
    induction m using Finsupp.induction_linear with
    | zero => exact smul_zero _
    | add f g hf hg => rw [smul_add, hf, hg]
    | single q c => exact one_smul_single q c
  mul_smul x y m := by
    rw [← MulOpposite.op_unop x, ← MulOpposite.op_unop y, ← MulOpposite.op_mul]
    exact mul_smul' y.unop x.unop m
  smul_zero t := smul_zero t
  smul_add t m₁ m₂ := smul_add t m₁ m₂
  add_smul x y m := add_smul x y m
  zero_smul m := _root_.zero_smul _ m

end LeftCosetModule
