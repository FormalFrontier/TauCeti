/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.NumberTheory.HeckeRing.Defs
public import Mathlib.GroupTheory.Index

/-!
# Hecke rings: the double coset API

Basic API for the double cosets `HeckeCoset` indexing a Hecke coset module, following
[Shimura][shimura1971], Chapter 3. This file provides representatives of double cosets, the
characterisation of when two elements give the same double coset, and the quotient
`Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets inside a double coset `Γ₁gΓ₂`, which is used to
define the Hecke product in later files and is finite for a Hecke triple. It also houses
the basis-element API of the coset module: `HeckeCosetModule.single` with its evaluation,
summation, and additivity laws, the `induction_linear` principle, and the transported
`Module` instance — placed at this layer so every later file (convolution, one, and the
coset actions) can build on one shared vocabulary. Finally it defines the degree of a
double coset, the number of left cosets in its decomposition, together with its
relative-index form, since that count is read straight off `DecompQuotient`.

The coset vocabulary is vendored from the in-review mathlib4 PR
[#41253](https://github.com/leanprover-community/mathlib4/pull/41253) (Chris Birkbeck), per the
ModularForms roadmap's dependency policy; migrate to Mathlib and delete it when that stack
merges. The degree section is instead ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/AbstractHeckeRing/Degree.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).

## Main definitions

* `HeckeCoset.toSet`: the underlying set `H₁gH₂` of a double coset.
* `HeckeCoset.rep`: a chosen representative in `Δ`.
* `DoubleCoset.DecompQuotient`: the quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)` indexing the left cosets
  in `Γ₁gΓ₂`; finite for a Hecke triple. Its mirror `DecompQuotient Γ₂ Γ₁ g⁻¹` indexes the
  right cosets `Γ₁a`, and is finite too.
* `HeckeCosetModule.single`: the basis element `b • [D]` of the Hecke coset module, with
  `single_apply`, `sum_single_index`, `smul_single_one`, `single_add`, `induction_linear`,
  and the `Module R` instance `HeckeCosetModule.instModule`.
* Pointwise evaluation of the coset module: `zero_apply`, `add_apply`, `smul_apply`,
  `mem_support_iff`, `notMem_support_iff`, `sum_def`, `sum_apply` and `sum_smul_index`.
  `HeckeCosetModule` is a `def` over `Finsupp` carrying transported instances, so Mathlib's
  `Finsupp` evaluation lemmas hold *definitionally* — they can be applied in term mode — but
  `rw`, `simp` and `grind` match syntactically and so cannot see through the wrapper. These
  restatements are what makes those facts usable tactically.

  In particular these do not compete with their `Finsupp` originals: at this type
  `simp [Finsupp.mem_support_iff]` reports the argument as unused and `simp [Finsupp.add_apply]`
  makes no progress, because neither left-hand side matches through the wrapper. The wrapper
  restatement is the only form `simp` can apply.
* `HeckeCoset.degree`: the number of left cosets in the decomposition of a double coset,
  with `degree_eq_relIndex` and `degree_mk` presenting it as a relative index,
  `degree_eq_natCard_decompQuotient` as the (hypothesis-free) count of that quotient, and
  `degree_one` the identity coset.

## Main results

* `HeckeCoset.eq_iff`: `mk H₁ H₂ g = mk H₁ H₂ h ↔ H₁gH₂ = H₁hH₂`.
* `HeckeCoset.toSet_injective`: a double coset is determined by its underlying set.
* `DoubleCoset.doubleCoset_eq_iUnion_rightCosets` and
  `DoubleCoset.op_mul_out_inv_smul_injective`: Shimura's decomposition `Γ₁gΓ₂ = ⊔ᵥ Γ₁(gτᵥ⁻¹)`
  into *right* cosets, indexed without repetition by `DecompQuotient Γ₂ Γ₁ g⁻¹` — the mirror of
  `DoubleCoset.doubleCoset_eq_iUnion_leftCosets` and `mk_out_mul_injective`.
* `DoubleCoset.doubleCoset_eq_iUnion_rightCosets_of_forall_exists`: a criterion for a supplied
  family of right-coset representatives to cover a double coset.
* `IsHeckeTriple.commensurable_conjAct_inv_left`, and the `Finite` instance beside it: that
  right-coset index is finite, the mirror of the `Fintype` instance on `DecompQuotient H₁ H₂ g`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
-/

public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

namespace HeckeCoset

variable {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

/-- The underlying set `H₁gH₂` of a double coset, well-defined on the quotient. -/
def toSet (D : HeckeCoset Δ H₁ H₂) : Set G :=
  Quotient.lift (fun g : Δ ↦ doubleCoset (g : G) H₁ H₂) (fun _ _ h ↦ h) D

/-- A representative `g : Δ` of a double coset (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset Δ H₁ H₂) : Δ := Quotient.out D

@[simp] lemma mk_rep (D : HeckeCoset Δ H₁ H₂) : mk H₁ H₂ D.rep = D := Quotient.out_eq' D

/-- Two elements of `Δ` define the same `HeckeCoset` iff their double cosets coincide. -/
lemma eq_iff {g h : Δ} : mk H₁ H₂ g = mk H₁ H₂ h ↔
    doubleCoset (g : G) H₁ H₂ = doubleCoset (h : G) H₁ H₂ := Quotient.eq''

@[simp] lemma toSet_mk (g : Δ) : toSet (mk H₁ H₂ g) = doubleCoset (g : G) H₁ H₂ := (rfl)

lemma toSet_eq_doubleCoset_rep (D : HeckeCoset Δ H₁ H₂) :
    D.toSet = doubleCoset (D.rep : G) H₁ H₂ := by rw [← toSet_mk, mk_rep]

/-- A double coset is determined by its underlying set. -/
lemma toSet_injective : Function.Injective (toSet : HeckeCoset Δ H₁ H₂ → Set G) := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ fun _ _ h ↦ Quotient.sound' h

lemma rep_mem (D : HeckeCoset Δ H₁ H₂) : (D.rep : G) ∈ D.toSet :=
  D.toSet_eq_doubleCoset_rep ▸ mem_doubleCoset_self H₁ H₂ _

/-- `mk H₁ H₂ g₁ = mk H₁ H₂ g₂` when `g₁` lies in the double coset of `g₂`. -/
lemma mk_eq_mk_of_mem {g₁ g₂ : Δ} (h : (g₁ : G) ∈ doubleCoset (g₂ : G) H₁ H₂) :
    mk H₁ H₂ g₁ = mk H₁ H₂ g₂ :=
  eq_iff.mpr (doubleCoset_eq_of_mem h)

section Map

variable {Δ' : Submonoid G} {H₁' H₂' : Subgroup G}

/-- **Functoriality of `HeckeCoset` in its triple.** Inclusions `Δ ≤ Δ'`, `H₁ ≤ H₁'` and
`H₂ ≤ H₂'` send `H₁ g H₂` to `H₁' g H₂'`: widening the coefficient subgroups can only merge
double cosets, never split them. -/
noncomputable def map (hΔ : Δ ≤ Δ') (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') :
    HeckeCoset Δ H₁ H₂ → HeckeCoset Δ' H₁' H₂' :=
  Quotient.map (Submonoid.inclusion hΔ) fun a b hab ↦ by
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hb⟩ := DoubleCoset.rel_iff.mp hab
    exact DoubleCoset.rel_iff.mpr ⟨γ₁, h₁ hγ₁, γ₂, h₂ hγ₂, hb⟩

@[simp] lemma map_mk (hΔ : Δ ≤ Δ') (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') (g : Δ) :
    map hΔ h₁ h₂ (mk H₁ H₂ g) = mk H₁' H₂' (Submonoid.inclusion hΔ g) := (rfl)

@[simp] lemma map_id (D : HeckeCoset Δ H₁ H₂) :
    map (le_refl Δ) (le_refl H₁) (le_refl H₂) D = D :=
  Quotient.inductionOn D fun _ ↦ rfl

variable {Δ'' : Submonoid G} {H₁'' H₂'' : Subgroup G}

@[simp] lemma map_map (hΔ : Δ ≤ Δ') (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') (hΔ' : Δ' ≤ Δ'')
    (h₁' : H₁' ≤ H₁'') (h₂' : H₂' ≤ H₂'') (D : HeckeCoset Δ H₁ H₂) :
    map hΔ' h₁' h₂' (map hΔ h₁ h₂ D) = map (hΔ.trans hΔ') (h₁.trans h₁') (h₂.trans h₂') D :=
  Quotient.inductionOn D fun _ ↦ rfl

end Map

/-- Induction: to prove something for all double cosets, prove it for `mk H₁ H₂ g`. -/
protected lemma induction {motive : HeckeCoset Δ H₁ H₂ → Prop}
    (h : ∀ g : Δ, motive (mk H₁ H₂ g)) :
    ∀ D, motive D :=
  Quotient.ind' h

/-- Two-argument induction for double cosets. -/
protected lemma induction₂ {motive : HeckeCoset Δ H₁ H₂ → HeckeCoset Δ H₁ H₂ → Prop}
    (h : ∀ g₁ g₂ : Δ, motive (mk H₁ H₂ g₁) (mk H₁ H₂ g₂)) : ∀ D₁ D₂, motive D₁ D₂ := fun D₁ D₂ ↦
  Quotient.inductionOn₂' D₁ D₂ h

variable {H : Subgroup G}

@[simp] lemma toSet_one : toSet (1 : HeckeCoset Δ H H) = (H : Set G) := by
  -- `toSet 1` unfolds to the set product `↑H * {1} * ↑H`; `change` states it so that the
  -- pointwise set lemmas apply (there is no rewriting lemma through the quotient here)
  change (H : Set G) * {(1 : G)} * H = (H : Set G)
  rw [Subgroup.subgroup_mul_singleton H.one_mem, coe_mul_coe]

lemma rep_one_mem : (rep (1 : HeckeCoset Δ H H) : G) ∈ H := by
  simpa using rep_mem (1 : HeckeCoset Δ H H)

end HeckeCoset

namespace DoubleCoset

/-- The decomposition quotient `Γ₁ ⧸ (Γ₁ ∩ gΓ₂g⁻¹)`, indexing the left cosets of `Γ₂` inside
the double coset `Γ₁gΓ₂`; see `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`. -/
abbrev DecompQuotient (Γ₁ Γ₂ : Subgroup G) (g : G) :=
  Γ₁ ⧸ (ConjAct.toConjAct g • Γ₂).subgroupOf Γ₁

instance (Γ₁ Γ₂ : Subgroup G) (g : G) : Nonempty (DecompQuotient Γ₁ Γ₂ g) :=
  ⟨QuotientGroup.mk 1⟩

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

open scoped Pointwise in
/-- The conjugation criterion for the stabilizer subgroup indexing `DecompQuotient`: an element
of `(ConjAct.toConjAct g • H₂).subgroupOf H₁` conjugates by `g` into `H₂`. -/
lemma conj_mem_of_stabilizer {H₁ H₂ : Subgroup G} (g : G)
    (n : (ConjAct.toConjAct g • H₂).subgroupOf H₁) : g⁻¹ * (n : G) * g ∈ H₂ := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

/-- Equality of classes in `DecompQuotient H₁ H₂ g` gives the conjugation relation between their
representatives: `u₁⁻¹ u₂` lies in the stabilizer indexing the decomposition, so conjugating it
by `g` lands in `H₂`.

Note the two subgroups play different roles: the representatives live in `H₁`, which indexes the
quotient, while the conclusion lands in `H₂`, which is the one being conjugated. They coincide in
the common case `DecompQuotient H H g`. -/
-- Reach for this whenever a class equality `⟦u₁⟧ = ⟦u₂⟧` has to become a membership:
-- `QuotientGroup.eq` supplies the stabilizer membership and `conj_mem_of_stabilizer` does the
-- conjugation, so unfolding `QuotientGroup.leftRel` by hand duplicates both.
lemma conj_mem_of_mk_eq {H₁ H₂ : Subgroup G} (g : G) {u₁ u₂ : H₁}
    (h : (QuotientGroup.mk u₁ : DecompQuotient H₁ H₂ g) = QuotientGroup.mk u₂) :
    g⁻¹ * ((u₁ : G)⁻¹ * u₂) * g ∈ H₂ :=
  conj_mem_of_stabilizer g ⟨_, QuotientGroup.eq.mp h⟩

/-- **Shimura's decomposition of a double coset into right cosets.** `Γ₁gΓ₂` is the union of the
right cosets `Γ₁ · (g τᵥ⁻¹)`, where `τᵥ` runs over representatives of `Γ₂ ⧸ (Γ₂ ∩ g⁻¹Γ₁g)` — the
mirror of `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`, and of Mathlib's
`doubleCoset_union_rightCoset`, which is indexed by all of `Γ₂` and so repeats each coset.

The inverse on `τᵥ` is what converts the *left*-coset quotient `Γ₂ ⧸ (Γ₂ ∩ g⁻¹Γ₁g)` into an index
for the right cosets: `Γ₁ g τ = Γ₁ g τ'` exactly when `τ'τ⁻¹ ∈ Γ₂ ∩ g⁻¹Γ₁g`.

It lives here rather than beside `doubleCoset_eq_iUnion_leftCosets` because it is phrased with
`DecompQuotient`, which this file defines. -/
lemma doubleCoset_eq_iUnion_rightCosets (Γ₁ Γ₂ : Subgroup G) (g : G) :
    doubleCoset g Γ₁ Γ₂ =
      ⋃ v : DecompQuotient Γ₂ Γ₁ g⁻¹,
        MulOpposite.op (g * ((v.out : G))⁻¹) • (Γ₁ : Set G) := by
  rw [← doubleCoset_union_rightCoset]
  refine le_antisymm (Set.iUnion_subset fun t ↦ ?_) (Set.iUnion_subset fun v ↦ ?_)
  · -- `t : Γ₂` lands in the coset of the class of `t⁻¹`
    refine Set.subset_iUnion_of_subset (QuotientGroup.mk t⁻¹) (le_of_eq ?_)
    refine (rightCoset_eq_iff Γ₁).mpr ?_
    have h := conj_mem_of_mk_eq (H₁ := Γ₂) (H₂ := Γ₁) g⁻¹ (Quotient.out_eq (QuotientGroup.mk t⁻¹))
    simpa [mul_assoc] using h
  · exact Set.subset_iUnion_of_subset ((v.out)⁻¹) (le_of_eq (by simp))

/-- **A right-coset decomposition criterion.** Suppose every product `a * g` with `g ∈ Γ₂`
factors as `d * rep i` with `d ∈ Γ₁`, and conversely every `rep i` equals `a * g` for some
`g ∈ Γ₂`. Then the double coset `Γ₁ a Γ₂` is the union of the right cosets
`Γ₁ · rep i`.

This criterion proves coverage only; injectivity of the representative family is a separate
property. -/
lemma doubleCoset_eq_iUnion_rightCosets_of_forall_exists {ι : Type*} (Γ₁ Γ₂ : Subgroup G)
    (a : G) (rep : ι → G)
    (hforward : ∀ g : G, g ∈ Γ₂ → ∃ (i : ι) (d : G), d ∈ Γ₁ ∧ a * g = d * rep i)
    (hreverse : ∀ i : ι, ∃ g : G, g ∈ Γ₂ ∧ a * g = rep i) :
    doubleCoset a Γ₁ Γ₂ = ⋃ i : ι, MulOpposite.op (rep i) • (Γ₁ : Set G) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.iUnion_subset fun i x hx ↦ ?_)
  · obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := mem_doubleCoset.mp hx
    obtain ⟨i, d, hd, heq⟩ := hforward g₂ hg₂
    refine Set.mem_iUnion.mpr ⟨i, (mem_rightCoset_iff _).mpr ?_⟩
    have hx' : g₁ * a * g₂ * (rep i)⁻¹ = g₁ * d := by
      rw [mul_assoc g₁, heq, mul_assoc, mul_inv_cancel_right]
    rw [hx']
    exact Γ₁.mul_mem hg₁ hd
  · obtain ⟨g, hg, hgeq⟩ := hreverse i
    refine mem_doubleCoset.mpr ⟨x * (rep i)⁻¹, (mem_rightCoset_iff _).mp hx,
      g, hg, ?_⟩
    rw [mul_assoc, hgeq, inv_mul_cancel_right]

/-- The right cosets of `doubleCoset_eq_iUnion_rightCosets` are pairwise distinct, so that union
is a partition and the sum of a `Γ₁`-invariant function over it counts each coset once. -/
lemma op_mul_out_inv_smul_injective (Γ₁ Γ₂ : Subgroup G) (g : G) :
    Function.Injective fun v : DecompQuotient Γ₂ Γ₁ g⁻¹ ↦
      MulOpposite.op (g * ((v.out : G))⁻¹) • (Γ₁ : Set G) := by
  intro v w hvw
  have h := (rightCoset_eq_iff Γ₁).mp hvw.symm
  rw [← QuotientGroup.out_eq' v, ← QuotientGroup.out_eq' w, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv]
  simpa [mul_assoc] using h

end DoubleCoset

namespace IsHeckeTriple

/-- Every member of the double coset `H₁gH₂` of an element of `Δ` lies in `Δ`. -/
theorem mem_of_mem_doubleCoset {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    {g x : G} (hg : g ∈ Δ) (hx : x ∈ doubleCoset g (H₁ : Set G) H₂) : x ∈ Δ := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hx
  exact mul_mem (mul_mem (mem_of_mem_left H₂ hh₁) hg) (mem_of_mem_right H₁ hh₂)

/-- For a Hecke triple, the decomposition quotient of any `g : Δ` is finite: `Δ`
commensurates `H₂`, which is commensurable with `H₁`. -/
noncomputable instance {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    (g : Δ) : Fintype (DecompQuotient H₁ H₂ (g : G)) :=
  Subgroup.fintypeOfIndexNeZero (IsHeckeTriple.commensurable_conjAct_right g).1

/-- Conjugating the *left* subgroup by the inverse of an element of `Δ` gives a subgroup
commensurable with the right one. This is `commensurable_conjAct_right` on the other flank:
the commensurator is a subgroup, so it contains `g⁻¹` along with `g`.

It is what makes `DecompQuotient H₂ H₁ g⁻¹` — the index of Shimura's decomposition of `H₁gH₂`
into *right* cosets `H₁a` — finite. -/
theorem commensurable_conjAct_inv_left {Δ : Submonoid G} {H₁ H₂ : Subgroup G}
    [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    Commensurable (ConjAct.toConjAct (g : G)⁻¹ • H₁) H₂ := by
  have hg : Commensurable (ConjAct.toConjAct ((g : G)⁻¹) • H₁) H₁ :=
    inv_mem (mem_commensurator_left H₂ g)
  exact hg.trans (commensurable (Δ := Δ))

/-- For a Hecke triple, the *right*-coset decomposition quotient of any `g : Δ` is finite.

This is the companion of the instance above on the other flank, and it is the finiteness the
slash sum over Shimura's decomposition `H₁gH₂ = ⊔ᵥ H₁aᵥ` needs. `Finite` rather than `Fintype`:
no enumeration is chosen here, and a second `Fintype` on a quotient of the same shape would
compete with the one above. -/
instance {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    Finite (DecompQuotient H₂ H₁ (g : G)⁻¹) :=
  @Finite.of_fintype _
    (Subgroup.fintypeOfIndexNeZero (IsHeckeTriple.commensurable_conjAct_inv_left g).1)

end IsHeckeTriple

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

open scoped Pointwise in
/-- The degree of a double coset: the number of left cosets `σᵢgH₂` in the decomposition
`H₁gH₂ = ⊔ᵢ σᵢgH₂`, i.e. the relative index `[H₁ : H₁ ∩ gH₂g⁻¹]`. Stating it needs no
finiteness — `Subgroup.relIndex` is a `Nat.card`, which is `0` when the index is infinite;
the Hecke-triple hypothesis enters only where the count is genuinely finite. -/
noncomputable def degree (D : HeckeCoset Δ H₁ H₂) : ℕ :=
  (ConjAct.toConjAct (D.rep : G) • H₂).relIndex H₁

open scoped Pointwise in
/-- The degree as a relative index: `deg(H₁gH₂) = [H₁ : H₁ ∩ gH₂g⁻¹]`. This is the form in
which concrete degree computations identify the count with a congruence-subgroup index. -/
lemma degree_eq_relIndex (D : HeckeCoset Δ H₁ H₂) :
    D.degree = (ConjAct.toConjAct (D.rep : G) • H₂).relIndex H₁ :=
  (rfl)

open scoped Pointwise in
/-- The degree at an explicit representative: the count computed from any `g`, not only
from the chosen `rep`. This is the form concrete coset calculations use, since they present
a double coset as `mk H H g`. -/
@[simp] lemma degree_mk (g : Δ) :
    (HeckeCoset.mk H₁ H₂ g).degree = (ConjAct.toConjAct (g : G) • H₂).relIndex H₁ := by
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ :=
    DoubleCoset.mem_doubleCoset.mp (toSet_mk g ▸ rep_mem (HeckeCoset.mk H₁ H₂ g))
  have hfix₂ : ConjAct.toConjAct h₂ • H₂ = H₂ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₂)
  have hfix₁ : ConjAct.toConjAct h₁ • H₁ = H₁ :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh₁)
  have htransport := Subgroup.relIndex_pointwise_smul
    (ConjAct.toConjAct h₁) (ConjAct.toConjAct (g : G) • H₂) H₁
  rw [hfix₁] at htransport
  rw [degree_eq_relIndex, heq, map_mul, map_mul, ← smul_smul, ← smul_smul, hfix₂,
    htransport]

/-- The identity double coset has degree one: `H·1·H = H` is a single left coset. -/
@[simp] lemma degree_one {H : Subgroup G} : (1 : HeckeCoset Δ H H).degree = 1 := by
  rw [one_def H, degree_mk]
  simp

/-- The degree counts the decomposition quotient. No finiteness is involved: a relative
index is by definition the `Nat.card` of exactly this quotient, so the two sides are the
same term. -/
lemma degree_eq_natCard_decompQuotient (D : HeckeCoset Δ H₁ H₂) :
    D.degree = Nat.card (DecompQuotient H₁ H₂ (D.rep : G)) :=
  (rfl)

variable [IsHeckeTriple Δ H₁ H₂]

/-- Under the Hecke-triple hypothesis the decomposition quotient is finite, so the degree is
its `Fintype.card`. The hypothesis is needed only for the `Fintype` instance, not for the
count itself — see `degree_eq_natCard_decompQuotient`. -/
lemma degree_eq_card_decompQuotient (D : HeckeCoset Δ H₁ H₂) :
    D.degree = Fintype.card (DecompQuotient H₁ H₂ (D.rep : G)) := by
  rw [degree_eq_natCard_decompQuotient, Nat.card_eq_fintype_card]

/-- Every double coset has positive degree. -/
lemma degree_pos (D : HeckeCoset Δ H₁ H₂) : 0 < D.degree := by
  rw [degree_eq_card_decompQuotient]; exact Fintype.card_pos

end HeckeCoset

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ : Subgroup G}

section SingleWrapper

variable (R : Type*) [Zero R]

/-- A basis element of the Hecke coset module: `single R D b` is the formal sum `b • [D]`. As
for `Finsupp` itself, this is the type-correct way to produce elements of
`HeckeCosetModule Δ H₁ H₂ R`. Only `[Zero R]` is assumed, so consumers with coefficient
assumptions below `Semiring` (the left-coset scalar operations) can use it. -/
noncomputable def single (D : HeckeCoset Δ H₁ H₂) (b : R) :
    HeckeCosetModule Δ H₁ H₂ R :=
  Finsupp.single D b

/-- `Finsupp.sum_single_index`, as a wrapper-level equation: summing over a basis element
evaluates the summand at its point. -/
lemma sum_single_index {N : Type*} [AddCommMonoid N] {D : HeckeCoset Δ H₁ H₂} {b : R}
    {F : HeckeCoset Δ H₁ H₂ → R → N} (h : F D 0 = 0) : (single R D b).sum F = F D b :=
  Finsupp.sum_single_index h

/-- Evaluating a basis element: `single R D b` is `b` at `D` and `0` elsewhere. -/
@[simp, grind =]
lemma single_apply {D A : HeckeCoset Δ H₁ H₂} {b : R} [Decidable (D = A)] :
    single R D b A = if D = A then b else 0 :=
  Finsupp.single_apply

end SingleWrapper

section SingleAlgebra

variable (R : Type*) [AddCommMonoid R]

/-- `Finsupp.single_zero`, as a wrapper-level equation. -/
@[simp] lemma single_zero (D : HeckeCoset Δ H₁ H₂) : single R D (0 : R) = 0 :=
  Finsupp.single_zero D

/-- Every element is the sum of its basis components. -/
@[simp]
lemma sum_single (f : HeckeCosetModule Δ H₁ H₂ R) : f.sum (single R) = f :=
  Finsupp.sum_single f

/-- `Finsupp.single_add`, as a wrapper-level equation. -/
@[simp]
lemma single_add (D : HeckeCoset Δ H₁ H₂) (b c : R) :
    single R D (b + c) = single R D b + single R D c :=
  Finsupp.single_add D b c

/-- `Finsupp.induction_linear`, restated for the wrapper type `HeckeCosetModule Δ H₁ H₂ R` in
its basis vocabulary `single`, in the same way that `MonoidAlgebra.induction_linear` restates
it for `MonoidAlgebra`: to prove a property of all elements, prove it for `0`, for sums, and
for basis elements. -/
lemma induction_linear {p : HeckeCosetModule Δ H₁ H₂ R → Prop}
    (f : HeckeCosetModule Δ H₁ H₂ R) (h0 : p 0)
    (hadd : ∀ f g : HeckeCosetModule Δ H₁ H₂ R, p f → p g → p (f + g))
    (hsingle : ∀ (D : HeckeCoset Δ H₁ H₂) (b : R), p (single R D b)) : p f :=
  Finsupp.induction_linear f h0 hadd hsingle

end SingleAlgebra

section SingleModule

variable (R : Type*) [Semiring R]

/-- The `R`-module structure of the Hecke coset module, transporting the standard `Finsupp`
module structure to the wrapper type. -/
noncomputable instance instModule : Module R (HeckeCosetModule Δ H₁ H₂ R) :=
  inferInstanceAs (Module R (HeckeCoset Δ H₁ H₂ →₀ R))

/-- Scaling the unit basis element produces the basis element of the scalar. -/
@[simp]
lemma smul_single_one (D : HeckeCoset Δ H₁ H₂) (b : R) : b • single R D 1 = single R D b :=
  Finsupp.smul_single_one D b

end SingleModule

/-! ### Pointwise evaluation

`HeckeCosetModule` is a `def` over `Finsupp`, so Mathlib's `Finsupp` evaluation lemmas hold
definitionally but neither `rw` nor `simp` can match them through the wrapper. These are the
wrapper-level restatements; without them every consumer re-derives its own private copies.
Each is stated at the coefficient assumptions its underlying operation actually needs: the
`FunLike` coercion and `Finsupp.support` need only `[Zero R]`, while the wrapper's `0`, `+`
and `•` come from its `AddCommMonoid` and `Module` instances. -/

section EvalSupport

variable {R : Type*} [Zero R]

/-- `Finsupp.mem_support_iff`, at the wrapper type. -/
@[simp, grind =] lemma mem_support_iff {f : HeckeCosetModule Δ H₁ H₂ R}
    {D : HeckeCoset Δ H₁ H₂} : D ∈ f.support ↔ f D ≠ 0 :=
  Finsupp.mem_support_iff

/-- `Finsupp.notMem_support_iff`, at the wrapper type: the elimination form of
`mem_support_iff`. Deliberately unannotated — `mem_support_iff` is the `@[simp]` normal form,
and `simp` discharges this direction from it. -/
lemma notMem_support_iff {f : HeckeCosetModule Δ H₁ H₂ R} {D : HeckeCoset Δ H₁ H₂} :
    D ∉ f.support ↔ f D = 0 :=
  Finsupp.notMem_support_iff

/-- `Finsupp.sum` unfolded to a `Finset.sum`, at the wrapper type. -/
-- `rfl` rather than a cited lemma: `Finsupp.sum` is a plain `def` for exactly this
-- `Finset.sum`, and Mathlib exposes no unfolding lemma to name here.
lemma sum_def {N : Type*} [AddCommMonoid N] (f : HeckeCosetModule Δ H₁ H₂ R)
    (F : HeckeCoset Δ H₁ H₂ → R → N) : f.sum F = ∑ D ∈ f.support, F D (f D) := (rfl)

/-- `Finsupp.sum_apply`, at the wrapper type: evaluation commutes with a `Finsupp.sum`. The
target coefficients are independent of the source's. -/
@[simp, grind =] lemma sum_apply {S : Type*} [AddCommMonoid S] {H₃ H₄ : Subgroup G}
    (f : HeckeCosetModule Δ H₁ H₂ R)
    (F : HeckeCoset Δ H₁ H₂ → R → HeckeCosetModule Δ H₃ H₄ S) (D : HeckeCoset Δ H₃ H₄) :
    (f.sum F) D = f.sum fun E c ↦ F E c D :=
  Finsupp.sum_apply

end EvalSupport

section EvalZero

variable {R : Type*} [AddCommMonoid R]

/-- `Finsupp.zero_apply`, at the wrapper type. Not `@[grind =]`: unlike Mathlib's
`Finsupp.zero_apply`, where `M` is recoverable from `(0 : α →₀ M)`, the wrapper's coercion
leaves `R` and its `AddCommMonoid` uninstantiable, and `grind` rejects the pattern. -/
@[simp] lemma zero_apply (D : HeckeCoset Δ H₁ H₂) :
    (0 : HeckeCosetModule Δ H₁ H₂ R) D = 0 :=
  Finsupp.zero_apply

/-- `Finsupp.add_apply`, at the wrapper type. -/
@[simp, grind =] lemma add_apply (f g : HeckeCosetModule Δ H₁ H₂ R) (D : HeckeCoset Δ H₁ H₂) :
    (f + g) D = f D + g D :=
  Finsupp.add_apply f g D

end EvalZero

section EvalSMul

variable {R : Type*} [Semiring R]

/-- `Finsupp.smul_apply`, at the wrapper type. -/
@[simp, grind =] lemma smul_apply (a : R) (f : HeckeCosetModule Δ H₁ H₂ R)
    (D : HeckeCoset Δ H₁ H₂) : (a • f) D = a * f D :=
  (Finsupp.smul_apply a f D).trans (smul_eq_mul _ _)

/-- `Finsupp.sum_smul_index`, at the wrapper type: a scalar pushes into a `Finsupp.sum`. -/
@[grind =] lemma sum_smul_index {N : Type*} [AddCommMonoid N] (a : R)
    (f : HeckeCosetModule Δ H₁ H₂ R) (F : HeckeCoset Δ H₁ H₂ → R → N) (h0 : ∀ D, F D 0 = 0) :
    (a • f).sum F = f.sum fun D c ↦ F D (a * c) :=
  Finsupp.sum_smul_index h0

end EvalSMul

end HeckeCosetModule
