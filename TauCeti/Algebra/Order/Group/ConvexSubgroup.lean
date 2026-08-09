/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Quotient

/-!
# Convex subgroups of linearly ordered groups

A subgroup of a group with a linear order is *convex* if it contains every element
lying between two of its members. That definition, the closure and preimage constructions
and the elementary exclusion lemmas need no more than a group with a linear order. The
results that make convex subgroups useful for valuation theory need the value-group
setting, a linearly ordered commutative group: there any two convex subgroups are
comparable, each has a largest convex subgroup avoiding a given element, and the quotient
by one carries a linear order making it an ordered group again — so convex subgroups are
exactly the kernels of the order-compatible quotients of a value group.
This file develops the basic theory following Wedhorn, *Adic Spaces* (arXiv:1910.05934v1),
§1.4 and §7.1; the convex subgroup `cΓ_v(I)` of Wedhorn Definition 7.3 is intended to be
built from `closure` in the forthcoming valuation-spectrum development of `Spv (A, I)`.

## Main definitions

* `TauCeti.ConvexSubgroup Γ` : The type of order-convex subgroups of `Γ`.
* `TauCeti.ConvexSubgroup.quotientLinearOrder` : The linear order on `Γ ⧸ H.toSubgroup`
  induced by a convex subgroup `H`.
* `TauCeti.ConvexSubgroup.quotientIsOrderedMonoid` : That order is compatible with the
  quotient group structure.
* `TauCeti.ConvexSubgroup.closure S` : The smallest convex subgroup containing a set.
* `TauCeti.ConvexSubgroup.maxAvoid hγ` : The largest convex subgroup avoiding `γ ≠ 1`.
* `TauCeti.ConvexSubgroup.comap` : The preimage of a convex subgroup under a monotone
  monoid homomorphism.

## Main results

* `TauCeti.ConvexSubgroup.le_total` : Convex subgroups are totally ordered by
  inclusion.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §1.4, §7.1

Ported from the AINTLIB development `projects/AdicSpaces/Adic spaces/OrderedGroupConvex.lean`,
adapted to the pinned Mathlib: the quotient order is obtained from Mathlib's condensation
API (`Quotient.instLinearOrder` over order-connected fibers) rather than constructed by hand.
-/

public section

namespace TauCeti

variable (Γ : Type*) [Group Γ] [LinearOrder Γ]

/-- A **convex subgroup** of a group `Γ` with a linear order is a subgroup
that is order-convex: if `a ≤ x ≤ b` and `a, b ∈ H`, then `x ∈ H`. -/
structure ConvexSubgroup extends Subgroup Γ where
  ordConnected' : carrier.OrdConnected

namespace ConvexSubgroup

variable {Γ}

instance : SetLike (ConvexSubgroup Γ) Γ where
  coe H := H.carrier
  coe_injective := by
    intro ⟨H₁, _⟩ ⟨H₂, _⟩ h
    congr 1
    exact Subgroup.ext (Set.ext_iff.mp h)

instance : SubgroupClass (ConvexSubgroup Γ) Γ where
  mul_mem {H} := H.toSubgroup.mul_mem'
  one_mem {H} := H.toSubgroup.one_mem'
  inv_mem {H} := H.toSubgroup.inv_mem'

@[ext]
theorem ext {H₁ H₂ : ConvexSubgroup Γ} (h : ∀ x, x ∈ H₁ ↔ x ∈ H₂) : H₁ = H₂ :=
  SetLike.ext h

/-- A convex subgroup is an order-connected subset. -/
theorem ordConnected (H : ConvexSubgroup Γ) : (H : Set Γ).OrdConnected :=
  H.ordConnected'

/-- Convexity: if `a, b ∈ H` and `a ≤ x ≤ b`, then `x ∈ H`. -/
theorem convex (H : ConvexSubgroup Γ) {a b x : Γ} (ha : a ∈ H) (hb : b ∈ H)
    (h₁ : a ≤ x) (h₂ : x ≤ b) : x ∈ H :=
  H.ordConnected'.out ha hb ⟨h₁, h₂⟩

/-- A convex subgroup contains every element between `1` and one of its members. -/
theorem mem_of_one_le_le {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (h1 : 1 ≤ x) (hx : x ≤ h) : x ∈ H :=
  H.convex (one_mem H) hh h1 hx

/-- A convex subgroup contains every element between one of its members and `1`. -/
theorem mem_of_le_le_one {H : ConvexSubgroup Γ} {x h : Γ}
    (hh : h ∈ H) (hx : h ≤ x) (h1 : x ≤ 1) : x ∈ H :=
  H.convex hh (one_mem H) hx h1

/-- The trivial subgroup `{1}` is convex. -/
instance : Bot (ConvexSubgroup Γ) where
  bot :=
    { toSubgroup := ⊥
      ordConnected' := by
        have h : (⊥ : Subgroup Γ).carrier = ({1} : Set Γ) := by
          ext x
          simp
        rw [h]
        exact Set.ordConnected_singleton }

/-- The full group is a convex subgroup. -/
instance : Top (ConvexSubgroup Γ) where
  top :=
    { toSubgroup := ⊤
      ordConnected' := by
        have h : (⊤ : Subgroup Γ).carrier = (Set.univ : Set Γ) := by
          ext x
          simp
        rw [h]
        exact Set.ordConnected_univ }

@[simp]
theorem mem_bot {x : Γ} : x ∈ (⊥ : ConvexSubgroup Γ) ↔ x = 1 :=
  Subgroup.mem_bot

@[simp]
theorem mem_top {x : Γ} : x ∈ (⊤ : ConvexSubgroup Γ) :=
  trivial

/-- Convex subgroups are ordered by inclusion. -/
instance : PartialOrder (ConvexSubgroup Γ) :=
  PartialOrder.ofSetLike (ConvexSubgroup Γ) Γ

instance : OrderBot (ConvexSubgroup Γ) where
  bot_le H _ hx := mem_bot.mp hx ▸ one_mem H

instance : OrderTop (ConvexSubgroup Γ) where
  le_top _ _ _ := mem_top

/-! ### Elements outside a convex subgroup -/

/-- An excluded element below `1` lies below every member. -/
theorem lt_of_not_mem_of_lt_one (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1)
    {h : Γ} (hh : h ∈ H) : γ < h := by
  by_contra hle
  push Not at hle
  exact hγ (H.convex hh (one_mem H) hle hγ1.le)

/-- An excluded element above `1` lies above every member. -/
theorem lt_of_not_mem_of_one_lt (H : ConvexSubgroup Γ) {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ)
    {h : Γ} (hh : h ∈ H) : h < γ := by
  by_contra hle
  push Not at hle
  exact hγ (H.convex (one_mem H) hh hγ1.le hle)

/-- Elements above an excluded element above `1` are excluded, by convexity. -/
theorem not_mem_of_not_mem_of_one_lt_le (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : 1 < γ) {x : Γ} (hγx : γ ≤ x) : x ∉ H :=
  fun hx ↦ hγ (H.convex (one_mem H) hx hγ1.le hγx)

/-- Elements below an excluded element below `1` are excluded, by convexity. -/
theorem not_mem_of_not_mem_of_le_lt_one (H : ConvexSubgroup Γ)
    {γ : Γ} (hγ : γ ∉ H) (hγ1 : γ < 1) {x : Γ} (hxγ : x ≤ γ) : x ∉ H :=
  fun hx ↦ hγ (H.convex hx (one_mem H) hxγ hγ1.le)

/-! ### The smallest convex subgroup containing a set -/

/-- The smallest convex subgroup containing a set `S`, as the intersection of all convex
subgroups containing `S`. The convex subgroup `cΓ_v(I)` of Wedhorn Definition 7.3 will be
an instance of this construction. -/
def closure (S : Set Γ) : ConvexSubgroup Γ where
  toSubgroup :=
    { carrier := {x | ∀ H : ConvexSubgroup Γ, S ⊆ H → x ∈ H}
      one_mem' := fun H _ ↦ one_mem H
      mul_mem' := fun ha hb H hS ↦ mul_mem (ha H hS) (hb H hS)
      inv_mem' := fun ha H hS ↦ inv_mem (ha H hS) }
  ordConnected' := ⟨fun _ ha _ hb _ hz H hS ↦ H.ordConnected'.out (ha H hS) (hb H hS) hz⟩

/-- Membership in the convex closure: membership in every convex subgroup containing the
generating set. Deliberately not a `simp` lemma — as a normal form it would rewrite every
`x ∈ closure S` into the defining intersection, exposing the construction. `closure_le` is
the universal property `simp` should use instead. -/
theorem mem_closure {S : Set Γ} {x : Γ} :
    x ∈ closure S ↔ ∀ H : ConvexSubgroup Γ, S ⊆ H → x ∈ H :=
  Iff.rfl

/-- The generating set is contained in its convex closure. -/
theorem subset_closure (S : Set Γ) : S ⊆ closure S :=
  fun _ hx _ hS ↦ hS hx

/-- Universal property: `closure S` lies inside a convex subgroup iff the generating set
does. -/
@[simp]
theorem closure_le {S : Set Γ} {H : ConvexSubgroup Γ} : closure S ≤ H ↔ S ⊆ H :=
  ⟨fun h ↦ (subset_closure S).trans h, fun hS _ hx ↦ hx H hS⟩

/-! ### Preimages of convex subgroups -/

/-- The preimage of a convex subgroup under an ordered group homomorphism is a convex
subgroup. This lifts convex subgroups from quotient value groups back to the original
value group. -/
def comap {Δ F : Type*} [Group Δ] [LinearOrder Δ] [FunLike F Γ Δ]
    [MonoidHomClass F Γ Δ] [OrderHomClass F Γ Δ] (f : F)
    (K : ConvexSubgroup Δ) : ConvexSubgroup Γ where
  toSubgroup := K.toSubgroup.comap (MonoidHomClass.toMonoidHom f)
  ordConnected' := K.ordConnected'.preimage_mono (OrderHomClass.monotone f)

@[simp]
theorem mem_comap {Δ F : Type*} [Group Δ] [LinearOrder Δ] [FunLike F Γ Δ]
    [MonoidHomClass F Γ Δ] [OrderHomClass F Γ Δ] {f : F}
    {K : ConvexSubgroup Δ} {x : Γ} :
    x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl

/-! ### Total ordering of convex subgroups -/

section TotalOrder

variable {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]

/-- Any two convex subgroups are comparable. -/
protected theorem le_total (H₁ H₂ : ConvexSubgroup Γ) : H₁ ≤ H₂ ∨ H₂ ≤ H₁ := by
  by_contra h
  push Not at h
  obtain ⟨hne₁, hne₂⟩ := h
  obtain ⟨a, haH₁, haH₂⟩ := Set.not_subset.mp fun hsub ↦ hne₁ fun x hx ↦ hsub hx
  have ha1 : a ≠ 1 := fun h ↦ haH₂ (h ▸ one_mem H₂)
  refine hne₂ fun b hb ↦ ?_
  have hainv : a⁻¹ ∉ H₂ := inv_mem_iff.not.mpr haH₂
  rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
  · have hab : a < b := H₂.lt_of_not_mem_of_lt_one haH₂ ha_lt hb
    have hba : b < a⁻¹ := H₂.lt_of_not_mem_of_one_lt hainv (one_lt_inv_of_inv ha_lt) hb
    exact H₁.convex haH₁ (inv_mem haH₁) hab.le hba.le
  · have hba : b < a := H₂.lt_of_not_mem_of_one_lt haH₂ ha_gt hb
    have hab : a⁻¹ < b := H₂.lt_of_not_mem_of_lt_one hainv (inv_lt_one_of_one_lt ha_gt) hb
    exact H₁.convex (inv_mem haH₁) haH₁ hab.le hba.le

noncomputable instance : LinearOrder (ConvexSubgroup Γ) :=
  { (inferInstance : PartialOrder (ConvexSubgroup Γ)) with
    le_total := ConvexSubgroup.le_total
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _
    toDecidableLT := Classical.decRel _ }

/-! ### The largest convex subgroup avoiding an element -/

/-- An element bounded in absolute value by a member of a convex subgroup is a member. -/
theorem mem_of_mabs_le_mabs {H : ConvexSubgroup Γ} {x h : Γ} (hh : h ∈ H)
    (hx : |x|ₘ ≤ |h|ₘ) : x ∈ H := by
  have habs : |h|ₘ ∈ H := by
    rcases mabs_choice h with e | e <;> rw [e]
    · exact hh
    · exact inv_mem hh
  exact H.convex (inv_mem habs) habs (by simpa using (mabs_le.mp hx).1) (mabs_le.mp hx).2

/-- The largest convex subgroup avoiding an element `γ ≠ 1`: Mathlib's Archimedean open ball
at the class of `γ`, that is, the elements of strictly larger Archimedean class. Reusing
`MulArchimedeanClass.ballSubgroup` rather than building the directed union of all convex
subgroups avoiding `γ` gives the same subgroup with the group structure already in place. -/
noncomputable def maxAvoid {γ : Γ} (hγ : γ ≠ 1) : ConvexSubgroup Γ where
  toSubgroup := MulArchimedeanClass.ballSubgroup (MulArchimedeanClass.mk γ)
  ordConnected' := by
    have htop : MulArchimedeanClass.mk γ ≠ ⊤ := fun h ↦ hγ (MulArchimedeanClass.mk_eq_top_iff.mp h)
    constructor
    intro a ha b hb x hx
    simp only [Subgroup.mem_carrier, MulArchimedeanClass.mem_ballSubgroup_iff htop] at ha hb ⊢
    exact lt_of_lt_of_le (lt_min ha hb)
      (MulArchimedeanClass.min_le_mk_of_le_of_le hx.1 hx.2)

/-- Membership in `maxAvoid hγ`: a strictly larger Archimedean class than `γ`. -/
@[simp]
theorem mem_maxAvoid_iff {γ : Γ} {hγ : γ ≠ 1} {x : Γ} :
    x ∈ maxAvoid hγ ↔ MulArchimedeanClass.mk γ < MulArchimedeanClass.mk x :=
  MulArchimedeanClass.mem_ballSubgroup_iff
    (fun h ↦ hγ (MulArchimedeanClass.mk_eq_top_iff.mp h))

/-- The avoided element is not a member. -/
theorem not_mem_maxAvoid {γ : Γ} (hγ : γ ≠ 1) : γ ∉ maxAvoid hγ := by
  rw [mem_maxAvoid_iff (hγ := hγ)]
  exact lt_irrefl _

/-- Universal property: a convex subgroup lies inside `maxAvoid hγ` iff it excludes
`γ`. -/
@[simp]
theorem le_maxAvoid {γ : Γ} {hγ : γ ≠ 1} {H : ConvexSubgroup Γ} :
    H ≤ maxAvoid hγ ↔ γ ∉ H := by
  refine ⟨fun h hγH ↦ not_mem_maxAvoid hγ (h hγH), fun h x hx ↦ ?_⟩
  rw [mem_maxAvoid_iff (hγ := hγ)]
  by_contra hle
  rw [not_lt, MulArchimedeanClass.mk_le_mk] at hle
  obtain ⟨n, hn⟩ := hle
  exact h (mem_of_mabs_le_mabs (H.toSubgroup.pow_mem hx n) (hn.trans_eq (mabs_pow n x).symm))

/-! ### The quotient linear order -/

section Quotient

/-- The fibers of the projection to the quotient by a convex subgroup are the cosets, which
are order-connected by convexity. This is the hypothesis Mathlib's condensation API takes as
an instance (`Quotient.mk_le_mk`, `Quotient.instLinearOrder`); it is supplied explicitly at
both call sites rather than registered globally, since as an instance its head would match
every quotient of a linear order and send synthesis down a blind alley. -/
private theorem ordConnected_leftRel_fiber (H : ConvexSubgroup Γ) :
    ∀ q : Γ ⧸ H.toSubgroup,
      Set.OrdConnected (Quotient.mk (QuotientGroup.leftRel H.toSubgroup) ⁻¹' {q}) := by
  intro q
  constructor
  induction q using Quotient.inductionOn with | _ b =>
  intro x hx y hy z hz
  have hx' : x⁻¹ * b ∈ H.toSubgroup := QuotientGroup.eq.mp hx
  have hy' : y⁻¹ * b ∈ H.toSubgroup := QuotientGroup.eq.mp hy
  have hz' : z⁻¹ * b ∈ H.toSubgroup :=
    H.convex hy' hx' (mul_le_mul_left (inv_le_inv' hz.2) b)
      (mul_le_mul_left (inv_le_inv' hz.1) b)
  exact QuotientGroup.eq.mpr hz'

variable (H : ConvexSubgroup Γ)

/-- The quotient of `Γ` by a convex subgroup `H` is linearly ordered, as the condensation
of `Γ` along the order-connected cosets. The body is not exposed: consumers work through
`quotient_le_iff` rather than by unfolding the condensation. -/
@[no_expose]
noncomputable instance quotientLinearOrder : LinearOrder (Γ ⧸ H.toSubgroup) :=
  @Quotient.instLinearOrder Γ (QuotientGroup.leftRel H.toSubgroup) _
    (ordConnected_leftRel_fiber H) (fun _ _ ↦ Classical.dec _)

omit [IsOrderedMonoid Γ] in
/-- The coercion `Γ → Γ ⧸ H.toSubgroup` is `Quotient.mk` of the left-coset setoid; this
names the definitional equality so that the condensation API applies by rewriting. -/
private theorem coe_eq_mk (a : Γ) :
    (a : Γ ⧸ H.toSubgroup) = Quotient.mk (QuotientGroup.leftRel H.toSubgroup) a :=
  rfl

/-- The defining unfolding of `≤` on the quotient by a convex subgroup:
`[a] ≤ [b]` iff `b⁻¹ * a ≤ 1` or `b⁻¹ * a ∈ H`. -/
@[simp]
theorem quotient_le_iff (a b : Γ) :
    ((a : Γ ⧸ H.toSubgroup) ≤ (b : Γ ⧸ H.toSubgroup)) ↔
      (b⁻¹ * a ≤ 1 ∨ b⁻¹ * a ∈ H.toSubgroup) := by
  rw [coe_eq_mk, coe_eq_mk, Quotient.mk_le_mk (H := ordConnected_leftRel_fiber H)]
  refine or_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ ?_
  · simpa using mul_le_mul_right h b⁻¹
  · simpa using mul_le_mul_right h b
  · constructor
    · intro h
      simpa [mul_inv_rev] using H.toSubgroup.inv_mem (QuotientGroup.leftRel_apply.mp h)
    · intro h
      exact QuotientGroup.leftRel_apply.mpr
        (by simpa [mul_inv_rev] using H.toSubgroup.inv_mem h)

/-- The quotient linear order is compatible with the group operation. -/
instance quotientIsOrderedMonoid : IsOrderedMonoid (Γ ⧸ H.toSubgroup) where
  mul_le_mul_left a b hab c := by
    induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
    induction c using Quotient.inductionOn with | _ c =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, quotient_le_iff] at *
    have h : (b * c)⁻¹ * (a * c) = b⁻¹ * a := by
      simp [mul_inv_rev, mul_comm, mul_assoc]
    rw [h]
    exact hab

end Quotient

end TotalOrder

end ConvexSubgroup

end TauCeti
