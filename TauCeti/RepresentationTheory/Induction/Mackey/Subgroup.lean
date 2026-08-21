/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# The Mackey subgroup

For subgroups `H` and `K` of a group `G` and an element `s : G`, the *Mackey subgroup*

`mackeySubgroup s H K = K ⊓ sHs⁻¹`

is the subgroup on which the summand of the Mackey decomposition attached to the double coset
`KsH` lives: the conjugate representation `{}^s A` is a representation of `sHs⁻¹`, it is restricted
along `mackeySubgroup s H K ≤ sHs⁻¹` and then induced along `mackeySubgroup s H K ≤ K`.  The two
inclusions are pinned here as `TauCeti.mackeyToConjH` and `TauCeti.mackeyToK`; there is no second
intersection with `K`.

The reason the Mackey subgroup is the right object is geometric.  The group `K` acts on `G ⧸ H` by
translation, and the stabilizer of the coset `sH` is exactly `mackeySubgroup s H K`
(`TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`, resting on the description
`TauCeti.stabilizer_quotientGroup_mk` of the stabilizer in `G` as the conjugate `sHs⁻¹`).  The
`K`-orbit of `sH` is the image of the double coset `KsH`
(`TauCeti.preimage_orbit_eq_doubleCoset`), so the partition of `G ⧸ H` into `K`-orbits is the
partition of `G` into double cosets, and orbit-stabilizer turns each orbit into an index:
`|K·sH| = [K : K ⊓ sHs⁻¹]`.  This is the combinatorial content of the Mackey decomposition, and it
yields the classical double-coset size formula `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`
(`TauCeti.card_doubleCoset_mul_card_mackeySubgroup`).  The two facts about the translation action
that this rests on are generic group theory and live with the topics they belong to: the
stabilizer description in `TauCeti.GroupTheory.QuotientGroup.Basic` and the identification of a
double coset with an orbit in `TauCeti.GroupTheory.DoubleCoset.Orbits`.

Because the Mackey decomposition is indexed by double cosets while its summands are built from a
*chosen* representative, the dependence on the representative has to be pinned too: replacing `s`
by `k * s * h` with `k ∈ K` and `h ∈ H` conjugates the Mackey subgroup by `k`
(`TauCeti.mackeySubgroup_conj`), so the two subgroups are isomorphic
(`TauCeti.mackeySubgroupCongr`) and in particular have the same index in `K`.  Nothing here asserts
a canonical representative-independent summand; that would need coherent conjugation equivalences
of the representations themselves.

Everything in this file is a statement about subgroups of `G`, with no coefficients and no
representations; it is placed with the induction files because `mackeySubgroup` is the
roadmap-specific subgroup the induction and restriction of that layer run along.

## Main definitions

* `TauCeti.mackeySubgroup`: the subgroup `K ⊓ sHs⁻¹`.
* `TauCeti.mackeyToK`, `TauCeti.mackeyToConjH`: the two inclusions of the Mackey subgroup, into
  `K` and into `sHs⁻¹`.
* `TauCeti.mackeySubgroupCongr`: the isomorphism between the Mackey subgroups of two
  representatives of one double coset, and `TauCeti.mackeySubgroupOfCongr`, the same isomorphism
  with both sides read as subgroups of `K`.
* `TauCeti.mackeySubgroupSelfEquiv`: the identification of the Mackey subgroup of a representative
  lying in `H` with `H` itself.
* `TauCeti.mackeySubgroupNormalEquiv`: for normal `H`, the same identification at every
  representative.

## Main statements

* `TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`: the stabilizer of `sH` in `K` is the Mackey
  subgroup.
* `TauCeti.mackeySubgroup_conj`: changing the double-coset representative conjugates the Mackey
  subgroup.
* `TauCeti.card_orbit_eq_relIndex`: the `K`-orbit of `sH` has as many elements as the Mackey
  subgroup has index in `K`.
* `TauCeti.relIndex_mackeySubgroup_conj`: that index depends only on the double coset.
* `TauCeti.card_doubleCoset_mul_card_mackeySubgroup`: the double-coset size formula
  `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`.
* `TauCeti.stabilizer_smul_eq_mackeySubgroup_subgroupOf`: the same stabilizer description for an
  arbitrary `G`-set, at a translate `s • p`.

## References

Layer 3 of `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks to
"name the subgroup `mackeySubgroup s H K := K ⊓ (MulAut.conj s • H)`" carrying the two
homomorphisms `mackeyToK` and `mackeyToConjH`, and Layer 4, which asks for the invariance of the
Mackey data "under replacing `s` by `h₁ s h₂`" as its own lemma.  `mackeySubgroup` is pinned in the
accompanying `Suggested.lean`.

* [J.-P. Serre, *Linear Representations of Finite Groups*][serre1977], Section 7.3.
-/

public section

open MulAction
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- The **Mackey subgroup** `K ⊓ sHs⁻¹`: the subgroup carrying the summand of the Mackey
decomposition attached to the double coset `KsH`.

It comes with the two inclusions `TauCeti.mackeyToConjH` into `sHs⁻¹`, along which the conjugate
representation `{}^s A` is restricted, and `TauCeti.mackeyToK` into `K`, along which the result is
induced. -/
def mackeySubgroup (s : G) (H K : Subgroup G) : Subgroup G :=
  K ⊓ MulAut.conj s • H

variable {s : G} {H K : Subgroup G}

/-- The Mackey subgroup unfolded: it is the intersection of `K` with the conjugate `sHs⁻¹`. -/
theorem mackeySubgroup_def (s : G) (H K : Subgroup G) :
    mackeySubgroup s H K = K ⊓ MulAut.conj s • H :=
  (rfl)

@[simp]
theorem mem_mackeySubgroup_iff {x : G} :
    x ∈ mackeySubgroup s H K ↔ x ∈ K ∧ s⁻¹ * x * s ∈ H := by
  simp [mackeySubgroup_def]

/-- The Mackey subgroup is contained in `K`, the second subgroup argument. -/
theorem mackeySubgroup_le_right : mackeySubgroup s H K ≤ K :=
  inf_le_left

/-- The Mackey subgroup is contained in the conjugate `sHs⁻¹` of the first subgroup argument. -/
theorem mackeySubgroup_le_conj : mackeySubgroup s H K ≤ MulAut.conj s • H :=
  inf_le_right

variable (s H K) in
/-- The inclusion of the Mackey subgroup into `K`, along which the Mackey summand is induced. -/
def mackeyToK : mackeySubgroup s H K →* K :=
  Subgroup.inclusion mackeySubgroup_le_right

variable (s H K) in
/-- The inclusion of the Mackey subgroup into `sHs⁻¹`, along which the conjugate representation
`{}^s A` is restricted. -/
def mackeyToConjH : mackeySubgroup s H K →* (MulAut.conj s • H : Subgroup G) :=
  Subgroup.inclusion mackeySubgroup_le_conj

@[simp]
theorem coe_mackeyToK_apply (x : mackeySubgroup s H K) : (mackeyToK s H K x : G) = (x : G) :=
  (rfl)

@[simp]
theorem coe_mackeyToConjH_apply (x : mackeySubgroup s H K) :
    (mackeyToConjH s H K x : G) = (x : G) :=
  (rfl)

theorem mackeyToK_injective : Function.Injective (mackeyToK s H K) :=
  Subgroup.inclusion_injective _

theorem mackeyToConjH_injective : Function.Injective (mackeyToConjH s H K) :=
  Subgroup.inclusion_injective _

section Special

-- Not `@[simp]`: `simp` reaches `K ⊓ H` here through `mackeySubgroup_of_mem` and `one_mem`.
theorem mackeySubgroup_one (H K : Subgroup G) : mackeySubgroup 1 H K = K ⊓ H := by
  rw [mackeySubgroup_def, conj_one_smul]

/-- A representative lying in `H` gives back the plain intersection `K ⊓ H`. -/
@[simp]
theorem mackeySubgroup_of_mem (hs : s ∈ H) : mackeySubgroup s H K = K ⊓ H := by
  rw [mackeySubgroup_def, Subgroup.conj_smul_eq_self_of_mem hs]

/-- A representative lying in `H` has all of `H` for its Mackey subgroup, so the Mackey subgroup
sits inside `H` as the top subgroup. -/
theorem mackeySubgroup_subgroupOf_self_of_mem (hs : s ∈ H) :
    (mackeySubgroup s H H).subgroupOf H = ⊤ := by
  rw [mackeySubgroup_of_mem hs, inf_idem, Subgroup.subgroupOf_self]

/-- The Mackey subgroup of a representative lying in `H`, identified with `H` itself. -/
noncomputable def mackeySubgroupSelfEquiv (hs : s ∈ H) :
    ((mackeySubgroup s H H).subgroupOf H) ≃* H :=
  (MulEquiv.subgroupCongr (mackeySubgroup_subgroupOf_self_of_mem hs)).trans Subgroup.topEquiv

@[simp]
theorem coe_mackeySubgroupSelfEquiv_apply (hs : s ∈ H)
    (y : (mackeySubgroup s H H).subgroupOf H) :
    (mackeySubgroupSelfEquiv hs y : H) = (y : H) :=
  (rfl)

/-- For a normal `H` the Mackey subgroup does not depend on the representative at all: it is
`K ⊓ H` for every `s`.  This is why Clifford theory over a normal subgroup only ever sees the one
intersection. -/
@[simp]
theorem mackeySubgroup_of_normal [H.Normal] : mackeySubgroup s H K = K ⊓ H := by
  rw [mackeySubgroup_def, Subgroup.Normal.conj_smul_eq_self]

/-- For a normal subgroup, the Mackey subgroup at every representative is the whole subgroup.
This is the group equivalence used to read a Mackey intertwining space over `H` itself. -/
noncomputable def mackeySubgroupNormalEquiv (s : G) [H.Normal] :
    ((mackeySubgroup s H H).subgroupOf H) ≃* H :=
  (MulEquiv.subgroupCongr (by
    rw [mackeySubgroup_of_normal, inf_idem, Subgroup.subgroupOf_self])).trans Subgroup.topEquiv

@[simp]
theorem coe_mackeySubgroupNormalEquiv_apply (s : G) [H.Normal]
    (y : (mackeySubgroup s H H).subgroupOf H) :
    (mackeySubgroupNormalEquiv s y : H) = (y : H) := by
  simp [mackeySubgroupNormalEquiv]

/-- The homomorphism underlying `mackeySubgroupNormalEquiv` is the canonical inclusion into `H`. -/
@[simp]
theorem coe_mackeySubgroupNormalEquiv (s : G) [H.Normal] :
    (mackeySubgroupNormalEquiv (H := H) s : ((mackeySubgroup s H H).subgroupOf H) →* H) =
      ((mackeySubgroup s H H).subgroupOf H).subtype := by
  ext y
  exact congrArg Subtype.val (coe_mackeySubgroupNormalEquiv_apply s y)

/-- Inducing from the whole group leaves nothing to intersect: the Mackey subgroup is `K`. -/
-- Not `@[simp]`: `simp` reaches `K` here through `mackeySubgroup_of_mem` and `Subgroup.mem_top`.
theorem mackeySubgroup_top_left (s : G) (K : Subgroup G) : mackeySubgroup s ⊤ K = K := by
  ext x; simp

/-- Restricting to the whole group leaves the bare conjugate `sHs⁻¹`. -/
@[simp]
theorem mackeySubgroup_top_right (s : G) (H : Subgroup G) :
    mackeySubgroup s H ⊤ = MulAut.conj s • H := by
  ext x; simp

end Special

section Representative

/-- **Changing the representative of a double coset conjugates the Mackey subgroup.** Replacing
`s` by `k * s * h`, with `k ∈ K` and `h ∈ H`, leaves the double coset `KsH` unchanged and
replaces `K ⊓ sHs⁻¹` by its conjugate `k (K ⊓ sHs⁻¹) k⁻¹`. -/
theorem mackeySubgroup_conj {k h : G} (hk : k ∈ K) (hh : h ∈ H) :
    mackeySubgroup (k * s * h) H K = MulAut.conj k • mackeySubgroup s H K := by
  rw [mackeySubgroup_def, mackeySubgroup_def, Subgroup.smul_inf,
    Subgroup.conj_smul_eq_self_of_mem hk, conj_mul_smul, conj_mul_smul,
    Subgroup.conj_smul_eq_self_of_mem hh]

/-- The Mackey subgroups of two representatives of one double coset are isomorphic, by
conjugation.  This is the invariance that makes the *index* of the Mackey subgroup, and hence the
dimension of the Mackey summand, a function of the double coset alone. -/
def mackeySubgroupCongr {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G) :
    mackeySubgroup s H K ≃* mackeySubgroup (k * s * h) H K :=
  (Subgroup.equivSMul (MulAut.conj k) (mackeySubgroup s H K)).trans
    (MulEquiv.subgroupCongr (mackeySubgroup_conj hk hh).symm)

@[simp]
theorem coe_mackeySubgroupCongr_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (x : mackeySubgroup s H K) :
    (mackeySubgroupCongr hk hh s x : G) = k * (x : G) * k⁻¹ := by
  simp [mackeySubgroupCongr]

@[simp]
theorem coe_mackeySubgroupCongr_symm_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (y : mackeySubgroup (k * s * h) H K) :
    ((mackeySubgroupCongr hk hh s).symm y : G) = k⁻¹ * (y : G) * k := by
  have hy : k * ((mackeySubgroupCongr hk hh s).symm y : G) * k⁻¹ = (y : G) := by
    rw [← coe_mackeySubgroupCongr_apply hk hh s, MulEquiv.apply_symm_apply]
  rw [← hy]
  simp [mul_assoc]

/-- The same isomorphism as `TauCeti.mackeySubgroupCongr`, with both Mackey subgroups read
inside `K` along `TauCeti.mackeySubgroup_le_right`.  That is where the Mackey summands live, so
this is the form in which a change of representative is transported. -/
def mackeySubgroupOfCongr {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G) :
    (mackeySubgroup s H K).subgroupOf K ≃* (mackeySubgroup (k * s * h) H K).subgroupOf K :=
  ((Subgroup.subgroupOfEquivOfLe (mackeySubgroup_le_right (s := s) (H := H) (K := K))).trans
      (mackeySubgroupCongr hk hh s)).trans
    (Subgroup.subgroupOfEquivOfLe
      (mackeySubgroup_le_right (s := k * s * h) (H := H) (K := K))).symm

@[simp]
theorem coe_mackeySubgroupOfCongr_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (y : (mackeySubgroup s H K).subgroupOf K) :
    ((mackeySubgroupOfCongr hk hh s y : K) : G) = k * ((y : K) : G) * k⁻¹ := by
  simp [mackeySubgroupOfCongr]

@[simp]
theorem coe_mackeySubgroupOfCongr_symm_apply {k h : G} (hk : k ∈ K) (hh : h ∈ H) (s : G)
    (y : (mackeySubgroup (k * s * h) H K).subgroupOf K) :
    (((mackeySubgroupOfCongr hk hh s).symm y : K) : G) = k⁻¹ * ((y : K) : G) * k := by
  have hy : k * ((((mackeySubgroupOfCongr hk hh s).symm y : K)) : G) * k⁻¹ = ((y : K) : G) := by
    rw [← coe_mackeySubgroupOfCongr_apply hk hh s, MulEquiv.apply_symm_apply]
  rw [← hy]
  simp [mul_assoc]

end Representative

section Orbit

/-- **The Mackey subgroup is a stabilizer**: it is the stabilizer of the coset `sH` for the
translation action of `K` on `G ⧸ H`, read as a subgroup of `K`. -/
@[simp]
theorem stabilizer_eq_mackeySubgroup_subgroupOf (s : G) (H K : Subgroup G) :
    stabilizer (↥K) ((s : G ⧸ H)) = (mackeySubgroup s H K).subgroupOf K := by
  ext g
  -- `K` acts on `G ⧸ H` through `Subgroup.subtype K`, so stabilizing in `K` is stabilizing in
  -- `G` while lying in `K`, and `stabilizer_quotientGroup_mk` identifies the latter with `sHs⁻¹`.
  rw [Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff, mem_stabilizer_iff,
    compHom_smul_def (Subgroup.subtype K), Subgroup.coe_subtype, ← mem_stabilizer_iff,
    stabilizer_quotientGroup_mk, mem_conj_smul]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

/-- **Orbit-stabilizer for the Mackey subgroup**: the `K`-orbit of the coset `sH` has as many
elements as the Mackey subgroup has index in `K`. -/
theorem card_orbit_eq_relIndex (s : G) (H K : Subgroup G) :
    Nat.card (orbit K ((s : G ⧸ H))) = (mackeySubgroup s H K).relIndex K := by
  rw [Subgroup.relIndex, ← stabilizer_eq_mackeySubgroup_subgroupOf, Nat.card_coe_set_eq]
  exact (index_stabilizer K _).symm

/-- If `H` has finite index in `G` then the Mackey subgroup has finite index in `K`, so the Mackey
summand attached to `s` is induced along a finite-index inclusion. -/
instance instIsFiniteRelIndexMackeySubgroup (s : G) (H K : Subgroup G) [H.FiniteIndex] :
    (mackeySubgroup s H K).IsFiniteRelIndex K where
  relIndex_ne_zero := by
    rw [← card_orbit_eq_relIndex]
    have : Finite (orbit K ((s : G ⧸ H))) := Set.Finite.to_subtype (Set.toFinite _)
    exact Nat.card_ne_zero.2 ⟨⟨⟨_, mem_orbit_self _⟩⟩, this⟩

/-- **The double-coset size formula**: `|KsH| · |K ⊓ sHs⁻¹| = |K| · |H|`.

With `Nat.card`'s convention that an infinite type has cardinality `0`, this holds without any
finiteness hypothesis. -/
theorem card_doubleCoset_mul_card_mackeySubgroup (s : G) (H K : Subgroup G) :
    Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G)) * Nat.card (mackeySubgroup s H K)
      = Nat.card K * Nat.card H := by
  -- The double coset is `(Ks)H`, so `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient` counts
  -- it as `|H|` times the size of the image of `Ks` in `G ⧸ H`, and that image is the orbit.
  have himg : (QuotientGroup.mk : G → G ⧸ H) '' ((K : Set G) * {s}) = orbit K ((s : G ⧸ H)) :=
    QuotientGroup.mk_surjective.preimage_injective <| by
      rw [QuotientGroup.preimage_image_mk_eq_mul, preimage_orbit_eq_doubleCoset,
        DoubleCoset.doubleCoset]
  have hdc : Nat.card (DoubleCoset.doubleCoset s (K : Set G) (H : Set G))
      = Nat.card H * Nat.card (orbit K ((s : G ⧸ H))) := by
    rw [DoubleCoset.doubleCoset, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, himg]
  have hK : Nat.card (mackeySubgroup s H K) * (mackeySubgroup s H K).relIndex K = Nat.card K := by
    rw [Subgroup.relIndex,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe mackeySubgroup_le_right).toEquiv]
    exact Subgroup.card_mul_index _
  rw [hdc, card_orbit_eq_relIndex, mul_assoc, mul_comm ((mackeySubgroup s H K).relIndex K), hK,
    mul_comm]

/-- The index of the Mackey subgroup in `K` depends only on the double coset `KsH`, not on the
representative `s` chosen inside it: the two subgroups are conjugate by an element of `K`
(`TauCeti.mackeySubgroup_conj`), and conjugation fixes `K`, so it preserves the relative index. -/
theorem relIndex_mackeySubgroup_conj {s k h : G} {H K : Subgroup G} (hk : k ∈ K) (hh : h ∈ H) :
    (mackeySubgroup (k * s * h) H K).relIndex K = (mackeySubgroup s H K).relIndex K :=
  calc (mackeySubgroup (k * s * h) H K).relIndex K
      = (MulAut.conj k • mackeySubgroup s H K).relIndex (MulAut.conj k • K) := by
        rw [mackeySubgroup_conj hk hh, Subgroup.conj_smul_eq_self_of_mem hk]
    _ = (mackeySubgroup s H K).relIndex K := Subgroup.relIndex_pointwise_smul _ _ _

section Translate

variable {α : Type*} [MulAction G α]

/-- **The Mackey subgroup is a stabilizer, for an arbitrary action.** For a point `p` of any
`G`-set and `s : G`, the stabilizer of the translate `s • p` in a subgroup `Γ` is the Mackey
subgroup of `Γ` and `stabilizer G p` at `s`, read inside `Γ`.

`stabilizer_eq_mackeySubgroup_subgroupOf` above is the same statement for the translation action
of `Γ` on `G ⧸ H`. Neither implies the other: that one is stated for Mathlib's
`mulLeftCosetsCompSubtypeVal` action on cosets, this one for the restriction of scalars
`Subgroup.instMulAction`, and `MulAction ↥Γ (G ⧸ H)` has both. The general form is the one a sum
over the points of an arbitrary `G`-set needs. -/
theorem stabilizer_smul_eq_mackeySubgroup_subgroupOf (s : G) (Γ : Subgroup G) (p : α) :
    stabilizer (↥Γ) (s • p) = (mackeySubgroup s (stabilizer G p) Γ).subgroupOf Γ := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff, mem_stabilizer_iff, Subgroup.smul_def,
    mem_stabilizer_iff, mul_smul, mul_smul]
  exact ⟨fun hg => ⟨g.2, inv_smul_eq_iff.mpr hg⟩, fun hg => inv_smul_eq_iff.mp hg.2⟩

end Translate

end Orbit

end TauCeti
