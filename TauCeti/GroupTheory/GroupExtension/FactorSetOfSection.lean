/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.GroupExtension.OfFactorSet

/-!
# The factor set of a group extension with abelian kernel

`TauCeti.FactorSet.groupExtension` builds a group extension `1 → M → E_α → G → 1` out of a factor
set `α`. This file runs the construction backwards: an extension `S : GroupExtension M E G` with
abelian kernel, together with a set-theoretic section `σ` of its projection normalized by
`σ 1 = 1`, determines a factor set, and `S` is equivalent to the extension that factor set builds.
So every extension with abelian kernel *is* one of the twisted products, and — with
`TauCeti.FactorSet.nonempty_groupExtensionEquiv` for the converse direction — the classification of
such extensions is the classification of factor sets modulo coboundaries.

Two ingredients make the correspondence precise.

The action of `G` on `M` must be the one the extension itself provides. Conjugation in `E` moves
the copy of `M`, and because `M` is abelian this conjugation is trivial on the copy of `M`
(`TauCeti.GroupExtension.conjAct_inl`), hence depends only on the image in `G`
(`TauCeti.GroupExtension.conjAct_eq_of_rightHom_eq`); packaged as a homomorphism it is
`TauCeti.GroupExtension.conjActOfSection`, independent of the section used to write it down.
`TauCeti.GroupExtension.InducesAction S` says that this conjugation is the ambient
`MulDistribMulAction` of `G` on `M`. For a central extension the conjugation is trivial
(`TauCeti.GroupExtension.conjAct_eq_one_of_le_center`), so there `InducesAction` holds exactly for
the trivial action, the case in which a projective representation of `G` becomes a linear
representation of `E`.

The factor set itself measures the failure of the section to be a homomorphism:
`σ g * σ h * (σ (g * h))⁻¹` lies in the copy of `M`, and `TauCeti.GroupExtension.factorSetFun` is
its preimage. Changing the section changes the factor set by a coboundary
(`TauCeti.GroupExtension.isMulCoboundary₂_div`), so the class in `H²(G, M)` is an invariant of the
extension.

Only the descent of the conjugation action and the factor set itself need `M` abelian; the section
bookkeeping (`TauCeti.GroupExtension.factorSetFun`, `TauCeti.GroupExtension.normalizeSection`,
`TauCeti.GroupExtension.sectionDiff`) is stated for an arbitrary kernel.

## Main definitions

* `TauCeti.GroupExtension.conjActOfSection`: the action of `G` on an abelian kernel by conjugation.
* `TauCeti.GroupExtension.InducesAction`: the extension conjugates the kernel by the given action.
* `TauCeti.GroupExtension.factorSet`: the factor set of a normalized section.
* `TauCeti.GroupExtension.normalizeSection`: any section, corrected to send `1` to `1`.

## Main results

* `TauCeti.GroupExtension.section_mul`: `σ g * σ h = inl (α (g, h)) * σ (g * h)`, the defining
  property of the factor set.
* `TauCeti.GroupExtension.factorSetToGroupExtensionEquiv`: the extension is equivalent to the
  twisted product built from its factor set, and `TauCeti.GroupExtension.exists_factorSet` is the
  resulting existence statement for an arbitrary extension with abelian kernel.
* `TauCeti.GroupExtension.factorSet_canonicalSection`: reading the factor set off the twisted
  product built from `α`, using its canonical section, returns `α`.
* `TauCeti.GroupExtension.isMulCoboundary₂_div`: two normalized sections give factor sets that
  differ by a multiplicative `2`-coboundary.

## References

This continues the central-extension target of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` ("projective representations,
factor sets, and the Schur multiplier"), which asks that `H²(G, k^×)` classify central extensions
up to equivalence. See G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker
(1985), Ch. 1, and I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti.GroupExtension

open groupCohomology

universe u v w

variable {G : Type u} {M : Type v} {E : Type w} [Group G] [Group E]

section InlInv

variable [Group M] (S : GroupExtension M E G)

/-- The partial inverse of the inclusion `S.inl : M →* E` of a group extension. It is a genuine
inverse on the range of `S.inl` and junk off it, so it stays file-local: the public API records
its values through `S.inl` instead, in `TauCeti.GroupExtension.inl_factorSetFun` and
`TauCeti.GroupExtension.inl_sectionDiff`. -/
private noncomputable def inlInv (e : E) : M := Function.invFun S.inl e

variable {S}

@[simp]
private theorem inlInv_inl (m : M) : inlInv S (S.inl m) = m :=
  Function.leftInverse_invFun S.inl_injective m

private theorem inl_inlInv {e : E} (he : e ∈ S.inl.range) : S.inl (inlInv S e) = e :=
  Function.invFun_eq (MonoidHom.mem_range.1 he)

@[simp]
private theorem inlInv_one : inlInv S (1 : E) = 1 := by
  simpa using inlInv_inl (S := S) (1 : M)

end InlInv

section Conj

variable [Group M] {S : GroupExtension M E G}

/-- **A central extension acts trivially on its kernel.** -/
theorem conjAct_eq_one_of_le_center (h : S.inl.range ≤ Subgroup.center E) (e : E) :
    S.conjAct e = 1 := by
  ext m
  refine S.inl_injective ?_
  rw [GroupExtension.inl_conjAct_comm, Subgroup.mem_center_iff.1 (h ⟨m, rfl⟩) e,
    mul_inv_cancel_right]
  simp

variable (S) in
/-- The extension `S` conjugates its kernel by the ambient action of `G` on `M`. This is the
compatibility that makes `TauCeti.GroupExtension.factorSet` a `TauCeti.FactorSet` for that action;
for a central extension it says the ambient action is trivial. -/
def InducesAction [MulDistribMulAction G M] : Prop :=
  ∀ (e : E) (m : M), S.conjAct e m = S.rightHom e • m

/-- The image of the kernel is conjugated by a section according to the ambient action. -/
theorem inl_smul [MulDistribMulAction G M] (σ : S.Section) (hact : InducesAction S) (g : G)
    (m : M) : S.inl (g • m) = σ g * S.inl m * (σ g)⁻¹ := by
  have h := hact (σ g) m
  rw [GroupExtension.Section.rightHom_section] at h
  rw [← h, GroupExtension.inl_conjAct_comm]

end Conj

section ConjAct

variable [CommGroup M] {S : GroupExtension M E G}

/-- Conjugating an abelian kernel by an element of the kernel does nothing. -/
theorem conjAct_inl (m : M) : S.conjAct (S.inl m) = 1 := by
  ext n
  refine S.inl_injective ?_
  rw [GroupExtension.inl_conjAct_comm, ← map_inv, ← map_mul, ← map_mul, mul_comm m n,
    mul_inv_cancel_right]
  simp

/-- Conjugation of an abelian kernel depends only on the image of the conjugating element in the
quotient. -/
theorem conjAct_eq_of_rightHom_eq {e e' : E} (h : S.rightHom e = S.rightHom e') :
    S.conjAct e = S.conjAct e' := by
  obtain ⟨m, hm⟩ : e * e'⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have he : e = S.inl m * e' := by rw [hm, inv_mul_cancel_right]
  rw [he, map_mul, conjAct_inl, one_mul]

/-- **The action of `G` on an abelian kernel.** Conjugation in `E` descends along the projection
to `G` because it is trivial on the kernel, so any section presents it as a homomorphism
`G →* MulAut M`; `TauCeti.GroupExtension.conjActOfSection_eq` says the presentation does not depend
on the section. Mathlib's `GroupExtension.Splitting.conjAct` is the special case of a section that
is a homomorphism, which exists only for a split extension. -/
noncomputable def conjActOfSection (σ : S.Section) : G →* MulAut M where
  toFun g := S.conjAct (σ g)
  map_one' := by
    rw [conjAct_eq_of_rightHom_eq (e' := (1 : E)) (by simp), map_one]
  map_mul' g h := by
    rw [conjAct_eq_of_rightHom_eq (e' := σ g * σ h) (by simp), map_mul]

@[simp]
theorem conjActOfSection_apply (σ : S.Section) (g : G) : conjActOfSection σ g = S.conjAct (σ g) :=
  (rfl)

theorem conjActOfSection_eq (σ σ' : S.Section) :
    conjActOfSection σ = conjActOfSection (S := S) σ' := by
  ext g m
  exact DFunLike.congr_fun (conjAct_eq_of_rightHom_eq (S := S) (e := σ g) (e' := σ' g) (by simp)) m

theorem InducesAction.conjActOfSection_eq_toMulAut [MulDistribMulAction G M]
    (hact : InducesAction S) (σ : S.Section) :
    conjActOfSection σ = MulDistribMulAction.toMulAut G M := by
  ext g m
  simpa using hact (σ g) m

end ConjAct

section FactorSetFun

variable [Group M] {S : GroupExtension M E G}

/-- **The factor set of a section**, as a bare function: `σ g * σ h * (σ (g * h))⁻¹` lies in the
kernel, and this is its preimage there. It is a genuine factor set once the kernel is abelian, the
section is normalized and the ambient action is the conjugation action; see
`TauCeti.GroupExtension.factorSet`. -/
noncomputable def factorSetFun (σ : S.Section) (p : G × G) : M :=
  inlInv S (σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹)

@[simp]
theorem inl_factorSetFun (σ : S.Section) (g h : G) :
    S.inl (factorSetFun σ (g, h)) = σ g * σ h * (σ (g * h))⁻¹ :=
  inl_inlInv (GroupExtension.Section.mul_mul_mul_inv_mem_range_inl σ g h)

/-- **The factor set measures the failure of a section to be a homomorphism.** This matches the
convention of `TauCeti.FactorSet.canonicalSection_mul`. -/
theorem section_mul (σ : S.Section) (g h : G) :
    (σ g : E) * σ h = S.inl (factorSetFun σ (g, h)) * σ (g * h) := by
  rw [inl_factorSetFun, inv_mul_cancel_right]

theorem factorSetFun_one_one (σ : S.Section) (hσ : σ 1 = 1) : factorSetFun σ (1, 1) = 1 := by
  refine S.inl_injective ?_
  simp [hσ]

end FactorSetFun

section FactorSet

variable [CommGroup M] {S : GroupExtension M E G} [MulDistribMulAction G M]

theorem isMulCocycle₂_factorSetFun (σ : S.Section) (hact : InducesAction S) :
    IsMulCocycle₂ (factorSetFun σ) := by
  intro g₁ g₂ g₃
  refine S.inl_injective ?_
  rw [mul_comm (factorSetFun σ (g₁ * g₂, g₃)), map_mul, map_mul, inl_smul σ hact]
  simp only [inl_factorSetFun]
  rw [mul_assoc g₁ g₂ g₃]
  group

/-- **The factor set of a normalized section** of an extension whose conjugation action on its
abelian kernel is the ambient one. -/
noncomputable def factorSet (σ : S.Section) (hσ : σ 1 = 1) (hact : InducesAction S) :
    FactorSet G M where
  toFun := factorSetFun σ
  isMulCocycle₂' := isMulCocycle₂_factorSetFun σ hact
  map_one_one' := factorSetFun_one_one σ hσ

@[simp]
theorem coe_factorSet (σ : S.Section) (hσ : σ 1 = 1) (hact : InducesAction S) :
    ⇑(factorSet σ hσ hact) = factorSetFun σ :=
  FactorSet.coe_mk _ _ _

theorem inl_factorSet (σ : S.Section) (hσ : σ 1 = 1) (hact : InducesAction S) (g h : G) :
    S.inl (factorSet σ hσ hact (g, h)) = σ g * σ h * (σ (g * h))⁻¹ := by
  simp only [coe_factorSet]
  exact inl_factorSetFun σ g h

end FactorSet

section Equiv

variable [CommGroup M] {S : GroupExtension M E G} [MulDistribMulAction G M]
  (σ : S.Section) (hσ : σ 1 = 1) (hact : InducesAction S)

/-- The comparison homomorphism `⟨a, g⟩ ↦ inl a * σ g` from the twisted product built from the
factor set of `σ` back to the extension. It is an isomorphism; see
`TauCeti.GroupExtension.factorSetToGroupExtensionEquiv`. -/
noncomputable def ofFactorSetHom : (factorSet σ hσ hact).Extension →* E where
  toFun x := S.inl x.left * σ x.right
  map_one' := by simp [hσ]
  map_mul' x y := by
    simp only [FactorSet.Extension.mul_left, FactorSet.Extension.mul_right, map_mul,
      inl_smul σ hact, coe_factorSet, inl_factorSetFun]
    group

@[simp]
theorem ofFactorSetHom_apply (x : (factorSet σ hσ hact).Extension) :
    ofFactorSetHom σ hσ hact x = S.inl x.left * σ x.right :=
  (rfl)

/-- **An extension with abelian kernel is the twisted product built from its factor set.** -/
noncomputable def factorSetToGroupExtensionEquiv :
    (factorSet σ hσ hact).groupExtension.Equiv S :=
  GroupExtension.Equiv.ofMonoidHom (ofFactorSetHom σ hσ hact)
    (by ext a; simp [hσ])
    (by ext x; simp)

@[simp]
theorem factorSetToGroupExtensionEquiv_apply (x : (factorSet σ hσ hact).Extension) :
    factorSetToGroupExtensionEquiv σ hσ hact x = S.inl x.left * σ x.right :=
  (rfl)

end Equiv

section Normalize

variable [Group M] {S : GroupExtension M E G}

open scoped Classical in
/-- Any section can be corrected at the identity to a normalized one; see
`TauCeti.GroupExtension.normalizeSection_one` and
`TauCeti.GroupExtension.normalizeSection_apply`. -/
noncomputable def normalizeSection (σ : S.Section) : S.Section where
  toFun g := if g = 1 then 1 else σ g
  rightInverse_rightHom g := by by_cases hg : g = 1 <;> simp [hg]

@[simp]
theorem normalizeSection_one (σ : S.Section) : normalizeSection σ 1 = 1 := by
  simp [normalizeSection]

@[simp]
theorem normalizeSection_apply (σ : S.Section) (g : G) [Decidable (g = 1)] :
    normalizeSection σ g = if g = 1 then 1 else σ g := by
  by_cases hg : g = 1 <;> simp [normalizeSection, hg]

@[simp]
theorem normalizeSection_apply_of_ne (σ : S.Section) {g : G} (hg : g ≠ 1) :
    normalizeSection σ g = σ g := by
  simp [normalizeSection, hg]

end Normalize

section Exists

variable [CommGroup M] {S : GroupExtension M E G} [MulDistribMulAction G M]

/-- **Every group extension with abelian kernel arises from a factor set**, provided the ambient
action of `G` on the kernel is the one the extension conjugates by. -/
theorem exists_factorSet (hact : InducesAction S) :
    ∃ α : FactorSet G M, Nonempty (α.groupExtension.Equiv S) :=
  ⟨_, ⟨factorSetToGroupExtensionEquiv (normalizeSection S.surjInvRightHom)
    (normalizeSection_one _) hact⟩⟩

end Exists

section RoundTrip

variable [CommGroup M] [MulDistribMulAction G M] (α : FactorSet G M)

/-- The twisted product built from a factor set conjugates its kernel by the given action of `G`. -/
theorem inducesAction_groupExtension : InducesAction α.groupExtension := by
  intro x a
  refine α.groupExtension.inl_injective ?_
  rw [GroupExtension.inl_conjAct_comm]
  simp only [FactorSet.groupExtension_inl, FactorSet.groupExtension_rightHom,
    FactorSet.rightHom_apply]
  rw [FactorSet.mul_inl, mul_inv_cancel_right]

/-- **Reading the factor set back off the extension it builds returns it unchanged**, when the
factor set is read off the canonical section. -/
theorem factorSet_canonicalSection :
    factorSet α.canonicalSection α.canonicalSection_one (inducesAction_groupExtension α) = α := by
  ext p
  obtain ⟨g, h⟩ := p
  refine FactorSet.inl_injective α ?_
  rw [← FactorSet.groupExtension_inl,
    inl_factorSet α.canonicalSection α.canonicalSection_one (inducesAction_groupExtension α) g h,
    FactorSet.groupExtension_inl, FactorSet.canonicalSection_mul, mul_inv_cancel_right]

end RoundTrip

section SectionDiff

variable [Group M] {S : GroupExtension M E G} (σ σ' : S.Section)

/-- The difference of two sections, as a function `G → M`: `σ g * (σ' g)⁻¹` lies in the kernel, and
this is its preimage there. It is the rescaling relating the two factor sets; see
`TauCeti.GroupExtension.isMulCoboundary₂_div`. -/
noncomputable def sectionDiff (g : G) : M := inlInv S (σ g * (σ' g)⁻¹)

@[simp]
theorem inl_sectionDiff (g : G) : S.inl (sectionDiff σ σ' g) = σ g * (σ' g)⁻¹ :=
  inl_inlInv (GroupExtension.Section.mul_inv_mem_range_inl σ σ' g)

end SectionDiff

section Coboundary

variable [CommGroup M] {S : GroupExtension M E G} (σ σ' : S.Section) [MulDistribMulAction G M]
  (hσ : σ 1 = 1) (hσ' : σ' 1 = 1) (hact : InducesAction S)

/-- **Two normalized sections give cohomologous factor sets.** Combined with
`TauCeti.FactorSet.nonempty_groupExtensionEquiv`, which turns a coboundary back into an equivalence
of extensions, this says the class of the factor set in `H²(G, M)` is an invariant of the
extension. -/
theorem isMulCoboundary₂_div :
    IsMulCoboundary₂ fun p : G × G => factorSet σ hσ hact p / factorSet σ' hσ' hact p := by
  refine ⟨sectionDiff σ σ', fun g h => ?_⟩
  have e₁ : (σ g : E) * σ h
      = S.inl (factorSet σ hσ hact (g, h) * sectionDiff σ σ' (g * h)) * σ' (g * h) := by
    rw [map_mul, inl_factorSet, inl_sectionDiff]
    group
  have e₂ : (σ g : E) * σ h
      = S.inl (g • sectionDiff σ σ' h * sectionDiff σ σ' g * factorSet σ' hσ' hact (g, h))
        * σ' (g * h) := by
    rw [map_mul, map_mul, inl_smul σ hact, inl_sectionDiff, inl_sectionDiff, inl_factorSet]
    group
  have key := S.inl_injective (mul_right_cancel (e₁.symm.trans e₂))
  rw [div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul, ← key]

end Coboundary

end TauCeti.GroupExtension
