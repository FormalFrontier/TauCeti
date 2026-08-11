/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.GroupTheory.DoubleCoset.Basic

/-!
# Moving the base point of a decomposition quotient

`DoubleCoset.DecompQuotient Γ₁ Γ₂ g` is `Γ₁ ⧸ (gΓ₂g⁻¹).subgroupOf Γ₁`, so it depends on `g`
only through the conjugate `gΓ₂g⁻¹`. The conjugation facts themselves are general subgroup
theory and live in `TauCeti.GroupTheory.DoubleCoset.Basic`
(`conjAct_smul_mul_right_of_mem_normalizer` and the two `subgroupOf_…` lemmas); this file turns
them into equivalences of the quotients:

* moving the base point on the **left** by anything normalizing `Γ₁` conjugates the stabilizer,
  hence gives `Γ₁/Stab(hg) ≃ Γ₁/Stab(g)`;
* moving it on the **right** by anything normalizing `Γ₂` changes the stabilizer not at all, so
  the two-sided move reduces to the left one.

Ported from the AINTLIB [`LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) project,
`LeanModularForms/HeckeRIngs/AbstractHeckeRing/StabConjugation.lean`
(Chris Birkbeck). The source states these for a bundled `HeckePair` and for `g` in the
ambient submonoid `Δ`; neither is used by the arguments, so they are stated here for arbitrary
subgroups, an arbitrary `g : G`, and multipliers taken from the normalizers.

## Main results

* `DoubleCoset.decompQuotientEquivMulLeft`, `DoubleCoset.decompQuotientEquivMulLeftRight`:
  the equivalences of decomposition quotients induced by moving the base point.
* `DoubleCoset.decompQuotientEquivMulLeft_mk`,
  `DoubleCoset.decompQuotientEquivMulLeftRight_mk`: what each does to a representative.
-/

public section

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G]

/-- Moving the base point on the left by anything normalizing `Γ₁` is an equivalence of
decomposition quotients, `Γ₁/Stab(hg) ≃ Γ₁/Stab(g)`, induced by `σ ↦ h⁻¹σh`.

Well-definedness is `subgroupOf_conjAct_smul_mul_left_of_mem_normalizer`: the two stabilizers
differ by that conjugation, so it carries one coset relation to the other. -/
noncomputable def decompQuotientEquivMulLeft (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq
      (subgroupOf_conjAct_smul_mul_left_of_mem_normalizer Γ₁ Γ₂ g h)).trans <|
    Quotient.congr (Γ₁.normalizerMonoidHom h).symm.toEquiv fun a b ↦ by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_map_equiv,
        MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_inv, ← map_mul]

/-- What `decompQuotientEquivMulLeft` does to a representative: it conjugates by `h⁻¹`.

Deliberately *not* `@[simp]`. The left-hand side is not in simp normal form and cannot be
made so: `QuotientGroup.mk`'s implicit subgroup argument comes from the type index
`DecompQuotient Γ₁ Γ₂ (↑h * g)`, and simp rewrites `ConjAct.toConjAct (↑h * g)` inside it to
`ConjAct.toConjAct ↑h * ConjAct.toConjAct g` via `ConjAct.toConjAct_mul`. `scripts/lint-env.sh`
reports exactly that as a `simpNF` violation. Rewrite with this lemma by name. -/
lemma decompQuotientEquivMulLeft_mk (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) (x : Γ₁) :
    decompQuotientEquivMulLeft Γ₁ Γ₂ g h (QuotientGroup.mk x) =
      QuotientGroup.mk ((Γ₁.normalizerMonoidHom h).symm x) :=
  -- `(rfl)` rather than `rfl`: the equivalences are not `@[expose]`, so the parentheses opt
  -- out of exporting the definitional equality that this lemma exists to replace.
  (rfl)

/-- Moving the base point on both sides — on the left by anything normalizing `Γ₁`, on the
right by anything normalizing `Γ₂` — is again an equivalence of decomposition quotients. Right
multiplication contributes nothing (`subgroupOf_conjAct_smul_mul_right_of_mem_normalizer`), so
this is `decompQuotientEquivMulLeft` after re-associating. -/
noncomputable def decompQuotientEquivMulLeftRight (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) {k : G} (hk : k ∈ Subgroup.normalizer Γ₂) :
    DecompQuotient Γ₁ Γ₂ ((h : G) * g * k) ≃ DecompQuotient Γ₁ Γ₂ g :=
  (Subgroup.quotientEquivOfEq (by rw [mul_assoc])).trans
    ((decompQuotientEquivMulLeft Γ₁ Γ₂ (g * k) h).trans
      (Subgroup.quotientEquivOfEq
        (subgroupOf_conjAct_smul_mul_right_of_mem_normalizer Γ₁ Γ₂ g hk)))

/-- What `decompQuotientEquivMulLeftRight` does to a representative. Not `@[simp]`, for the
same reason as `decompQuotientEquivMulLeft_mk`. -/
lemma decompQuotientEquivMulLeftRight_mk (Γ₁ Γ₂ : Subgroup G) (g : G)
    (h : Subgroup.normalizer (Γ₁ : Set G)) {k : G} (hk : k ∈ Subgroup.normalizer Γ₂) (x : Γ₁) :
    decompQuotientEquivMulLeftRight Γ₁ Γ₂ g h hk (QuotientGroup.mk x) =
      QuotientGroup.mk ((Γ₁.normalizerMonoidHom h).symm x) :=
  (rfl)

end DoubleCoset
