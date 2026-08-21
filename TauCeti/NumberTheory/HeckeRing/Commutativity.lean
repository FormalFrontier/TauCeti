/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Associativity
import Mathlib.Tactic.Group

/-!
# Hecke rings: commutativity via an anti-involution

Shimura's commutativity criterion (Proposition 3.8 of [Shimura][shimura1971]): if the monoid
`Δ` admits an anti-involution `ι` preserving `H` and fixing every double coset `HgH` for
`g ∈ Δ`, then Shimura's multiplicity is symmetric, `m(g₁, g₂; d) = m(g₂, g₁; d)`, so the
structure constants of the convolution product are symmetric and the Hecke ring `𝕋 Δ H R` is
commutative for every commutative semiring `R`. Following Shimura, the anti-involution is
data on the submonoid `Δ` alone — it need not extend to the ambient group, and `Δ` contains
no inverses in general — while an anti-involution of the ambient group preserving `H` and `Δ`
restricts to one of the datum via `HeckeAntiInvolution.ofAmbient`. The classical instance is
the transpose on `GL₂(ℚ)`, which fixes the double cosets of `M₂(ℤ)`-integral matrices by the
elementary divisor theorem.

The symmetry of the multiplicity is proved through the one-sided count
`DoubleCoset.multiplicity_eq_card_filter`: the anti-involution induces an injection between
the two count sets by transporting the representative decomposition of `(σᵢ g₁)⁻¹ d` through
`ι` (Shimura's change of variables), and the two opposite injections give equality.

Ported from the AINTLIB `LeanModularForms` project
(`HeckeRIngs/AbstractHeckeRing/Commutativity.lean`,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), per the
ModularForms roadmap's dependency policy, rebuilt on the one-sided multiplicity count of the
vendored Mathlib stack.

## Main definitions

* `HeckeAntiInvolution`: an anti-involution of the Hecke datum `(Δ, H)` — a monoid
  homomorphism `Δ →* Δᵐᵒᵖ`, involutive on `Δ` and preserving `H`.
* `HeckeAntiInvolution.ofAmbient`: restriction of an anti-involution of the ambient group.
* `HeckeAntiInvolution.onHeckeCoset`: the induced action on double cosets.

## Main results

* `HeckeAntiInvolution.multiplicity_comm`: Shimura's multiplicity is symmetric when the
  anti-involution fixes every double coset.
* `HeckeCosetModule.mul_comm_of_antiInvolution`: the convolution product is commutative.
* `HeckeCosetModule.commSemiringOfAntiInvolution`: the resulting `CommSemiring (𝕋 Δ H R)`.
-/

public section

open DoubleCoset Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G}

/-- An anti-involution of the Hecke datum `(Δ, H)`: a monoid homomorphism `Δ →* Δᵐᵒᵖ`
(equivalently, an anti-homomorphism of `Δ`) that is involutive and preserves membership in
`H`. Following Shimura, the data lives on the submonoid `Δ` alone; an anti-involution of the
ambient group restricts via `HeckeAntiInvolution.ofAmbient`. Shimura's commutativity
criterion applies when it moreover fixes every double coset `HgH`, `g ∈ Δ`; see
`HeckeAntiInvolution.multiplicity_comm`. -/
structure HeckeAntiInvolution (Δ : Submonoid G) (H : Subgroup G) where
  /-- The underlying homomorphism to the opposite monoid. -/
  toFun : Δ →* Δᵐᵒᵖ
  /-- The induced map on `Δ` is involutive. -/
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  /-- The induced map preserves membership in `H`. -/
  mem_H : ∀ g : Δ, (g : G) ∈ H → ((toFun g).unop : G) ∈ H

namespace HeckeAntiInvolution

@[ext]
lemma ext {ι₁ ι₂ : HeckeAntiInvolution Δ H} (h : ι₁.toFun = ι₂.toFun) : ι₁ = ι₂ := by
  cases ι₁; cases ι₂; subst h; rfl

variable (ι : HeckeAntiInvolution Δ H)

/-- The underlying function of the anti-involution, as a map on elements of `G` lying in
`Δ`. The membership witness is explicit; it is proof-irrelevant, so rewriting is unaffected
by which witness appears. -/
def bar (x : G) (hx : x ∈ Δ) : G := ((ι.toFun ⟨x, hx⟩).unop : G)

/-- The anti-involution maps `Δ` into itself. -/
lemma bar_mem_Δ (x : G) (hx : x ∈ Δ) : ι.bar x hx ∈ Δ := ((ι.toFun ⟨x, hx⟩).unop).2

/-- `bar` does not depend on the membership witness; equal elements have equal images. -/
lemma bar_congr {x y : G} (e : x = y) (hx : x ∈ Δ) (hy : y ∈ Δ) :
    ι.bar x hx = ι.bar y hy := by subst e; rfl

/-- The anti-involution is an involution. -/
@[simp] lemma bar_bar {x : G} (hx : x ∈ Δ) (hbx : ι.bar x hx ∈ Δ) :
    ι.bar (ι.bar x hx) hbx = x :=
  congrArg Subtype.val (ι.involutive ⟨x, hx⟩)

/-- The anti-involution reverses multiplication. The memberships of the factors are
explicit so that `rw [ι.bar_mul hx hy]` determines the factors. -/
lemma bar_mul {x y : G} (hx : x ∈ Δ) (hy : y ∈ Δ) (hxy : x * y ∈ Δ) :
    ι.bar (x * y) hxy = ι.bar y hy * ι.bar x hx := by
  simpa [bar, MulMemClass.mk_mul_mk] using
    congrArg (fun u : Δᵐᵒᵖ ↦ ((u.unop : Δ) : G)) (map_mul ι.toFun ⟨x, hx⟩ ⟨y, hy⟩)

/-- The anti-involution fixes the identity. -/
@[simp] lemma bar_one (h : (1 : G) ∈ Δ) : ι.bar 1 h = 1 :=
  congrArg Subtype.val (congrArg MulOpposite.unop (map_one ι.toFun))

/-- The anti-involution preserves membership in `H`. -/
lemma bar_mem_H {x : G} (hx : x ∈ Δ) (h : x ∈ H) : ι.bar x hx ∈ H := ι.mem_H ⟨x, hx⟩ h

/-- Membership in `H` is preserved in both directions by the anti-involution. -/
@[simp] lemma bar_mem_H_iff {x : G} (hx : x ∈ Δ) : ι.bar x hx ∈ H ↔ x ∈ H := by
  refine ⟨fun h ↦ ?_, ι.bar_mem_H hx⟩
  have h2 := ι.bar_mem_H (ι.bar_mem_Δ x hx) h
  rwa [ι.bar_bar] at h2

/-- An anti-involution of the ambient group `G` preserving `H` and `Δ` restricts to an
anti-involution of the Hecke datum `(Δ, H)`. The classical instance is the transpose on
`GL₂(ℚ)` restricted to the integral matrices. -/
def ofAmbient (f : G →* Gᵐᵒᵖ) (hinv : ∀ g, (f (f g).unop).unop = g)
    (hH : ∀ g ∈ H, (f g).unop ∈ H) (hΔ : ∀ g ∈ Δ, (f g).unop ∈ Δ) :
    HeckeAntiInvolution Δ H where
  toFun :=
    { toFun g := MulOpposite.op ⟨(f g).unop, hΔ g g.2⟩
      map_one' := by
        apply MulOpposite.unop_injective
        exact Subtype.ext (by simp)
      map_mul' a b := by
        apply MulOpposite.unop_injective
        exact Subtype.ext (by simp) }
  involutive g := Subtype.ext (hinv g)
  mem_H g hg := hH g hg

@[simp] lemma ofAmbient_bar (f : G →* Gᵐᵒᵖ) (hinv : ∀ g, (f (f g).unop).unop = g)
    (hH : ∀ g ∈ H, (f g).unop ∈ H) (hΔ : ∀ g ∈ Δ, (f g).unop ∈ Δ) (x : G) (hx : x ∈ Δ) :
    (ofAmbient f hinv hH hΔ).bar x hx = (f x).unop := (rfl)

/-- The anti-involution maps the double coset of `a` into the double coset of `bar a`. -/
lemma bar_mem_doubleCoset [IsHeckeTriple Δ H H] {a x : G} (ha : a ∈ Δ) (hx : x ∈ Δ)
    (hmem : x ∈ doubleCoset a (H : Set G) H) :
    ι.bar x hx ∈ doubleCoset (ι.bar a ha) (H : Set G) H := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := mem_doubleCoset.mp hmem
  have hh₁Δ : h₁ ∈ Δ := IsHeckeTriple.mem_of_mem_left (Δ := Δ) H hh₁
  have hh₂Δ : h₂ ∈ Δ := IsHeckeTriple.mem_of_mem_left (Δ := Δ) H hh₂
  refine mem_doubleCoset.mpr ⟨ι.bar h₂ hh₂Δ, ι.bar_mem_H hh₂Δ hh₂, ι.bar h₁ hh₁Δ,
    ι.bar_mem_H hh₁Δ hh₁, ?_⟩
  rw [ι.bar_mul (mul_mem hh₁Δ ha) hh₂Δ, ι.bar_mul hh₁Δ ha, mul_assoc]

/-- The induced action of the anti-involution on the double cosets `H\Δ/H`. -/
noncomputable def onHeckeCoset (D : HeckeCoset Δ H H) : HeckeCoset Δ H H :=
  HeckeCoset.mk H H ⟨ι.bar (D.rep : G) D.rep.2, ι.bar_mem_Δ _ _⟩

/-- `onHeckeCoset` sends the class of `g` to the class of `bar g`. -/
@[simp] lemma onHeckeCoset_mk [IsHeckeTriple Δ H H] (g : Δ) :
    ι.onHeckeCoset (HeckeCoset.mk H H g) =
      HeckeCoset.mk H H ⟨ι.bar (g : G) g.2, ι.bar_mem_Δ _ _⟩ := by
  refine HeckeCoset.eq_iff.mpr ?_
  have hrep : ((HeckeCoset.mk H H g).rep : G) ∈ doubleCoset (g : G) (H : Set G) H := by
    have h := HeckeCoset.rep_mem (HeckeCoset.mk H H g)
    rwa [HeckeCoset.toSet_mk] at h
  exact doubleCoset_eq_of_mem (ι.bar_mem_doubleCoset g.2 _ hrep)

/-- The induced action on double cosets is an involution. -/
@[simp] lemma onHeckeCoset_onHeckeCoset [IsHeckeTriple Δ H H] (D : HeckeCoset Δ H H) :
    ι.onHeckeCoset (ι.onHeckeCoset D) = D := by
  induction D using HeckeCoset.induction with
  | h g =>
    rw [ι.onHeckeCoset_mk, ι.onHeckeCoset_mk]
    exact congrArg (HeckeCoset.mk H H) (Subtype.ext (ι.bar_bar g.2 _))

/-- When the anti-involution fixes every double coset, `bar g` lies in the double coset of
`g` for every `g ∈ Δ`. -/
lemma bar_mem_doubleCoset_self [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g : Δ) :
    ι.bar (g : G) g.2 ∈ doubleCoset (g : G) (H : Set G) H := by
  have hg := congrArg HeckeCoset.toSet ((ι.onHeckeCoset_mk g).symm.trans (h_fix _))
  rw [HeckeCoset.toSet_mk, HeckeCoset.toSet_mk] at hg
  exact hg ▸ mem_doubleCoset_self H H _

/-- Decompose `bar x` through the double coset of `g` when `x ∈ HgH`. -/
private lemma exists_bar_eq [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) {g : Δ} {x : G}
    (hx : x ∈ doubleCoset (g : G) (H : Set G) H) :
    ∃ a ∈ H, ∃ b ∈ H,
      ι.bar x (IsHeckeTriple.mem_of_mem_doubleCoset g.2 hx) = a * (g : G) * b := by
  have hbar := ι.bar_mem_doubleCoset g.2 (IsHeckeTriple.mem_of_mem_doubleCoset g.2 hx) hx
  rw [doubleCoset_eq_of_mem (ι.bar_mem_doubleCoset_self h_fix g)] at hbar
  exact mem_doubleCoset.mp hbar

/-- Membership in the one-sided count set is invariant under replacing a representative of
a class in `DecompQuotient H H g₂` by the canonical `out`. -/
private lemma out_mul_inv_mul_mem {g₁ g₂ d : G} {u : G} (hu : u ∈ H)
    (hmem : (u * g₂)⁻¹ * d ∈ doubleCoset g₁ (H : Set G) H) :
    ((((QuotientGroup.mk ⟨u, hu⟩ : DecompQuotient H H g₂).out : G)) * g₂)⁻¹ * d ∈
      doubleCoset g₁ (H : Set G) H := by
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g₂ • H).subgroupOf H) (⟨u, hu⟩ : H)
  have hout : (((QuotientGroup.mk ⟨u, hu⟩ : DecompQuotient H H g₂).out : G)) = u * n := by
    simpa [Subgroup.coe_mul] using congrArg (Subtype.val : H → G) hn
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := mem_doubleCoset.mp hmem
  refine mem_doubleCoset.mpr ⟨g₂⁻¹ * (n : G)⁻¹ * g₂ * h₁,
    H.mul_mem (by simpa [mul_assoc] using H.inv_mem (conj_mem_of_stabilizer g₂ n)) hh₁,
    h₂, hh₂, ?_⟩
  rw [hout]
  calc (u * n * g₂)⁻¹ * d
      = (g₂⁻¹ * (n : G)⁻¹ * g₂) * ((u * g₂)⁻¹ * d) := by group
    _ = (g₂⁻¹ * (n : G)⁻¹ * g₂) * (h₁ * g₁ * h₂) := by rw [heq]
    _ = g₂⁻¹ * (n : G)⁻¹ * g₂ * h₁ * g₁ * h₂ := by group

open Classical in
/-- Shimura's change of variables: the anti-involution transports a member of the one-sided
count set of `m(g₁, g₂; d)` to a member of the one-sided count set of `m(g₂, g₁; d)`. -/
private noncomputable def commFwdMap [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    (g₁ g₂ d : Δ) {aD bD : G} (haD : aD ∈ H) (hbD : bD ∈ H)
    (hbarD : ι.bar (d : G) d.2 = aD * (d : G) * bD)
    {a₁ b₁ : G} (ha₁ : a₁ ∈ H) (hb₁ : b₁ ∈ H)
    (hbar₁ : ι.bar (g₁ : G) g₁.2 = a₁ * (g₁ : G) * b₁)
    (p : {i : DecompQuotient H H (g₁ : G) |
      ((i.out : G) * g₁)⁻¹ * (d : G) ∈ doubleCoset (g₂ : G) (H : Set G) H}) :
    {j : DecompQuotient H H (g₂ : G) |
      ((j.out : G) * g₂)⁻¹ * (d : G) ∈ doubleCoset (g₁ : G) (H : Set G) H} :=
  have hx : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p.1.out : G) * g₁)⁻¹ * (d : G))
        (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p.2) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p.2
  ⟨QuotientGroup.mk ⟨aD⁻¹ * hx.choose, H.mul_mem (H.inv_mem haD) hx.choose_spec.1⟩,
    out_mul_inv_mul_mem _ (by
      -- the raw membership `(aD⁻¹ * a * g₂)⁻¹ * d ∈ H g₁ H` for the chosen decomposition
      -- `bar((σᵢ g₁)⁻¹ d) = a g₂ b`, before passing to the canonical representative
      obtain ⟨hb, hbar⟩ := hx.choose_spec.2.choose_spec
      set a := hx.choose
      set b := hx.choose_spec.2.choose
      have houtΔ : ((p.1.out : H) : G) ∈ Δ :=
        IsHeckeTriple.mem_of_mem_left (Δ := Δ) H (p.1.out : H).2
      have hxΔ : ((p.1.out : G) * g₁)⁻¹ * (d : G) ∈ Δ :=
        IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p.2
      have houtg₁Δ : (p.1.out : G) * (g₁ : G) ∈ Δ := mul_mem houtΔ g₁.2
      have hd : (d : G) = (p.1.out : G) * (g₁ : G) * (((p.1.out : G) * g₁)⁻¹ * (d : G)) := by
        group
      have h2 : ι.bar (d : G) d.2 =
          ι.bar (((p.1.out : G) * g₁)⁻¹ * (d : G)) hxΔ *
            (ι.bar (g₁ : G) g₁.2 * ι.bar (p.1.out : G) houtΔ) := by
        rw [ι.bar_congr hd d.2 (mul_mem houtg₁Δ hxΔ), ι.bar_mul houtg₁Δ hxΔ,
          ι.bar_mul houtΔ g₁.2]
      have hkey : aD * (d : G) * bD =
          a * (g₂ : G) * b * (a₁ * (g₁ : G) * b₁) * ι.bar (p.1.out : G) houtΔ := by
        rw [← hbarD, ← hbar, ← hbar₁, h2]
        group
      refine mem_doubleCoset.mpr ⟨b * a₁, H.mul_mem hb ha₁,
        b₁ * ι.bar (p.1.out : G) houtΔ * bD⁻¹,
        H.mul_mem (H.mul_mem hb₁ (ι.bar_mem_H houtΔ (p.1.out : H).2)) (H.inv_mem hbD), ?_⟩
      have hADd : aD * (d : G) =
          a * (g₂ : G) *
            (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) houtΔ * bD⁻¹)) := by
        calc aD * (d : G) = aD * (d : G) * bD * bD⁻¹ := by group
          _ = a * (g₂ : G) * b * (a₁ * (g₁ : G) * b₁) * ι.bar (p.1.out : G) houtΔ * bD⁻¹ := by
            rw [hkey]
          _ = a * (g₂ : G) *
              (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) houtΔ * bD⁻¹)) := by
            group
      calc (aD⁻¹ * a * (g₂ : G))⁻¹ * (d : G)
          = ((g₂ : G))⁻¹ * a⁻¹ * (aD * (d : G)) := by group
        _ = ((g₂ : G))⁻¹ * a⁻¹ *
              (a * (g₂ : G) *
                (b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) houtΔ * bD⁻¹))) := by
            rw [hADd]
        _ = b * a₁ * (g₁ : G) * (b₁ * ι.bar (p.1.out : G) houtΔ * bD⁻¹) := by group)⟩

/-- Transport back through the anti-involution: two elements of `Δ` whose barred
decompositions share the middle `g₂` with stabilizer-related left parts differ by an element
of `H`. The proof expands the involution through the two decompositions, staying inside `Δ`
throughout — `bar` is never applied to an inverse. -/
private lemma bar_diff_mem [IsHeckeTriple Δ H H] {x₁ x₂ : G} (hx₁ : x₁ ∈ Δ) (hx₂ : x₂ ∈ Δ)
    {g₂ : Δ} {a₁' b₁' a₂' b₂' : G} (ha₁' : a₁' ∈ H) (hb₁' : b₁' ∈ H) (hb₂' : b₂' ∈ H)
    (hbar₁' : ι.bar x₁ hx₁ = a₁' * (g₂ : G) * b₁')
    (hbar₂' : ι.bar x₂ hx₂ = a₂' * (g₂ : G) * b₂')
    (hconj : (g₂ : G)⁻¹ * (a₁'⁻¹ * a₂') * g₂ ∈ H) : x₂ * x₁⁻¹ ∈ H := by
  set m : G := (g₂ : G)⁻¹ * (a₁'⁻¹ * a₂') * g₂ with hm
  -- rewrite the second decomposition through the stabilizer relation to share `a₁'`
  have hx₂eq : ι.bar x₂ hx₂ = a₁' * (g₂ : G) * (m * b₂') := by rw [hbar₂', hm]; group
  have ha₁'Δ : a₁' ∈ Δ := IsHeckeTriple.mem_of_mem_left (Δ := Δ) H ha₁'
  have hb₁'Δ : b₁' ∈ Δ := IsHeckeTriple.mem_of_mem_left (Δ := Δ) H hb₁'
  have hmb₂'Δ : m * b₂' ∈ Δ := mul_mem (IsHeckeTriple.mem_of_mem_left (Δ := Δ) H hconj)
    (IsHeckeTriple.mem_of_mem_left (Δ := Δ) H hb₂')
  have ha₁g₂Δ : a₁' * (g₂ : G) ∈ Δ := mul_mem ha₁'Δ g₂.2
  -- expand the involution through the two decompositions
  have hx₁' : x₁ = ι.bar b₁' hb₁'Δ * (ι.bar (g₂ : G) g₂.2 * ι.bar a₁' ha₁'Δ) := by
    have h := (ι.bar_bar hx₁ (ι.bar_mem_Δ x₁ hx₁)).symm
    rw [ι.bar_congr hbar₁' (ι.bar_mem_Δ x₁ hx₁) (mul_mem ha₁g₂Δ hb₁'Δ),
      ι.bar_mul ha₁g₂Δ hb₁'Δ, ι.bar_mul ha₁'Δ g₂.2] at h
    exact h
  have hx₂' : x₂ = ι.bar (m * b₂') hmb₂'Δ * (ι.bar (g₂ : G) g₂.2 * ι.bar a₁' ha₁'Δ) := by
    have h := (ι.bar_bar hx₂ (ι.bar_mem_Δ x₂ hx₂)).symm
    rw [ι.bar_congr hx₂eq (ι.bar_mem_Δ x₂ hx₂) (mul_mem ha₁g₂Δ hmb₂'Δ),
      ι.bar_mul ha₁g₂Δ hmb₂'Δ, ι.bar_mul ha₁'Δ g₂.2] at h
    exact h
  -- the common right factor cancels
  have hcalc : x₂ * x₁⁻¹ = ι.bar (m * b₂') hmb₂'Δ * (ι.bar b₁' hb₁'Δ)⁻¹ := by
    rw [hx₁', hx₂']; group
  rw [hcalc]
  exact H.mul_mem (ι.bar_mem_H hmb₂'Δ (H.mul_mem hconj hb₂'))
    (H.inv_mem (ι.bar_mem_H hb₁'Δ hb₁'))

/-- The transported class determines the original: two members of the count set with barred
decompositions sharing the middle `g₂` and stabilizer-related left parts differ by `H` on
the left of `g₁`. -/
private lemma commFwdMap_injective [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D)
    (g₁ g₂ d : Δ) {aD bD : G} (haD : aD ∈ H) (hbD : bD ∈ H)
    (hbarD : ι.bar (d : G) d.2 = aD * (d : G) * bD)
    {a₁ b₁ : G} (ha₁ : a₁ ∈ H) (hb₁ : b₁ ∈ H)
    (hbar₁ : ι.bar (g₁ : G) g₁.2 = a₁ * (g₁ : G) * b₁) :
    Function.Injective (ι.commFwdMap h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁) := by
  intro p₁ p₂ heq
  have hx₁ : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p₁.1.out : G) * g₁)⁻¹ * (d : G))
        (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p₁.2) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p₁.2
  have hx₂ : ∃ a ∈ H, ∃ b ∈ H,
      ι.bar (((p₂.1.out : G) * g₁)⁻¹ * (d : G))
        (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p₂.2) = a * (g₂ : G) * b :=
    ι.exists_bar_eq h_fix p₂.2
  have hmk : (QuotientGroup.mk ⟨aD⁻¹ * hx₁.choose,
        H.mul_mem (H.inv_mem haD) hx₁.choose_spec.1⟩ : DecompQuotient H H (g₂ : G)) =
      QuotientGroup.mk ⟨aD⁻¹ * hx₂.choose,
        H.mul_mem (H.inv_mem haD) hx₂.choose_spec.1⟩ :=
    congrArg Subtype.val heq
  have hconj := conj_mem_of_mk_eq (g₂ : G) hmk
  -- the conjugation relation transfers to the chosen left parts, since `aD` cancels
  have hconj' : ((g₂ : G))⁻¹ * (hx₁.choose⁻¹ * hx₂.choose) * g₂ ∈ H := by
    simpa [mul_assoc] using hconj
  -- transport back through the anti-involution: the two count-set elements differ by `H`
  have hdiff : (((p₂.1.out : G) * g₁)⁻¹ * (d : G)) *
      ((((p₁.1.out : G) * g₁)⁻¹ * (d : G)))⁻¹ ∈ H :=
    ι.bar_diff_mem (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p₁.2)
      (IsHeckeTriple.mem_of_mem_doubleCoset g₂.2 p₂.2)
      hx₁.choose_spec.1 hx₁.choose_spec.2.choose_spec.1 hx₂.choose_spec.2.choose_spec.1
      hx₁.choose_spec.2.choose_spec.2 hx₂.choose_spec.2.choose_spec.2 hconj'
  -- conclude equality in the decomposition quotient through the coset injectivity
  have hcoset : (((p₂.1.out : G) * g₁ : G) : G ⧸ H) = (((p₁.1.out : G) * g₁ : G) : G ⧸ H) := by
    rw [QuotientGroup.eq]
    have : (((p₂.1.out : G) * g₁)⁻¹ * (d : G)) *
        ((((p₁.1.out : G) * g₁)⁻¹ * (d : G)))⁻¹ =
        ((p₂.1.out : G) * g₁)⁻¹ * ((p₁.1.out : G) * g₁) := by group
    exact this ▸ hdiff
  exact Subtype.ext (mk_out_mul_injective H H (g₁ : G) hcoset.symm)

/-- One direction of the symmetry of Shimura's multiplicity under an anti-involution fixing
every double coset. -/
private lemma multiplicity_le_comm [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ d : Δ) :
    multiplicity H H H (g₁ : G) (g₂ : G) (d : G) ≤
      multiplicity H H H (g₂ : G) (g₁ : G) (d : G) := by
  classical
  obtain ⟨aD, haD, bD, hbD, hbarD⟩ :=
    ι.exists_bar_eq h_fix (mem_doubleCoset_self H H (d : G))
  obtain ⟨a₁, ha₁, b₁, hb₁, hbar₁⟩ :=
    ι.exists_bar_eq h_fix (mem_doubleCoset_self H H (g₁ : G))
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter]
  exact Nat.card_le_card_of_injective
    (ι.commFwdMap h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁)
    (ι.commFwdMap_injective h_fix g₁ g₂ d haD hbD hbarD ha₁ hb₁ hbar₁)

/-- **Shimura's multiplicity is symmetric under an anti-involution** (Proposition 3.8 of
[Shimura][shimura1971]): when the anti-involution fixes every double coset,
`m(g₁, g₂; d) = m(g₂, g₁; d)`. -/
theorem multiplicity_comm [IsHeckeTriple Δ H H]
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ d : Δ) :
    multiplicity H H H (g₁ : G) (g₂ : G) (d : G) =
      multiplicity H H H (g₂ : G) (g₁ : G) (d : G) :=
  le_antisymm (ι.multiplicity_le_comm h_fix g₁ g₂ d) (ι.multiplicity_le_comm h_fix g₂ g₁ d)

end HeckeAntiInvolution

namespace HeckeCosetModule

open HeckeAntiInvolution

variable (R : Type*) {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]

/-- The structure constants of the Hecke ring are symmetric under an anti-involution fixing
every double coset. -/
lemma structureConstants_comm [Semiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (g₁ g₂ : Δ) :
    structureConstants R H H H g₁ g₂ = structureConstants R H H H g₂ g₁ := by
  classical
  ext D
  rw [structureConstants_apply, structureConstants_apply,
    ι.multiplicity_comm h_fix g₁ g₂ D.rep]

/-- **Shimura's commutativity criterion** (Proposition 3.8 of [Shimura][shimura1971]): the
Hecke ring over a commutative semiring is commutative when an anti-involution fixes every
double coset. -/
theorem mul_comm_of_antiInvolution [CommSemiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) (f g : 𝕋 Δ H R) :
    f * g = g * f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => rw [mul_def, mul_def, HeckeCosetModule.zero_mul, HeckeCosetModule.mul_zero]
  | hadd f₁ f₂ h₁ h₂ => rw [_root_.add_mul, _root_.mul_add, h₁, h₂]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => rw [mul_def, mul_def, HeckeCosetModule.zero_mul, HeckeCosetModule.mul_zero]
    | hadd g₁ g₂ h₁ h₂ => rw [_root_.mul_add, _root_.add_mul, h₁, h₂]
    | hsingle D₂ b =>
      rw [single_mul_single, single_mul_single,
        structureConstants_comm R ι h_fix D₂.rep D₁.rep, smul_comm]

/-- The Hecke ring over a commutative semiring is a commutative semiring when an
anti-involution fixes every double coset (Proposition 3.8 of [Shimura][shimura1971]). Not an
instance: the anti-involution is data supplied per application (for `GL₂` it is the
transpose). -/
@[instance_reducible]
noncomputable def commSemiringOfAntiInvolution [CommSemiring R] (ι : HeckeAntiInvolution Δ H)
    (h_fix : ∀ D : HeckeCoset Δ H H, ι.onHeckeCoset D = D) : CommSemiring (𝕋 Δ H R) :=
  { instSemiringHeckeRing R with
    mul_comm := mul_comm_of_antiInvolution R ι h_fix }

end HeckeCosetModule
