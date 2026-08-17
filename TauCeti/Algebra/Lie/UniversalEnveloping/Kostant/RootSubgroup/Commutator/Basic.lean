/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic
public import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
public import TauCeti.RingTheory.Nilpotent.RootString.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Chevalley commutator relations for Kostant root subgroups

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ`, let `M ≤ V` be a
`U_ℤ`-stable additive subgroup, and let `eᵢ`, `eⱼ`, `eₖ` be distinguished root vectors with
nilpotent images. If

```text
⁅eᵢ, eⱼ⁆ = c • eₖ,   ⁅eᵢ, eₖ⁆ = 0,   ⁅eⱼ, eₖ⁆ = 0
```

for an integer `c` — the situation of two roots `α`, `β` with `α + β` a root but neither
`2α + β` nor `α + 2β` a root, `c` being the Chevalley structure constant `N_{α β}` — then the
root subgroups on the points of `M ⊗ A` satisfy the Chevalley commutator relation

```text
x_α(t) x_β(u) x_α(t)⁻¹ = x_β(u) x_{α+β}(c t u).
```

This is the case of the Chevalley commutator formula in which only one further root subgroup
occurs; in a simply-laced root system every pair of non-proportional roots falls under it or under
the commuting case. The relation holds over every commutative ring `A`, with no factorial
inverted, because it descends from the coefficient-one normal-ordering rule for divided powers.

The multiply-laced types `B`, `C`, and `F₄` also produce pairs `α`, `β` for which `2α + β`
is a root. There the second bracket no longer vanishes: instead

```text
⁅eᵢ, eⱼ⁆ = c • eₖ,   ⁅eᵢ, ⁅eᵢ, eⱼ⁆⁆ = (2 * d) • e_l,   ⁅eᵢ, e_l⁆ = ⁅eⱼ, eₖ⁆ = ⁅eₖ, e_l⁆ = 0,
```

the factor `2` being what makes `(ad eᵢ)² eⱼ / 2` integral, and the relation acquires one more
factor:

```text
x_α(t) x_β(u) x_α(t)⁻¹ = x_β(u) x_{α+β}(c t u) x_{2α+β}(d t² u).
```

Type `G₂` additionally needs the longer chain with factors at `3α + β` and `3α + 2β`; its
transport to Kostant root subgroups is in
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2`.

The general statements about integral nilpotent exponentials are
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq` and
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul`; this file only supplies the
Lie-theoretic hypotheses and transports the identities to the root subgroups in
`LinearMap.GeneralLinearGroup`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupPoints`: root subgroups of
  commuting root vectors commute.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_eq`: the Chevalley
  commutator relation, for any `𝔾ₐ`-point carrying the parameter `c * t * u`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_eq'`: the same relation
  with that point written out.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_eq`: its conjugation
  form.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_eq'`: the conjugation
  form with that point written out.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupPoints_of_lie_eq`:
  the element-commutator form.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupPoints_of_lie_eq'`:
  the element-commutator form with the third point written out.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_lie_eq`: the Chevalley
  commutator relation for the chain `β`, `α + β`, `2α + β`, for `𝔾ₐ`-points carrying the parameters
  `c * t * u` and `d * t² * u`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_lie_eq'`: the same
  relation with those points written out.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_lie_eq`: its
  conjugation form.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_lie_lie_eq'`: the
  conjugation form with those points written out.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-- A Kostant-stable lattice is stable under the divided powers of every integral multiple of a
distinguished root vector. -/
theorem dividedPower_zsmul_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (c : ℤ) (k : ι) : ∀ n, ∀ v ∈ M,
    Associative.dividedPower n (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) • v ∈ M := by
  intro n v hv
  rw [Associative.dividedPower_zsmul, smul_assoc]
  exact M.zsmul_mem (dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) _

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- **The degenerate Chevalley commutator relation for Kostant root subgroups.** Root subgroups
attached to commuting root vectors commute. For a root system this is the case of two roots whose
sum is not a root and which are not opposite. -/
theorem commute_kostantRootSubgroupPoints {i j : ι} (hij : ⁅e i, e j⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Commute (kostantRootSubgroupPoints e h ρ M hM i hi f)
      (kostantRootSubgroupPoints e h ρ M hM j hj g) := by
  have hcomm := commute_of_lie_eq_zero ρ hij
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  exact commute_baseChangeExp M hcomm hi hj _ _ _ _

/-- **The Chevalley commutator relation for Kostant root subgroups.** Suppose the distinguished
root vectors satisfy `⁅eᵢ, eⱼ⁆ = c • eₖ` with `eₖ` central for both, and let `w` be any
`𝔾ₐ`-point whose parameter is `c` times the product of the parameters of `f` and `g`. Then

```text
xᵢ(f) xⱼ(g) = xⱼ(g) xₖ(w) xᵢ(f).
```

The hypotheses are exactly the class-two case of the Chevalley commutator formula: `α + β` is a
root, while `2α + β` and `α + 2β` are not. -/
theorem kostantRootSubgroupPoints_mul_of_lie_eq {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g w : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hw : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) w) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk w *
        kostantRootSubgroupPoints e h ρ M hM i hi f := by
  -- The commutator of the first two root vectors is `c` times the third.
  have hxy := mul_eq_mul_add_zsmul_of_lie_eq ρ hij
  -- The third root vector commutes with the other two.
  have hcxz := commute_of_lie_eq_zero ρ hik
  have hcyz := commute_of_lie_eq_zero ρ hjk
  -- Stability of `M` under the divided powers of the scaled commutator.
  have hMz := dividedPower_zsmul_apply_mem e h ρ M hM c k
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  rw [hw, ← baseChangeExp_zsmul c M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) hMz hk]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy (Commute.smul_right hcxz c)
    (Commute.smul_right hcyz c) hi hj _ _ hMz _ _

/-- The Chevalley commutator relation with the third `𝔾ₐ`-point written out: it is the point whose
parameter is `c` times the product of the parameters of `f` and `g`. -/
theorem kostantRootSubgroupPoints_mul_of_lie_eq' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM i hi f :=
  kostantRootSubgroupPoints_mul_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g _
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- The conjugation form of the Chevalley commutator relation: conjugating the root subgroup of
`eⱼ` by the root subgroup of `eᵢ` multiplies it by the root subgroup of `eₖ`, at the parameter
`c * t * u`. -/
theorem kostantRootSubgroupPoints_conj_of_lie_eq {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g w : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hw : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) w) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk w := by
  rw [kostantRootSubgroupPoints_mul_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g w hw,
    mul_inv_cancel_right]

/-- The conjugation form of the Chevalley commutator relation with the third `𝔾ₐ`-point written
out: it is the point whose parameter is `c` times the product of the parameters of `f` and `g`. -/
theorem kostantRootSubgroupPoints_conj_of_lie_eq' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) :=
  kostantRootSubgroupPoints_conj_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g _
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **The canonical class-two Chevalley commutator relation for Kostant root-subgroup
actions.** Suppose `⁅eᵢ, eⱼ⁆ = c • eₖ`, with `eₖ` commuting with `eᵢ` and `eⱼ`, and let `z`
have additive parameter `c` times the product of the parameters of `f` and `g`. Then
`⁅xᵢ(f), xⱼ(g)⁆ = xₖ(z)`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g z : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hz : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) z) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk z := by
  rw [commutatorElement_def,
    kostantRootSubgroupPoints_conj_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g z hz]
  rw [(commute_kostantRootSubgroupPoints e h ρ M hM hjk hj hk g z).eq]
  simp

/-- The canonical class-two Chevalley commutator relation with the third `𝔾ₐ`-point written
out at parameter `c` times the product of the parameters of `f` and `g`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq' {i j k : ι} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
          (Multiplicative.ofAdd ((c : A) *
            (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) :=
  commutatorElement_kostantRootSubgroupPoints_of_lie_eq
    e h ρ M hM hij hik hjk hi hj hk f g _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **The Chevalley commutator relation for Kostant root subgroups along the chain
`β`, `α + β`, `2α + β`.** Suppose the distinguished root vectors satisfy

```text
⁅eᵢ, eⱼ⁆ = c • eₖ,   ⁅eᵢ, ⁅eᵢ, eⱼ⁆⁆ = (2 * d) • e_l,
```

with `⁅eᵢ, e_l⁆ = ⁅eⱼ, eₖ⁆ = ⁅eₖ, e_l⁆ = 0`, and let `p`, `q` be `𝔾ₐ`-points whose parameters are
`c t u` and `d t² u`, where `t` and `u` are the parameters of `f` and `g`. Then

```text
xᵢ(f) xⱼ(g) = xⱼ(g) xₖ(p) x_l(q) xᵢ(f).
```

These hypotheses are the case of the Chevalley commutator formula in which the roots
`i α + j β` with `i, j > 0` are exactly `α + β` and `2 α + β`; the factor `2` in the second bracket
records that the integral element of the Kostant form is `(ad eᵢ)² eⱼ / 2`. -/
theorem kostantRootSubgroupPoints_mul_of_lie_lie_eq {i j k l : ι} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g p q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM i hi f := by
  -- The commutator of the first two root vectors is `c` times the third.
  have hxy := mul_eq_mul_add_zsmul_of_lie_eq ρ hij
  -- The second bracket is twice the fourth root vector, scaled by `d`.
  have hik := hiij
  rw [hij, lie_zsmul] at hik
  have hxz : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) *
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) =
      c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) +
        2 • (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))) := by
    simpa only [one_zsmul, one_mul] using
      (zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := 1) (q := c) (r := d) (n := 2) (by simpa using hik))
  -- The remaining brackets vanish.
  have hcxw := commute_of_lie_eq_zero ρ hil
  have hcyz := commute_of_lie_eq_zero ρ hjk
  have hczw := commute_of_lie_eq_zero ρ hkl
  -- Stability of `M` under the divided powers of the two scaled root vectors.
  have hMz := dividedPower_zsmul_apply_mem e h ρ M hM c k
  have hMw := dividedPower_zsmul_apply_mem e h ρ M hM d l
  have hz := hk.smul c
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  rw [hp, hq, ← baseChangeExp_zsmul c M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) hMz hk,
    ← baseChangeExp_zsmul d M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM l n hv) hMw hl]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M hxy hxz
    (Commute.smul_right hcxw d) (Commute.smul_right hcyz c)
    ((hczw.smul_left c).smul_right d) hi hj hz _ _ hMz hMw _ _

/-- The Chevalley commutator relation for the chain `β`, `α + β`, `2α + β`, with the two extra
`𝔾ₐ`-points written out: their parameters are `c t u` and `d t² u`. -/
theorem kostantRootSubgroupPoints_mul_of_lie_lie_eq' {i j k l : ι} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM i hi f :=
  kostantRootSubgroupPoints_mul_of_lie_lie_eq e h ρ M hM hij hiij hil hjk hkl hi hj hk hl f g _ _
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- The conjugation form of the Chevalley commutator relation for the chain
`β`, `α + β`, `2α + β`:
conjugating the root subgroup of `eⱼ` by that of `eᵢ` multiplies it by the root subgroups of `eₖ`
and of `e_l`, at the parameters `c t u` and `d t² u`. -/
theorem kostantRootSubgroupPoints_conj_of_lie_lie_eq {i j k l : ι} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g p q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q := by
  rw [kostantRootSubgroupPoints_mul_of_lie_lie_eq e h ρ M hM hij hiij hil hjk hkl hi hj hk hl
    f g p q hp hq, mul_inv_cancel_right]

/-- The conjugation form of the Chevalley commutator relation for the chain
`β`, `α + β`, `2α + β`,
with the two extra `𝔾ₐ`-points written out. -/
theorem kostantRootSubgroupPoints_conj_of_lie_lie_eq' {i j k l : ι} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) :=
  kostantRootSubgroupPoints_conj_of_lie_lie_eq e h ρ M hM hij hiij hil hjk hkl hi hj hk hl f g _ _
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
    (congrArg Multiplicative.toAdd
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
