/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic
public import TauCeti.RingTheory.Nilpotent.RootString.G2

/-!
# The type-G₂ commutator relation for Kostant root subgroups

This file transports the integral type-`G₂` exponential identity to the Kostant root subgroups
attached to an admissible lattice. Suppose six distinguished root vectors follow the positive
root string

```text
α, β, α + β, 2α + β, 3α + β, 3α + 2β.
```

Write `c`, `d`, `a`, and `b` for the integral coefficients of the last four vectors in the
successive divided brackets. The hypotheses below say directly that these scaled brackets have
the normalizations required by the integral straightening rule:

```text
[eα, eβ]       = c e_{α+β},
c [eα,e_{α+β}] = 2d e_{2α+β},
d [eα,e_{2α+β}] = 3a e_{3α+β},
dc [e_{2α+β},e_{α+β}] = 3b e_{3α+2β}.
```

The resulting relation is

```text
xα(t) xβ(u) = xβ(u) x_{α+β}(c t u) x_{2α+β}(d t² u)
  x_{3α+β}(a t³ u) x_{3α+2β}(b t³ u²) xα(t).
```

No factorial is inverted in the value ring. Thus the formula is valid in characteristics two and
three as well as in characteristic zero. Together with the commuting, class-two, and length-two
relations in `Commutator.Basic`, this supplies the exceptional rank-two pointwise Chevalley
relation needed by the integral Chevalley--Demazure construction.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_g2_relations`: the
  type-`G₂` product relation with its four output points supplied by the caller.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_g2_relations'`: the same
  relation with all four output points written explicitly.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_g2_relations`: the
  conjugation form of the relation.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_conj_of_g2_relations'`: the
  explicit-parameter conjugation form.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ x ∈ kostantForm e h, ∀ v ∈ M, ρ x v ∈ M)

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- **The type-`G₂` Chevalley commutator relation for Kostant root subgroups.** The indices
`i, j, k, l, m, o` correspond respectively to the roots
`α, β, α + β, 2α + β, 3α + β, 3α + 2β`. The four supplied points have parameters
`c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupPoints_mul_of_g2_relations
    {i j k l m o : ι} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (b : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r *
        kostantRootSubgroupPoints e h ρ M hM o ho s *
        kostantRootSubgroupPoints e h ρ M hM i hi f := by
  let x := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  let y := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))
  let z := c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))
  let w := d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))
  let v := a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))
  let z' := b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))
  have hxy : x * y = y * x + z :=
    mul_eq_mul_add_zsmul_of_lie_eq ρ hij
  have hxz : x * z = z * x + 2 • w := by
    have hbracket := congrArg (c • ·) (mul_sub_mul_eq_map_ι_lie ρ (e i) (e k))
    rw [← map_zsmul, ← map_zsmul, hik, map_zsmul, map_zsmul] at hbracket
    rw [← sub_eq_iff_eq_add']
    have htwo : (2 : ℕ) • w = (2 : ℤ) • w := (natCast_zsmul w 2).symm
    rw [htwo]
    simpa only [x, z, w, smul_sub, mul_smul_comm, smul_mul_assoc, mul_zsmul] using hbracket
  have hxw : x * w = w * x + 3 • v := by
    have hbracket := congrArg (d • ·) (mul_sub_mul_eq_map_ι_lie ρ (e i) (e l))
    rw [← map_zsmul, ← map_zsmul, hil, map_zsmul, map_zsmul] at hbracket
    rw [← sub_eq_iff_eq_add']
    have hthree : (3 : ℕ) • v = (3 : ℤ) • v := (natCast_zsmul v 3).symm
    rw [hthree]
    simpa only [x, w, v, smul_sub, mul_smul_comm, smul_mul_assoc, mul_zsmul] using hbracket
  have hwz : w * z = z * w + 3 • z' := by
    have hbracket := congrArg ((d * c) • ·) (mul_sub_mul_eq_map_ι_lie ρ (e l) (e k))
    rw [← map_zsmul, ← map_zsmul, hlk, map_zsmul, map_zsmul] at hbracket
    rw [← sub_eq_iff_eq_add']
    have hthree : (3 : ℕ) • z' = (3 : ℤ) • z' := (natCast_zsmul z' 3).symm
    rw [hthree]
    simp only [z, w, z', mul_smul_comm, smul_mul_assoc]
    have hcd : c • d •
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l)) *
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) =
        d • c •
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l)) *
            ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) := by
      rw [← mul_zsmul, mul_comm c d, mul_zsmul]
    rw [hcd]
    simpa only [smul_sub, mul_zsmul] using hbracket
  have hxv : Commute x v := (commute_of_lie_eq_zero ρ him).smul_right a
  have hxz' : Commute x z' := (commute_of_lie_eq_zero ρ hio).smul_right b
  have hyz : Commute y z := (commute_of_lie_eq_zero ρ hjk).smul_right c
  have hwv : Commute w v := ((commute_of_lie_eq_zero ρ hlm).smul_left d).smul_right a
  have hzz' : Commute z z' := ((commute_of_lie_eq_zero ρ hko).smul_left c).smul_right b
  have hwz' : Commute w z' := ((commute_of_lie_eq_zero ρ hlo).smul_left d).smul_right b
  have hvz' : Commute v z' := ((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right b
  have hMz := dividedPower_zsmul_apply_mem e h ρ M hM c k
  have hMw := dividedPower_zsmul_apply_mem e h ρ M hM d l
  have hMv := dividedPower_zsmul_apply_mem e h ρ M hM a m
  have hMz' := dividedPower_zsmul_apply_mem e h ρ M hM b o
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  rw [hp, hq, hr, hs,
    ← baseChangeExp_zsmul c M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv) hMz hk,
    ← baseChangeExp_zsmul d M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM l n hv) hMw hl,
    ← baseChangeExp_zsmul a M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM m n hv) hMv hm,
    ← baseChangeExp_zsmul b M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM o n hv) hMz' ho]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M hxy hxz hxw hwz hxv
    hxz' hyz hwv hzz' hwz' hvz' hi hj (hk.smul c) (hl.smul d) _ _ hMz hMw hMv hMz' _ _

/-- The type-`G₂` Chevalley commutator relation with the four additional root-subgroup points
written explicitly at parameters `c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupPoints_mul_of_g2_relations'
    {i j k l m o : ι} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
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
        kostantRootSubgroupPoints e h ρ M hM m hm
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM o ho
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((b : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) *
        kostantRootSubgroupPoints e h ρ M hM i hi f :=
  kostantRootSubgroupPoints_mul_of_g2_relations e h ρ M hM hij hik hil hlk him hio hjk hlm hko
    hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- The conjugation form of the type-`G₂` Chevalley relation. Conjugating the `β`-root subgroup by
the `α`-root subgroup produces the four positive-root factors at parameters
`c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupPoints_conj_of_g2_relations
    {i j k l m o : ι} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (b : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g *
        (kostantRootSubgroupPoints e h ρ M hM i hi f)⁻¹ =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r *
        kostantRootSubgroupPoints e h ρ M hM o ho s := by
  rw [kostantRootSubgroupPoints_mul_of_g2_relations e h ρ M hM hij hik hil hlk him hio hjk hlm
    hko hlo hmo hi hj hk hl hm ho f g p q r s hp hq hr hs, mul_inv_cancel_right]

/-- The conjugation form of the type-`G₂` Chevalley relation with all four additional
root-subgroup points written explicitly. -/
theorem kostantRootSubgroupPoints_conj_of_g2_relations'
    {i j k l m o : ι} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
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
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM m hm
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM o ho
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((b : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) :=
  kostantRootSubgroupPoints_conj_of_g2_relations e h ρ M hM hij hik hil hlk him hio hjk hlm hko
    hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
