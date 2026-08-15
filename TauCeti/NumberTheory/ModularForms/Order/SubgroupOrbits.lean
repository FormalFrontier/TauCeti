/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Order
public import TauCeti.NumberTheory.ModularForms.Norm.Reduction
public import TauCeti.NumberTheory.ModularForms.Order.Orbits

import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Finite support of the order divisor at general level

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, the vanishing order of a modular form on
`Γ` is constant on `Γ`-orbits of the upper half-plane. This file descends the order to that
orbit space and proves that a nonzero form has nonzero order on only finitely many orbits.

The proof follows the norm-map route prescribed for the general-level valence formula. The
norm of the form is a nonzero level-one modular form, and its order dominates that of the
original form at every point. Thus every `Γ`-orbit in the support lies above an
`SL(2, ℤ)`-orbit in the finite support of the norm. Each such fiber is finite because a
finite-index subgroup splits any `SL(2, ℤ)`-orbit into only finitely many `Γ`-orbits.

## Main declarations

* `TauCeti.ModularForm.orderOfVanishingOnSubgroupOrbit`: the order descended to the
  `Γ`-orbit space.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnSubgroupOrbit`: finite support of
  the interior order divisor of a nonzero general-level modular form.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamond-shurman2005],
  Chapter 3.
-/

public noncomputable section

open UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- The vanishing order of a form for `Γ ≤ SL(2, ℤ)`, descended to the `Γ`-orbit space of
the upper half-plane. -/
public def orderOfVanishingOnSubgroupOrbit
    [SlashInvariantFormClass F (NormReduction.G Γ) k] (f : F)
    (q : MulAction.orbitRel.Quotient Γ ℍ) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt f) fun _ b ⟨g, hg⟩ ↦ by
    have hg' : g • b = _ := hg
    rw [← hg', Subgroup.smul_def, MulAction.compHom_smul_def,
      orderOfVanishingAt_smul f
        (γ := Matrix.SpecialLinearGroup.mapGL ℝ g.val) (by simp [NormReduction.G, g.2])
        (by rw [← Matrix.GeneralLinearGroup.val_det_apply,
          Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos) b]

/-- Evaluating the descended order on the orbit of `p` recovers the vanishing order at `p`. -/
@[simp]
public lemma orderOfVanishingOnSubgroupOrbit_mk
    [SlashInvariantFormClass F (NormReduction.G Γ) k] (f : F) (p : ℍ) :
    orderOfVanishingOnSubgroupOrbit f (Quotient.mk'' p) = orderOfVanishingAt f p := by
  unfold orderOfVanishingOnSubgroupOrbit
  rfl

private def subgroupOrbitToOrbit (Γ : Subgroup SL(2, ℤ)) :
    MulAction.orbitRel.Quotient Γ ℍ →
      MulAction.orbitRel.Quotient SL(2, ℤ) ℍ :=
  Setoid.map_of_le (MulAction.orbitRel_subgroup_le Γ)

@[simp]
private lemma subgroupOrbitToOrbit_mk (Γ : Subgroup SL(2, ℤ)) (p : ℍ) :
    subgroupOrbitToOrbit Γ (Quotient.mk'' p) = Quotient.mk'' p := by
  rfl

private lemma equivSubgroupOrbits_fst (Γ : Subgroup SL(2, ℤ))
    (r : MulAction.orbitRel.Quotient Γ ℍ) :
    (MulAction.equivSubgroupOrbits ℍ Γ r).1 = subgroupOrbitToOrbit Γ r := by
  induction r using Quotient.inductionOn' with
  | _ p => rfl

private noncomputable def subgroupOrbitFiberEquiv (Γ : Subgroup SL(2, ℤ))
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    {r : MulAction.orbitRel.Quotient Γ ℍ // subgroupOrbitToOrbit Γ r = q} ≃
      MulAction.orbitRel.Quotient Γ q.orbit :=
  ((MulAction.equivSubgroupOrbits ℍ Γ).subtypeEquiv fun r ↦ by
    rw [equivSubgroupOrbits_fst]).trans
    (Equiv.sigmaSubtype q)

private lemma finite_subgroupOrbitToOrbit_fiber [Γ.FiniteIndex]
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    Set.Finite (subgroupOrbitToOrbit Γ ⁻¹' {q}) := by
  let _ : Finite (MulAction.orbitRel.Quotient Γ q.orbit) :=
    Subgroup.finite_quotient_of_pretransitive_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := Γ))
  let _ : Finite {r : MulAction.orbitRel.Quotient Γ ℍ // subgroupOrbitToOrbit Γ r = q} :=
    Finite.of_equiv _ (subgroupOrbitFiberEquiv Γ q).symm
  let _ : Finite (subgroupOrbitToOrbit Γ ⁻¹' {q}) := Finite.of_injective
    (fun r : (subgroupOrbitToOrbit Γ ⁻¹' {q}) ↦
      (⟨r, Set.mem_singleton_iff.mp r.2⟩ :
        {s : MulAction.orbitRel.Quotient Γ ℍ // subgroupOrbitToOrbit Γ s = q}))
    fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h)
  exact Set.toFinite _

private lemma orderOfVanishingOnSubgroupOrbit_ne_zero_norm
    [Γ.FiniteIndex] [ModularFormClass F (NormReduction.G Γ) k] (f : F)
    {q : MulAction.orbitRel.Quotient Γ ℍ}
    (hq : orderOfVanishingOnSubgroupOrbit f q ≠ 0) :
    orderOfVanishingOnOrbit (_root_.ModularForm.norm 𝒮ℒ f)
      (subgroupOrbitToOrbit Γ q) ≠ 0 := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    rw [subgroupOrbitToOrbit_mk, orderOfVanishingOnOrbit_mk]
    have hpos : 0 < orderOfVanishingAt f p :=
      lt_of_le_of_ne (orderOfVanishingAt_nonneg (ModularFormClass.holo f) p) (Ne.symm hq)
    exact ne_of_gt (hpos.trans_le
      (orderOfVanishingAt_le_orderOfVanishingAt_norm (ℋ := 𝒮ℒ) f p))

/-- A nonzero modular form for a finite-index subgroup `Γ ≤ SL(2, ℤ)` has nonzero
vanishing order on only finitely many `Γ`-orbits in the upper half-plane.

This is the finite-support statement for the interior part of the general-level divisor.
It is obtained from the finite support of the level-one norm, order domination under the
norm, and finiteness of the fibers of `subgroupOrbitToOrbit`. -/
public theorem hasFiniteSupport_orderOfVanishingOnSubgroupOrbit
    [Γ.FiniteIndex] [ModularFormClass F (NormReduction.G Γ) k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (orderOfVanishingOnSubgroupOrbit f).HasFiniteSupport := by
  let normf := _root_.ModularForm.norm 𝒮ℒ f
  have hnorm' : normf ≠ 0 :=
    (_root_.ModularForm.norm_eq_zero_iff 𝒮ℒ f).not.mpr hf
  have hnorm : (⇑normf : ℍ → ℂ) ≠ 0 :=
    fun h ↦ hnorm' ((FunLike.coe_zero_iff normf).mp h)
  apply Set.Finite.of_finite_fibers (subgroupOrbitToOrbit Γ)
  · exact (hasFiniteSupport_orderOfVanishingOnOrbit hnorm).subset fun q hq ↦ by
      obtain ⟨r, hr, rfl⟩ := hq
      exact orderOfVanishingOnSubgroupOrbit_ne_zero_norm f hr
  · intro q _
    exact (finite_subgroupOrbitToOrbit_fiber q).subset Set.inter_subset_right

end ModularForm

end TauCeti

end
