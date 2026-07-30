/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Classification
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Action.End

/-!
# The automorphism group of the complex unit disc

`Conformal/UnitDisc/Automorphism/Classification.lean` shows that a holomorphic self-map of the
open unit disc with a holomorphic two-sided inverse has the standard form
`z ↦ u * (z - a) / (1 - conj a * z)`.  That is a statement about individual maps.  This file
turns the family into the *group* `Aut(𝔻)` that the conformal-mapping roadmap's L2 layer asks
for, and identifies it with the standard family.

The group is `unitDiscAut`, a `Subgroup (Equiv.Perm Complex.UnitDisc)`: a permutation of the
bundled disc belongs to it exactly when both it and its inverse are restrictions of functions
`ℂ → ℂ` that are holomorphic on `Metric.ball 0 1` (the predicate `IsHolomorphicUnitDiscPerm`).
Stated this way the subgroup axioms are elementary — a composite of holomorphic maps is
holomorphic — while the classification supplies the description of the underlying set.

## Main results

* `TauCeti.unitDiscAut` — the group of holomorphic automorphisms of the unit disc.
* `TauCeti.mem_unitDiscAut_iff` — `Aut(𝔻) = {z ↦ u * (z - a) / (1 - conj a * z)}`: a permutation
  of the disc is a holomorphic automorphism iff it is a standard automorphism.
* `TauCeti.unitDiscStandardAutomorphismEquiv_symm_eq` — the standard family is closed under
  inversion, with the explicit parameters `(u, a) ↦ (u⁻¹, u • (-a))`.
* `TauCeti.exists_unitDiscStandardAutomorphismEquiv_mul` — it is closed under composition; the
  parameters of the composite are supplied abstractly by the group structure rather than by a
  direct computation.
* `TauCeti.exists_mem_unitDiscAut_apply_eq` — `Aut(𝔻)` acts transitively on the disc.
* `TauCeti.mem_unitDiscRotation_iff` — the stabiliser of the origin is the rotation subgroup
  `unitDiscRotation`, the image of `Circle` under its action on the disc.

Transitivity together with the stabiliser description is how `Aut(𝔻)` gets used downstream:
normalise a map at a chosen base point (transitivity), then read off the freedom that is left
over (a rotation).

This discharges the group half of the conformal-mapping roadmap's L2 description of the disc
automorphism group `Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}` (see `ConformalMapping/README.md`).  As with
the rest of the L0--L3 conformal-mapping material, it is coordinated with the upstream Mathlib
Riemann-mapping effort leanprover-community/mathlib4#33505, whose human-curated predecessors are
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`; should a disc
automorphism group land upstream, these declarations are a temporary shim to be deleted and their
consumers refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §2.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- A permutation of the complex unit disc is *holomorphic* when it is the restriction of a
function `ℂ → ℂ` that is holomorphic on the open unit ball.

Holomorphy of a map of the bundled disc is phrased through a scalar representative, matching the
generality bar of the conformal-mapping roadmap (everything is stated for `f : ℂ → ℂ`) and the
hypotheses of `exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv`. -/
def IsHolomorphicUnitDiscPerm (e : Equiv.Perm Complex.UnitDisc) : Prop :=
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (0 : ℂ) 1) ∧ ∀ z : Complex.UnitDisc, (e z : ℂ) = f z

/-- A scalar representative of a self-map of the disc maps the open unit ball into itself. -/
lemma mapsTo_ball_of_forall_coe_eq {e : Complex.UnitDisc → Complex.UnitDisc} {f : ℂ → ℂ}
    (hf : ∀ z : Complex.UnitDisc, (e z : ℂ) = f z) :
    MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have := (e (Complex.UnitDisc.mk w hw')).norm_lt_one
  rw [hf (Complex.UnitDisc.mk w hw')] at this
  simpa [mem_ball_zero_iff] using this

/-- **The automorphism group of the unit disc.** A permutation of `Complex.UnitDisc` is a
holomorphic automorphism when both it and its inverse extend to functions that are holomorphic
on the open unit ball. -/
def unitDiscAut : Subgroup (Equiv.Perm Complex.UnitDisc) where
  carrier := {e | IsHolomorphicUnitDiscPerm e ∧ IsHolomorphicUnitDiscPerm e.symm}
  one_mem' :=
    ⟨⟨id, differentiableOn_id, fun _ => rfl⟩, ⟨id, differentiableOn_id, fun _ => rfl⟩⟩
  mul_mem' := by
    rintro e₁ e₂ ⟨⟨f₁, hf₁, hf₁e⟩, ⟨g₁, hg₁, hg₁e⟩⟩ ⟨⟨f₂, hf₂, hf₂e⟩, ⟨g₂, hg₂, hg₂e⟩⟩
    refine ⟨⟨f₁ ∘ f₂, hf₁.comp hf₂ (mapsTo_ball_of_forall_coe_eq hf₂e), fun z => ?_⟩,
      ⟨g₂ ∘ g₁, hg₂.comp hg₁ (mapsTo_ball_of_forall_coe_eq hg₁e), fun z => ?_⟩⟩
    · rw [Equiv.Perm.mul_apply, hf₁e (e₂ z), hf₂e z, Function.comp_apply]
    · rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hg₂e (e₁.symm z), hg₁e z,
        Function.comp_apply]
  inv_mem' := by
    rintro e ⟨he, hesymm⟩
    exact ⟨hesymm, by rwa [Equiv.Perm.inv_def, Equiv.symm_symm]⟩

lemma mem_unitDiscAut {e : Equiv.Perm Complex.UnitDisc} :
    e ∈ unitDiscAut ↔ IsHolomorphicUnitDiscPerm e ∧ IsHolomorphicUnitDiscPerm e.symm :=
  Iff.rfl

/-- The inverse of a standard disc automorphism is again one: inverting `z ↦ u * (z - a) /
(1 - conj a * z)` replaces the rotation `u` by `u⁻¹` and moves the centre to the image `u • (-a)`
of the origin. -/
lemma unitDiscStandardAutomorphismEquiv_symm_eq (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a).symm =
      unitDiscStandardAutomorphismEquiv u⁻¹ (u • (-a)) := by
  refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
  have hu : (u : ℂ) ≠ 0 := u.coe_ne_zero
  have hconj : (starRingEnd ℂ) (u : ℂ) = (u : ℂ)⁻¹ := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]
  have hd₁ : 1 - (starRingEnd ℂ) (a : ℂ) * ((u : ℂ)⁻¹ * (z : ℂ)) ≠ 0 := by
    simpa using one_sub_conj_mul_ne_zero_unitDisc (u⁻¹ • z) a
  have hd₂ : 1 - (starRingEnd ℂ) ((u : ℂ) * -(a : ℂ)) * (z : ℂ) ≠ 0 := by
    simpa using one_sub_conj_mul_ne_zero_unitDisc z (u • (-a))
  rw [map_mul, map_neg, hconj] at hd₂
  simp only [unitDiscStandardAutomorphismEquiv_symm, Equiv.trans_apply, MulAction.toPerm_apply,
    unitDiscMoebiusEquiv_apply, coe_unitDiscMoebius, coe_unitDiscStandardAutomorphismEquiv_apply,
    Complex.UnitDisc.coe_circle_smul, Complex.UnitDisc.coe_neg, Circle.coe_inv, map_mul, map_neg,
    hconj, sub_neg_eq_add]
  field_simp
  ring

/-- A standard disc automorphism is holomorphic. -/
lemma isHolomorphicUnitDiscPerm_unitDiscStandardAutomorphismEquiv
    (u : Circle) (a : Complex.UnitDisc) :
    IsHolomorphicUnitDiscPerm (unitDiscStandardAutomorphismEquiv u a) :=
  ⟨fun w => (u : ℂ) * ((w - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * w)),
    differentiableOn_unitDiscStandardAutomorphismFormula u a,
    fun z => coe_unitDiscStandardAutomorphismEquiv_apply u a z⟩

/-- Every standard disc automorphism is a holomorphic automorphism of the disc. -/
lemma unitDiscStandardAutomorphismEquiv_mem_unitDiscAut (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a ∈ unitDiscAut :=
  ⟨isHolomorphicUnitDiscPerm_unitDiscStandardAutomorphismEquiv u a, by
    rw [unitDiscStandardAutomorphismEquiv_symm_eq]
    exact isHolomorphicUnitDiscPerm_unitDiscStandardAutomorphismEquiv _ _⟩

/-- **`Aut(𝔻) = {e^{iθ}(z − a)/(1 − āz)}`.** A permutation of the complex unit disc is a
holomorphic automorphism exactly when it is a standard automorphism.

The forward direction is the classification theorem
`exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv`, which rests on the Schwarz lemma;
the converse is the holomorphy of the standard formula and of its inverse. -/
theorem mem_unitDiscAut_iff {e : Equiv.Perm Complex.UnitDisc} :
    e ∈ unitDiscAut ↔
      ∃ (u : Circle) (a : Complex.UnitDisc), e = unitDiscStandardAutomorphismEquiv u a := by
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨⟨f, hf, hfe⟩, ⟨g, hg, hge⟩⟩ := he
    have hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := mapsTo_ball_of_forall_coe_eq hfe
    have hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := mapsTo_ball_of_forall_coe_eq hge
    have hgf' : ∀ z : Complex.UnitDisc, g (f z) = z := fun z => by
      rw [← hfe z, ← hge (e z), Equiv.symm_apply_apply]
    have hfg' : ∀ z : Complex.UnitDisc, f (g z) = z := fun z => by
      rw [← hge z, ← hfe (e.symm z), Equiv.apply_symm_apply]
    have hgf : LeftInvOn g f (ball (0 : ℂ) 1) := fun w hw =>
      hgf' (Complex.UnitDisc.mk w (by simpa [mem_ball_zero_iff] using hw))
    have hfg : RightInvOn g f (ball (0 : ℂ) 1) := fun w hw =>
      hfg' (Complex.UnitDisc.mk w (by simpa [mem_ball_zero_iff] using hw))
    obtain ⟨u, a, -, hua⟩ :=
      exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv hf hg hfmaps hgmaps hgf hfg
    exact ⟨u, a, Equiv.ext fun z =>
      Complex.UnitDisc.coe_injective (by rw [hfe z, hua z])⟩
  · rintro ⟨u, a, rfl⟩
    exact unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u a

/-- The underlying set of `Aut(𝔻)` is the range of the standard parametrisation by a rotation
and a centre. -/
theorem coe_unitDiscAut :
    (unitDiscAut : Set (Equiv.Perm Complex.UnitDisc)) =
      range fun p : Circle × Complex.UnitDisc => unitDiscStandardAutomorphismEquiv p.1 p.2 := by
  ext e
  simp only [SetLike.mem_coe, mem_range, Prod.exists]
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨u, a, rfl⟩ := mem_unitDiscAut_iff.1 he
    exact ⟨u, a, rfl⟩
  · rintro ⟨u, a, rfl⟩
    exact unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u a

/-- The standard disc automorphisms are closed under composition.

This is a corollary of the group structure and the classification: no computation with the
composite of two Moebius factors is needed. -/
theorem exists_unitDiscStandardAutomorphismEquiv_mul
    (u₁ u₂ : Circle) (a₁ a₂ : Complex.UnitDisc) :
    ∃ (u : Circle) (a : Complex.UnitDisc),
      unitDiscStandardAutomorphismEquiv u₁ a₁ * unitDiscStandardAutomorphismEquiv u₂ a₂ =
        unitDiscStandardAutomorphismEquiv u a :=
  mem_unitDiscAut_iff.1
    (mul_mem (unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u₁ a₁)
      (unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u₂ a₂))

/-- **`Aut(𝔻)` acts transitively on the disc.** Any point of the disc can be moved to any other
by a holomorphic automorphism, namely the composite of the Moebius factor centred at the source
with the inverse of the one centred at the target. -/
theorem exists_mem_unitDiscAut_apply_eq (z w : Complex.UnitDisc) :
    ∃ e ∈ unitDiscAut, e z = w := by
  refine ⟨(unitDiscMoebiusEquiv w).symm * unitDiscMoebiusEquiv z, ?_, ?_⟩
  · refine mul_mem ?_ ?_
    · rw [← unitDiscStandardAutomorphismEquiv_one w]
      exact inv_mem (unitDiscStandardAutomorphismEquiv_mem_unitDiscAut 1 w)
    · rw [← unitDiscStandardAutomorphismEquiv_one z]
      exact unitDiscStandardAutomorphismEquiv_mem_unitDiscAut 1 z
  · rw [Equiv.Perm.mul_apply, unitDiscMoebiusEquiv_apply, unitDiscMoebius_self,
      unitDiscMoebiusEquiv_symm, unitDiscMoebiusEquiv_apply, unitDiscMoebius_apply_zero, neg_neg]

/-- The rotations `z ↦ u * z`, as a subgroup of the permutations of the unit disc.  It is the
image of `Circle` under its multiplicative action on the disc. -/
noncomputable def unitDiscRotation : Subgroup (Equiv.Perm Complex.UnitDisc) :=
  (MulAction.toPermHom Circle Complex.UnitDisc).range

lemma mem_unitDiscRotation_iff_exists {e : Equiv.Perm Complex.UnitDisc} :
    e ∈ unitDiscRotation ↔ ∃ u : Circle, MulAction.toPerm u = e := by
  simp [unitDiscRotation, MonoidHom.mem_range]

lemma unitDiscStandardAutomorphismEquiv_zero_mem_unitDiscRotation (u : Circle) :
    unitDiscStandardAutomorphismEquiv u 0 ∈ unitDiscRotation :=
  mem_unitDiscRotation_iff_exists.2 ⟨u, (unitDiscStandardAutomorphismEquiv_zero u).symm⟩

/-- **The stabiliser of the origin in `Aut(𝔻)` is the rotation group.** A permutation of the disc
is a rotation exactly when it is a holomorphic automorphism fixing the origin.

The forward implication is immediate; the converse is the classification, which forces the centre
of a standard automorphism fixing `0` to be `0`.  This is the group-theoretic form of the
rigidity statement behind the Schwarz lemma. -/
theorem mem_unitDiscRotation_iff {e : Equiv.Perm Complex.UnitDisc} :
    e ∈ unitDiscRotation ↔ e ∈ unitDiscAut ∧ e 0 = 0 := by
  constructor
  · intro he
    obtain ⟨u, rfl⟩ := mem_unitDiscRotation_iff_exists.1 he
    refine ⟨?_, by simp⟩
    rw [← unitDiscStandardAutomorphismEquiv_zero u]
    exact unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u 0
  · rintro ⟨he, h0⟩
    obtain ⟨u, a, rfl⟩ := mem_unitDiscAut_iff.1 he
    have ha : a = 0 := by
      rw [unitDiscStandardAutomorphismEquiv_apply_zero, ← Complex.UnitDisc.coe_eq_zero,
        Complex.UnitDisc.coe_circle_smul, Complex.UnitDisc.coe_neg, mul_eq_zero, neg_eq_zero,
        Complex.UnitDisc.coe_eq_zero] at h0
      exact h0.resolve_left u.coe_ne_zero
    subst ha
    exact unitDiscStandardAutomorphismEquiv_zero_mem_unitDiscRotation u

/-- The rotations are holomorphic automorphisms of the disc. -/
theorem unitDiscRotation_le_unitDiscAut : unitDiscRotation ≤ unitDiscAut :=
  fun _ he => (mem_unitDiscRotation_iff.1 he).1

end TauCeti
