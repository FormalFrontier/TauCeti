/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Rigidity
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Parametrization

/-!
# Fixed points of holomorphic self-maps of the unit disc

A holomorphic self-map of the open unit disc that fixes **two** distinct points of the disc is
the identity (`TauCeti.eqOn_id_of_isFixedPt_of_isFixedPt`); equivalently, the fixed-point set of
any self-map other than the identity is a subsingleton
(`TauCeti.eqOn_id_or_subsingleton_inter_fixedPoints`).

This generalises `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` of
`UnitDisc/Automorphism/Parametrization.lean`, which says the same for a member of `Aut(𝔻)`, from
automorphisms to arbitrary holomorphic self-maps.

## The argument

The automorphism case is exactly what the proof runs on.  Two fixed points make the
Schwarz--Pick contraction estimate an equality at that pair of points for a trivial reason —
both sides are the same pseudo-hyperbolic expression — so the classification form of
Schwarz--Pick rigidity,
`exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq`
of `SchwarzPick/Rigidity.lean`, turns `f` into a standard disc automorphism
`ζ ↦ u * (ζ - b) / (1 - conj b * ζ)`.  Its two fixed points then force it to be the identity of
`Aut(𝔻)` by the already-merged automorphism statement.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ`
for every theorem added in layers L0--L6, everything below is stated for maps of `ℂ`, matching
the rest of `Conformal/SchwarzPick/`.  The hypothesis `Function.IsFixedPt f a` is Mathlib's
spelling of `f a = a`, as in `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt`.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, the
L0--L3 material of this roadmap overlaps the in-progress human-curated Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves its
prerequisites internally as private lemmas; Mathlib's `Analysis/Complex/Schwarz.lean` and
`Analysis/Complex/BranchLogRoot.lean` are the preceding human-curated work.  This file is
therefore a **temporary shim** in the same sense as the rest of `Conformal/SchwarzPick/`: should
a human-curated fixed-point form of Schwarz--Pick land upstream, these statements are to be
backed by it, or deleted and their consumers refactored onto it.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VI §2.
-/

public section

namespace TauCeti

open Metric Set

variable {f : ℂ → ℂ} {z w : ℂ}

/-- **A holomorphic self-map of the disc with two distinct fixed points is the identity.**

If `f` is differentiable on the open unit ball `ball (0 : ℂ) 1`, maps that ball into itself and
fixes two distinct points `z ≠ w` of it, then `f` agrees with the identity on the whole ball.
This is `TauCeti.eq_one_of_mem_unitDiscAut_of_isFixedPt` with its hypothesis weakened from
membership in `Aut(𝔻)` to an arbitrary holomorphic self-map. -/
theorem eqOn_id_of_isFixedPt_of_isFixedPt (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) (hz : z ∈ ball (0 : ℂ) 1)
    (hw : w ∈ ball (0 : ℂ) 1) (hne : z ≠ w) (hfz : Function.IsFixedPt f z)
    (hfw : Function.IsFixedPt f w) : EqOn f id (ball (0 : ℂ) 1) := by
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hw1 : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
  have heq : pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w := by
    rw [hfz.eq, hfw.eq]
  obtain ⟨u, b, hb⟩ :=
    exists_forall_unitDisc_eq_unitDiscStandardAutomorphismEquiv_of_pseudoHyperbolicExpr_map_eq
      hf hmaps hz hw hne heq
  -- Read the two fixed points inside the disc as fixed points of the automorphism.
  have hmem : unitDiscStandardAutomorphismEquiv u b ∈ unitDiscAut :=
    unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u b
  have hfix : ∀ {p : ℂ} (hp : ‖p‖ < 1), Function.IsFixedPt f p →
      Function.IsFixedPt (unitDiscStandardAutomorphismEquiv u b) (Complex.UnitDisc.mk p hp) := by
    intro p hp hfp
    have h := hb (Complex.UnitDisc.mk p hp)
    rw [Complex.UnitDisc.coe_mk, hfp.eq] at h
    exact Complex.UnitDisc.coe_injective (h.symm.trans (Complex.UnitDisc.coe_mk p hp).symm)
  have hmkne : Complex.UnitDisc.mk z hz1 ≠ Complex.UnitDisc.mk w hw1 := by
    intro h
    exact hne (by simpa using congrArg (fun t : Complex.UnitDisc => (t : ℂ)) h)
  have hone : unitDiscStandardAutomorphismEquiv u b = 1 :=
    eq_one_of_mem_unitDiscAut_of_isFixedPt hmem hmkne (hfix hz1 hfz) (hfix hw1 hfw)
  intro ζ hζ
  have hζ1 : ‖ζ‖ < 1 := by simpa [mem_ball_zero_iff] using hζ
  have h := hb (Complex.UnitDisc.mk ζ hζ1)
  rw [hone] at h
  simpa using h

/-- **The fixed-point set of a self-map other than the identity is a subsingleton.** -/
theorem subsingleton_inter_fixedPoints_of_not_eqOn_id
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hid : ¬ EqOn f id (ball (0 : ℂ) 1)) :
    (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton := by
  rintro p ⟨hp, hfp⟩ q ⟨hq, hfq⟩
  by_contra hne
  exact hid (eqOn_id_of_isFixedPt_of_isFixedPt hf hmaps hp hq hne hfp hfq)

/-- **The fixed-point dichotomy for a holomorphic self-map of the disc.** Either the map is the
identity, or it fixes at most one point of the disc. -/
theorem eqOn_id_or_subsingleton_inter_fixedPoints (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1)) :
    EqOn f id (ball (0 : ℂ) 1) ∨ (ball (0 : ℂ) 1 ∩ Function.fixedPoints f).Subsingleton := by
  by_cases hid : EqOn f id (ball (0 : ℂ) 1)
  · exact Or.inl hid
  · exact Or.inr (subsingleton_inter_fixedPoints_of_not_eqOn_id hf hmaps hid)

end TauCeti
