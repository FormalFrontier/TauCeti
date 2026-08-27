/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The `2`-torsion of the group of points of a Weierstrass curve

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`. In that normal form negation is `-(x, y) = (x, -y)`, so a point is its own
negative exactly when `y = 0`, and the `2`-torsion of `W(K)` is the origin together with the
points `(x, 0)` at the roots of `f`.

The counting statement `card_ker_nsmul_two` is what turns a root count into a torsion count. It
is one side of the archimedean local-image formula of explicit `2`-descent, which reads
`#(im μ_v) = #E(ℝ)[2] / 2` at a real place.

## Main statements

* `WeierstrassCurve.Affine.card_ker_nsmul_two`: `#W(K)[2]` is the number of roots of `f` in `K`,
  plus one for the origin.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean` lines 806-868 — the `2`-torsion section, which sits after
the range that `TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean` ported.

This advances `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (README:813-820), whose
"Explicit `2`-descent (core, this layer)" bullet names the local conditions and the rank bound;
the archimedean local-image count needs this torsion count.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

variable {K : Type*} [Field K] (W : Affine K) [W.IsCharNeTwoNF] [W.IsElliptic] [DecidableEq K]

/-- **The `2`-torsion of `W(K)` has one more element than `f` has roots in `K`.**

The underlying reason is that the `2`-torsion is the origin together with the points `(x, 0)` at
the roots of `f`; that set equality is established inside the proof, but only the cardinality is
exported, because that is all the archimedean local-image count consumes. A caller needing the
identification itself should ask for it as its own theorem. -/
theorem card_ker_nsmul_two : Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker =
    Nat.card {x : K // W.f.eval x = 0} + 1 := by
  have h2F : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  have hfin : Finite {x : K | W.f.eval x = 0} :=
    Set.Finite.to_subtype (Polynomial.finite_setOfPred_isRoot W.f_ne_zero)
  set pt : {x : K | W.f.eval x = 0} → W.Point :=
    fun x ↦ Point.some _ _ (W.nonsingular_of_eval_f_eq_zero x.2)
  have hinj : Function.Injective pt := by
    intro a b hab
    exact Subtype.ext ((Point.some.injEq _ _ _ _ _ _).mp hab).1
  have hset : ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point) =
      insert 0 (Set.range pt) := by
    ext P
    constructor
    · intro hP
      induction P with
      | zero => exact Set.mem_insert _ _
      | some x y h =>
        have hy := y_eq_zero_of_order_two h2F h (hP : (2 : ℕ) • (Point.some x y h : W.Point) = 0)
        subst hy
        have hx : W.f.eval x = 0 := by
          have := (W.equation_iff_eval_f_eq_sq x 0).mp h.1
          simpa using this
        exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · intro hP
      rcases Set.mem_insert_iff.mp hP with rfl | ⟨x, rfl⟩
      · exact zero_mem _
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, two_nsmul]
        exact Point.add_self_of_Y_eq (by rw [negY_of_isCharNeTwoNF, neg_zero])
  calc Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker
      = ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point).ncard := Nat.card_coe_set_eq _
    _ = (insert 0 (Set.range pt)).ncard := by rw [hset]
    _ = (Set.range pt).ncard + 1 :=
        Set.ncard_insert_of_notMem (by intro ⟨x, hx⟩; exact Point.some_ne_zero _ hx)
    _ = Nat.card {x : K // W.f.eval x = 0} + 1 := by
        rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
        rfl

end Affine

end WeierstrassCurve

end
