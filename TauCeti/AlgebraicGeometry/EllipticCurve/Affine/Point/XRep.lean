/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Fibres of the projective `x`-coordinate

The map `Point.xRep` sending an affine point to a projective representative of its
`x`-coordinate has finite fibres: a value of `x` is attained by at most the two points `±P` above
it. Stated separately from the duplication formulae because it uses none of them — only the
injectivity of `xRep` up to sign — and because the Northcott finiteness argument in
`TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight` consumes it directly.

## Main results

* `WeierstrassCurve.Affine.finite_preimage_xRep` : the fibre of `xRep` over `![x, 1]` is finite.
* `WeierstrassCurve.Affine.finite_preimage_xRep0` : the fibre of the zeroth homogeneous
  coordinate `xRep 0` is finite.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- Only finitely many points share a given projective `x`-coordinate. -/
lemma finite_preimage_xRep (x : F) : {P : W.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : W.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_ofPred_eq] at hQ
  have hpair : {P : W.Point | P.xRep = ![x, 1]} = {Q, -Q} := by
    ext : 1; simp [← hQ, Point.xRep_eq_xRep_iff]
  rw [hpair]
  simp

/-- Only finitely many points share a given value of `xRep 0`, the zeroth *homogeneous*
coordinate of the projective representative. For a nonzero point this is the affine
`x`-coordinate, but at the point at infinity `xRep = ![1, 0]`, so the value there is `1` — which
is why the proof carries the extra `{0}` case. -/
lemma finite_preimage_xRep0 (x : F) : {P : W.Point | P.xRep 0 = x}.Finite := by
  have : {P : W.Point | P.xRep 0 = x} ⊆ {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset this

end Affine

end WeierstrassCurve

end
