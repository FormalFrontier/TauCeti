/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector

/-!
# The quadratic elements of a Clifford algebra as a Lie subalgebra

A Clifford algebra is an associative algebra, so its commutator makes it a Lie algebra. Inside it
the **quadratic elements** — the span of the half-normalized commutators
`TauCeti.CliffordAlgebra.cliffordBivector Q a b` of two generators — are closed under the bracket,
and this file equips them with the resulting `LieSubalgebra` structure.

Closure is a two-line consequence of the action-normalization identity
`TauCeti.CliffordAlgebra.cliffordBivector_lie_ι`, which says that a Clifford bivector brackets a
generator to the infinitesimal rotation `x ↦ polar Q b x • a - polar Q a x • b`. Because bracketing
with a fixed element is a derivation for the associative product, the bracket of two Clifford
bivectors is obtained by rotating each of the two generators of the second one in turn, so it is
again a sum of two Clifford bivectors
(`TauCeti.CliffordAlgebra.lie_cliffordBivector_cliffordBivector`).

Nothing here needs the quadratic form to be nondegenerate, the module to be finite-dimensional, or
the base to be a field: the statements hold over any commutative ring in which `2` is invertible.
The identification of this subalgebra with `𝔰𝔬(V, Q)` — Mathlib's
`skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)` — does need those hypotheses, and is not
proved here; the bridging fact this file does supply is that a quadratic element brackets every
generator back into the generators
(`TauCeti.CliffordAlgebra.lie_ι_mem_range_ι_of_mem_quadraticLieSubalgebra`), which is what makes
that comparison map exist at all.

Following Mathlib's `Mathlib/Algebra/Lie/SkewAdjoint.lean`, the Lie ring structure on an
associative ring is a *local* instance (`LieRing.ofAssociativeRing`): it cannot be global, since it
would clash with the module bracket when a ring is regarded as a module over itself. A downstream
file that states results about `quadraticLieSubalgebra` therefore has to put the same attribute in
scope.

## Main definitions

* `TauCeti.CliffordAlgebra.quadraticLieSubalgebra`: the quadratic elements of `CliffordAlgebra Q`,
  as a Lie subalgebra under the commutator bracket.

## Main results

* `TauCeti.CliffordAlgebra.lie_cliffordBivector_cliffordBivector`: the bracket of two Clifford
  bivectors, as a sum of two Clifford bivectors.
* `TauCeti.CliffordAlgebra.quadraticLieSubalgebra_toSubmodule_le`: the universal property of the
  underlying submodule, from which the containments below are read off.
* `TauCeti.CliffordAlgebra.quadraticLieSubalgebra_le_evenOdd_zero`,
  `TauCeti.CliffordAlgebra.quadraticLieSubalgebra_le_even` and
  `TauCeti.CliffordAlgebra.quadraticLieSubalgebra_le_filtration_two`: the quadratic elements are
  even and have filtration degree at most two.
* `TauCeti.CliffordAlgebra.quadraticLieSubalgebra_toSubmodule_eq_range`: they are exactly the image
  of `⋀[R]^2 M` under `TauCeti.CliffordAlgebra.cliffordBivectorExterior`.
* `TauCeti.CliffordAlgebra.lie_ι_mem_range_ι_of_mem_quadraticLieSubalgebra`: bracketing with a
  quadratic element preserves the generators.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 9, "the abstract quadratic realization".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

omit [Invertible (2 : R)] in
/-- Bracketing with a fixed element of an associative ring is a derivation. -/
private theorem lie_mul (x y z : CliffordAlgebra Q) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- **The bracket of two Clifford bivectors.** Bracketing with `cliffordBivector Q a b` is a
derivation which rotates a generator by `x ↦ polar Q b x • a - polar Q a x • b`, so it takes the
Clifford bivector of `(c, d)` to the sum of the Clifford bivectors of the two rotated pairs. This
is the closure property that makes the quadratic elements a Lie subalgebra. -/
theorem lie_cliffordBivector_cliffordBivector (a b c d : M) :
    ⁅cliffordBivector Q a b, cliffordBivector Q c d⁆ =
      cliffordBivector Q
          (QuadraticMap.polar Q b c • a - QuadraticMap.polar Q a c • b) d +
        cliffordBivector Q c
          (QuadraticMap.polar Q b d • a - QuadraticMap.polar Q a d • b) := by
  rw [cliffordBivector_def Q c d, lie_smul, lie_sub, lie_mul, lie_mul, cliffordBivector_lie_ι,
    cliffordBivector_lie_ι, cliffordBivector_def Q _ d, cliffordBivector_def Q c _, ← smul_add]
  congr 1
  abel

/-- The set of Clifford bivectors of `Q`, indexed by pairs of vectors. -/
private def bivectorSet : Set (CliffordAlgebra Q) :=
  Set.range fun p : M × M => cliffordBivector Q p.1 p.2

private theorem cliffordBivector_mem_span (a b : M) :
    cliffordBivector Q a b ∈ Submodule.span R (bivectorSet Q) :=
  Submodule.subset_span ⟨(a, b), rfl⟩

private theorem lie_cliffordBivector_mem_span (a b : M) {y : CliffordAlgebra Q}
    (hy : y ∈ Submodule.span R (bivectorSet Q)) :
    ⁅cliffordBivector Q a b, y⁆ ∈ Submodule.span R (bivectorSet Q) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    rw [lie_cliffordBivector_cliffordBivector]
    exact add_mem (cliffordBivector_mem_span Q _ _) (cliffordBivector_mem_span Q _ _)
  | zero => rw [lie_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hy hz => rw [lie_add]; exact Submodule.add_mem _ hy hz
  | smul r _ _ hy => rw [lie_smul]; exact Submodule.smul_mem _ r hy

private theorem lie_mem_span {x y : CliffordAlgebra Q}
    (hx : x ∈ Submodule.span R (bivectorSet Q)) (hy : y ∈ Submodule.span R (bivectorSet Q)) :
    ⁅x, y⁆ ∈ Submodule.span R (bivectorSet Q) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    exact lie_cliffordBivector_mem_span Q _ _ hy
  | zero => rw [zero_lie]; exact Submodule.zero_mem _
  | add _ _ _ _ hz hw => rw [add_lie]; exact Submodule.add_mem _ hz hw
  | smul r _ _ hz => rw [smul_lie]; exact Submodule.smul_mem _ r hz

/-- **The quadratic elements of a Clifford algebra**, as a Lie subalgebra of `CliffordAlgebra Q`
under the commutator bracket: the `R`-span of the Clifford bivectors
`TauCeti.CliffordAlgebra.cliffordBivector Q a b`.

Unlike a transported bracket on `⋀[R]^2 M`, this is a subobject of the Clifford algebra itself, so
it needs no scoped instances beyond the local `LieRing.ofAssociativeRing` on an associative ring. -/
noncomputable def quadraticLieSubalgebra : LieSubalgebra R (CliffordAlgebra Q) :=
  { Submodule.span R (bivectorSet Q) with lie_mem' := lie_mem_span Q }

/-- The definitional pin: the quadratic elements are the span of the Clifford bivectors. -/
theorem quadraticLieSubalgebra_toSubmodule :
    (quadraticLieSubalgebra Q).toSubmodule =
      Submodule.span R (Set.range fun p : M × M => cliffordBivector Q p.1 p.2) := (rfl)

/-- Every Clifford bivector is a quadratic element. -/
theorem cliffordBivector_mem_quadraticLieSubalgebra (a b : M) :
    cliffordBivector Q a b ∈ quadraticLieSubalgebra Q :=
  cliffordBivector_mem_span Q a b

/-- **The universal property of the quadratic elements**: any submodule containing every Clifford
bivector contains them all. Every containment below is an instance of this. -/
theorem quadraticLieSubalgebra_toSubmodule_le {P : Submodule R (CliffordAlgebra Q)}
    (hP : ∀ a b : M, cliffordBivector Q a b ∈ P) :
    (quadraticLieSubalgebra Q).toSubmodule ≤ P := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨p, rfl⟩
  exact hP _ _

/-- The quadratic elements are even. -/
theorem quadraticLieSubalgebra_le_evenOdd_zero :
    (quadraticLieSubalgebra Q).toSubmodule ≤ evenOdd Q 0 :=
  quadraticLieSubalgebra_toSubmodule_le Q (cliffordBivector_mem_evenOdd_zero Q)

/-- The quadratic elements lie in the even subalgebra. -/
theorem quadraticLieSubalgebra_le_even :
    (quadraticLieSubalgebra Q).toSubmodule ≤ Subalgebra.toSubmodule (even Q) := by
  rw [CliffordAlgebra.even_toSubmodule]
  exact quadraticLieSubalgebra_le_evenOdd_zero Q

/-- The quadratic elements have filtration degree at most two. -/
theorem quadraticLieSubalgebra_le_filtration_two :
    (quadraticLieSubalgebra Q).toSubmodule ≤ filtration Q 2 :=
  quadraticLieSubalgebra_toSubmodule_le Q (cliffordBivector_mem_filtration_two Q)

/-- **The quadratic elements are the image of the second exterior power.** This is the sense in
which the Lie subalgebra realizes `⋀[R]^2 M` inside the Clifford algebra; the map itself is
`TauCeti.CliffordAlgebra.cliffordBivectorExterior`. -/
theorem quadraticLieSubalgebra_toSubmodule_eq_range :
    (quadraticLieSubalgebra Q).toSubmodule = LinearMap.range (cliffordBivectorExterior Q) :=
  le_antisymm
    (quadraticLieSubalgebra_toSubmodule_le Q fun a b =>
      ⟨exteriorPower.ιMulti R 2 ![a, b], cliffordBivectorExterior_apply_ιMulti Q a b⟩)
    (cliffordBivectorExterior_range_le Q _ (cliffordBivector_mem_quadraticLieSubalgebra Q))

/-- **Quadratic elements preserve the generators.** Bracketing with a quadratic element sends
`ι Q m` back into the image of `ι Q`; on the span of the generators it is therefore an
endomorphism, which is what the comparison with the skew-adjoint endomorphisms of
`QuadraticMap.polarBilin Q` is built from. -/
theorem lie_ι_mem_range_ι_of_mem_quadraticLieSubalgebra {x : CliffordAlgebra Q}
    (hx : x ∈ quadraticLieSubalgebra Q) (m : M) : ⁅x, ι Q m⁆ ∈ LinearMap.range (ι Q) := by
  have key : (quadraticLieSubalgebra Q).toSubmodule ≤
      { carrier := {y : CliffordAlgebra Q | ∀ m : M, ⁅y, ι Q m⁆ ∈ LinearMap.range (ι Q)}
        add_mem' := fun hy hz m => by rw [add_lie]; exact Submodule.add_mem _ (hy m) (hz m)
        zero_mem' := fun m => by rw [zero_lie]; exact Submodule.zero_mem _
        smul_mem' := fun r _ hy m => by
          rw [smul_lie]; exact Submodule.smul_mem _ r (hy m) } :=
    quadraticLieSubalgebra_toSubmodule_le Q fun a b m =>
      ⟨_, (cliffordBivector_lie_ι Q a b m).symm⟩
  exact key hx m

end CommRing

end CliffordAlgebra

end TauCeti
