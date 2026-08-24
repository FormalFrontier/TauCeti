/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The left-regular representation of a Lie map into an associative algebra

Let `q : L →ₗ⁅R⁆ A` be a Lie algebra map from `L` into an associative `R`-algebra `A`, the latter
bracketed by its ring commutator. Left multiplication by the image of `q` makes `A` itself a
representation of `L`:

`x • a = q x * a`.

This is the *left-regular* action along `q`, and it is a different `L`-module from the inner
derivation action `x • a = ⁅q x, a⁆` that `LieAlgebra.ad` supplies; the two differ by right
multiplication (`LieHom.ad_apply_eq_leftRegularRep_sub_mulRight`), and only the left-regular one
has the left ideals of `A` among its submodules. Kostant's isotypy theorem is a statement about
the left-regular action of a semisimple Lie algebra on the Clifford algebra of its Killing form,
so this file supplies the general construction that specialization needs.

Because the module structure it defines competes with the self-module structure of `A` as a Lie
ring, the action is packaged as a homomorphism `L →ₗ⁅R⁆ Module.End R A` rather than as an
instance: a consumer installs the associated `LieRingModule` where it wants it, with
`LieRingModule.compLieHom`.

## Main definitions

* `LieHom.leftRegularRep`: the left-regular representation `L →ₗ⁅R⁆ Module.End R A` along `q`.

## Main results

* `LieHom.leftRegularRep_apply`: it acts by left multiplication.
* `LieHom.leftRegularRep_injective_iff`: it is faithful exactly when `q` is injective, because
  left multiplication determines the multiplier.
* `LieHom.leftRegularRep_comp_mulRight`: right multiplications are intertwiners of the
  left-regular representation; this is the commutant that makes the isotypy arguments run.
* `LieHom.leftRegularRep_mem_of_mem`: every left ideal of `A` is invariant.
* `LieHom.ad_apply_eq_leftRegularRep_sub_mulRight`: the inner derivation action is the difference
  of the left-regular action and right multiplication.

## References

This is the general construction behind the "Kostant's setting, packaged" target of Layer 9 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`; see
`TauCeti/LinearAlgebra/CliffordAlgebra/Quadratic/Lie/LeftRegular.lean` for that specialization.

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
-/

public section

universe u v w

namespace LieHom

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} {L : Type v} {A : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]

/-- **The left-regular representation along a Lie map into an associative algebra.** The Lie
algebra `L` acts on `A` by left multiplication by the image of `q`, which is a Lie action because
`q` turns the bracket of `L` into the ring commutator of `A`. -/
def leftRegularRep (q : L →ₗ⁅R⁆ A) : L →ₗ⁅R⁆ Module.End R A :=
  ((Algebra.lmul R A : A →ₐ[R] Module.End R A) : A →ₗ⁅R⁆ Module.End R A).comp q

/-- **The action formula.** `x` acts on `a` by left multiplication by `q x`. -/
@[simp, grind =]
theorem leftRegularRep_apply (q : L →ₗ⁅R⁆ A) (x : L) (a : A) :
    leftRegularRep q x a = q x * a :=
  (rfl)

/-- The endomorphism by which `x` acts is `LinearMap.mulLeft R (q x)`, which is how the
left-multiplication API of an associative algebra reaches the left-regular representation. -/
theorem leftRegularRep_eq_mulLeft (q : L →ₗ⁅R⁆ A) (x : L) :
    leftRegularRep q x = LinearMap.mulLeft R (q x) :=
  (rfl)

/-- **The left-regular representation is faithful exactly when `q` is injective.** It is the
composite of `q` with `Algebra.lmul`, and left multiplication determines the multiplier
(`Algebra.lmul_injective`), so no information is lost in passing to left multiplications. -/
theorem leftRegularRep_injective_iff (q : L →ₗ⁅R⁆ A) :
    Function.Injective (leftRegularRep q) ↔ Function.Injective q :=
  Algebra.lmul_injective.of_comp_iff q

/-- **Right multiplication intertwines the left-regular representation with itself.** This is
associativity of `A`, read as the statement that the right multiplications lie in the commutant of
the image of `leftRegularRep q`. -/
theorem leftRegularRep_comp_mulRight (q : L →ₗ⁅R⁆ A) (x : L) (b : A) :
    (leftRegularRep q x).comp (LinearMap.mulRight R b) =
      (LinearMap.mulRight R b).comp (leftRegularRep q x) := by
  rw [leftRegularRep_eq_mulLeft, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  exact LinearMap.commute_mulLeft_right (R := R) (q x) b

/-- **Left ideals are invariant** under the left-regular representation: the action is by left
multiplication, which is exactly what a left ideal absorbs. -/
theorem leftRegularRep_mem_of_mem (q : L →ₗ⁅R⁆ A) (I : Submodule A A) (x : L) {a : A}
    (ha : a ∈ I) : leftRegularRep q x a ∈ I := by
  rw [leftRegularRep_apply, ← smul_eq_mul]
  exact I.smul_mem _ ha

/-- **The inner derivation action is the left-regular action minus right multiplication.** The two
`L`-module structures on `A` that `q` produces are therefore genuinely different; only the
left-regular one is built here. -/
theorem ad_apply_eq_leftRegularRep_sub_mulRight (q : L →ₗ⁅R⁆ A) (x : L) :
    LieAlgebra.ad R A (q x) = leftRegularRep q x - LinearMap.mulRight R (q x) := by
  rw [leftRegularRep_eq_mulLeft, LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply]

end LieHom
