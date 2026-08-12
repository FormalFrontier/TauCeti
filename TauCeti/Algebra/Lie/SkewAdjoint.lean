/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# The adjoint action of a Lie algebra carrying an invariant bilinear form

A bilinear form `B` on a Lie algebra `L` is *invariant* when `B ⁅x, y⁆ z = -B y ⁅x, z⁆`
(`LinearMap.BilinForm.lieInvariant`). Read with `x` fixed, that equation says exactly that the
endomorphism `ad x` is skew-adjoint for `B`: invariance of a form and skew-adjointness of the
adjoint action are the same statement, transposed. So a Lie algebra with an invariant form maps to
the Lie algebra of skew-adjoint endomorphisms of that form, by `x ↦ ad x`, and the map is a
homomorphism because `ad` already is.

This file builds that homomorphism, `TauCeti.LieAlgebra.adSO`, against `skewAdjointLieSubalgebra` —
Mathlib's `𝔰𝔬` of a bilinear form — and identifies the kernel of its polar-form specialization
`TauCeti.LieAlgebra.adjointSO` with the centre. The form that specialization targets is not `B`
itself but the polar form of the quadratic form `x ↦ B x x`, which is `B + B.flip`; that is the
shape a Clifford algebra consumes, since the Clifford relation `ι v * ι v = Q v` polarizes to
`polar Q`. For symmetric `B` the polar form is `2 • B`; skew-adjointness for `B` always implies
skew-adjointness for `2 • B`, and the two conditions agree when `2` is invertible in `R`, but not in
general. Stating the codomain against `QuadraticMap.polarBilin` avoids a factor of two travelling
with every later use.

The motivating instance is the Killing form of a Lie algebra, whose quadratic form is
`TauCeti.LieAlgebra.killingQuadraticForm`. It is invariant (`LieModule.traceForm_lieInvariant`) and
symmetric, so `ad` maps `L` into the skew-adjoint endomorphisms of the polar form `2 • κ`; when `L`
is Killing-semisimple and `2` is invertible
the form is moreover nondegenerate, which is the hypothesis under which the skew-adjoint
endomorphisms are the quadratic elements of the Clifford algebra `Cliff(L, κ)`
(`TauCeti.CliffordAlgebra.soEquivQuadratic`). Composing the two is the adjoint quadratic lift
`L → Cliff(L, κ)` whose left-regular action is the subject of Kostant's isotypy theorem; that
composite is not built here.

## Main definitions

* `TauCeti.LieAlgebra.adSO`: the adjoint action of a Lie algebra carrying an invariant bilinear
  form `B`, as a Lie algebra homomorphism into the skew-adjoint endomorphisms of `B`.
* `TauCeti.LieAlgebra.adjointSO`: the same map read into the skew-adjoint endomorphisms of the
  polar form.
* `TauCeti.LieAlgebra.killingQuadraticForm`: the Killing form read as a quadratic form.

## Main results

* `TauCeti.LieAlgebra.ad_mem_skewAdjointSubmodule`: invariance of a form is skew-adjointness of the
  adjoint action.
* `TauCeti.LieAlgebra.ker_adjointSO`: the kernel of `adjointSO` is the centre, so `adjointSO` is
  injective exactly when the centre is trivial (`TauCeti.LieAlgebra.adjointSO_injective_iff`).
* `TauCeti.LieAlgebra.polarBilin_killingQuadraticForm`: the polar form of the Killing quadratic
  form is `2 • killingForm`.
* `TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate`: over a ring in which `2` is invertible,
  the Killing quadratic form of a Killing-semisimple Lie algebra is nondegenerate.

## Implementation notes

The pinned signature in the roadmap's `Suggested.lean` carries a symmetry hypothesis on `B` and
works over a field. Neither is used: invariance of `B` already forces invariance of `B.flip`
(`TauCeti.LieAlgebra.lieInvariant_flip`), hence of the polar form `B + B.flip`, and the argument is
a rearrangement of the invariance equation valid over any commutative ring. Symmetry is used only
where it genuinely bites, in `polarBilin_killingQuadraticForm`, which is stated for the Killing form
rather than hypothesised. Carrying an unused hypothesis on a `def` would in any case be rejected by
the `unusedArguments` linter.
-/

public section

open LinearMap (BilinForm)

namespace TauCeti.LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section Invariant

variable {B C : BilinForm R L}

/-- The flip of an invariant bilinear form is invariant: invariance is the equation
`B ⁅x, y⁆ z = -B y ⁅x, z⁆`, and reading it with the roles of `y` and `z` exchanged is the same
equation for the flip. -/
theorem lieInvariant_flip (hB : B.lieInvariant L) :
    LinearMap.BilinForm.lieInvariant L (LinearMap.flip B) := fun x y z => by
  simp only [LinearMap.flip_apply]
  rw [hB x z y, neg_neg]

/-- Invariance is preserved by sums, the two invariance equations adding termwise. -/
theorem lieInvariant_add (hB : B.lieInvariant L) (hC : C.lieInvariant L) :
    (B + C).lieInvariant L := fun x y z => by
  simp only [LinearMap.add_apply, hB x y z, hC x y z, neg_add]

/-- The polar form of the quadratic form `x ↦ B x x` of an invariant `B` is again invariant: it is
`B + B.flip`, and both summands are. -/
theorem lieInvariant_polarBilin (hB : B.lieInvariant L) :
    LinearMap.BilinForm.lieInvariant L
      (QuadraticMap.polarBilin (LinearMap.BilinMap.toQuadraticMap B)) := by
  rw [LinearMap.BilinMap.polarBilin_toQuadraticMap]
  exact lieInvariant_add hB (lieInvariant_flip hB)

/-- **Invariance is skew-adjointness of the adjoint action.** The invariance equation
`B ⁅x, y⁆ z = -B y ⁅x, z⁆`, read with `x` held fixed, says that `ad x` is skew-adjoint for `B`. -/
theorem ad_mem_skewAdjointSubmodule (hB : B.lieInvariant L) (x : L) :
    _root_.LieAlgebra.ad R L x ∈ B.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  simp only [Pi.neg_apply, _root_.LieAlgebra.ad_apply, map_neg]
  exact hB x y z

end Invariant

section AdjointSO

/-- **The adjoint homomorphism** `ad : L →ₗ⁅R⁆ 𝔰𝔬(L, B)` of a Lie algebra carrying an invariant
bilinear form `B`: `ad x` is skew-adjoint for `B`, and `ad` is a Lie algebra homomorphism. -/
def adSO (B : BilinForm R L) (hB : B.lieInvariant L) :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra B where
  toFun x := ⟨_root_.LieAlgebra.ad R L x, ad_mem_skewAdjointSubmodule hB x⟩
  map_add' x y := by ext z; simp
  map_smul' r x := by ext z; simp
  map_lie' {x y} := by ext z; simp

@[simp]
theorem adSO_apply (B : BilinForm R L) (hB : B.lieInvariant L) (x y : L) :
    (adSO B hB x : Module.End R L) y = ⁅x, y⁆ := (rfl)

/-- The adjoint homomorphism read into the skew-adjoint endomorphisms of the *polar* form of
`x ↦ B x x`, which is `B + B.flip`, and is `2 • B` for symmetric `B`. Skew-adjointness for `B`
implies skew-adjointness for the polar form, the converse needing `2` to be cancellable; the polar
form is what the Clifford algebra of `B` sees. -/
def adjointSO (B : BilinForm R L) (hB : B.lieInvariant L) :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra
      (QuadraticMap.polarBilin (LinearMap.BilinMap.toQuadraticMap B)) :=
  adSO _ (lieInvariant_polarBilin hB)

variable (B : BilinForm R L) (hB : B.lieInvariant L)

@[simp]
theorem adjointSO_apply (x y : L) : (adjointSO B hB x : Module.End R L) y = ⁅x, y⁆ :=
  adSO_apply _ (lieInvariant_polarBilin hB) x y

/-- The kernel of the adjoint homomorphism is the centre, since `adjointSO` is `ad` with its
codomain restricted. -/
theorem ker_adjointSO : (adjointSO B hB).ker = _root_.LieAlgebra.center R L := by
  rw [← _root_.LieAlgebra.self_module_ker_eq_center,
    ← _root_.LieAlgebra.ad_ker_eq_self_module_ker]
  ext x
  have h : (adjointSO B hB x : Module.End R L) = _root_.LieAlgebra.ad R L x := by ext y; simp
  simp only [LieHom.mem_ker, ← ZeroMemClass.coe_eq_zero, h]

/-- The adjoint homomorphism is injective exactly when the centre of `L` is trivial. -/
theorem adjointSO_injective_iff :
    Function.Injective (adjointSO B hB) ↔ _root_.LieAlgebra.center R L = ⊥ := by
  rw [← LieHom.ker_eq_bot, ker_adjointSO]

end AdjointSO

section Killing

variable (R L)

/-- **The Killing quadratic form** `x ↦ κ(x, x)` of a Lie algebra. This is the form whose Clifford
algebra carries Kostant's isotypic left-regular module; it is nondegenerate whenever `L` is
Killing-semisimple and `2` is invertible in `R` (`killingQuadraticForm_nondegenerate`). -/
noncomputable def killingQuadraticForm : QuadraticForm R L :=
  LinearMap.BilinMap.toQuadraticMap (killingForm R L)

@[simp]
theorem killingQuadraticForm_apply (x : L) :
    killingQuadraticForm R L x = killingForm R L x x :=
  LinearMap.BilinMap.toQuadraticMap_apply _ x

/-- The polar form of the Killing quadratic form is `2 • κ`: here the symmetry of the Killing form
does the work, collapsing `κ + κ.flip`. -/
@[simp]
theorem polarBilin_killingQuadraticForm :
    QuadraticMap.polarBilin (killingQuadraticForm R L) = (2 : R) • killingForm R L := by
  rw [killingQuadraticForm, LinearMap.BilinMap.polarBilin_toQuadraticMap,
    LieModule.traceForm_flip, two_smul]

/-- The Killing quadratic form is nondegenerate for a Killing-semisimple Lie algebra over a ring in
which `2` is invertible. Both hypotheses are needed: `IsKilling` is nondegeneracy of `κ` itself, and
without an invertible `2` the polar form of a quadratic form is a weaker invariant than the form. -/
theorem killingQuadraticForm_nondegenerate [Invertible (2 : R)] [_root_.LieAlgebra.IsKilling R L] :
    (killingQuadraticForm R L).Nondegenerate := by
  have h2 : IsUnit (2 : R) := isUnit_of_invertible 2
  obtain ⟨hl, hr⟩ := _root_.LieAlgebra.IsKilling.killingForm_nondegenerate R L
  rw [← QuadraticMap.nondegenerate_polar_iff, polarBilin_killingQuadraticForm]
  refine ⟨fun x hx => hl x fun y => ?_, fun y hy => hr y fun x => ?_⟩
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hx y
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hy x

/-- The adjoint homomorphism of a Lie algebra into the skew-adjoint endomorphisms of the polar form
`2 • κ` of its Killing quadratic form (`polarBilin_killingQuadraticForm`). This is the homomorphism
whose composite with the quadratic realization inside `Cliff(L, κ)` is the adjoint quadratic lift of
Kostant's theorem. -/
noncomputable def killingAdjointSO :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin (killingQuadraticForm R L)) :=
  adjointSO (killingForm R L) (LieModule.traceForm_lieInvariant R L L)

@[simp]
theorem killingAdjointSO_apply (x y : L) :
    (killingAdjointSO R L x : Module.End R L) y = ⁅x, y⁆ :=
  adjointSO_apply (killingForm R L) (LieModule.traceForm_lieInvariant R L L) x y

end Killing

end TauCeti.LieAlgebra
