/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The adjoint action of a Lie algebra carrying an invariant bilinear form

A bilinear form `B` on a Lie algebra `L` is *invariant* when `B ⁅x, y⁆ z = -B y ⁅x, z⁆`
(`LinearMap.BilinForm.lieInvariant`). Read with `x` fixed, that equation says exactly that the
endomorphism `ad x` is skew-adjoint for `B`: invariance of a form and skew-adjointness of the
adjoint action are the same statement, transposed. So a Lie algebra with an invariant form maps to
the Lie algebra of skew-adjoint endomorphisms of that form, by `x ↦ ad x`, and the map is a
homomorphism because `ad` already is.

This file builds that homomorphism, `TauCeti.LieAlgebra.adSkewAdjoint`, against
`skewAdjointLieSubalgebra` — Mathlib's `𝔰𝔬` of a bilinear form — and identifies the kernel of its
polar-form specialization `TauCeti.LieAlgebra.adjointSO` with the centre. The two names differ only
in their codomain: `adSkewAdjoint` lands in the skew-adjoint endomorphisms of `B` itself, while
`adjointSO`, the roadmap-pinned map, lands in those of the polar form. The form the latter targets
is not `B`
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

* `TauCeti.LieAlgebra.adSkewAdjoint`: the adjoint action of a Lie algebra carrying an invariant
  bilinear form `B`, as a Lie algebra homomorphism into the skew-adjoint endomorphisms of `B`.
* `TauCeti.LieAlgebra.adjointSO`: the same map read into the skew-adjoint endomorphisms of the
  polar form.
* `TauCeti.LieAlgebra.killingQuadraticForm`: the Killing form read as a quadratic form.

## Main results

* `TauCeti.LieAlgebra.ad_mem_skewAdjointSubmodule`: invariance of a form is skew-adjointness of the
  adjoint action.
* `TauCeti.LieAlgebra.ker_adSkewAdjoint`: the kernel of `adSkewAdjoint` is the centre, so the map is
  injective exactly when the centre is trivial
  (`TauCeti.LieAlgebra.adSkewAdjoint_injective_iff`); the same for the polar-form and Killing
  specializations (`TauCeti.LieAlgebra.ker_adjointSO`, `TauCeti.LieAlgebra.ker_killingAdjointSO`).
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

The polar form and nondegeneracy of the Killing quadratic form are the general facts
`LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip` and
`LinearMap.BilinForm.Nondegenerate.toQuadraticMap` of
`TauCeti/LinearAlgebra/QuadraticForm/Radical.lean` applied to the Killing form, which is symmetric;
nothing in either argument is about the Killing form.

The stability of invariance under flipping and addition is a statement about a form on any Lie
module `M` over `L`, the generality in which Mathlib defines `lieInvariant`, and is stated that way
here; only from `ad_mem_skewAdjointSubmodule` on, where the adjoint action enters, is the module
`L` itself.
-/

public section

open LinearMap (BilinForm)

namespace TauCeti.LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section Invariant

variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] {B C : BilinForm R M}

omit [LieAlgebra R L]

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

/-- The polar form of the quadratic form `y ↦ B y y` of an invariant `B` is again invariant: it is
`B + B.flip`, and both summands are. -/
theorem lieInvariant_polarBilin (hB : B.lieInvariant L) :
    LinearMap.BilinForm.lieInvariant L
      (QuadraticMap.polarBilin (LinearMap.BilinMap.toQuadraticMap B)) := by
  rw [LinearMap.BilinMap.polarBilin_toQuadraticMap]
  exact lieInvariant_add hB (lieInvariant_flip hB)

end Invariant

section SkewAdjoint

variable {B : BilinForm R L}

/-- **Invariance is skew-adjointness of the adjoint action.** The invariance equation
`B ⁅x, y⁆ z = -B y ⁅x, z⁆`, read with `x` held fixed, says that `ad x` is skew-adjoint for `B`. -/
theorem ad_mem_skewAdjointSubmodule (hB : B.lieInvariant L) (x : L) :
    _root_.LieAlgebra.ad R L x ∈ B.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  simp only [Pi.neg_apply, _root_.LieAlgebra.ad_apply, map_neg]
  exact hB x y z

end SkewAdjoint

section AdjointSO

/-- **The adjoint homomorphism** `ad : L →ₗ⁅R⁆ 𝔰𝔬(L, B)` of a Lie algebra carrying an invariant
bilinear form `B`: `ad x` is skew-adjoint for `B`, and `ad` is a Lie algebra homomorphism. -/
def adSkewAdjoint (B : BilinForm R L) (hB : B.lieInvariant L) :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra B where
  toFun x := ⟨_root_.LieAlgebra.ad R L x, ad_mem_skewAdjointSubmodule hB x⟩
  map_add' x y := by ext z; simp
  map_smul' r x := by ext z; simp
  map_lie' {x y} := by ext z; simp

/-- `adSkewAdjoint` is `ad` with its codomain restricted: as an endomorphism of `L` it is `ad x`. -/
@[simp]
theorem coe_adSkewAdjoint (B : BilinForm R L) (hB : B.lieInvariant L) (x : L) :
    (adSkewAdjoint B hB x : Module.End R L) = _root_.LieAlgebra.ad R L x := (rfl)

/-- The kernel of the adjoint homomorphism is the centre, since `adSkewAdjoint` is `ad` with its
codomain restricted. -/
@[simp]
theorem ker_adSkewAdjoint (B : BilinForm R L) (hB : B.lieInvariant L) :
    (adSkewAdjoint B hB).ker = _root_.LieAlgebra.center R L := by
  rw [← _root_.LieAlgebra.self_module_ker_eq_center,
    ← _root_.LieAlgebra.ad_ker_eq_self_module_ker]
  ext x
  simp only [LieHom.mem_ker, ← ZeroMemClass.coe_eq_zero, coe_adSkewAdjoint]

/-- The adjoint homomorphism is injective exactly when the centre of `L` is trivial. -/
theorem adSkewAdjoint_injective_iff (B : BilinForm R L) (hB : B.lieInvariant L) :
    Function.Injective (adSkewAdjoint B hB) ↔ _root_.LieAlgebra.center R L = ⊥ := by
  rw [← LieHom.ker_eq_bot, ker_adSkewAdjoint]

/-- The adjoint homomorphism read into the skew-adjoint endomorphisms of the *polar* form of
`x ↦ B x x`, which is `B + B.flip`, and is `2 • B` for symmetric `B`. Skew-adjointness for `B`
implies skew-adjointness for the polar form, the converse needing `2` to be cancellable; the polar
form is what the Clifford algebra of `B` sees. -/
def adjointSO (B : BilinForm R L) (hB : B.lieInvariant L) :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra
      (QuadraticMap.polarBilin (LinearMap.BilinMap.toQuadraticMap B)) :=
  adSkewAdjoint _ (lieInvariant_polarBilin hB)

variable (B : BilinForm R L) (hB : B.lieInvariant L)

/-- The polar-form specialization is again `ad` with its codomain restricted. -/
@[simp]
theorem coe_adjointSO (x : L) :
    (adjointSO B hB x : Module.End R L) = _root_.LieAlgebra.ad R L x :=
  coe_adSkewAdjoint _ (lieInvariant_polarBilin hB) x

/-- The polar-form specialization acts by the bracket. This is the equation the roadmap pins
`adjointSO` by; it is not `@[simp]`, since `coe_adjointSO` together with `LieAlgebra.ad_apply`
already rewrites the left-hand side. -/
theorem adjointSO_apply (x y : L) : (adjointSO B hB x : Module.End R L) y = ⁅x, y⁆ := by
  rw [coe_adjointSO, _root_.LieAlgebra.ad_apply]

/-- The kernel of the adjoint homomorphism is the centre, since `adjointSO` is `ad` with its
codomain restricted. -/
@[simp]
theorem ker_adjointSO : (adjointSO B hB).ker = _root_.LieAlgebra.center R L :=
  ker_adSkewAdjoint _ (lieInvariant_polarBilin hB)

/-- The adjoint homomorphism is injective exactly when the centre of `L` is trivial. -/
theorem adjointSO_injective_iff :
    Function.Injective (adjointSO B hB) ↔ _root_.LieAlgebra.center R L = ⊥ :=
  adSkewAdjoint_injective_iff _ (lieInvariant_polarBilin hB)

end AdjointSO

section Killing

variable (R L)

/-- **The Killing quadratic form** `x ↦ κ(x, x)` of a Lie algebra. This is the form whose Clifford
algebra carries Kostant's isotypic left-regular module; it is nondegenerate whenever `L` is
Killing-semisimple and `2` is invertible in `R` (`killingQuadraticForm_nondegenerate`). -/
noncomputable def killingQuadraticForm : QuadraticForm R L :=
  LinearMap.BilinMap.toQuadraticMap (killingForm R L)

/-- The Killing quadratic form evaluates at `x` to `κ(x, x)`. This is the equation the roadmap pins
`killingQuadraticForm` by. -/
@[simp]
theorem killingQuadraticForm_apply (x : L) :
    killingQuadraticForm R L x = killingForm R L x x :=
  LinearMap.BilinMap.toQuadraticMap_apply _ x

/-- The polar form of the Killing quadratic form is `2 • κ`: here the symmetry of the Killing form
does the work, collapsing `κ + κ.flip`. -/
@[simp]
theorem polarBilin_killingQuadraticForm :
    QuadraticMap.polarBilin (killingQuadraticForm R L) = (2 : R) • killingForm R L := by
  rw [killingQuadraticForm]
  exact LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip (LieModule.traceForm_flip R L L)

/-- The Killing quadratic form is nondegenerate for a Killing-semisimple Lie algebra over a ring in
which `2` is invertible. Both hypotheses are needed: `IsKilling` is nondegeneracy of `κ` itself, and
without an invertible `2` the polar form of a quadratic form is a weaker invariant than the form. -/
theorem killingQuadraticForm_nondegenerate [Invertible (2 : R)] [_root_.LieAlgebra.IsKilling R L] :
    (killingQuadraticForm R L).Nondegenerate := by
  rw [killingQuadraticForm]
  exact LinearMap.BilinForm.Nondegenerate.toQuadraticMap
    (_root_.LieAlgebra.IsKilling.killingForm_nondegenerate R L) (LieModule.traceForm_flip R L L)

/-- The adjoint homomorphism of a Lie algebra into the skew-adjoint endomorphisms of the polar form
`2 • κ` of its Killing quadratic form (`polarBilin_killingQuadraticForm`). This is the homomorphism
whose composite with the quadratic realization inside `Cliff(L, κ)` is the adjoint quadratic lift of
Kostant's theorem. -/
noncomputable def killingAdjointSO :
    L →ₗ⁅R⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin (killingQuadraticForm R L)) :=
  adjointSO (killingForm R L) (LieModule.traceForm_lieInvariant R L L)

/-- The Killing specialization is again `ad` with its codomain restricted. -/
@[simp]
theorem coe_killingAdjointSO (x : L) :
    (killingAdjointSO R L x : Module.End R L) = _root_.LieAlgebra.ad R L x :=
  coe_adjointSO (killingForm R L) (LieModule.traceForm_lieInvariant R L L) x

/-- The kernel of the Killing adjoint homomorphism is the centre. -/
@[simp]
theorem ker_killingAdjointSO :
    (killingAdjointSO R L).ker = _root_.LieAlgebra.center R L :=
  ker_adjointSO (killingForm R L) (LieModule.traceForm_lieInvariant R L L)

/-- The Killing adjoint homomorphism is injective exactly when the centre of `L` is trivial. -/
theorem killingAdjointSO_injective_iff :
    Function.Injective (killingAdjointSO R L) ↔ _root_.LieAlgebra.center R L = ⊥ :=
  adjointSO_injective_iff (killingForm R L) (LieModule.traceForm_lieInvariant R L L)

end Killing

end TauCeti.LieAlgebra
