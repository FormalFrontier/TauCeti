/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Smooth circle presentations

The geometric presentation of an oriented knot in a manifold is a smooth embedding of the
standard oriented circle into that manifold.  This file specializes `TauCeti.SmoothEmbedding` to
that source, without introducing a privileged `Knot` type, and supplies the two canonical kinds
of reparametrization of the circle:

* rotation by `a : Circle`, which preserves the standard orientation;
* complex conjugation, which reverses it.

The rotations use Mathlib's smooth scalar-action diffeomorphisms for the analytic Lie group
`Circle`; reflection is the smooth inversion map of that group.  The resulting operations on
`TauCeti.SmoothCircleEmbedding` are instances of the general source-reparametrization operation
`TauCeti.SmoothEmbedding.compDiffeomorph`.  In particular, they preserve the image and commute
with transport by a diffeomorphism of the ambient manifold.

This is the first geometric presentation requested by layer 4 of the geometric-topology roadmap.
A parametrization gives the image circle its orientation.  A framing is deliberately not included
here: defining a push-off as a framing requires the tubular-neighbourhood interface from layer 1.
The unoriented presentation is likewise a later quotient by orientation-reversing
reparametrizations, rather than a second bundled embedding type.

## Main definitions

* `TauCeti.circleRotationHom`: the smooth rotation action of `Circle` on itself.
* `TauCeti.circleReflection`: complex conjugation as a self-diffeomorphism of `Circle`.
* `TauCeti.SmoothCircleEmbedding`: smooth embeddings of the standard circle into a manifold.
* `TauCeti.SmoothCircleEmbedding.rotate`: orientation-preserving reparametrization by a rotation.
* `TauCeti.SmoothCircleEmbedding.reverse`: orientation-reversing reparametrization by conjugation.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped Manifold ContDiff

/-- Rotations of the complex unit circle, as smooth self-diffeomorphisms. -/
def circleRotationHom : Circle →* Diff (𝓡 1) Circle ∞ where
  toFun a := _root_.Diffeomorph.smul (𝓡 1) (𝓡 1) ∞ a
  map_one' := _root_.Diffeomorph.ext fun x => one_mul x
  map_mul' a b := _root_.Diffeomorph.ext fun x => mul_assoc a b x

/-- A circle rotation acts by multiplication on the complex unit circle. -/
@[simp]
theorem circleRotationHom_apply_apply (a x : Circle) : circleRotationHom a x = a * x :=
  (rfl)

/-- The homomorphism from circle rotations to circle diffeomorphisms is injective. -/
theorem circleRotationHom_injective : Function.Injective circleRotationHom := by
  intro a b hab
  have h := DFunLike.congr_fun hab 1
  simpa using h

/-- Complex conjugation, as the orientation-reversing smooth self-diffeomorphism of the circle. -/
def circleReflection : Diff (𝓡 1) Circle ∞ :=
  { toEquiv := Equiv.inv Circle
    contMDiff_toFun := contMDiff_inv (𝓡 1) ∞
    contMDiff_invFun := contMDiff_inv (𝓡 1) ∞ }

/-- Reflection of the complex unit circle is inversion. -/
@[simp]
theorem circleReflection_apply (x : Circle) : circleReflection x = x⁻¹ := by
  rfl

/-- Reflection of the circle is an involution. -/
@[simp]
theorem circleReflection_mul_self : circleReflection * circleReflection = 1 := by
  apply _root_.Diffeomorph.ext
  intro x
  simp

/-- Reflection is its own inverse as a circle diffeomorphism. -/
@[simp]
theorem circleReflection_inv : circleReflection⁻¹ = circleReflection := by
  exact inv_eq_of_mul_eq_one_right circleReflection_mul_self

/-- Reflection conjugates rotation by `a` to rotation by `a⁻¹`. -/
@[simp]
theorem circleReflection_mul_circleRotationHom (a : Circle) :
    circleReflection * circleRotationHom a = circleRotationHom (a⁻¹) * circleReflection := by
  apply _root_.Diffeomorph.ext
  intro x
  simp only [Diffeomorph.mul_apply, circleReflection_apply, circleRotationHom_apply_apply,
    mul_inv_rev, mul_comm]

/-- A smooth circle presentation in a manifold modelled on `I` is a smooth embedding of the
standard complex unit circle into the manifold.  Its parametrization orients the image circle. -/
abbrev SmoothCircleEmbedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  SmoothEmbedding (𝓡 1) I ∞ Circle M

namespace SmoothCircleEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Reparametrize a smooth circle embedding by the orientation-preserving rotation `x ↦ a * x`.
This changes the marked parametrization but not the oriented image. -/
def rotate (f : SmoothCircleEmbedding I M) (a : Circle) : SmoothCircleEmbedding I M :=
  f.compDiffeomorph (circleRotationHom a)

/-- Rotating a smooth circle embedding precomposes its underlying map with multiplication on the
circle. -/
@[simp]
theorem rotate_apply (f : SmoothCircleEmbedding I M) (a x : Circle) :
    f.rotate a x = f (a * x) := by
  rw [rotate.eq_def, SmoothEmbedding.compDiffeomorph_apply, circleRotationHom_apply_apply]

/-- Rotation by `1` does not change a smooth circle embedding. -/
@[simp]
theorem rotate_one (f : SmoothCircleEmbedding I M) : f.rotate 1 = f := by
  apply SmoothEmbedding.ext
  intro x
  simp

/-- Successive rotations multiply their parameters. -/
@[simp]
theorem rotate_rotate (f : SmoothCircleEmbedding I M) (a b : Circle) :
    (f.rotate b).rotate a = f.rotate (b * a) := by
  apply SmoothEmbedding.ext
  intro x
  simp [mul_assoc]

/-- Rotation does not change the image of a smooth circle embedding. -/
@[simp]
theorem range_rotate (f : SmoothCircleEmbedding I M) (a : Circle) :
    range (f.rotate a) = range f :=
  SmoothEmbedding.range_compDiffeomorph f (circleRotationHom a)

/-- Circle rotation acts on smooth circle embeddings by reparametrization. -/
instance instMulActionCircle : MulAction Circle (SmoothCircleEmbedding I M) where
  smul a f := f.rotate a
  one_smul := rotate_one
  mul_smul a b f :=
    (congrArg (fun c => f.rotate c) (mul_comm a b)).trans (rotate_rotate f a b).symm

/-- The circle action on smooth circle embeddings is rotation of the source. -/
@[simp]
theorem smul_def (a : Circle) (f : SmoothCircleEmbedding I M) : a • f = f.rotate a :=
  rfl

/-- Reverse the orientation of a smooth circle presentation by precomposing with complex
conjugation. -/
def reverse (f : SmoothCircleEmbedding I M) : SmoothCircleEmbedding I M :=
  f.compDiffeomorph circleReflection

/-- Reversing a smooth circle presentation sends the parameter `x` to `x⁻¹`. -/
@[simp]
theorem reverse_apply (f : SmoothCircleEmbedding I M) (x : Circle) :
    f.reverse x = f x⁻¹ := by
  rw [reverse.eq_def, SmoothEmbedding.compDiffeomorph_apply, circleReflection_apply]

/-- Reversing a smooth circle presentation twice gives the original presentation. -/
@[simp]
theorem reverse_reverse (f : SmoothCircleEmbedding I M) : f.reverse.reverse = f := by
  apply SmoothEmbedding.ext
  intro x
  simp

/-- Orientation reversal does not change the image of a smooth circle embedding. -/
@[simp]
theorem range_reverse (f : SmoothCircleEmbedding I M) : range f.reverse = range f :=
  SmoothEmbedding.range_compDiffeomorph f circleReflection

/-- Reversing after rotation by `a` is rotating the reversed presentation by `a⁻¹`. -/
@[simp]
theorem reverse_rotate (f : SmoothCircleEmbedding I M) (a : Circle) :
    (f.rotate a).reverse = f.reverse.rotate (a⁻¹) := by
  apply SmoothEmbedding.ext
  intro x
  simp [mul_comm]

section Ambient

variable [IsManifold I ∞ M]

/-- Ambient diffeomorphisms commute with rotation of a smooth circle presentation. -/
instance instSMulCommClassDiff :
    SMulCommClass (Diff I M ∞) Circle (SmoothCircleEmbedding I M) :=
  ⟨fun e a f => by
    apply SmoothEmbedding.ext
    intro x
    simp⟩

/-- Ambient diffeomorphisms commute with orientation reversal of a smooth circle presentation. -/
@[simp]
theorem reverse_smul (e : Diff I M ∞) (f : SmoothCircleEmbedding I M) :
    reverse (SmoothEmbedding.transDiffeomorph f e) = e • f.reverse := by
  simpa only [SmoothEmbedding.smul_def, reverse] using
    (SmoothEmbedding.transDiffeomorph_compDiffeomorph f circleReflection e).symm

end Ambient

end SmoothCircleEmbedding

end TauCeti
