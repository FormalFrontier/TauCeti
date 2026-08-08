/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The group of self-diffeomorphisms

Mathlib's `Diffeomorph I I' M M' n` is the type of `Cⁿ` diffeomorphisms between two manifolds,
with composition (`Diffeomorph.trans`), inverse (`Diffeomorph.symm`), and the identity
(`Diffeomorph.refl`) already in place. When the source and target coincide these assemble into a
group: this file equips the self-diffeomorphisms `M ≃ₘ^n⟮I, I⟯ M` with `One`, `Mul`, and `Inv`
instances and proves the `Group` axioms, exactly as Mathlib does for `Equiv.Perm`
(`Mathlib/Algebra/Group/End.lean`). The multiplication is `f * g = g.trans f`, so that `f * g`
acts as the function composition `f ∘ g`, matching the `Equiv.Perm` convention.

This is the group object the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology") asks for as its first deliverable: "The **group** `Diff(M) := M ≃ₘ^∞⟮I, I⟯ M` under
composition (the `Group` instance is routine from the existing `Diffeomorph` composition and
inverse)." It is the underlying group of the topological group `Diff(M)` whose homotopy type the
Smale conjecture `[Kir97, Problem 4.34]` is about; the C^∞ topology making it a topological group is
a separate, later layer-3 deliverable, so this file stops at the bare group structure. The
construction works for every smoothness exponent `n`, with `n = ∞` the case named by the roadmap.

## Main definitions

* `TauCeti.Diff I M n`: notation/abbreviation for the group `M ≃ₘ^n⟮I, I⟯ M` of `Cⁿ`
  self-diffeomorphisms of `M`.
* the `One`, `Mul`, `Inv`, and `Group` instances on `M ≃ₘ^n⟮I, I⟯ M`.
* `TauCeti.Diffeomorph.toPerm`: the forgetful group homomorphism to the underlying permutation
  group `Equiv.Perm M`, which is injective.
* `TauCeti.Diffeomorph.toHomeomorphHom`: the forgetful group homomorphism to the underlying
  homeomorphism group, which is injective.

## Main results

* `TauCeti.Diffeomorph.mul_apply` / `one_apply` / `inv_apply` and the `coe_*` companions: the group
  operations act by composition, the identity, and the inverse diffeomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Diffeomorph

/-- The identity diffeomorphism is the unit of the self-diffeomorphism group. -/
instance instOne : One (M ≃ₘ^n⟮I, I⟯ M) where one := _root_.Diffeomorph.refl I M n

/-- Multiplication of self-diffeomorphisms is composition: `f * g` follows `g` then `f`, so that it
acts as `f ∘ g`, matching the `Equiv.Perm` convention. -/
instance instMul : Mul (M ≃ₘ^n⟮I, I⟯ M) where mul f g := g.trans f

/-- The inverse in the self-diffeomorphism group is the inverse diffeomorphism. -/
instance instInv : Inv (M ≃ₘ^n⟮I, I⟯ M) where inv f := f.symm

/-- Composition of diffeomorphisms is associative. -/
theorem trans_assoc {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {H' : Type*} [TopologicalSpace H'] {G : Type*} [TopologicalSpace G]
    {G' : Type*} [TopologicalSpace G'] {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
    {J' : ModelWithCorners 𝕜 F' G'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
    (f : M ≃ₘ^n⟮I, I'⟯ M') (g : M' ≃ₘ^n⟮I', J⟯ N) (h : N ≃ₘ^n⟮J, J'⟯ N') :
    (f.trans g).trans h = f.trans (g.trans h) :=
  _root_.Diffeomorph.ext fun _ => rfl

/-- The `Cⁿ` self-diffeomorphisms of `M` form a group under composition, with multiplication
acting as function composition. -/
instance instGroup : Group (M ≃ₘ^n⟮I, I⟯ M) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := _root_.Diffeomorph.trans_refl
  mul_one := _root_.Diffeomorph.refl_trans
  inv_mul_cancel := _root_.Diffeomorph.self_trans_symm

/-- The unit of the self-diffeomorphism group is the identity diffeomorphism. -/
theorem one_def : (1 : M ≃ₘ^n⟮I, I⟯ M) = _root_.Diffeomorph.refl I M n := rfl

/-- Multiplication in the self-diffeomorphism group is `Diffeomorph.trans` in composition order. -/
theorem mul_def (f g : M ≃ₘ^n⟮I, I⟯ M) : f * g = g.trans f := rfl

/-- Inversion in the self-diffeomorphism group is the inverse diffeomorphism. -/
theorem inv_def (f : M ≃ₘ^n⟮I, I⟯ M) : f⁻¹ = f.symm := rfl

/-- The unit self-diffeomorphism coerces to the identity function. -/
@[simp]
theorem coe_one : ⇑(1 : M ≃ₘ^n⟮I, I⟯ M) = id := rfl

/-- Multiplication of self-diffeomorphisms coerces to function composition. -/
@[simp]
theorem coe_mul (f g : M ≃ₘ^n⟮I, I⟯ M) : ⇑(f * g) = f ∘ g := rfl

/-- The inverse self-diffeomorphism coerces to the inverse diffeomorphism. -/
@[simp]
theorem coe_inv (f : M ≃ₘ^n⟮I, I⟯ M) : ⇑(f⁻¹) = f.symm := rfl

/-- Multiplication of self-diffeomorphisms acts by applying the right factor, then the left. -/
@[simp]
theorem mul_apply (f g : M ≃ₘ^n⟮I, I⟯ M) (x : M) : (f * g) x = f (g x) := rfl

/-- The unit self-diffeomorphism fixes every point. -/
@[simp]
theorem one_apply (x : M) : (1 : M ≃ₘ^n⟮I, I⟯ M) x = x := rfl

/-- The inverse in the self-diffeomorphism group acts as the inverse diffeomorphism. -/
@[simp]
theorem inv_apply (f : M ≃ₘ^n⟮I, I⟯ M) (x : M) : f⁻¹ x = f.symm x := rfl

/-- The underlying equivalence of the unit self-diffeomorphism is the unit permutation. -/
@[simp]
theorem toEquiv_one : (1 : M ≃ₘ^n⟮I, I⟯ M).toEquiv = 1 := rfl

/-- The underlying equivalence preserves multiplication of self-diffeomorphisms. -/
@[simp]
theorem toEquiv_mul (f g : M ≃ₘ^n⟮I, I⟯ M) : (f * g).toEquiv = f.toEquiv * g.toEquiv := rfl

/-- The underlying equivalence preserves inversion of self-diffeomorphisms. -/
@[simp]
theorem toEquiv_inv (f : M ≃ₘ^n⟮I, I⟯ M) : (f⁻¹).toEquiv = f.toEquiv⁻¹ := rfl

/-- The forgetful group homomorphism from the self-diffeomorphism group to the permutation group of
the underlying set, sending a diffeomorphism to its underlying equivalence. -/
@[expose, simps]
def toPerm : (M ≃ₘ^n⟮I, I⟯ M) →* Equiv.Perm M where
  toFun f := f.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The forgetful homomorphism to permutations is injective. -/
theorem toPerm_injective : Function.Injective (toPerm : (M ≃ₘ^n⟮I, I⟯ M) → Equiv.Perm M) :=
  _root_.Diffeomorph.toEquiv_injective

/-- The forgetful group homomorphism from self-diffeomorphisms to self-homeomorphisms. -/
def toHomeomorphHom : (M ≃ₘ^n⟮I, I⟯ M) →* (M ≃ₜ M) where
  toFun f := f.toHomeomorph
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The forgetful homomorphism to self-homeomorphisms sends a diffeomorphism to its underlying
homeomorphism. -/
@[simp]
theorem toHomeomorphHom_apply (f : M ≃ₘ^n⟮I, I⟯ M) :
    toHomeomorphHom f = f.toHomeomorph := by
  ext x
  rfl

/-- The forgetful homomorphism to self-homeomorphisms is injective. -/
theorem toHomeomorphHom_injective :
    Function.Injective (toHomeomorphHom : (M ≃ₘ^n⟮I, I⟯ M) → (M ≃ₜ M)) := by
  intro f g h
  apply _root_.Diffeomorph.ext
  intro x
  exact congr_fun (congrArg DFunLike.coe h) x

end Diffeomorph

/-- `Diff I M n` is the group of `Cⁿ` self-diffeomorphisms of the manifold `M` modelled on `I`,
under composition. With `n = ∞` this is the group underlying `Diff(M)` of the geometric-topology
roadmap. -/
abbrev Diff (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) : Type _ := M ≃ₘ^n⟮I, I⟯ M

end TauCeti
