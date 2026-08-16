/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate

/-!
# Chevalley relations for represented Kostant root subgroups

A Kostant-stable integral lattice and a finite basis represent each divided-power root action by
an affine group-scheme morphism `xᵢ : 𝔾ₐ → GLₙ`. This file connects those represented morphisms
to the Chevalley relations already proved for the underlying divided-power actions.

If two distinguished root vectors commute, their represented root-subgroup values commute. If

```text
⁅eᵢ, eⱼ⁆ = c eₖ,   ⁅eᵢ, eₖ⁆ = 0,   ⁅eⱼ, eₖ⁆ = 0,
```

then the canonical commutator relation is

```text
⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u).
```

The statements are also provided in any finite integral basis. Their scheme-valued counterparts
are in `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.SchemeRelations`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupPoints_of_lie_eq`:
  the canonical commutator form for the divided-power actions.
* `TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix`: the commuting relation
  in an integral basis.
* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupMatrix_of_lie_eq`:
  the class-two relation in an integral basis.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {A : Type*} [CommRing A]

section Points

/-- **The canonical class-two Chevalley commutator relation for Kostant root-subgroup
actions.** If the third root vector is the commutator of the first two and commutes with both,
then the element commutator is exactly the third root-subgroup value. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g z : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hz : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) z) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk z := by
  rw [commutatorElement_def,
    kostantRootSubgroupPoints_conj_of_lie_eq e h ρ M hM hij hik hjk hi hj hk f g z hz]
  rw [(commute_kostantRootSubgroupPoints e h ρ M hM hjk hj hk g z).eq]
  simp

end Points

section Matrices

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

/-- Represented Kostant root subgroups attached to commuting root vectors commute in every
integral basis. -/
theorem commute_kostantRootSubgroupMatrix {i j : I} (hij : ⁅e i, e j⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Commute (kostantRootSubgroupMatrix e h ρ M hM i hi b f)
      (kostantRootSubgroupMatrix e h ρ M hM j hj b g) := by
  rw [kostantRootSubgroupMatrix_def, kostantRootSubgroupMatrix_def]
  exact (commute_kostantRootSubgroupPoints e h ρ M hM hij hi hj f g).map
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)

/-- **The class-two Chevalley commutator relation in an integral basis.** The matrix commutator
of the first two represented root subgroups is the third at parameter `c t u`. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_eq {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (f g z : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hz : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) z) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi b f,
        kostantRootSubgroupMatrix e h ρ M hM j hj b g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk b z := by
  rw [kostantRootSubgroupMatrix_def, kostantRootSubgroupMatrix_def,
    kostantRootSubgroupMatrix_def]
  simpa only [MonoidHom.comp_apply, map_commutatorElement] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
      (commutatorElement_kostantRootSubgroupPoints_of_lie_eq
        e h ρ M hM hij hik hjk hi hj hk f g z hz)

end Matrices

end TauCeti.UniversalEnvelopingAlgebra
