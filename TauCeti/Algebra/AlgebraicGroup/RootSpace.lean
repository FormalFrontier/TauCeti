/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# Root spaces of a split pair

Let `G = Spec H` be an affine group scheme over `R` whose augmentation cotangent space is finite
projective, so that its Lie algebra is the single `R`-module
`Module.Dual R (Bialgebra.CotangentSpace R H)` carrying the adjoint comodule of
`TauCeti.Algebra.AlgebraicGroup.Tangent.Representation`. A split torus in `G` is a homomorphism
`T = D(M) → G` of affine group schemes, that is, a morphism `π : H →ₐc[R] R[M]` of coordinate
bialgebras, where `M` is the character lattice written multiplicatively.

Restricting the adjoint representation along `π` decomposes the Lie algebra into weight
submodules, indexed by the characters of `T`. This file names them: `adjointWeightSpace π α` is
`𝔤_α`, `roots π` is the set of nonzero characters with a nonzero weight submodule, and the Lie
algebra is the direct sum of `𝔤_1` and the `𝔤_α` for `α` a root. A point of `T` acts on `𝔤_α`
by the value of the character `α`, which is what makes `α` a root rather than a bare index.

Nothing here asserts that `π` is a closed immersion, that `T` is a maximal torus, that `G` is
reductive, or that `roots π` is a root system; those all need hypotheses this file does not carry.
What is fixed here is the object those statements will be about.

## Main definitions

* `TauCeti.Derivation.adjointWeightSpace`: the weight submodule `𝔤_α` of the Lie algebra of `G`
  under a split torus.
* `TauCeti.Derivation.roots`: the set of roots of the pair, the nonzero characters whose weight
  submodule is nonzero.

## Main results

* `TauCeti.Derivation.isInternal_adjointWeightSpace`: **the Lie algebra of `G` is the internal
  direct sum of its weight submodules under a split torus.**
* `TauCeti.Derivation.sup_iSup_adjointWeightSpace_eq_top`: the zero weight submodule together with
  the root submodules exhaust the Lie algebra.
* `TauCeti.Derivation.finite_roots`: **the set of roots is finite.**
* `TauCeti.Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace`: a point of the torus acts on
  `𝔤_α` by the value of `α` at that point.

## Roadmap

Layer 7 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the root datum
`(X*(T), Φ, X_*(T), Φ^∨)` of a split pair `(G, T)`, taking the split case first. The character and
cocharacter lattices with their pairing are already in
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`; this file supplies `Φ`, the remaining piece of the
root datum that is read off the group rather than the torus. Layer 9's split reductive group
schemes over `ℤ` take the split maximal torus as part of their data and are defined by conditions
on exactly this decomposition, and milestone `L0` of `TauCetiRoadmap/CFSGStatement/README.md`
consumes those pinned Chevalley--Demazure groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 (the roots of a split reductive group).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* B. Conrad, *Reductive Group Schemes* (SGA3 exposition), §3.2.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace Derivation

attribute [local instance] Classical.decEq

variable {R : Type*} {H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {M : Type*} [CommGroup M]

/-- The weight submodule `𝔤_α` of the Lie algebra of `G = Spec H` under the split torus
`T = D(M) → G` with coordinate morphism `π`: the part of the Lie algebra on which `T` acts through
the character `α`. -/
noncomputable def adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) (α : M) :
    Submodule R (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M) α

/-- **The Lie algebra of `G` is the internal direct sum of its weight submodules under a split
torus.** -/
theorem isInternal_adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) :
    DirectSum.IsInternal (adjointWeightSpace π) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.isInternal_weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M)

/-- The weight submodules span the Lie algebra. -/
theorem iSup_adjointWeightSpace_eq_top (π : H →ₐc[R] MonoidAlgebra R M) :
    ⨆ α : M, adjointWeightSpace π α = ⊤ :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.iSup_weightSpace_eq_top (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M)

/-- The weight submodules are independent. -/
theorem iSupIndep_adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) :
    iSupIndep (adjointWeightSpace π) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.iSupIndep_weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M)

/-- The roots of the split pair `(G, T)`: the nontrivial characters of `T` whose weight submodule
in the Lie algebra of `G` is nonzero. -/
def roots (π : H →ₐc[R] MonoidAlgebra R M) : Set M :=
  {α | α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥}

theorem mem_roots {π : H →ₐc[R] MonoidAlgebra R M} {α : M} :
    α ∈ roots π ↔ α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥ :=
  Iff.rfl

theorem ne_one_of_mem_roots {π : H →ₐc[R] MonoidAlgebra R M} {α : M} (hα : α ∈ roots π) :
    α ≠ 1 :=
  hα.1

theorem adjointWeightSpace_ne_bot_of_mem_roots {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    (hα : α ∈ roots π) : adjointWeightSpace π α ≠ ⊥ :=
  hα.2

/-- Off the roots and the trivial character the weight submodule vanishes. -/
theorem adjointWeightSpace_eq_bot_of_notMem_roots {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    (hα : α ≠ 1) (h : α ∉ roots π) : adjointWeightSpace π α = ⊥ := by
  by_contra hbot
  exact h ⟨hα, hbot⟩

/-- **The set of roots is finite.** The Lie algebra is finitely generated, so only finitely many
weight submodules are nonzero. -/
theorem finite_roots (π : H →ₐc[R] MonoidAlgebra R M) : (roots π).Finite :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  Set.Finite.subset
    (DiagonalizableGroup.finite_setOf_weightSpace_ne_bot
      (Module.Dual R (Bialgebra.CotangentSpace R H)) (π : H →ₗc[R] MonoidAlgebra R M))
    fun _ hα => hα.2

/-- **The Lie algebra is spanned by the zero weight submodule together with the root
submodules.** -/
theorem sup_iSup_adjointWeightSpace_eq_top (π : H →ₐc[R] MonoidAlgebra R M) :
    (adjointWeightSpace π 1 ⊔ ⨆ α ∈ roots π, adjointWeightSpace π α) = ⊤ := by
  refine top_unique ?_
  rw [← iSup_adjointWeightSpace_eq_top π]
  refine iSup_le fun α => ?_
  by_cases hα : α = 1
  · subst hα
    exact le_sup_left
  · by_cases hbot : adjointWeightSpace π α = ⊥
    · rw [hbot]
      exact bot_le
    · exact le_sup_of_le_right (le_iSup₂ (f := fun β (_ : β ∈ roots π) => adjointWeightSpace π β)
        α ⟨hα, hbot⟩)

/-- **A point of the torus acts on the root submodule `𝔤_α` by the value of the character `α`.**
This is the property that makes `α` a root of `(G, T)` and not merely an index of the
decomposition. -/
theorem endOfPoint_tmul_of_mem_adjointWeightSpace {A : Type*} [CommRing A] [Algebra R A]
    (π : H →ₐc[R] MonoidAlgebra R M) (f : MonoidAlgebra R M →ₐ[R] A) (a : A) {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)} (hx : x ∈ adjointWeightSpace π α) :
    letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
      adjointComodule (R := R) (H := H)
    Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H))
        (f.comp (π : H →ₐ[R] MonoidAlgebra R M)) (a ⊗ₜ[R] x) =
      (a * f (MonoidAlgebra.single α (1 : R))) ⊗ₜ[R] x :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace
    (Module.Dual R (Bialgebra.CotangentSpace R H)) π f a hx

end Derivation

end TauCeti
