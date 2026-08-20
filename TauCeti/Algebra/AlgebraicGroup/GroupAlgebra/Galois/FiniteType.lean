/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Invariant.Basic
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants

/-!
# Finiteness of descended group algebras

Let `L/k` be a finite Galois extension and let a finitely generated abelian group `M` carry an
integral representation of `Gal(L/k)`. The simultaneous semilinear action on
`L[Multiplicative M]` has an invariant `k`-subalgebra. This file proves that the split group
algebra is finite as a module over that invariant algebra and, by the Artin--Tate lemma, that the
invariant algebra is finite type over `k`.

Finite type is necessary before the invariant algebra can serve as the coordinate algebra of the
torus descended from the split torus `D(M)`. The remaining Galois-descent step is to identify its
scalar extension to `L` with `L[Multiplicative M]` and transport the Hopf structure through that
identification.

## Main declarations

* `TauCeti.GaloisDescent.groupAlgebraInvariants_isIntegral`: the split group algebra is integral
  over its invariant algebra.
* `TauCeti.GaloisDescent.groupAlgebraInvariants_moduleFinite`: for a finitely generated exponent
  group, the split group algebra is module-finite over its invariant algebra.
* `TauCeti.GaloisDescent.instFiniteTypeGroupAlgebraInvariants`: the invariant algebra is finite
  type over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 7.8
  (Artin--Tate).

This advances Layer 4, "Tori: split and non-split", of the ReductiveGroups roadmap. It supplies
the finite-type part of the inverse Galois-descent construction from an integral Galois lattice.
-/

public section

open scoped TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

universe u_k u_L u_M

variable {k : Type u_k} {L : Type u_L} {M : Type u_M}
variable [Field k] [Field L] [Algebra k L] [AddCommGroup M]

/-- The split group algebra is integral over the invariant algebra when its automorphism group
is finite. -/
theorem groupAlgebraInvariants_isIntegral
    [Finite (L ≃ₐ[k] L)] (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Algebra.IsIntegral (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) := by
  let _ : SMul (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    ⟨fun σ x ↦ groupAlgebraAction rho σ x⟩
  let _ : MulSemiringAction (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    MulSemiringAction.compHom _ (groupAlgebraAction rho)
  have action_apply (σ : L ≃ₐ[k] L) (x : MonoidAlgebra L (Multiplicative M)) :
      σ • x = groupAlgebraAction rho σ x := rfl
  let _ : SMulCommClass (L ≃ₐ[k] L) (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) :=
    ⟨fun σ x y ↦ by
      simpa only [Algebra.smul_def, action_apply, map_mul, Subalgebra.algebraMap_def,
        Algebra.algebraMap_self, RingHom.id_apply] using
        congrArg (· * groupAlgebraAction rho σ y)
          ((mem_groupAlgebraInvariants_iff rho x).mp x.property σ)⟩
  let _ : Algebra.IsInvariant (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) (L ≃ₐ[k] L) :=
    { isInvariant := fun x hx ↦ by
        refine ⟨⟨x, (mem_groupAlgebraInvariants_iff rho x).mpr ?_⟩, rfl⟩
        intro σ
        simpa only [action_apply] using hx σ }
  exact Algebra.IsInvariant.isIntegral
    (groupAlgebraInvariants rho) (MonoidAlgebra L (Multiplicative M)) (L ≃ₐ[k] L)

/-- If `L/k` is finite and the exponent group is finitely generated, the split group
algebra is finite as a module over its invariant algebra. -/
theorem groupAlgebraInvariants_moduleFinite
    [FiniteDimensional k L] [Module.Finite ℤ M]
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Module.Finite (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) := by
  let _ : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  let _ : Group.FG (Multiplicative M) := AddGroup.fg_iff_mul_fg.mp inferInstance
  let _ : Algebra.FiniteType k (MonoidAlgebra L (Multiplicative M)) :=
    Algebra.FiniteType.trans (R := k) (S := L)
      (Module.Finite.finiteType L) inferInstance
  let _ : Algebra.FiniteType (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (groupAlgebraInvariants rho) (MonoidAlgebra L (Multiplicative M))
  let _ : Algebra.IsIntegral (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) :=
    groupAlgebraInvariants_isIntegral rho
  exact Algebra.IsIntegral.finite

/-- The invariant algebra of the automorphism action on the group algebra of a finitely generated
abelian group is finite type over the ground field. -/
noncomputable instance instFiniteTypeGroupAlgebraInvariants
    [FiniteDimensional k L] [Module.Finite ℤ M]
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Algebra.FiniteType k (groupAlgebraInvariants rho) := by
  let _ : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  let _ : Group.FG (Multiplicative M) := AddGroup.fg_iff_mul_fg.mp inferInstance
  let _ : Algebra.FiniteType k (MonoidAlgebra L (Multiplicative M)) :=
    Algebra.FiniteType.trans (R := k) (S := L)
      (Module.Finite.finiteType L) inferInstance
  let _ : Module.Finite (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) :=
    groupAlgebraInvariants_moduleFinite rho
  exact ⟨fg_of_fg_of_fg (A := k) (B := groupAlgebraInvariants rho)
    (C := MonoidAlgebra L (Multiplicative M))
      Algebra.FiniteType.out Module.Finite.fg_top (fun _ _ h ↦ Subtype.ext h)⟩

end TauCeti.GaloisDescent
