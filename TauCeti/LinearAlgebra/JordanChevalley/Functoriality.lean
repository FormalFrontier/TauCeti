/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Functoriality of the multiplicative Jordan decomposition

The multiplicative Jordan--Chevalley decomposition of a linear automorphism does not depend on
the coordinates used to describe it.  A linear equivalence `e : V ≃ₗ[K] W` transports an
automorphism by conjugation.  This file proves that semisimplicity and unipotence are invariant
under this transport and that both canonical Jordan factors commute with it.

This is the first functoriality step for the Jordan decomposition requested in Layer 4 of the
ReductiveGroups roadmap.  In particular, it makes the general-linear decomposition invariant
under a change of basis, as required before it can be transported through a faithful
representation of an affine algebraic group.

## Main declarations

* `TauCeti.GeneralLinearGroup.isSemisimple_congrLinearEquiv_iff`: semisimplicity is invariant
  under linear conjugation.
* `TauCeti.GeneralLinearGroup.isUnipotent_congrLinearEquiv_iff`: unipotence is invariant under
  linear conjugation.
* `TauCeti.GeneralLinearGroup.jordanDecomposition_congrLinearEquiv`: the canonical pair is
  equivariant under linear conjugation.
* `TauCeti.GeneralLinearGroup.semisimplePart_congrLinearEquiv` and
  `TauCeti.GeneralLinearGroup.unipotentPart_congrLinearEquiv`: the two factor formulas.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

open Module

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}

section Predicates

variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Semisimplicity of a linear automorphism is invariant under transport by a linear
equivalence. -/
@[simp]
theorem isSemisimple_congrLinearEquiv_iff
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    IsSemisimple (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (e.symm.trans (g.toLinearEquiv.trans e))) ↔ IsSemisimple g := by
  rw [isSemisimple_def, isSemisimple_def]
  symm
  apply LinearEquiv.isSemisimple_iff (e := e)
  ext x
  simp

/-- Unipotence of a linear automorphism is invariant under transport by a linear equivalence. -/
@[simp]
theorem isUnipotent_congrLinearEquiv_iff
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    IsUnipotent (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (e.symm.trans (g.toLinearEquiv.trans e))) ↔ IsUnipotent g := by
  rw [isUnipotent_def, isUnipotent_def]
  rw [← LinearMap.GeneralLinearGroup.congrLinearEquiv_apply e g]
  have hmap :
      LinearEquiv.conjRingEquiv e ((g : End K V) - 1) =
        ((LinearMap.GeneralLinearGroup.congrLinearEquiv e g :
          GeneralLinearGroup K W) : End K W) - 1 := by
    ext x
    simp
  rw [← hmap]
  exact IsNilpotent.map_iff (LinearEquiv.conjRingEquiv e).injective

end Predicates

section PerfectField

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V]

/-- The multiplicative Jordan--Chevalley decomposition commutes with transport by a linear
equivalence. -/
theorem jordanDecomposition_congrLinearEquiv
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    letI := FiniteDimensional.of_surjective e.toLinearMap e.surjective
    jordanDecomposition (LinearMap.GeneralLinearGroup.congrLinearEquiv e g) =
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e (semisimplePart g),
        LinearMap.GeneralLinearGroup.congrLinearEquiv e (unipotentPart g)) := by
  let _ := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  symm
  apply (eq_jordanDecomposition_iff
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e g) _ _).2
  refine ⟨(isSemisimple_congrLinearEquiv_iff e _).2 (isSemisimple_semisimplePart g),
    (isUnipotent_congrLinearEquiv_iff e _).2 (isUnipotent_unipotentPart g), ?_, ?_⟩
  · exact (commute_semisimplePart_unipotentPart g).map
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom
  · rw [← map_mul, semisimplePart_mul_unipotentPart]

/-- The semisimple factor of the multiplicative Jordan decomposition commutes with transport by
a linear equivalence. -/
@[simp]
theorem semisimplePart_congrLinearEquiv
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    letI := FiniteDimensional.of_surjective e.toLinearMap e.surjective
    semisimplePart (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (e.symm.trans (g.toLinearEquiv.trans e))) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv e (semisimplePart g) := by
  let _ := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  rw [← LinearMap.GeneralLinearGroup.congrLinearEquiv_apply e g]
  rw [semisimplePart_def (LinearMap.GeneralLinearGroup.congrLinearEquiv e g)]
  exact congrArg Prod.fst (jordanDecomposition_congrLinearEquiv e g)

/-- The unipotent factor of the multiplicative Jordan decomposition commutes with transport by a
linear equivalence. -/
@[simp]
theorem unipotentPart_congrLinearEquiv
    (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V) :
    letI := FiniteDimensional.of_surjective e.toLinearMap e.surjective
    unipotentPart (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (e.symm.trans (g.toLinearEquiv.trans e))) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv e (unipotentPart g) := by
  let _ := FiniteDimensional.of_surjective e.toLinearMap e.surjective
  rw [← LinearMap.GeneralLinearGroup.congrLinearEquiv_apply e g]
  rw [unipotentPart_def (LinearMap.GeneralLinearGroup.congrLinearEquiv e g)]
  exact congrArg Prod.snd (jordanDecomposition_congrLinearEquiv e g)

end PerfectField

end GeneralLinearGroup

end TauCeti
