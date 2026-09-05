/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal

/-!
# Conjugating maximal tori

Conjugation by a rational point is an automorphism of an affine group, so it carries every
maximal torus to another maximal torus. This file states that fact in Hopf coordinates, where a
closed subgroup is represented contravariantly by its defining Hopf ideal.

## Main declaration

* `TauCeti.HopfIdeal.IsMaximalTorus.conjugate`: a conjugate of a maximal torus is maximal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §17.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal.IsMaximalTorus

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H.obj}

/-- A conjugate of a maximal torus by a rational point of the ambient affine group is again a
maximal torus. -/
theorem conjugate (hI : IsMaximalTorus k H.obj I)
    (g : HopfAlgebra.points (R := k) (H := H.obj) (CommAlgCat.of k k)) :
    IsMaximalTorus k H.obj (I.conjugate g) := by
  let e := ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k)
    (CommHopfAlgCat.innerConjugationIso H.obj g)
  have e_hom : e.hom.hom = (CommHopfAlgCat.innerConjugationIso H.obj g).hom := by
    simp only [e, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom]
  have e_bialgHom : FiniteTypeCommHopfAlgCat.toBialgHom e.hom =
      (CommHopfAlgCat.innerConjugationIso H.obj g).hom.hom := by
    exact congrArg (fun f ↦ f.hom) e_hom
  have heq : I.conjugate g =
      I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
    apply HopfIdeal.ext
    intro x
    rw [HopfIdeal.mem_conjugate_iff, HopfIdeal.mem_comapOfSurjective]
    rw [e_bialgHom]
  rw [heq]
  exact hI.comapOfIso e

/-- Conjugation by a rational point preserves and reflects the maximal-torus property. -/
theorem conjugate_iff
    (g : HopfAlgebra.points (R := k) (H := H.obj) (CommAlgCat.of k k)) :
    IsMaximalTorus k H.obj (I.conjugate g) ↔ IsMaximalTorus k H.obj I := by
  constructor
  · intro hI
    have hI' := hI.conjugate g⁻¹
    rwa [HopfIdeal.conjugate_conjugate_inv] at hI'
  · exact fun hI ↦ hI.conjugate g

end TauCeti.HopfIdeal.IsMaximalTorus
