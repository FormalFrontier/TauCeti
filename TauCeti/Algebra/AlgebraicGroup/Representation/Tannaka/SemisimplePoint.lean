/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.JordanDecomposition

/-!
# Tannakian characterization of semisimple points

Let `H` be a Hopf algebra over a commutative semiring `k`, let `K` be a perfect field equipped with
a `k`-algebra structure, and let `g : WithConv (H →ₐ[k] K)` be a `K`-valued point. The natural
automorphism formed from the semisimple factors of the actions of `g` on finitely generated
comodules equals the original point-action automorphism exactly when `g` is semisimple.

## Main declarations

* `TauCeti.HopfAlgebra.isSemisimplePoint_iff_fgPointSemisimplePartNatIso_eq_fgPointNatIsoHom`:
  the intrinsic characterization by the Tannakian semisimple-factor automorphism.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is a representation-theoretic step toward the Jordan decomposition of group elements in
Layer 4 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory LinearMap WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v x

variable {k : Type u} {H : Type v} {K : Type x}
variable [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H] [Field K] [Algebra k K]
  [PerfectField K]

/-- A point is semisimple exactly when the natural semisimple factors of all its
finitely generated comodule actions recover its original point action. -/
theorem isSemisimplePoint_iff_fgPointSemisimplePartNatIso_eq_fgPointNatIsoHom
    (g : WithConv (H →ₐ[k] K)) :
    IsSemisimplePoint g ↔
      Tannaka.fgPointSemisimplePartNatIso.{u, v, x, u} k H K g =
        Tannaka.fgPointNatIsoHom.{u, v, x, u} k H K g := by
  constructor
  · intro hg
    apply Aut.ext
    apply NatTrans.ext
    funext (M : FGComoduleCat.{u, v, u} k H)
    rw [Tannaka.fgPointSemisimplePartNatIso_hom_app,
      Tannaka.fgPointNatIsoHom_hom_app,
      GeneralLinearGroup.semisimplePart_eq_self ((isSemisimplePoint_def g).mp hg M)]
    have haction :
        (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction M g)).toLinearEquiv = Comodule.pointsAction M g :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).apply_symm_apply _
    rw [haction]
  · intro h
    apply (isSemisimplePoint_def g).mpr
    intro M
    have happ := congrArg
      (fun a : Aut (FGComoduleCat.scalarExtensionFunctor.{u, v, u, x} k H K) ↦
        a.hom.app M) h
    rw [Tannaka.fgPointSemisimplePartNatIso_hom_app,
      Tannaka.fgPointNatIsoHom_hom_app] at happ
    rw [cancel_epi] at happ
    rw [cancel_mono] at happ
    have hfactor : GeneralLinearGroup.semisimplePart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) := by
      have hlinear := congrArg SemimoduleCat.Hom.hom happ
      simp only [LinearEquiv.toModuleIsoₛ_hom, SemimoduleCat.hom_ofHom] at hlinear
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).injective
      ext v
      exact LinearMap.congr_fun hlinear v
    have hM : GeneralLinearGroup.IsSemisimple
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) := by
      rw [← hfactor]
      exact GeneralLinearGroup.isSemisimple_semisimplePart _
    exact hM

end HopfAlgebra

end TauCeti
