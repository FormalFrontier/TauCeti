/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.JordanDecomposition
public import TauCeti.LinearAlgebra.JordanChevalley.Semisimple

/-!
# Semisimple points of an affine group

Let `H` be a Hopf algebra over a field `k` and let `K / k` be a field extension. A `K`-valued
point `g : H →ₐ[k] K` acts on the scalar extension of every finite-dimensional `H`-comodule.
This file calls `g` **semisimple** when every one of those linear automorphisms is semisimple.

For the commutative coordinate Hopf algebra of an affine group scheme, taking `K` to be an
algebraic closure of `k` gives the representation-theoretic definition of a geometric semisimple
element. The definition is tied directly to the multiplicative Jordan decomposition: over a
perfect field, a point is semisimple exactly when the natural semisimple factors of all its
finite-comodule actions recover its original action.

Semisimple points contain the identity and are closed under inverses and natural powers. Products
of commuting semisimple points are semisimple over a perfect field, and semisimplicity is invariant
under conjugation. Each statement follows from the corresponding result for general linear groups
because every comodule point action is a group homomorphism.

## Main declarations

* `TauCeti.HopfAlgebra.IsSemisimple`: a point acts semisimply in every finite-dimensional
  comodule.
* `TauCeti.HopfAlgebra.isSemisimple_iff_endOfPoint`: the equivalent formulation using the
  underlying comodule action endomorphisms.
* `TauCeti.HopfAlgebra.IsSemisimple.inv`, `.mul`, and `.pow`: closure under inversion, commuting
  products, and natural powers.
* `TauCeti.HopfAlgebra.isSemisimple_mul_mul_inv_iff`: invariance under conjugation.
* `TauCeti.HopfAlgebra.isSemisimple_iff_fgPointSemisimplePartNatIso_eq`: the intrinsic
  characterization by the Tannakian semisimple-factor automorphism.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the intrinsic semisimple-element predicate needed by Layer 4, "Jordan
decomposition", of the ReductiveGroups roadmap. It uses the representation--comodule dictionary
built in Layer 1.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v x

variable {k : Type u} {H : Type v} {K : Type x}
variable [Field k] [Semiring H] [_root_.HopfAlgebra k H] [Field K] [Algebra k K]

/-- A field-valued point of a Hopf algebra is semisimple when it acts by a semisimple linear
automorphism on the scalar extension of every finite-dimensional comodule.

When `H` is the commutative coordinate Hopf algebra of an affine group over `k` and `K` is an
algebraic closure, this is the standard representation-theoretic definition of a geometric
semisimple element. -/
def IsSemisimple (g : WithConv (H →ₐ[k] K)) : Prop :=
  ∀ M : FGComoduleCat.{u, v, u} k H,
    GeneralLinearGroup.IsSemisimple
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))

/-- Unfolding the definition of a semisimple point gives semisimplicity of its action on every
finite comodule. -/
theorem isSemisimple_iff (g : WithConv (H →ₐ[k] K)) :
    IsSemisimple g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        GeneralLinearGroup.IsSemisimple
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :=
  Iff.rfl

/-- A point is semisimple exactly when each underlying point-action endomorphism is
semisimple. -/
theorem isSemisimple_iff_endOfPoint (g : WithConv (H →ₐ[k] K)) :
    IsSemisimple g ↔
      ∀ M : FGComoduleCat.{u, v, u} k H,
        Module.End.IsSemisimple (Comodule.endOfPoint M g.ofConv) := by
  rw [isSemisimple_iff]
  constructor
  · intro h M
    have hM := (GeneralLinearGroup.isSemisimple_def _).mp (h M)
    -- Expose the point-action endomorphism beneath the general-linear-group coercion so its
    -- characteristic equation lemma applies.
    change Module.End.IsSemisimple (Comodule.pointsAction M g).toLinearMap at hM
    rw [Comodule.pointsAction_toLinearMap] at hM
    exact hM
  · intro h M
    rw [GeneralLinearGroup.isSemisimple_def]
    have hM := h M
    rw [← Comodule.pointsAction_toLinearMap M g] at hM
    exact hM

/-- The identity point is semisimple. -/
@[simp]
theorem isSemisimple_one :
    IsSemisimple (1 : WithConv (H →ₐ[k] K)) := by
  intro M
  rw [map_one]
  exact GeneralLinearGroup.isSemisimple_one

/-- The inverse of a semisimple point is semisimple. -/
theorem IsSemisimple.inv {g : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimple g) : IsSemisimple g⁻¹ := by
  intro M
  have haction :
      LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g⁻¹) =
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))⁻¹ := by
    rw [map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
  rw [haction]
  exact (hg M).inv

/-- A point is semisimple if and only if its inverse is semisimple. -/
@[simp]
theorem isSemisimple_inv_iff (g : WithConv (H →ₐ[k] K)) :
    IsSemisimple g⁻¹ ↔ IsSemisimple g := by
  constructor
  · intro hg
    have := hg.inv
    rwa [inv_inv] at this
  · exact IsSemisimple.inv

/-- Every natural power of a semisimple point is semisimple. -/
theorem IsSemisimple.pow {g : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimple g) (n : ℕ) : IsSemisimple (g ^ n) := by
  intro M
  rw [map_pow]
  rw [show LinearMap.GeneralLinearGroup.ofLinearEquiv
      (Comodule.pointsAction M g ^ n) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) ^ n by
      exact map_pow (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm _ n]
  exact (hg M).pow n

/-- Semisimplicity of points is invariant under conjugation. -/
@[simp]
theorem isSemisimple_mul_mul_inv_iff (g h : WithConv (H →ₐ[k] K)) :
    IsSemisimple (h * g * h⁻¹) ↔ IsSemisimple g := by
  constructor
  · intro hg M
    have hM := hg M
    simp only [map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv] at hM
    exact (GeneralLinearGroup.isSemisimple_mul_mul_inv_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mp hM
  · intro hg M
    simp only [map_mul, map_inv, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
    exact (GeneralLinearGroup.isSemisimple_mul_mul_inv_iff
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M h))).mpr (hg M)

section PerfectField

variable [PerfectField K]

/-- The product of two commuting semisimple points is semisimple. -/
theorem IsSemisimple.mul {g h : WithConv (H →ₐ[k] K)}
    (hg : IsSemisimple g) (hh : IsSemisimple h)
    (hcomm : Commute g h) : IsSemisimple (g * h) := by
  intro M
  rw [map_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]
  apply (hg M).mul (hh M)
  have hactionComm := hcomm.map (Comodule.pointsAction M)
  rw [commute_iff_eq] at hactionComm ⊢
  rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
    ← LinearMap.GeneralLinearGroup.ofLinearEquiv_mul, hactionComm]

/-- A point is semisimple exactly when the natural semisimple factors of all its
finite-comodule actions recover its original point action. -/
theorem isSemisimple_iff_fgPointSemisimplePartNatIso_eq
    (g : WithConv (H →ₐ[k] K)) :
    IsSemisimple g ↔
      Tannaka.fgPointSemisimplePartNatIso.{u, v, x, u} k H K g =
        Tannaka.fgPointNatIsoHom.{u, v, x, u} k H K g := by
  constructor
  · intro hg
    apply Aut.ext
    apply NatTrans.ext
    funext (M : FGComoduleCat.{u, v, u} k H)
    rw [Tannaka.fgPointSemisimplePartNatIso_hom_app,
      Tannaka.fgPointNatIsoHom_hom_app,
      GeneralLinearGroup.semisimplePart_eq_self (hg M)]
    have haction :
        (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction M g)).toLinearEquiv = Comodule.pointsAction M g :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (K ⊗[k] M)).apply_symm_apply
        (Comodule.pointsAction M g)
    rw [haction]
  · intro h M
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
      have hequiv :
          (GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction M g))).toLinearEquiv =
            Comodule.pointsAction M g :=
        LinearEquiv.toLinearMap_injective hlinear
      calc
        GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) =
            LinearMap.GeneralLinearGroup.ofLinearEquiv
              (GeneralLinearGroup.semisimplePart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv
                  (Comodule.pointsAction M g))).toLinearEquiv :=
          ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (K ⊗[k] M)).symm_apply_apply _).symm
        _ = LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :=
          congrArg LinearMap.GeneralLinearGroup.ofLinearEquiv hequiv
    rw [← hfactor]
    exact GeneralLinearGroup.isSemisimple_semisimplePart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))

end PerfectField

end HopfAlgebra

end TauCeti
