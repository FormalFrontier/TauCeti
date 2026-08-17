/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Prod
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Intertwining

/-!
# Functoriality of the multiplicative Jordan decomposition

The multiplicative Jordan--Chevalley decomposition of a linear automorphism does not depend on
the coordinates used to describe it.  A linear equivalence `e : V ≃ₗ[K] W` transports an
automorphism by conjugation.  This file proves that semisimplicity is invariant under this
transport and that both canonical Jordan factors commute with it.  More generally,
every linear map between finite-dimensional modules over a perfect field that intertwines two
automorphisms also intertwines their canonical semisimple and unipotent factors; no injectivity or
surjectivity assumption is needed.

This is the first functoriality step for the Jordan decomposition requested in Layer 4 of the
ReductiveGroups roadmap.  In particular, it makes the general-linear decomposition invariant
under a change of basis, as required before it can be transported through a faithful
representation of an affine algebraic group.

## Main declarations

* `TauCeti.GeneralLinearGroup.isSemisimple_congrLinearEquiv_iff`: semisimplicity is invariant
  under linear conjugation.
* `TauCeti.GeneralLinearGroup.isSemisimple_conj_iff`: semisimplicity is invariant under
  conjugation within the general linear group.
* `TauCeti.GeneralLinearGroup.jordanDecomposition_congrLinearEquiv`: the canonical pair is
  equivariant under linear conjugation.
* `TauCeti.GeneralLinearGroup.semisimplePart_congrLinearEquiv` and
  `TauCeti.GeneralLinearGroup.unipotentPart_congrLinearEquiv`: the two factor formulas.
* `TauCeti.GeneralLinearGroup.comp_semisimplePart_eq_of_comp_eq`: intertwiners commute with
  semisimple factors.
* `TauCeti.GeneralLinearGroup.comp_unipotentPart_eq_of_comp_eq`: intertwiners commute with
  unipotent factors.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap Polynomial

namespace GeneralLinearGroup

open _root_.Module

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

/-- Semisimplicity is invariant under conjugation by a linear automorphism. -/
@[simp]
theorem isSemisimple_conj_iff (g h : GeneralLinearGroup K V) :
    IsSemisimple (h * g * h⁻¹) ↔ IsSemisimple g := by
  have heq : h * g * h⁻¹ =
      LinearMap.GeneralLinearGroup.congrLinearEquiv h.toLinearEquiv g := by
    have hinv : ((h⁻¹ : GeneralLinearGroup K V) : End K V) =
        h.toLinearEquiv.symm.toLinearMap := by
      calc
        _ = (h⁻¹).toLinearEquiv.toLinearMap :=
          (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap _).symm
        _ = h.toLinearEquiv.symm.toLinearMap := congrArg LinearEquiv.toLinearMap
          (LinearMap.GeneralLinearGroup.toLinearEquiv_inv h)
    ext v
    simp only [Units.val_mul, End.mul_apply,
      LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
      LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv]
    rw [LinearMap.congr_fun hinv v]
    simp only [LinearEquiv.coe_toLinearMap]
  rw [heq, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  exact isSemisimple_congrLinearEquiv_iff h.toLinearEquiv g

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

section Intertwining

variable [FiniteDimensional K W]

/-- A linear map intertwining two automorphisms also intertwines their semisimple factors. -/
theorem comp_semisimplePart_eq_of_comp_eq
    (f : V →ₗ[K] W) (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
    (hfg : f.comp (g : Module.End K V) = (h : Module.End K W).comp f) :
    f.comp (semisimplePart g : Module.End K V) =
      (semisimplePart h : Module.End K W).comp f := by
  let gh : GeneralLinearGroup K (V × W) := prodMap g h
  have hgraph : f.graph ≤ f.graph.comap (gh : Module.End K (V × W)) := by
    intro x hx
    -- Unfold `Submodule.comap` membership to the action of the locally named product map.
    change (gh : Module.End K (V × W)) x ∈ f.graph
    rw [LinearMap.mem_graph_iff] at hx ⊢
    rw [coe_prodMap, LinearMap.prodMap_apply, hx]
    exact (LinearMap.congr_fun hfg x.1).symm
  have hs := coe_semisimplePart_mem_adjoin gh
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
  obtain ⟨p, hp⟩ := hs
  apply LinearMap.ext
  intro x
  have hx : (x, f x) ∈ f.graph := by simp
  have hpx : aeval (gh : Module.End K (V × W)) p (x, f x) ∈ f.graph :=
    aeval_apply_smul_mem_of_le_comap hx p _ hgraph
  have hp' : aeval (gh : Module.End K (V × W)) p =
      (semisimplePart gh : Module.End K (V × W)) := hp
  rw [hp'] at hpx
  -- Replace the local name `gh` by its defining product map before using its factor formula.
  change (semisimplePart (prodMap g h) : Module.End K (V × W)) (x, f x) ∈ f.graph at hpx
  rw [semisimplePart_prodMap, LinearMap.mem_graph_iff, coe_prodMap,
    LinearMap.prodMap_apply] at hpx
  exact hpx.symm

/-- A linear map intertwining two automorphisms also intertwines their unipotent factors. -/
theorem comp_unipotentPart_eq_of_comp_eq
    (f : V →ₗ[K] W) (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W)
    (hfg : f.comp (g : Module.End K V) = (h : Module.End K W).comp f) :
    f.comp (unipotentPart g : Module.End K V) =
      (unipotentPart h : Module.End K W).comp f := by
  have hs := comp_semisimplePart_eq_of_comp_eq f g h hfg
  have hs_inv := comp_inv_eq_of_comp_eq f (semisimplePart g) (semisimplePart h) hs
  have hug : unipotentPart g = (semisimplePart g)⁻¹ * g := by
    apply mul_left_cancel (a := semisimplePart g)
    simp
  have huh : unipotentPart h = (semisimplePart h)⁻¹ * h := by
    apply mul_left_cancel (a := semisimplePart h)
    simp
  rw [hug, huh]
  apply LinearMap.ext
  intro x
  -- Expose multiplication of automorphisms as composition of their underlying endomorphisms.
  change f ((↑((semisimplePart g)⁻¹) : Module.End K V) ((g : Module.End K V) x)) =
    (↑((semisimplePart h)⁻¹) : Module.End K W) ((h : Module.End K W) (f x))
  calc
    _ = (↑((semisimplePart h)⁻¹) : Module.End K W)
        (f ((g : Module.End K V) x)) :=
      LinearMap.congr_fun hs_inv ((g : Module.End K V) x)
    _ = _ := congrArg (↑((semisimplePart h)⁻¹) : Module.End K W)
      (LinearMap.congr_fun hfg x)

end Intertwining

end PerfectField

end GeneralLinearGroup

end TauCeti
