/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Prod

/-!
# Intertwining multiplicative Jordan decompositions

Over a perfect field, every linear map intertwining two automorphisms also intertwines their
canonical semisimple and unipotent factors.  No injectivity or surjectivity assumption on the
linear map is needed.

The proof applies the product automorphism to the graph of the intertwiner.  The graph is invariant
under the product, and the semisimple factor is a polynomial in that product, so the graph is also
invariant under the semisimple factor.  The product decomposition is componentwise, which gives
the desired equality for semisimple factors; the equality for unipotent factors then follows from
`u = s⁻¹g`.

This completes the linear-algebraic functoriality step in Layer 4 of the ReductiveGroups roadmap.
It is the input needed to transport Jordan decompositions through representations of affine
algebraic groups.

## Main declarations

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

universe u v w

section PerfectField

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

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
  have hs_inv :
      f.comp (↑((semisimplePart g)⁻¹) : Module.End K V) =
        (↑((semisimplePart h)⁻¹) : Module.End K W).comp f := by
    apply LinearMap.ext
    intro x
    calc
      f ((↑((semisimplePart g)⁻¹) : Module.End K V) x) =
          (↑((semisimplePart h)⁻¹) : Module.End K W)
            ((semisimplePart h : Module.End K W)
              (f ((↑((semisimplePart g)⁻¹) : Module.End K V) x))) := by
        exact ((semisimplePart h).toLinearEquiv.symm_apply_apply _).symm
      _ = (↑((semisimplePart h)⁻¹) : Module.End K W)
          (f ((semisimplePart g : Module.End K V)
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x))) := by
        exact congrArg (↑((semisimplePart h)⁻¹) : Module.End K W)
          (LinearMap.congr_fun hs
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x)).symm
      _ = (↑((semisimplePart h)⁻¹) : Module.End K W) (f x) := by
        have hxg : (semisimplePart g : Module.End K V)
            ((↑((semisimplePart g)⁻¹) : Module.End K V) x) = x :=
          LinearMap.congr_fun (semisimplePart g).val_inv x
        rw [hxg]
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

end PerfectField

end GeneralLinearGroup

end TauCeti
