/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# The universal property of profinite completion

This file restates the categorical universal property of Mathlib's profinite completion for
unbundled groups and continuous monoid homomorphisms. It also proves that the canonical map from
a finite group to its profinite completion is bijective.

The correspondence is obtained from `ProfiniteGrp.ProfiniteCompletion.homEquiv`; the finite-group
result uses its canonical map's dense range and Mathlib's residual-finiteness criterion.
-/

public section

namespace TauCeti

open CategoryTheory

namespace ProfiniteCompletion

universe u v

variable (G : Type u) [Group G]
variable (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [TotallyDisconnectedSpace P]

/-- Continuous homomorphisms from the profinite completion of `G` to a profinite group `P`
correspond to abstract homomorphisms from `G` to `P`. -/
noncomputable def continuousMonoidHomEquiv :
    (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) ≃ (G →* P) :=
  (ConcreteCategory.homEquiv (C := ProfiniteGrp)).symm |>.trans
    (ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of G) (ProfiniteGrp.of P)) |>.trans
      (ConcreteCategory.homEquiv (C := GrpCat))

/-- The unbundled profinite-completion correspondence restricts a continuous homomorphism along
the canonical map. -/
@[simp]
theorem continuousMonoidHomEquiv_apply
    (f : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* P) (g : G) :
    continuousMonoidHomEquiv G P f g =
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) := by
  -- The forward direction of `ProfiniteGrp.ProfiniteCompletion.homEquiv` is inverse to
  -- `ProfiniteGrp.ProfiniteCompletion.lift`, so Mathlib's `lift_eta` computes it.
  have key : ∀ F : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) ⟶
        ProfiniteGrp.of P,
      ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of G) (ProfiniteGrp.of P) F =
        ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G) ≫ (forget₂ _ _).map F := by
    intro F
    have h : ProfiniteGrp.ProfiniteCompletion.lift
        (ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of G) (ProfiniteGrp.of P) F) = F :=
      Equiv.symm_apply_apply
        (ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of G) (ProfiniteGrp.of P)) F
    conv_rhs => rw [← h]
    exact (ProfiniteGrp.ProfiniteCompletion.lift_eta _).symm
  -- The remaining concrete-category plumbing is definitional.
  exact congrArg (fun m : GrpCat.of G ⟶ GrpCat.of P => m.hom g) (key (ConcreteCategory.ofHom f))

/-- The continuous lift of an abstract homomorphism agrees with it on the original group. -/
@[simp]
theorem continuousMonoidHomEquiv_symm_apply_etaFn (f : G →* P) (g : G) :
    (continuousMonoidHomEquiv G P).symm f
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g) = f g := by
  rw [← continuousMonoidHomEquiv_apply, Equiv.apply_symm_apply]

/-- Two continuous homomorphisms from a profinite completion to a Hausdorff topological group
agree if they agree on the canonical dense image of the original group. -/
@[ext]
theorem continuousMonoidHom_ext
    {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* Q}
    (h : ∀ x : G,
      f (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x) =
        g (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) x)) : f = g := by
  apply DFunLike.coe_injective
  exact (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).equalizer
    f.continuous_toFun g.continuous_toFun (funext h)

/-- The canonical map from a finite group to its profinite completion is bijective. -/
theorem etaFn_bijective_of_finite [Finite G] :
    Function.Bijective (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G)) := by
  refine ⟨(ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (G := GrpCat.of G)).2 inferInstance, ?_⟩
  intro x
  have hx : x ∈ closure (Set.range
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G))) := by
    rw [(ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of G)).closure_range]
    exact Set.mem_univ x
  rw [(Set.finite_range _).isClosed.closure_eq] at hx
  exact hx

end ProfiniteCompletion

end TauCeti
