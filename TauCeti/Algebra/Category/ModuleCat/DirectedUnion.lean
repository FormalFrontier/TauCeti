/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import TauCeti.LinearAlgebra.Submodule.DirectedUnion

/-!
# Directed unions as colimits of modules

A monotone family of submodules over a directed preorder defines a diagram in `ModuleCat`, with
the submodule inclusions as transition maps. If its supremum is a submodule `T`, the inclusions
into `T` exhibit `ModuleCat.of R T` as the colimit of this diagram.

The universal map is the linear map `TauCeti.Submodule.iSupLift` glued from the legs of an
arbitrary cocone.

## Main declarations

* `TauCeti.ModuleCat.submoduleFunctor`: the diagram associated to a monotone family of submodules.
* `TauCeti.ModuleCat.submoduleCocone`: the inclusion cocone into the supremum submodule.
* `TauCeti.ModuleCat.submoduleCoconeIsColimit`: the inclusion cocone is a colimit.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v x

namespace ModuleCat

variable {R : Type u} {M : Type v} {ι : Type x}
variable [Ring R] [AddCommGroup M] [Module R M]
variable [Preorder ι]

private theorem inclusion_hom_ext {A B : Submodule R M}
    (f g : ModuleCat.of R A ⟶ ModuleCat.of R B)
    (h : ∀ m, ((f m : B) : M) = g m) : f = g := by
  apply ModuleCat.hom_ext
  ext m
  exact h m

/-- A monotone family of submodules, regarded as a diagram in `ModuleCat` whose maps are the
canonical inclusions. -/
noncomputable abbrev submoduleFunctor (K : ι → Submodule R M) (hK : Monotone K) :
    CategoryTheory.Functor ι (ModuleCat.{v} R) where
  obj i := ModuleCat.of R (K i)
  map f := ModuleCat.ofHom (Submodule.inclusion (hK (leOfHom f)))
  map_id i := by
    apply inclusion_hom_ext
    intro m
    rfl
  map_comp f g := by
    apply inclusion_hom_ext
    intro m
    rfl

/-- The cocone from a monotone family of submodules to a submodule equal to their supremum. -/
noncomputable abbrev submoduleCocone (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) : Cocone (submoduleFunctor K hK) :=
  Cocone.mk (ModuleCat.of R T)
    { app := fun i ↦ ModuleCat.ofHom (Submodule.inclusion ((le_iSup K i).trans hT.le))
      naturality := fun _ _ _ ↦ by
        apply inclusion_hom_ext
        intro m
        rfl }

/-- The point of the directed-submodule cocone is the module carried by the supremum. -/
@[simp]
theorem submoduleCocone_pt (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) :
    (submoduleCocone K hK T hT).pt = ModuleCat.of R T :=
  rfl

/-- A leg of the directed-submodule cocone is the corresponding submodule inclusion. -/
@[simp]
theorem submoduleCocone_ι_app (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) (i : ι) :
    (submoduleCocone K hK T hT).ι.app i =
      ModuleCat.ofHom (Submodule.inclusion ((le_iSup K i).trans hT.le)) :=
  rfl

private noncomputable abbrev coconeLinearMap (K : ι → Submodule R M) (hK : Monotone K)
    (s : Cocone (submoduleFunctor K hK)) (i : ι) : K i →ₗ[R] s.pt :=
  (s.ι.app i).hom

private theorem submoduleFunctor_ι_app_eq_comp_inclusion [IsDirectedOrder ι]
    (K : ι → Submodule R M) (hK : Monotone K) (s : Cocone (submoduleFunctor K hK))
    (i j : ι) (hij : K i ≤ K j) :
    coconeLinearMap K hK s i =
      (coconeLinearMap K hK s j).comp (Submodule.inclusion hij) := by
  apply LinearMap.ext
  intro m
  have h_app {a b : ι} (hab : a ≤ b) (x : K a) :
      coconeLinearMap K hK s b (Submodule.inclusion (hK hab) x) =
        coconeLinearMap K hK s a x := by
    have h : (coconeLinearMap K hK s b).comp (Submodule.inclusion (hK hab)) =
        coconeLinearMap K hK s a := by
      have hw := congrArg ModuleCat.Hom.hom (s.w (homOfLE hab))
      simp only [submoduleFunctor, ModuleCat.hom_comp,
        ConcreteCategory.hom_ofHom] at hw
      exact hw
    exact LinearMap.congr_fun h x
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  calc
    coconeLinearMap K hK s i m =
        coconeLinearMap K hK s k (Submodule.inclusion (hK hik) m) := (h_app hik m).symm
    _ = coconeLinearMap K hK s k
        (Submodule.inclusion (hK hjk) (Submodule.inclusion hij m)) := by rfl
    _ = coconeLinearMap K hK s j (Submodule.inclusion hij m) := h_app hjk _

/-- A submodule equal to the supremum of a monotone family over a directed preorder is the
colimit of that family in `ModuleCat`. -/
noncomputable def submoduleCoconeIsColimit [IsDirectedOrder ι]
    (K : ι → Submodule R M) (hK : Monotone K)
    (T : Submodule R M) (hT : ⨆ i, K i = T) : IsColimit (submoduleCocone K hK T hT) where
  desc s := ModuleCat.ofHom (Submodule.iSupLift K hK.directed_le
    (coconeLinearMap K hK s) (submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
    T hT.ge)
  fac s i := by
    apply ModuleCat.hom_ext
    change (Submodule.iSupLift K hK.directed_le (coconeLinearMap K hK s)
      (submoduleFunctor_ι_app_eq_comp_inclusion K hK s) T hT.ge).comp
        (Submodule.inclusion ((le_iSup K i).trans hT.le)) = coconeLinearMap K hK s i
    exact Submodule.iSupLift_comp_inclusion
      (dir := hK.directed_le)
      (hf := submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
      ((le_iSup K i).trans hT.le)
  uniq s g hg := by
    apply ModuleCat.hom_ext
    apply Submodule.iSupLift_unique
      (dir := hK.directed_le)
      (hf := submoduleFunctor_ι_app_eq_comp_inclusion K hK s)
    intro i m _
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hg i)) m

end ModuleCat

end TauCeti
