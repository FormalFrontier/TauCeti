/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central isogenies of group schemes

For group schemes over a field, an isogeny is a homomorphism whose underlying scheme morphism is
finite, flat, and surjective. It is central when its scheme-theoretic kernel is central. We express
the latter condition intrinsically through the functor of points: for every test scheme over the
base, every point killed by the homomorphism commutes with every other point of the source.

Quantifying over all test schemes is essential. Centrality only on points over the base field
would miss infinitesimal points and need not describe a central subgroup scheme. The functorial
definition below is equivalent, by Yoneda, to factorization of the kernel through the
scheme-theoretic centre once that closed subgroup has been constructed.

The API records the equivalent pointwise statement that the kernel of every induced group
homomorphism is contained in the ordinary group centre. It also shows that isomorphisms have
central kernel and that every isogeny out of a commutative group scheme is central.

## Main declarations

* `TauCeti.GroupScheme.HasCentralKernel`: every functor-of-points kernel is central.
* `TauCeti.GroupScheme.hasCentralKernel`: the corresponding morphism property.
* `TauCeti.GroupScheme.pointMap_injective_of_mono`: a morphism monic in `Over X` induces an
  injective map on points over every test scheme.
* `TauCeti.GroupScheme.HasCentralKernel.precomp_of_mono`: central kernels are preserved by
  precomposition with a morphism monic in `Over X`.
* `TauCeti.GroupScheme.HasCentralKernel.postcomp_of_mono`: central kernels are preserved by
  postcomposition with a morphism monic in `Over X`.
* `TauCeti.GroupScheme.hasCentralKernel_comp_iff_of_mono`: postcomposition by a morphism monic in
  `Over X` preserves and reflects central kernels.
* `TauCeti.GroupScheme.hasCentralKernel_respectsIso`: having central kernel respects isomorphisms
  of arrows.
* `TauCeti.GroupScheme.isogenies`: the finite, flat, surjective morphism property on group schemes.
* `TauCeti.GroupScheme.IsIsogeny`: the corresponding predicate on a group-scheme morphism.
* `TauCeti.GroupScheme.centralIsogenies`: the central-isogeny morphism property.
* `TauCeti.GroupScheme.IsCentralIsogeny`: an isogeny with central kernel.
* `TauCeti.GroupScheme.isCentralIsogeny_iff_isIsogeny_and`: the predicate-level bridge to the two
  constituent properties.
* `TauCeti.GroupScheme.centralIsogenies_respectsIso`: central isogenies respect isomorphisms of
  arrows.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

The property-level isogeny API is adapted from
`TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny`.

This supplies the central-isogeny interface required by Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {F G H K : Grp (Over X)}

/-- The homomorphism induced by a group-scheme morphism on points valued in a test scheme over
the base. -/
noncomputable def pointMap (f : G ⟶ H) (T : Over X) :
    (T ⟶ G.X) →* (T ⟶ H.X) :=
  ((CategoryTheory.yonedaGrp.map f).app (Opposite.op T)).hom

/-- The map on points is postcomposition with the underlying morphism of group objects. -/
@[simp]
theorem pointMap_apply (f : G ⟶ H) (T : Over X) (g : T ⟶ G.X) :
    pointMap f T g = g ≫ f.hom.hom :=
  (rfl)

/-- The map on points induced by an identity morphism is the identity homomorphism. -/
@[simp]
theorem pointMap_id (G : Grp (Over X)) (T : Over X) :
    pointMap (𝟙 G) T = MonoidHom.id (T ⟶ G.X) := by
  ext g
  simp

/-- The map on points induced by a composite is the composite of the maps on points. -/
@[simp]
theorem pointMap_comp (f : G ⟶ H) (g : H ⟶ K) (T : Over X) :
    pointMap (f ≫ g) T = (pointMap g T).comp (pointMap f T) := by
  ext h
  simp

/-- The morphism property of having central kernel: over every test scheme, each point in the
kernel commutes with every point of the source.

This all-test-schemes condition is the functor-of-points formulation of the scheme-theoretic
kernel being contained in the centre. -/
def hasCentralKernel (X : Scheme) : MorphismProperty (Grp (Over X)) :=
  fun G _ f ↦
    ∀ (T : Over X) (g : T ⟶ G.X), g ≫ f.hom.hom = 1 → ∀ h : T ⟶ G.X, Commute g h

/-- A group-scheme morphism has central kernel when it belongs to `hasCentralKernel X`. -/
abbrev HasCentralKernel (f : G ⟶ H) : Prop :=
  hasCentralKernel X f

/-- A group-scheme morphism has central kernel exactly when the kernel of its map on points over
every test scheme is contained in the ordinary group centre. -/
theorem hasCentralKernel_iff_pointMap_ker_le_center (f : G ⟶ H) :
    HasCentralKernel f ↔
      ∀ T : Over X, (pointMap f T).ker ≤ Subgroup.center (T ⟶ G.X) := by
  constructor
  · intro hf T g hg
    rw [Subgroup.mem_center_iff]
    intro h
    exact (hf T g ((MonoidHom.mem_ker).mp hg) h).eq.symm
  · intro hf T g hg h
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp (hf T ((MonoidHom.mem_ker).mpr hg)) h).symm

/-- A group-scheme morphism monic in `Over X` induces an injective map on points over every test
scheme. -/
theorem pointMap_injective_of_mono (e : G ⟶ H) [Mono e.hom.hom] (T : Over X) :
    Function.Injective (pointMap e T) :=
  fun _ _ h ↦ (cancel_mono e.hom.hom).1 h

/-- A group-scheme morphism with monic underlying morphism has central kernel: every point in its
kernel is the identity. -/
theorem hasCentralKernel_of_mono (f : G ⟶ H) [Mono f.hom.hom] : HasCentralKernel f := by
  intro T g hg h
  have hg_one : g = 1 := by
    apply pointMap_injective_of_mono f T
    simpa only [pointMap_apply, map_one] using hg
  rw [hg_one]
  exact Commute.one_left h

/-- Every morphism from a commutative group scheme has central kernel. -/
theorem hasCentralKernel_of_isCommMonObj (f : G ⟶ H) [IsCommMonObj G.X] :
    HasCentralKernel f := by
  intro T g _ h
  exact Commute.all g h

/-- Precomposing with a morphism monic in `Over X` preserves the central-kernel condition. -/
theorem HasCentralKernel.precomp_of_mono (e : F ⟶ G) [Mono e.hom.hom] (f : G ⟶ H)
    (hf : HasCentralKernel f) : HasCentralKernel (e ≫ f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  have hg' : pointMap f T (pointMap e T g) = 1 := by
    rw [← MonoidHom.comp_apply, ← pointMap_comp]
    exact MonoidHom.mem_ker.mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  apply pointMap_injective_of_mono e T
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.mp (hf T <| MonoidHom.mem_ker.mpr hg')
    (pointMap e T h))

/-- Postcomposing with a morphism monic in `Over X` preserves the central-kernel condition. -/
theorem HasCentralKernel.postcomp_of_mono (f : G ⟶ H) (e : H ⟶ K) [Mono e.hom.hom]
    (hf : HasCentralKernel f) : HasCentralKernel (f ≫ e) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center] at hf ⊢
  intro T g hg
  apply hf T
  rw [MonoidHom.mem_ker]
  apply pointMap_injective_of_mono e T
  rw [map_one, ← MonoidHom.comp_apply, ← pointMap_comp]
  exact MonoidHom.mem_ker.mp hg

/-- Postcomposition by a morphism monic in `Over X` preserves and reflects the central-kernel
condition. -/
theorem hasCentralKernel_comp_iff_of_mono (f : G ⟶ H) (e : H ⟶ K) [Mono e.hom.hom] :
    HasCentralKernel (f ≫ e) ↔ HasCentralKernel f := by
  constructor
  · intro hfe T g hg h
    apply hfe T g ?_ h
    change pointMap (f ≫ e) T g = 1
    rw [pointMap_comp, MonoidHom.comp_apply]
    change pointMap f T g = 1 at hg
    rw [hg, map_one]
  · exact fun hf ↦ hf.postcomp_of_mono f e

/-- Having central kernel is invariant under isomorphisms of arrows. -/
instance hasCentralKernel_respectsIso : (hasCentralKernel X).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro _ _ _ e f hf
    exact HasCentralKernel.precomp_of_mono e.hom f hf
  · intro _ _ _ e f hf
    exact HasCentralKernel.postcomp_of_mono f e.hom hf

section Isogeny

variable {k : Type u} [Field k]
variable {G H K : Grp (Over (Spec (CommRingCat.of k)))}

/-- The morphism property of being an isogeny of group schemes over a field: the underlying
scheme morphism is finite, flat, and surjective. -/
def isogenies (k : Type u) [Field k] :
    MorphismProperty (Grp (Over (Spec (CommRingCat.of k)))) :=
  (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme).inverseImage
    (Grp.forget _ ⋙ Over.forget _)

/-- A homomorphism of group schemes is an isogeny when its underlying scheme morphism is finite,
flat, and surjective. -/
abbrev IsIsogeny (f : G ⟶ H) : Prop :=
  isogenies k f

/-- A group-scheme morphism is an isogeny exactly when its underlying scheme morphism is finite,
flat, and surjective. -/
theorem isIsogeny_iff (f : G ⟶ H) :
    IsIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left :=
  Iff.rfl

/-- Group-scheme isogenies contain identities and are closed under composition. -/
instance : (isogenies k).IsMultiplicative := by
  unfold isogenies
  let : (@Flat ⊓ @Surjective : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  let : (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  infer_instance

/-- Being a group-scheme isogeny is invariant under isomorphisms of arrows. -/
instance : (isogenies k).RespectsIso := by
  unfold isogenies
  let _ : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) ↦ inferInstance)
  let _ : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) ↦ inferInstance)
  let _ : MorphismProperty.RespectsIso
      (@Flat ⊓ @Surjective : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @Flat @Surjective
  let _ : MorphismProperty.RespectsIso
      (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @IsFinite (@Flat ⊓ @Surjective)
  exact MorphismProperty.RespectsIso.inverseImage
    (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme)
    (Grp.forget (Over (Spec (CommRingCat.of k))) ⋙ Over.forget (Spec (CommRingCat.of k)))

/-- The identity of a group scheme is an isogeny. -/
@[simp]
theorem isIsogeny_id (G : Grp (Over (Spec (CommRingCat.of k)))) : IsIsogeny (𝟙 G) :=
  (isogenies k).id_mem G

/-- Every isomorphism of group schemes is an isogeny. -/
theorem isIsogeny_of_isIso (f : G ⟶ H) [IsIso f] : IsIsogeny f :=
  (isogenies k).of_isIso f

namespace IsIsogeny

/-- The underlying scheme morphism of a group-scheme isogeny is finite. -/
theorem isFinite {f : G ⟶ H} (hf : IsIsogeny f) : IsFinite f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.1

/-- The underlying scheme morphism of a group-scheme isogeny is flat. -/
theorem flat {f : G ⟶ H} (hf : IsIsogeny f) : Flat f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.2.1

/-- The underlying scheme morphism of a group-scheme isogeny is surjective. -/
theorem surjective {f : G ⟶ H} (hf : IsIsogeny f) : Surjective f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.2.2

/-- A composite of group-scheme isogenies is an isogeny. -/
theorem comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) :=
  (isogenies k).comp_mem f g hf hg

end IsIsogeny

/-- The morphism property of being a central isogeny of group schemes over a field. -/
def centralIsogenies (k : Type u) [Field k] :
    MorphismProperty (Grp (Over (Spec (CommRingCat.of k)))) :=
  isogenies k ⊓ hasCentralKernel (Spec (CommRingCat.of k))

/-- Central isogenies are invariant under pre- and postcomposition with isomorphisms. -/
instance centralIsogenies_respectsIso : (centralIsogenies k).RespectsIso := by
  unfold centralIsogenies
  infer_instance

/-- A central isogeny is an isogeny whose scheme-theoretic kernel is central, expressed on the
functor of points over every test scheme. -/
abbrev IsCentralIsogeny (f : G ⟶ H) : Prop :=
  centralIsogenies k f

/-- A central isogeny is precisely an isogeny with central kernel. -/
theorem isCentralIsogeny_iff_isIsogeny_and (f : G ⟶ H) :
    IsCentralIsogeny f ↔ IsIsogeny f ∧ HasCentralKernel f :=
  Iff.rfl

/-- A morphism is a central isogeny exactly when its underlying scheme morphism is finite, flat,
and surjective and its kernel is central on all scheme-valued points. -/
theorem isCentralIsogeny_iff (f : G ⟶ H) :
    IsCentralIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        HasCentralKernel f := by
  rw [isCentralIsogeny_iff_isIsogeny_and, isIsogeny_iff]
  simp only [and_assoc]

/-- A group-scheme morphism is a central isogeny exactly when it is finite, flat, and surjective
and, on points over every test scheme, its kernel is contained in the ordinary group centre. -/
theorem isCentralIsogeny_iff_pointMap_ker_le_center (f : G ⟶ H) :
    IsCentralIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        ∀ T : Over (Spec (CommRingCat.of k)),
          (pointMap f T).ker ≤ Subgroup.center (T ⟶ G.X) := by
  rw [isCentralIsogeny_iff, hasCentralKernel_iff_pointMap_ker_le_center]

/-- The isogeny underlying a central isogeny. -/
theorem IsCentralIsogeny.isIsogeny {f : G ⟶ H} (hf : IsCentralIsogeny f) : IsIsogeny f :=
  (isCentralIsogeny_iff_isIsogeny_and f).mp hf |>.1

/-- The underlying scheme morphism of a central isogeny is finite. -/
theorem IsCentralIsogeny.isFinite {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    IsFinite f.hom.hom.left :=
  hf.isIsogeny.isFinite

/-- The underlying scheme morphism of a central isogeny is flat. -/
theorem IsCentralIsogeny.flat {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    Flat f.hom.hom.left :=
  hf.isIsogeny.flat

/-- The underlying scheme morphism of a central isogeny is surjective. -/
theorem IsCentralIsogeny.surjective {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    Surjective f.hom.hom.left :=
  hf.isIsogeny.surjective

/-- The central-kernel property underlying a central isogeny. -/
theorem IsCentralIsogeny.hasCentralKernel {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    HasCentralKernel f :=
  (isCentralIsogeny_iff_isIsogeny_and f).mp hf |>.2

/-- Every isogeny from a commutative group scheme is central. -/
theorem IsIsogeny.isCentral_of_isCommMonObj {f : G ⟶ H} (hf : IsIsogeny f)
    [IsCommMonObj G.X] : IsCentralIsogeny f :=
  (isCentralIsogeny_iff_isIsogeny_and f).mpr ⟨hf, hasCentralKernel_of_isCommMonObj f⟩

/-- The identity of a group scheme is a central isogeny. -/
@[simp]
theorem isCentralIsogeny_id (G : Grp (Over (Spec (CommRingCat.of k)))) :
    IsCentralIsogeny (𝟙 G) :=
  (isCentralIsogeny_iff_isIsogeny_and _).mpr
    ⟨isIsogeny_id G, hasCentralKernel_of_mono (𝟙 G)⟩

/-- Every isomorphism of group schemes is a central isogeny. -/
theorem isCentralIsogeny_of_isIso (f : G ⟶ H) [IsIso f] : IsCentralIsogeny f :=
  (isCentralIsogeny_iff_isIsogeny_and f).mpr
    ⟨isIsogeny_of_isIso f, hasCentralKernel_of_mono f⟩

end Isogeny

end TauCeti.GroupScheme
