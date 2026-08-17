/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Central isogenies of group schemes

For group schemes over a field, an isogeny is a homomorphism whose underlying scheme morphism is
finite and surjective. It is central when its scheme-theoretic kernel is central. We express the
latter condition intrinsically through the functor of points: for every test scheme over the
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
* `TauCeti.GroupScheme.isogenies`: the finite-surjective morphism property on group schemes.
* `TauCeti.GroupScheme.IsIsogeny`: the corresponding predicate on a group-scheme morphism.
* `TauCeti.GroupScheme.IsCentralIsogeny`: an isogeny with central kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

This supplies the central-isogeny interface required by Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {G H K : Grp (Over X)}

/-- The homomorphism induced by a group-scheme morphism on points valued in a test scheme over
the base. -/
@[expose] noncomputable def pointMap (f : G ⟶ H) (T : Over X) :
    (T ⟶ G.X) →* (T ⟶ H.X) :=
  ((CategoryTheory.yonedaGrp.map f).app (Opposite.op T)).hom

/-- The map on points is postcomposition with the underlying morphism of group objects. -/
@[simp]
theorem pointMap_apply (f : G ⟶ H) (T : Over X) (g : T ⟶ G.X) :
    pointMap f T g = g ≫ f.hom.hom :=
  rfl

/-- A group-scheme morphism has central kernel when, over every test scheme, each point in its
kernel commutes with every point of the source.

This all-test-schemes condition is the functor-of-points formulation of the scheme-theoretic
kernel being contained in the centre. -/
def HasCentralKernel (f : G ⟶ H) : Prop :=
  ∀ (T : Over X) (g : T ⟶ G.X), g ≫ f.hom.hom = 1 → ∀ h : T ⟶ G.X, Commute g h

/-- Unfolding centrality of the kernel gives the all-test-schemes commutation condition. -/
theorem hasCentralKernel_iff (f : G ⟶ H) :
    HasCentralKernel f ↔
      ∀ (T : Over X) (g : T ⟶ G.X), g ≫ f.hom.hom = 1 →
        ∀ h : T ⟶ G.X, Commute g h :=
  Iff.rfl

/-- A group-scheme morphism has central kernel exactly when the kernel of its map on points over
every test scheme is contained in the ordinary group centre. -/
theorem hasCentralKernel_iff_pointMap_ker_le_center (f : G ⟶ H) :
    HasCentralKernel f ↔
      ∀ T : Over X, (pointMap f T).ker ≤ Subgroup.center (T ⟶ G.X) := by
  rw [hasCentralKernel_iff]
  constructor
  · intro hf T g hg
    rw [Subgroup.mem_center_iff]
    intro h
    exact (hf T g ((MonoidHom.mem_ker).mp hg) h).eq.symm
  · intro hf T g hg h
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp (hf T ((MonoidHom.mem_ker).mpr hg)) h).symm

/-- An isomorphism of group schemes has central kernel: every point in its kernel is the
identity. -/
theorem hasCentralKernel_of_isIso (f : G ⟶ H) [IsIso f] : HasCentralKernel f := by
  intro T g hg h
  have hg_one : g = 1 := by
    apply (cancel_mono f.hom.hom).1
    rw [hg]
    simp
  rw [hg_one]
  exact Commute.one_left h

/-- Every morphism from a commutative group scheme has central kernel. -/
theorem hasCentralKernel_of_isCommMonObj (f : G ⟶ H) [IsCommMonObj G.X] :
    HasCentralKernel f := by
  intro T g _ h
  exact Commute.all g h

section Isogeny

variable {k : Type u} [Field k]
variable {G H K : Grp (Over (Spec (CommRingCat.of k)))}

/-- The morphism property of being an isogeny of group schemes over a field: the underlying
scheme morphism is finite and surjective. -/
def isogenies (k : Type u) [Field k] :
    MorphismProperty (Grp (Over (Spec (CommRingCat.of k)))) :=
  (@IsFinite ⊓ @Surjective : MorphismProperty Scheme).inverseImage
    (Grp.forget _ ⋙ Over.forget _)

/-- A homomorphism of group schemes is an isogeny when its underlying scheme morphism is finite
and surjective. -/
abbrev IsIsogeny (f : G ⟶ H) : Prop :=
  isogenies k f

/-- A group-scheme morphism is an isogeny exactly when its underlying scheme morphism is finite
and surjective. -/
theorem isIsogeny_iff (f : G ⟶ H) :
    IsIsogeny f ↔ IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left :=
  Iff.rfl

/-- Group-scheme isogenies contain identities and are closed under composition. -/
instance : (isogenies k).IsMultiplicative := by
  unfold isogenies
  let : (@IsFinite ⊓ @Surjective : MorphismProperty Scheme).IsMultiplicative :=
    MorphismProperty.IsMultiplicative.inf
  infer_instance

/-- Being a group-scheme isogeny is invariant under isomorphisms of arrows. -/
instance : (isogenies k).RespectsIso := by
  unfold isogenies
  let _ : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) ↦ inferInstance)
  let _ : MorphismProperty.RespectsIso
      (@IsFinite ⊓ @Surjective : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @IsFinite @Surjective
  exact MorphismProperty.RespectsIso.inverseImage
    (@IsFinite ⊓ @Surjective : MorphismProperty Scheme)
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

/-- The underlying scheme morphism of a group-scheme isogeny is surjective. -/
theorem surjective {f : G ⟶ H} (hf : IsIsogeny f) : Surjective f.hom.hom.left :=
  (isIsogeny_iff f).mp hf |>.2

/-- A composite of group-scheme isogenies is an isogeny. -/
theorem comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) :=
  (isogenies k).comp_mem f g hf hg

end IsIsogeny

/-- A central isogeny is an isogeny whose scheme-theoretic kernel is central, expressed on the
functor of points over every test scheme. -/
def IsCentralIsogeny (f : G ⟶ H) : Prop :=
  IsIsogeny f ∧ HasCentralKernel f

/-- A morphism is a central isogeny exactly when its underlying scheme morphism is finite and
surjective and its kernel is central on all scheme-valued points. -/
theorem isCentralIsogeny_iff (f : G ⟶ H) :
    IsCentralIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left ∧ HasCentralKernel f := by
  rw [IsCentralIsogeny, isIsogeny_iff, and_assoc]

/-- A group-scheme morphism is a central isogeny exactly when it is finite and surjective and,
on points over every test scheme, its kernel is contained in the ordinary group centre. -/
theorem isCentralIsogeny_iff_pointMap_ker_le_center (f : G ⟶ H) :
    IsCentralIsogeny f ↔
      IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        ∀ T : Over (Spec (CommRingCat.of k)),
          (pointMap f T).ker ≤ Subgroup.center (T ⟶ G.X) := by
  rw [isCentralIsogeny_iff, hasCentralKernel_iff_pointMap_ker_le_center]

/-- The isogeny underlying a central isogeny. -/
theorem IsCentralIsogeny.isIsogeny {f : G ⟶ H} (hf : IsCentralIsogeny f) : IsIsogeny f :=
  hf.1

/-- The underlying scheme morphism of a central isogeny is finite. -/
theorem IsCentralIsogeny.isFinite {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    IsFinite f.hom.hom.left :=
  hf.isIsogeny.isFinite

/-- The underlying scheme morphism of a central isogeny is surjective. -/
theorem IsCentralIsogeny.surjective {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    Surjective f.hom.hom.left :=
  hf.isIsogeny.surjective

/-- The central-kernel property underlying a central isogeny. -/
theorem IsCentralIsogeny.hasCentralKernel {f : G ⟶ H} (hf : IsCentralIsogeny f) :
    HasCentralKernel f :=
  hf.2

/-- Every isogeny from a commutative group scheme is central. -/
theorem IsIsogeny.isCentral_of_isCommMonObj {f : G ⟶ H} (hf : IsIsogeny f)
    [IsCommMonObj G.X] : IsCentralIsogeny f :=
  ⟨hf, hasCentralKernel_of_isCommMonObj f⟩

/-- The identity of a group scheme is a central isogeny. -/
@[simp]
theorem isCentralIsogeny_id (G : Grp (Over (Spec (CommRingCat.of k)))) :
    IsCentralIsogeny (𝟙 G) :=
  ⟨isIsogeny_id G, hasCentralKernel_of_isIso (𝟙 G)⟩

/-- Every isomorphism of group schemes is a central isogeny. -/
theorem isCentralIsogeny_of_isIso (f : G ⟶ H) [IsIso f] : IsCentralIsogeny f :=
  ⟨isIsogeny_of_isIso f, hasCentralKernel_of_isIso f⟩

end Isogeny

end TauCeti.GroupScheme
