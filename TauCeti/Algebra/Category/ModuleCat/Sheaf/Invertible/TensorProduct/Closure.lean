/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Restriction
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction
public import TauCeti.CategoryTheory.Sites.CoversTop

/-!
# Tensor products of invertible sheaves

The tensor product of two locally free rank-one sheaves is again locally free of rank one. The
proof refines local trivialization atlases for the two factors to a common cover. On each member
of that cover, both factors are the standard free rank-one sheaf, so the tensor product is
trivial by the tensor-unit isomorphisms.

## Main declarations

* `SheafOfModules.LocalTrivializations.tensorProduct` constructs a local trivialization atlas for
  the tensor product of two locally trivialized sheaves;
* `SheafOfModules.IsInvertible.tensorProduct` proves closure of invertible sheaves under tensor
  product.

These declarations provide the site-level closure result used to define tensor products of line
  bundles and, subsequently, the tensor operation in the Picard group.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} (ringCatSheaf R)}

namespace LocalTrivializations

/-- A common refinement of two local trivialization atlases trivializes their tensor product. -/
@[expose]
def tensorProduct (tM : LocalTrivializations.{u, v₁, u₁} M)
    (tN : LocalTrivializations.{u, v₁, u₁} N) :
    LocalTrivializations.{u, v₁, u₁} (SheafOfModules.tensorProduct R M N) := by
  let r : CategoryTheory.GrothendieckTopology.CoversTop.CommonRefinement.{u₁, v₁, u₁, u₁}
      J tM.X tN.X :=
    CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement tM.coversTop tN.coversTop
  exact
    { I := r.I
      X := r.X
      coversTop := r.coversTop
      iso := fun i ↦ by
        let F : SheafOfModules.{u, v₁, max u₁ v₁} (ringCatSheaf (R.over (r.X i))) :=
          _root_.SheafOfModules.free (R := ringCatSheaf (R.over (r.X i))) (PUnit.{u + 1})
        exact (SheafOfModules.tensorProductFreePUnitIsoLeft.{u, v₁, max u₁ v₁}
          (R.over (r.X i)) F).symm ≪≫
          SheafOfModules.tensorProductCongrLeft.{u, v₁, max u₁ v₁} (R.over (r.X i))
            (tM.isoOver (r.leftIndex i) (r.left i)) ≪≫
          SheafOfModules.tensorProductCongrRight.{u, v₁, max u₁ v₁} (R.over (r.X i))
            (tN.isoOver (r.rightIndex i) (r.right i)) ≪≫
          (SheafOfModules.overTensorProductIso R M N (r.X i)).symm }

/-- The tensor-product atlas uses the indexing type of the common refinement. -/
@[simp]
lemma tensorProduct_I (tM : LocalTrivializations.{u, v₁, u₁} M)
    (tN : LocalTrivializations.{u, v₁, u₁} N) :
    (tensorProduct tM tN).I =
      (CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement
        tM.coversTop tN.coversTop).I :=
  rfl

/-- The tensor-product atlas uses the objects of the common refinement. -/
@[simp]
lemma tensorProduct_X (tM : LocalTrivializations.{u, v₁, u₁} M)
    (tN : LocalTrivializations.{u, v₁, u₁} N) :
    (tensorProduct tM tN).X =
      (CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement
        tM.coversTop tN.coversTop).X :=
  rfl

/-- The tensor-product atlas trivializes through the corresponding restricted factors. -/
@[simp]
lemma tensorProduct_iso (tM : LocalTrivializations.{u, v₁, u₁} M)
    (tN : LocalTrivializations.{u, v₁, u₁} N) (i : (tensorProduct tM tN).I) :
    (tensorProduct tM tN).iso i =
      let r := CategoryTheory.GrothendieckTopology.CoversTop.commonRefinement
        tM.coversTop tN.coversTop
      let F : SheafOfModules.{u, v₁, max u₁ v₁} (ringCatSheaf (R.over (r.X i))) :=
        _root_.SheafOfModules.free (R := ringCatSheaf (R.over (r.X i))) (PUnit.{u + 1})
      cast (by
        dsimp only [r]
        dsimp only [F]
        rw [tensorProduct_X]
        rfl)
        ((SheafOfModules.tensorProductFreePUnitIsoLeft (R.over (r.X i)) F).symm ≪≫
          SheafOfModules.tensorProductCongrLeft (R.over (r.X i))
            (tM.isoOver (r.leftIndex i) (r.left i)) ≪≫
          SheafOfModules.tensorProductCongrRight (R.over (r.X i))
            (tN.isoOver (r.rightIndex i) (r.right i)) ≪≫
          (SheafOfModules.overTensorProductIso R M N (r.X i)).symm) :=
  rfl

end LocalTrivializations

namespace IsInvertible

/-- The tensor product of two invertible sheaves is invertible. -/
theorem tensorProduct [IsInvertible M] [IsInvertible N] :
    IsInvertible (SheafOfModules.tensorProduct R M N) := by
  let tM := LocalTrivializations.ofIsInvertible M
  let tN := LocalTrivializations.ofIsInvertible N
  exact (LocalTrivializations.tensorProduct tM tN).isInvertible

end IsInvertible

end SheafOfModules

end

end TauCeti
