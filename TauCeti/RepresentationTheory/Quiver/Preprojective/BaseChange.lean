/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# Base change for additive preprojective algebras

The additive preprojective algebra is defined over a commutative ring, but its presentation has
integer coefficients: the doubled paths are unchanged and only the coefficients are transported.
Consequently a ring homomorphism `f : k →+* l` gives a canonical coefficient map

```text
Π_k(Q) → Π_l(Q).
```

This is the presentation-level base-change map.  It is deliberately a semilinear `RingHom`: its
restriction to scalars is `f`, while the target is naturally an `l`-algebra.  The quotient map is
characterized on every basis path, so the construction does not silently identify `Π_l(Q)` with a
tensor product.  Such a tensor-product identification is a separate result and is not part of this
module.

The relation is preserved because the global preprojective relator is a sum of differences of
paths with coefficients `1` and `-1`.  The same argument works for loops and parallel arrows,
which are retained by `Quiver.Symmetrify`.

This is the base-change clause of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  The conventions follow the presentation and
later-factor-first multiplication fixed in `Preprojective.Basic`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w z

section

variable {k : Type w} {l : Type z} {Q : Type u}
  [CommRing k] [CommRing l] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-! ### The path-algebra map behind the quotient map -/

private theorem preprojectiveBaseChangePathAlgHom_hcomp
    {a b c : Symmetrify Q} (p : Path a b) (q : Path c a) :
    (preprojectiveMk l Q (ofPath ⟨a, b, p⟩) : preprojectiveAlgebra l Q) *
        preprojectiveMk l Q (ofPath ⟨c, a, q⟩) =
      preprojectiveMk l Q (ofPath ⟨c, b, q.comp p⟩) := by
  rw [← map_mul, ofPath_mul_ofPath_of_comp]

private theorem preprojectiveBaseChangePathAlgHom_hzero
    {x y : Quiver.TotalPath (Symmetrify Q)} (h : y.2.1 ≠ x.1) :
    (preprojectiveMk l Q (ofPath x) : preprojectiveAlgebra l Q) *
        preprojectiveMk l Q (ofPath y) = 0 := by
  rw [← map_mul, ofPath_mul_ofPath_of_not_composable h, map_zero]

private theorem preprojectiveBaseChangePathAlgHom_hone :
    letI : Fintype (Symmetrify Q) := Fintype.ofFinite _
    (∑ v : Symmetrify Q,
        (preprojectiveMk l Q
          (ofPath ⟨v, v, Path.nil⟩) : preprojectiveAlgebra l Q)) = 1 := by
  let _ := Fintype.ofFinite (Symmetrify Q)
  calc
    (∑ v : Symmetrify Q,
        (preprojectiveMk l Q
          (ofPath ⟨v, v, Path.nil⟩) : preprojectiveAlgebra l Q)) =
        preprojectiveMk l Q (∑ v : Symmetrify Q,
          (ofPath ⟨v, v, Path.nil⟩ : pathAlgebra l (Symmetrify Q))) := by
      rw [map_sum]
    _ = preprojectiveMk l Q (∑ v : Symmetrify Q, vertexIdempotent l v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [vertexIdempotent_eq_ofPath]
    _ = preprojectiveMk l Q 1 := by rw [one_def]
    _ = 1 := (preprojectiveMk l Q).map_one

private noncomputable def preprojectiveBaseChangePathAlgHom (f : k →+* l) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    pathAlgebra k (Symmetrify Q) →ₐ[k] preprojectiveAlgebra l Q := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  exact PathAlgebra.liftAlgHom k
    (fun x => preprojectiveMk l Q (ofPath x))
    preprojectiveBaseChangePathAlgHom_hcomp
    preprojectiveBaseChangePathAlgHom_hzero
    preprojectiveBaseChangePathAlgHom_hone

private theorem preprojectiveBaseChangePathAlgHom_ofPath (f : k →+* l)
    (x : Quiver.TotalPath (Symmetrify Q)) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    preprojectiveBaseChangePathAlgHom f (ofPath x) = preprojectiveMk l Q (ofPath x) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  rw [preprojectiveBaseChangePathAlgHom]
  exact PathAlgebra.liftAlgHom_ofPath k _ _ _ _ x

private theorem preprojectiveBaseChangePathAlgHom_headBacktrackElem (f : k →+* l)
    {i j : Q} (a : i ⟶ j) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    preprojectiveBaseChangePathAlgHom f (headBacktrackElem k a) =
      preprojectiveMk l Q (headBacktrackElem l a) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  rw [headBacktrackElem_def, preprojectiveBaseChangePathAlgHom_ofPath,
    headBacktrackElem_def]

private theorem preprojectiveBaseChangePathAlgHom_tailBacktrackElem (f : k →+* l)
    {i j : Q} (a : i ⟶ j) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    preprojectiveBaseChangePathAlgHom f (tailBacktrackElem k a) =
      preprojectiveMk l Q (tailBacktrackElem l a) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  rw [tailBacktrackElem_def, preprojectiveBaseChangePathAlgHom_ofPath,
    tailBacktrackElem_def]

/-! ### Descent through the preprojective relation -/

private theorem preprojectiveBaseChangePathAlgHom_relator (f : k →+* l) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    preprojectiveBaseChangePathAlgHom f (preprojectiveRelator k Q) = 0 := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  rw [preprojectiveRelator_def]
  simp only [map_sum, map_sub, preprojectiveBaseChangePathAlgHom_headBacktrackElem,
    preprojectiveBaseChangePathAlgHom_tailBacktrackElem]
  simpa only [preprojectiveRelator_def, map_sum, map_sub] using
    (preprojectiveMk_preprojectiveRelator l Q)

private noncomputable def preprojectiveBaseChangeAlgHom (f : k →+* l) :
    letI : Algebra k (preprojectiveAlgebra l Q) :=
      ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
    preprojectiveAlgebra k Q →ₐ[k] preprojectiveAlgebra l Q := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  exact preprojectiveLift (preprojectiveBaseChangePathAlgHom f)
    (preprojectiveBaseChangePathAlgHom_relator f)

/-! ### The public coefficient map -/

/-- The coefficient base-change map on an additive preprojective algebra.

The map leaves every doubled path unchanged and applies `f` to its coefficients.  It is exposed
as a `RingHom` because the scalar rings on the two quotient algebras differ; its semilinearity is
recorded by `preprojectiveBaseChange_algebraMap`. -/
noncomputable def preprojectiveBaseChange (f : k →+* l) :
    preprojectiveAlgebra k Q →+* preprojectiveAlgebra l Q := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  exact (preprojectiveBaseChangeAlgHom f).toRingHom

/-- The base-change map sends the quotient class of every path to the quotient class of the same
path over the new coefficient ring. -/
@[simp]
theorem preprojectiveBaseChange_preprojectiveMk_ofPath (f : k →+* l)
    (x : Quiver.TotalPath (Symmetrify Q)) :
    preprojectiveBaseChange f (preprojectiveMk k Q (ofPath x)) =
      preprojectiveMk l Q (ofPath x) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
      (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  -- The public map is the underlying ring map of the quotient lift; expose that lift here.
  change preprojectiveBaseChangeAlgHom f (preprojectiveMk k Q (ofPath x)) = _
  rw [preprojectiveBaseChangeAlgHom, preprojectiveLift_preprojectiveMk,
    preprojectiveBaseChangePathAlgHom_ofPath]

/-- The map on preprojective algebras carries the source scalar action to the target scalar action
through the coefficient homomorphism. -/
@[simp]
theorem preprojectiveBaseChange_algebraMap (f : k →+* l) (r : k) :
    preprojectiveBaseChange f (algebraMap k (preprojectiveAlgebra k Q) r) =
      algebraMap l (preprojectiveAlgebra l Q) (f r) := by
  let _ : Algebra k (preprojectiveAlgebra l Q) :=
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f).toAlgebra'
        (fun c x => Algebra.commutes (R := l) (A := preprojectiveAlgebra l Q) (f c) x)
  -- The target is a `k`-algebra via the composite coefficient map.
  change preprojectiveBaseChangeAlgHom f (algebraMap k (preprojectiveAlgebra k Q) r) =
    ((algebraMap l (preprojectiveAlgebra l Q)).comp f) r
  exact (preprojectiveBaseChangeAlgHom f).commutes r

/-- Base change along the identity coefficient homomorphism is the identity map. -/
@[simp]
theorem preprojectiveBaseChange_id :
    preprojectiveBaseChange (RingHom.id k) = RingHom.id (preprojectiveAlgebra k Q) := by
  apply preprojectiveAlgebra_ringHom_ext
  · intro r
    simp
  · intro x
    simp

/-- Base change along a composite coefficient homomorphism is the composite of the base-change
maps. -/
@[simp]
theorem preprojectiveBaseChange_comp {m : Type*} [CommRing m] (f : k →+* l) (g : l →+* m) :
    preprojectiveBaseChange (Q := Q) (g.comp f) =
      (preprojectiveBaseChange (Q := Q) g).comp (preprojectiveBaseChange (Q := Q) f) := by
  apply preprojectiveAlgebra_ringHom_ext
  · intro r
    simp
  · intro x
    simp

end

end TauCeti
