/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Factorial.NatCast
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule
public import TauCeti.RepresentationTheory.Intertwining

/-!
# The Weyl modules of the two extreme shapes: symmetric and exterior powers

The Weyl construction `TauCeti.YoungTableau.weylModule` cuts a subrepresentation of
`(kⁿ)^{⊗d}` out of a Young symmetrizer `c_t`. This file evaluates it at the two extreme shapes,
where the symmetrizer degenerates and the answer is a power of the standard representation:

* a shape with **at most one row** has the whole symmetric group as its row group and a trivial
  column group, so `c_t` is the symmetrization `∑_σ σ` and the Weyl module is `Symᵈ(kⁿ)`;
* a shape with **at most one column** has the whole symmetric group as its column group and a
  trivial row group, so `c_t` is the antisymmetrization `∑_σ sgn(σ) σ` and the Weyl module is
  `⋀ᵈ(kⁿ)`.

Both are proved the same way, and the two halves of the argument are already in place. On the
linear-algebra side, `SymmetricPower.toTensorPower` and Mathlib's `exteriorPower.toTensorPower`
map the symmetric and the exterior power **into** the tensor power, with image exactly the image
of the symmetrization, respectively antisymmetrization, operator, and are injective because
composing back is multiplication by `d!`, invertible over a `ℚ`-algebra. On the symmetric-group
side, the extreme-shape lemmas of `TauCeti/RepresentationTheory/Symmetric/Symmetrizer.lean`
collapse `c_t` to a single factor and evaluate it in the group algebra, which is read here as an
operator on the tensor power. Both maps are equivariant for `GL n k`, because
`GL n k` acts diagonally and the two operators only permute tensor factors; so the identification
of subspaces is an isomorphism of representations, by
`Representation.IntertwiningMap.equivOfRange`.

The hypotheses are stated on the shape, as `μ.colLen 0 ≤ 1` and `μ.rowLen 0 ≤ 1`, which is how
`TauCeti.YoungTableau.rowSubgroup_eq_top_iff` and
`TauCeti.YoungTableau.colSubgroup_eq_top_iff` read the two degeneracies off the diagram. No
condition relating `μ.card` to `n` is needed: for a one-column shape with `μ.card > n` both sides
are zero, the exterior power because it is above the rank and the Weyl module by
`TauCeti.YoungTableau.weylModule_eq_bot`, and the isomorphism holds vacuously.

## Main results

* `TauCeti.YoungTableau.weylRepEquivSymPowerRep`: **`𝕊^{(d)}(kⁿ) ≅ Symᵈ(kⁿ)`**, the Weyl module of
  a shape with at most one row is the symmetric power, with
  `TauCeti.weylRepOfShapeEquivSymPowerRep` its shape-indexed form.
* `TauCeti.YoungTableau.weylRepEquivExtPowerRep`: **`𝕊^{(1ᵈ)}(kⁿ) ≅ ⋀ᵈ(kⁿ)`**, the Weyl module of
  a shape with at most one column is the exterior power, with
  `TauCeti.weylRepOfShapeEquivExtPowerRep` its shape-indexed form.
* `TauCeti.YoungTableau.permTensorActionAlgHom_youngSymmetrizerOver_of_rowSubgroup_eq_top` and
  `TauCeti.YoungTableau.permTensorActionAlgHom_youngSymmetrizerOver_of_colSubgroup_eq_top`: the
  operators on the tensor power that `c_t` becomes at the two extreme shapes.

## Implementation notes

The symmetric statements are over a base ring in `Type`, not in `Type u`: Mathlib's
`SymmetricPower R ι M` requires `R` and the index type `ι` to lie in the same universe, and the
index type here is `Fin μ.card`. The exterior statements carry no such restriction. This matches
`TauCeti.symPowerRep`, which is already monomorphic for the same reason.

The results are stated for an arbitrary tableau of the shape, not only for the row-superstandard
one, since the Weyl module of any tableau of a given shape is the image of an operator that the
extreme-shape hypothesis pins down completely. The shape-indexed forms are then the special case
of the row-superstandard tableau, which is what `TauCeti.weylModuleOfShape` is defined from.

## References

* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris1991],
  Lecture 6, "Weyl's construction", where `𝕊^{(d)}V = Sym^d V` and `𝕊^{(1^d)}V = ⋀^d V` are the
  two extreme cases of the construction.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 2, "Young symmetrizers and the Schur functor", whose two remaining deliverables
  `S^{(d)} V ≅ Symᵈ V` and `S^{(1ᵈ)} V ≅ ⋀ᵈ V` are proved here.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

/-! ### The Young symmetrizer of an extreme shape -/

namespace YoungTableau

section Semiring

variable (k : Type u) [CommSemiring k] [Algebra ℚ k] {μ : YoungDiagram} (n : ℕ)

/-- On a shape with at most one row the Young symmetrizer acts on the tensor power by the
symmetrization operator `∑_σ σ`. -/
theorem permTensorActionAlgHom_youngSymmetrizerOver_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) :
    permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) =
      ∑ σ : Equiv.Perm (Fin μ.card),
        (PiTensorProduct.reindex k (fun _ : Fin μ.card => Fin n → k) σ).toLinearMap := by
  rw [youngSymmetrizerOver_eq_sum_of_rowSubgroup_eq_top k t h, map_sum]
  exact Finset.sum_congr rfl fun σ _ => by
    rw [permTensorActionAlgHom_of, permTensorAction_apply]

end Semiring

section Ring

-- The signed sum below is a `ℤ`-linear combination, so it asks the base ring for negation; that is
-- the only difference from the `CommSemiring` hypothesis of the section above, and it is the same
-- split as between `TauCeti.YoungTableau.youngSymmetrizerOver_eq_sum_of_rowSubgroup_eq_top` and
-- `TauCeti.YoungTableau.youngSymmetrizerOver_eq_sum_of_colSubgroup_eq_top`, which the two theorems
-- respectively rewrite with.
variable (k : Type u) [CommRing k] [Algebra ℚ k] {μ : YoungDiagram} (n : ℕ)

/-- On a shape with at most one column the Young symmetrizer acts on the tensor power by the
antisymmetrization operator `∑_σ sgn(σ) σ`. -/
theorem permTensorActionAlgHom_youngSymmetrizerOver_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) :
    permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t) =
      ∑ σ : Equiv.Perm (Fin μ.card), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex k (fun _ : Fin μ.card => Fin n → k) σ).toLinearMap := by
  rw [youngSymmetrizerOver_eq_sum_of_colSubgroup_eq_top k t h, map_sum]
  exact Finset.sum_congr rfl fun σ _ => by
    rw [map_zsmul, permTensorActionAlgHom_of, permTensorAction_apply]

end Ring

end YoungTableau

/-! ### A shape with at most one row: the symmetric power -/

section OneRow

variable (k : Type) [CommRing k] [Algebra ℚ k] (n : ℕ) {μ : YoungDiagram}

/-- The symmetrization, as an intertwining map of the symmetric power of the standard
representation with its tensor power. -/
noncomputable def symPowerToTensorPower (d : ℕ) :
    Representation.IntertwiningMap (symPowerRep k n d) (tensorPowerRep k n d) where
  toLinearMap := SymmetricPower.toTensorPower k (Fin d) (Fin n → k)
  isIntertwining' g := by
    rw [Representation.symmetricPower_apply, Representation.tensorPower_apply]
    exact SymmetricPower.toTensorPower_comp_map (stdRep k n g)

omit [Algebra ℚ k] in
@[simp]
theorem symPowerToTensorPower_toLinearMap (d : ℕ) :
    (symPowerToTensorPower k n d).toLinearMap =
      SymmetricPower.toTensorPower k (Fin d) (Fin n → k) :=
  (rfl)

/-- **The symmetric power is the Weyl module of a shape with at most one row**, by the
symmetrization `SymmetricPower.toTensorPower`.

This runs the direction the construction produces; the public form of the statement is its inverse
`TauCeti.YoungTableau.weylRepEquivSymPowerRep`. -/
private noncomputable def symPowerRepEquivWeylRep (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1) :
    (symPowerRep k n μ.card).Equiv (YoungTableau.weylRep k n t) :=
  (symPowerToTensorPower k n μ.card).equivOfRange
    (SymmetricPower.toTensorPower_injective
      (by simpa using IsUnit.natCast_factorial_of_algebra (A := k) ℚ μ.card))
    (by
      rw [symPowerToTensorPower_toLinearMap, YoungTableau.weylModule_toSubmodule,
        YoungTableau.permTensorActionAlgHom_youngSymmetrizerOver_of_rowSubgroup_eq_top k n t
          ((YoungTableau.rowSubgroup_eq_top_iff t).2 h)]
      exact SymmetricPower.range_toTensorPower)

/-- The isomorphism `TauCeti.symPowerRepEquivWeylRep` is the symmetrization, read inside the
tensor power. -/
private theorem symPowerRepEquivWeylRep_apply_coe (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1)
    (x : SymmetricPower k (Fin μ.card) (Fin n → k)) :
    ((symPowerRepEquivWeylRep k n t h x : (YoungTableau.weylModule k n t).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) =
      SymmetricPower.toTensorPower k (Fin μ.card) (Fin n → k) x :=
  Representation.IntertwiningMap.equivOfRange_apply_coe _ _ _ x

/-- **`𝕊^{(d)}(kⁿ) ≅ Symᵈ(kⁿ)`**: the Weyl module of a shape with at most one row is the
symmetric power of the standard representation. -/
noncomputable def YoungTableau.weylRepEquivSymPowerRep (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1) :
    (YoungTableau.weylRep k n t).Equiv (symPowerRep k n μ.card) :=
  (symPowerRepEquivWeylRep k n t h).symm

/-- The isomorphism `TauCeti.YoungTableau.weylRepEquivSymPowerRep` is inverse to the
symmetrization: symmetrizing its value returns the element of the tensor power it was applied
to. -/
@[simp]
theorem YoungTableau.toTensorPower_weylRepEquivSymPowerRep (t : YoungTableau μ)
    (h : μ.colLen 0 ≤ 1) (x : (YoungTableau.weylModule k n t).toSubmodule) :
    SymmetricPower.toTensorPower k (Fin μ.card) (Fin n → k)
        (YoungTableau.weylRepEquivSymPowerRep k n t h x) =
      (x : ⨂[k]^μ.card (Fin n → k)) := by
  rw [YoungTableau.weylRepEquivSymPowerRep, ← symPowerRepEquivWeylRep_apply_coe k n t h,
    Representation.Equiv.apply_symm_apply]

/-- The shape-indexed form of `TauCeti.YoungTableau.weylRepEquivSymPowerRep`. -/
noncomputable def weylRepOfShapeEquivSymPowerRep (μ : YoungDiagram) (h : μ.colLen 0 ≤ 1) :
    (weylRepOfShape k n μ).Equiv (symPowerRep k n μ.card) :=
  (YoungTableau.weylRepEquivOfShape k n
      (StandardYoungTableau.rowSuperstandard μ).toTableau).symm.trans
    (YoungTableau.weylRepEquivSymPowerRep k n _ h)

/-- The shape-indexed isomorphism is the tableau-indexed one at the row-superstandard tableau,
after moving the argument along `TauCeti.YoungTableau.weylRepEquivOfShape`. -/
@[simp]
theorem weylRepOfShapeEquivSymPowerRep_apply (μ : YoungDiagram) (h : μ.colLen 0 ≤ 1)
    (x : (weylModuleOfShape k n μ).toSubmodule) :
    weylRepOfShapeEquivSymPowerRep k n μ h x =
      YoungTableau.weylRepEquivSymPowerRep k n
        (StandardYoungTableau.rowSuperstandard μ).toTableau h
        ((YoungTableau.weylRepEquivOfShape k n
          (StandardYoungTableau.rowSuperstandard μ).toTableau).symm x) :=
  Representation.Equiv.trans_apply _ _ x

end OneRow

/-! ### A shape with at most one column: the exterior power -/

section OneColumn

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ) {μ : YoungDiagram}

/-- The antisymmetrization, as an intertwining map of the exterior power of the standard
representation with its tensor power. -/
noncomputable def extPowerToTensorPower (d : ℕ) :
    Representation.IntertwiningMap (extPowerRep k n d) (tensorPowerRep k n d) where
  toLinearMap := exteriorPower.toTensorPower k (Fin n → k) d
  isIntertwining' g := by
    rw [Representation.exteriorPower_apply, Representation.tensorPower_apply]
    exact exteriorPower.toTensorPower_comp_map d (stdRep k n g)

omit [Algebra ℚ k] in
@[simp]
theorem extPowerToTensorPower_toLinearMap (d : ℕ) :
    (extPowerToTensorPower k n d).toLinearMap = exteriorPower.toTensorPower k (Fin n → k) d :=
  (rfl)

/-- **The exterior power is the Weyl module of a shape with at most one column**, by the
antisymmetrization `exteriorPower.toTensorPower`.

This runs the direction the construction produces; the public form of the statement is its inverse
`TauCeti.YoungTableau.weylRepEquivExtPowerRep`. -/
private noncomputable def extPowerRepEquivWeylRep (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1) :
    (extPowerRep k n μ.card).Equiv (YoungTableau.weylRep k n t) :=
  (extPowerToTensorPower k n μ.card).equivOfRange
    (exteriorPower.toTensorPower_injective μ.card (IsUnit.natCast_factorial_of_algebra ℚ μ.card))
    (by
      rw [extPowerToTensorPower_toLinearMap, YoungTableau.weylModule_toSubmodule,
        YoungTableau.permTensorActionAlgHom_youngSymmetrizerOver_of_colSubgroup_eq_top k n t
          ((YoungTableau.colSubgroup_eq_top_iff t).2 h)]
      exact exteriorPower.range_toTensorPower μ.card)

/-- The isomorphism `TauCeti.extPowerRepEquivWeylRep` is the antisymmetrization, read inside the
tensor power. -/
private theorem extPowerRepEquivWeylRep_apply_coe (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1)
    (x : ⋀[k]^μ.card (Fin n → k)) :
    ((extPowerRepEquivWeylRep k n t h x : (YoungTableau.weylModule k n t).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = exteriorPower.toTensorPower k (Fin n → k) μ.card x :=
  Representation.IntertwiningMap.equivOfRange_apply_coe _ _ _ x

/-- **`𝕊^{(1ᵈ)}(kⁿ) ≅ ⋀ᵈ(kⁿ)`**: the Weyl module of a shape with at most one column is the
exterior power of the standard representation. -/
noncomputable def YoungTableau.weylRepEquivExtPowerRep (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1) :
    (YoungTableau.weylRep k n t).Equiv (extPowerRep k n μ.card) :=
  (extPowerRepEquivWeylRep k n t h).symm

/-- The isomorphism `TauCeti.YoungTableau.weylRepEquivExtPowerRep` is inverse to the
antisymmetrization: antisymmetrizing its value returns the element of the tensor power it was
applied to. -/
@[simp]
theorem YoungTableau.toTensorPower_weylRepEquivExtPowerRep (t : YoungTableau μ)
    (h : μ.rowLen 0 ≤ 1) (x : (YoungTableau.weylModule k n t).toSubmodule) :
    exteriorPower.toTensorPower k (Fin n → k) μ.card
        (YoungTableau.weylRepEquivExtPowerRep k n t h x) =
      (x : ⨂[k]^μ.card (Fin n → k)) := by
  rw [YoungTableau.weylRepEquivExtPowerRep, ← extPowerRepEquivWeylRep_apply_coe k n t h,
    Representation.Equiv.apply_symm_apply]

/-- The shape-indexed form of `TauCeti.YoungTableau.weylRepEquivExtPowerRep`. -/
noncomputable def weylRepOfShapeEquivExtPowerRep (μ : YoungDiagram) (h : μ.rowLen 0 ≤ 1) :
    (weylRepOfShape k n μ).Equiv (extPowerRep k n μ.card) :=
  (YoungTableau.weylRepEquivOfShape k n
      (StandardYoungTableau.rowSuperstandard μ).toTableau).symm.trans
    (YoungTableau.weylRepEquivExtPowerRep k n _ h)

/-- The shape-indexed isomorphism is the tableau-indexed one at the row-superstandard tableau,
after moving the argument along `TauCeti.YoungTableau.weylRepEquivOfShape`. -/
@[simp]
theorem weylRepOfShapeEquivExtPowerRep_apply (μ : YoungDiagram) (h : μ.rowLen 0 ≤ 1)
    (x : (weylModuleOfShape k n μ).toSubmodule) :
    weylRepOfShapeEquivExtPowerRep k n μ h x =
      YoungTableau.weylRepEquivExtPowerRep k n
        (StandardYoungTableau.rowSuperstandard μ).toTableau h
        ((YoungTableau.weylRepEquivOfShape k n
          (StandardYoungTableau.rowSuperstandard μ).toTableau).symm x) :=
  Representation.Equiv.trans_apply _ _ x

end OneColumn

end TauCeti
