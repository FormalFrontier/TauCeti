/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The vertex simple representations of a quiver

For a vertex `i` of a quiver `Q`, the *vertex simple* representation `Sᵢ` is the base field `k` at
`i` and the zero module at every other vertex, every arrow acting by zero. This file constructs
`Sᵢ` and proves that it is a simple object of the category of representations.

The construction is a `CategoryTheory.Paths.lift` of the prefunctor sending `i` to `k`, every other
vertex to the zero module, and every arrow to the zero map; functoriality along path concatenation
is then supplied by Mathlib. Simplicity is checked pointwise: a monomorphism into `Sᵢ` is zero away
from `i` because the target vanishes there, so it is determined by its component at `i`, where `k`
is a simple `k`-module.

## Main definitions

* `TauCeti.simpleRep k Q i`: the vertex simple representation `Sᵢ`.
* `TauCeti.simpleRepSelfEquiv`: the identification `(Sᵢ)ᵢ ≃ₗ[k] k`, and
  `TauCeti.simpleRepGenerator`: the element of `(Sᵢ)ᵢ` it sends to `1`.

## Main results

* `TauCeti.simpleRep_simple`: `Sᵢ` is a simple object of `TauCeti.QuiverRep k Q`.
* `TauCeti.exists_smul_simpleRepGenerator`: `(Sᵢ)ᵢ` is the line spanned by the generator.
* `TauCeti.hom_simpleRep_eq_zero_iff` and `TauCeti.simpleRep_hom_eq_zero_iff`: a morphism into or
  out of `Sᵢ` is detected by its component at `i`.
* `TauCeti.dimVector_simpleRep`: the dimension vector of `Sᵢ` is `Pi.single i 1`.
* `TauCeti.not_nonempty_simpleRep_iso`: vertex simples at distinct vertices are not isomorphic.

## Implementation notes

`simpleRep` branches on equality of vertices. It is noncomputable in any case, so that branch is
decided classically and no `DecidableEq Q` instance appears in the interface; `simpleRep_obj_self`
and `simpleRep_obj_of_ne` describe the two cases without mentioning the branch. Only
`dimVector_simpleRep` assumes `DecidableEq Q`, because `Pi.single` needs one to be stated.

The objects of `CategoryTheory.Paths Q` are the vertices of `Q`, so the statements below use a
vertex directly as an object of the path category.

The roadmap pins the simplicity result as `simpleRep_simple`, so the instance carries that name
rather than the `simple_simpleRep` a Mathlib predicate prefix would give it.

## References

This implements the vertex simples of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

variable (k : Type u) (Q : Type v) [Field k] [Quiver Q]

open scoped Classical in
/-- The **vertex simple** representation `Sᵢ` of a quiver: the base field `k` at the vertex `i`,
the zero module at every other vertex, and the zero map along every arrow. -/
noncomputable def simpleRep (i : Q) : QuiverRep k Q :=
  Paths.lift { obj := fun a ↦ if a = i then ModuleCat.of k k else 0, map := fun _ ↦ 0 }

variable {k Q}

/-- At `i`, the vertex simple `Sᵢ` is the base field `k`. -/
@[simp]
theorem simpleRep_obj_self (i : Q) : (simpleRep k Q i).obj i = ModuleCat.of k k :=
  if_pos rfl

/-- Away from `i`, the vertex simple `Sᵢ` is the zero module. -/
@[simp]
theorem simpleRep_obj_of_ne {i a : Q} (h : a ≠ i) : (simpleRep k Q i).obj a = 0 :=
  if_neg h

/-- Away from `i`, the vertex simple `Sᵢ` vanishes. -/
theorem isZero_simpleRep_obj {i a : Q} (h : a ≠ i) : IsZero ((simpleRep k Q i).obj a) := by
  rw [simpleRep_obj_of_ne h]
  exact isZero_zero _

/-- At `i`, the vertex simple `Sᵢ` is the simple `k`-module `k`. -/
instance simple_simpleRep_obj_self (i : Q) : Simple ((simpleRep k Q i).obj i) := by
  rw [simpleRep_obj_self]
  infer_instance

instance finiteDimensional_simpleRep_obj (i a : Q) :
    FiniteDimensional k ((simpleRep k Q i).obj a) := by
  rcases eq_or_ne a i with rfl | ha
  · rw [simpleRep_obj_self]
    exact inferInstanceAs (FiniteDimensional k k)
  · rw [simpleRep_obj_of_ne ha]
    have : Subsingleton ((0 : ModuleCat k) : Type u) :=
      ModuleCat.subsingleton_of_isZero (isZero_zero _)
    infer_instance

/-! ### The vertex simple is a line at its vertex -/

variable (k)

/-- The vector space that the vertex simple `Sᵢ` puts at `i` is the base field. -/
noncomputable def simpleRepSelfEquiv (i : Q) :
    (simpleRep k Q i).obj ((Paths.of Q).obj i) ≃ₗ[k] k :=
  (eqToIso (simpleRep_obj_self i)).toLinearEquiv

/-- The canonical generator of the line `(Sᵢ)ᵢ`: the element corresponding to `1 : k`. -/
noncomputable def simpleRepGenerator (i : Q) : (simpleRep k Q i).obj ((Paths.of Q).obj i) :=
  (simpleRepSelfEquiv k i).symm 1

/-- The generator of `(Sᵢ)ᵢ` corresponds to `1 : k`. -/
@[simp]
theorem simpleRepSelfEquiv_apply_generator (i : Q) :
    simpleRepSelfEquiv k i (simpleRepGenerator k i) = 1 :=
  (simpleRepSelfEquiv k i).apply_symm_apply 1

/-- **The vertex simple is a line at its vertex**: every element of `(Sᵢ)ᵢ` is a multiple of the
generator. -/
theorem exists_smul_simpleRepGenerator {i : Q}
    (x : (simpleRep k Q i).obj ((Paths.of Q).obj i)) :
    ∃ c : k, x = c • simpleRepGenerator k i := by
  refine ⟨simpleRepSelfEquiv k i x, ?_⟩
  rw [simpleRepGenerator, ← LinearEquiv.map_smul, smul_eq_mul, mul_one,
    LinearEquiv.symm_apply_apply]

/-- The generator of `(Sᵢ)ᵢ` is nonzero. -/
theorem simpleRepGenerator_ne_zero (i : Q) : simpleRepGenerator k i ≠ 0 := by
  intro h
  have h1 := congrArg (simpleRepSelfEquiv k i) h
  rw [simpleRepSelfEquiv_apply_generator, map_zero] at h1
  exact one_ne_zero h1

variable {k}

/-- Every arrow of the quiver acts by zero on the vertex simple `Sᵢ`. -/
@[simp]
theorem simpleRep_map_toPath (i : Q) {a b : Q} (e : a ⟶ b) :
    (simpleRep k Q i).map e.toPath = 0 :=
  Paths.lift_toPath _ e

/-- More generally, every path of positive length acts by zero on the vertex simple `Sᵢ`. -/
@[simp]
theorem simpleRep_map_cons (i : Q) {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    (simpleRep k Q i).map (p.cons e) = 0 := by
  rw [simpleRep, Paths.lift_cons]
  exact Limits.comp_zero

/-- A path of positive length acts by zero on the vertex simple `Sᵢ`; only the trivial paths, which
act by the identity, survive. -/
theorem simpleRep_map_eq_zero_of_length_ne_zero (i : Q) {a b : Q} (p : Quiver.Path a b)
    (hp : p.length ≠ 0) : (simpleRep k Q i).map p = 0 := by
  cases p with
  | nil => exact absurd rfl hp
  | cons q e => exact simpleRep_map_cons i q e

/-- A morphism into the vertex simple `Sᵢ` vanishes as soon as its component at `i` does: all its
other components land in a zero module. -/
@[simp]
theorem hom_simpleRep_eq_zero_iff {i : Q} {M : QuiverRep k Q} (f : M ⟶ simpleRep k Q i) :
    f = 0 ↔ f.app i = 0 := by
  refine ⟨fun h ↦ by
    rw [h]
    exact CategoryTheory.Limits.zero_app (ModuleCat k) M (simpleRep k Q i)
      ((Paths.of Q).obj i), fun h ↦ ?_⟩
  refine NatTrans.ext (funext fun a ↦ ?_)
  rcases eq_or_ne a i with rfl | ha
  · exact h
  · exact (isZero_simpleRep_obj (Q := Q) ha).eq_of_tgt _ _

/-- Dually, a morphism out of the vertex simple `Sᵢ` vanishes as soon as its component at `i` does:
all its other components start from a zero module. -/
@[simp]
theorem simpleRep_hom_eq_zero_iff {i : Q} {M : QuiverRep k Q} (f : simpleRep k Q i ⟶ M) :
    f = 0 ↔ f.app i = 0 := by
  refine ⟨fun h ↦ by
    rw [h]
    exact CategoryTheory.Limits.zero_app (ModuleCat k) (simpleRep k Q i) M
      ((Paths.of Q).obj i), fun h ↦ ?_⟩
  refine NatTrans.ext (funext fun a ↦ ?_)
  rcases eq_or_ne a i with rfl | ha
  · exact h
  · exact (isZero_simpleRep_obj (Q := Q) ha).eq_of_src _ _

/-- **The vertex simples are simple.** The vertex representation `Sᵢ = simpleRep k Q i` is a simple
object of `TauCeti.QuiverRep k Q`. -/
instance simpleRep_simple (i : Q) : Simple (simpleRep k Q i) where
  mono_isIso_iff_nonzero {M} f _ := by
    constructor
    · intro _ h
      have hzi : IsZero ((simpleRep k Q i).obj i) := (IsZero.of_epi_eq_zero f h).obj i
      rw [simpleRep_obj_self] at hzi
      exact not_subsingleton k (ModuleCat.subsingleton_of_isZero hzi)
    · intro h
      rw [NatTrans.isIso_iff_isIso_app]
      intro a
      change Q at a
      change IsIso (f.app ((Paths.of Q).obj a))
      rcases eq_or_ne a i with rfl | ha
      · letI : Simple ((simpleRep k Q a).obj ((Paths.of Q).obj a)) := by
          change Simple ((simpleRep k Q a).obj a)
          exact simple_simpleRep_obj_self a
        exact isIso_of_mono_of_nonzero ((hom_simpleRep_eq_zero_iff f).ne.mp h)
      · have ht : IsZero ((simpleRep k Q i).obj ((Paths.of Q).obj a)) := by
          change IsZero ((simpleRep k Q i).obj a)
          exact isZero_simpleRep_obj (Q := Q) ha
        have hs : IsZero (M.obj ((Paths.of Q).obj a)) :=
          IsZero.of_mono (f.app ((Paths.of Q).obj a)) ht
        rw [hs.eq_of_src (f.app ((Paths.of Q).obj a)) (hs.iso ht).hom]
        infer_instance

/-- The dimension vector of the vertex simple `Sᵢ` is the standard basis vector at `i`. -/
@[simp]
theorem dimVector_simpleRep [DecidableEq Q] (i : Q) :
    dimVector (simpleRep k Q i) = Pi.single i 1 := by
  funext a
  rw [dimVector_apply, Paths.of_obj, Pi.single_apply]
  rcases eq_or_ne a i with rfl | ha
  · rw [if_pos rfl, simpleRep_obj_self]
    exact Module.finrank_self k
  · rw [if_neg ha]
    have : Subsingleton ((simpleRep k Q i).obj a) :=
      ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj ha)
    exact Module.finrank_zero_of_subsingleton

/-- Vertex simples at distinct vertices are not isomorphic: their dimension vectors differ. -/
theorem not_nonempty_simpleRep_iso {i j : Q} (h : i ≠ j) :
    ¬ Nonempty (simpleRep k Q i ≅ simpleRep k Q j) := by
  classical
  rintro ⟨e⟩
  have hd := dimVector_eq_of_iso e
  rw [dimVector_simpleRep, dimVector_simpleRep] at hd
  simpa [Pi.single_apply, h] using congrFun hd i

end TauCeti
