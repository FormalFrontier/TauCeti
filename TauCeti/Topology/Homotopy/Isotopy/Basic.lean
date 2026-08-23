/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic

/-!
# Isotopy and ambient isotopy

An *isotopy* between two continuous maps is a homotopy whose every time slice is a topological
embedding, and an *ambient isotopy* of a space `Y` is a
homotopy from the identity of `Y` whose level-preserving total map `I × Y → I × Y` is a
homeomorphism. These are the point-set foundations that the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology`) asks for once, in full generality, before specialising.
`Isotopy` deliberately uses the slice-wise, homotopy-through-embeddings convention.
Burde--Zieschang, *Knots*, Chapter 1, Definition 1.1 instead requires the associated
level-preserving map `I × X → I × Y` to be an embedding. The two conditions agree when `X` is
compact and `Y` is Hausdorff, but the slice-wise condition is weaker for the arbitrary spaces
allowed here. `AmbientIsotopy` follows their Definition 1.2, generalized to this continuous
topological setting. The non-ambient relation is a general point-set notion of isotopy; later
knot-equivalence foundations should use ambient isotopy, specialized as needed to smooth
embeddings `S¹ ↪ M`. Later geometric-topology foundations specialize these notions as appropriate
for locally flat isotopy, diffeotopies, and concordance.

## A warning: non-ambient isotopy is degenerate for knots

The non-ambient relation `Isotopy`/`Isotopic` is *not* the right equivalence for classical knot
theory. It records a moving embedded image, but it need not extend to a motion of the ambient
space and therefore need not preserve knot complements. *Ambient* isotopy is the relation with
knot-theoretic content: an ambient isotopy induces a homeomorphism of complements, so knot
invariants must be built on `AmbientIsotopy` and the `AmbientIsotopic` equivalence from
`TauCeti.Topology.Homotopy.AmbientIsotopic.Basic`, not on `Isotopy`/`Isotopic`. See
Burde--Zieschang, *Knots*, Chapter 1 §A, where ambient isotopy (Definition 1.2) is introduced
after their stronger level-preserving notion of non-ambient isotopy (Definition 1.1).

## Main definitions

* `TauCeti.Isotopy f₀ f₁`: a homotopy from `f₀` to `f₁` through topological embeddings.
* `TauCeti.Isotopic f₀ f₁`: the proposition that such an isotopy exists. This is the reusable
  general non-ambient relation; knot-equivalence layers should instead use `AmbientIsotopic` from
  `TauCeti.Topology.Homotopy.AmbientIsotopic.Basic`.
* `TauCeti.AmbientIsotopy Y`: a homotopy of `Y` from the identity whose total
  level-preserving map is a homeomorphism.
* `TauCeti.AmbientIsotopy.trans` / `TauCeti.AmbientIsotopy.symm`: the composition and inverse of
  ambient isotopies, the closure operations that make ambient isotopy an equivalence relation.

## Main results

* `TauCeti.Isotopy.isEmbedding_left` / `isEmbedding_right`: the endpoints of an isotopy are
  embeddings.
* `TauCeti.Isotopic.refl` / `TauCeti.Isotopic.symm` / `TauCeti.Isotopic.trans`: isotopy is
  reflexive on embeddings, symmetric, and transitive.
* `TauCeti.Isotopic.homotopic`: isotopic maps are homotopic.
* `TauCeti.AmbientIsotopy.isotopy` / `TauCeti.AmbientIsotopy.isotopic`: an ambient isotopy
  carries any embedding `f` to the isotopic embedding `Φ.final ∘ f`. This is the "ambient
  isotopy implies isotopy" direction.
* `TauCeti.AmbientIsotopy.final_trans` / `TauCeti.AmbientIsotopy.symm_final_final` /
  `TauCeti.AmbientIsotopy.final_symm_final`: the final maps of the composite and inverse ambient
  isotopies, and that the inverse final map undoes the original on both sides.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An **isotopy** between `f₀ f₁ : C(X, Y)` is a homotopy for which every time slice
`x ↦ F(t, x)` is a topological embedding.

As an equivalence this non-ambient relation is too coarse for classical knot theory: it need not
extend to a motion of the ambient space and therefore need not preserve knot complements. Use
`AmbientIsotopy`/`AmbientIsotopic` for knot equivalence; see the module docstring and the
comparison with the Burde--Zieschang definition there. -/
abbrev Isotopy (f₀ f₁ : C(X, Y)) : Type _ :=
  HomotopyWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g

namespace Isotopy

variable {f₀ f₁ : C(X, Y)}

/-- Every time-slice of an isotopy is a topological embedding. -/
theorem isEmbedding_apply (F : Isotopy f₀ f₁) (t : I) :
    IsEmbedding fun x => F (t, x) :=
  F.prop' t

/-- The map an isotopy starts at is a topological embedding. -/
theorem isEmbedding_left (F : Isotopy f₀ f₁) : IsEmbedding f₀ := by
  simpa using F.isEmbedding_apply 0

/-- The map an isotopy ends at is a topological embedding. -/
theorem isEmbedding_right (F : Isotopy f₀ f₁) : IsEmbedding f₁ := by
  simpa using F.isEmbedding_apply 1

end Isotopy

/-- Two maps `f₀ f₁ : C(X, Y)` are **isotopic** if there is an isotopy between them.

Warning: for classical knot theory this non-ambient relation is too coarse: it need not preserve
knot complements, so knot invariants must be built on `AmbientIsotopic`, not on `Isotopic`. -/
def Isotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Isotopy f₀ f₁)

/-- Two maps are isotopic exactly when there is an isotopy between them. -/
theorem isotopic_def {f₀ f₁ : C(X, Y)} : Isotopic f₀ f₁ ↔ Nonempty (Isotopy f₀ f₁) := Iff.rfl

namespace Isotopic

variable {f₀ f₁ : C(X, Y)}

/-- An isotopy witnesses that its endpoints are isotopic. -/
theorem of_isotopy (F : Isotopy f₀ f₁) : Isotopic f₀ f₁ := ⟨F⟩

/-- Isotopy is reflexive on embeddings. -/
theorem refl (f : C(X, Y)) (hf : IsEmbedding f) : Isotopic f f :=
  ⟨HomotopyWith.refl f hf⟩

/-- Isotopy is symmetric. -/
@[symm]
theorem symm (h : Isotopic f₀ f₁) : Isotopic f₁ f₀ :=
  ⟨h.some.symm⟩

/-- Isotopy is transitive. -/
@[trans]
theorem trans {f₂ : C(X, Y)} (h₀₁ : Isotopic f₀ f₁) (h₁₂ : Isotopic f₁ f₂) : Isotopic f₀ f₂ :=
  ⟨h₀₁.some.trans h₁₂.some⟩

/-- The left endpoint of an isotopy relation is an embedding. -/
theorem isEmbedding_left (h : Isotopic f₀ f₁) : IsEmbedding f₀ :=
  Isotopy.isEmbedding_left h.some

/-- The right endpoint of an isotopy relation is an embedding. -/
theorem isEmbedding_right (h : Isotopic f₀ f₁) : IsEmbedding f₁ :=
  Isotopy.isEmbedding_right h.some

/-- Isotopic maps are homotopic. -/
theorem homotopic (h : Isotopic f₀ f₁) : Homotopic f₀ f₁ :=
  ⟨h.some.toHomotopy⟩

/-- Isotopic maps are homotopic through embeddings in Mathlib's generic API. -/
theorem homotopicWith (h : Isotopic f₀ f₁) :
    HomotopicWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g :=
  h

end Isotopic

/-- An **ambient isotopy** of `Y` is a homotopy from the identity map of `Y` whose
level-preserving total map is a homeomorphism. The time-`1` map `Φ.final` is the resulting
homeomorphism. -/
structure AmbientIsotopy (Y : Type*) [TopologicalSpace Y] extends C(I × Y, Y) where
  /-- the level-preserving total map of the ambient isotopy is a homeomorphism -/
  isHomeomorph_total' : IsHomeomorph fun p : I × Y => (p.1, toFun p)
  /-- the ambient isotopy starts at the identity of `Y` -/
  map_zero_left' : ∀ y, toFun (0, y) = y

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- Two ambient isotopies are equal when their underlying continuous maps agree pointwise. -/
@[ext]
theorem ext {Φ Ψ : AmbientIsotopy Y}
    (h : ∀ p, Φ.toContinuousMap p = Ψ.toContinuousMap p) : Φ = Ψ := by
  cases Φ
  cases Ψ
  simp only [AmbientIsotopy.mk.injEq]
  exact ContinuousMap.ext h

/-- The level-preserving total map of an ambient isotopy. -/
def totalMap : C(I × Y, I × Y) :=
  ⟨fun p => (p.1, Φ.toContinuousMap p), by fun_prop⟩

@[simp]
theorem totalMap_apply (p : I × Y) : Φ.totalMap p = (p.1, Φ.toContinuousMap p) := (rfl)

/-- The level-preserving total map of an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_total : IsHomeomorph Φ.totalMap :=
  Φ.isHomeomorph_total'

/-- Every time-slice of an ambient isotopy is a self-homeomorphism of `Y`. -/
theorem isHomeomorph_apply (t : I) : IsHomeomorph fun y => Φ.toContinuousMap (t, y) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · let k : Y → I × Y := fun y => (t, y)
    have hk_cont : Continuous k := by fun_prop
    have hcomp : IsEmbedding (k ∘ fun y => Φ.toContinuousMap (t, y)) := by
      convert Φ.isHomeomorph_total.isEmbedding.comp (isEmbedding_prodMkRight t) using 1
      ext y <;> rfl
    exact IsEmbedding.of_comp (by fun_prop) hk_cont hcomp
  · intro y
    rcases Φ.isHomeomorph_total.surjective (t, y) with ⟨p, hp⟩
    refine ⟨p.2, ?_⟩
    have ht : p.1 = t := congrArg Prod.fst hp
    rw [← ht]
    exact congrArg Prod.snd hp

/-- The ambient isotopy starts at the identity of `Y`. -/
@[simp]
theorem map_zero_left (y : Y) : Φ.toContinuousMap (0, y) = y :=
  Φ.map_zero_left' y

/-- The time-`1` homeomorphism produced by an ambient isotopy, as a continuous map. -/
def final : C(Y, Y) := ⟨fun y => Φ.toContinuousMap (1, y), by fun_prop⟩

@[simp]
theorem final_apply (y : Y) : Φ.final y = Φ.toContinuousMap (1, y) := (rfl)

/-- The final map produced by an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_final : IsHomeomorph Φ.final :=
  Φ.isHomeomorph_apply 1

/-- The time-`t` self-homeomorphism bundled as a `Homeomorph`. -/
noncomputable def homeomorph (t : I) : Y ≃ₜ Y :=
  IsHomeomorph.homeomorph (fun y => Φ.toContinuousMap (t, y)) (Φ.isHomeomorph_apply t)

@[simp]
theorem homeomorph_apply (t : I) (y : Y) : Φ.homeomorph t y = Φ.toContinuousMap (t, y) :=
  (rfl)

/-- The time-`1` homeomorphism produced by an ambient isotopy. -/
noncomputable def finalHomeomorph : Y ≃ₜ Y :=
  Φ.homeomorph 1

@[simp]
theorem finalHomeomorph_apply (y : Y) : Φ.finalHomeomorph y = Φ.final y :=
  (rfl)

/-- The constant ambient isotopy at the identity. -/
def refl (Y : Type*) [TopologicalSpace Y] : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => p.2, by fun_prop⟩
  isHomeomorph_total' := .id
  map_zero_left' _ := rfl

/-- The final map of the constant ambient isotopy is the identity. -/
@[simp 1100]
theorem final_refl (y : Y) : (refl Y).final y = y := (rfl)

/-- Every time slice of the constant ambient isotopy is the identity homeomorphism. -/
@[simp]
theorem homeomorph_refl (t : I) : (refl Y).homeomorph t = Homeomorph.refl Y := by
  ext y
  rw [homeomorph_apply, Homeomorph.refl_apply]
  rfl

/-- The final homeomorphism of the constant ambient isotopy is the identity. -/
@[simp]
theorem finalHomeomorph_refl : (refl Y).finalHomeomorph = Homeomorph.refl Y := by
  rw [finalHomeomorph, homeomorph_refl]

instance : Inhabited (AmbientIsotopy Y) := ⟨refl Y⟩

/-- An ambient isotopy carries any embedding `f` to the embedding `Φ.final ∘ f` through an
explicit isotopy: at time `t` the embedding is the homeomorphism `Φ t` postcomposed with `f`. -/
def isotopy {f : C(X, Y)} (hf : IsEmbedding f) : Isotopy f (Φ.final.comp f) where
  toFun := fun p => Φ.toContinuousMap (p.1, f p.2)
  continuous_toFun := by fun_prop
  map_zero_left := fun x => Φ.map_zero_left (f x)
  map_one_left := fun _ => rfl
  prop' := fun t => (Φ.isHomeomorph_apply t).isEmbedding.comp hf

@[simp]
theorem isotopy_apply {f : C(X, Y)} (hf : IsEmbedding f) (t : I) (x : X) :
    Φ.isotopy hf (t, x) = Φ.toContinuousMap (t, f x) :=
  (rfl)

/-- **Ambient isotopy implies isotopy**: an ambient isotopy of `Y` carries any embedding `f`
into `Y` to the isotopic embedding `Φ.final ∘ f`. -/
theorem isotopic {f : C(X, Y)} (hf : IsEmbedding f) : Isotopic f (Φ.final.comp f) :=
  ⟨Φ.isotopy hf⟩

/-- The level-preserving total map of an ambient isotopy, bundled as a self-homeomorphism of
`I × Y`. -/
noncomputable def totalHomeomorph : (I × Y) ≃ₜ (I × Y) :=
  IsHomeomorph.homeomorph Φ.totalMap Φ.isHomeomorph_total

@[simp]
theorem totalHomeomorph_apply (p : I × Y) :
    Φ.totalHomeomorph p = (p.1, Φ.toContinuousMap p) := (rfl)

/-- The inverse total homeomorphism preserves the time coordinate. -/
@[simp]
theorem totalHomeomorph_symm_fst (p : I × Y) : (Φ.totalHomeomorph.symm p).1 = p.1 := by
  have h := Φ.totalHomeomorph.apply_symm_apply p
  rw [totalHomeomorph_apply] at h
  exact (Prod.ext_iff.mp h).1

/-- **Composition of ambient isotopies**: follow `Φ_t` then `Ψ_t` at each time `t`. -/
def trans (Ψ : AmbientIsotopy Y) : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => Ψ.toContinuousMap (p.1, Φ.toContinuousMap p), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, Ψ.toContinuousMap (p.1, Φ.toContinuousMap p)))
        = ⇑Ψ.totalMap ∘ ⇑Φ.totalMap := by
      funext p
      simp [Function.comp, totalMap_apply]
    rw [heq]
    exact Ψ.isHomeomorph_total.comp Φ.isHomeomorph_total
  map_zero_left' y := by
    -- the composite's `toFun` at time `0` is `Ψ (0, Φ (0, y))`, which both factors fix.
    simp

@[simp]
theorem trans_apply (Ψ : AmbientIsotopy Y) (p : I × Y) :
    (Φ.trans Ψ).toContinuousMap p = Ψ.toContinuousMap (p.1, Φ.toContinuousMap p) := (rfl)

/-- The final map of the composite ambient isotopy `Φ.trans Ψ` is the composition of the final
maps of `Φ` and `Ψ`: at the endpoint it is `Ψ.final ∘ Φ.final`. -/
@[simp 1100]
theorem final_trans (Ψ : AmbientIsotopy Y) (y : Y) :
    (Φ.trans Ψ).final y = Ψ.final (Φ.final y) := by
  rw [final_apply, trans_apply, final_apply, final_apply]

/-- Every time slice of a composite ambient isotopy is the composite of the corresponding
time slices. -/
@[simp]
theorem homeomorph_trans (Ψ : AmbientIsotopy Y) (t : I) :
    (Φ.trans Ψ).homeomorph t = (Φ.homeomorph t).trans (Ψ.homeomorph t) := by
  ext y
  rw [homeomorph_apply, trans_apply, Homeomorph.trans_apply, homeomorph_apply, homeomorph_apply]

/-- The final homeomorphism of a composite ambient isotopy is the composite of the final
homeomorphisms. -/
@[simp]
theorem finalHomeomorph_trans (Ψ : AmbientIsotopy Y) :
    (Φ.trans Ψ).finalHomeomorph = Φ.finalHomeomorph.trans Ψ.finalHomeomorph := by
  rw [finalHomeomorph, finalHomeomorph, finalHomeomorph, homeomorph_trans]

/-- **Inverse of an ambient isotopy**: undo `Φ_t` at each time `t`. -/
noncomputable def symm : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => (Φ.totalHomeomorph.symm p).2,
    continuous_snd.comp Φ.totalHomeomorph.symm.continuous⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, (Φ.totalHomeomorph.symm p).2))
        = ⇑Φ.totalHomeomorph.symm := by
      funext p
      exact Prod.ext (Φ.totalHomeomorph_symm_fst p).symm rfl
    rw [heq]
    exact Φ.totalHomeomorph.symm.isHomeomorph
  map_zero_left' y := by
    have h0 : Φ.totalHomeomorph (0, y) = (0, y) := by
      rw [totalHomeomorph_apply, Φ.map_zero_left]
    have hsymm : Φ.totalHomeomorph.symm (0, y) = (0, y) :=
      Φ.totalHomeomorph.symm_apply_eq.mpr h0.symm
    simp [hsymm]

@[simp]
theorem symm_apply (p : I × Y) :
    Φ.symm.toContinuousMap p = (Φ.totalHomeomorph.symm p).2 := (rfl)

/-- The inverse ambient isotopy undoes the original: its final map is a left inverse of the
original final map. -/
@[simp↓ 1100]
theorem symm_final_final (y : Y) : Φ.symm.final (Φ.final y) = y := by
  have h1 : Φ.totalHomeomorph (1, y) = (1, Φ.toContinuousMap (1, y)) := by
    rw [totalHomeomorph_apply]
  simp only [final_apply, symm_apply]
  rw [Φ.totalHomeomorph.symm_apply_eq.mpr h1.symm]

/-- The original ambient isotopy undoes its inverse: the original final map is a left inverse of
the inverse final map. -/
@[simp↓ 1100]
theorem final_symm_final (y : Y) : Φ.final (Φ.symm.final y) = y := by
  have hfst : (Φ.totalHomeomorph.symm (1, y)).1 = 1 := Φ.totalHomeomorph_symm_fst (1, y)
  have happ := Φ.totalHomeomorph.apply_symm_apply (1, y)
  rw [totalHomeomorph_apply] at happ
  have hpair : ((1 : I), (Φ.totalHomeomorph.symm (1, y)).2) = Φ.totalHomeomorph.symm (1, y) :=
    Prod.ext hfst.symm rfl
  simp only [final_apply, symm_apply]
  rw [hpair]
  exact (Prod.ext_iff.mp happ).2

/-- Every time slice of the inverse ambient isotopy is the inverse of the corresponding
time slice. -/
@[simp]
theorem homeomorph_symm (t : I) : Φ.symm.homeomorph t = (Φ.homeomorph t).symm := by
  ext y
  symm
  apply (Φ.homeomorph t).symm_apply_eq.mpr
  have hfst : (Φ.totalHomeomorph.symm (t, y)).1 = t := Φ.totalHomeomorph_symm_fst (t, y)
  have happ := Φ.totalHomeomorph.apply_symm_apply (t, y)
  rw [totalHomeomorph_apply] at happ
  have hpair : (t, (Φ.totalHomeomorph.symm (t, y)).2) = Φ.totalHomeomorph.symm (t, y) :=
    Prod.ext hfst.symm rfl
  simp only [homeomorph_apply, symm_apply]
  rw [hpair]
  exact (Prod.ext_iff.mp happ).2.symm

/-- The final homeomorphism of the inverse ambient isotopy is the inverse final homeomorphism. -/
@[simp]
theorem finalHomeomorph_symm : Φ.symm.finalHomeomorph = Φ.finalHomeomorph.symm := by
  rw [finalHomeomorph, finalHomeomorph, homeomorph_symm]

end AmbientIsotopy

end TauCeti
