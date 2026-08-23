/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality

/-!
# Functoriality of the PBW filtration

Every homomorphism of Lie algebras induces a filtered homomorphism of their universal enveloping
algebras: a word of at most `k` canonical generators is sent to a word of at most `k` canonical
generators. This file states that fact both as preservation of membership and as a map between the
filtration submodules.

The image statements retain information which an inclusion alone would discard. A split
epimorphism maps each filtration step onto the corresponding target step. For a split
monomorphism, the image of a filtration step is exactly the target step intersected with the range
of the enveloping-algebra map. Consequently, an equivalence of Lie algebras identifies the
filtration steps by linear equivalences.

These results do not use the Poincare--Birkhoff--Witt basis theorem. In particular, the exact image
statement for an arbitrary, not necessarily split, Lie subalgebra inclusion remains part of the
ordered-monomial stage of PBW.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.map_mem_pbwFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_le`: induced maps preserve PBW degree.
* `TauCeti.UniversalEnvelopingAlgebra.mapFiltration`: the induced linear map between filtration
  steps, functorial in the Lie homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_of_rightInverse`: split epimorphisms map
  each filtration step onto the corresponding target step.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_inf_range_of_leftInverse`: for a split
  monomorphism, a source step maps to the intersection of the target step with the map's range.
* `TauCeti.UniversalEnvelopingAlgebra.mapEquivFiltration`: a Lie equivalence induces a linear
  equivalence on every filtration step.

## Roadmap

This supplies the functoriality component of Layer 3, "PBW, a substantial sub-project", in
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. It is used by the
Chevalley--Demazure construction in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, on which
the pinned ambient groups in milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` depend.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The image of a PBW filtration step under an induced enveloping-algebra map lies in the
corresponding target step. -/
theorem map_pbwFiltration_le (f : LieHom R L M) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap ≤ pbwFiltration R M k := by
  rw [pbwFiltration_eq_pow, pbwFiltration_eq_pow]
  simpa only [TauCeti.Algebra.wordFiltration_eq_pow] using
    TauCeti.Algebra.map_wordFiltration_le
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap (map R f)
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap
      (fun x => by
        simpa only [LieHom.coe_toLinearMap, map_ι] using
          TauCeti.Algebra.apply_mem_wordFiltration_one
            (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap (f x)) k

/-- A homomorphism of Lie algebras sends an element of PBW filtration degree at most `k` to one of
degree at most `k`. -/
theorem map_mem_pbwFiltration (f : LieHom R L M) {k : ℕ}
    {x : _root_.UniversalEnvelopingAlgebra R L} (hx : x ∈ pbwFiltration R L k) :
    map R f x ∈ pbwFiltration R M k :=
  map_pbwFiltration_le R f k ⟨x, hx, rfl⟩

/-- Induced enveloping-algebra maps also preserve the step immediately preceding a PBW
filtration degree. -/
theorem map_pbwFiltrationPrevious_le (f : LieHom R L M) (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (map R f).toLinearMap ≤
      pbwFiltrationPrevious R M k := by
  cases k with
  | zero => simp
  | succ k => simpa using map_pbwFiltration_le R f k

/-- A homomorphism of Lie algebras sends an element of the step preceding PBW filtration degree
`k` to one of the corresponding preceding step. -/
theorem map_mem_pbwFiltrationPrevious (f : LieHom R L M) {k : ℕ}
    {x : _root_.UniversalEnvelopingAlgebra R L} (hx : x ∈ pbwFiltrationPrevious R L k) :
    map R f x ∈ pbwFiltrationPrevious R M k :=
  map_pbwFiltrationPrevious_le R f k ⟨x, hx, rfl⟩

/-- The linear map between the `k`-th PBW filtration steps induced by a Lie homomorphism. -/
noncomputable def mapFiltration (f : LieHom R L M) (k : ℕ) :
    pbwFiltration R L k →ₗ[R] pbwFiltration R M k :=
  (map R f).toLinearMap.restrict fun _ hx => map_mem_pbwFiltration R f hx

/-- The map between PBW filtration steps acts by the induced enveloping-algebra map. -/
@[simp]
theorem mapFiltration_apply (f : LieHom R L M) (k : ℕ) (x : pbwFiltration R L k) :
    mapFiltration R f k x = map R f x :=
  LinearMap.coe_restrict_apply _ _

/-- The identity Lie homomorphism induces the identity on each PBW filtration step. -/
@[simp]
theorem mapFiltration_id (k : ℕ) :
    mapFiltration R (LieHom.id : LieHom R L L) k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [mapFiltration_apply, LinearMap.id_apply, map_id, AlgHom.id_apply]

/-- Composition of Lie homomorphisms becomes composition of their maps between PBW filtration
steps. -/
@[simp]
theorem mapFiltration_comp (f : LieHom R L M) (g : LieHom R M N) (k : ℕ) :
    mapFiltration R (g.comp f) k = (mapFiltration R g k).comp (mapFiltration R f k) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [mapFiltration_apply, LinearMap.comp_apply, map_comp, AlgHom.comp_apply]

/-- A split epimorphism of Lie algebras maps every PBW filtration step onto the corresponding
target step. -/
theorem map_pbwFiltration_eq_of_rightInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : f.comp g = LieHom.id) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap = pbwFiltration R M k := by
  apply le_antisymm (map_pbwFiltration_le R f k)
  intro y hy
  refine ⟨map R g y, map_mem_pbwFiltration R g hy, ?_⟩
  exact map_rightInverse R h y

/-- For a split monomorphism of Lie algebras, the image of the `k`-th PBW filtration step is the
intersection of the target step with the range of the induced enveloping-algebra map. -/
theorem map_pbwFiltration_eq_inf_range_of_leftInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : g.comp f = LieHom.id) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap =
      pbwFiltration R M k ⊓ LinearMap.range (map R f).toLinearMap := by
  have hcomap : pbwFiltration R L k =
      (pbwFiltration R M k).comap (map R f).toLinearMap := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.1 (map_pbwFiltration_le R f k)
    · intro x hx
      rw [Submodule.mem_comap, AlgHom.toLinearMap_apply] at hx
      simpa only [map_leftInverse R h x] using map_mem_pbwFiltration R g hx
  rw [hcomap, Submodule.map_comap_eq, inf_comm]

/-- A Lie algebra equivalence maps each PBW filtration step exactly onto the corresponding target
step. -/
@[simp]
theorem mapEquiv_pbwFiltration (e : LieEquiv R L M) (k : ℕ) :
    (pbwFiltration R L k).map (mapEquiv R e).toLinearMap = pbwFiltration R M k := by
  have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
    ext x
    exact e.apply_symm_apply x
  have he : (mapEquiv R e).toLinearMap = (map R e.toLieHom).toLinearMap := by
    ext x
    exact AlgHom.congr_fun (mapEquiv_toAlgHom R e) x
  rw [he]
  exact map_pbwFiltration_eq_of_rightInverse R e.toLieHom e.symm.toLieHom h k

/-- A Lie algebra equivalence maps each preceding PBW filtration step exactly onto the
corresponding preceding target step. -/
@[simp]
theorem mapEquiv_pbwFiltrationPrevious (e : LieEquiv R L M) (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (mapEquiv R e).toLinearMap =
      pbwFiltrationPrevious R M k := by
  cases k with
  | zero => simp
  | succ k => simp

/-- The linear equivalence between the `k`-th PBW filtration steps induced by a Lie algebra
equivalence. -/
noncomputable def mapEquivFiltration (e : LieEquiv R L M) (k : ℕ) :
    pbwFiltration R L k ≃ₗ[R] pbwFiltration R M k :=
  (mapEquiv R e).toLinearEquiv.ofSubmodules _ _ (mapEquiv_pbwFiltration R e k)

/-- The equivalence between PBW filtration steps acts by the enveloping-algebra equivalence. -/
@[simp]
theorem mapEquivFiltration_apply (e : LieEquiv R L M) (k : ℕ)
    (x : pbwFiltration R L k) : mapEquivFiltration R e k x = mapEquiv R e x := by
  rw [mapEquivFiltration, LinearEquiv.ofSubmodules_apply, AlgEquiv.coe_toLinearEquiv]

/-- The identity Lie equivalence induces the identity on each PBW filtration step. -/
@[simp]
theorem mapEquivFiltration_refl (k : ℕ) :
    mapEquivFiltration R (LieEquiv.refl : LieEquiv R L L) k = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [mapEquivFiltration_apply, mapEquiv_refl, LinearEquiv.refl_apply]
  rfl

/-- Composition of Lie equivalences becomes composition of their equivalences between PBW
filtration steps. -/
@[simp]
theorem mapEquivFiltration_trans (e : LieEquiv R L M) (d : LieEquiv R M N) (k : ℕ) :
    (mapEquivFiltration R e k).trans (mapEquivFiltration R d k) =
      mapEquivFiltration R (e.trans d) k := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [LinearEquiv.trans_apply, mapEquivFiltration_apply]
  rw [← mapEquiv_trans, AlgEquiv.trans_apply]

/-- Passing to the inverse Lie equivalence gives the inverse linear equivalence between PBW
filtration steps. -/
@[simp]
theorem mapEquivFiltration_symm (e : LieEquiv R L M) (k : ℕ) :
    (mapEquivFiltration R e k).symm = mapEquivFiltration R e.symm k := by
  apply LinearEquiv.ext
  intro x
  apply (mapEquivFiltration R e k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [mapEquivFiltration_apply]
  rw [← mapEquiv_symm]
  exact ((mapEquiv R e).apply_symm_apply x).symm

end TauCeti.UniversalEnvelopingAlgebra
