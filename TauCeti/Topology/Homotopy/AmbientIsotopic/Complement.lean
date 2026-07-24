/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic

/-!
# Ambient isotopy preserves the complement of the range

The point of ambient isotopy, as opposed to the naive isotopy of
`TauCeti.Topology.Homotopy.Isotopy.Basic`, is that it moves the *whole* ambient space, not just an
embedded image. Consequently an ambient isotopy carrying a map `f` to a map `g` induces a
homeomorphism of their complements `(range f)ᶜ ≃ₜ (range g)ᶜ`. This is exactly why the
geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 4, "knot theory")
insists that knot invariants be built on ambient isotopy: the complement of a knot is the basic
invariant, and it is a homeomorphism invariant of the ambient-isotopy class precisely because of
the theorem in this file. The module docstring of `TauCeti.Topology.Homotopy.Isotopy.Basic` states
this fact in prose ("an ambient isotopy induces a homeomorphism of complements"); here it is
proved.

Everything is stated for arbitrary continuous maps `f : C(X, Y)`, since the range and its
complement make sense without an embedding hypothesis; the embedded case (knots) is the intended
specialisation. The witnessing homeomorphism is a restriction of the ambient isotopy's final
homeomorphism `Φ.finalHomeomorph`, so it is compatible with all the naturality already recorded
for that homeomorphism in `TauCeti.Topology.Homotopy.Isotopy.Basic`.

## Main definitions

* `TauCeti.AmbientIsotopy.rangeHomeomorph`: the homeomorphism `range f ≃ₜ range (Φ.final.comp f)`
  induced on ranges by an ambient isotopy `Φ`.
* `TauCeti.AmbientIsotopy.complementHomeomorph`: the homeomorphism
  `(range f)ᶜ ≃ₜ (range (Φ.final.comp f))ᶜ` induced on complements.

## Main results

* `TauCeti.AmbientIsotopy.range_final_comp`: the final homeomorphism carries `range f` onto the
  range of the moved map `Φ.final.comp f`.
* `TauCeti.AmbientIsotopic.nonempty_rangeHomeomorph` /
  `TauCeti.AmbientIsotopic.nonempty_complementHomeomorph`: ambient isotopic maps have homeomorphic
  ranges and homeomorphic complements. The complement statement is the knot-invariance fact.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y) (f : C(X, Y))

/-- The final homeomorphism of an ambient isotopy carries `range f` onto the range of the moved
map `Φ.final.comp f`: the image `Φ.finalHomeomorph '' range f` is `range (Φ.final.comp f)`. -/
theorem range_final_comp :
    Set.range (Φ.final.comp f) = Φ.finalHomeomorph '' Set.range f := by
  rw [ContinuousMap.coe_comp, Set.range_comp]
  rfl

/-- A point misses `range f` exactly when its image under the final homeomorphism misses the range
of the moved map. This is the compatibility that lets the final homeomorphism restrict to the
complements. -/
theorem notMem_range_iff (y : Y) :
    y ∉ Set.range f ↔ Φ.finalHomeomorph y ∉ Set.range (Φ.final.comp f) := by
  rw [range_final_comp, Φ.finalHomeomorph.injective.mem_set_image]

/-- The homeomorphism of ranges induced by an ambient isotopy: `Φ.finalHomeomorph` restricts to a
homeomorphism from `range f` onto the range of the moved map `Φ.final.comp f`. -/
@[expose] noncomputable def rangeHomeomorph : Set.range f ≃ₜ Set.range (Φ.final.comp f) :=
  (Homeomorph.image Φ.finalHomeomorph (Set.range f)).trans
    (Homeomorph.setCongr (Φ.range_final_comp f).symm)

theorem rangeHomeomorph_coe_apply (y : Set.range f) :
    (Φ.rangeHomeomorph f y : Y) = Φ.finalHomeomorph y := rfl

/-- The homeomorphism of complements induced by an ambient isotopy: `Φ.finalHomeomorph` restricts
to a homeomorphism from `(range f)ᶜ` onto `(range (Φ.final.comp f))ᶜ`. This is the point-set core
of knot-complement invariance under ambient isotopy. -/
@[expose] noncomputable def complementHomeomorph :
    ↥(Set.range f)ᶜ ≃ₜ ↥(Set.range (Φ.final.comp f))ᶜ :=
  Φ.finalHomeomorph.subtype (Φ.notMem_range_iff f)

theorem complementHomeomorph_coe_apply (y : ↥(Set.range f)ᶜ) :
    (Φ.complementHomeomorph f y : Y) = Φ.finalHomeomorph y := rfl

end AmbientIsotopy

namespace AmbientIsotopic

variable {f g : C(X, Y)}

/-- **Ambient isotopy preserves ranges up to homeomorphism.** If `f` and `g` are ambient isotopic,
their ranges (the embedded images, for embeddings) are homeomorphic. -/
theorem nonempty_rangeHomeomorph (hfg : AmbientIsotopic f g) :
    Nonempty (Set.range f ≃ₜ Set.range g) := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact ⟨Φ.rangeHomeomorph f⟩

/-- **Ambient isotopy preserves complements up to homeomorphism.** If `f` and `g` are ambient
isotopic, the complements `(range f)ᶜ` and `(range g)ᶜ` are homeomorphic. For knots (embeddings
`S¹ ↪ M`) this is the invariance of the knot complement, the reason knot invariants are built on
ambient isotopy rather than on the naive isotopy relation. -/
theorem nonempty_complementHomeomorph (hfg : AmbientIsotopic f g) :
    Nonempty (↥(Set.range f)ᶜ ≃ₜ ↥(Set.range g)ᶜ) := by
  obtain ⟨Φ, rfl⟩ := hfg
  exact ⟨Φ.complementHomeomorph f⟩

end AmbientIsotopic

end TauCeti
