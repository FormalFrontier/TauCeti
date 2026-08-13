/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Transporting ambient isotopies across changes of ambient coordinates

The geometric-topology roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, "Encoding
conventions") mandates that isotopy and ambient isotopy be *"defined generally, then
specialised ... in full generality"*, with the single general construction underlying locally
flat isotopy (layer 2), diffeotopies (layer 3), and concordance (layer 6) -- *"none of those
should re-define it"*. This file records one such general closure property: an ambient isotopy
can be transported through a change of coordinates on its ambient space.

Given an ambient isotopy `Φ` of `Y` and a homeomorphism `h : Y ≃ₜ Z`, `Φ.transport h` runs `Φ`
in the coordinates supplied by `h`, producing an ambient isotopy of `Z`. Its total map is
obtained by pre- and post-composing `Φ`'s total homeomorphism with `id ×ₜ h⁻¹` and `id ×ₜ h`,
so it is again an ambient isotopy. The endpoint formula records that each time slice is `h`
conjugating the corresponding slice of `Φ`; downstream specialisations to smooth or locally
flat settings can add their own structure on top of this point-set statement.

The self-homeomorphism case `h : Y ≃ₜ Y` is `Φ.conj h`, the conjugation of an ambient isotopy
that keeps the ambient space fixed; here the endpoint slices land in the group `Y ≃ₜ Y` and the
transport formulas specialise to genuine group conjugates `h * - * h⁻¹`.

## Main definitions

* `TauCeti.AmbientIsotopy.transport`: the ambient isotopy `Φ` transported across `h : Y ≃ₜ Z`,
  with total map `(t, z) ↦ (t, h (Φ (t, h⁻¹ z)))`.
* `TauCeti.AmbientIsotopy.conj`: the self-homeomorphism case `Φ.transport h` for `h : Y ≃ₜ Y`,
  the ambient isotopy `Φ` conjugated by `h`.

## Main results

* `TauCeti.AmbientIsotopy.homeomorph_transport`: every time slice of `Φ.transport h` is the
  conjugate `(h.symm.trans (Φ.homeomorph t)).trans h`.
* `TauCeti.AmbientIsotopy.finalHomeomorph_transport`: the final homeomorphism of `Φ.transport h`
  is the conjugate `(h.symm.trans Φ.finalHomeomorph).trans h`.
* `TauCeti.AmbientIsotopy.homeomorph_conj` / `finalHomeomorph_conj`: the self-homeomorphism
  specialisations, with the conjugates written as group products `h * - * h⁻¹` in `Y ≃ₜ Y`.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- **Transport of an ambient isotopy** across a homeomorphism `h : Y ≃ₜ Z` of ambient spaces:
at each time `t` run the homeomorphism `Φ t` in the coordinates supplied by `h`, giving
`z ↦ h (Φ (t, h⁻¹ z))`. The total map is a homeomorphism because it is `Φ`'s total homeomorphism
pre- and post-composed with the product homeomorphisms `id ×ₜ h⁻¹` and `id ×ₜ h`. -/
noncomputable def transport (h : Y ≃ₜ Z) : AmbientIsotopy Z where
  toContinuousMap := ⟨fun p => h (Φ.toContinuousMap (p.1, h.symm p.2)), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Z => (p.1, h (Φ.toContinuousMap (p.1, h.symm p.2))))
        = ⇑((Homeomorph.refl I).prodCongr h) ∘ Φ.totalMap ∘
          ⇑((Homeomorph.refl I).prodCongr h.symm) := by
      funext p
      obtain ⟨t, z⟩ := p
      simp [Homeomorph.coe_prodCongr, Function.comp_def]
    rw [heq]
    exact (((Homeomorph.refl I).prodCongr h).isHomeomorph.comp Φ.isHomeomorph_total).comp
      ((Homeomorph.refl I).prodCongr h.symm).isHomeomorph
  map_zero_left' z := by
    simp

@[simp]
theorem transport_apply (h : Y ≃ₜ Z) (p : I × Z) :
    (Φ.transport h).toContinuousMap p = h (Φ.toContinuousMap (p.1, h.symm p.2)) := (rfl)

@[simp 1100]
theorem final_transport (h : Y ≃ₜ Z) (z : Z) :
    (Φ.transport h).final z = h (Φ.final (h.symm z)) := by
  rw [final_apply, transport_apply, final_apply]

/-- Every time slice of a transported ambient isotopy is the corresponding slice of `Φ` read in
the coordinates supplied by `h`:
`(Φ.transport h).homeomorph t = (h.symm.trans (Φ.homeomorph t)).trans h`. -/
@[simp]
theorem homeomorph_transport (h : Y ≃ₜ Z) (t : I) :
    (Φ.transport h).homeomorph t = (h.symm.trans (Φ.homeomorph t)).trans h := by
  ext z
  simp only [homeomorph_apply, transport_apply, Homeomorph.trans_apply]

/-- The final homeomorphism of a transported ambient isotopy is the final homeomorphism of `Φ`
read in the coordinates supplied by `h`:
`(Φ.transport h).finalHomeomorph = (h.symm.trans Φ.finalHomeomorph).trans h`. -/
@[simp]
theorem finalHomeomorph_transport (h : Y ≃ₜ Z) :
    (Φ.transport h).finalHomeomorph = (h.symm.trans Φ.finalHomeomorph).trans h := by
  ext z
  simp only [finalHomeomorph_apply, final_transport, Homeomorph.trans_apply]

/-- **Conjugation of an ambient isotopy** by a self-homeomorphism `h`: the special case of
`AmbientIsotopy.transport` in which the change of coordinates fixes the ambient space, so the
endpoint slices conjugate inside the group `Y ≃ₜ Y`. The total map is
`(t, y) ↦ (t, h (Φ (t, h⁻¹ y)))`. -/
noncomputable def conj (h : Y ≃ₜ Y) : AmbientIsotopy Y := Φ.transport h

@[simp]
theorem conj_apply (h : Y ≃ₜ Y) (p : I × Y) :
    (Φ.conj h).toContinuousMap p = h (Φ.toContinuousMap (p.1, h.symm p.2)) := (rfl)

@[simp 1100]
theorem final_conj (h : Y ≃ₜ Y) (y : Y) : (Φ.conj h).final y = h (Φ.final (h.symm y)) := by
  rw [final_apply, conj_apply, final_apply]

/-- Every time slice of a conjugated ambient isotopy is the conjugate of the corresponding time
slice: `(Φ.conj h).homeomorph t = h * Φ.homeomorph t * h⁻¹`. -/
@[simp]
theorem homeomorph_conj (h : Y ≃ₜ Y) (t : I) :
    (Φ.conj h).homeomorph t = h * Φ.homeomorph t * h⁻¹ := by
  ext y
  simp only [homeomorph_apply, conj_apply, Homeomorph.mul_apply, Homeomorph.inv_apply]

/-- The final homeomorphism of a conjugated ambient isotopy is the conjugate of the final
homeomorphism: `(Φ.conj h).finalHomeomorph = h * Φ.finalHomeomorph * h⁻¹`. -/
@[simp]
theorem finalHomeomorph_conj (h : Y ≃ₜ Y) :
    (Φ.conj h).finalHomeomorph = h * Φ.finalHomeomorph * h⁻¹ := by
  ext y
  simp only [finalHomeomorph_apply, final_conj, Homeomorph.mul_apply, Homeomorph.inv_apply]

end AmbientIsotopy

end TauCeti
