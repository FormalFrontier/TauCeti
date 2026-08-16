/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.NumberTheory.Modular.Orbits

-- these two serve only the private centre computation, so they stay off the public surface
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Orders of the point stabilisers of the modular group

The stabiliser of a point of `ℍ` in `SL(2, ℤ)` is finite, and its order depends only on the
orbit. Off the two elliptic orbits that order is `2` — the centre `±1`, which acts trivially —
while on the orbit of `i` it is `4` and on the orbit of `ρ` it is `6`. Dividing by the centre
these are the `PSL(2, ℤ)`-orders `e_i = 2`, `e_ρ = 3` and `e_P = 1` elsewhere, the weights the
valence formula attaches to its orbits.

Mathlib classifies the stabilising matrices (`ModularGroup.stabilizer_I`,
`ModularGroup.stabilizer_ρ`, `ModularGroup.stabilizer_of_ne`), but only at a point of the closed
fundamental domain `𝒟`. Added here is the passage to an arbitrary point of `ℍ`, which
`ModularGroup.exists_smul_mem_fd` and conjugation supply, together with the resulting counts.

The three orbit-level counts are stated with their hypotheses on the class of `z` in
`MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`, rather than on a fundamental-domain representative,
because that is the form the valence formula's index type consumes: its non-elliptic orbits are
literally the `q` with `q ≠ ⟦i⟧` and `q ≠ ⟦ρ⟧`.

## Main declarations

* `TauCeti.ModularGroup.finite_stabilizer`: every point stabiliser is finite, so the elliptic
  order is defined at every point of `ℍ`.
* `TauCeti.ModularGroup.card_stabilizer_I` and `TauCeti.ModularGroup.card_stabilizer_ρ`: the
  orders `4` and `6` at the two elliptic points themselves.
* `TauCeti.ModularGroup.card_stabilizer_of_orbit_eq_I` and
  `TauCeti.ModularGroup.card_stabilizer_of_orbit_eq_ρ`: the same orders everywhere on those two
  orbits.
* `TauCeti.ModularGroup.card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ`: order `2` on every
  other orbit.
* `TauCeti.ModularGroup.card_stabilizer_eq_two_mul_card_stabilizer_psl`: the projective order is
  the matrix one halved.
* `TauCeti.ModularGroup.card_stabilizer_psl_I`, `TauCeti.ModularGroup.card_stabilizer_psl_ρ` and
  `TauCeti.ModularGroup.card_stabilizer_psl_eq_one_of_orbit_ne_I_of_orbit_ne_ρ`: the resulting
  elliptic orders `e_i = 2`, `e_ρ = 3` and `e_P = 1`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §2.3 — the elliptic points of `SL(2, ℤ)`
  and their stabiliser orders.
-/

public section

open MulAction UpperHalfPlane ModularGroup

open scoped MatrixGroups Modular

namespace TauCeti

namespace ModularGroup

variable {w z : ℍ}

private theorem finite_stabilizer_of_subset (s : Finset SL(2, ℤ))
    (hs : ∀ g : SL(2, ℤ), g • w = w → g ∈ s) : Finite (stabilizer SL(2, ℤ) w) :=
  (s.finite_toSet.subset fun g hg ↦ hs g hg).to_subtype

private theorem finite_stabilizer_of_smul (g : SL(2, ℤ))
    (h : Finite (stabilizer SL(2, ℤ) (g • z))) : Finite (stabilizer SL(2, ℤ) z) :=
  Finite.of_equiv _ (stabilizerEquivStabilizerOfOrbitRel
    (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit z g))).toEquiv

/-- **Every point stabiliser is finite**, so the elliptic order `e_P` is defined at every point
of `ℍ` and not only inside the fundamental domain. -/
instance finite_stabilizer (z : ℍ) : Finite (stabilizer SL(2, ℤ) z) := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  refine finite_stabilizer_of_smul g ?_
  by_cases hI : g • z = I
  · exact hI ▸ finite_stabilizer_of_subset {1, -1, S, -S} fun _ h ↦ stabilizer_I.mp h
  by_cases hρ : g • z = ρ
  · exact hρ ▸ finite_stabilizer_of_subset _ fun _ h ↦ stabilizer_ρ.mp h
  by_cases hρ' : g • z = (1 : ℝ) +ᵥ ρ
  · -- `ρ + 1` is `T • ρ`, so its stabiliser is conjugate to the one at `ρ`
    rw [hρ', ← modular_T_smul]
    refine finite_stabilizer_of_smul T⁻¹ ?_
    rw [← mul_smul, inv_mul_cancel, one_smul]
    exact finite_stabilizer_of_subset _ fun _ h ↦ stabilizer_ρ.mp h
  · exact finite_stabilizer_of_subset {1, -1} fun _ h ↦ by
      rcases stabilizer_of_ne hg h hI hρ hρ' with rfl | rfl <;> simp

private theorem card_stabilizer_of_coe_eq {s : Finset SL(2, ℤ)}
    (h : (stabilizer SL(2, ℤ) w : Set SL(2, ℤ)) = ↑s) :
    Nat.card (stabilizer SL(2, ℤ) w) = s.card := by
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq]
  simp

-- None of the `SL(2, ℤ)` counts below is `@[simp]`, and none can be: their common
-- left-hand side `Nat.card (stabilizer SL(2, ℤ) z)` is not in simp-normal form, because
-- `MulAction.mem_stabilizer_iff` and `ModularGroup.sl_moeb` rewrite the membership condition
-- underneath the `Nat.card`, so `simpNF` rejects the attribute on every one of them.

/-- **The stabiliser of `i` has order `4`**: the centre `±1` together with `±S`, the inversion
fixing `i`. In `PSL(2, ℤ)` this is the elliptic order `e_i = 2`. -/
theorem card_stabilizer_I : Nat.card (stabilizer SL(2, ℤ) I) = 4 :=
  (card_stabilizer_of_coe_eq (s := {1, -1, S, -S}) (by ext g; simpa using stabilizer_I)).trans
    (by decide)

/-- **The stabiliser of `ρ` has order `6`**: the centre `±1` together with `±ST` and `±T⁻¹S`,
the two rotations of order three fixing `ρ`. In `PSL(2, ℤ)` this is the elliptic order
`e_ρ = 3`. -/
theorem card_stabilizer_ρ : Nat.card (stabilizer SL(2, ℤ) ρ) = 6 :=
  (card_stabilizer_of_coe_eq (s := {1, -1, S * T, -(S * T), T⁻¹ * S, -(T⁻¹ * S)})
    (by ext g; simpa using stabilizer_ρ)).trans (by decide)

/-- **Order `4` everywhere on the orbit of `i`**, not just at `i`: conjugate stabilisers have
equal order, so `card_stabilizer_I` propagates along the orbit. -/
theorem card_stabilizer_of_orbit_eq_I
    (hz : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' I) :
    Nat.card (stabilizer SL(2, ℤ) z) = 4 := by
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (I : ℍ) = z := Quotient.exact' hz
  exact (card_stabilizer_smul g I).trans card_stabilizer_I

/-- **Order `6` everywhere on the orbit of `ρ`**, not just at `ρ`; the companion of
`card_stabilizer_of_orbit_eq_I`. -/
theorem card_stabilizer_of_orbit_eq_ρ
    (hz : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' ρ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 6 := by
  obtain ⟨g, rfl⟩ : ∃ g : SL(2, ℤ), g • (ρ : ℍ) = z := Quotient.exact' hz
  exact (card_stabilizer_smul g ρ).trans card_stabilizer_ρ

/-- **Away from the two elliptic orbits the stabiliser is just the centre**, of order `2`, so
`e_P = 1` in `PSL(2, ℤ)`. No fundamental-domain membership is asked of `z`: the exclusions are
read on its orbit, which is what the valence formula's non-elliptic index type carries. -/
theorem card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ (z : ℍ)
    (hI : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I)
    (hρ : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 2 := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  have hq : (Quotient.mk'' (g • z) : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' z :=
    Quotient.sound' ⟨g, rfl⟩
  -- the representative in `𝒟` inherits both exclusions, so Mathlib's classification applies
  have hI' : g • z ≠ I := fun h ↦ hI (hq ▸ (orbit_mk_eq_I_iff hg).mpr h)
  have hρ' : g • z ≠ ρ := fun h ↦ hρ (hq ▸ (orbit_mk_eq_ρ_iff hg).mpr (Or.inl h))
  have hρ'' : g • z ≠ (1 : ℝ) +ᵥ ρ := fun h ↦ hρ (hq ▸ (orbit_mk_eq_ρ_iff hg).mpr (Or.inr h))
  rw [← card_stabilizer_smul g z]
  refine (card_stabilizer_of_coe_eq (s := {1, -1}) ?_).trans (by decide)
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rcases stabilizer_of_ne hg hx hI' hρ' hρ'' with rfl | rfl <;> simp
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [MulAction.mem_stabilizer_iff]

/-! ### The projective orders `e_P` -/

-- the centre of `SL(2, ℤ)` has order two. Built on Mathlib rather than on an explicit `{±1}`
-- computation: the matrix and module special linear groups agree (`toLin'_equiv`), the module
-- one has centre the roots of unity (`centerEquivRootsOfUnity`), and `-1` is a primitive second
-- root over `ℤ`.
private theorem card_center : Nat.card (Subgroup.center SL(2, ℤ)) = 2 := by
  have hroot : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hrank : max (Module.finrank ℤ (Fin 2 → ℤ)) 1 = 2 := by simp
  rw [Nat.card_congr (Subgroup.centerCongr Matrix.SpecialLinearGroup.toLin'_equiv).toEquiv,
    Nat.card_congr (SpecialLinearGroup.centerEquivRootsOfUnity (R := ℤ) (V := Fin 2 → ℤ)).toEquiv,
    hrank, hroot.card_rootsOfUnity]

/-- **The `SL(2, ℤ)`-stabiliser order is twice the `PSL(2, ℤ)` one.** The two differ exactly by
the centre `±1`, which acts trivially on `ℍ`, so every projective stabiliser is the matrix one
halved — the passage from the counts `4`, `6`, `2` to the elliptic orders `e_P`. -/
theorem card_stabilizer_eq_two_mul_card_stabilizer_psl (z : ℍ) :
    Nat.card (stabilizer SL(2, ℤ) z) = 2 * Nat.card (stabilizer PSL(2, ℤ) z) := by
  rw [TauCeti.card_stabilizer_eq_card_subgroup_mul_card_stabilizer_quotient _ z
    fun g ↦ UpperHalfPlane.pslMk_smul g z, card_center]

-- Neither elliptic order below is `@[simp]`, tested: `MulAction.mem_stabilizer_iff` rewrites
-- `Nat.card (stabilizer G z)` into a `Nat.card` of a subtype underneath, so the left-hand side is
-- not in simp-normal form and `simpNF` rejects the attribute — the same reason recorded above for
-- the `SL(2, ℤ)` counts.

/-- **The elliptic order at `i` is `e_i = 2`** — the order of the `PSL(2, ℤ)`-stabiliser, not the
weight: the valence formula weights that orbit by the reciprocal `1 / e_i = 1 / 2`. -/
theorem card_stabilizer_psl_I : Nat.card (stabilizer PSL(2, ℤ) I) = 2 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl I
  rw [card_stabilizer_I] at h
  omega

/-- **The elliptic order at `ρ` is `e_ρ = 3`** — again the stabiliser order; the valence formula
weights that orbit by `1 / e_ρ = 1 / 3`. -/
theorem card_stabilizer_psl_ρ : Nat.card (stabilizer PSL(2, ℤ) ρ) = 3 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl ρ
  rw [card_stabilizer_ρ] at h
  omega

/-- **Every non-elliptic orbit has `e_P = 1`**: away from the orbits of `i` and `ρ`, the
`PSL(2, ℤ)`-action on `ℍ` is free. -/
theorem card_stabilizer_psl_eq_one_of_orbit_ne_I_of_orbit_ne_ρ (z : ℍ)
    (hI : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' I)
    (hρ : (Quotient.mk'' z : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) ≠ Quotient.mk'' ρ) :
    Nat.card (stabilizer PSL(2, ℤ) z) = 1 := by
  have h := card_stabilizer_eq_two_mul_card_stabilizer_psl z
  rw [card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ z hI hρ] at h
  omega

end ModularGroup

end TauCeti

end
