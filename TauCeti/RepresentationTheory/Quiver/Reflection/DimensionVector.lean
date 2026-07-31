/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.EulerForm
public import Mathlib.LinearAlgebra.Reflection

/-!
# Simple reflections on the dimension vectors of a quiver

For a vertex `i` of a finite quiver `Q`, the simple reflection `sᵢ` is the reflection of the
dimension-vector lattice `Q → ℤ` that negates the simple dimension vector `αᵢ = Pi.single i 1`
and fixes the hyperplane orthogonal to it for the polarized Tits form. It is the numerical
shadow of the Bernstein-Gelfand-Ponomarev reflection functor at `i`, and the generator of the
Weyl group action under which the roots of the Tits form are stable.

The reflection is built from Mathlib's `Module.preReflection`, taking the linear form to be the
polarized Tits form paired with `αᵢ`. Following that naming, `TauCeti.vertexPreReflection` is
available with no hypothesis on `i`, while the reflection identities need `q(αᵢ) = 1`,
equivalently that `i` carries no loop; `TauCeti.vertexReflection` is the automorphism obtained
at such a loopless vertex. In an acyclic quiver every vertex is loopless, by
`TauCeti.Quiver.IsAcyclic.isEmpty_hom_self`.

The reflection of the quiver itself, which reverses the arrows at `i`, is
`TauCeti.Quiver.Reflect` in `TauCeti.RepresentationTheory.Quiver.Reflection.Basic`;
`TauCeti.RepresentationTheory.Quiver.Reflection.EulerForm` relates the two.

## Main definitions and results

* `TauCeti.vertexPreReflection`: the map `sᵢ`, as a `ℤ`-linear endomorphism of the
  dimension-vector lattice, defined at every vertex.
* `TauCeti.vertexReflection`: the same map at a loopless vertex, where it is a genuine
  reflection, packaged as a linear automorphism.
* `TauCeti.titsForm_vertexPreReflection`: the simple reflection at a loopless vertex preserves
  the Tits form; `TauCeti.titsPolarForm_vertexPreReflection` is the bilinear counterpart.
* `TauCeti.bijOn_vertexPreReflection`: consequently the simple reflection permutes each level set
  of the Tits form, in particular the roots `q(d) = 1`.

## References

This implements the “simple reflection at a vertex” target of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 5 root-system
bridge consumes the symmetrized Gram matrix `TauCeti.titsPolarForm_single_single`. See
Derksen--Weyman, *An Introduction to Quiver Representations*.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q]

/-- The simple reflection `sᵢ` at a vertex `i`, acting on dimension vectors by
`d ↦ d - ⟨αᵢ, d⟩ αᵢ` for the polarized Tits form and the simple dimension vector
`αᵢ = Pi.single i 1`.

No hypothesis on `i` is imposed here, following `Module.preReflection`; the reflection identities
hold at a loopless vertex, where `⟨αᵢ, αᵢ⟩ = 2`, and there `vertexReflection` packages this map
as an automorphism. -/
noncomputable def vertexPreReflection (i : Q) : Module.End ℤ (Q → ℤ) :=
  Module.preReflection (Pi.single i 1) (titsPolarForm Q (Pi.single i 1))

/-- The defining formula for the simple reflection at a vertex. -/
theorem vertexPreReflection_apply (i : Q) (d : Q → ℤ) :
    vertexPreReflection Q i d = d - titsPolarForm Q (Pi.single i 1) d • Pi.single i 1 :=
  Module.preReflection_apply _ _ _

/-- Away from `i`, the simple reflection at `i` leaves a dimension vector unchanged. -/
theorem vertexPreReflection_apply_of_ne (i : Q) (d : Q → ℤ) {v : Q} (hv : v ≠ i) :
    vertexPreReflection Q i d v = d v := by
  rw [vertexPreReflection_apply]
  simp [Pi.single_apply, hv]

/-- The coordinate of the simple reflection at the reflected vertex. -/
theorem vertexPreReflection_apply_self (i : Q) (d : Q → ℤ) :
    vertexPreReflection Q i d i
      = -d i + ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [vertexPreReflection_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
    titsPolarForm_single_left]
  ring

/-- At a loopless vertex the reflected coordinate is the classical formula
`-dᵢ + ∑_{v ≠ i} (#(i ⟶ v) + #(v ⟶ i)) d_v`, the sum running over the neighbours of `i`. -/
theorem vertexPreReflection_apply_self_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) (d : Q → ℤ) :
    vertexPreReflection Q i d i
      = -d i + ∑ v ∈ Finset.univ.erase i,
          ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [vertexPreReflection_apply_self,
    ← Finset.add_sum_erase _ (fun v ↦ ((Fintype.card (i ⟶ v) : ℤ) +
      (Fintype.card (v ⟶ i) : ℤ)) * d v) (Finset.mem_univ i)]
  rw [Fintype.card_eq_zero_iff.mpr h]
  ring

/-- The simple reflection at a loopless vertex negates the corresponding simple dimension
vector. -/
@[simp]
theorem vertexPreReflection_single_self {i : Q} (h : IsEmpty (i ⟶ i)) :
    vertexPreReflection Q i (Pi.single i 1) = -Pi.single i 1 :=
  Module.preReflection_apply_self (titsPolarForm_single_self_of_isEmpty Q h)

/-- The simple reflection at `i` adds a multiple of `αᵢ` to any other simple dimension vector, the
multiple being the number of arrows joining the two vertices in either direction. -/
theorem vertexPreReflection_single_of_ne (i : Q) {j : Q} (hj : j ≠ i) :
    vertexPreReflection Q i (Pi.single j 1)
      = Pi.single j 1
        + ((Fintype.card (i ⟶ j) : ℤ) + (Fintype.card (j ⟶ i) : ℤ)) • Pi.single i 1 := by
  rw [vertexPreReflection_apply, titsPolarForm_single_single, if_neg (Ne.symm hj), mul_zero,
    zero_sub, neg_smul, sub_neg_eq_add]

/-- The simple reflection fixes every dimension vector orthogonal to `αᵢ` for the polarized Tits
form. -/
theorem vertexPreReflection_apply_of_titsPolarForm_eq_zero (i : Q) {d : Q → ℤ}
    (hd : titsPolarForm Q (Pi.single i 1) d = 0) :
    vertexPreReflection Q i d = d := by
  rw [vertexPreReflection_apply, hd, zero_smul, sub_zero]

/-- The simple reflection at a loopless vertex is an involution. -/
theorem involutive_vertexPreReflection {i : Q} (h : IsEmpty (i ⟶ i)) :
    Function.Involutive (vertexPreReflection Q i) :=
  Module.involutive_preReflection (titsPolarForm_single_self_of_isEmpty Q h)

/-- The simple reflection at a loopless vertex, as a linear automorphism of the dimension-vector
lattice. -/
noncomputable def vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) : (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ) :=
  Module.reflection (titsPolarForm_single_self_of_isEmpty Q h)

@[simp]
theorem coe_vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) :
    ⇑(vertexReflection Q h) = ⇑(vertexPreReflection Q i) := by
  funext d
  exact (Module.reflection_apply d (titsPolarForm_single_self_of_isEmpty Q h)).trans
    (vertexPreReflection_apply Q i d).symm

/-- The simple reflection at a loopless vertex is its own inverse. -/
@[simp]
theorem vertexReflection_symm {i : Q} (h : IsEmpty (i ⟶ i)) :
    (vertexReflection Q h).symm = vertexReflection Q h :=
  Module.reflection_symm _

/-! ### Invariance of the Tits form -/

/-- The simple reflection at a loopless vertex preserves the Tits form. -/
theorem titsForm_vertexPreReflection {i : Q} (h : IsEmpty (i ⟶ i)) (d : Q → ℤ) :
    titsForm Q (vertexPreReflection Q i d) = titsForm Q d := by
  set c := titsPolarForm Q (Pi.single i 1) d with hc
  have hsingle : titsForm Q (c • Pi.single i (1 : ℤ)) = c * c := by
    rw [QuadraticMap.map_smul, titsForm_single_of_isEmpty Q h, smul_eq_mul, mul_one]
  have hpolar : titsPolarForm Q d (c • Pi.single i (1 : ℤ)) = c * c := by
    rw [map_smul, smul_eq_mul, titsPolarForm_comm, ← hc]
  rw [vertexPreReflection_apply, titsForm_sub, hsingle, hpolar]
  ring

/-- The simple reflection at a loopless vertex preserves the polarized Tits form. -/
theorem titsPolarForm_vertexPreReflection {i : Q} (h : IsEmpty (i ⟶ i)) (d e : Q → ℤ) :
    titsPolarForm Q (vertexPreReflection Q i d) (vertexPreReflection Q i e)
      = titsPolarForm Q d e := by
  have hadd := titsForm_add Q (vertexPreReflection Q i d) (vertexPreReflection Q i e)
  rw [← map_add, titsForm_vertexPreReflection Q h, titsForm_vertexPreReflection Q h,
    titsForm_vertexPreReflection Q h] at hadd
  have := titsForm_add Q d e
  linarith

/-- The simple reflection at a loopless vertex permutes every level set of the Tits form; taking
the level `1` this says that it permutes the roots of `Q`. -/
theorem bijOn_vertexPreReflection {i : Q} (h : IsEmpty (i ⟶ i)) (n : ℤ) :
    Set.BijOn (vertexPreReflection Q i) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
  have hmaps : Set.MapsTo (vertexReflection Q h) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
    intro d hd
    simpa only [Set.mem_ofPred_eq, coe_vertexReflection, titsForm_vertexPreReflection Q h]
      using hd
  rw [← coe_vertexReflection Q h]
  exact Module.bijOn_reflection_of_mapsTo (titsPolarForm_single_self_of_isEmpty Q h) hmaps

end TauCeti
