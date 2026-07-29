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
polarized Tits form paired with `αᵢ`. This makes `TauCeti.vertexReflection` available with no
hypothesis on `i`; the reflection identities need `q(αᵢ) = 1`, equivalently that `i` carries no
loop, and that hypothesis is carried explicitly by the lemmas that need it. In an acyclic quiver
every vertex is loopless, by `TauCeti.Quiver.IsAcyclic.isEmpty_hom_self`.

## Main definitions and results

* `TauCeti.vertexReflection`: the simple reflection `sᵢ`, as a `ℤ`-linear endomorphism of the
  dimension-vector lattice.
* `TauCeti.vertexReflectionEquiv`: the same map at a loopless vertex, packaged as a linear
  automorphism.
* `TauCeti.titsPolarForm_single_single`: the Gram matrix of the polarized Tits form in the simple
  dimension vectors is `2·I - (A + Aᵀ)` for the arrow-count matrix `A`, the symmetrized Cartan
  matrix of the quiver.
* `TauCeti.titsForm_vertexReflection`: the simple reflection at a loopless vertex preserves the
  Tits form; `TauCeti.titsPolarForm_vertexReflection` is the bilinear counterpart.
* `TauCeti.bijOn_vertexReflection`: consequently the simple reflection permutes each level set of
  the Tits form, in particular the roots `q(d) = 1`.

## References

This implements the “simple reflection at a vertex” target of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 5 root-system
bridge consumes the symmetrized Gram matrix computed here. See Derksen--Weyman, *An Introduction
to Quiver Representations*.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q]

/-! ### The Euler and Tits forms in the simple dimension vectors -/

/-- The Euler form with a simple dimension vector on the left counts the arrows out of `i`. -/
theorem eulerForm_single_left (i : Q) (e : Q → ℤ) :
    eulerForm Q (Pi.single i 1) e = e i - ∑ b : Q, (Fintype.card (i ⟶ b) : ℤ) * e b := by
  have h₁ : ∑ v : Q, (Pi.single i 1 : Q → ℤ) v * e v = e i := by
    simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']
  have h₂ : ∀ a : Q, (∑ b : Q, ∑ _f : a ⟶ b, (Pi.single i 1 : Q → ℤ) a * e b)
      = (Pi.single i 1 : Q → ℤ) a * ∑ b : Q, (Fintype.card (a ⟶ b) : ℤ) * e b := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [eulerForm_def, h₁, Finset.sum_congr rfl fun a _ ↦ h₂ a]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- The Euler form with a simple dimension vector on the right counts the arrows into `j`. -/
theorem eulerForm_single_right (d : Q → ℤ) (j : Q) :
    eulerForm Q d (Pi.single j 1) = d j - ∑ a : Q, (Fintype.card (a ⟶ j) : ℤ) * d a := by
  have h₁ : ∑ v : Q, d v * (Pi.single j 1 : Q → ℤ) v = d j := by
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  have h₂ : ∀ a : Q, (∑ b : Q, ∑ _f : a ⟶ b, d a * (Pi.single j 1 : Q → ℤ) b)
      = (Fintype.card (a ⟶ j) : ℤ) * d a := by
    intro a
    have h₃ : ∀ b : Q, (∑ _f : a ⟶ b, d a * (Pi.single j 1 : Q → ℤ) b)
        = if b = j then (Fintype.card (a ⟶ b) : ℤ) * d a else 0 := by
      intro b
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Pi.single_apply]
      split <;> simp
    rw [Finset.sum_congr rfl fun b _ ↦ h₃ b, Finset.sum_ite_eq' Finset.univ j]
    simp
  rw [eulerForm_def, h₁, Finset.sum_congr rfl fun a _ ↦ h₂ a]

/-- The Euler form in the simple dimension vectors: `⟨αᵢ, αⱼ⟩ = δᵢⱼ - #(i ⟶ j)`. -/
theorem eulerForm_single_single (i j : Q) :
    eulerForm Q (Pi.single i 1) (Pi.single j 1)
      = (if i = j then 1 else 0) - (Fintype.card (i ⟶ j) : ℤ) := by
  rw [eulerForm_single_left]
  simp [Pi.single_apply, mul_ite, eq_comm]

/-- The Tits form of a simple dimension vector counts the loops at that vertex. -/
theorem titsForm_single (i : Q) :
    titsForm Q (Pi.single i 1) = 1 - (Fintype.card (i ⟶ i) : ℤ) := by
  rw [titsForm_def, eulerForm_single_single]
  simp

/-- A loopless vertex has a simple dimension vector of Tits norm one, that is, `αᵢ` is a root. -/
theorem titsForm_single_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) :
    titsForm Q (Pi.single i 1) = 1 := by
  rw [titsForm_single, Fintype.card_eq_zero_iff.mpr h]
  simp

/-- The polarized Tits form against a simple dimension vector, in coordinates. -/
theorem titsPolarForm_single_left (i : Q) (d : Q → ℤ) :
    titsPolarForm Q (Pi.single i 1) d
      = 2 * d i - ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [titsPolarForm_def, eulerForm_single_left, eulerForm_single_right]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- The polarized Tits form against a simple dimension vector on the right, in coordinates. -/
theorem titsPolarForm_single_right (d : Q → ℤ) (i : Q) :
    titsPolarForm Q d (Pi.single i 1)
      = 2 * d i - ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [titsPolarForm_comm, titsPolarForm_single_left]

/-- The Gram matrix of the polarized Tits form in the simple dimension vectors is
`2·I - (A + Aᵀ)`, for `A` the matrix of arrow counts: the symmetrized Cartan matrix of `Q`. -/
theorem titsPolarForm_single_single (i j : Q) :
    titsPolarForm Q (Pi.single i 1) (Pi.single j 1)
      = 2 * (if i = j then 1 else 0)
        - ((Fintype.card (i ⟶ j) : ℤ) + (Fintype.card (j ⟶ i) : ℤ)) := by
  rw [titsPolarForm_def, eulerForm_single_single, eulerForm_single_single]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos (rfl : i = i)]
    ring
  · rw [if_neg hij, if_neg hij.symm]
    ring

/-- A loopless vertex has `⟨αᵢ, αᵢ⟩ = 2` for the polarized Tits form: the normalization that
makes the simple reflection at `i` an involution. -/
theorem titsPolarForm_single_self_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) :
    titsPolarForm Q (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [titsPolarForm_single_single, Fintype.card_eq_zero_iff.mpr h]
  simp

/-! ### The simple reflection at a vertex -/

/-- The simple reflection `sᵢ` at a vertex `i`, acting on dimension vectors by
`d ↦ d - ⟨αᵢ, d⟩ αᵢ` for the polarized Tits form and the simple dimension vector
`αᵢ = Pi.single i 1`.

No hypothesis on `i` is imposed here, following `Module.preReflection`; the reflection identities
hold at a loopless vertex, where `⟨αᵢ, αᵢ⟩ = 2`. -/
noncomputable def vertexReflection (i : Q) : Module.End ℤ (Q → ℤ) :=
  Module.preReflection (Pi.single i 1) (titsPolarForm Q (Pi.single i 1))

/-- The defining formula for the simple reflection at a vertex. -/
theorem vertexReflection_apply (i : Q) (d : Q → ℤ) :
    vertexReflection Q i d = d - titsPolarForm Q (Pi.single i 1) d • Pi.single i 1 :=
  Module.preReflection_apply _ _ _

/-- Away from `i`, the simple reflection at `i` leaves a dimension vector unchanged. -/
theorem vertexReflection_apply_of_ne (i : Q) (d : Q → ℤ) {v : Q} (hv : v ≠ i) :
    vertexReflection Q i d v = d v := by
  rw [vertexReflection_apply]
  simp [Pi.single_apply, hv]

/-- The coordinate of the simple reflection at the reflected vertex. -/
theorem vertexReflection_apply_self (i : Q) (d : Q → ℤ) :
    vertexReflection Q i d i
      = -d i + ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [vertexReflection_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
    titsPolarForm_single_left]
  ring

/-- At a loopless vertex the reflected coordinate is the classical formula
`-dᵢ + ∑_{v ≠ i} (#(i ⟶ v) + #(v ⟶ i)) d_v`, the sum running over the neighbours of `i`. -/
theorem vertexReflection_apply_self_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) (d : Q → ℤ) :
    vertexReflection Q i d i
      = -d i + ∑ v ∈ Finset.univ.erase i,
          ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [vertexReflection_apply_self,
    ← Finset.add_sum_erase _ (fun v ↦ ((Fintype.card (i ⟶ v) : ℤ) +
      (Fintype.card (v ⟶ i) : ℤ)) * d v) (Finset.mem_univ i)]
  rw [Fintype.card_eq_zero_iff.mpr h]
  ring

/-- The simple reflection at a loopless vertex negates the corresponding simple dimension
vector. -/
theorem vertexReflection_single_self {i : Q} (h : IsEmpty (i ⟶ i)) :
    vertexReflection Q i (Pi.single i 1) = -Pi.single i 1 :=
  Module.preReflection_apply_self (titsPolarForm_single_self_of_isEmpty Q h)

/-- The simple reflection at `i` adds a multiple of `αᵢ` to any other simple dimension vector, the
multiple being the number of arrows joining the two vertices in either direction. -/
theorem vertexReflection_single_of_ne (i : Q) {j : Q} (hj : j ≠ i) :
    vertexReflection Q i (Pi.single j 1)
      = Pi.single j 1
        + ((Fintype.card (i ⟶ j) : ℤ) + (Fintype.card (j ⟶ i) : ℤ)) • Pi.single i 1 := by
  rw [vertexReflection_apply, titsPolarForm_single_single, if_neg (Ne.symm hj), mul_zero,
    zero_sub, neg_smul, sub_neg_eq_add]

/-- The simple reflection fixes every dimension vector orthogonal to `αᵢ` for the polarized Tits
form. -/
theorem vertexReflection_apply_of_titsPolarForm_eq_zero (i : Q) {d : Q → ℤ}
    (hd : titsPolarForm Q (Pi.single i 1) d = 0) :
    vertexReflection Q i d = d := by
  rw [vertexReflection_apply, hd, zero_smul, sub_zero]

/-- The simple reflection at a loopless vertex is an involution. -/
theorem involutive_vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) :
    Function.Involutive (vertexReflection Q i) :=
  Module.involutive_preReflection (titsPolarForm_single_self_of_isEmpty Q h)

/-- The simple reflection at a loopless vertex, as a linear automorphism of the dimension-vector
lattice. -/
noncomputable def vertexReflectionEquiv {i : Q} (h : IsEmpty (i ⟶ i)) : (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ) :=
  Module.reflection (titsPolarForm_single_self_of_isEmpty Q h)

@[simp]
theorem coe_vertexReflectionEquiv {i : Q} (h : IsEmpty (i ⟶ i)) :
    ⇑(vertexReflectionEquiv Q h) = ⇑(vertexReflection Q i) := by
  funext d
  exact (Module.reflection_apply d (titsPolarForm_single_self_of_isEmpty Q h)).trans
    (vertexReflection_apply Q i d).symm

/-! ### Invariance of the Tits form -/

/-- The simple reflection at a loopless vertex preserves the Tits form. -/
theorem titsForm_vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) (d : Q → ℤ) :
    titsForm Q (vertexReflection Q i d) = titsForm Q d := by
  set c := titsPolarForm Q (Pi.single i 1) d with hc
  have hsingle : titsForm Q (c • Pi.single i (1 : ℤ)) = c * c := by
    rw [QuadraticMap.map_smul, titsForm_single_of_isEmpty Q h, smul_eq_mul, mul_one]
  have hpolar : titsPolarForm Q d (c • Pi.single i (1 : ℤ)) = c * c := by
    rw [map_smul, smul_eq_mul, titsPolarForm_comm, ← hc]
  rw [vertexReflection_apply, titsForm_sub, hsingle, hpolar]
  ring

/-- The simple reflection at a loopless vertex preserves the polarized Tits form. -/
theorem titsPolarForm_vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) (d e : Q → ℤ) :
    titsPolarForm Q (vertexReflection Q i d) (vertexReflection Q i e)
      = titsPolarForm Q d e := by
  have hadd := titsForm_add Q (vertexReflection Q i d) (vertexReflection Q i e)
  rw [← map_add, titsForm_vertexReflection Q h, titsForm_vertexReflection Q h,
    titsForm_vertexReflection Q h] at hadd
  have := titsForm_add Q d e
  linarith

/-- The simple reflection at a loopless vertex permutes every level set of the Tits form; taking
the level `1` this says that it permutes the roots of `Q`. -/
theorem bijOn_vertexReflection {i : Q} (h : IsEmpty (i ⟶ i)) (n : ℤ) :
    Set.BijOn (vertexReflection Q i) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
  have hmaps : Set.MapsTo (vertexReflectionEquiv Q h) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
    intro d hd
    simpa only [Set.mem_setOf_eq, coe_vertexReflectionEquiv, titsForm_vertexReflection Q h]
      using hd
  rw [← coe_vertexReflectionEquiv Q h]
  exact Module.bijOn_reflection_of_mapsTo (titsPolarForm_single_self_of_isEmpty Q h) hmaps

end TauCeti
