/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector

/-!
# The Coxeter transformation on the dimension vectors of a quiver

Composing the simple reflections of a finite quiver `Q` at the successive vertices of a word
`l = [i₁, …, iₙ]` gives the endomorphism `sᵢₙ ∘ ⋯ ∘ sᵢ₁` of the dimension-vector lattice `Q → ℤ`.
The Coxeter transformation is the case of a word listing every vertex exactly once, taken in a
sink-admissible order; it is the numerical shadow of the Coxeter functor, the composite of the
Bernstein-Gelfand-Ponomarev reflection functors at `i₁, …, iₙ`: each reflection functor acts on
dimension vectors by the simple reflection at its vertex
(`TauCeti.dimVector_reflectRep_of_indecomposable`), and reflecting the quiver itself changes
neither the polarized Tits form nor the simple reflections built from it
(`TauCeti.vertexPreReflection_reflect_apply`), so the successive reflections may all be read in
the original quiver.

Following `TauCeti.vertexPreReflection`, the composite is defined for an arbitrary word, and the
results that need the Coxeter case say so through explicit `List.Nodup` and vertex-exhaustion
hypotheses.

The main result is that this composite has **no nonzero fixed vector** once the word runs over
every vertex without repetition and the polarized Tits form has trivial radical, in particular
whenever the Tits form is anisotropic, and so for a quiver of ADE type, where the Tits form is
positive definite and `QuadraticMap.PosDef.anisotropic` applies. This is the engine of the
Bernstein-Gelfand-Ponomarev proof of Gabriel's theorem that forbids a nonzero dimension vector from
being carried to itself after a full pass of the Coxeter functor. The separate positive-root height
argument supplies the descent to a vertex simple.

## Main definitions and results

* `TauCeti.vertexPreReflectionList`: the composite of the simple reflections along a word in the
  vertices, as a `ℤ`-linear endomorphism of the dimension-vector lattice. As with
  `TauCeti.vertexPreReflection`, no hypothesis on the vertices is imposed.
* `TauCeti.vertexReflectionList`: the same map as a linear automorphism, over a word in loopless
  vertices, with `TauCeti.coe_vertexReflectionList_symm` identifying its inverse as the composite
  along the reversed word.
* `TauCeti.titsForm_vertexPreReflectionList` and
  `TauCeti.bijOn_vertexPreReflectionList`: the composite preserves the Tits form, and hence
  permutes each of its level sets, in particular the roots `q(d) = 1`.
* `TauCeti.titsPolarForm_eq_zero_of_vertexPreReflectionList_eq_self`: a vector fixed by the
  composite along a repetition-free word in all the vertices lies in the radical of the polarized
  Tits form.
* `TauCeti.vertexPreReflectionList_eq_self_iff`: consequently, once that radical is trivial the only
  fixed vector is `0`; `TauCeti.vertexPreReflectionList_eq_self_iff_of_anisotropic` is the same
  statement for an anisotropic Tits form.

## References

This implements the Coxeter-element half of the "Coxeter functor" target of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, which the reflection
induction of Layer 5 consumes. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's
theorem*, and Derksen--Weyman, *An Introduction to Quiver Representations*.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q]

/-- The composite of the simple reflections at the vertices of a word, applied in the order in
which they are listed, so that `l = [i₁, …, iₙ]` gives `sᵢₙ ∘ ⋯ ∘ sᵢ₁`. Over a repetition-free
word running through all the vertices this is the Coxeter transformation.

No hypothesis on the vertices is imposed here, following `TauCeti.vertexPreReflection`; over a
word in loopless vertices `TauCeti.vertexReflectionList` packages this map as an
automorphism. -/
noncomputable def vertexPreReflectionList (l : List Q) : Module.End ℤ (Q → ℤ) :=
  (l.reverse.map (vertexPreReflection Q)).prod

@[simp]
theorem vertexPreReflectionList_nil : vertexPreReflectionList Q [] = 1 := by
  simp [vertexPreReflectionList]

/-- The vertex at the head of the word is reflected first. -/
@[simp]
theorem vertexPreReflectionList_cons (i : Q) (l : List Q) :
    vertexPreReflectionList Q (i :: l)
      = vertexPreReflectionList Q l * vertexPreReflection Q i := by
  simp [vertexPreReflectionList]

/-- The vertex at the head of the word is reflected first, in applied form. -/
theorem vertexPreReflectionList_apply_cons (i : Q) (l : List Q) (d : Q → ℤ) :
    vertexPreReflectionList Q (i :: l) d
      = vertexPreReflectionList Q l (vertexPreReflection Q i d) := by
  rw [vertexPreReflectionList_cons, Module.End.mul_apply]

/-- Concatenating two words composes their reflection products, the first word acting first. -/
theorem vertexPreReflectionList_append (l₁ l₂ : List Q) :
    vertexPreReflectionList Q (l₁ ++ l₂)
      = vertexPreReflectionList Q l₂ * vertexPreReflectionList Q l₁ := by
  simp [vertexPreReflectionList, List.map_append, List.prod_append]

/-- Off the word, the reflection product changes no coordinate: each simple reflection in the
composite alters only the coordinate at its own vertex. -/
@[simp]
theorem vertexPreReflectionList_apply_of_notMem {l : List Q} {i : Q} (hi : i ∉ l) (d : Q → ℤ) :
    vertexPreReflectionList Q l d i = d i := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [List.mem_cons, not_or] at hi
    rw [vertexPreReflectionList_apply_cons, ih hi.2, vertexPreReflection_apply_of_ne Q j d hi.1]

/-! ### Invariance of the Tits form -/

/-- The reflection product along a word in loopless vertices preserves the Tits form. -/
theorem titsForm_vertexPreReflectionList {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d : Q → ℤ) : titsForm Q (vertexPreReflectionList Q l d) = titsForm Q d := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [vertexPreReflectionList_apply_cons, ih (fun i hi ↦ hl i (by simp [hi])),
      titsForm_vertexPreReflection Q (hl j (by simp))]

/-- The reflection product along a word in loopless vertices preserves the polarized Tits
form. -/
theorem titsPolarForm_vertexPreReflectionList {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d e : Q → ℤ) :
    titsPolarForm Q (vertexPreReflectionList Q l d) (vertexPreReflectionList Q l e)
      = titsPolarForm Q d e := by
  induction l generalizing d e with
  | nil => simp
  | cons j l ih =>
    rw [vertexPreReflectionList_apply_cons, vertexPreReflectionList_apply_cons,
      ih (fun i hi ↦ hl i (by simp [hi])), titsPolarForm_vertexPreReflection Q (hl j (by simp))]

/-! ### The Coxeter transformation as an automorphism -/

/-- The reflection product along a word in loopless vertices, as a linear automorphism of the
dimension-vector lattice; over a repetition-free word running through all the vertices this is the
Coxeter transformation. -/
noncomputable def vertexReflectionList {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ) :=
  ((l.attach.map fun i : {i // i ∈ l} ↦ vertexReflection Q (hl i.1 i.2)).reverse).prod

private theorem map_vertexReflection_toLinearMap {l : List Q}
    (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    (l.attach.map fun i : {i // i ∈ l} ↦ vertexReflection Q (hl i.1 i.2)).map
        (fun e ↦ e.toLinearMap)
      = l.map (vertexPreReflection Q) := by
  rw [List.map_map]
  rw [← List.attach_map_val (f := vertexPreReflection Q)]
  apply List.map_congr_left
  intro i hi
  apply LinearMap.coe_injective
  exact coe_vertexReflection Q (hl i.1 i.2)

omit [Quiver Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)] [DecidableEq Q] in
private theorem toLinearMap_list_prod
    (L : List ((Q → ℤ) ≃ₗ[ℤ] (Q → ℤ))) :
    L.prod.toLinearMap = (L.map fun e ↦ e.toLinearMap).prod := by
  calc
    _ = (L.map (LinearEquiv.automorphismGroup.toLinearMapMonoidHom :
        ((Q → ℤ) ≃ₗ[ℤ] (Q → ℤ)) →* Module.End ℤ (Q → ℤ))).prod :=
      map_list_prod (LinearEquiv.automorphismGroup.toLinearMapMonoidHom :
        ((Q → ℤ) ≃ₗ[ℤ] (Q → ℤ)) →* Module.End ℤ (Q → ℤ)) L
    _ = _ := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      exact LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply e

/-- Coercing the reflection automorphism along a word to a function gives the corresponding
pre-reflection product. -/
@[simp]
theorem coe_vertexReflectionList {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    ⇑(vertexReflectionList Q hl) = ⇑(vertexPreReflectionList Q l) := by
  have h : (vertexReflectionList Q hl).toLinearMap = vertexPreReflectionList Q l := by
    rw [vertexReflectionList, vertexPreReflectionList, toLinearMap_list_prod, List.map_reverse,
      map_vertexReflection_toLinearMap Q hl, List.map_reverse]
  rw [← LinearEquiv.coe_coe]
  exact congrArg (fun f : Module.End ℤ (Q → ℤ) ↦ (f : (Q → ℤ) → (Q → ℤ))) h

/-- The reflection product along a word in loopless vertices is bijective. -/
theorem vertexPreReflectionList_bijective {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    Function.Bijective (vertexPreReflectionList Q l) := by
  rw [← coe_vertexReflectionList Q hl]
  exact (vertexReflectionList Q hl).bijective

/-- The inverse automorphism is the reflection product along the reversed word. -/
@[simp]
theorem coe_vertexReflectionList_symm {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    ⇑(vertexReflectionList Q hl).symm = ⇑(vertexPreReflectionList Q l.reverse) := by
  have hinv : (vertexReflectionList Q hl).symm =
      (l.attach.map fun i : {i // i ∈ l} ↦ vertexReflection Q (hl i.1 i.2)).prod := by
    rw [vertexReflectionList]
    -- `LinearEquiv.automorphismGroup` defines group inversion as `LinearEquiv.symm`; exposing that
    -- operation lets `List.prod_reverse_noncomm` compute the inverse of the reversed product.
    change ((l.attach.map fun i : {i // i ∈ l} ↦
      vertexReflection Q (hl i.1 i.2)).reverse.prod)⁻¹ = _
    rw [List.prod_reverse_noncomm]
    simp only [inv_inv, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact vertexReflection_symm Q (hl i.1 i.2)
  have h : (vertexReflectionList Q hl).symm.toLinearMap =
      vertexPreReflectionList Q l.reverse := by
    rw [hinv, vertexPreReflectionList, List.reverse_reverse, toLinearMap_list_prod,
      map_vertexReflection_toLinearMap Q hl]
  rw [← LinearEquiv.coe_coe]
  exact congrArg (fun f : Module.End ℤ (Q → ℤ) ↦ (f : (Q → ℤ) → (Q → ℤ))) h

/-- Composing the pre-reflection lists for a word and its reverse gives the identity. -/
theorem vertexPreReflectionList_reverse_mul {l : List Q}
    (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    vertexPreReflectionList Q l.reverse * vertexPreReflectionList Q l = 1 := by
  apply LinearMap.ext
  intro d
  rw [Module.End.mul_apply, Module.End.one_apply, ← coe_vertexReflectionList_symm Q hl,
    ← coe_vertexReflectionList Q hl]
  exact (vertexReflectionList Q hl).symm_apply_apply d

/-- The reflection product along a word in loopless vertices permutes every level set of the
Tits form; at the level `1` this says that it permutes the roots of `Q`. -/
theorem bijOn_vertexPreReflectionList {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (n : ℤ) :
    Set.BijOn (vertexPreReflectionList Q l) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
  have h : vertexPreReflectionList Q l ⁻¹' {d : Q → ℤ | titsForm Q d = n}
      = {d : Q → ℤ | titsForm Q d = n} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, titsForm_vertexPreReflectionList Q hl]
  have hbij := (vertexPreReflectionList_bijective Q hl).bijOn_preimage
    (t := {d : Q → ℤ | titsForm Q d = n})
  rwa [h] at hbij

/-! ### Fixed vectors -/

/-- A vector fixed by the reflection product along a repetition-free word is orthogonal, for the
polarized Tits form, to the simple dimension vector at every vertex of that word. -/
theorem titsPolarForm_single_eq_zero_of_vertexPreReflectionList_eq_self {l : List Q}
    (hnd : l.Nodup) {v : Q → ℤ} (hv : vertexPreReflectionList Q l v = v) {i : Q} (hi : i ∈ l) :
    titsPolarForm Q (Pi.single i 1) v = 0 := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hjl, hnd'⟩ := List.nodup_cons.mp hnd
    -- The head `j` occurs nowhere else in the word, so the remaining reflections leave the `j`-th
    -- coordinate of `sⱼ v` untouched.
    have hcoord : vertexPreReflectionList Q (j :: l) v j
        = v j - titsPolarForm Q (Pi.single j 1) v := by
      rw [vertexPreReflectionList_apply_cons,
        vertexPreReflectionList_apply_of_notMem Q hjl, vertexPreReflection_apply]
      simp
    -- The `j`-th coordinate of the fixed-point equation therefore reads `vⱼ - ⟨αⱼ, v⟩ = vⱼ`.
    rw [hv] at hcoord
    have hj : titsPolarForm Q (Pi.single j 1) v = 0 := by omega
    -- Then `sⱼ` fixes `v`, so the tail of the word fixes `v` as well.
    have hfix : vertexPreReflection Q j v = v :=
      vertexPreReflection_apply_of_titsPolarForm_eq_zero Q j hj
    rw [vertexPreReflectionList_apply_cons, hfix] at hv
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact hj
    · exact ih hnd' hv hi'

/-- A vector fixed by the reflection product along a repetition-free word in *all* the vertices
lies in the radical of the polarized Tits form. -/
theorem titsPolarForm_eq_zero_of_vertexPreReflectionList_eq_self {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) {v : Q → ℤ} (hv : vertexPreReflectionList Q l v = v) (d : Q → ℤ) :
    titsPolarForm Q d v = 0 := by
  have hsingle : ∀ i : Q, titsPolarForm Q (Pi.single i 1) v = 0 := fun i ↦
    titsPolarForm_single_eq_zero_of_vertexPreReflectionList_eq_self Q hnd hv (hmem i)
  rw [pi_eq_sum_univ' d, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hsingle i, mul_zero]

/-- **The Coxeter transformation of a quiver whose polarized Tits form has trivial radical fixes
only the zero vector**, as soon as the word of vertices it is taken along is repetition-free and
exhausts the vertices.

This fixed-point obstruction is one input to the reflection induction behind Gabriel's theorem: no
nonzero dimension vector survives a full pass of the Coxeter functor unchanged. The descent itself
requires a separate positive-root height argument. An anisotropic Tits form has trivial radical,
which is the form the hypothesis takes in
`TauCeti.vertexPreReflectionList_eq_self_iff_of_anisotropic`. -/
theorem vertexPreReflectionList_eq_self_iff
    (hsep : LinearMap.SeparatingRight (titsPolarForm Q)) {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    vertexPreReflectionList Q l v = v ↔ v = 0 :=
  ⟨fun hv ↦ hsep v (titsPolarForm_eq_zero_of_vertexPreReflectionList_eq_self Q hnd hmem hv),
    fun hv ↦ by rw [hv, map_zero]⟩

/-- **The Coxeter transformation of a quiver with anisotropic Tits form fixes only the zero
vector**: a vector in the radical of the polarized form is isotropic, since `⟨v, v⟩ = 2 q(v)`.

For a quiver of ADE type the Tits form is positive definite, and
`QuadraticMap.PosDef.anisotropic` supplies the hypothesis. -/
theorem vertexPreReflectionList_eq_self_iff_of_anisotropic (hani : (titsForm Q).Anisotropic)
    {l : List Q} (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    vertexPreReflectionList Q l v = v ↔ v = 0 := by
  refine vertexPreReflectionList_eq_self_iff Q (fun w hw ↦ hani w ?_) hnd hmem v
  have h := hw w
  rw [titsPolarForm_def, ← titsForm_def] at h
  omega

end TauCeti
