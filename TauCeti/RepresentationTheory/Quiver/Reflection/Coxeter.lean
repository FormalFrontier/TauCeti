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
Bernstein-Gelfand-Ponomarev proof of Gabriel's theorem: it is what forbids an indecomposable
representation from being carried to itself by the Coxeter functor, and so forces the reflection
induction to descend to a vertex simple.

## Main definitions and results

* `TauCeti.vertexPreReflectionProd`: the composite of the simple reflections along a word in the
  vertices, as a `ℤ`-linear endomorphism of the dimension-vector lattice. As with
  `TauCeti.vertexPreReflection`, no hypothesis on the vertices is imposed.
* `TauCeti.vertexReflectionProd`: the same map as a linear automorphism, over a word in loopless
  vertices, with `TauCeti.coe_vertexReflectionProd_symm` identifying its inverse as the composite
  along the reversed word.
* `TauCeti.titsForm_vertexPreReflectionProd` and
  `TauCeti.bijOn_vertexPreReflectionProd`: the composite preserves the Tits form, and hence
  permutes each of its level sets, in particular the roots `q(d) = 1`.
* `TauCeti.titsPolarForm_eq_zero_of_vertexPreReflectionProd_eq_self`: a vector fixed by the
  composite along a repetition-free word in all the vertices lies in the radical of the polarized
  Tits form.
* `TauCeti.vertexPreReflectionProd_eq_self_iff` and
  `TauCeti.vertexReflectionProd_eq_self_iff`: consequently, once that radical is trivial the only
  fixed vector is `0`;
  `TauCeti.vertexPreReflectionProd_eq_self_iff_of_anisotropic` and
  `TauCeti.vertexReflectionProd_eq_self_iff_of_anisotropic` are the same statements for an
  anisotropic Tits form.

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
word in loopless vertices `TauCeti.vertexReflectionProd` packages this map as an
automorphism. -/
noncomputable def vertexPreReflectionProd (l : List Q) : Module.End ℤ (Q → ℤ) :=
  (l.reverse.map (vertexPreReflection Q)).prod

@[simp]
theorem vertexPreReflectionProd_nil : vertexPreReflectionProd Q [] = 1 := by
  simp [vertexPreReflectionProd]

/-- The vertex at the head of the word is reflected first. -/
@[simp]
theorem vertexPreReflectionProd_cons (i : Q) (l : List Q) :
    vertexPreReflectionProd Q (i :: l)
      = vertexPreReflectionProd Q l * vertexPreReflection Q i := by
  simp [vertexPreReflectionProd]

/-- The vertex at the head of the word is reflected first, in applied form. -/
theorem vertexPreReflectionProd_apply_cons (i : Q) (l : List Q) (d : Q → ℤ) :
    vertexPreReflectionProd Q (i :: l) d
      = vertexPreReflectionProd Q l (vertexPreReflection Q i d) := by
  rw [vertexPreReflectionProd_cons, Module.End.mul_apply]

/-- Concatenating two words composes their reflection products, the first word acting first. -/
theorem vertexPreReflectionProd_append (l₁ l₂ : List Q) :
    vertexPreReflectionProd Q (l₁ ++ l₂)
      = vertexPreReflectionProd Q l₂ * vertexPreReflectionProd Q l₁ := by
  simp [vertexPreReflectionProd, List.map_append, List.prod_append]

/-- Off the word, the reflection product changes no coordinate: each simple reflection in the
composite alters only the coordinate at its own vertex. -/
theorem vertexPreReflectionProd_apply_of_notMem {l : List Q} {i : Q} (hi : i ∉ l) (d : Q → ℤ) :
    vertexPreReflectionProd Q l d i = d i := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [List.mem_cons, not_or] at hi
    rw [vertexPreReflectionProd_apply_cons, ih hi.2, vertexPreReflection_apply_of_ne Q j d hi.1]

/-! ### Invariance of the Tits form -/

/-- The reflection product along a word in loopless vertices preserves the Tits form. -/
theorem titsForm_vertexPreReflectionProd {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d : Q → ℤ) : titsForm Q (vertexPreReflectionProd Q l d) = titsForm Q d := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [vertexPreReflectionProd_apply_cons, ih (fun i hi ↦ hl i (by simp [hi])),
      titsForm_vertexPreReflection Q (hl j (by simp))]

/-- The reflection product along a word in loopless vertices preserves the polarized Tits
form. -/
theorem titsPolarForm_vertexPreReflectionProd {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d e : Q → ℤ) :
    titsPolarForm Q (vertexPreReflectionProd Q l d) (vertexPreReflectionProd Q l e)
      = titsPolarForm Q d e := by
  induction l generalizing d e with
  | nil => simp
  | cons j l ih =>
    rw [vertexPreReflectionProd_apply_cons, vertexPreReflectionProd_apply_cons,
      ih (fun i hi ↦ hl i (by simp [hi])), titsPolarForm_vertexPreReflection Q (hl j (by simp))]

/-! ### The Coxeter transformation as an automorphism -/

/-- Over loopless vertices the reversed word undoes the word: the simple reflections are
involutions, and are unwound from the outside in. -/
theorem vertexPreReflectionProd_reverse_apply {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d : Q → ℤ) :
    vertexPreReflectionProd Q l.reverse (vertexPreReflectionProd Q l d) = d := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [List.reverse_cons, vertexPreReflectionProd_apply_cons, vertexPreReflectionProd_append,
      Module.End.mul_apply, ih (fun i hi ↦ hl i (by simp [hi]))]
    simpa using involutive_vertexPreReflection Q (hl j (by simp)) d

/-- The reflection product along a word in loopless vertices is bijective, the reversed word
providing the inverse. -/
theorem vertexPreReflectionProd_bijective {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    Function.Bijective (vertexPreReflectionProd Q l) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨vertexPreReflectionProd Q l.reverse,
    vertexPreReflectionProd_reverse_apply Q hl, fun d ↦ ?_⟩
  have h := vertexPreReflectionProd_reverse_apply Q (l := l.reverse)
    (fun i hi ↦ hl i (by simpa using hi)) d
  rwa [List.reverse_reverse] at h

/-- The reflection product along a word in loopless vertices, as a linear automorphism of the
dimension-vector lattice; over a repetition-free word running through all the vertices this is the
Coxeter transformation. -/
noncomputable def vertexReflectionProd {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ) :=
  LinearEquiv.ofBijective (vertexPreReflectionProd Q l)
    (vertexPreReflectionProd_bijective Q hl)

@[simp]
theorem coe_vertexReflectionProd {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    ⇑(vertexReflectionProd Q hl) = ⇑(vertexPreReflectionProd Q l) := by
  funext d
  simp [vertexReflectionProd]

/-- The inverse automorphism is the reflection product along the reversed word. -/
@[simp]
theorem coe_vertexReflectionProd_symm {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    ⇑(vertexReflectionProd Q hl).symm = ⇑(vertexPreReflectionProd Q l.reverse) := by
  funext d
  rw [LinearEquiv.symm_apply_eq, coe_vertexReflectionProd]
  have h := vertexPreReflectionProd_reverse_apply Q (l := l.reverse)
    (fun i hi ↦ hl i (by simpa using hi)) d
  rw [List.reverse_reverse] at h
  exact h.symm

/-- The reflection product along a word in loopless vertices permutes every level set of the
Tits form; at the level `1` this says that it permutes the roots of `Q`. -/
theorem bijOn_vertexPreReflectionProd {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (n : ℤ) :
    Set.BijOn (vertexPreReflectionProd Q l) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
  have h : vertexPreReflectionProd Q l ⁻¹' {d : Q → ℤ | titsForm Q d = n}
      = {d : Q → ℤ | titsForm Q d = n} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, titsForm_vertexPreReflectionProd Q hl]
  have hbij := (vertexPreReflectionProd_bijective Q hl).bijOn_preimage
    (t := {d : Q → ℤ | titsForm Q d = n})
  rwa [h] at hbij

/-! ### Fixed vectors -/

/-- A vector fixed by the reflection product along a repetition-free word is orthogonal, for the
polarized Tits form, to the simple dimension vector at every vertex of that word. -/
theorem titsPolarForm_single_eq_zero_of_vertexPreReflectionProd_eq_self {l : List Q}
    (hnd : l.Nodup) {v : Q → ℤ} (hv : vertexPreReflectionProd Q l v = v) {i : Q} (hi : i ∈ l) :
    titsPolarForm Q (Pi.single i 1) v = 0 := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hjl, hnd'⟩ := List.nodup_cons.mp hnd
    -- The head `j` occurs nowhere else in the word, so the remaining reflections leave the `j`-th
    -- coordinate of `sⱼ v` untouched.
    have hcoord : vertexPreReflectionProd Q (j :: l) v j
        = v j - titsPolarForm Q (Pi.single j 1) v := by
      rw [vertexPreReflectionProd_apply_cons,
        vertexPreReflectionProd_apply_of_notMem Q hjl, vertexPreReflection_apply]
      simp
    -- The `j`-th coordinate of the fixed-point equation therefore reads `vⱼ - ⟨αⱼ, v⟩ = vⱼ`.
    rw [hv] at hcoord
    have hj : titsPolarForm Q (Pi.single j 1) v = 0 := by omega
    -- Then `sⱼ` fixes `v`, so the tail of the word fixes `v` as well.
    have hfix : vertexPreReflection Q j v = v :=
      vertexPreReflection_apply_of_titsPolarForm_eq_zero Q j hj
    rw [vertexPreReflectionProd_apply_cons, hfix] at hv
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact hj
    · exact ih hnd' hv hi'

/-- A vector fixed by the reflection product along a repetition-free word in *all* the vertices
lies in the radical of the polarized Tits form. -/
theorem titsPolarForm_eq_zero_of_vertexPreReflectionProd_eq_self {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) {v : Q → ℤ} (hv : vertexPreReflectionProd Q l v = v) (d : Q → ℤ) :
    titsPolarForm Q d v = 0 := by
  have hsingle : ∀ i : Q, titsPolarForm Q (Pi.single i 1) v = 0 := fun i ↦
    titsPolarForm_single_eq_zero_of_vertexPreReflectionProd_eq_self Q hnd hv (hmem i)
  rw [pi_eq_sum_univ' d, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hsingle i, mul_zero]

/-- **The Coxeter transformation of a quiver whose polarized Tits form has trivial radical fixes
only the zero vector**, as soon as the word of vertices it is taken along is repetition-free and
exhausts the vertices.

This is the input to the reflection induction behind Gabriel's theorem: no nonzero dimension
vector survives a full pass of the Coxeter functor unchanged. An anisotropic Tits form has
trivial radical, which is the form the hypothesis takes in
`TauCeti.vertexPreReflectionProd_eq_self_iff_of_anisotropic`. -/
theorem vertexPreReflectionProd_eq_self_iff
    (hsep : LinearMap.SeparatingRight (titsPolarForm Q)) {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    vertexPreReflectionProd Q l v = v ↔ v = 0 :=
  ⟨fun hv ↦ hsep v (titsPolarForm_eq_zero_of_vertexPreReflectionProd_eq_self Q hnd hmem hv),
    fun hv ↦ by rw [hv, map_zero]⟩

/-- **The Coxeter transformation of a quiver whose polarized Tits form has trivial radical fixes
only the zero vector**, in the automorphism packaging. -/
theorem vertexReflectionProd_eq_self_iff (hsep : LinearMap.SeparatingRight (titsPolarForm Q))
    {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l)
    (v : Q → ℤ) :
    vertexReflectionProd Q hl v = v ↔ v = 0 := by
  simp only [coe_vertexReflectionProd]
  exact vertexPreReflectionProd_eq_self_iff Q hsep hnd hmem v

/-- **The Coxeter transformation of a quiver with anisotropic Tits form fixes only the zero
vector**: a vector in the radical of the polarized form is isotropic, since `⟨v, v⟩ = 2 q(v)`.

For a quiver of ADE type the Tits form is positive definite, and
`QuadraticMap.PosDef.anisotropic` supplies the hypothesis. -/
theorem vertexPreReflectionProd_eq_self_iff_of_anisotropic (hani : (titsForm Q).Anisotropic)
    {l : List Q} (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    vertexPreReflectionProd Q l v = v ↔ v = 0 := by
  refine vertexPreReflectionProd_eq_self_iff Q (fun w hw ↦ hani w ?_) hnd hmem v
  have h := hw w
  rw [titsPolarForm_def, ← titsForm_def] at h
  omega

/-- **The Coxeter transformation of a quiver with anisotropic Tits form fixes only the zero
vector**, in the automorphism packaging. -/
theorem vertexReflectionProd_eq_self_iff_of_anisotropic (hani : (titsForm Q).Anisotropic)
    {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l)
    (v : Q → ℤ) :
    vertexReflectionProd Q hl v = v ↔ v = 0 := by
  simp only [coe_vertexReflectionProd]
  exact vertexPreReflectionProd_eq_self_iff_of_anisotropic Q hani hnd hmem v

end TauCeti
