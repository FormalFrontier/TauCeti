/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.DimensionVector

/-!
# The Coxeter transformation on the dimension vectors of a quiver

Composing the simple reflections of a finite quiver `Q` at the successive vertices of a list
`l = [i₁, …, iₙ]` gives the endomorphism `sᵢₙ ∘ ⋯ ∘ sᵢ₁` of the dimension-vector lattice
`Q → ℤ`. When `l` is a sink-admissible ordering of the vertices this is the numerical shadow of
the Coxeter functor, the composite of the Bernstein-Gelfand-Ponomarev reflection functors at
`i₁, …, iₙ`: each reflection functor acts on dimension vectors by the simple reflection at its
vertex (`TauCeti.dimVector_reflectRep_of_indecomposable`), and reflecting the quiver itself
changes neither the polarized Tits form nor the simple reflections built from it
(`TauCeti.vertexPreReflection_reflect_apply`), so the successive reflections may all be read in
the original quiver.

The main result is that this transformation has **no nonzero fixed vector** once the list runs
over every vertex without repetition and the polarized Tits form has trivial radical, in
particular whenever the Tits form is anisotropic, and so for a quiver of ADE type, where the
Tits form is positive definite and `QuadraticMap.PosDef.anisotropic` applies. This is the engine
of the Bernstein-Gelfand-Ponomarev proof of Gabriel's theorem: it is what forbids an
indecomposable representation from being carried to itself by the Coxeter functor, and so forces
the reflection induction to descend to a vertex simple.

The proof reads the fixed-point equation off one coordinate at a time rather than through a
linear-independence argument. The head `j` of the list occurs nowhere else in it, so the later
reflections leave the `j`-th coordinate alone; the `j`-th coordinate of the equation therefore
says exactly that `v` is orthogonal to `αⱼ`, whereupon `sⱼ` fixes `v` and the tail of the list
inherits the hypothesis.

## Main definitions and results

* `TauCeti.coxeterPreTransformation`: the composite of the simple reflections along a list of
  vertices, as a `ℤ`-linear endomorphism of the dimension-vector lattice. As with
  `TauCeti.vertexPreReflection`, no hypothesis on the vertices is imposed.
* `TauCeti.coxeterTransformation`: the same map as a linear automorphism, over a list of loopless
  vertices.
* `TauCeti.titsForm_coxeterPreTransformation` and
  `TauCeti.bijOn_coxeterPreTransformation`: the transformation preserves the Tits form, and hence
  permutes each of its level sets, in particular the roots `q(d) = 1`.
* `TauCeti.titsPolarForm_eq_zero_of_coxeterPreTransformation_eq_self`: a vector fixed by the
  transformation of a repetition-free list of all the vertices lies in the radical of the
  polarized Tits form.
* `TauCeti.coxeterPreTransformation_eq_self_iff` and
  `TauCeti.coxeterTransformation_eq_self_iff`: consequently, once that radical is trivial the only
  fixed vector is `0`;
  `TauCeti.coxeterPreTransformation_eq_self_iff_of_anisotropic` and
  `TauCeti.coxeterTransformation_eq_self_iff_of_anisotropic` are the same statements for an
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

/-- The Coxeter transformation along a list of vertices: the composite of the simple reflections
at those vertices, applied in the order in which they are listed, so that
`l = [i₁, …, iₙ]` gives `sᵢₙ ∘ ⋯ ∘ sᵢ₁`.

No hypothesis on the vertices is imposed here, following `TauCeti.vertexPreReflection`; over a
list of loopless vertices `TauCeti.coxeterTransformation` packages this map as an
automorphism. -/
noncomputable def coxeterPreTransformation (l : List Q) : Module.End ℤ (Q → ℤ) :=
  l.foldr (fun i c ↦ c * vertexPreReflection Q i) 1

@[simp]
theorem coxeterPreTransformation_nil : coxeterPreTransformation Q [] = 1 := by
  simp [coxeterPreTransformation]

/-- The vertex at the head of the list is reflected first. -/
theorem coxeterPreTransformation_cons (i : Q) (l : List Q) :
    coxeterPreTransformation Q (i :: l)
      = coxeterPreTransformation Q l * vertexPreReflection Q i := by
  simp [coxeterPreTransformation]

/-- The vertex at the head of the list is reflected first, in applied form. -/
theorem coxeterPreTransformation_apply_cons (i : Q) (l : List Q) (d : Q → ℤ) :
    coxeterPreTransformation Q (i :: l) d
      = coxeterPreTransformation Q l (vertexPreReflection Q i d) := by
  rw [coxeterPreTransformation_cons, Module.End.mul_apply]

/-- Concatenating two lists of vertices composes their Coxeter transformations, the first list
acting first. -/
theorem coxeterPreTransformation_append (l₁ l₂ : List Q) :
    coxeterPreTransformation Q (l₁ ++ l₂)
      = coxeterPreTransformation Q l₂ * coxeterPreTransformation Q l₁ := by
  induction l₁ with
  | nil => simp
  | cons i l ih =>
    rw [List.cons_append, coxeterPreTransformation_cons, ih, coxeterPreTransformation_cons,
      mul_assoc]

/-- Off the list, the Coxeter transformation changes no coordinate: each simple reflection in the
composite alters only the coordinate at its own vertex. -/
theorem coxeterPreTransformation_apply_of_notMem {l : List Q} {i : Q} (hi : i ∉ l) (d : Q → ℤ) :
    coxeterPreTransformation Q l d i = d i := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [List.mem_cons, not_or] at hi
    rw [coxeterPreTransformation_apply_cons, ih hi.2, vertexPreReflection_apply_of_ne Q j d hi.1]

/-! ### Invariance of the Tits form -/

/-- The Coxeter transformation along a list of loopless vertices preserves the Tits form. -/
theorem titsForm_coxeterPreTransformation {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d : Q → ℤ) : titsForm Q (coxeterPreTransformation Q l d) = titsForm Q d := by
  induction l generalizing d with
  | nil => simp
  | cons j l ih =>
    rw [coxeterPreTransformation_apply_cons, ih (fun i hi ↦ hl i (by simp [hi])),
      titsForm_vertexPreReflection Q (hl j (by simp))]

/-- The Coxeter transformation along a list of loopless vertices preserves the polarized Tits
form. -/
theorem titsPolarForm_coxeterPreTransformation {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i))
    (d e : Q → ℤ) :
    titsPolarForm Q (coxeterPreTransformation Q l d) (coxeterPreTransformation Q l e)
      = titsPolarForm Q d e := by
  induction l generalizing d e with
  | nil => simp
  | cons j l ih =>
    rw [coxeterPreTransformation_apply_cons, coxeterPreTransformation_apply_cons,
      ih (fun i hi ↦ hl i (by simp [hi])), titsPolarForm_vertexPreReflection Q (hl j (by simp))]

/-! ### The Coxeter transformation as an automorphism -/

/-- The Coxeter transformation along a list of loopless vertices is bijective, being a composite
of involutions. -/
theorem coxeterPreTransformation_bijective {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    Function.Bijective (coxeterPreTransformation Q l) := by
  induction l with
  | nil =>
    rw [coxeterPreTransformation_nil, Module.End.coe_one]
    exact Function.bijective_id
  | cons j l ih =>
    rw [coxeterPreTransformation_cons, Module.End.coe_mul]
    exact (ih fun i hi ↦ hl i (by simp [hi])).comp
      (involutive_vertexPreReflection Q (hl j (by simp))).bijective

/-- The Coxeter transformation along a list of loopless vertices, as a linear automorphism of the
dimension-vector lattice. -/
noncomputable def coxeterTransformation {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    (Q → ℤ) ≃ₗ[ℤ] (Q → ℤ) :=
  LinearEquiv.ofBijective (coxeterPreTransformation Q l)
    (coxeterPreTransformation_bijective Q hl)

@[simp]
theorem coe_coxeterTransformation {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) :
    ⇑(coxeterTransformation Q hl) = ⇑(coxeterPreTransformation Q l) := by
  funext d
  simp [coxeterTransformation]

/-- The Coxeter transformation along a list of loopless vertices permutes every level set of the
Tits form; at the level `1` this says that it permutes the roots of `Q`. -/
theorem bijOn_coxeterPreTransformation {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (n : ℤ) :
    Set.BijOn (coxeterPreTransformation Q l) {d : Q → ℤ | titsForm Q d = n}
      {d : Q → ℤ | titsForm Q d = n} := by
  refine ⟨fun d hd ↦ ?_, (coxeterPreTransformation_bijective Q hl).injective.injOn, fun d hd ↦ ?_⟩
  · simpa only [Set.mem_ofPred_eq, titsForm_coxeterPreTransformation Q hl] using hd
  · obtain ⟨e, rfl⟩ := (coxeterPreTransformation_bijective Q hl).surjective d
    exact ⟨e, by simpa only [Set.mem_ofPred_eq, titsForm_coxeterPreTransformation Q hl] using hd,
      rfl⟩

/-! ### Fixed vectors -/

/-- A vector fixed by the Coxeter transformation along a repetition-free list is orthogonal, for
the polarized Tits form, to the simple dimension vector at every vertex of that list.

The induction peels off the head `j` of the list. It occurs nowhere else, so the remaining
reflections leave the `j`-th coordinate of `sⱼ v` untouched, and the `j`-th coordinate of the
fixed-point equation reads `vⱼ - ⟨αⱼ, v⟩ = vⱼ`. Then `sⱼ` fixes `v`, so the tail of the list
fixes `v` as well. -/
theorem titsPolarForm_single_eq_zero_of_coxeterPreTransformation_eq_self {l : List Q}
    (hnd : l.Nodup) {v : Q → ℤ} (hv : coxeterPreTransformation Q l v = v) {i : Q} (hi : i ∈ l) :
    titsPolarForm Q (Pi.single i 1) v = 0 := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hjl, hnd'⟩ := List.nodup_cons.mp hnd
    have hcoord : coxeterPreTransformation Q (j :: l) v j
        = v j - titsPolarForm Q (Pi.single j 1) v := by
      rw [coxeterPreTransformation_apply_cons,
        coxeterPreTransformation_apply_of_notMem Q hjl, vertexPreReflection_apply]
      simp
    rw [hv] at hcoord
    have hj : titsPolarForm Q (Pi.single j 1) v = 0 := by omega
    have hfix : vertexPreReflection Q j v = v :=
      vertexPreReflection_apply_of_titsPolarForm_eq_zero Q j hj
    rw [coxeterPreTransformation_apply_cons, hfix] at hv
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact hj
    · exact ih hnd' hv hi'

/-- A vector fixed by the Coxeter transformation along a repetition-free list of *all* the
vertices lies in the radical of the polarized Tits form. -/
theorem titsPolarForm_eq_zero_of_coxeterPreTransformation_eq_self {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) {v : Q → ℤ} (hv : coxeterPreTransformation Q l v = v) (d : Q → ℤ) :
    titsPolarForm Q d v = 0 := by
  have hsingle : ∀ i : Q, titsPolarForm Q (Pi.single i 1) v = 0 := fun i ↦
    titsPolarForm_single_eq_zero_of_coxeterPreTransformation_eq_self Q hnd hv (hmem i)
  have hd : d = ∑ i : Q, d i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [hd, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ ↦ by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hsingle i, mul_zero]

/-- **The Coxeter transformation of a quiver whose polarized Tits form has trivial radical fixes
only the zero vector**, as soon as the list of vertices it is taken along is repetition-free and
exhausts the vertices.

This is the input to the reflection induction behind Gabriel's theorem: no nonzero dimension
vector survives a full pass of the Coxeter functor unchanged. An anisotropic Tits form has
trivial radical, which is the form the hypothesis takes in
`TauCeti.coxeterPreTransformation_eq_self_iff_of_anisotropic`. -/
theorem coxeterPreTransformation_eq_self_iff
    (hsep : LinearMap.SeparatingRight (titsPolarForm Q)) {l : List Q} (hnd : l.Nodup)
    (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    coxeterPreTransformation Q l v = v ↔ v = 0 :=
  ⟨fun hv ↦ hsep v (titsPolarForm_eq_zero_of_coxeterPreTransformation_eq_self Q hnd hmem hv),
    fun hv ↦ by rw [hv, map_zero]⟩

/-- **The Coxeter transformation of a quiver whose polarized Tits form has trivial radical fixes
only the zero vector**, in the automorphism packaging. -/
theorem coxeterTransformation_eq_self_iff (hsep : LinearMap.SeparatingRight (titsPolarForm Q))
    {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l)
    (v : Q → ℤ) :
    coxeterTransformation Q hl v = v ↔ v = 0 := by
  simp only [coe_coxeterTransformation]
  exact coxeterPreTransformation_eq_self_iff Q hsep hnd hmem v

/-- **The Coxeter transformation of a quiver with anisotropic Tits form fixes only the zero
vector**: a vector in the radical of the polarized form is isotropic, since `⟨v, v⟩ = 2 q(v)`.

For a quiver of ADE type the Tits form is positive definite, and
`QuadraticMap.PosDef.anisotropic` supplies the hypothesis. -/
theorem coxeterPreTransformation_eq_self_iff_of_anisotropic (hani : (titsForm Q).Anisotropic)
    {l : List Q} (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l) (v : Q → ℤ) :
    coxeterPreTransformation Q l v = v ↔ v = 0 := by
  refine coxeterPreTransformation_eq_self_iff Q (fun w hw ↦ hani w ?_) hnd hmem v
  have h := hw w
  rw [titsPolarForm_def, ← titsForm_def] at h
  omega

/-- **The Coxeter transformation of a quiver with anisotropic Tits form fixes only the zero
vector**, in the automorphism packaging. -/
theorem coxeterTransformation_eq_self_iff_of_anisotropic (hani : (titsForm Q).Anisotropic)
    {l : List Q} (hl : ∀ i ∈ l, IsEmpty (i ⟶ i)) (hnd : l.Nodup) (hmem : ∀ i : Q, i ∈ l)
    (v : Q → ℤ) :
    coxeterTransformation Q hl v = v ↔ v = 0 := by
  simp only [coe_coxeterTransformation]
  exact coxeterPreTransformation_eq_self_iff_of_anisotropic Q hani hnd hmem v

end TauCeti
