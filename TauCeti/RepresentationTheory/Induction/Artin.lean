/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Completeness
public import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Artin's induction theorem

Let `𝒮` be a family of subgroups of a finite group `G` that **covers `G` up to conjugacy**: every
element of `G` has a conjugate lying in some member of `𝒮`.  Over a field `k` in which `|G|` is
invertible, induction from `𝒮` is then surjective on class functions: the class functions
`Ind_S^G ψ`, for `S ∈ 𝒮` and `ψ` a class function of `S`, span all class functions of `G`
(`TauCeti.ClassFunction.inducedFrom_eq_top`).

The proof is the classical duality argument.  The character pairing is nondegenerate, so the span is
everything as soon as nothing nonzero is orthogonal to it.  Frobenius reciprocity converts
orthogonality to *every* class function induced from `S` into the vanishing of the restriction of
`h` to `S`, and a class function whose restriction to every member of `𝒮` vanishes is zero, because
each `x` is conjugate into some member and a class function is constant on conjugacy classes.

**Artin's induction theorem** is the case where `𝒮` is the family of cyclic subgroups
(`TauCeti.ClassFunction.cyclicInduced_eq_top`), which covers `G` for the trivial reason that `x`
generates a cyclic subgroup containing it.  The covering hypothesis is stated for a general family
because that is the shape Brauer's induction theorem needs, with the elementary subgroups in place
of the cyclic ones.

Over an algebraically closed `k` the spanning set can be cut down to genuine induced *characters*:
the irreducible characters of `S` span the class functions of `S`, so
`TauCeti.ClassFunction.cyclicInducedCharacters_eq_top` says that the characters induced from the
irreducible characters of the cyclic subgroups already span.  Applied to the character of a
representation of `G`, this is Artin's theorem in its usual phrasing: every character of `G` is a
linear combination of characters induced from cyclic subgroups.

## Main definitions

* `TauCeti.ClassFunction.inducedFrom`: the submodule of class functions of `G` spanned by the class
  functions induced from a family `𝒮` of subgroups, and `TauCeti.ClassFunction.cyclicInduced` for
  the family of cyclic subgroups.
* `TauCeti.ClassFunction.inducedCharactersFrom`: the smaller spanning set in which only irreducible
  characters of the members of `𝒮` are induced, and
  `TauCeti.ClassFunction.cyclicInducedCharacters` for the family of cyclic subgroups.

## Main statements

* `TauCeti.ClassFunction.inducedFrom_eq_top`: induction from a family of subgroups covering `G` up
  to conjugacy spans all class functions, and
  `TauCeti.ClassFunction.cyclicInduced_eq_top`: **Artin's induction theorem**, its cyclic case, with
  `TauCeti.ClassFunction.exists_sum_smul_ind` the explicit finite-combination form.
* `TauCeti.ClassFunction.inducedCharactersFrom_eq_inducedFrom`: over an algebraically closed field,
  inducing only the irreducible characters of the subgroups spans as much as inducing all their
  class functions, whence `TauCeti.ClassFunction.inducedCharactersFrom_eq_top` and
  `TauCeti.ClassFunction.cyclicInducedCharacters_eq_top`, with
  `TauCeti.ClassFunction.exists_sum_smul_ind_ofCharacter` the explicit form.  Specialized to the
  character of a representation of `G` this is the classical statement of Artin's theorem.

## Implementation notes

Only the invertibility of `|G|` in `k` is assumed for the first form; no algebraic closure is
needed, because the duality argument runs on
`TauCeti.ClassFunction.characterPairing_nondegenerate` alone.  Algebraic closure enters only in the
refinement to induced characters, where completeness of the irreducible characters of the subgroup
is used.

The covering hypothesis is written out as `∀ x : G, ∃ S ∈ 𝒮, ∃ y : G, y * x * y⁻¹ ∈ S` rather than
bundled into a predicate: it is used once, and the cyclic instance discharges it with `y = 1`.

The coefficients produced here are elements of `k`.  Artin's sharper theorem says that over `ℂ` they
may be taken rational, and that `|G| • χ` is even an integral combination of induced characters;
both refinements need the virtual-character lattice rather than the class functions, and neither is
proved here.

## References

This is the "Artin's induction theorem" item of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, in the spanning
(equivalently, surjectivity) form that the layer calls for; the integral `|G| • χ` form and the
rational refinement remain open, as do Brauer's induction theorem and Brauer's characterization of
characters.

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 9.2,
  Theorem 17 and its corollary.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, Wiley (1981), Section 15.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u v

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G]

/-! ### Class functions induced from a family of subgroups -/

/-- The submodule of class functions of `G` spanned by the class functions induced from the members
of a family `𝒮` of subgroups of `G`.

`TauCeti.ClassFunction.inducedFrom_eq_top` is the statement that this submodule is everything as
soon as `𝒮` covers `G` up to conjugacy and `|G|` is invertible in `k`. -/
noncomputable def inducedFrom (𝒮 : Set (Subgroup G)) : Submodule k (ClassFunction k G) :=
  Submodule.span k {f | ∃ S ∈ 𝒮, ∃ ψ : ClassFunction k S, ind S ψ = f}

/-- The submodule of class functions of `G` spanned by the class functions induced from its cyclic
subgroups.

Artin's induction theorem, `TauCeti.ClassFunction.cyclicInduced_eq_top`, is the statement that this
submodule is everything as soon as `|G|` is invertible in `k`. -/
noncomputable def cyclicInduced : Submodule k (ClassFunction k G) :=
  inducedFrom k G {S | IsCyclic S}

variable {k G}

/-- A class function induced from a member of `𝒮` lies in `TauCeti.ClassFunction.inducedFrom`, the
submodule these generate. -/
theorem ind_mem_inducedFrom {𝒮 : Set (Subgroup G)} {S : Subgroup G} (hS : S ∈ 𝒮)
    (ψ : ClassFunction k S) :
    ind S ψ ∈ inducedFrom k G 𝒮 :=
  Submodule.subset_span ⟨S, hS, ψ, rfl⟩

/-- A class function induced from a cyclic subgroup lies in
`TauCeti.ClassFunction.cyclicInduced`, the submodule these generate. -/
theorem ind_mem_cyclicInduced (C : Subgroup G) (hC : IsCyclic C) (ψ : ClassFunction k C) :
    ind C ψ ∈ cyclicInduced k G :=
  ind_mem_inducedFrom hC ψ

/-- **A class function orthogonal to every induction from `𝒮` vanishes**, when `𝒮` covers `G` up to
conjugacy.  Frobenius reciprocity turns orthogonality to all of `Ind_S^G (ClassFunction k S)` into
orthogonality of the restriction of `h` to `S` against all class functions of `S`, so that
restriction is zero by nondegeneracy of the pairing on `S`.  Any conjugate of `x` lying in `S` then
evaluates `h` at `x`. -/
theorem eq_zero_of_characterPairing_inducedFrom_eq_zero [Fintype G]
    [Invertible (Nat.card G : k)] {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ x : G, ∃ S ∈ 𝒮, ∃ y : G, y * x * y⁻¹ ∈ S) {h : ClassFunction k G}
    (hh : ∀ f ∈ inducedFrom k G 𝒮, characterPairing f h = 0) :
    h = 0 := by
  classical
  have hG : IsUnit (Nat.card G : k) := isUnit_of_invertible _
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨S, hS, y, hy⟩ := h𝒮 x
  have hres : comap S.subtype h = 0 := by
    let : Invertible (Nat.card S : k) := (isUnit_natCard_subgroup _ hG).invertible
    refine characterPairing_nondegenerate.2 _ fun ψ => ?_
    rw [← characterPairing_ind hG ψ h]
    exact hh _ (ind_mem_inducedFrom hS ψ)
  have hzero := congrArg (fun f : ClassFunction k S => f.1 ⟨y * x * y⁻¹, hy⟩) hres
  rw [← mem_iff.mp h.2 x y]
  simpa using hzero

/-- The orthogonal complement of `TauCeti.ClassFunction.inducedFrom` for the character pairing is
trivial, when `𝒮` covers `G` up to conjugacy. -/
theorem orthogonal_inducedFrom_eq_bot [Fintype G] [Invertible (Nat.card G : k)]
    {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ x : G, ∃ S ∈ 𝒮, ∃ y : G, y * x * y⁻¹ ∈ S) :
    (characterPairing (k := k) (G := G)).orthogonal (inducedFrom k G 𝒮) = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hh =>
    eq_zero_of_characterPairing_inducedFrom_eq_zero h𝒮 fun f hf =>
      LinearMap.BilinForm.mem_orthogonal_iff.mp hh f hf

/-- **Induction from a covering family of subgroups is surjective on class functions.**  If every
element of the finite group `G` is conjugate into a member of `𝒮`, and `|G|` is invertible in `k`,
then the class functions induced from the members of `𝒮` span all class functions of `G`.

`TauCeti.ClassFunction.cyclicInduced_eq_top` is Artin's induction theorem, the case of the cyclic
subgroups; the family of elementary subgroups, which Brauer's induction theorem uses, satisfies the
same hypothesis. -/
theorem inducedFrom_eq_top [Invertible (Nat.card G : k)] {𝒮 : Set (Subgroup G)}
    (h𝒮 : ∀ x : G, ∃ S ∈ 𝒮, ∃ y : G, y * x * y⁻¹ ∈ S) :
    inducedFrom k G 𝒮 = ⊤ := by
  let := Fintype.ofFinite G
  have hrefl := (characterPairing_isSymm (k := k) (G := G)).isRefl
  calc inducedFrom k G 𝒮
      = (characterPairing (k := k) (G := G)).orthogonal
          ((characterPairing (k := k) (G := G)).orthogonal (inducedFrom k G 𝒮)) :=
        (LinearMap.BilinForm.orthogonal_orthogonal characterPairing_nondegenerate hrefl _).symm
    _ = ⊤ := by rw [orthogonal_inducedFrom_eq_bot h𝒮, LinearMap.BilinForm.orthogonal_bot]

/-- **Artin's induction theorem.**  Over a field in which the order of the finite group `G` is
invertible, the class functions induced from the cyclic subgroups of `G` span all class functions
of `G`.

Equivalently, the induction map `⨁_{C cyclic} ClassFunction k C → ClassFunction k G` is surjective.
The explicit finite-combination form is `TauCeti.ClassFunction.exists_sum_smul_ind`, and
`TauCeti.ClassFunction.cyclicInducedCharacters_eq_top` refines the spanning set to induced
characters. -/
theorem cyclicInduced_eq_top [Invertible (Nat.card G : k)] : cyclicInduced k G = ⊤ :=
  inducedFrom_eq_top fun x =>
    ⟨Subgroup.zpowers x, Subgroup.isCyclic_zpowers x, 1, by simp⟩

/-- **Artin's induction theorem**, written out: every class function of `G` is a finite `k`-linear
combination of class functions induced from cyclic subgroups. -/
theorem exists_sum_smul_ind [Invertible (Nat.card G : k)] (f : ClassFunction k G) :
    ∃ (n : ℕ) (C : Fin n → Subgroup G) (_ : ∀ i, IsCyclic (C i))
      (ψ : ∀ i, ClassFunction k (C i)) (c : Fin n → k),
      ∑ i, c i • ind (C i) (ψ i) = f := by
  have hf : f ∈ cyclicInduced k G :=
    (cyclicInduced_eq_top (k := k) (G := G)).symm ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hf
  choose C hC ψ hψ using fun i => (g i).2
  exact ⟨n, C, hC, ψ, c, by simpa only [hψ] using hg⟩

/-! ### Characters induced from a family of subgroups -/

variable (k G)

/-- The submodule of class functions of `G` spanned by the characters induced from the irreducible
characters of the members of a family `𝒮` of subgroups of `G`.

This is contained in `TauCeti.ClassFunction.inducedFrom`, and over an algebraically closed field the
two agree (`TauCeti.ClassFunction.inducedCharactersFrom_eq_inducedFrom`).

As in `TauCeti.ClassFunction.le_span_irreducibleCharacters`, the irreducibles are taken on the
coordinate spaces `Fin n → k`, which is where the Wedderburn presentation of the group algebra
produces them. -/
noncomputable def inducedCharactersFrom (𝒮 : Set (Subgroup G)) : Submodule k (ClassFunction k G) :=
  Submodule.span k
    {f | ∃ S ∈ 𝒮, ∃ (n : ℕ) (ρ : Representation k S (Fin n → k)),
      ρ.IsIrreducible ∧ ind S (ofCharacter ρ) = f}

/-- The submodule of class functions of `G` spanned by the characters induced from the irreducible
characters of its cyclic subgroups. -/
noncomputable def cyclicInducedCharacters : Submodule k (ClassFunction k G) :=
  inducedCharactersFrom k G {S | IsCyclic S}

variable {k G}

/-- A character induced from an irreducible character of a member of `𝒮` lies in
`TauCeti.ClassFunction.inducedCharactersFrom`, the submodule these generate. -/
theorem ind_ofCharacter_mem_inducedCharactersFrom {𝒮 : Set (Subgroup G)} {S : Subgroup G}
    (hS : S ∈ 𝒮) {n : ℕ} (ρ : Representation k S (Fin n → k)) (hρ : ρ.IsIrreducible) :
    ind S (ofCharacter ρ) ∈ inducedCharactersFrom k G 𝒮 :=
  Submodule.subset_span ⟨S, hS, n, ρ, hρ, rfl⟩

/-- A character is a class function, so inducing only the irreducible characters of the members of
`𝒮` spans no more than inducing all their class functions. -/
theorem inducedCharactersFrom_le_inducedFrom (𝒮 : Set (Subgroup G)) :
    inducedCharactersFrom k G 𝒮 ≤ inducedFrom k G 𝒮 :=
  Submodule.span_le.mpr <| by
    rintro - ⟨S, hS, -, ρ, -, rfl⟩
    exact ind_mem_inducedFrom hS (ofCharacter ρ)

/-- Inducing an arbitrary class function of a subgroup gains nothing over inducing its irreducible
characters: over an algebraically closed field the latter already span the class functions of the
subgroup, and induction is linear. -/
theorem inducedFrom_le_inducedCharactersFrom [IsAlgClosed k] [Invertible (Nat.card G : k)]
    (𝒮 : Set (Subgroup G)) :
    inducedFrom k G 𝒮 ≤ inducedCharactersFrom k G 𝒮 := by
  have hG : IsUnit (Nat.card G : k) := isUnit_of_invertible _
  refine Submodule.span_le.mpr ?_
  rintro - ⟨S, hS, ψ, rfl⟩
  let : Invertible (Nat.card S : k) := (isUnit_natCard_subgroup _ hG).invertible
  let := Fintype.ofFinite (ConjClasses S)
  obtain ⟨d, ρ, b, hirr, hb⟩ := exists_basis_ofCharacter k S
  have hsum : ψ = ∑ D, b.repr ψ D • ofCharacter (ρ D) := by
    conv_lhs => rw [← b.sum_repr ψ]
    exact Finset.sum_congr rfl fun D _ => by rw [hb D]
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun D _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _
    (ind_ofCharacter_mem_inducedCharactersFrom hS (ρ D) (hirr D))

/-- Over an algebraically closed field, inducing the irreducible characters of the members of `𝒮`
spans exactly as much as inducing all their class functions. -/
theorem inducedCharactersFrom_eq_inducedFrom [IsAlgClosed k] [Invertible (Nat.card G : k)]
    (𝒮 : Set (Subgroup G)) :
    inducedCharactersFrom k G 𝒮 = inducedFrom k G 𝒮 :=
  le_antisymm (inducedCharactersFrom_le_inducedFrom 𝒮) (inducedFrom_le_inducedCharactersFrom 𝒮)

/-- **Induction of irreducible characters from a covering family of subgroups already spans the
class functions**, over an algebraically closed field in which `|G|` is invertible. -/
theorem inducedCharactersFrom_eq_top [IsAlgClosed k] [Invertible (Nat.card G : k)]
    {𝒮 : Set (Subgroup G)} (h𝒮 : ∀ x : G, ∃ S ∈ 𝒮, ∃ y : G, y * x * y⁻¹ ∈ S) :
    inducedCharactersFrom k G 𝒮 = ⊤ :=
  top_le_iff.mp ((inducedFrom_eq_top h𝒮).ge.trans (inducedFrom_le_inducedCharactersFrom 𝒮))

/-- **Artin's induction theorem, in its character form.**  Over an algebraically closed field in
which the order of the finite group `G` is invertible, the characters induced from the irreducible
characters of the cyclic subgroups of `G` span all class functions of `G`.

In particular every character of `G` is a linear combination of characters induced from cyclic
subgroups; `TauCeti.ClassFunction.exists_sum_smul_ind_ofCharacter` writes that combination out. -/
theorem cyclicInducedCharacters_eq_top [IsAlgClosed k] [Invertible (Nat.card G : k)] :
    cyclicInducedCharacters k G = ⊤ :=
  inducedCharactersFrom_eq_top fun x =>
    ⟨Subgroup.zpowers x, Subgroup.isCyclic_zpowers x, 1, by simp⟩

/-- **Artin's induction theorem**, written out over an algebraically closed field: every class
function of `G` — in particular, by `TauCeti.ClassFunction.ofCharacter`, every character of `G` — is
a finite `k`-linear combination of characters induced from irreducible characters of cyclic
subgroups. -/
theorem exists_sum_smul_ind_ofCharacter [IsAlgClosed k] [Invertible (Nat.card G : k)]
    (f : ClassFunction k G) :
    ∃ (n : ℕ) (C : Fin n → Subgroup G) (_ : ∀ i, IsCyclic (C i)) (d : Fin n → ℕ)
      (ρ : ∀ i, Representation k (C i) (Fin (d i) → k)) (_ : ∀ i, (ρ i).IsIrreducible)
      (c : Fin n → k),
      ∑ i, c i • ind (C i) (ofCharacter (ρ i)) = f := by
  have hf : f ∈ cyclicInducedCharacters k G :=
    (cyclicInducedCharacters_eq_top (k := k) (G := G)).symm ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp hf
  choose C hC d ρ hρ hfg using fun i => (g i).2
  exact ⟨n, C, hC, d, ρ, hρ, c, by simpa only [hfg] using hg⟩

end ClassFunction

end TauCeti
