/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# The kernel of a complex character

A representation `ρ` of a group has a kernel, the subgroup `ρ.ker` of the elements acting as the
identity, and it is normal because it is the kernel of a homomorphism. The character sees that
kernel: for a finite-dimensional complex representation of a **finite** group,

`g ∈ ρ.ker ↔ ρ.character g = ρ.character 1`,

so the kernel is read off the character alone. That equivalence is the content of this file
(`Representation.mem_ker_iff_char_eq` and its `FDRep` form `FDRep.mem_ker_iff_char_eq`), together
with the consequence that the locus where a whole *family* of characters takes its value at the
identity is the common kernel of that family (`FDRep.coe_iInf_ker`), a normal subgroup
(`FDRep.normal_iInf_ker`).

One direction is immediate: if `ρ g` is the identity then its trace is `finrank ℂ V`. The other is
not, and it is where the analysis enters. The eigenvalues of `ρ g` are roots of unity, so each has
real part at most `1`; the character value is those eigenvalues summed with the dimensions of the
eigenspaces as weights, and those dimensions add up to `finrank ℂ V`. Attaining the value
`finrank ℂ V` therefore forces every eigenvalue to have real part `1`, hence to be `1`, and `ρ g`
is diagonalizable, so it is the identity. That argument is carried out for a bare endomorphism in
`TauCeti.End.trace_eq_finrank_iff`; here it is only transported to representations and characters.

Finiteness of the group is used only to know that `g` has finite order, and it is exactly what the
statement needs. For an element of infinite order there is no constraint on the eigenvalues of
`ρ g`, and the character can take the value `finrank ℂ V` without `ρ g` being the identity: the
representation of `ℤ` on `ℂ²` sending `n` to the unipotent matrix with off-diagonal entry `n` has
character constantly `2`, while no nonzero `n` acts as the identity. The statements are therefore
given first for an element with `g ^ n = 1`, where the hypothesis is explicit, and then specialized
to a finite group.

The restriction to `ℂ` is inherited from `TauCeti.End.trace_eq_finrank_iff`, and is one of proof
rather than of substance: the equivalence holds over any field of characteristic zero, the
eigenvalues generating a cyclotomic subfield of the algebraic closure that embeds into `ℂ`. What the
proof compares are the real parts of the eigenvalues, which is what such an embedding buys; the
descent along one is not carried out, and `ℂ` is where the character theory downstream of this file
works.

The kernel description is what turns a character computation into a normal subgroup, and that is a
**prerequisite** of the character-theoretic proof of **Frobenius's theorem**, not that proof nor a
milestone of it. The exceptional characters of
`TauCeti/RepresentationTheory/Induction/ExceptionalCharacter.lean` are irreducible characters of
`G`, and the classical argument exhibits the Frobenius kernel `TauCeti.frobeniusKernel` as their
common kernel; `FDRep.coe_iInf_ker` and `FDRep.normal_iInf_ker` are the generic half of that step,
saying that such a common kernel is cut out by character equations and is a normal subgroup.
Nothing here identifies that locus with `TauCeti.frobeniusKernel`: constructing the coherent family
out of the exceptional-character correspondence, and proving that its common kernel is
`TauCeti.frobeniusKernel`, remain to be done, and only then does the bundled
`frobeniusKernelSubgroup` with its normality follow.

## Main statements

* `Representation.char_eq_finrank_iff_of_pow_eq_one` and `Representation.char_eq_finrank_iff`:
  **a complex character attains its degree at `g` exactly when `g` acts as the identity.**
* `Representation.mem_ker_iff_char_eq` and `FDRep.mem_ker_iff_char_eq`: the same, read as a
  description of the kernel; `FDRep.coe_ker` states it as an equality of sets.
* `FDRep.coe_iInf_ker`: **the locus where every member of a family of characters takes its value at
  the identity is the common kernel of that family**, which `FDRep.normal_iInf_ker` records as a
  normal subgroup.
* `FDRep.ker_eq_ker_of_char_eq`: the kernel depends on the representation only through its
  character.
* `FDRep.ker_eq_top_iff` and `FDRep.ker_eq_bot_iff`: the kernel is everything exactly when the
  character is constant, and trivial exactly when the character detects the identity.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Lemma 2.15 and Chapter 7,
  Section 7B.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 2.1.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8, the `frobeniusKernelSubgroup` milestone "that its support is a normal subgroup".
-/

public section

open Module

universe u v w

namespace Representation

section Monoid

variable {G : Type v} {V : Type w} [Monoid G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- **A complex character attains its degree exactly on the elements acting as the identity.**
Stated for an element with `g ^ n = 1`; `Representation.char_eq_finrank_iff` is the form for a
finite group, where every element has finite order. -/
theorem char_eq_finrank_iff_of_pow_eq_one (ρ : Representation ℂ G V) {g : G} {n : ℕ}
    (hn : n ≠ 0) (hg : g ^ n = 1) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  TauCeti.End.trace_eq_finrank_iff hn (by rw [← map_pow, hg, map_one])

end Monoid

section Group

variable {G : Type v} {V : Type w} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- **A complex character of a finite group attains its degree exactly on the elements acting as
the identity.** -/
theorem char_eq_finrank_iff [Finite G] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  char_eq_finrank_iff_of_pow_eq_one ρ (orderOf_pos g).ne' (pow_orderOf_eq_one g)

/-- **The kernel of a complex representation of a finite group is read off its character**: `g`
acts as the identity exactly when the character takes at `g` the value it takes at the identity. -/
theorem mem_ker_iff_char_eq [Finite G] (ρ : Representation ℂ G V) (g : G) :
    g ∈ ρ.ker ↔ ρ.character g = ρ.character 1 := by
  rw [MonoidHom.mem_ker, char_one, char_eq_finrank_iff]

end Group

end Representation

namespace FDRep

variable {G : Type u} [Group G]

/-- **The kernel of a finite-dimensional complex representation of a finite group is read off its
character**: `g` acts as the identity exactly when the character takes at `g` the value it takes at
the identity. -/
theorem mem_ker_iff_char_eq [Finite G] (V : FDRep ℂ G) (g : G) :
    g ∈ V.ρ.ker ↔ V.character g = V.character 1 :=
  Representation.mem_ker_iff_char_eq V.ρ g

/-- **The kernel of a finite-dimensional complex representation of a finite group, as the set of
elements at which the character takes its value at the identity.** -/
theorem coe_ker [Finite G] (V : FDRep ℂ G) :
    (V.ρ.ker : Set G) = {g | V.character g = V.character 1} :=
  Set.ext fun g => mem_ker_iff_char_eq V g

/-- **Representations with the same character have the same kernel.** The kernel depends on the
representation only through its character, being cut out by the character values. -/
theorem ker_eq_ker_of_char_eq [Finite G] {V W : FDRep ℂ G}
    (h : V.character = W.character) : V.ρ.ker = W.ρ.ker :=
  SetLike.ext fun g => by
    rw [mem_ker_iff_char_eq V g, mem_ker_iff_char_eq W g, h]

/-- **A representation of a finite group is trivial exactly when its character is constant.** -/
theorem ker_eq_top_iff [Finite G] (V : FDRep ℂ G) :
    V.ρ.ker = ⊤ ↔ ∀ g : G, V.character g = V.character 1 := by
  rw [Subgroup.eq_top_iff']
  exact forall_congr' fun g => mem_ker_iff_char_eq V g

/-- **A representation of a finite group is faithful exactly when its character detects the
identity.** -/
theorem ker_eq_bot_iff [Finite G] (V : FDRep ℂ G) :
    V.ρ.ker = ⊥ ↔ ∀ g : G, V.character g = V.character 1 → g = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  exact forall_congr' fun g => imp_congr_left (mem_ker_iff_char_eq V g)

section Family

variable {ι : Type*}

/-- **The common kernel of a family of representations is a normal subgroup.** Each kernel is
normal, and Mathlib's `Subgroup.normal_iInf_normal` passes that to the infimum; what is added here
is the registration as an instance, that lemma taking its hypothesis as an explicit argument, so
that the normality of a common kernel is available to instance search where `FDRep.coe_iInf_ker`
presents it as a locus of character equations. -/
instance normal_iInf_ker {k : Type*} [Field k] (W : ι → FDRep k G) :
    (⨅ i, (W i).ρ.ker).Normal :=
  Subgroup.normal_iInf_normal fun _ => inferInstance

/-- **The common kernel of a family of representations, as a set of character equations.** An
element lies in it exactly when every character of the family takes at it the value it takes at the
identity. Together with `FDRep.normal_iInf_ker` this is how a character computation produces a
normal subgroup. -/
theorem coe_iInf_ker [Finite G] (W : ι → FDRep ℂ G) :
    ((⨅ i, (W i).ρ.ker : Subgroup G) : Set G)
      = {g | ∀ i, (W i).character g = (W i).character 1} :=
  Set.ext fun g => by
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    exact forall_congr' fun i => mem_ker_iff_char_eq (W i) g

end Family

end FDRep
