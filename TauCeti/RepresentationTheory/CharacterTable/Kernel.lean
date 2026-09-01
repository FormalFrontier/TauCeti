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
kernel: for a finite-dimensional complex representation and an element `g` of **finite order**,

`g ∈ ρ.ker ↔ ρ.character g = ρ.character 1`,

so the kernel is read off the character alone. That equivalence is the content of this file
(`Representation.mem_ker_iff_char_eq` and its `FDRep` form `FDRep.mem_ker_iff_char_eq`), together
with the consequence that the locus where a whole *family* of characters takes its value at the
identity is the common kernel of that family (`FDRep.coe_iInf_ker`), a normal subgroup by
`FDRep.normal_iInf_ker` (`TauCeti/RepresentationTheory/FDRep.lean`, that normality needing no
characters).

One direction is immediate: if `ρ g` is the identity then its trace is `finrank ℂ V`. The other is
not, and it is where the analysis enters. The eigenvalues of `ρ g` are roots of unity, so each has
real part at most `1`; the character value is those eigenvalues summed with the dimensions of the
eigenspaces as weights, and those dimensions add up to `finrank ℂ V`. Attaining the value
`finrank ℂ V` therefore forces every eigenvalue to have real part `1`, hence to be `1`, and `ρ g`
is diagonalizable, so it is the identity. That argument is carried out for a bare endomorphism in
`TauCeti.End.trace_eq_finrank_iff`; here it is only transported to representations and characters.

Finite order is exactly what the statement needs, and it is all that is assumed here. For an element
of infinite order there is no constraint on the eigenvalues of `ρ g`, and the character can take the
value `finrank ℂ V` without `ρ g` being the identity: the representation of `ℤ` on `ℂ²` sending `n`
to the unipotent matrix with off-diagonal entry `n` has character constantly `2`, while no nonzero
`n` acts as the identity. The statements are therefore given first for an element with `g ^ n = 1`,
where the hypothesis is explicit, then for one of finite order; the statements about the whole
kernel assume `IsMulTorsion G`, which a finite group satisfies by `isOfFinOrder_of_finite`.

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
  the identity is the common kernel of that family**, which `FDRep.normal_iInf_ker`
  (`TauCeti/RepresentationTheory/FDRep.lean`) records as a normal subgroup.
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
Stated for an element with `g ^ n = 1`; `Representation.char_eq_finrank_iff` is the form for an
element of finite order. -/
theorem char_eq_finrank_iff_of_pow_eq_one (ρ : Representation ℂ G V) {g : G} {n : ℕ}
    (hn : n ≠ 0) (hg : g ^ n = 1) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  TauCeti.End.trace_eq_finrank_iff hn (by rw [← map_pow, hg, map_one])

/-- **A complex character attains its degree at an element of finite order exactly when that
element acts as the identity.** -/
theorem char_eq_finrank_iff (ρ : Representation ℂ G V) {g : G} (hg : IsOfFinOrder g) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  char_eq_finrank_iff_of_pow_eq_one ρ hg.orderOf_pos.ne' (pow_orderOf_eq_one g)

end Monoid

section Group

variable {G : Type v} {V : Type w} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- **The kernel of a complex representation is read off its character**: an element of finite
order acts as the identity exactly when the character takes at it the value it takes at the
identity. -/
theorem mem_ker_iff_char_eq (ρ : Representation ℂ G V) {g : G} (hg : IsOfFinOrder g) :
    g ∈ ρ.ker ↔ ρ.character g = ρ.character 1 := by
  rw [MonoidHom.mem_ker, char_one, char_eq_finrank_iff ρ hg]

end Group

end Representation

namespace FDRep

variable {G : Type u} [Group G]

/-- **The kernel of a finite-dimensional complex representation is read off its character**: an
element `g` of finite order acts as the identity exactly when the character takes at `g` the value
it takes at the identity. -/
theorem mem_ker_iff_char_eq (V : FDRep ℂ G) {g : G} (hg : IsOfFinOrder g) :
    g ∈ V.ρ.ker ↔ V.character g = V.character 1 :=
  Representation.mem_ker_iff_char_eq V.ρ hg

/-- **The kernel of a finite-dimensional complex representation of a torsion group, as the set of
elements at which the character takes its value at the identity.** -/
theorem coe_ker (V : FDRep ℂ G) (hG : IsMulTorsion G) :
    (V.ρ.ker : Set G) = {g | V.character g = V.character 1} :=
  Set.ext fun g => mem_ker_iff_char_eq V (hG g)

/-- **Representations with the same character have the same kernel.** The kernel depends on the
representation only through its character, being cut out by the character values. -/
theorem ker_eq_ker_of_char_eq (hG : IsMulTorsion G) {V W : FDRep ℂ G}
    (h : V.character = W.character) : V.ρ.ker = W.ρ.ker :=
  SetLike.ext fun g => by
    rw [mem_ker_iff_char_eq V (hG g), mem_ker_iff_char_eq W (hG g), h]

/-- **A representation of a torsion group is trivial exactly when its character is constant.** -/
theorem ker_eq_top_iff (V : FDRep ℂ G) (hG : IsMulTorsion G) :
    V.ρ.ker = ⊤ ↔ ∀ g : G, V.character g = V.character 1 := by
  rw [Subgroup.eq_top_iff']
  exact forall_congr' fun g => mem_ker_iff_char_eq V (hG g)

/-- **A representation of a torsion group is faithful exactly when its character detects the
identity.** -/
theorem ker_eq_bot_iff (V : FDRep ℂ G) (hG : IsMulTorsion G) :
    V.ρ.ker = ⊥ ↔ ∀ g : G, V.character g = V.character 1 → g = 1 := by
  rw [Subgroup.eq_bot_iff_forall]
  exact forall_congr' fun g => imp_congr_left (mem_ker_iff_char_eq V (hG g))

section Family

variable {ι : Type*}

/-- **The common kernel of a family of representations, as a set of character equations.** An
element lies in it exactly when every character of the family takes at it the value it takes at the
identity. Together with `FDRep.normal_iInf_ker` this is how a character computation produces a
normal subgroup. -/
theorem coe_iInf_ker (W : ι → FDRep ℂ G) (hG : IsMulTorsion G) :
    ((⨅ i, (W i).ρ.ker : Subgroup G) : Set G)
      = {g | ∀ i, (W i).character g = (W i).character 1} :=
  Set.ext fun g => by
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    exact forall_congr' fun i => mem_ker_iff_char_eq (W i) (hG g)

end Family

end FDRep
