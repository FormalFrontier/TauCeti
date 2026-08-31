/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Irreducible
public import TauCeti.RepresentationTheory.LinearCharacter

/-!
# Inducing a linear character from a normal subgroup

Let `N` be a normal subgroup of a finite group `G` and let `χ : N →* kˣ` be a linear character,
carried by the one-dimensional representation `FDRep.ofLinearCharacter χ`.  The Mackey
irreducibility criterion for a normal subgroup, `TauCeti.simple_indFDRep_iff_of_normal`, asks that
the representation be irreducible -- automatic here, a line having no proper nonzero
subrepresentation -- and that no conjugate `{}^s (χ)` for `s ∉ N` be isomorphic to `χ`.  On a line
that second condition is an identity in `N →* kˣ`, because a one-dimensional representation is
determined by the scalar it acts by: `FDRep.nonempty_iso_ofLinearCharacter_iff`.  The criterion
therefore becomes elementary group theory: `Ind_N^G χ` is irreducible exactly when **no element
outside `N` stabilizes `χ`**, that is, when for every `s ∉ N` there is an `x ∈ N` with
`χ (s x s⁻¹) ≠ χ x`.

When `χ` is moreover **faithful** the condition loses all reference to `χ`: `χ (s x s⁻¹) ≠ χ x`
becomes `s x s⁻¹ ≠ x`, so the induced representation is irreducible exactly when the centralizer
of `N` in `G` is contained in `N`.  This is the form the classical examples are checked in --
`A₃ ◁ S₃` in `TauCeti.RepresentationTheory.Induction.Mackey.SymmetricThree`, and the rotation
subgroup of a dihedral group -- where the ambient group is visibly nonabelian on `N`.

The whole file is the normal-subgroup half of the roadmap's dichotomy: nothing induced from the
*non-normal* point stabilizer of `S₃` is irreducible
(`TauCeti.not_simple_indFDRep_stabilizer_perm_fin_three`), while a faithful character of the
normal subgroup `A₃` does induce irreducibly.

## Main statements

* `TauCeti.conjNormalFDRep_ofLinearCharacter`: conjugating a one-dimensional representation
  conjugates its linear character, as an equality of objects.
* `TauCeti.simple_indFDRep_ofLinearCharacter_iff`: **the Mackey criterion for an induced linear
  character** -- `Ind_N^G χ` is irreducible exactly when no element outside `N` stabilizes `χ`.
* `TauCeti.simple_indFDRep_ofLinearCharacter_iff_centralizer_le`: for a faithful `χ`, exactly when
  `C_G(N) ≤ N`.

## References

The Layer 4 "normal-subgroup corollary" of
[the induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
read on a linear character, as its "Mackey on a small group" and "`D₄` dihedral induction" worked
examples require.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.4, Proposition 23 and its
  corollary for a normal subgroup.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

section Conjugation

variable {k G : Type u} [CommRing k] [Group G] {N : Subgroup G} [N.Normal]

/-- **Conjugating a one-dimensional representation conjugates its linear character.**  Both sides
are the line `k` with `x : N` acting by the scalar `χ (g⁻¹ x g)`, so this is an equality of
objects of `FDRep k N`, not merely an isomorphism. -/
@[simp]
theorem conjNormalFDRep_ofLinearCharacter (g : G) (χ : N →* kˣ) :
    conjNormalFDRep g (FDRep.ofLinearCharacter χ) =
      FDRep.ofLinearCharacter (χ.comp (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom) :=
  FDRep.actionRes_obj_ofLinearCharacter _ _

/-- **A conjugate of a one-dimensional representation is isomorphic to it exactly when the
conjugated linear character is the same one.**  There is no room for anything but an equality of
scalars: a line is determined by the character it carries.

Not a `simp` lemma: with `conjNormalFDRep_ofLinearCharacter` tagged, `simp` already rewrites this
left-hand side to `χ.comp ↑(MulAut.conjNormal g)⁻¹ = χ` through
`FDRep.nonempty_iso_ofLinearCharacter_iff`, so tagging it too is a `simpNF` violation. This is the
pointwise spelling of that same condition. -/
theorem nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff (g : G) (χ : N →* kˣ) :
    Nonempty (conjNormalFDRep g (FDRep.ofLinearCharacter (k := k) χ) ≅ FDRep.ofLinearCharacter χ) ↔
      ∀ x : N, χ (MulAut.conjNormal g⁻¹ x) = χ x := by
  rw [conjNormalFDRep_ofLinearCharacter, FDRep.nonempty_iso_ofLinearCharacter_iff]
  exact DFunLike.ext_iff

end Conjugation

section Criterion

variable {k G : Type u} [Field k] [Group G] {N : Subgroup G} [N.Normal] [Finite G] [IsAlgClosed k]
  [CharZero k]

/-- **The Mackey irreducibility criterion for an induced linear character.**  For a normal
subgroup `N ◁ G` and a linear character `χ : N →* kˣ`, the induced representation `Ind_N^G χ` is
irreducible exactly when **no element of `G` outside `N` stabilizes `χ`**: for every `s ∉ N` some
`x ∈ N` has `χ (s x s⁻¹) ≠ χ x`.

The irreducibility of `χ` itself, which the general criterion also asks for, is automatic: a line
has no proper nonzero subrepresentation. -/
theorem simple_indFDRep_ofLinearCharacter_iff (χ : N →* kˣ) :
    Simple (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) ↔
      ∀ s ∉ N, ∃ x : N, χ (MulAut.conjNormal s x) ≠ χ x := by
  rw [simple_indFDRep_iff_of_normal]
  simp only [not_nonempty_iff.symm, nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff, not_forall,
    and_iff_right (FDRep.simple_ofLinearCharacter χ)]
  -- The general criterion conjugates by `s⁻¹`; reindex over the complement of `N`, which is
  -- closed under inversion.
  exact ⟨fun h s hs => by simpa using h s⁻¹ (fun hc => hs (by simpa using inv_mem hc)),
    fun h s hs => by simpa using h s⁻¹ (fun hc => hs (by simpa using inv_mem hc))⟩

/-- **A faithful linear character of a normal subgroup induces irreducibly exactly when the
centralizer of that subgroup is no bigger than the subgroup.**  Faithfulness turns the Mackey
condition `χ (s x s⁻¹) ≠ χ x` into `s x s⁻¹ ≠ x`, so all reference to `χ` disappears and only the
position of `N` inside `G` is left. -/
theorem simple_indFDRep_ofLinearCharacter_iff_centralizer_le {χ : N →* kˣ}
    (hχ : Function.Injective χ) :
    Simple (indFDRep (FDRep.ofLinearCharacter (k := k) χ)) ↔
      Subgroup.centralizer (N : Set G) ≤ N := by
  rw [simple_indFDRep_ofLinearCharacter_iff]
  constructor
  · intro h s hs
    by_contra hsN
    obtain ⟨x, hx⟩ := h s hsN
    refine hx (congrArg χ (Subtype.ext ?_))
    rw [MulAut.conjNormal_apply, ← Subgroup.mem_centralizer_iff.mp hs (x : G) x.2]
    group
  · intro h s hs
    by_contra hall
    refine hs (h (Subgroup.mem_centralizer_iff.mpr fun x hxN => ?_))
    have hx : s * x * s⁻¹ = x := by
      have hconj := congrArg Subtype.val (hχ (not_not.mp (not_exists.mp hall ⟨x, hxN⟩)))
      rwa [MulAut.conjNormal_apply] at hconj
    conv_lhs => rw [← hx]
    group

end Criterion

end TauCeti
