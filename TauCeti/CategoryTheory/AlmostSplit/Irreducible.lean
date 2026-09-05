/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Sequence
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# The irreducible morphisms attached to an almost-split sequence

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be an almost-split (Auslander-Reiten) sequence, that is, a short exact
sequence whose first map is left almost split and whose second map is right almost split
(`CategoryTheory.ShortComplex.IsAlmostSplit`). This file identifies the **irreducible morphisms**
at its two ends: `B ⟶ C` and `A ⟶ B` are themselves irreducible, and more precisely

* the irreducible morphisms `X ⟶ C` are exactly the composites `X ⟶ B ⟶ C` of a **split
  monomorphism** into the middle term with `B ⟶ C`, and dually
* the irreducible morphisms `A ⟶ Y` are exactly the composites `A ⟶ B ⟶ Y` of `A ⟶ B` with a
  **split epimorphism** out of the middle term.

This is what makes the middle term of an almost-split sequence the receptacle of all the
irreducible morphisms at its ends, and hence what determines the arrows of the Auslander-Reiten
quiver at the vertex `C`: an arrow `[X] → [C]` exists exactly when the nonzero `X` is a **retract**
of `B`. Only a retraction is produced here, since the ambient category is not asked to have
biproducts or to be idempotent-complete; where it is — the module categories Auslander-Reiten
theory is read in — a retract of `B` is a direct summand of it.
One half of each equivalence is already the sharpened factorization
`TauCeti.IsRightAlmostSplit.exists_isSplitMono_of_isIrreducibleMorphism` of
`TauCeti/CategoryTheory/AlmostSplit/Basic.lean`; the content here is the converse, that composing
`B ⟶ C` with a split monomorphism into the middle term never destroys irreducibility.

## The hypotheses

Two things are asked beyond the sequence itself.

**The two maps of the sequence are radical**, that is, they lie in the radical of the category
(`TauCeti.jacobsonRadical`), so that `𝟙 - t ≫ S.f` and `𝟙 - S.g ≫ t` are invertible for every `t`.
That invertibility is the whole engine of the two proofs, and it is the only thing they use about
`S.f` and `S.g` beyond the almost-split property, so it is asked for directly rather than deduced
from a hypothesis on the objects. In the situation the results are meant for both memberships are
automatic: as soon as the two ends have **local endomorphism rings** —
they are indecomposable (`TauCeti.IsRightAlmostSplit.indecomposable`), and in the Krull-Schmidt
categories where Auslander-Reiten theory lives, finite-dimensional modules over a
finite-dimensional algebra, indecomposability *is* locality of the endomorphism ring — `S.f` is
radical because it is not a split monomorphism and `S.g` is radical because it is not a split
epimorphism. That derivation is
`CategoryTheory.ShortComplex.IsAlmostSplit.mem_jacobsonRadical_f` and `.mem_jacobsonRadical_g`.

**The object at the other end of the tested morphism has a nonzero identity.** Without it the
statements are false rather than merely unprovable: for a zero object `X` the zero map `X ⟶ C` is
`0 ≫ S.g` with `0 : X ⟶ S.X₂` a split monomorphism, and the zero morphism is never irreducible
(`TauCeti.not_isIrreducibleMorphism_zero`). The condition `𝟙 X ≠ 0` is `¬ IsZero X`
(`CategoryTheory.Limits.IsZero.iff_id_eq_zero`); it is automatic for the indecomposable `X` an
arrow of the Auslander-Reiten quiver runs from.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.mem_jacobsonRadical_f` and `.mem_jacobsonRadical_g`:
  **both maps of an almost-split sequence are radical** once the corresponding end has a local
  endomorphism ring; these supply the radical hypotheses of everything below.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_comp_g`: **a split monomorphism
  into the middle term followed by the second map is irreducible**, and dually
  `.isIrreducibleMorphism_f_comp`.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_g` and
  `.isIrreducibleMorphism_f`: **both maps of an almost-split sequence are irreducible morphisms**,
  the case of the identity of the middle term.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_iff_exists_isSplitMono` and
  `.isIrreducibleMorphism_iff_exists_isSplitEpi`: **the irreducible morphisms at either end of an
  almost-split sequence are exactly those factoring through the middle term by a split
  monomorphism, resp. a split epimorphism.**

## Implementation notes

The factorization clause of irreducibility is proved by the classical Jacobson-radical argument,
not by an idempotent-splitting one, so no biproducts, no abelian structure and no Krull-Schmidt
hypothesis are needed. The ambient category is preadditive and `CategoryTheory.Balanced`, which is
exactly what makes `S.f` a kernel of `S.g` and `S.g` a cokernel of `S.f`: exactness is consumed
only through `CategoryTheory.ShortComplex.Exact.lift'` and `.desc'`, whose remaining hypotheses
`Mono S.f` and `Epi S.g` are supplied by short exactness. An abelian category — the setting of
Auslander-Reiten theory — is balanced.

Given a factorization `p ≫ q` of `i ≫ S.g` with `q` not a split epimorphism, the right almost
split property lifts `q` to `w : Z ⟶ S.X₂`, and the difference `i - p ≫ w` dies under `S.g`, so it
is `t ≫ S.f` for some `t`. Composing with a retraction `r` of `i` turns this into
`p ≫ (w ≫ r) = 𝟙 X - t ≫ (S.f ≫ r)`, whose right-hand side is invertible because `S.f ≫ r` is
radical; a composite that is invertible has a split monomorphism for its first factor. The proof
for the other end is the same argument read backwards, and is written out rather than obtained
from `CategoryTheory.ShortComplex.IsAlmostSplit.op`, which would need the radical of `Cᵒᵖ`
identified with the radical of `C`.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.5.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.10.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S : ShortComplex C}

namespace IsAlmostSplit

variable (hS : IsAlmostSplit S)

include hS

/-! ### The two maps of an almost-split sequence are radical -/

omit [Balanced C] in
/-- **The first map of an almost-split sequence is radical**, as soon as its source has a local
endomorphism ring: it is not a split monomorphism
(`TauCeti.IsLeftAlmostSplit.not_isSplitMono`), and out of an object with a local endomorphism ring
that is exactly radicality (`TauCeti.mem_jacobsonRadical_iff_not_isSplitMono`). -/
theorem mem_jacobsonRadical_f [IsLocalRing (End S.X₁)] : S.f ∈ jacobsonRadical S.X₁ S.X₂ :=
  mem_jacobsonRadical_iff_not_isSplitMono.2 hS.isLeftAlmostSplit_f.not_isSplitMono

omit [Balanced C] in
/-- **The second map of an almost-split sequence is radical**, as soon as its target has a local
endomorphism ring, the dual of
`CategoryTheory.ShortComplex.IsAlmostSplit.mem_jacobsonRadical_f`: it is not a split epimorphism,
and into an object with a local endomorphism ring that is exactly radicality
(`TauCeti.mem_jacobsonRadical_iff_not_isSplitEpi`). -/
theorem mem_jacobsonRadical_g [IsLocalRing (End S.X₃)] : S.g ∈ jacobsonRadical S.X₂ S.X₃ :=
  mem_jacobsonRadical_iff_not_isSplitEpi.2 hS.isRightAlmostSplit_g.not_isSplitEpi

variable (hf : S.f ∈ jacobsonRadical S.X₁ S.X₂) (hg : S.g ∈ jacobsonRadical S.X₂ S.X₃)

include hf hg

/-! ### Irreducible morphisms into the right-hand end -/

/-- **A split monomorphism into the middle term of an almost-split sequence, followed by the
second map, is an irreducible morphism.**

The two maps of the sequence are asked to be radical, which they are as soon as the two ends have
local endomorphism rings (`CategoryTheory.ShortComplex.IsAlmostSplit.mem_jacobsonRadical_f` and
`.mem_jacobsonRadical_g`). The source `X` is asked only to be nonzero, in the form `𝟙 X ≠ 0`: for
a zero object the composite is the zero morphism, which is never irreducible.

Neither of the two negative clauses of irreducibility needs the factorization property. That
`i ≫ S.g` is not a split epimorphism is because `S.g` is not one; that it is not a split
monomorphism is because it is radical, `S.g` being so. -/
theorem isIrreducibleMorphism_comp_g {X : C} (hX : 𝟙 X ≠ 0) {i : X ⟶ S.X₂}
    (hi : IsSplitMono i) : IsIrreducibleMorphism (i ≫ S.g) := by
  have := hS.shortExact.mono_f
  refine isIrreducibleMorphism_iff.2 ⟨?_, ?_, ?_⟩
  · exact not_isSplitMono_of_mem_jacobsonRadical hX (comp_mem_jacobsonRadical_left i hg)
  · exact fun _ => hS.isRightAlmostSplit_g.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp i S.g)
  · intro Z p q hpq
    by_cases hq : IsSplitEpi q
    · exact Or.inr hq
    refine Or.inl ?_
    -- The almost split property lifts `q` through `S.g`.
    obtain ⟨w, hw⟩ := hS.isRightAlmostSplit_g.factors Z q hq
    -- The difference of the two factorizations of `i ≫ S.g` through `S.g` comes from `S.X₁`.
    have hzero : (i - p ≫ w) ≫ S.g = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hw, hpq, sub_self]
    obtain ⟨t, ht⟩ := hS.shortExact.exact.lift' (i - p ≫ w) hzero
    have hpw : p ≫ w = i - t ≫ S.f := by rw [ht]; abel
    -- `S.f ≫ retraction i` is radical, so the identity minus a multiple of it is invertible.
    have hiso : IsIso (𝟙 X - t ≫ (S.f ≫ retraction i)) :=
      mem_jacobsonRadical_iff_isIso_id_sub_comp_left.1
        (comp_mem_jacobsonRadical_right hf (retraction i)) t
    have hkey : (p ≫ w) ≫ retraction i = 𝟙 X - t ≫ (S.f ≫ retraction i) := by
      rw [hpw, Preadditive.sub_comp, Category.assoc, IsSplitMono.id]
    have hiso' : IsIso (p ≫ (w ≫ retraction i)) := by rw [← Category.assoc, hkey]; exact hiso
    exact isSplitMono_of_isSplitMono_comp p (w ≫ retraction i)

/-- **The second map of an almost-split sequence is an irreducible morphism**, the case of the
identity of the middle term in
`CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_comp_g`. -/
theorem isIrreducibleMorphism_g : IsIrreducibleMorphism S.g := by
  have h := hS.isIrreducibleMorphism_comp_g hf hg (X := S.X₂)
    (fun h0 => hS.not_isZero_X₂ ((IsZero.iff_id_eq_zero _).2 h0)) (i := 𝟙 S.X₂) inferInstance
  rwa [Category.id_comp] at h

/-- **The irreducible morphisms into the right-hand end of an almost-split sequence are exactly
the split monomorphisms into its middle term composed with its second map**, for a nonzero source
`X`, in the form `hX : 𝟙 X ≠ 0`.

So the sources of the irreducible morphisms into `S.X₃` are precisely the nonzero retracts of
`S.X₂`: this is the statement that reads off the arrows of the Auslander-Reiten quiver ending at
`S.X₃` from the middle term of the sequence. -/
theorem isIrreducibleMorphism_iff_exists_isSplitMono {X : C} (hX : 𝟙 X ≠ 0) (h : X ⟶ S.X₃) :
    IsIrreducibleMorphism h ↔ ∃ i : X ⟶ S.X₂, IsSplitMono i ∧ i ≫ S.g = h := by
  refine ⟨fun hh => hS.isRightAlmostSplit_g.exists_isSplitMono_of_isIrreducibleMorphism hh,
    fun hi => ?_⟩
  obtain ⟨i, hi, rfl⟩ := hi
  exact hS.isIrreducibleMorphism_comp_g hf hg hX hi

/-! ### Irreducible morphisms out of the left-hand end -/

/-- **The first map of an almost-split sequence followed by a split epimorphism out of its middle
term is an irreducible morphism**, the dual of
`CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_comp_g`.

As there, the two maps of the sequence are asked to be radical, and the target `Y` is asked to be
nonzero, in the form `hY : 𝟙 Y ≠ 0`: for a zero object the composite is the zero morphism, which
is never irreducible. -/
theorem isIrreducibleMorphism_f_comp {Y : C} (hY : 𝟙 Y ≠ 0) {p : S.X₂ ⟶ Y}
    (hp : IsSplitEpi p) : IsIrreducibleMorphism (S.f ≫ p) := by
  have := hS.shortExact.epi_g
  refine isIrreducibleMorphism_iff.2 ⟨?_, ?_, ?_⟩
  · exact fun _ => hS.isLeftAlmostSplit_f.not_isSplitMono (isSplitMono_of_isSplitMono_comp S.f p)
  · exact not_isSplitEpi_of_mem_jacobsonRadical hY (comp_mem_jacobsonRadical_right hf p)
  · intro Z a b hab
    by_cases ha : IsSplitMono a
    · exact Or.inl ha
    refine Or.inr ?_
    -- The almost split property extends `a` along `S.f`.
    obtain ⟨w, hw⟩ := hS.isLeftAlmostSplit_f.factors Z a ha
    -- The difference of the two factorizations of `S.f ≫ p` through `S.f` descends to `S.X₃`.
    have hzero : S.f ≫ (p - w ≫ b) = 0 := by
      rw [Preadditive.comp_sub, ← Category.assoc, hw, hab, sub_self]
    obtain ⟨t, ht⟩ := hS.shortExact.exact.desc' (p - w ≫ b) hzero
    have hwb : w ≫ b = p - S.g ≫ t := by rw [ht]; abel
    -- `section_ p ≫ S.g` is radical, so the identity minus a multiple of it is invertible.
    have hiso : IsIso (𝟙 Y - (section_ p ≫ S.g) ≫ t) :=
      mem_jacobsonRadical_iff_isIso_id_sub_comp_right.1
        (comp_mem_jacobsonRadical_left (section_ p) hg) t
    have hkey : (section_ p ≫ w) ≫ b = 𝟙 Y - (section_ p ≫ S.g) ≫ t := by
      rw [Category.assoc, hwb, Preadditive.comp_sub, IsSplitEpi.id, ← Category.assoc]
    have hiso' : IsIso ((section_ p ≫ w) ≫ b) := by rw [hkey]; exact hiso
    exact isSplitEpi_of_isSplitEpi_comp (section_ p ≫ w) b

/-- **The first map of an almost-split sequence is an irreducible morphism**, the case of the
identity of the middle term in
`CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_f_comp`. -/
theorem isIrreducibleMorphism_f : IsIrreducibleMorphism S.f := by
  have h := hS.isIrreducibleMorphism_f_comp hf hg (Y := S.X₂)
    (fun h0 => hS.not_isZero_X₂ ((IsZero.iff_id_eq_zero _).2 h0)) (p := 𝟙 S.X₂) inferInstance
  rwa [Category.comp_id] at h

/-- **The irreducible morphisms out of the left-hand end of an almost-split sequence are exactly
its first map composed with a split epimorphism out of its middle term**, for a nonzero target
`Y`, in the form `hY : 𝟙 Y ≠ 0`; the dual of
`CategoryTheory.ShortComplex.IsAlmostSplit.isIrreducibleMorphism_iff_exists_isSplitMono`. -/
theorem isIrreducibleMorphism_iff_exists_isSplitEpi {Y : C} (hY : 𝟙 Y ≠ 0) (h : S.X₁ ⟶ Y) :
    IsIrreducibleMorphism h ↔ ∃ p : S.X₂ ⟶ Y, IsSplitEpi p ∧ S.f ≫ p = h := by
  refine ⟨fun hh => hS.isLeftAlmostSplit_f.exists_isSplitEpi_of_isIrreducibleMorphism hh,
    fun hp => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hp
  exact hS.isIrreducibleMorphism_f_comp hf hg hY hp

end IsAlmostSplit

end CategoryTheory.ShortComplex
