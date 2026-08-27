/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.OrbitCount
public import TauCeti.GroupTheory.SpecificGroups.Braid

/-!
# Markov moves and Markov equivalence of braids

Closing up a braid on `n` strands, by joining the `i`-th endpoint at the top to the `i`-th
endpoint at the bottom, presents an oriented link. After forgetting its framing, two such braids,
possibly on different numbers of strands, close to isotopic oriented links exactly when they are
related by a chain of the two *Markov moves*:
conjugation `b ↦ c * b * c⁻¹` inside a fixed braid group, and stabilization
`b ↦ strandIncl b * (σ_last)^(±1)`, which adds a strand and crosses it once, in either sense,
with the previous one. That is Markov's theorem; only the moves, not the theorem, are formalized
here, since the link presentation the theorem is stated against does not exist yet.

This file introduces framed braid-closure data and its forgetful map, the unframed
braids-of-any-width that the ordinary Markov moves act on, the equivalence relation
`TauCeti.MarkovEquiv` they generate, and the first invariant of that relation: the number of
components of the closure. It does not yet define the equivalence relation on framed braid
closures; ordinary stabilization changes the blackboard framing.

## Main definitions

* `TauCeti.MarkovBraid`: a braid together with the number of strands it is a braid on.
* `TauCeti.FramedMarkovBraid`: a braid closure with an integer framing coefficient on each
  component; its `forgetFraming` projection drops those coefficients.
* `TauCeti.MarkovBraid.componentCount`: the number of components of the closure of the braid,
  computed as the number of orbits of the underlying permutation of the strands.
* `TauCeti.IsMarkovMove`: the generating moves, three constructors for the two moves —
  conjugation, and stabilization in each of its two signs.
* `TauCeti.MarkovEquiv`: Markov equivalence, the equivalence relation they generate.

## Main results

* `TauCeti.MarkovBraid.componentCount_conj`, `TauCeti.MarkovBraid.componentCount_stabilize` and
  `TauCeti.MarkovBraid.componentCount_stabilizeInv`: each move separately preserves the number of
  components of the closure.
* `TauCeti.MarkovEquiv.componentCount_eq`: Markov-equivalent braids have closures with the same
  number of components. This is the invariant that keeps the relation from being everything.
* `TauCeti.markovEquiv_sigma_last_one_one`: the trivial braid on one strand and the single
  crossing `σ₀` on two strands are Markov equivalent.
* `TauCeti.not_markovEquiv_one_of_ne`: trivial braids on different numbers of strands are *not*
  Markov equivalent.
* `TauCeti.not_markovEquiv_sigma_last_one_two`: the single crossing and the trivial braid on two
  strands are not Markov equivalent.
* `TauCeti.MarkovEquiv.equivalence`: Markov equivalence is an equivalence relation.
* `TauCeti.MarkovEquiv.induction`: the induction principle that makes the `Prop`-valued
  definition of Markov equivalence usable outside this file.

## Implementation notes

A braid on `n` strands is `TauCeti.BraidGroup n`, a different type for each `n`, while the
stabilization move leaves that type; so the moves are stated on the total space
`TauCeti.MarkovBraid`, whose field `predStrands` records the strand count minus one. Every link
that is a braid closure is the closure of a braid on at least one strand, and the stabilization
move needs a strand to cross the new one with, so `predStrands + 1` rather than `predStrands` is
the strand count.

The component count is read off the underlying permutation `TauCeti.BraidGroup.permHom`: in the
closure, the strand ending at position `i` is joined to the strand starting at position `i`, so
the components of the closure are exactly the orbits of that permutation on the strands. Its
invariance under stabilization is where the work is, and it is supplied by
`TauCeti/GroupTheory/Perm/OrbitCount.lean`: stabilizing adjoins a fixed point to the underlying
permutation and immediately splices it into an existing orbit.

## References

* A. A. Markov, *Über die freie Äquivalenz der geschlossenen Zöpfe*, Rec. Math. Moscou 1 (1935),
  73-78.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Theorem 2.3.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1
  (printed p. 10) and Proposition 16.10 (Chapter 16).

This advances Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), which asks for framed and oriented presentations,
the forgetful maps between them, the equivalence attached to each presentation -- "Markov moves
(braids)" -- and "braid-to-diagram via Markov" as an edge of the spanning tree of presentations.
The relation in this file is specifically the ordinary unframed relation after applying
`TauCeti.FramedMarkovBraid.forgetFraming`; framing-preserving Markov equivalence remains future
work.
-/

public section

namespace TauCeti

open BraidGroup

/-- A braid together with the number of strands it is a braid on. The Markov moves relate braids
on different numbers of strands, so they are stated on this total space rather than on a single
`TauCeti.BraidGroup n`. -/
structure MarkovBraid where
  /-- The number of strands, minus one. Every braid closure is the closure of a braid on at least
  one strand, and stabilization needs a strand to cross the new one with. -/
  predStrands : ℕ
  /-- The braid itself, on `predStrands + 1` strands. -/
  braid : BraidGroup (predStrands + 1)

/-- A framed oriented braid-closure presentation. The braid direction supplies the orientation.
A framing of an oriented link in `S³`, relative to the Seifert framing, is specified by one
integer coefficient on each component; the components of a braid closure are the orbits of its
underlying permutation. The projection `forgetFraming` drops this data to the ordinary unframed
braid on which `TauCeti.MarkovEquiv` is defined. -/
structure FramedMarkovBraid where
  /-- Forget the framing coefficients, retaining the underlying braid and its strand count. -/
  forgetFraming : MarkovBraid
  /-- The framing coefficient of each component, relative to its Seifert framing. -/
  framing : Quotient (Equiv.Perm.SameCycle.setoid
    (permHom (forgetFraming.predStrands + 1) forgetFraming.braid)) → ℤ

namespace MarkovBraid

/-- The number of components of the closure of a braid. In the closure, the strand arriving at
position `i` is joined to the strand leaving position `i`, so two strands lie on the same
component exactly when the underlying permutation `TauCeti.BraidGroup.permHom` carries one to the
other; the components are therefore its orbits, and this is their number. (The closure itself is
a link, which the library cannot yet express; this is the count read off the braid.) -/
noncomputable def componentCount (β : MarkovBraid) : ℕ :=
  orbitCount (permHom (β.predStrands + 1) β.braid)

/-- The trivial braid on `n + 1` strands has component count `n + 1`. Informally, its closure is
the `(n + 1)`-component unlink. -/
@[simp]
theorem componentCount_one (n : ℕ) : componentCount ⟨n, 1⟩ = n + 1 := by
  unfold componentCount
  rw [map_one, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Conjugate braids have closures with the same number of components. -/
@[simp]
theorem componentCount_conj {n : ℕ} (b c : BraidGroup (n + 1)) :
    componentCount ⟨n, c * b * c⁻¹⟩ = componentCount ⟨n, b⟩ := by
  unfold componentCount
  rw [map_mul, map_mul, map_inv, orbitCount_conj]

end MarkovBraid

/-- The permutation-level content of both stabilization moves: adjoining an uncrossed strand adds
one orbit to the underlying permutation of the strands, and crossing the new strand with the
previous one splices that orbit back into the orbit of the old last strand. -/
private theorem orbitCount_permHom_strandIncl_mul_swap {n : ℕ} (b : BraidGroup (n + 1)) :
    orbitCount (permHom (n + 2) (strandIncl b) *
        Equiv.swap (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))) =
      orbitCount (permHom (n + 1) b) := by
  have hsplice := orbitCount_mul_swap_add_one (τ := permHom (n + 2) (strandIncl b))
    (permHom_strandIncl_last b) (Fin.castSucc_lt_last (Fin.last n)).ne
  have hextend := orbitCount_add_one_eq_of_semiconj
    (f := (Fin.castSucc : Fin (n + 1) → Fin (n + 2))) (p := Fin.last (n + 1))
    (σ := permHom (n + 1) b) (τ := permHom (n + 2) (strandIncl b))
    (Fin.castSucc_injective _) (fun i ↦ (Fin.castSucc_lt_last i).ne)
    (fun _ hy ↦ Fin.eq_castSucc_of_ne_last hy) fun i ↦ (permHom_strandIncl_castSucc b i).symm
  omega

namespace MarkovBraid

/-- **Positive stabilization does not change the number of components of the closure.** -/
@[simp]
theorem componentCount_stabilize {n : ℕ} (b : BraidGroup (n + 1)) :
    componentCount ⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ = componentCount ⟨n, b⟩ := by
  unfold componentCount
  rw [map_mul, permHom_sigma_last]
  exact orbitCount_permHom_strandIncl_mul_swap b

/-- **Negative stabilization does not change the number of components of the closure.** The sign
of the new crossing is irrelevant here, a transposition being its own inverse. -/
@[simp]
theorem componentCount_stabilizeInv {n : ℕ} (b : BraidGroup (n + 1)) :
    componentCount ⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ = componentCount ⟨n, b⟩ := by
  unfold componentCount
  rw [map_mul, map_inv, permHom_sigma_last, Equiv.swap_inv]
  exact orbitCount_permHom_strandIncl_mul_swap b

end MarkovBraid

/-- The three generating **Markov moves** on braids. The first is conjugation inside a fixed braid
group; the other two add a strand and cross it once, positively or negatively, with the strand
below it. Each is stated as a move from the larger or conjugated braid *to* the smaller one; the
equivalence relation `TauCeti.MarkovEquiv` they generate is symmetric. -/
inductive IsMarkovMove : MarkovBraid → MarkovBraid → Prop
  /-- Markov move I: conjugation. -/
  | conj {n : ℕ} (b c : BraidGroup (n + 1)) : IsMarkovMove ⟨n, c * b * c⁻¹⟩ ⟨n, b⟩
  /-- Markov move II, positive stabilization: the previously-last strand crosses over the new
  strand. -/
  | stabilize {n : ℕ} (b : BraidGroup (n + 1)) :
      IsMarkovMove ⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ ⟨n, b⟩
  /-- Markov move II, negative stabilization: the previously-last strand crosses under the new
  strand. -/
  | stabilizeInv {n : ℕ} (b : BraidGroup (n + 1)) :
      IsMarkovMove ⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ ⟨n, b⟩

/-- **Unframed Markov equivalence**: the equivalence relation generated by the ordinary Markov
moves. By Markov's theorem (not formalized here), two braids are Markov equivalent exactly when
their closures are isotopic oriented links after forgetting framing. This is not the
framing-preserving relation on `TauCeti.FramedMarkovBraid`: stabilization changes the blackboard
framing. -/
def MarkovEquiv : MarkovBraid → MarkovBraid → Prop := Relation.EqvGen IsMarkovMove

namespace MarkovEquiv

/-- Markov equivalence is an equivalence relation. -/
theorem equivalence : Equivalence MarkovEquiv :=
  Relation.EqvGen.is_equivalence IsMarkovMove

@[refl]
theorem refl (β : MarkovBraid) : MarkovEquiv β β := Relation.EqvGen.refl β

@[symm]
theorem symm {β γ : MarkovBraid} (h : MarkovEquiv β γ) : MarkovEquiv γ β :=
  Relation.EqvGen.symm _ _ h

@[trans]
theorem trans {β γ δ : MarkovBraid} (h : MarkovEquiv β γ) (h' : MarkovEquiv γ δ) :
    MarkovEquiv β δ := Relation.EqvGen.trans _ _ _ h h'

/-- The induction principle for Markov equivalence. A `Prop`-valued definition does not unfold
outside the file that introduces it, so this is what makes `TauCeti.MarkovEquiv` usable: a
property holding of every single move and closed under reflexivity, symmetry and transitivity
holds of every Markov-equivalent pair. -/
theorem induction {motive : MarkovBraid → MarkovBraid → Prop}
    (move : ∀ {β γ : MarkovBraid}, IsMarkovMove β γ → motive β γ)
    (refl : ∀ β : MarkovBraid, motive β β)
    (symm : ∀ {β γ : MarkovBraid}, MarkovEquiv β γ → motive β γ → motive γ β)
    (trans : ∀ {β γ δ : MarkovBraid}, MarkovEquiv β γ → MarkovEquiv γ δ → motive β γ →
      motive γ δ → motive β δ)
    {β γ : MarkovBraid} (h : MarkovEquiv β γ) : motive β γ := by
  induction h with
  | rel _ _ hmove => exact move hmove
  | refl b => exact refl b
  | symm _ _ hbc ih => exact symm hbc ih
  | trans _ _ _ hbc hcd ih ih' => exact trans hbc hcd ih ih'

end MarkovEquiv

/-- A single Markov move is a Markov equivalence. -/
theorem IsMarkovMove.markovEquiv {β γ : MarkovBraid} (h : IsMarkovMove β γ) : MarkovEquiv β γ :=
  Relation.EqvGen.rel _ _ h

/-- A single Markov move does not change the number of components of the closure. -/
theorem IsMarkovMove.componentCount_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) :
    β.componentCount = γ.componentCount := by
  induction h with
  | conj b c => exact MarkovBraid.componentCount_conj b c
  | stabilize b => exact MarkovBraid.componentCount_stabilize b
  | stabilizeInv b => exact MarkovBraid.componentCount_stabilizeInv b

/-- **The number of components of the closure is a Markov invariant.** -/
theorem MarkovEquiv.componentCount_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.componentCount = γ.componentCount :=
  h.induction (fun hmove ↦ hmove.componentCount_eq) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih')

/-- The trivial braid on one strand and the single crossing on two strands are Markov equivalent,
by one stabilization. Informally, these are the two smallest braid presentations of the unknot. -/
theorem markovEquiv_sigma_last_one_one :
    MarkovEquiv ⟨1, sigma (Fin.last 0)⟩ ⟨0, (1 : BraidGroup 1)⟩ := by
  have h := (IsMarkovMove.stabilize (1 : BraidGroup 1)).markovEquiv
  rwa [map_one, one_mul] at h

/-- **Markov equivalence is not the total relation.** Trivial braids on different numbers of
strands have different component counts, so they are never Markov equivalent. Informally, their
closures are unlinks with different numbers of components. -/
theorem not_markovEquiv_one_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ¬ MarkovEquiv ⟨m, 1⟩ ⟨n, 1⟩ := fun h ↦ by
  have hcount := h.componentCount_eq
  rw [MarkovBraid.componentCount_one, MarkovBraid.componentCount_one] at hcount
  omega

/-- The single crossing on two strands is not Markov equivalent to the trivial braid on two
strands, since they have different component counts. Informally, their closures are the unknot
and the two-component unlink, respectively. -/
theorem not_markovEquiv_sigma_last_one_two :
    ¬ MarkovEquiv ⟨1, sigma (Fin.last 0)⟩ ⟨1, (1 : BraidGroup 2)⟩ := fun h ↦
  not_markovEquiv_one_of_ne (Nat.zero_ne_one) (markovEquiv_sigma_last_one_one.symm.trans h)

end TauCeti
