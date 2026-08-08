/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.Spanning
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Artin's induction theorem, rational form

Over an algebraically closed field `k` of characteristic zero, there is a single nonzero integer
`d` such that `d • χ` is a `ℤ`-linear combination of characters induced from irreducible characters
of cyclic subgroups, for **every** virtual character `χ` of the finite group `G`
(`TauCeti.ClassFunction.exists_zsmul_eq_sum_zsmul_ind_ofCharacter`).  Dividing by `d`, every virtual
character is a `ℚ`-linear combination of characters induced from cyclic subgroups: the induction map
`⨁_{C cyclic} R(C) → R(G)` is rationally surjective.

The proof turns the `k`-linear spanning statement of
`TauCeti.RepresentationTheory.Induction.Spanning` into an arithmetic one by a lattice descent.  The
characters induced from the cyclic subgroups span the class functions over `k`, so a subfamily of
them is a `k`-basis; that subfamily has as many members as the basis of irreducible characters
`TauCeti.basisIrreducibleCharacter`, and, being characters, its members lie in the `ℤ`-lattice that
the irreducible characters span.  The integer matrix expressing them in that basis is invertible
over `k`, so its determinant `d` is a nonzero integer, and multiplying by the adjugate expresses
`d • χᵢ` over the induced characters with integer coefficients.

## What this is not: the sharp constant

Artin's theorem in its sharp form takes the denominator to be `|G|` itself: `|G| • χ` is a
`ℤ`-linear combination of characters induced from cyclic subgroups.  The `d` produced here is the
determinant of a change-of-basis matrix, and nothing below identifies it with `|G|` or bounds it.
That refinement needs the explicit Artin identity writing `|G| • 1` as a sum of characters induced
from cyclic subgroups, together with the projection formula, and is not proved here; neither is
Brauer's integral induction theorem, whose denominator is `1`.

## Main statements

* `TauCeti.ClassFunction.exists_zsmul_eq_sum_zsmul_ind_ofCharacter`: **Artin's induction theorem,
  rational form**, in the explicit shape "some nonzero integer multiple of every virtual character
  is an integer combination of characters induced from cyclic subgroups".
* `TauCeti.ClassFunction.ind_ofCharacter_mem_virtualCharacters`: a character induced from a
  subgroup is a virtual character, the fact that lets the descent run inside the lattice.

## Implementation notes

`k` and `G` lie in the same universe here, unlike in
`TauCeti.RepresentationTheory.Induction.Spanning`: the virtual-character lattice is defined through
`FDRep k G`, and Mathlib's `Rep k G` puts the field and the group in a common universe.

The lattice descent is a general statement about a `ℤ`-lattice inside a finite-dimensional vector
space and has nothing to do with characters, but it is kept `private` here rather than given a home
of its own in the linear-algebra hierarchy, there being exactly one use of it.

## References

This proves the rational half of the "Artin's induction theorem" item of Layer 6 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, which asks for "the rational
surjectivity of `⨁_{C cyclic} R(C) → R(G)`" and, separately, for the `ℤ`-membership of `|G| • χ`;
the latter is not proved here.

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 9.2,
  Theorem 17 and its corollary.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, Wiley (1981), Section 15.
-/

public section

namespace TauCeti

namespace ClassFunction

open Matrix Module

universe u

/-- The lattice descent behind Artin's theorem, as a statement of linear algebra: if a `ℤ`-lattice
in a finite-dimensional vector space is spanned by a basis `B`, and a family `T` of lattice vectors
spans the space over the field, then some nonzero integer multiple of every lattice vector is an
integer combination of the `T`.

The integer is the determinant of the matrix expressing `T` in `B`: that matrix is a change of basis
over the field, hence has nonzero determinant, and its adjugate exhibits the combinations. -/
private theorem exists_zsmul_mem_span_int {k V ι : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [Finite ι] (B : Basis ι k V) (T : ι → V)
    (hT : ∀ j, T j ∈ Submodule.span ℤ (Set.range B))
    (hspan : Submodule.span k (Set.range T) = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ v ∈ Submodule.span ℤ (Set.range B),
      d • v ∈ Submodule.span ℤ (Set.range T) := by
  classical
  let _ := Fintype.ofFinite ι
  choose M hM using fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hT j)
  let N : Matrix ι ι ℤ := Matrix.of M
  have hMN : ∀ j, ∑ i, N j i • B i = T j := hM
  let B' : Basis ι k V :=
    basisOfTopLeSpanOfCardEqFinrank T (by rw [hspan]) (finrank_eq_card_basis B).symm
  have hB' : ⇑B' = T := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have hrepr : ∀ j i, B.repr (T j) i = (N j i : k) := by
    intro j i
    rw [← hMN j]
    simp [Finsupp.single_apply]
  have htoMatrix : B.toMatrix ⇑B' = (N.map (Int.cast : ℤ → k))ᵀ := by
    ext i j
    rw [Basis.toMatrix_apply, hB', hrepr]
    simp
  have hmap : ((N.det : ℤ) : k) = (N.map (Int.cast : ℤ → k)).det := by
    rw [show (N.map (Int.cast : ℤ → k)) = (Int.castRingHom k).mapMatrix N from rfl,
      ← RingHom.map_det]
    rfl
  have hdet : ((N.det : ℤ) : k) ≠ 0 := by
    have hone := congrArg Matrix.det (B.toMatrix_mul_toMatrix_flip B')
    rw [Matrix.det_mul, Matrix.det_one, htoMatrix, Matrix.det_transpose] at hone
    intro h
    rw [hmap] at h
    rw [h, zero_mul] at hone
    exact zero_ne_one hone
  refine ⟨N.det, by simpa using hdet, ?_⟩
  have hB : ∀ i, (N.det : ℤ) • B i ∈ Submodule.span ℤ (Set.range T) := by
    intro i
    have key : ∑ j, N.adjugate i j • T j = (N.det : ℤ) • B i := by
      calc ∑ j, N.adjugate i j • T j
          = ∑ j, ∑ l, (N.adjugate i j * N j l) • B l := by
            simp_rw [← hMN, Finset.smul_sum, smul_smul]
        _ = ∑ l, (∑ j, N.adjugate i j * N j l) • B l := by
            rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul]
        _ = ∑ l, ((N.adjugate * N) i l) • B l := by simp_rw [Matrix.mul_apply]
        _ = (N.det : ℤ) • B i := by rw [Matrix.adjugate_mul]; simp [Matrix.one_apply]
    rw [← key]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro - ⟨i, rfl⟩
    exact hB i
  · simp
  · intro x y _ _ hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hx

variable {k G : Type u} [Field k] [Group G] [Finite G]

/-- **A character induced from a subgroup is a virtual character.**  Inducing the class function of
a finite-dimensional representation gives the class function of the induced representation
(`TauCeti.ClassFunction.ind_ofFDRep`), and a character is a virtual character. -/
theorem ind_ofCharacter_mem_virtualCharacters (S : Subgroup G) {n : ℕ}
    (ρ : Representation k S (Fin n → k)) :
    ((ind S (ofCharacter ρ) : ClassFunction k G) : G → k) ∈ virtualCharacters k G := by
  have hof : (ofCharacter ρ : ClassFunction k S) = ofFDRep (FDRep.of ρ) :=
    (ofFDRep_eq_ofCharacter (FDRep.of ρ)).symm
  have hind : ind S (ofCharacter ρ) = ofFDRep (indFDRep (k := k) (G := G) (FDRep.of ρ)) := by
    rw [hof, ClassFunction.ind_ofFDRep]
  rw [hind, show ((ofFDRep (indFDRep (k := k) (G := G) (FDRep.of ρ)) : ClassFunction k G) : G → k)
      = (indFDRep (k := k) (G := G) (FDRep.of ρ)).character from funext fun g => ofFDRep_apply _ g]
  exact character_mem_virtualCharacters _

section AlgClosed

variable [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- A class function that is a virtual character lies in the `ℤ`-span of the basis of irreducible
characters: the lattice is the `ℤ`-span of the irreducible characters
(`TauCeti.mem_virtualCharacters_iff`), and those are exactly the basis vectors. -/
private theorem mem_span_int_range_basisIrreducibleCharacter {f : ClassFunction k G}
    (hf : (f : G → k) ∈ virtualCharacters k G) :
    f ∈ Submodule.span ℤ (Set.range (basisIrreducibleCharacter k G)) := by
  obtain ⟨c, hc⟩ := mem_virtualCharacters_iff.mp hf
  have hbasis : ∀ i, ((basisIrreducibleCharacter k G i : ClassFunction k G) : G → k) =
      irreducibleCharacter k i := fun i => funext fun g => basisIrreducibleCharacter_apply i g
  have hsum : f = ∑ i, c i • basisIrreducibleCharacter k G i := by
    refine Subtype.ext (hc.trans (funext fun g => ?_))
    rw [Submodule.coe_sum]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Int.cast_smul_eq_zsmul k (c i), SetLike.val_smul, hbasis]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end AlgClosed

variable (k G)

/-- **Artin's induction theorem, rational form.**  Over an algebraically closed field of
characteristic zero there is a nonzero integer `d`, independent of the character, such that `d • f`
is an integer combination of characters induced from irreducible characters of cyclic subgroups of
`G`, for every virtual character `f`.  Equivalently, after inverting `d`, every virtual character is
a `ℚ`-linear combination of characters induced from cyclic subgroups: the induction map
`⨁_{C cyclic} R(C) → R(G)` is rationally surjective.

The sharp form of the theorem takes `d = |G|`; that is not proved here, and the `d` produced is a
change-of-basis determinant.  See the module docstring. -/
theorem exists_zsmul_eq_sum_zsmul_ind_ofCharacter [IsAlgClosed k] [CharZero k] :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ f ∈ virtualCharacters k G,
      ∃ (m : ℕ) (C : Fin m → Subgroup G) (_ : ∀ i, IsCyclic (C i)) (n : Fin m → ℕ)
        (ρ : ∀ i, Representation k (C i) (Fin (n i) → k)) (_ : ∀ i, (ρ i).IsIrreducible)
        (c : Fin m → ℤ),
        ∑ i, c i • ((ind (C i) (ofCharacter (ρ i)) : ClassFunction k G) : G → k) = d • f := by
  classical
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let 𝒢 : Set (ClassFunction k G) :=
    {f | ∃ S ∈ {S : Subgroup G | IsCyclic S}, ∃ (n : ℕ) (ρ : Representation k S (Fin n → k)),
      ρ.IsIrreducible ∧ ind S (ofCharacter ρ) = f}
  have hmem : ∀ f : ClassFunction k G, f ∈ 𝒢 ↔
      ∃ S ∈ {S : Subgroup G | IsCyclic S}, ∃ (n : ℕ) (ρ : Representation k S (Fin n → k)),
        ρ.IsIrreducible ∧ ind S (ofCharacter ρ) = f := fun _ => Iff.rfl
  have hspan : Submodule.span k 𝒢 = ⊤ :=
    top_le_iff.mp <| ((cyclicInducedCharacters_eq_inducedCharactersFrom (k := k) (G := G)) ▸
        (cyclicInducedCharacters_eq_top (k := k) (G := G)).ge).trans <|
      inducedCharactersFrom_le_iff.mpr fun S hS n ρ hρ =>
        Submodule.subset_span ((hmem _).mpr ⟨S, hS, n, ρ, hρ, rfl⟩)
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent k 𝒢
  let Bb : Basis b k (ClassFunction k G) :=
    Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  let B := basisIrreducibleCharacter k G
  let e : Fin (Nat.card (ConjClasses G)) ≃ b := B.indexEquiv Bb
  let T : Fin (Nat.card (ConjClasses G)) → ClassFunction k G := fun i => (e i : ClassFunction k G)
  have hTmem : ∀ i, T i ∈ 𝒢 := fun i => hbsub (e i).2
  have hTspan : Submodule.span k (Set.range T) = ⊤ := by
    have : Set.range T = b := by
      rw [show T = Subtype.val ∘ e from rfl, Set.range_comp, e.range_eq_univ, Set.image_univ,
        Subtype.range_coe]
    rw [this, hbspan, hspan]
  obtain ⟨d, hd, hlattice⟩ := exists_zsmul_mem_span_int B T
    (fun j => mem_span_int_range_basisIrreducibleCharacter
      (by obtain ⟨S, -, n, ρ, -, hρ⟩ := (hmem _).mp (hTmem j)
          exact hρ ▸ ind_ofCharacter_mem_virtualCharacters S ρ))
    hTspan
  refine ⟨d, hd, fun f hf => ?_⟩
  have hfmem : (⟨f, virtualCharacters_le_classFunction hf⟩ : ClassFunction k G) ∈
      Submodule.span ℤ (Set.range B) := mem_span_int_range_basisIrreducibleCharacter hf
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hlattice _ hfmem)
  choose C hC n ρ hρ hTeq using fun i => (hmem _).mp (hTmem i)
  refine ⟨Nat.card (ConjClasses G), C, hC, n, ρ, hρ, c, ?_⟩
  have hcoe := congrArg (fun F : ClassFunction k G => (F : G → k)) hc
  simpa [hTeq, Submodule.coe_sum] using hcoe

end ClassFunction

end TauCeti
