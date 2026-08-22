/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Eigenrow
public import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# The eigenrows of the class-multiplication matrices are the central characters

Let `G` be a finite group and `k` an algebraically closed field in which `|G|` is invertible. The
class sums `K_C` are a basis of the centre `Z(k[G])`, and the class-multiplication matrices `Mᵢ`
record multiplication by `K_{Cᵢ}` in that basis. A **normalized common left eigenrow** of the family
`{Mᵢ}` is a function `v` on the conjugacy classes with `v (ConjClasses.mk 1) = 1` and
`v ᵥ* Mᵢ = v Cᵢ • v` for every class; `TauCeti.isClassEigenrow_iff_exists_algHom` identifies these
with the `k`-algebra homomorphisms `Z(k[G]) →ₐ[k] k`, by a computation inside the class algebra that
knows nothing about representations.

This file supplies the representation theory that computation is missing: **those algebra
homomorphisms are exactly the central characters `ωᵪ` of the irreducible representations of `G`**.
Collecting their values on the class sums gives the **central character table**
`TauCeti.centralCharacterTable k G`, the matrix `Ω` of the Burnside--Dixon--Schneider algorithm, and
`TauCeti.isClassEigenrow_iff_exists_centralCharacterTable_eq` says that its rows are precisely the
normalized common left eigenrows. So an eigenrow computed from the structure constants alone is a
central character, and there are exactly as many of them as `G` has conjugacy classes.

The proof runs through a Wedderburn presentation `k[G] ≃ₐ[k] ∏ᵢ Matₙᵢ(k)`. Such a presentation
splits the centre as the product algebra `∏ᵢ k` (`TauCeti.centerMonoidAlgebraAlgEquivPi`), whose
only algebra homomorphisms to `k` are the coordinate evaluations (`AlgHom.eq_piEvalAlgHom`);
the evaluation at a block is the central character of the representation that block carries
(`TauCeti.centralCharacter_blockRepresentation`), and every irreducible representation is equivalent
to a block, hence has the same central character as one.

## Main definitions

* `TauCeti.centralCharacterTable`: the central character table `Ω` of `G`.
* `TauCeti.finEquivCentralCharacter`: the enumeration of the algebra homomorphisms out of
  `Z(k[G])` by the irreducible representations, and `TauCeti.finEquivEigenrow`, the same for the
  normalized common left eigenrows.
* `TauCeti.basisCentralCharacterTable`: the rows of `Ω`, as a basis of the functions on the
  conjugacy classes.

## Main statements

* `TauCeti.exists_centralCharacter_eq`: **every algebra homomorphism out of the centre is a central
  character**, and `TauCeti.centralCharacter_irreducibleRepresentation_injective`: **distinct
  irreducibles have distinct central characters**.
* `TauCeti.isClassEigenrow_iff_exists_centralCharacterTable_eq`: **the normalized common left
  eigenrows of the class-multiplication matrices are exactly the rows of `Ω`**, and
  `TauCeti.card_normalized_isClassEigenrow`: there are as many of them as conjugacy classes. The
  version requiring only a split centre is
  `TauCeti.card_normalized_isClassEigenrow_of_nonempty_center_algEquiv`.
  Dropping the normalization only adds scalar multiples:
  `TauCeti.exists_eq_smul_centralCharacterTable` says **every nonzero common left eigenvector of the
  class-multiplication matrices is a multiple of a row of `Ω`**, and
  `TauCeti.linearIndependent_centralCharacterTable` says those rows are linearly independent, hence
  a basis.
* `TauCeti.eq_of_centralCharacter_eq`: **the central characters separate the points of the centre**.
* `TauCeti.centralCharacterTable_mul_characterDegree`: the conversion `ωᵪ(K_C) · χ(1) = |C| · χ(g)`
  between `Ω` and the ordinary character table `TauCeti.characterTable`, with the two quotient
  forms `TauCeti.centralCharacterTable_eq_div` and `TauCeti.characterTable_eq_div` reading each
  table off the other.

## Implementation notes

The rows of `Ω` are indexed by the same enumeration `TauCeti.finEquivIrreducibleCharacters` of the
irreducible characters as the rows of `TauCeti.characterTable`, so the two tables are aligned row by
row and `TauCeti.centralCharacterTable_mul_characterDegree` converts between them entry by entry.

That conversion is stated without division, so it holds over every algebraically closed field in
which `|G|` is invertible. Dividing it out in either direction needs the corresponding factor to be
invertible: `TauCeti.characterTable_eq_div` divides by the class size `|C|`, which the standing
hypotheses already make invertible, while
`TauCeti.centralCharacterTable_eq_div` divides by the degree `χ(1)` and so takes its nonvanishing
as an explicit hypothesis rather than assuming characteristic zero.

`TauCeti.centralCharacter_blockRepresentation` carries the irreducibility of the block as an
instance argument rather than deriving it: the central character is only defined for an irreducible
representation, and irreducibility of a block is the theorem
`TauCeti.isIrreducible_blockRepresentation`, which mentions the chosen presentation `e` and so
cannot be an instance. Callers supply it with `have := isIrreducible_blockRepresentation e i`.

## References

This is the step that Layer 5 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
calls for after `normalized_eigenrow_iff_algHom`: the identification of the algebra homomorphisms
out of the centre with the central characters, and the central table `Ω` itself. See I. M. Isaacs,
*Character Theory of Finite Groups* (1976), Chapter 3, or J. D. Dixon, *High speed computation of
group characters*, Numer. Math. 10 (1967).
-/

public section

namespace TauCeti

open scoped Matrix MonoidAlgebra

universe u v w

section Block

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G] {ι : Type w} {d : ι → ℕ}
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

/-- **The central character of a Wedderburn block is the corresponding coordinate of the splitting
of the centre.** A central element of `k[G]` acts on the `i`-th matrix factor as the scalar matrix
that `TauCeti.centerMonoidAlgebraAlgEquivPi` records there, hence on the representation the block
carries as that scalar. -/
theorem centralCharacter_blockRepresentation [∀ i, NeZero (d i)] (i : ι)
    [(blockRepresentation e i).IsIrreducible] (z : Subalgebra.center k k[G]) :
    Representation.centralCharacter (blockRepresentation e i) z =
      centerMonoidAlgebraAlgEquivPi e z i := by
  have hne : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  obtain ⟨j⟩ := hne
  classical
  have hv : (Pi.single j 1 : Fin (d i) → k) ≠ 0 := by
    intro h
    simpa using congrFun h j
  refine Representation.centralCharacter_eq_of_ne_zero_of_asAlgebraHom_apply_eq _ hv ?_
  rw [asAlgebraHom_blockRepresentation, blockAlgHom_apply,
    ← algebraMap_centerMonoidAlgebraAlgEquivPi_apply e z i, Matrix.toLinAlgEquiv'.commutes,
    Module.algebraMap_end_apply]

end Block

section Classification

variable (k : Type u) (G : Type v) [Field k] [IsAlgClosed k] [Group G] [Finite G]
  [Invertible (Nat.card G : k)]

/-- **Every irreducible representation has the central character of an enumerated one**: it is
equivalent to one of them, and equivalent representations have the same central character. -/
theorem exists_centralCharacter_irreducibleRepresentation_eq {W : Type w} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (σ : _root_.Representation k G W) [σ.IsIrreducible] :
    ∃ i, Representation.centralCharacter (irreducibleRepresentation k i) =
      Representation.centralCharacter σ := by
  obtain ⟨i, ⟨φ⟩⟩ := ClassFunction.exists_nonempty_equiv (irreducibleRepresentation k)
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) σ
  exact ⟨i, Representation.centralCharacter_eq_of_equiv σ _ φ⟩

/-- **Every algebra homomorphism out of the centre of `k[G]` is a central character.** A Wedderburn
presentation splits the centre as a product of copies of `k`, on which the only algebra
homomorphisms to `k` are the coordinate evaluations; the evaluation at a block is the central
character of the representation that block carries. -/
theorem exists_centralCharacter_eq (φ : Subalgebra.center k k[G] →ₐ[k] k) :
    ∃ i, Representation.centralCharacter (irreducibleRepresentation k i) = φ := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix k G
  have := hd
  obtain ⟨a, ha⟩ :=
    (φ.comp (centerMonoidAlgebraAlgEquivPi e).symm.toAlgHom).eq_piEvalAlgHom
  have := isIrreducible_blockRepresentation e a
  obtain ⟨i, hi⟩ :=
    exists_centralCharacter_irreducibleRepresentation_eq k G (blockRepresentation e a)
  refine ⟨i, hi.trans (AlgHom.ext fun z => ?_)⟩
  rw [centralCharacter_blockRepresentation]
  simpa using (congrArg (fun ψ => ψ (centerMonoidAlgebraAlgEquivPi e z)) ha).symm

/-- **Distinct enumerated irreducibles have distinct central characters.** Each is equivalent to a
Wedderburn block, and its central character is the evaluation at that block; equal central
characters therefore force the same block, hence equivalent representations. -/
theorem centralCharacter_irreducibleRepresentation_injective :
    Function.Injective fun i : Fin (Nat.card (ConjClasses G)) =>
      Representation.centralCharacter (irreducibleRepresentation k i) := by
  classical
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix k G
  have := hd
  have : ∀ a, (blockRepresentation e a).IsIrreducible := fun a =>
    isIrreducible_blockRepresentation e a
  have hcard : Nat.card (Fin n) = Nat.card (ConjClasses G) := by
    simpa using card_eq_card_conjClasses_of_algEquiv_pi_matrix e
  choose c hc using fun i : Fin (Nat.card (ConjClasses G)) =>
    ClassFunction.exists_nonempty_equiv (blockRepresentation e)
      (fun _ _ h => isEmpty_equiv_blockRepresentation e h) hcard (irreducibleRepresentation k i)
  intro i j hij
  by_contra hne
  have hE : ∀ z, centerMonoidAlgebraAlgEquivPi e z (c i) =
      centerMonoidAlgebraAlgEquivPi e z (c j) := fun z => by
    rw [← centralCharacter_blockRepresentation, ← centralCharacter_blockRepresentation,
      Representation.centralCharacter_eq_of_equiv _ _ (hc i).some,
      Representation.centralCharacter_eq_of_equiv _ _ (hc j).some]
    exact DFunLike.congr_fun hij z
  have hcc : c i = c j := by
    have h := hE ((centerMonoidAlgebraAlgEquivPi e).symm (Pi.single (c i) 1))
    rw [AlgEquiv.apply_symm_apply] at h
    by_contra hcij
    simp [Pi.single_eq_of_ne (Ne.symm hcij)] at h
  have hEq : (irreducibleRepresentation k i).Equiv (irreducibleRepresentation k j) := by
    have h1 := (hc i).some
    rw [hcc] at h1
    exact h1.trans (hc j).some.symm
  exact (pairwise_isEmpty_equiv_irreducibleRepresentation k hne).elim hEq

/-- **The irreducible representations of `G` are in bijection with the algebra homomorphisms out of
the centre of `k[G]`**, by taking central characters. -/
noncomputable def finEquivCentralCharacter :
    Fin (Nat.card (ConjClasses G)) ≃ (Subalgebra.center k k[G] →ₐ[k] k) :=
  Equiv.ofBijective _
    ⟨centralCharacter_irreducibleRepresentation_injective k G, exists_centralCharacter_eq k G⟩

@[simp]
theorem finEquivCentralCharacter_apply (i : Fin (Nat.card (ConjClasses G))) :
    finEquivCentralCharacter k G i =
      Representation.centralCharacter (irreducibleRepresentation k i) :=
  (rfl)

/-- **The central characters separate the points of the centre of `k[G]`**: a central element is
determined by the scalars by which it acts on the irreducible representations. -/
theorem eq_of_centralCharacter_eq {z w : Subalgebra.center k k[G]}
    (h : ∀ i, Representation.centralCharacter (irreducibleRepresentation k i) z =
      Representation.centralCharacter (irreducibleRepresentation k i) w) : z = w := by
  have : NeZero (Nat.card G : k) := ⟨Invertible.ne_zero _⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix k G
  have := hd
  refine (centerMonoidAlgebraAlgEquivPi e).injective (funext fun a => ?_)
  have := isIrreducible_blockRepresentation e a
  obtain ⟨i, hi⟩ :=
    exists_centralCharacter_irreducibleRepresentation_eq k G (blockRepresentation e a)
  rw [← centralCharacter_blockRepresentation e a z, ← centralCharacter_blockRepresentation e a w,
    ← hi]
  exact h i

end Classification

section CentralTable

variable (k : Type u) (G : Type v) [Field k] [IsAlgClosed k] [Group G] [Fintype G] [DecidableEq G]
  [Invertible (Nat.card G : k)]

/-- **The central character table `Ω` of `G`**: the square matrix whose `(i, C)` entry is the value
of the central character of the `i`-th irreducible representation on the class sum of `C`.

Its rows are indexed by the same enumeration of the irreducible characters as the rows of
`TauCeti.characterTable`, and the two tables determine one another by
`TauCeti.centralCharacterTable_mul_characterDegree`. -/
noncomputable def centralCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) k := fun i =>
  classSumRow (Representation.centralCharacter (irreducibleRepresentation k i))

variable {k G}

/-- The entries of the central character table are the values `ωᵪ(K_C)`. -/
@[simp]
theorem centralCharacterTable_apply (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    centralCharacterTable k G i C =
      Representation.centralCharacter (irreducibleRepresentation k i) (classSumCenter C) :=
  classSumRow_apply _ C

/-- Every row of the central character table is normalized: the class sum of the class of `1` is
the unit of the centre. -/
theorem centralCharacterTable_mk_one (i : Fin (Nat.card (ConjClasses G))) :
    centralCharacterTable k G i (ConjClasses.mk (1 : G)) = 1 :=
  classSumRow_mk_one _

/-- **Every row of the central character table is a common left eigenrow of the
class-multiplication matrices**: a central character is an algebra homomorphism out of the centre,
and the coordinate identity for the class sums is exactly the eigenrow condition. -/
theorem isClassEigenrow_centralCharacterTable (i : Fin (Nat.card (ConjClasses G))) :
    IsClassEigenrow (centralCharacterTable k G i) :=
  isClassEigenrow_classSumRow _

/-- Distinct rows of the central character table are distinct. -/
theorem centralCharacterTable_injective :
    Function.Injective (centralCharacterTable k G) := fun _ _ h =>
  centralCharacter_irreducibleRepresentation_injective k G (classSumRow_injective h)

/-- **The normalized common left eigenrows of the class-multiplication matrices are exactly the
rows of the central character table.**

This is the step that turns the linear algebra of the class algebra into representation theory: the
eigenrow condition alone characterises the algebra homomorphisms out of the centre
(`TauCeti.isClassEigenrow_iff_exists_algHom`), and those are the central characters of the
irreducible representations (`TauCeti.exists_centralCharacter_eq`). -/
theorem isClassEigenrow_iff_exists_centralCharacterTable_eq {v : ConjClasses G → k}
    (hv₁ : v (ConjClasses.mk (1 : G)) = 1) :
    IsClassEigenrow v ↔ ∃ i, centralCharacterTable k G i = v := by
  refine ⟨fun hv => ?_, ?_⟩
  · obtain ⟨φ, hφ⟩ := (isClassEigenrow_iff_exists_algHom hv₁).mp hv
    obtain ⟨i, hi⟩ := exists_centralCharacter_eq k G φ
    exact ⟨i, by rw [centralCharacterTable, hi, hφ]⟩
  · rintro ⟨i, rfl⟩
    exact isClassEigenrow_centralCharacterTable i

/-- **Every nonzero common left eigenvector of the class-multiplication matrices is a multiple of a
row of the central character table**, so the rows of `Ω` are those eigenvectors up to scale.
Normalization need not be assumed: the value of such a vector at the class of `1` is automatically
nonzero, and is exactly the scale factor. -/
theorem exists_eq_smul_centralCharacterTable {w : ConjClasses G → k} (hw₀ : w ≠ 0)
    (hw : ∀ Cᵢ : ConjClasses G, ∃ c : k,
      w ᵥ* (classMultMatrix Cᵢ).map (Int.cast : ℤ → k) = c • w) :
    ∃ i, w = w (ConjClasses.mk (1 : G)) • centralCharacterTable k G i := by
  have hw₁ : w (ConjClasses.mk (1 : G)) ≠ 0 := by
    intro h₀
    refine hw₀ (funext fun Cᵢ => ?_)
    obtain ⟨c, hc⟩ := hw Cᵢ
    have h := congrFun hc (ConjClasses.mk (1 : G))
    rw [vecMul_classMultMatrix_apply] at h
    simpa [structureConstant_mk_one_right, h₀] using h
  have hv₁ : ((w (ConjClasses.mk (1 : G)))⁻¹ • w) (ConjClasses.mk (1 : G)) = 1 :=
    inv_mul_cancel₀ hw₁
  have hv : IsClassEigenrow ((w (ConjClasses.mk (1 : G)))⁻¹ • w) :=
    isClassEigenrow_of_forall_exists_smul hv₁ fun Cᵢ => by
      obtain ⟨c, hc⟩ := hw Cᵢ
      exact ⟨c, by rw [Matrix.smul_vecMul, hc, smul_comm]⟩
  obtain ⟨i, hi⟩ := (isClassEigenrow_iff_exists_centralCharacterTable_eq hv₁).mp hv
  exact ⟨i, by rw [hi, smul_inv_smul₀ hw₁]⟩

variable (k G)

/-- **The irreducible representations of `G` are in bijection with the normalized common left
eigenrows of the class-multiplication matrices**, an irreducible going to the corresponding row of
the central character table. -/
noncomputable def finEquivEigenrow :
    Fin (Nat.card (ConjClasses G)) ≃
      {v : ConjClasses G → k // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v} :=
  (finEquivCentralCharacter k G).trans algHomEquivEigenrow

@[simp]
theorem coe_finEquivEigenrow (i : Fin (Nat.card (ConjClasses G))) :
    (finEquivEigenrow k G i : ConjClasses G → k) = centralCharacterTable k G i := by
  rw [finEquivEigenrow, Equiv.trans_apply, algHomEquivEigenrow_apply_coe,
    finEquivCentralCharacter_apply, centralCharacterTable]

/-- **A finite group has as many normalized common left eigenrows as conjugacy classes.** The
normalization `v (ConjClasses.mk 1) = 1` cannot be dropped: the zero row is a common left eigenrow
too (`TauCeti.isClassEigenrow_zero`). See
`TauCeti.card_normalized_isClassEigenrow_of_nonempty_center_algEquiv` for the version that requires
only an explicit splitting of the centre. -/
theorem card_normalized_isClassEigenrow :
    Nat.card {v : ConjClasses G → k // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v} =
      Nat.card (ConjClasses G) := by
  rw [← Nat.card_congr (finEquivEigenrow k G)]
  simp

/-- **The rows of the central character table are linearly independent.** Distinct algebra
homomorphisms into a field are linearly independent, by Dedekind's theorem
(`linearIndependent_algHom_toLinearMap`), and distinct irreducibles have distinct central characters
(`TauCeti.centralCharacter_irreducibleRepresentation_injective`); a row is the tuple of values of
such a homomorphism on the class-sum basis, so the rows inherit that independence. -/
theorem linearIndependent_centralCharacterTable :
    LinearIndependent k (centralCharacterTable k G) := by
  have hli : LinearIndependent k fun i : Fin (Nat.card (ConjClasses G)) =>
      (Representation.centralCharacter (irreducibleRepresentation k i)).toLinearMap :=
    (linearIndependent_algHom_toLinearMap k (Subalgebra.center k k[G]) k).comp _
      (centralCharacter_irreducibleRepresentation_injective k G)
  have hrow : ∀ i, Module.Basis.constr (classSumBasis (k := k) (G := G)) k
        (centralCharacterTable k G i) =
      (Representation.centralCharacter (irreducibleRepresentation k i)).toLinearMap := fun i =>
    Module.Basis.ext classSumBasis fun C => by
      rw [Module.Basis.constr_basis, AlgHom.toLinearMap_apply, classSumBasis_apply,
        centralCharacterTable_apply]
  have hli' : LinearIndependent k fun i : Fin (Nat.card (ConjClasses G)) =>
      Module.Basis.constr (classSumBasis (k := k) (G := G)) k (centralCharacterTable k G i) := by
    simpa only [hrow] using hli
  exact LinearIndependent.of_comp
    (Module.Basis.constr (classSumBasis (k := k) (G := G)) k).toLinearMap hli'

/-- **The rows of the central character table are a basis** of the functions on the conjugacy
classes: they are linearly independent, and there are as many of them as conjugacy classes, which is
the dimension of that space. Together with
`TauCeti.exists_eq_smul_centralCharacterTable` this is the full description of the common left
eigenvectors of the class-multiplication matrices. -/
noncomputable def basisCentralCharacterTable :
    Module.Basis (Fin (Nat.card (ConjClasses G))) k (ConjClasses G → k) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_centralCharacterTable k G)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.card_eq_fintype_card])

@[simp]
theorem coe_basisCentralCharacterTable :
    ⇑(basisCentralCharacterTable k G) = centralCharacterTable k G :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

variable {k G}

/-- **The conversion between the central table and the character table**:
`ωᵪ(K_C) · χ(1) = |C| · χ(g_C)`, in the division-free form that needs no invertibility of the
degree. Dividing by the class size `|C|`, which is always invertible here, reads the character table
off the central one (`TauCeti.characterTable_eq_div`); dividing by the degree `χ(1)`, which is
invertible in characteristic zero, reads the central table off the character table
(`TauCeti.centralCharacterTable_eq_div`). -/
theorem centralCharacterTable_mul_characterDegree (i : Fin (Nat.card (ConjClasses G)))
    (C : ConjClasses G) :
    centralCharacterTable k G i C * (characterDegree k i : k) =
      Nat.card C.carrier * characterTable k G i C := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  have h := Representation.centralCharacter_classSumCenter_mul_character_one
    (irreducibleRepresentation k i) (rfl : ConjClasses.mk g = ConjClasses.mk g)
  rw [character_irreducibleRepresentation, irreducibleCharacter_one] at h
  simpa using h

/-- The central character table read off the character table, wherever the degree `χ(1)` is nonzero
in `k`; that holds in particular in characteristic zero, where the degree is a positive natural
number, by `TauCeti.characterDegree_pos`. -/
theorem centralCharacterTable_eq_div (i : Fin (Nat.card (ConjClasses G)))
    (hdeg : (characterDegree k i : k) ≠ 0) (C : ConjClasses G) :
    centralCharacterTable k G i C =
      Nat.card C.carrier * characterTable k G i C / (characterDegree k i : k) := by
  rw [eq_div_iff hdeg, centralCharacterTable_mul_characterDegree]

/-- The character table read off the central character table. No hypothesis beyond the standing
ones is needed, because the class size `|C|` is already invertible in `k`: the second
column-orthogonality relation `TauCeti.card_conjClass_mul_sum_characterTable_mul_characterTable_inv`
exhibits the invertible `|G|` as a multiple of it. -/
theorem characterTable_eq_div (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    characterTable k G i C =
      (characterDegree k i : k) * centralCharacterTable k G i C / Nat.card C.carrier := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  have hC : (Nat.card (ConjClasses.mk g).carrier : k) ≠ 0 := fun h0 =>
    Invertible.ne_zero (Nat.card G : k) <| by
      have h := card_conjClass_mul_sum_characterTable_mul_characterTable_inv (k := k) g g
      rw [ite_eq_left (IsConj.refl g), h0, zero_mul] at h
      exact h.symm
  rw [eq_div_iff hC, mul_comm (characterTable k G i (ConjClasses.mk g)),
    ← centralCharacterTable_mul_characterDegree i (ConjClasses.mk g)]
  exact mul_comm _ _

end CentralTable

end TauCeti
