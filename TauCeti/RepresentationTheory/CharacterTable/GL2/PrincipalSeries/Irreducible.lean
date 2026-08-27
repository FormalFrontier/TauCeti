/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The fundamental theorem of algebra, which supplies `IsAlgClosed ℂ`: the Mackey criterion and
-- Schur's lemma below are both stated over an algebraically closed field.
public import Mathlib.Analysis.Complex.Polynomial.Basic
-- `TauCeti.GL2WeylElement` and the Bruhat decomposition of `GL₂` are what reduce the Mackey
-- condition to a single group element.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
-- `TauCeti.GL2PrincipalSeries` and the Borel character it is induced from are the subject.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Basic
-- The Mackey irreducibility criterion `TauCeti.simple_indFDRep_iff`, its predicate
-- `TauCeti.MackeyDisjoint`, and the Mackey subgroup the predicate is stated on.
public import TauCeti.RepresentationTheory.Induction.Mackey.Irreducible
-- Non-public: irreducibility of a line and its passage to `CategoryTheory.Simple` are used only
-- inside the proof that the two sides of the Mackey condition are simple.
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The principal series of `GL₂(𝔽_q)` is irreducible exactly off the diagonal

The principal series `Ind_B^{GL₂}(α ⊗ β)` of `GL₂(𝔽_q)` is irreducible if and only if the two
characters `α, β : 𝔽_qˣ → ℂˣ` are distinct. This file proves that, the last of the three
statements the character-theory roadmap asks of the principal series; the other two, its
definition and its dimension `q + 1`, are in
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries/Basic.lean`.

The proof is the Mackey irreducibility criterion `TauCeti.simple_indFDRep_iff` run against the
Bruhat decomposition. The criterion says that `Ind_B^{GL₂} A` is irreducible exactly when `A` is
irreducible and, for every `s ∉ B`, the restrictions of `A` and of its conjugate `{}^s A` to
`B ⊓ sBs⁻¹` share no nonzero intertwiner. The Borel representation `α ⊗ β` is a line, hence
irreducible, and Bruhat collapses the second condition: every `s ∉ B` is `b₁ w b₂` for the Weyl
element `w = !![0, 1; 1, 0]`, and Mackey disjointness depends only on the double coset
(`TauCeti.mackeyDisjoint_mul_left_mul_right_iff`), so the whole criterion becomes one condition
at `w`.

At `w` the two restrictions are again lines, so Schur's lemma
(`FDRep.finrank_hom_simple_simple`) turns disjointness into non-isomorphism, and characters
separate them: on the diagonal matrix `diag(a, 1)`, which lies in `B ⊓ wBw⁻¹`, one takes the value
`α a` and the other the value `β a`, because conjugating by `w` swaps the two diagonal entries.
Conversely, for `α = β` the Borel character is `α ∘ det` (`TauCeti.GL2Borel.linearChar_self`),
which conjugation cannot move, so the two restrictions carry the same action and the criterion
fails.

## Main definitions

* `TauCeti.GL2Borel.mackeyTorusElt`: a diagonal matrix, read as an element of the Mackey subgroup
  at the Weyl element; this is where the two sides of the Mackey condition are compared.

## Main statements

* `TauCeti.GL2Borel.inv_weyl_mul_torusHom_mul_weyl`: conjugating a diagonal matrix by the Weyl
  element swaps its two entries.
* `TauCeti.GL2Borel.mackeyDisjoint_weyl_iff`: the single Mackey condition, at the Weyl element,
  holds exactly when `α ≠ β`.
* `TauCeti.simple_GL2PrincipalSeries_iff`: **the principal series `Ind_B^{GL₂}(α ⊗ β)` is
  irreducible if and only if `α ≠ β`.**

## Implementation notes

The universe of `F` is pinned to `Type` in the representation-theoretic statements, unlike in
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries/Basic.lean`, where the principal
series is defined for `F : Type u`. The Mackey criterion `TauCeti.simple_indFDRep_iff` asks for
the coefficient field and the group to lie in the *same* universe, and the coefficient field here
is `ℂ : Type`; pinning `F : Type` is what puts `GL (Fin 2) F` there too. The criterion therefore
covers finite fields presented by a `Type`-valued representative — every finite field has one, up
to a ring isomorphism, namely `GaloisField p n` — but it does not apply *directly* to a finite
field declared in some `Type u` with `u ≠ 0`; such a presentation first has to be transported
along a ring isomorphism with a small model, or wait for the upstream generalization described
next. The purely group-theoretic lemmas about the Weyl conjugation keep both an arbitrary universe
and an arbitrary commutative ring.

That pin is not a choice this file could make differently. The predicate
`TauCeti.MackeyDisjoint` is itself declared for a field and a group in one universe, so the very
statement of the Mackey condition at `ℂ` and `GL (Fin 2) F` needs `F : Type`; and the criterion
that consumes it ends at Mathlib's `FDRep.simple_iff_end_is_rank_one`, which is stated for
`{k : Type u} {G : Type u}`. Relaxing the pin therefore means an upstream generalization of that
Mathlib lemma, not a change here. `TauCeti/RepresentationTheory/CharacterTable/GL2/Steinberg.lean`
records the same obstruction for the companion criterion `FDRep.simple_iff_char_is_norm_one`.

Mackey disjointness is unfolded through `TauCeti.mackeyDisjoint_iff_finrank_eq_zero` and Schur's
lemma rather than by exhibiting intertwiners by hand: both sides of the Mackey condition at `w`
are one-dimensional, so `FDRep.finrank_hom_simple_simple` reduces the condition to the existence
of an isomorphism, and for one-dimensional representations an isomorphism is exactly an equality
of the characters they carry.

The membership `diag(a, 1) ∈ B ⊓ wBw⁻¹` is all that is used of the Mackey subgroup; the file
deliberately does not compute `B ⊓ wBw⁻¹` to be the split torus, because the reducible direction
needs no such description — `α ∘ det` is conjugation-invariant on all of `GL₂`, not only on the
torus.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The Borel and the principal series": the target `simple_GL2PrincipalSeries_iff`, whose
  name is the roadmap's.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42, §7.3, Proposition 23.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Lecture 5.2.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

/-- **The character of a restriction along a group homomorphism is the character pulled back.**
This is `TauCeti.character_resFDRep` for an arbitrary homomorphism in place of the inclusion of a
subgroup; it stays private because the only restrictions it is read on here are the two sides of
the Mackey condition. -/
private theorem character_actionRes_obj {k : Type u} {S T : Type v} [Field k] [Group S] [Group T]
    (f : S →* T) (A : FDRep k T) (x : S) :
    FDRep.character ((Action.res (FGModuleCat k) f).obj A) x = A.character (f x) :=
  (rfl)

/-- **A representation on a line is a simple object of `FDRep k G`.** Private packaging of
`TauCeti.Representation.isIrreducible_of_finrank_eq_one` and
`TauCeti.FDRep.simple_of_isIrreducible`, used only to feed Schur's lemma below. -/
private theorem simple_of_finrank_eq_one {k : Type u} {S : Type v} [Field k] [Group S]
    (X : FDRep k S) (h : Module.finrank k X = 1) : Simple X :=
  have : Representation.IsIrreducible X.ρ :=
    Representation.isIrreducible_of_finrank_eq_one _ h
  FDRep.simple_of_isIrreducible X

namespace GL2Borel

/-! ### The Weyl conjugation on the split torus -/

section CommRing

variable {R : Type*} [CommRing R]

/-- **Conjugating a diagonal matrix by the Weyl element swaps its two entries.** This is the whole
geometric content of the Mackey condition for the principal series: the `w`-conjugate of the
character `α ⊗ β` is `β ⊗ α`. -/
theorem inv_weyl_mul_torusHom_mul_weyl (p : Rˣ × Rˣ) :
    (GL2WeylElement R)⁻¹ * ((torusHom p : GL2Borel R) : GL (Fin 2) R) * GL2WeylElement R
      = ((torusHom (p.2, p.1) : GL2Borel R) : GL (Fin 2) R) := by
  rw [gl2WeylElement_inv, coe_torusHom, coe_torusHom]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The diagonal matrices lie in the Mackey subgroup at the Weyl element.** They are upper
triangular, and so are their `w`-conjugates, which are again diagonal. -/
theorem torusHom_mem_mackeySubgroup_weyl (p : Rˣ × Rˣ) :
    ((torusHom p : GL2Borel R) : GL (Fin 2) R)
      ∈ mackeySubgroup (GL2WeylElement R) (GL2Borel R) (GL2Borel R) := by
  refine mem_mackeySubgroup_iff.mpr ⟨(torusHom p).2, ?_⟩
  rw [inv_weyl_mul_torusHom_mul_weyl]
  exact (torusHom (p.2, p.1)).2

/-- The diagonal matrix `diag(a, d)`, read as an element of the Mackey subgroup at the Weyl
element viewed inside the Borel subgroup. This is the one element the character computation is
performed at. -/
def mackeyTorusElt (p : Rˣ × Rˣ) :
    ((mackeySubgroup (GL2WeylElement R) (GL2Borel R) (GL2Borel R)).subgroupOf (GL2Borel R)) :=
  ⟨torusHom p, Subgroup.mem_subgroupOf.mpr (torusHom_mem_mackeySubgroup_weyl p)⟩

@[simp]
theorem coe_mackeyTorusElt (p : Rˣ × Rˣ) : (mackeyTorusElt p : GL2Borel R) = torusHom p :=
  (rfl)

/-- **The Mackey conjugation swaps the two torus coordinates.** Together with
`TauCeti.GL2Borel.linearChar_torusHom` this is what makes the two sides of the Mackey condition
take the values `α a` and `β a` at `diag(a, 1)`. -/
@[simp]
theorem mackeyToH_mackeyTorusElt (p : Rˣ × Rˣ) :
    mackeyToH (GL2WeylElement R) (GL2Borel R) (GL2Borel R) (mackeyTorusElt p)
      = torusHom (p.2, p.1) :=
  Subtype.ext <| by
    rw [coe_mackeyToH_apply, coe_mackeyTorusElt, inv_weyl_mul_torusHom_mul_weyl]

/-- **The determinant does not see the Mackey conjugation.** Conjugation is inner and the
determinant is a homomorphism into a commutative group, so it is unchanged; this is why the
boundary character `α ∘ det` gives a reducible principal series. -/
theorem det_mackeyToH (g : (mackeySubgroup (GL2WeylElement R) (GL2Borel R)
    (GL2Borel R)).subgroupOf (GL2Borel R)) :
    Matrix.GeneralLinearGroup.det
        ((mackeyToH (GL2WeylElement R) (GL2Borel R) (GL2Borel R) g : GL2Borel R) :
          GL (Fin 2) R)
      = Matrix.GeneralLinearGroup.det ((g : GL2Borel R) : GL (Fin 2) R) := by
  rw [coe_mackeyToH_apply, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

end CommRing

/-! ### The Mackey condition at the Weyl element -/

section Field

variable {F : Type} [Field F]

/-- **The two sides of the Mackey condition at the Weyl element are isomorphic exactly when the
two characters agree.** Both are lines, so an isomorphism is an equality of characters; the
diagonal matrices `diag(a, 1)` of the Mackey subgroup separate `α` from `β`, while for `α = β` the
common value `α ∘ det` is conjugation-invariant. -/
theorem nonempty_iso_mackey_weyl_iff (α β : Fˣ →* ℂˣ) :
    Nonempty (resFDRep ((mackeySubgroup (GL2WeylElement F) (GL2Borel F)
          (GL2Borel F)).subgroupOf (GL2Borel F)) (GL2BorelRep F α β) ≅
        (Action.res (FGModuleCat ℂ)
          (mackeyToH (GL2WeylElement F) (GL2Borel F) (GL2Borel F))).obj (GL2BorelRep F α β))
      ↔ α = β := by
  constructor
  · rintro ⟨e⟩
    -- Reading the equality of characters at `diag(a, 1)` gives `α a = β a`.
    have hchar := FDRep.char_iso e
    refine MonoidHom.ext fun a => Units.ext ?_
    have h := congrArg (fun χ => χ (mackeyTorusElt (a, 1))) hchar
    simpa [character_actionRes_obj] using h
  · rintro rfl
    -- The two actions are the same monoid homomorphism, because `α ∘ det` is
    -- conjugation-invariant.
    refine ⟨Action.mkIso (Iso.refl _) fun g => ?_⟩
    have hρ : Action.ρ (GL2BorelRep F α α) (g : GL2Borel F) =
        Action.ρ (GL2BorelRep F α α)
          (mackeyToH (GL2WeylElement F) (GL2Borel F) (GL2Borel F) g) := by
      rw [GL2BorelRep_def]
      refine FGModuleCat.hom_ext ?_
      rw [FDRep.hom_hom_action_ρ, FDRep.hom_hom_action_ρ, FDRep.of_ρ']
      refine LinearMap.ext fun v => ?_
      rw [linearRep_apply, linearRep_apply, linearChar_self, linearChar_self, det_mackeyToH]
    simp only [Iso.refl_hom]
    exact hρ

/-- **The Mackey condition of the principal series, at the Weyl element.** The restrictions of
`α ⊗ β` and of its `w`-conjugate to `B ⊓ wBw⁻¹` are disjoint exactly when `α ≠ β`. Together with
the Bruhat decomposition this is the whole content of
`TauCeti.simple_GL2PrincipalSeries_iff`. -/
@[simp]
theorem mackeyDisjoint_weyl_iff (α β : Fˣ →* ℂˣ) :
    MackeyDisjoint (GL2BorelRep F α β) (GL2WeylElement F) ↔ α ≠ β := by
  classical
  have hres : Simple (resFDRep ((mackeySubgroup (GL2WeylElement F) (GL2Borel F)
      (GL2Borel F)).subgroupOf (GL2Borel F)) (GL2BorelRep F α β)) :=
    simple_of_finrank_eq_one _ (finrank_GL2BorelRep F α β)
  have hconj : Simple ((Action.res (FGModuleCat ℂ)
      (mackeyToH (GL2WeylElement F) (GL2Borel F) (GL2Borel F))).obj (GL2BorelRep F α β)) :=
    simple_of_finrank_eq_one _ (finrank_GL2BorelRep F α β)
  simp only [mackeyDisjoint_iff_finrank_eq_zero, FDRep.finrank_hom_simple_simple]
  split_ifs with h
  · simp [(nonempty_iso_mackey_weyl_iff α β).mp h]
  · exact iff_of_true rfl fun hαβ => h ((nonempty_iso_mackey_weyl_iff α β).mpr hαβ)

end Field

end GL2Borel

/-! ### The irreducibility criterion -/

section FiniteField

variable (F : Type) [Field F] [Fintype F]

/-- **The principal series is irreducible exactly off the diagonal.** For a finite field `F` and
characters `α, β : Fˣ → ℂˣ`, the parabolically induced representation `Ind_B^{GL₂}(α ⊗ β)` of
`GL₂(F)` is irreducible if and only if `α ≠ β`.

Together with `TauCeti.finrank_GL2PrincipalSeries` this produces the `(q + 1)`-dimensional family
of the character table of `GL₂(𝔽_q)`; at `α = β` the induced representation is the reducible one
whose two constituents are the linear character `α ∘ det` and a twist of the Steinberg
representation. -/
@[simp]
theorem simple_GL2PrincipalSeries_iff (α β : Fˣ →* ℂˣ) :
    Simple (GL2PrincipalSeries F α β) ↔ α ≠ β := by
  rw [GL2PrincipalSeries_def, simple_indFDRep_iff (GL2BorelRep F α β)]
  constructor
  · rintro ⟨-, hdisj⟩
    exact (GL2Borel.mackeyDisjoint_weyl_iff α β).mp (hdisj _ gl2WeylElement_notMem_gl2Borel)
  · intro hne
    refine ⟨simple_of_finrank_eq_one _ (finrank_GL2BorelRep F α β), fun s hs => ?_⟩
    -- Bruhat: outside `B` every element is `b₁ w b₂`, and Mackey disjointness depends only on the
    -- double coset.
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ :=
      DoubleCoset.mem_doubleCoset.mp (GL2Borel.mem_doubleCoset_weyl_of_notMem hs)
    exact (mackeyDisjoint_mul_left_mul_right_iff _ hb₁ hb₂ _).mpr
      ((GL2Borel.mackeyDisjoint_weyl_iff α β).mpr hne)

end FiniteField

end TauCeti
