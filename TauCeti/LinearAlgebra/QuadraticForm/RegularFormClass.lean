/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Isometry classes of regular quadratic forms

Over a field in which `2` is invertible, every nondegenerate quadratic form on a
finite-dimensional space is isometric to a weighted sum of squares whose weights are units. This
file turns that diagonalization into a carrier for the isometry classes themselves: a *diagonal
presentation* is a rank `n` together with a tuple `w : Fin n → Kˣ`, presenting the form
`⟨w 0, …, w (n - 1)⟩`, and `TauCeti.RegularFormClass K` is the quotient of the presentations by
isometry of the forms they present.

Presenting classes by tuples of units, rather than by quotienting quadratic forms on arbitrary
finite-dimensional spaces, keeps the carrier in a single universe and makes the type a plain
`Quotient` of a sigma type. Mathlib's `QuadraticMap.Equivalent` already compares forms living on
different spaces, so nothing is lost: two regular forms are isometric exactly when their classes
agree, and only presentations of equal rank are ever related.

Concatenating weight tuples presents the orthogonal sum of the presented forms, which makes the
classes an additive commutative monoid whose zero is the class of the empty presentation and whose
rank is additive.

## Main definitions

* `TauCeti.RegularFormPresentation`: a rank together with a tuple of unit weights.
* `TauCeti.presentedForm`: the weighted sum of squares a presentation stands for.
* `TauCeti.RegularFormClass`: isometry classes of regular finite-dimensional quadratic forms.
* `TauCeti.RegularFormClass.rank`: the common rank of the presentations in a class.
* `TauCeti.RegularFormPresentation.append`: concatenation of presentations.
* `TauCeti.formClass`: the class of a regular form on a finite-dimensional space.

## Main results

* `TauCeti.nondegenerate_presentedForm`: a presented form is nondegenerate.
* `TauCeti.exists_presentedForm_equivalent`: every regular form has a diagonal presentation.
* `TauCeti.formClass_mk`: the class of a form is computed by any of its diagonalizations.
* `TauCeti.formClass_eq_iff`: two regular forms are isometric exactly when their classes agree.
* `TauCeti.presentedFormAppendIsometryEquiv`: concatenating weights presents the orthogonal sum.
* `TauCeti.formClass_prod`: the class of an orthogonal product is the sum of the classes.

## References

See T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I §2 and §5.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v w

variable {K : Type u} [Field K]

/-! ### Diagonal presentations -/

/-- A diagonal presentation: a rank `n` together with a tuple of units, read as the diagonal
form `⟨w 0, …, w (n - 1)⟩`. This presentation, the setoid `TauCeti.regularFormSetoid` and the
quotient `TauCeti.RegularFormClass` are the carrier design fixed by the human-authored
`TauCetiRoadmap/QuadraticFormInvariants` roadmap, whose `README.md` and `Suggested.lean` spell out
the three signatures used here. The presented form is regular under this file's standing hypothesis
that `2` is invertible in `K` (`TauCeti.nondegenerate_presentedForm`); the definition itself asks
only for a field, and in characteristic two the polar form of a weighted sum of squares vanishes,
so the presented form need not be nondegenerate. -/
abbrev RegularFormPresentation (K : Type u) [Field K] : Type u := Σ n : ℕ, Fin n → Kˣ

/-- The form presented by `(n, w)`, namely the weighted sum of squares with weights `w`. -/
def presentedForm (p : RegularFormPresentation K) : QuadraticForm K (Fin p.1 → K) :=
  weightedSumSquares K fun i => ((p.2 i : K))

/-- The presented form evaluates as the weighted sum of the squares of the coordinates. -/
@[simp]
theorem presentedForm_apply (p : RegularFormPresentation K) (x : Fin p.1 → K) :
    presentedForm p x = ∑ i, (p.2 i : K) * (x i * x i) := by
  simp [presentedForm, weightedSumSquares_apply]

/-- The presented form is Mathlib's weighted sum of squares taken with the `Kˣ`-action, which is
the shape produced by `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`. -/
theorem presentedForm_eq_weightedSumSquares (p : RegularFormPresentation K) :
    presentedForm p = weightedSumSquares K p.2 := by
  ext x
  simp [presentedForm, weightedSumSquares_apply, Units.smul_def]

/-- A presented form is regular: all its weights are units, so its radical vanishes. -/
theorem nondegenerate_presentedForm [Invertible (2 : K)] (p : RegularFormPresentation K) :
    (presentedForm p).Nondegenerate := by
  have h2 : NeZero (2 : K) := ⟨(isUnit_of_invertible (2 : K)).ne_zero⟩
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, presentedForm,
    QuadraticForm.radical_weightedSumSquares, Submodule.eq_bot_iff]
  intro v hv
  rw [Pi.mem_spanSubset_iff] at hv
  funext i
  exact hv i (by simp [Units.ne_zero])

/-! ### The carrier -/

/-- Two presentations are related when the forms they present are isometric. Mathlib's
`QuadraticMap.Equivalent` already compares forms on different spaces, so presentations of
different ranks may be compared; `TauCeti.fst_eq_of_presentedForm_equivalent` shows that only
presentations of equal rank are ever related. -/
instance regularFormSetoid (K : Type u) [Field K] : Setoid (RegularFormPresentation K) where
  r p q := (presentedForm p).Equivalent (presentedForm q)
  iseqv :=
    { refl := fun p => QuadraticMap.Equivalent.refl (presentedForm p)
      symm := fun h => h.symm
      trans := fun h h' => h.trans h' }

/-- The relation defining the setoid, unfolded. -/
@[simp]
theorem regularFormSetoid_iff {p q : RegularFormPresentation K} :
    p ≈ q ↔ (presentedForm p).Equivalent (presentedForm q) := Iff.rfl

/-- Isometry classes of diagonal presentations. When `2` is invertible in `K` every presented
form is regular and every regular form on a finite-dimensional space is presented, so this is
exactly the set of isometry classes of regular finite-dimensional quadratic forms; over a field
of characteristic two it is only the quotient of the diagonal presentations by isometry. -/
abbrev RegularFormClass (K : Type u) [Field K] : Type u := Quotient (regularFormSetoid K)

/-- Two presentations have the same class exactly when they present isometric forms. -/
@[simp]
theorem RegularFormClass.mk_eq_mk_iff {p q : RegularFormPresentation K} :
    Quotient.mk (regularFormSetoid K) p = Quotient.mk (regularFormSetoid K) q ↔
      (presentedForm p).Equivalent (presentedForm q) :=
  Quotient.eq

/-- Isometric presented forms have the same number of weights, because an isometry is in
particular a linear equivalence of the underlying coordinate spaces. -/
theorem fst_eq_of_presentedForm_equivalent {p q : RegularFormPresentation K}
    (h : (presentedForm p).Equivalent (presentedForm q)) : p.1 = q.1 := by
  obtain ⟨e⟩ := h
  simpa using e.toLinearEquiv.finrank_eq

/-- The rank of an isometry class. -/
def RegularFormClass.rank : RegularFormClass K → ℕ :=
  Quotient.lift Sigma.fst fun _ _ h => fst_eq_of_presentedForm_equivalent h

/-- The rank of the class of a presentation is the length of its weight tuple. -/
@[simp]
theorem RegularFormClass.rank_mk (p : RegularFormPresentation K) :
    RegularFormClass.rank (Quotient.mk (regularFormSetoid K) p) = p.1 := (rfl)

/-! ### The orthogonal sum -/

/-- The orthogonal sum of two diagonal presentations, obtained by concatenating the two weight
tuples. -/
def RegularFormPresentation.append (p q : RegularFormPresentation K) :
    RegularFormPresentation K :=
  ⟨p.1 + q.1, Fin.append p.2 q.2⟩

/-- Concatenation adds the two ranks. -/
@[simp]
theorem RegularFormPresentation.fst_append (p q : RegularFormPresentation K) :
    (RegularFormPresentation.append p q).1 = p.1 + q.1 := (rfl)

/-- The value of an orthogonal product on the two halves of a concatenated coordinate vector. -/
private theorem prod_apply_split {m n : ℕ} (w : Fin m → Kˣ) (v : Fin n → Kˣ)
    (x : Fin (m + n) → K) :
    ((presentedForm ⟨m, w⟩).prod (presentedForm ⟨n, v⟩))
        (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd m j)) =
      presentedForm ⟨m + n, Fin.append w v⟩ x := by
  rw [QuadraticMap.prod_apply, presentedForm_apply, presentedForm_apply, presentedForm_apply,
    Fin.sum_univ_add]
  simp

/-- Concatenating the weight tuples presents the orthogonal sum of the two presented forms. -/
def presentedFormAppendIsometryEquiv (p q : RegularFormPresentation K) :
    (presentedForm (RegularFormPresentation.append p q)).IsometryEquiv
      ((presentedForm p).prod (presentedForm q)) where
  toLinearEquiv :=
    (LinearEquiv.funCongrLeft K K (finSumFinEquiv (m := p.1) (n := q.1))).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin p.1) (Fin q.1) K K)
  map_app' x := prod_apply_split p.2 q.2 x

/-- The form presented by a concatenation is isometric to the orthogonal sum of the two
presented forms. -/
theorem equivalent_presentedForm_append_prod (p q : RegularFormPresentation K) :
    (presentedForm (RegularFormPresentation.append p q)).Equivalent
      ((presentedForm p).prod (presentedForm q)) :=
  ⟨presentedFormAppendIsometryEquiv p q⟩

/-- Concatenation of presentations respects isometry in each argument. -/
theorem presentedForm_append_congr {p p' q q' : RegularFormPresentation K}
    (hp : (presentedForm p).Equivalent (presentedForm p'))
    (hq : (presentedForm q).Equivalent (presentedForm q')) :
    (presentedForm (RegularFormPresentation.append p q)).Equivalent
      (presentedForm (RegularFormPresentation.append p' q')) :=
  (equivalent_presentedForm_append_prod p q).trans
    ((hp.prod hq).trans (equivalent_presentedForm_append_prod p' q').symm)

/-- Concatenation of presentations is commutative up to isometry. -/
theorem presentedForm_append_comm (p q : RegularFormPresentation K) :
    (presentedForm (RegularFormPresentation.append p q)).Equivalent
      (presentedForm (RegularFormPresentation.append q p)) := by
  have h : ((presentedForm p).prod (presentedForm q)).Equivalent
      ((presentedForm q).prod (presentedForm p)) :=
    ⟨QuadraticMap.IsometryEquiv.prodComm _ _⟩
  exact ((equivalent_presentedForm_append_prod p q).trans h).trans
    (equivalent_presentedForm_append_prod q p).symm

/-- Concatenation of presentations is associative up to isometry. -/
theorem presentedForm_append_assoc (p q r : RegularFormPresentation K) :
    (presentedForm (RegularFormPresentation.append
        (RegularFormPresentation.append p q) r)).Equivalent
      (presentedForm (RegularFormPresentation.append p
        (RegularFormPresentation.append q r))) := by
  have h₁ : ((presentedForm (RegularFormPresentation.append p q)).prod
      (presentedForm r)).Equivalent
      (((presentedForm p).prod (presentedForm q)).prod (presentedForm r)) :=
    (equivalent_presentedForm_append_prod p q).prod (QuadraticMap.Equivalent.refl _)
  have h₂ : (((presentedForm p).prod (presentedForm q)).prod (presentedForm r)).Equivalent
      ((presentedForm p).prod ((presentedForm q).prod (presentedForm r))) :=
    ⟨QuadraticMap.IsometryEquiv.prodAssoc _ _ _⟩
  have h₃ : ((presentedForm p).prod ((presentedForm q).prod (presentedForm r))).Equivalent
      ((presentedForm p).prod (presentedForm (RegularFormPresentation.append q r))) :=
    (QuadraticMap.Equivalent.refl _).prod (equivalent_presentedForm_append_prod q r).symm
  exact ((((equivalent_presentedForm_append_prod _ r).trans h₁).trans h₂).trans h₃).trans
    (equivalent_presentedForm_append_prod p (RegularFormPresentation.append q r)).symm

/-- Prepending an empty presentation does not change the form up to isometry. -/
theorem presentedForm_nil_append (w : Fin 0 → Kˣ) (q : RegularFormPresentation K) :
    (presentedForm (RegularFormPresentation.append ⟨0, w⟩ q)).Equivalent (presentedForm q) :=
  (equivalent_presentedForm_append_prod ⟨0, w⟩ q).trans
    ⟨QuadraticMap.IsometryEquiv.uniqueProd _ _⟩

/-- Orthogonal sum of isometry classes. -/
instance : Add (RegularFormClass K) :=
  ⟨Quotient.map₂ RegularFormPresentation.append fun _ _ hp _ _ hq =>
    presentedForm_append_congr hp hq⟩

/-- The class of the rank-zero form. -/
instance : Zero (RegularFormClass K) := ⟨Quotient.mk _ ⟨0, Fin.elim0⟩⟩

/-- The sum of two classes is the class of the concatenated presentation. -/
@[simp]
theorem RegularFormClass.mk_add_mk (p q : RegularFormPresentation K) :
    Quotient.mk (regularFormSetoid K) p + Quotient.mk (regularFormSetoid K) q =
      Quotient.mk (regularFormSetoid K) (RegularFormPresentation.append p q) := rfl

/-- The zero class is the class of the empty presentation. -/
theorem RegularFormClass.zero_def :
    (0 : RegularFormClass K) = Quotient.mk (regularFormSetoid K) ⟨0, Fin.elim0⟩ := rfl

/-- Orthogonal sum makes the isometry classes a commutative monoid. This is the additive half of
the semiring structure that carries the Witt-Grothendieck ring. -/
instance : AddCommMonoid (RegularFormClass K) where
  nsmul := nsmulRec
  add_assoc x y z := by
    refine Quotient.inductionOn₃ x y z fun p q r => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_append_assoc p q r)
  zero_add x := by
    refine Quotient.inductionOn x fun q => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_nil_append Fin.elim0 q)
  add_zero x := by
    refine Quotient.inductionOn x fun q => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr
      ((presentedForm_append_comm q ⟨0, Fin.elim0⟩).trans
        (presentedForm_nil_append Fin.elim0 q))
  add_comm x y := by
    refine Quotient.inductionOn₂ x y fun p q => ?_
    exact RegularFormClass.mk_eq_mk_iff.mpr (presentedForm_append_comm p q)

/-- Rank is additive on orthogonal sums. -/
@[simp]
theorem RegularFormClass.rank_add (x y : RegularFormClass K) :
    RegularFormClass.rank (x + y) = RegularFormClass.rank x + RegularFormClass.rank y := by
  refine Quotient.inductionOn₂ x y fun p q => ?_
  rw [RegularFormClass.mk_add_mk, RegularFormClass.rank_mk, RegularFormClass.rank_mk,
    RegularFormClass.rank_mk, RegularFormPresentation.fst_append]

/-- The zero class has rank zero. -/
@[simp]
theorem RegularFormClass.rank_zero : RegularFormClass.rank (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, RegularFormClass.rank_mk]

/-! ### The class of a regular form -/

variable [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Every regular form on a finite-dimensional space has a diagonal presentation. -/
theorem exists_presentedForm_equivalent (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    ∃ p : RegularFormPresentation K, Q.Equivalent (presentedForm p) := by
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  exact ⟨⟨Module.finrank K V, w⟩, by
    rwa [presentedForm_eq_weightedSumSquares]⟩

/-- The isometry class of a regular form on a finite-dimensional space. -/
noncomputable def formClass (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    RegularFormClass K :=
  Quotient.mk _ (exists_presentedForm_equivalent Q hQ).choose

/-- The class of a regular form is computed by any of its diagonalizations. -/
theorem formClass_mk (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (p : RegularFormPresentation K) (hp : Q.Equivalent (presentedForm p)) :
    formClass Q hQ = Quotient.mk (regularFormSetoid K) p :=
  RegularFormClass.mk_eq_mk_iff.mpr
    (((exists_presentedForm_equivalent Q hQ).choose_spec).symm.trans hp)

/-- Two regular forms are isometric exactly when their classes agree. -/
@[simp]
theorem formClass_eq_iff (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (R : QuadraticForm K W)
    (hR : R.Nondegenerate) : formClass Q hQ = formClass R hR ↔ Q.Equivalent R := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  obtain ⟨q, hq⟩ := exists_presentedForm_equivalent R hR
  rw [formClass_mk Q hQ p hp, formClass_mk R hR q hq, RegularFormClass.mk_eq_mk_iff]
  exact ⟨fun h => hp.trans (h.trans hq.symm), fun h => hp.symm.trans (h.trans hq)⟩

/-- The class of a presented form is the class of its presentation. -/
@[simp]
theorem formClass_presentedForm (p : RegularFormPresentation K) :
    formClass (presentedForm p) (nondegenerate_presentedForm p) =
      Quotient.mk (regularFormSetoid K) p :=
  formClass_mk _ _ p (QuadraticMap.Equivalent.refl _)

/-- The rank of the class of a regular form is the dimension of its space. -/
@[simp]
theorem rank_formClass (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    RegularFormClass.rank (formClass Q hQ) = Module.finrank K V := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.rank_mk]
  obtain ⟨e⟩ := hp
  simpa using e.toLinearEquiv.finrank_eq.symm

/-- The class of an orthogonal product is the sum of the classes. -/
theorem formClass_prod (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (R : QuadraticForm K W)
    (hR : R.Nondegenerate) :
    formClass (Q.prod R) (hQ.prod hR) = formClass Q hQ + formClass R hR := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  obtain ⟨q, hq⟩ := exists_presentedForm_equivalent R hR
  rw [formClass_mk Q hQ p hp, formClass_mk R hR q hq, RegularFormClass.mk_add_mk,
    formClass_mk _ _ _ ((hp.prod hq).trans (equivalent_presentedForm_append_prod p q).symm)]

end TauCeti
