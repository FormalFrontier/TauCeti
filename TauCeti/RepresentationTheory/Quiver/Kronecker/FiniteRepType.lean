/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.LocalRing.Basic
public import TauCeti.RingTheory.Polynomial.Truncated

/-!
# The Kronecker quiver has infinite representation type

This file exhibits, over *every* field, an infinite family of pairwise non-isomorphic
finite-dimensional indecomposable representations of the generalized Kronecker quiver as soon as
there are two distinct arrows: `TauCeti.kroneckerJordanRep` puts the truncated polynomial algebra
`k[X]/(Xⁿ⁺¹)` at both vertices, lets one distinguished arrow act by multiplication by the class of
`X` and every other arrow by the identity, and is indecomposable because its endomorphism algebra
is the local ring `k[X]/(Xⁿ⁺¹)`. The underlying construction of a representation from a pair of
vector spaces and a linear map along each arrow is `TauCeti.kroneckerRep`, in
`TauCeti.RepresentationTheory.Quiver.Kronecker.Representation`.

The Kronecker quiver `• ⇉ •` is the case of a two-element arrow type, and it is the boundary case
of Gabriel's theorem: connected and acyclic, but not of Dynkin type, its Tits form being the
positive *semi*definite `(a - b) ^ 2` of `TauCeti.Quiver.Kronecker.titsForm_apply`. The family below
supplies the representation-theoretic half of that boundary, namely that finite representation type
genuinely fails there.

The `A₂` quiver `• → •` -- a one-element arrow type -- is of Dynkin type and *does* have finite
representation type, so the hypothesis that two distinct arrows exist is not an artefact: with a
single arrow there is no arrow beside the distinguished one, so nothing forces the two components
of an endomorphism to agree and the Jordan block below is not indecomposable -- the `A₂`
indecomposables have dimension vectors `(1, 0)`, `(0, 1)` and `(1, 1)`.

## Main definitions

* `TauCeti.kroneckerJordanRep`: the nilpotent Jordan block of size `n + 1`, spread over the two
  vertices.

## Main results

* `TauCeti.indecomposable_kroneckerJordanRep`: the Jordan blocks are indecomposable, as soon as
  some arrow other than the distinguished one exists.
* `TauCeti.nonempty_kroneckerJordanRep_iso_iff`: two of them are isomorphic exactly when their
  sizes agree.
* `TauCeti.not_isFiniteRepType_kronecker`: over any field, a generalized Kronecker quiver with at
  least two arrows has infinite representation type.

## Implementation notes

`TauCeti.kroneckerJordanRep` carries `@[expose]`, for the reason the loop-quiver file
`TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType` records, and
`TauCeti.kroneckerRep` does too: a functor built by `CategoryTheory.Paths.lift` reveals its value
on objects only through its definition. The obstruction is at the level of *statements*, not of
proofs, so no characteristic lemma can remove it: without `@[expose]`, every statement below
reading an endomorphism of a Jordan block as a linear map on `k[X]/(Xⁿ⁺¹)` fails to elaborate.

Indecomposability runs through `TauCeti.indecomposable_of_idempotent_eq_zero_or_id` rather than the
brick criterion: the endomorphism algebra of a Jordan block is `k[X]/(Xⁿ⁺¹)`, which is not a field.
It is a *local* ring (`TauCeti.isLocalRing_adjoinRoot_X_pow`), and that is exactly enough, by
`TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`.

The two components of an endomorphism are forced to agree by naturality along an arrow acting as
the identity, which is why a second arrow is needed; the distinguished arrow then contributes the
one genuine relation, that the common component commutes with multiplication by the class of `X`,
and `AdjoinRoot.eq_mulRight_of_root_mul` turns that relation into the description of the
endomorphism algebra. Taking the vertex spaces to be a truncated polynomial algebra rather than a
line is what makes the result uniform in the base field: the one-dimensional representations
`k ⇉ k`, with the two arrows acting by `1` and by a scalar, are indecomposable and pairwise
non-isomorphic, but over a finite field there are only finitely many of them.

## References

This proves the `¬ IsFiniteRepType` half of the “Kronecker quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose other half -- the
positive semidefinite Tits form `(a - b) ^ 2` with radical `(1, 1)` -- is
`TauCeti.Quiver.Kronecker.titsForm_apply` and
`TauCeti.Quiver.Kronecker.titsForm_eq_zero_iff_exists_smul`. See Derksen--Weyman, *An Introduction
to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the Representation Theory
of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Polynomial

universe u v

variable {k : Type u} [Field k] {A : Type v}

/-! ### The Jordan blocks -/

-- The distinguished arrow is singled out by an `if`, so a `Decidable` instance for equality in `A`
-- is needed; the Jordan blocks are noncomputable anyway, so it is taken classically rather than
-- imposed as a hypothesis on `A`. The two lemmas below discharge the `if` in either direction, so
-- no statement in this file mentions the instance.
open Classical in
variable (k) in
/-- **The Kronecker Jordan block of size `n + 1`**: the truncated polynomial algebra `k[X]/(Xⁿ⁺¹)`
at both vertices of the generalized Kronecker quiver, with the arrow `a₁` acting by multiplication
by the class of `X` and every other arrow by the identity. -/
@[expose]
noncomputable def kroneckerJordanRep (a₁ : A) (n : ℕ) :
    QuiverRep k (Quiver.Kronecker A) :=
  kroneckerRep k (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))))
    (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))))
    fun a ↦ if a = a₁ then
        ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))
      else 𝟙 _

variable {a₀ a₁ : A} {n : ℕ}

-- Not `@[simp]`: these two rewrite the vertex spaces inside the implicit arguments of
-- `ModuleCat.Hom.hom`, which would take the left-hand sides of the two `_apply` lemmas below out
-- of simp-normal form (`simpNF`). Those are the forms `simp` needs, so these stay plain rewrites.
theorem kroneckerJordanRep_obj_src :
    (kroneckerJordanRep k a₁ n).obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

theorem kroneckerJordanRep_obj_tgt :
    (kroneckerJordanRep k a₁ n).obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

/-- The distinguished arrow acts on a Jordan block by multiplication by the class of `X`. -/
theorem kroneckerJordanRep_map_arrowPath_self :
    (kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁) =
      ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1)))) :=
  (kroneckerRep_map_arrowPath _ _ _ a₁).trans (ite_eq_left rfl)

/-- The action of the distinguished arrow, read on an element. -/
@[simp]
theorem kroneckerJordanRep_map_arrowPath_self_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁)).hom x =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x := by
  rw [kroneckerJordanRep_map_arrowPath_self]
  rfl

/-- Every other arrow acts on a Jordan block by the identity. -/
theorem kroneckerJordanRep_map_arrowPath_of_ne (h : a₀ ≠ a₁) :
    (kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀) =
      𝟙 (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))) :=
  (kroneckerRep_map_arrowPath _ _ _ a₀).trans (ite_eq_right h)

/-- The action of any other arrow, read on an element. -/
@[simp]
theorem kroneckerJordanRep_map_arrowPath_of_ne_apply (h : a₀ ≠ a₁)
    (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀)).hom x = x := by
  rw [kroneckerJordanRep_map_arrowPath_of_ne h]
  exact ModuleCat.id_apply (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))) x

/-- The linear map underlying an endomorphism of a Jordan block at the source vertex. -/
private noncomputable def jordanApp (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    AdjoinRoot ((X : k[X]) ^ (n + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (n + 1)) :=
  (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom

private theorem jordanApp_eq (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    jordanApp e = (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom := (rfl)

private theorem jordanApp_zero :
    jordanApp (0 : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) = 0 := (rfl)

private theorem jordanApp_id :
    jordanApp (𝟙 (kroneckerJordanRep k a₁ n)) = LinearMap.id := (rfl)

private theorem jordanApp_comp (e e' : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    jordanApp (e ≫ e') = (jordanApp e').comp (jordanApp e) := (rfl)

/-- **The two components of an endomorphism of a Jordan block agree**, by naturality along an arrow
that acts as the identity. -/
private theorem app_tgt_eq_app_src (h : a₀ ≠ a₁)
    (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := by
  refine ModuleCat.hom_ext
    (LinearMap.ext fun (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) ↦ ?_)
  have hnat : (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))).hom
        (((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀)).hom x) =
      ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀)).hom
        ((e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x) (e.naturality (Quiver.Kronecker.arrowPath a₀))
  rw [kroneckerJordanRep_map_arrowPath_of_ne_apply h] at hnat
  exact hnat.trans (kroneckerJordanRep_map_arrowPath_of_ne_apply h _)

/-- **Naturality along the distinguished arrow**, read on an element: the underlying map of an
endomorphism commutes with multiplication by the class of `X`. -/
private theorem jordanApp_root_mul (h : a₀ ≠ a₁)
    (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n)
    (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    jordanApp e (AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x) =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * jordanApp e x := by
  have hnat : (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))).hom
        (((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁)).hom x) =
      ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁)).hom
        ((e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x) (e.naturality (Quiver.Kronecker.arrowPath a₁))
  simp only [app_tgt_eq_app_src h e] at hnat
  rw [kroneckerJordanRep_map_arrowPath_self_apply] at hnat
  rw [jordanApp_eq]
  exact hnat.trans (kroneckerJordanRep_map_arrowPath_self_apply _)

/-- **An endomorphism of a Jordan block is multiplication by its value at `1`**, by
`TauCeti.AdjoinRoot.eq_mulRight_of_root_mul`: it commutes with multiplication by the class of
`X`. -/
private theorem jordanApp_eq_mulRight (h : a₀ ≠ a₁)
    (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    jordanApp e = LinearMap.mulRight k (jordanApp e 1) :=
  AdjoinRoot.eq_mulRight_of_root_mul (monic_X_pow (R := k) (n + 1)) (jordanApp_root_mul h e)

/-- **An endomorphism of a Jordan block is determined by its component at the source vertex**: the
component at the target agrees with it, by `app_tgt_eq_app_src`. -/
private theorem jordanApp_ext (h : a₀ ≠ a₁)
    {e e' : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n}
    (heq : jordanApp e = jordanApp e') : e = e' := by
  have hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := ModuleCat.hom_ext heq
  exact kronecker_hom_ext hsrc
    (by rw [app_tgt_eq_app_src h e, app_tgt_eq_app_src h e', hsrc])

/-- A Jordan block is finite-dimensional: both of its vertex spaces are `k[X]/(Xⁿ⁺¹)`. -/
theorem isFinDim_kroneckerJordanRep :
    IsFinDim k (Quiver.Kronecker A) (kroneckerJordanRep k a₁ n) := by
  refine isFinDim_iff.mpr fun w ↦ ?_
  cases w <;> exact (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot

/-- The dimension vector of a Jordan block is `n + 1` at both vertices. -/
theorem dimVector_kroneckerJordanRep (w : Quiver.Kronecker A) :
    dimVector (kroneckerJordanRep k a₁ n) w = n + 1 := by
  rw [dimVector_apply]
  -- `AdjoinRoot f` *is* `k[X] ⧸ (f)`, so Mathlib's dimension formula for such a quotient applies.
  cases w <;> exact finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (n + 1))

/-- A Jordan block is nonzero: its vertex spaces are the nontrivial ring `k[X]/(Xⁿ⁺¹)`. -/
theorem not_isZero_kroneckerJordanRep :
    ¬ IsZero (kroneckerJordanRep k a₁ n) := by
  intro hz
  have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
    ModuleCat.subsingleton_of_isZero
      (hz.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1)))

/-- **A Kronecker Jordan block is indecomposable, as soon as some arrow other than the distinguished
one exists.** An idempotent endomorphism is multiplication by an idempotent of `k[X]/(Xⁿ⁺¹)`, and
that ring is local, so that idempotent is `0` or `1`. -/
theorem indecomposable_kroneckerJordanRep (h : a₀ ≠ a₁) :
    Indecomposable (kroneckerJordanRep k a₁ n) := by
  refine indecomposable_of_idempotent_eq_zero_or_id not_isZero_kroneckerJordanRep fun e he ↦ ?_
  have hmul := jordanApp_eq_mulRight h e
  have hmul_apply : ∀ x, jordanApp e x = x * jordanApp e 1 := fun x ↦ by rw [hmul]; simp
  have hidem : IsIdempotentElem (jordanApp e 1) := by
    have h' := congrArg (fun t ↦ jordanApp t 1) he
    simp only [jordanApp_comp, LinearMap.comp_apply] at h'
    rw [hmul_apply (jordanApp e 1)] at h'
    exact h'
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
  · refine Or.inl (jordanApp_ext h ?_)
    rw [hmul, h0, jordanApp_zero]
    exact LinearMap.ext fun x ↦ by simp
  · refine Or.inr (jordanApp_ext h ?_)
    rw [hmul, h1, jordanApp_id]
    exact LinearMap.ext fun x ↦ by simp

/-- **Jordan blocks of different sizes are non-isomorphic**: their dimension vectors differ. -/
theorem eq_of_nonempty_kroneckerJordanRep_iso {m n : ℕ}
    (h : Nonempty (kroneckerJordanRep k a₁ m ≅ kroneckerJordanRep k a₁ n)) : m = n := by
  obtain ⟨e⟩ := h
  have hd := congrFun (dimVector_eq_of_iso e) (Quiver.Kronecker.src : Quiver.Kronecker A)
  rw [dimVector_kroneckerJordanRep, dimVector_kroneckerJordanRep] at hd
  omega

/-- Two Kronecker Jordan blocks are isomorphic exactly when their sizes agree. -/
@[simp]
theorem nonempty_kroneckerJordanRep_iso_iff {m n : ℕ} :
    Nonempty (kroneckerJordanRep k a₁ m ≅ kroneckerJordanRep k a₁ n) ↔ m = n :=
  ⟨eq_of_nonempty_kroneckerJordanRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **A generalized Kronecker quiver with at least two arrows has infinite representation type over
every field.** The Jordan blocks `TauCeti.kroneckerJordanRep` are finite-dimensional,
indecomposable and pairwise non-isomorphic, so `ℕ` indexes an infinite family of them.

For a one-element arrow type this fails, and must: that is the `A₂` quiver `• → •`, of Dynkin type,
which has exactly three indecomposables. -/
theorem not_isFiniteRepType_kronecker (k : Type u) [Field k] (A : Type v) [Nontrivial A] :
    ¬ IsFiniteRepType.{u, 0, v, u} k (Quiver.Kronecker A) := by
  obtain ⟨a₀, a₁, h⟩ := exists_pair_ne A
  exact not_isFiniteRepType_of_infinite (M := kroneckerJordanRep k a₁)
    (fun _ ↦ isFinDim_kroneckerJordanRep)
    (fun _ ↦ indecomposable_kroneckerJordanRep h)
    fun _ _ hne hiso ↦ hne (eq_of_nonempty_kroneckerJordanRep_iso hiso)

end TauCeti
