/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RingTheory.LocalRing.Basic
public import TauCeti.RingTheory.Polynomial.Truncated

/-!
# The Kronecker quiver has infinite representation type

A representation of the generalized Kronecker quiver is a pair of vector spaces together with one
linear map between them for each arrow. This file builds them as `TauCeti.kroneckerRep`, and
exhibits, over *every* field, an infinite family of pairwise non-isomorphic finite-dimensional
indecomposable ones as soon as there are two distinct arrows: `TauCeti.kroneckerJordanRep` puts the
truncated polynomial algebra `k[X]/(Xⁿ⁺¹)` at both vertices, lets one distinguished arrow act by
multiplication by the class of `X` and every other arrow by the identity, and is indecomposable
because its endomorphism algebra is the local ring `k[X]/(Xⁿ⁺¹)`.

The Kronecker quiver `• ⇉ •` is the case of a two-element arrow type, and it is the boundary case
of Gabriel's theorem: connected and acyclic, but not of Dynkin type, its Tits form being the
positive *semi*definite `(a - b) ^ 2` of `TauCeti.Quiver.Kronecker.titsForm_apply`. The family below
supplies the representation-theoretic half of that boundary, namely that finite representation type
genuinely fails there.

The `A₂` quiver `• → •` -- a one-element arrow type -- is of Dynkin type and *does* have finite
representation type, so the hypothesis that two distinct arrows exist is not an artefact: with a
single arrow the construction below degenerates, every arrow acting by the identity.

## Main definitions

* `TauCeti.kroneckerRep`: the representation of the generalized Kronecker quiver with prescribed
  vertex spaces and a prescribed linear map along each arrow.
* `TauCeti.kroneckerJordanRep`: the nilpotent Jordan block of size `n + 1`, spread over the two
  vertices.

## Main results

* `TauCeti.kronecker_hom_ext`: a morphism of representations of the generalized Kronecker quiver is
  determined by its two components.
* `TauCeti.indecomposable_kroneckerJordanRep`: the Jordan blocks are indecomposable, as soon as
  some arrow other than the distinguished one exists.
* `TauCeti.nonempty_kroneckerJordanRep_iso_iff`: two of them are isomorphic exactly when their
  sizes agree.
* `TauCeti.not_isFiniteRepType_kronecker`: over any field, a generalized Kronecker quiver with at
  least two arrows has infinite representation type.

## Implementation notes

`TauCeti.kroneckerRep` and `TauCeti.kroneckerJordanRep` carry `@[expose]`, for the reason the
loop-quiver file `TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType` records: a functor
built by `CategoryTheory.Paths.lift` reveals its value on objects only through its definition, so
without it the statements below -- which read an endomorphism as a linear map on `k[X]/(Xⁿ⁺¹)` --
do not even elaborate.

Indecomposability runs through `TauCeti.indecomposable_of_idempotent_eq_zero_or_id` rather than the
brick criterion: the endomorphism algebra of a Jordan block is `k[X]/(Xⁿ⁺¹)`, which is not a field.
It is a *local* ring (`TauCeti.isLocalRing_adjoinRoot_X_pow`), and that is exactly enough, by
`TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`.

The two components of an endomorphism are forced to agree by naturality along an arrow acting as
the identity, which is why a second arrow is needed; the distinguished arrow then contributes the
one genuine relation, that the common component commutes with multiplication by the class of `X`.
Taking the vertex spaces to be a truncated polynomial algebra rather than a line is what makes the
result uniform in the base field: the one-dimensional representations `k ⇉ k`, with the two arrows
acting by `1` and by a scalar, are indecomposable and pairwise non-isomorphic, but over a finite
field there are only finitely many of them.

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

universe u v t

variable {k : Type u} [Field k] {A : Type v}

/-! ### Representations of the generalized Kronecker quiver -/

section Rep

variable (k) in
/-- **A representation of the generalized Kronecker quiver**: a vector space `M` at the source, a
vector space `N` at the target, and a linear map `f a : M ⟶ N` along the arrow indexed by `a`.
There are no other arrows and no nontrivial paths, so this is the whole datum. -/
@[expose]
def kroneckerRep (M N : ModuleCat.{t} k) (f : A → (M ⟶ N)) :
    QuiverRep k (Quiver.Kronecker A) :=
  Paths.lift
    { obj := fun a ↦ match a with
        | .src => M
        | .tgt => N
      map := fun {a b} e ↦ match a, b, e with
        | .src, .tgt, e => f e
        | .src, .src, e => isEmptyElim e
        | .tgt, .src, e => isEmptyElim e
        | .tgt, .tgt, e => isEmptyElim e }

variable (M N : ModuleCat.{t} k) (f : A → (M ⟶ N))

@[simp]
theorem kroneckerRep_obj_src :
    (kroneckerRep k M N f).obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) = M :=
  rfl

@[simp]
theorem kroneckerRep_obj_tgt :
    (kroneckerRep k M N f).obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) = N :=
  rfl

/-- The arrow indexed by `a` acts on `TauCeti.kroneckerRep` by `f a`. -/
@[simp]
theorem kroneckerRep_map_arrowPath (a : A) :
    (kroneckerRep k M N f).map (Quiver.Kronecker.arrowPath a) = f a := by
  rw [← Quiver.Kronecker.toPath_arrow]
  exact (Paths.lift_toPath _ (Quiver.Kronecker.arrow a)).trans
    (congrArg f (Quiver.Kronecker.arrow_def a))

end Rep

/-- **A morphism of representations of the generalized Kronecker quiver is determined by its two
components.** The quiver has two vertices, so a natural transformation is a pair of linear maps. -/
theorem kronecker_hom_ext {ρ σ : QuiverRep.{u, 0, v, t} k (Quiver.Kronecker A)} {e e' : ρ ⟶ σ}
    (hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
    (htgt : e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))) : e = e' := by
  refine NatTrans.ext (funext fun w ↦ ?_)
  cases w
  · exact hsrc
  · exact htgt

/-! ### The Jordan blocks -/

variable (k) in
/-- **The Kronecker Jordan block of size `n + 1`**: the truncated polynomial algebra `k[X]/(Xⁿ⁺¹)`
at both vertices of the generalized Kronecker quiver, with the arrow `a₁` acting by multiplication
by the class of `X` and every other arrow by the identity. -/
@[expose]
noncomputable def kroneckerJordanRep [DecidableEq A] (a₁ : A) (n : ℕ) :
    QuiverRep k (Quiver.Kronecker A) :=
  kroneckerRep k (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))))
    (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))))
    fun a ↦ if a = a₁ then
        ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))
      else 𝟙 _

variable [DecidableEq A] {a₀ a₁ : A} {n : ℕ}

@[simp]
theorem kroneckerJordanRep_obj_src :
    (kroneckerJordanRep k a₁ n).obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

@[simp]
theorem kroneckerJordanRep_obj_tgt :
    (kroneckerJordanRep k a₁ n).obj (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
  rfl

/-- The action of an arrow on a Jordan block: multiplication by the class of `X` along the
distinguished arrow, and the identity along every other arrow. -/
theorem kroneckerJordanRep_map_arrowPath (a : A) :
    (kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a) =
      if a = a₁ then
          ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1))))
        else 𝟙 (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))) :=
  kroneckerRep_map_arrowPath _ _ _ a

/-- The distinguished arrow acts on a Jordan block by multiplication by the class of `X`. -/
theorem kroneckerJordanRep_map_arrowPath_self :
    (kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁) =
      ModuleCat.ofHom (LinearMap.mulLeft k (AdjoinRoot.root ((X : k[X]) ^ (n + 1)))) := by
  rw [kroneckerJordanRep_map_arrowPath]
  simp

/-- The action of the distinguished arrow, read on an element. -/
theorem kroneckerJordanRep_map_arrowPath_self_apply (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₁)).hom x =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) * x := by
  rw [kroneckerJordanRep_map_arrowPath_self]
  rfl

/-- Every other arrow acts on a Jordan block by the identity. -/
theorem kroneckerJordanRep_map_arrowPath_of_ne (h : a₀ ≠ a₁) :
    (kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀) =
      𝟙 (ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (n + 1)))) := by
  rw [kroneckerJordanRep_map_arrowPath]
  simp [h]

/-- The action of any other arrow, read on an element. -/
theorem kroneckerJordanRep_map_arrowPath_of_ne_apply (h : a₀ ≠ a₁)
    (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) :
    ((kroneckerJordanRep k a₁ n).map (Quiver.Kronecker.arrowPath a₀)).hom x = x := by
  rw [kroneckerJordanRep_map_arrowPath_of_ne h]
  rfl

/-- The linear map underlying an endomorphism of a Jordan block at the source vertex. -/
private noncomputable def jordanApp (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    AdjoinRoot ((X : k[X]) ^ (n + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (n + 1)) :=
  (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom

private theorem jordanApp_eq (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    jordanApp e = (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom := (rfl)

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

/-- **An endomorphism of a Jordan block is multiplication by its value at `1`.** It commutes with
multiplication by the class of `X`, hence with multiplication by every power of it, and those
powers are a basis. -/
private theorem jordanApp_eq_mulRight (h : a₀ ≠ a₁)
    (e : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n) :
    jordanApp e = LinearMap.mulRight k (jordanApp e 1) := by
  have hpow : ∀ i : ℕ, jordanApp e (AdjoinRoot.root ((X : k[X]) ^ (n + 1)) ^ i) =
      AdjoinRoot.root ((X : k[X]) ^ (n + 1)) ^ i * jordanApp e 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ' (AdjoinRoot.root ((X : k[X]) ^ (n + 1))) i, jordanApp_root_mul h, ih,
        ← mul_assoc, ← pow_succ' (AdjoinRoot.root ((X : k[X]) ^ (n + 1))) i]
  refine (AdjoinRoot.powerBasis' (monic_X_pow (R := k) (n + 1))).basis.ext fun i ↦ ?_
  rw [PowerBasis.coe_basis]
  simpa using hpow i

/-- A Jordan block is finite-dimensional: both of its vertex spaces are `k[X]/(Xⁿ⁺¹)`. -/
theorem isFinDim_kroneckerJordanRep :
    IsFinDim k (Quiver.Kronecker A) (kroneckerJordanRep k a₁ n) := by
  refine isFinDim_iff.mpr fun w ↦ ?_
  cases w <;> exact (monic_X_pow (R := k) (n + 1)).finite_adjoinRoot

/-- The dimension vector of a Jordan block is `n + 1` at both vertices. -/
theorem dimVector_kroneckerJordanRep (w : Quiver.Kronecker A) :
    dimVector (kroneckerJordanRep k a₁ n) w = n + 1 := by
  rw [dimVector_apply]
  cases w <;> exact finrank_adjoinRoot_X_pow k (n + 1)

/-- A Jordan block is nonzero: its vertex spaces are the nontrivial ring `k[X]/(Xⁿ⁺¹)`. -/
theorem not_isZero_kroneckerJordanRep :
    ¬ IsZero (kroneckerJordanRep k a₁ n) := by
  intro hz
  have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
    ModuleCat.subsingleton_of_isZero
      (hz.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (n + 1)))

/-- **A Kronecker Jordan block is indecomposable.** An idempotent endomorphism is multiplication by
an idempotent of `k[X]/(Xⁿ⁺¹)`, and that ring is local, so that idempotent is `0` or `1`. -/
theorem indecomposable_kroneckerJordanRep (h : a₀ ≠ a₁) :
    Indecomposable (kroneckerJordanRep k a₁ n) := by
  refine indecomposable_of_idempotent_eq_zero_or_id not_isZero_kroneckerJordanRep fun e he ↦ ?_
  have hmul : ∀ x, jordanApp e x = x * jordanApp e 1 := fun x ↦ by
    rw [jordanApp_eq_mulRight h e]; simp
  have hcomp : jordanApp e (jordanApp e 1) = jordanApp e 1 := by
    have hidem : (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom
          ((e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom
            (1 : AdjoinRoot ((X : k[X]) ^ (n + 1)))) =
        (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom
          (1 : AdjoinRoot ((X : k[X]) ^ (n + 1))) :=
      congrArg (fun g : kroneckerJordanRep k a₁ n ⟶ kroneckerJordanRep k a₁ n ↦
        (ModuleCat.Hom.hom (g.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))))
          (1 : AdjoinRoot ((X : k[X]) ^ (n + 1)))) he
    rw [jordanApp_eq]
    exact hidem
  have hsq : IsIdempotentElem (jordanApp e 1) := by
    have h1 : jordanApp e 1 * jordanApp e 1 = jordanApp e 1 := by
      rw [← hmul (jordanApp e 1)]
      exact hcomp
    exact h1
  rcases IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hsq with h0 | h1
  · refine Or.inl (kronecker_hom_ext ?_ ?_)
    · refine ModuleCat.hom_ext
        (LinearMap.ext fun (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) ↦ ?_)
      have hx : jordanApp e x = 0 := by rw [hmul x, h0, mul_zero]
      exact hx
    · rw [app_tgt_eq_app_src h e]
      refine ModuleCat.hom_ext
        (LinearMap.ext fun (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) ↦ ?_)
      have hx : jordanApp e x = 0 := by rw [hmul x, h0, mul_zero]
      exact hx
  · refine Or.inr (kronecker_hom_ext ?_ ?_)
    · refine ModuleCat.hom_ext
        (LinearMap.ext fun (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) ↦ ?_)
      have hx : jordanApp e x = x := by rw [hmul x, h1, mul_one]
      exact hx
    · rw [app_tgt_eq_app_src h e]
      refine ModuleCat.hom_ext
        (LinearMap.ext fun (x : AdjoinRoot ((X : k[X]) ^ (n + 1))) ↦ ?_)
      have hx : jordanApp e x = x := by rw [hmul x, h1, mul_one]
      exact hx

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
  classical
  obtain ⟨a₀, a₁, h⟩ := exists_pair_ne A
  exact not_isFiniteRepType_of_infinite (M := kroneckerJordanRep k a₁)
    (fun _ ↦ isFinDim_kroneckerJordanRep)
    (fun _ ↦ indecomposable_kroneckerJordanRep h)
    fun _ _ hne hiso ↦ hne (eq_of_nonempty_kroneckerJordanRep_iso hiso)

end TauCeti
