/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Kronecker.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Representation
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.Representation.Indecomposable

/-!
# The pencil of lines over the generalized Kronecker quiver

Put the base field at both vertices of the generalized Kronecker quiver, let one distinguished
arrow act by multiplication by a scalar `c` and every other arrow by the identity. This file
builds that representation, `TauCeti.kroneckerLineRep`, and proves that the resulting family is
made of pairwise non-isomorphic indecomposables:

`kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d ↔ c = d`.

Every member of the family has dimension vector `(1, 1)`. So on a quiver with at least two arrows
the dimension vector of a finite-dimensional indecomposable **does not determine it**, and its
Tits value is `2 - #arrows`, not `1`. Both facts are sharpness statements: the Gabriel injection
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic` and the root property
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic` are proved for an acyclic
quiver whose Tits form is *positive definite*, and the Kronecker quiver -- acyclic, with the
positive semidefinite Tits form `(a - b) ^ 2` of `TauCeti.Quiver.Kronecker.titsForm_apply` --
shows that neither survives the weakening of that hypothesis to acyclicity alone.

The family is the affine chart of the `ℙ¹`-family the Kronecker quiver is known for: letting the
two arrows of `• ⇉ •` act by a pair of scalars `(c₀, c₁)`, rescaling that pair by a unit produces
an isomorphic representation, so the classes are the points `[c₀ : c₁]` of the projective line.
Normalizing the non-distinguished arrows to the identity picks the chart `c₁ ≠ 0` and
parametrizes it by `c = c₀ / c₁`; the single class it omits is the point at infinity, where the
distinguished arrow acts by the identity and every other arrow by zero.

The member at `c = 0` is the smallest Jordan block `TauCeti.kroneckerJordanRep k a₁ 0` of
`TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType`, up to the identification of
`k[X]/(X)` with `k`. That file settles the representation type of the quiver with the blocks of
every size, which grow in dimension, and records there that the lines below would only settle it
over an infinite base field. The point of the lines is the other one: they are infinitely many
indecomposables *at a single dimension vector* when the field is infinite, and already two of
them over any field at all.

## Main definitions

* `TauCeti.kroneckerLineRep`: the line `k` at both vertices of the generalized Kronecker quiver,
  the distinguished arrow acting by a scalar and every other arrow by the identity.

## Main results

* `TauCeti.indecomposable_kroneckerLineRep`: a line representation is indecomposable, as soon as
  some arrow other than the distinguished one exists; its endomorphisms are recorded faithfully by
  a single scalar.
* `TauCeti.nonempty_kroneckerLineRep_iso_iff`: **two of them are isomorphic exactly when their
  scalars agree.**
* `TauCeti.dimVector_kroneckerLineRep`: every line representation has dimension vector `1` at
  both vertices.
* `TauCeti.exists_indecomposable_dimVector_eq_not_nonempty_iso`: **outside Dynkin type the
  dimension vector does not determine an indecomposable**: over every field, a generalized
  Kronecker quiver with two distinct arrows carries two non-isomorphic finite-dimensional
  indecomposables of the same dimension vector.
* `TauCeti.titsForm_dimVector_kroneckerLineRep`: the Tits value of that common dimension vector is
  `2 - #arrows`, which is `1` only for the `A₂` quiver.

## Implementation notes

`TauCeti.kroneckerLineRep` carries `@[expose]`, for the reason
`TauCeti.RepresentationTheory.Quiver.Kronecker.Representation` records for
`TauCeti.kroneckerRep`: a functor built by `CategoryTheory.Paths.lift` reveals its value on
objects only through its definition, so without it every statement below reading a component of a
morphism as a linear map on `k` fails to elaborate.

Indecomposability runs through `TauCeti.indecomposable_of_injective_of_isLocalRing` at the base
field, as the Jordan blocks do at a truncated polynomial algebra, rather than through the brick
criterion `TauCeti.indecomposable_of_finrank_end_eq_one`: recording an endomorphism by its scalar
is the same work either way, and the local-ring route does not also ask for the endomorphism
*space* to be identified with `k` as a module.

The private scalar recording a morphism is defined for a morphism between two line
representations with possibly different scalars, not only for an endomorphism: the isomorphism
classification composes it along an isomorphism and its inverse, which are morphisms of that
mixed shape.

## References

This supplies the `ℙ¹`-family of indecomposables of dimension vector `(1, 1)` asked for by the
"Kronecker quiver" worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. VIII.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {k : Type u} [Field k] {A : Type v}

/-! ### The line representations -/

-- The distinguished arrow is singled out by an `if`, so a `Decidable` instance for equality in `A`
-- is needed; it is taken classically rather than imposed as a hypothesis on `A`, as
-- `TauCeti.kroneckerJordanRep` does. The two lemmas below discharge the `if` in either direction,
-- so no statement in this file mentions the instance.
open Classical in
variable (k) in
/-- **The line representation of the generalized Kronecker quiver at a scalar `c`**: the base field
at both vertices, with the arrow `a₁` acting by multiplication by `c` and every other arrow by the
identity. -/
@[expose]
noncomputable def kroneckerLineRep (a₁ : A) (c : k) : QuiverRep k (Quiver.Kronecker A) :=
  kroneckerRep k (ModuleCat.of k k) (ModuleCat.of k k)
    fun a ↦ if a = a₁ then ModuleCat.ofHom (LinearMap.mulLeft k c) else 𝟙 _

variable {a₀ a₁ : A} {c d : k}

-- Not `@[simp]`: this and `TauCeti.kroneckerLineRep_map_arrowPath_of_ne` rewrite inside the
-- `ModuleCat.Hom.hom` of the two `_apply` lemmas below, taking those left-hand sides out of
-- simp-normal form (`simpNF`), exactly as the corresponding pair for the Jordan blocks does.
/-- The distinguished arrow acts on a line representation by multiplication by its scalar. -/
theorem kroneckerLineRep_map_arrowPath_self :
    (kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₁) =
      ModuleCat.ofHom (LinearMap.mulLeft k c) :=
  (kroneckerRep_map_arrowPath _ _ _ a₁).trans (ite_eq_left rfl)

/-- The action of the distinguished arrow, read on an element. -/
@[simp]
theorem kroneckerLineRep_map_arrowPath_self_apply (x : k) :
    ((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₁)).hom x = c * x := by
  rw [kroneckerLineRep_map_arrowPath_self]
  rfl

/-- Every other arrow acts on a line representation by the identity. -/
theorem kroneckerLineRep_map_arrowPath_of_ne (h : a₀ ≠ a₁) :
    (kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₀) = 𝟙 (ModuleCat.of k k) :=
  (kroneckerRep_map_arrowPath _ _ _ a₀).trans (ite_eq_right h)

/-- The action of any other arrow, read on an element. -/
@[simp]
theorem kroneckerLineRep_map_arrowPath_of_ne_apply (h : a₀ ≠ a₁) (x : k) :
    ((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₀)).hom x = x := by
  rw [kroneckerLineRep_map_arrowPath_of_ne (c := c) h]
  exact ModuleCat.id_apply (ModuleCat.of k k) x

/-- A line representation is finite-dimensional: both of its vertex spaces are the base field. -/
theorem isFinDim_kroneckerLineRep :
    IsFinDim k (Quiver.Kronecker A) (kroneckerLineRep k a₁ c) := by
  refine isFinDim_iff.mpr fun w ↦ ?_
  cases w <;> exact inferInstanceAs (FiniteDimensional k k)

-- Not `@[simp]`: `TauCeti.dimVector_apply` already is, so `simp` unfolds `dimVector` to a
-- `Module.finrank` before this could fire, exactly as for `TauCeti.dimVector_kroneckerJordanRep`.
/-- **The dimension vector of a line representation is `1` at both vertices.** The whole family
therefore sits at the single dimension vector `(1, 1)`. -/
theorem dimVector_kroneckerLineRep (w : Quiver.Kronecker A) :
    dimVector (kroneckerLineRep k a₁ c) w = 1 := by
  rw [dimVector_apply]
  cases w <;> exact Module.finrank_self k

/-- A line representation is nonzero: its vertex spaces are the base field. -/
theorem not_isZero_kroneckerLineRep :
    ¬ IsZero (kroneckerLineRep k a₁ c) := by
  intro hz
  have : Subsingleton k :=
    ModuleCat.subsingleton_of_isZero (hz.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  exact false_of_nontrivial_of_subsingleton k

/-! ### The morphisms between two line representations -/

/-- The linear map underlying a morphism of line representations at the source vertex. -/
private noncomputable def lineApp (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    k →ₗ[k] k :=
  (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom

private theorem lineApp_eq (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    lineApp e = (e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom := (rfl)

private theorem lineApp_zero :
    lineApp (0 : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) = 0 := (rfl)

private theorem lineApp_id : lineApp (𝟙 (kroneckerLineRep k a₁ c)) = LinearMap.id := (rfl)

private theorem lineApp_comp {c' : k} (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d)
    (e' : kroneckerLineRep k a₁ d ⟶ kroneckerLineRep k a₁ c') :
    lineApp (e ≫ e') = (lineApp e').comp (lineApp e) := (rfl)

/-- The scalar recording a morphism of line representations: the value at `1` of the linear map
above. -/
private noncomputable def lineScalar (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) : k :=
  lineApp e 1

private theorem lineScalar_def (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    lineScalar e = lineApp e 1 := (rfl)

/-- **A morphism of line representations acts at the source by multiplication by its scalar**, that
component being a linear endomorphism of the base field. -/
private theorem lineApp_apply (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) (x : k) :
    lineApp e x = x * lineScalar e := by
  rw [lineScalar_def, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

private theorem lineScalar_zero :
    lineScalar (0 : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) = 0 := by
  rw [lineScalar_def, lineApp_zero, LinearMap.zero_apply]

private theorem lineScalar_id : lineScalar (𝟙 (kroneckerLineRep k a₁ c)) = 1 := by
  rw [lineScalar_def, lineApp_id, LinearMap.id_apply]

private theorem lineScalar_comp {c' : k} (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d)
    (e' : kroneckerLineRep k a₁ d ⟶ kroneckerLineRep k a₁ c') :
    lineScalar (e ≫ e') = lineScalar e * lineScalar e' := by
  have h : lineApp (e ≫ e') 1 = lineApp e' (lineApp e 1) := by
    rw [lineApp_comp, LinearMap.comp_apply]
  rw [lineScalar_def, h, lineApp_apply e' (lineApp e 1), ← lineScalar_def]

/-- **The two components of a morphism of line representations agree**, by naturality along an
arrow that acts as the identity on both. -/
private theorem app_tgt_eq_app_src (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A)) =
      e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : k) ↦ ?_)
  have hnat : (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))).hom
        (((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₀)).hom x) =
      ((kroneckerLineRep k a₁ d).map (Quiver.Kronecker.arrowPath a₀)).hom
        ((e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x) (e.naturality (Quiver.Kronecker.arrowPath a₀))
  rw [kroneckerLineRep_map_arrowPath_of_ne_apply h] at hnat
  exact hnat.trans (kroneckerLineRep_map_arrowPath_of_ne_apply h _)

/-- **A morphism of line representations is determined by its component at the source vertex**: the
component at the target agrees with it. -/
private theorem lineApp_ext (h : a₀ ≠ a₁)
    {e e' : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d} (heq : lineApp e = lineApp e') :
    e = e' := by
  have hsrc : e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) =
      e'.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)) := ModuleCat.hom_ext heq
  exact kroneckerRep_hom_ext hsrc
    (by rw [app_tgt_eq_app_src h e, app_tgt_eq_app_src h e', hsrc])

private theorem lineScalar_injective (h : a₀ ≠ a₁) :
    Function.Injective
      (lineScalar : (kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) → k) := by
  intro e e' heq
  refine lineApp_ext h (LinearMap.ext fun x ↦ ?_)
  rw [lineApp_apply, lineApp_apply, heq]

/-- **Naturality along the distinguished arrow**: a morphism from the line at `c` to the line at
`d` intertwines multiplication by `c` with multiplication by `d`. -/
private theorem lineApp_mul (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) (x : k) :
    lineApp e (c * x) = d * lineApp e x := by
  have hnat : (e.app (Quiver.Kronecker.tgt : Paths (Quiver.Kronecker A))).hom
        (((kroneckerLineRep k a₁ c).map (Quiver.Kronecker.arrowPath a₁)).hom x) =
      ((kroneckerLineRep k a₁ d).map (Quiver.Kronecker.arrowPath a₁)).hom
        ((e.app (Quiver.Kronecker.src : Paths (Quiver.Kronecker A))).hom x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x) (e.naturality (Quiver.Kronecker.arrowPath a₁))
  rw [kroneckerLineRep_map_arrowPath_self_apply, app_tgt_eq_app_src h e] at hnat
  rw [lineApp_eq]
  exact hnat.trans (kroneckerLineRep_map_arrowPath_self_apply _)

/-- The scalars of the two lines agree on the scalar of any morphism between them. -/
private theorem mul_lineScalar (h : a₀ ≠ a₁)
    (e : kroneckerLineRep k a₁ c ⟶ kroneckerLineRep k a₁ d) :
    c * lineScalar e = d * lineScalar e := by
  have h1 := lineApp_mul h e 1
  rw [mul_one, lineApp_apply, ← lineScalar_def] at h1
  exact h1

/-! ### Indecomposability and the classification -/

/-- **A line representation is indecomposable, as soon as some arrow other than the distinguished
one exists.** Its endomorphisms are recorded faithfully by their scalar in the base field, which is
a local ring, so its only idempotent endomorphisms are `0` and the identity.

The second arrow is what forces the two components of an endomorphism to agree, and it is not an
artefact: over the `A₂` quiver of a single arrow nothing relates the two components, and the line
at `c = 0` is there the direct sum of the two vertex simples. That quiver has only the three
isomorphism classes counted by `TauCeti.card_skeleton_indecomposable_kronecker`, with no room for
a family. -/
theorem indecomposable_kroneckerLineRep (h : a₀ ≠ a₁) :
    Indecomposable (kroneckerLineRep k a₁ c) :=
  indecomposable_of_injective_of_isLocalRing not_isZero_kroneckerLineRep lineScalar
    (lineScalar_injective h) lineScalar_zero lineScalar_id fun e ↦ lineScalar_comp e e

/-- **Line representations at different scalars are non-isomorphic.** An isomorphism has an
invertible scalar, and its naturality along the distinguished arrow then equates the two
scalars. -/
theorem eq_of_nonempty_kroneckerLineRep_iso (h : a₀ ≠ a₁)
    (hiso : Nonempty (kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d)) : c = d := by
  obtain ⟨e⟩ := hiso
  have hunit : lineScalar e.hom * lineScalar e.inv = 1 := by
    rw [← lineScalar_comp, e.hom_inv_id, lineScalar_id]
  exact mul_right_cancel₀ (left_ne_zero_of_mul_eq_one hunit) (mul_lineScalar h e.hom)

/-- **Two line representations are isomorphic exactly when their scalars agree.** So over an
infinite field the isomorphism classes of indecomposables at the dimension vector `(1, 1)` are
infinite in number, the affine chart of the `ℙ¹` of the Kronecker quiver. -/
theorem nonempty_kroneckerLineRep_iso_iff (h : a₀ ≠ a₁) :
    Nonempty (kroneckerLineRep k a₁ c ≅ kroneckerLineRep k a₁ d) ↔ c = d :=
  ⟨eq_of_nonempty_kroneckerLineRep_iso h, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **Outside Dynkin type the dimension vector does not determine an indecomposable.** Over every
field, a generalized Kronecker quiver with two distinct arrows carries two non-isomorphic
finite-dimensional indecomposable representations with the same dimension vector, the lines at the
scalars `0` and `1`.

This is the sharpness of `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`:
that theorem holds over an acyclic quiver whose Tits form is positive definite, and the Kronecker
quiver is acyclic with a Tits form that is only positive semidefinite. -/
theorem exists_indecomposable_dimVector_eq_not_nonempty_iso (k : Type u) [Field k] {A : Type v}
    {a₀ a₁ : A} (h : a₀ ≠ a₁) :
    ∃ M N : QuiverRep.{u, 0, v, u} k (Quiver.Kronecker A),
      IsFinDim k (Quiver.Kronecker A) M ∧ Indecomposable M ∧
        IsFinDim k (Quiver.Kronecker A) N ∧ Indecomposable N ∧
        dimVector M = dimVector N ∧ ¬ Nonempty (M ≅ N) :=
  ⟨kroneckerLineRep k a₁ 0, kroneckerLineRep k a₁ 1, isFinDim_kroneckerLineRep,
    indecomposable_kroneckerLineRep h, isFinDim_kroneckerLineRep,
    indecomposable_kroneckerLineRep h,
    funext fun w ↦ (dimVector_kroneckerLineRep w).trans (dimVector_kroneckerLineRep w).symm,
    fun hiso ↦ zero_ne_one (eq_of_nonempty_kroneckerLineRep_iso h hiso)⟩

/-- **The Tits value of the dimension vector of a line representation is `2 - #arrows`.** It is
`1` exactly for the `A₂` quiver of a single arrow, and `0` for the Kronecker quiver `• ⇉ •`.

This is the sharpness of `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`: over
an acyclic quiver whose Tits form is only positive semidefinite, the dimension vector of an
indecomposable need not be a root. -/
theorem titsForm_dimVector_kroneckerLineRep [Fintype A] :
    titsForm (Quiver.Kronecker A)
        (fun j : Quiver.Kronecker A ↦ (dimVector (kroneckerLineRep k a₁ c) j : ℤ)) =
      2 - Fintype.card A := by
  have hd : (fun j : Quiver.Kronecker A ↦ (dimVector (kroneckerLineRep k a₁ c) j : ℤ)) = 1 := by
    funext j
    rw [dimVector_kroneckerLineRep, Nat.cast_one, Pi.one_apply]
  rw [hd, Quiver.Kronecker.titsForm_apply, Pi.one_apply, Pi.one_apply]
  ring

end TauCeti
