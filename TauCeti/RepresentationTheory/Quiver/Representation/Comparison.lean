/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Injective
public import TauCeti.RepresentationTheory.Quiver.Representation.Simple

/-!
# Comparing a vertex simple with its projective and its injective

For a vertex `i` of a quiver `Q` there are three representations attached to `i`: the vertex
simple `Sᵢ`, the projective `Pᵢ` and the injective `Iᵢ`. This file builds the two comparison
morphisms that tie them together, `Pᵢ ↠ Sᵢ` and `Sᵢ ↪ Iᵢ`, and proves that the first is an
epimorphism, the second a monomorphism, and that each is unique up to a scalar.

Both morphisms come from universal properties already available: `Pᵢ` represents evaluation at `i`
(`TauCeti.indecProjRepHomEquiv`) and `Iᵢ` represents the dual of evaluation at `i`
(`TauCeti.indecInjRepHomEquiv`), so a morphism `Pᵢ ⟶ Sᵢ` is an element of the line `(Sᵢ)ᵢ` and a
morphism `Sᵢ ⟶ Iᵢ` is a linear functional on it. The two canonical choices are the generator of
that line and the functional dual to it, and both are read off the identification
`TauCeti.simpleRepSelfEquiv` of `(Sᵢ)ᵢ` with the base field.

## Main definitions

* `TauCeti.indecProjRepToSimpleRep`: the morphism `Pᵢ ⟶ Sᵢ`, sending the trivial path to the
  generator and killing every path of positive length.
* `TauCeti.simpleRepToIndecInjRep`: the morphism `Sᵢ ⟶ Iᵢ`, reading off the coefficient of an
  element of `(Sᵢ)ᵢ` on the trivial path.

## Main results

* `TauCeti.epi_indecProjRepToSimpleRep`: `Pᵢ ↠ Sᵢ` is an epimorphism, and
  `TauCeti.mono_simpleRepToIndecInjRep`: `Sᵢ ↪ Iᵢ` is a monomorphism.
* `TauCeti.exists_smul_indecProjRepToSimpleRep` and
  `TauCeti.exists_smul_simpleRepToIndecInjRep`: every morphism `Pᵢ ⟶ Sᵢ`, respectively
  `Sᵢ ⟶ Iᵢ`, is a scalar multiple of the canonical one, so each comparison morphism is unique up
  to a scalar.

## Implementation notes

Only the two comparison morphisms and their formal properties are proved here. That `Pᵢ ↠ Sᵢ` is a
*projective cover* in the technical sense (a superfluous kernel) and `Sᵢ ↪ Iᵢ` an *injective
envelope* (an essential extension) is neither proved nor true in this generality: for the quiver
with one vertex and one loop the path algebra is `k[X]`, the kernel of `Pᵢ ↠ Sᵢ` is the ideal
`(X)`, and `(X) + (X - 1) = k[X]` with `(X - 1)` proper, so that kernel is not superfluous. What is
recorded instead is `TauCeti.indecProjRepToSimpleRep_app_basis_of_length_ne_zero`: the morphism
kills the basis vector of every path of positive length, so its kernel contains the arrow ideal.
That ideal is the Jacobson radical when it is nilpotent, for instance for a finite acyclic quiver,
but not in general: for the one-loop quiver the radical of `k[X]` is zero. Identifying the kernel
with the radical, and with it the technical statements, is left to the Layer 3 theory of covers and
envelopes, which is not yet available.

The field, the vertex type and the arrow types share one universe here, where the three files
building `Sᵢ`, `Pᵢ` and `Iᵢ` each keep them separate. The reason is that the vertex spaces of `Pᵢ`
and `Iᵢ` are built on `Quiver.Path i j`, so they live in the universe `max u v w` of the field, the
vertices and the arrows, whereas `Sᵢ` is built on the field itself and lives in the universe `u` of
the field alone. The three objects therefore lie in a common category `TauCeti.QuiverRep k Q`
exactly when `v, w ≤ u`, and `u = v = w` is the strongest such alignment Lean can state, there
being no way to hypothesize a universe inequality. Writing the alignment as `k : Type (max u v w)`
with `Q : Type v` and `Quiver.{w} Q` is not an option, tempting as it looks: a declaration whose
signature mentions `u`, `v` and `w` only inside that one `max` cannot be applied afterwards, since
every use asks Lean to solve `max ?a ?b ?c =?= max u v w`, which has no unique solution and is
reported as `stuck at solving universe constraint`; Lean's own `linter.checkUnivs` flags the
signature for exactly this reason. Lifting the restriction would instead mean rebuilding `Sᵢ` on a
`ULift` of the field, which would re-index every existing statement about it; `Sᵢ`, `Pᵢ` and `Iᵢ`
themselves are constructed with no relation between the universes, and only the statements
*comparing* them are restricted here.

A vertex `i : Q` is used below as an object of the free category `CategoryTheory.Paths Q`, which is
`Q` itself only by unfolding a semireducible definition; the `(Paths.of Q).obj` annotations record
that identification, exactly as in the files this one builds on.

## References

This implements the comparison morphisms `Pᵢ ↠ Sᵢ` and `Sᵢ ↪ Iᵢ` of Layer 1 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. III.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) {Q : Type u} [Field k] [Quiver.{u} Q]

/-! ### The surjection from a vertex projective onto its vertex simple -/

/-- **The canonical surjection `Pᵢ ↠ Sᵢ`**: under the universal property of `Pᵢ` it is the
generator of the line `(Sᵢ)ᵢ`. It sends the basis vector of the trivial path to that generator and
kills the basis vector of every path of positive length. -/
noncomputable def indecProjRepToSimpleRep (i : Q) : indecProjRep k Q i ⟶ simpleRep k Q i :=
  indecProjRepHom i (simpleRep k Q i) (simpleRepGenerator k i)

/-- The surjection `Pᵢ ↠ Sᵢ` carries the basis vector of a path `p : i → j` to the action of `p` on
the generator. -/
@[simp]
theorem indecProjRepToSimpleRep_app_basis {i j : Q} (p : Quiver.Path i j) :
    (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj j) (indecProjRepBasis k i j p)
      = (simpleRep k Q i).map p (simpleRepGenerator k i) :=
  indecProjRepHom_app_basis i (simpleRep k Q i) (simpleRepGenerator k i) j p

/-- The surjection `Pᵢ ↠ Sᵢ` sends the basis vector of the trivial path to the generator of
`(Sᵢ)ᵢ`. -/
theorem indecProjRepToSimpleRep_app_nil (i : Q) :
    (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj i)
        (indecProjRepBasis k i i Quiver.Path.nil) = simpleRepGenerator k i :=
  indecProjRepHom_app_nil i (simpleRep k Q i) (simpleRepGenerator k i)

-- Not `@[simp]`: `simp` reduces the left-hand side through `indecProjRepHomEquiv_apply` and
-- `indecProjRepToSimpleRep_app_basis`, so tagging the theorem is a simp-normal-form violation
-- (`simpNF`). It stays named because it is the universal-property reading of the surjection.
/-- The surjection `Pᵢ ↠ Sᵢ` is the morphism that the universal property of `Pᵢ` attaches to the
generator of the line `(Sᵢ)ᵢ`. -/
theorem indecProjRepHomEquiv_indecProjRepToSimpleRep (i : Q) :
    indecProjRepHomEquiv i (simpleRep k Q i) (indecProjRepToSimpleRep k i)
      = simpleRepGenerator k i := by
  rw [indecProjRepHomEquiv_apply, indecProjRepToSimpleRep_app_nil]

-- Not `@[simp]` either, for the same reason: its left-hand side is the left-hand side of the
-- `@[simp]` lemma `indecProjRepToSimpleRep_app_basis` above, so `simp` rewrites it before this
-- lemma could fire and `simpNF` reports "Left-hand side simplifies ... using
-- simp only [*, TauCeti.indecProjRepToSimpleRep_app_basis]". The `simp` form of this statement is
-- `simpleRep_map_eq_zero_of_length_ne_zero`, which the proof below is exactly the composite with.
/-- **The surjection `Pᵢ ↠ Sᵢ` kills the arrow ideal**: the basis vector of a path of positive
length goes to zero. -/
theorem indecProjRepToSimpleRep_app_basis_of_length_ne_zero {i j : Q} (p : Quiver.Path i j)
    (hp : p.length ≠ 0) :
    (indecProjRepToSimpleRep k i).app ((Paths.of Q).obj j) (indecProjRepBasis k i j p) = 0 := by
  rw [indecProjRepToSimpleRep_app_basis, simpleRep_map_eq_zero_of_length_ne_zero i p hp]
  rfl

/-- Every component of `Pᵢ ⟶ Sᵢ` is surjective: at `i` because the generator spans, and away from
`i` because the target vanishes. -/
theorem indecProjRepToSimpleRep_app_surjective (i j : Q) :
    Function.Surjective ((indecProjRepToSimpleRep k i).app ((Paths.of Q).obj j)) := by
  rcases eq_or_ne j i with rfl | hj
  · intro y
    obtain ⟨c, rfl⟩ := exists_smul_simpleRepGenerator k y
    refine ⟨c • indecProjRepBasis k j j Quiver.Path.nil, ?_⟩
    -- Stated as a `have`: the component is a `ModuleCat` morphism read through
    -- `ConcreteCategory.hom`, which `rw [map_smul]` cannot see past.
    have hsmul : (indecProjRepToSimpleRep k j).app ((Paths.of Q).obj j)
          (c • indecProjRepBasis k j j Quiver.Path.nil)
        = c • (indecProjRepToSimpleRep k j).app ((Paths.of Q).obj j)
          (indecProjRepBasis k j j Quiver.Path.nil) :=
      map_smul _ c _
    rw [hsmul, indecProjRepToSimpleRep_app_nil]
  · have : Subsingleton ((simpleRep k Q i).obj ((Paths.of Q).obj j)) :=
      ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj (Q := Q) hj)
    exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩

/-- **`Pᵢ ↠ Sᵢ` is an epimorphism.** Epimorphisms of representations are detected vertexwise, and
each component is surjective. -/
instance epi_indecProjRepToSimpleRep (i : Q) : Epi (indecProjRepToSimpleRep k i) := by
  haveI : ∀ X : Paths Q, Epi ((indecProjRepToSimpleRep k i).app X) := by
    intro X
    change Q at X
    exact (ModuleCat.epi_iff_surjective _).mpr (indecProjRepToSimpleRep_app_surjective k i X)
  exact NatTrans.epi_of_epi_app _

/-- The surjection `Pᵢ ↠ Sᵢ` is nonzero. -/
theorem indecProjRepToSimpleRep_ne_zero (i : Q) : indecProjRepToSimpleRep k i ≠ 0 := by
  intro h
  refine simpleRepGenerator_ne_zero k i ?_
  rw [← indecProjRepHomEquiv_indecProjRepToSimpleRep k i, h, map_zero]

/-- **The surjection `Pᵢ ↠ Sᵢ` is unique up to a scalar**: `Hom(Pᵢ, Sᵢ)` is the line spanned by
`TauCeti.indecProjRepToSimpleRep`. -/
theorem exists_smul_indecProjRepToSimpleRep {i : Q} (f : indecProjRep k Q i ⟶ simpleRep k Q i) :
    ∃ c : k, f = c • indecProjRepToSimpleRep k i := by
  obtain ⟨c, hc⟩ := exists_smul_simpleRepGenerator k (indecProjRepHomEquiv i (simpleRep k Q i) f)
  refine ⟨c, (indecProjRepHomEquiv i (simpleRep k Q i)).injective ?_⟩
  rw [map_smul, indecProjRepHomEquiv_indecProjRepToSimpleRep, hc]

/-! ### The embedding of a vertex simple into its vertex injective -/

/-- **The canonical embedding `Sᵢ ↪ Iᵢ`**: under the universal property of `Iᵢ` it is the linear
functional identifying the line `(Sᵢ)ᵢ` with the base field. -/
noncomputable def simpleRepToIndecInjRep (i : Q) : simpleRep k Q i ⟶ indecInjRep k Q i :=
  indecInjRepHom i (simpleRep k Q i) (simpleRepSelfEquiv k i).toLinearMap

/-- The embedding `Sᵢ ↪ Iᵢ` sends `x` at the vertex `j` to the function whose value on a path
`q : j → i` is the coefficient of the action of `q` on `x`. -/
@[simp]
theorem simpleRepToIndecInjRep_app_apply {i j : Q}
    (x : (simpleRep k Q i).obj ((Paths.of Q).obj j)) (q : Quiver.Path j i) :
    (simpleRepToIndecInjRep k i).app ((Paths.of Q).obj j) x q
      = simpleRepSelfEquiv k i ((simpleRep k Q i).map q x) :=
  indecInjRepHom_app_apply i (simpleRep k Q i) (simpleRepSelfEquiv k i).toLinearMap j x q

/-- The embedding `Sᵢ ↪ Iᵢ` is the morphism that the universal property of `Iᵢ` attaches to the
functional identifying the line `(Sᵢ)ᵢ` with the base field. -/
@[simp]
theorem indecInjRepHomEquiv_simpleRepToIndecInjRep (i : Q) :
    indecInjRepHomEquiv i (simpleRep k Q i) (simpleRepToIndecInjRep k i)
      = (simpleRepSelfEquiv k i).toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  rw [indecInjRepHomEquiv_apply]
  exact (simpleRepToIndecInjRep_app_apply k x Quiver.Path.nil).trans
    (congrArg _ (QuiverRep.map_nil_apply (simpleRep k Q i) i x))

/-- Every component of `Sᵢ ⟶ Iᵢ` is injective: at `i` because the coefficient on the trivial path
recovers the element, and away from `i` because the source vanishes. -/
theorem simpleRepToIndecInjRep_app_injective (i j : Q) :
    Function.Injective ((simpleRepToIndecInjRep k i).app ((Paths.of Q).obj j)) := by
  rcases eq_or_ne j i with rfl | hj
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    have hnil : (simpleRepToIndecInjRep k j).app ((Paths.of Q).obj j) x Quiver.Path.nil = 0 := by
      rw [hx]
      rfl
    have hval : simpleRepSelfEquiv k j x = 0 :=
      (congrArg (simpleRepSelfEquiv k j)
          (QuiverRep.map_nil_apply (simpleRep k Q j) j x)).symm.trans
        ((simpleRepToIndecInjRep_app_apply k x Quiver.Path.nil).symm.trans hnil)
    exact (simpleRepSelfEquiv k j).map_eq_zero_iff.mp hval
  · have : Subsingleton ((simpleRep k Q i).obj ((Paths.of Q).obj j)) :=
      ModuleCat.subsingleton_of_isZero (isZero_simpleRep_obj (Q := Q) hj)
    exact fun x y _ ↦ Subsingleton.elim x y

/-- **`Sᵢ ↪ Iᵢ` is a monomorphism.** Monomorphisms of representations are detected vertexwise, and
each component is injective. -/
instance mono_simpleRepToIndecInjRep (i : Q) : Mono (simpleRepToIndecInjRep k i) := by
  haveI : ∀ X : Paths Q, Mono ((simpleRepToIndecInjRep k i).app X) := by
    intro X
    change Q at X
    exact (ModuleCat.mono_iff_injective _).mpr (simpleRepToIndecInjRep_app_injective k i X)
  exact NatTrans.mono_of_mono_app _

/-- The embedding `Sᵢ ↪ Iᵢ` is nonzero. -/
theorem simpleRepToIndecInjRep_ne_zero (i : Q) : simpleRepToIndecInjRep k i ≠ 0 := by
  intro h
  have hzero : (simpleRepSelfEquiv k i).toLinearMap = 0 := by
    rw [← indecInjRepHomEquiv_simpleRepToIndecInjRep k i, h, map_zero]
  have h1 := congrArg (fun φ : Module.Dual k _ ↦ φ (simpleRepGenerator k i)) hzero
  simp only [LinearEquiv.coe_coe, simpleRepSelfEquiv_apply_generator, LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-- **The embedding `Sᵢ ↪ Iᵢ` is unique up to a scalar**: `Hom(Sᵢ, Iᵢ)` is the line spanned by
`TauCeti.simpleRepToIndecInjRep`. -/
theorem exists_smul_simpleRepToIndecInjRep {i : Q} (f : simpleRep k Q i ⟶ indecInjRep k Q i) :
    ∃ c : k, f = c • simpleRepToIndecInjRep k i := by
  refine ⟨indecInjRepHomEquiv i (simpleRep k Q i) f (simpleRepGenerator k i),
    (indecInjRepHomEquiv i (simpleRep k Q i)).injective ?_⟩
  rw [map_smul, indecInjRepHomEquiv_simpleRepToIndecInjRep]
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨c, rfl⟩ := exists_smul_simpleRepGenerator k x
  simp [smul_eq_mul, mul_comm]

end TauCeti
