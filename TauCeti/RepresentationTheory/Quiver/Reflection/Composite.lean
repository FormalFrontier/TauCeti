/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Admissible
public import TauCeti.RepresentationTheory.Quiver.Reflection.Coxeter
public import TauCeti.RepresentationTheory.Quiver.Reflection.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Reflection.FullyFaithful

/-!
# The Coxeter functor

Reflecting a quiver at a sink reverses the arrows there, and the Bernstein-Gelfand-Ponomarev
reflection functor `C⁺ᵢ` carries its representations to representations of the reflected quiver
(`TauCeti.reflectionFunctor`). Reflecting at the successive entries of a **sink-admissible** list
-- each entry a sink of the quiver its predecessors produce -- composes those functors, and along
a sink-admissible **ordering**, a repetition-free list of *all* the vertices, the quiver comes
back to itself (`TauCeti.Quiver.reflectList_eq_self`). The resulting endofunctor is the **Coxeter
functor** of this file, `TauCeti.coxeterFunctor`, and on dimension vectors it realizes the Coxeter
transformation `TauCeti.vertexPreReflectionList` of the ordering.

The Layer 4 identity `dim (C⁺ M) = c · dim M` is proved here for an indecomposable representation
with finite-dimensional vertex spaces, with the zero representation as its alternative. The proof
proceeds stagewise: away from the vertex simple at the current sink, reflection preserves
indecomposability and transforms the dimension vector as predicted; at that vertex simple,
reflection instead annihilates the representation (`TauCeti.isZero_reflectRep`). The corresponding
dichotomy for indecomposables is supplied by
`TauCeti.incomingSum_surjective_or_forall_subsingleton`.

## Main definitions

* `TauCeti.reflectionFunctorList`: the composite of the reflection functors along a
  sink-admissible list, from the representations of `q` to those of
  `TauCeti.Quiver.reflectList q l`.
* `TauCeti.coxeterFunctor`: the Coxeter functor `C⁺` of a sink-admissible ordering, an
  endofunctor of the representations of `q`.

## Main results

* `TauCeti.reflectionFunctorList_nil` and `TauCeti.reflectionFunctorList_cons`: the composite is
  the identity on the empty list and peels off one reflection functor at a time.
* `TauCeti.isZero_reflectionFunctorList_obj` and `TauCeti.isZero_coxeterFunctor_obj`: the zero
  representation is carried to the zero representation.
* `TauCeti.indecomposable_and_dimVector_reflectionFunctorList_or_isZero` and
  `TauCeti.indecomposable_and_dimVector_coxeterFunctor_or_isZero`: the dichotomy above, for a
  general sink-admissible list and for the Coxeter functor.
* `TauCeti.titsForm_dimVector_coxeterFunctor_obj`: the Coxeter functor preserves the Tits form of
  the dimension vector of an indecomposable representation it does not annihilate.

## Implementation notes

The quiver structure is carried as an *explicit argument* rather than as an instance, because the
recursion changes it: the vertex type is fixed and the arrows are reversed, so the recursion is on
the `Quiver` structure `TauCeti.Quiver.reflectAt`, not on a type synonym like
`TauCeti.Quiver.Reflect`, whose iteration would change the type at each step and so leave the
range of structural recursion. The existing `TauCeti.Quiver.instFintypeReflectHom` carries
arrow-finiteness along with it.

A consequence is that two `Quiver` structures on one vertex type occur in the same statement, and
the one in scope as a local instance is not always the intended one. Every statement below
therefore supplies the structure explicitly to `TauCeti.dimVector`, `TauCeti.titsForm` and
`TauCeti.vertexPreReflectionList`; vanishing is stated as `CategoryTheory.Limits.IsZero` of the
representation rather than vertexwise, since the vertexwise form would need the structure supplied
to `CategoryTheory.Functor.obj` as well.

The Coxeter functor is the composite transported along `TauCeti.Quiver.reflectList_eq_self`, an
equality of `Quiver` structures; `TauCeti.coxeterFunctor_def` exposes this characterization while
the auxiliary transport construction remains private.

The sink-admissible ordering is an argument of `TauCeti.coxeterFunctor` rather than something
chosen from `TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`: the Coxeter transformation the
functor realizes depends on the ordering, so a consumer that needs to name it must be able to name
the ordering too.

## References

This implements the “Coxeter functor” target of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, the engine of that
roadmap's Layer 5 reflection induction. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and
Gabriel's theorem*, and Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

/-! ### The composite of the reflection functors along a sink-admissible list -/

/-- **The composite of the reflection functors along a sink-admissible list.** Each entry of the
list is a sink of the quiver its predecessors produce, so the reflection functors at the
successive entries compose; the result carries the representations of `q` to those of
`TauCeti.Quiver.reflectList q l`.

The quiver structure is an explicit argument rather than an instance because it is what the
recursion moves: the vertex type stays fixed while the arrows are reversed. -/
noncomputable def reflectionFunctorList (k : Type u) {V : Type v} [fld : Field k] [fV : Fintype V] :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (_hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)),
      Quiver.IsSinkAdmissible q l →
      (@QuiverRep.{u, v, w, max v w x} k V fld q ⥤
        @QuiverRep.{u, v, w, max v w x} k V fld (Quiver.reflectList q l))
  | [], _, _, _ => 𝟭 _
  | i :: l, q, hq, hl => by
      letI := q
      letI := hq
      exact reflectionFunctor i (Quiver.isSinkAdmissible_cons.mp hl).1 ⋙
        reflectionFunctorList k l (Quiver.reflectAt q i) (@instFintypeReflectHom V q hq i)
          (Quiver.isSinkAdmissible_cons.mp hl).2

variable {k : Type u} {V : Type v} [fld : Field k] [fV : Fintype V]

@[simp]
theorem reflectionFunctorList_nil (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSinkAdmissible q []) :
    reflectionFunctorList.{u, v, w, x} k [] q hq hl = 𝟭 _ := by
  rw [reflectionFunctorList]

@[simp]
theorem reflectionFunctorList_cons (i : V) (l : List V) (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSinkAdmissible q (i :: l)) :
    reflectionFunctorList.{u, v, w, x} k (i :: l) q hq hl
      = @reflectionFunctor k V fld q fV hq i (Quiver.isSinkAdmissible_cons.mp hl).1 ⋙
        reflectionFunctorList k l (Quiver.reflectAt q i) (@instFintypeReflectHom V q hq i)
          (Quiver.isSinkAdmissible_cons.mp hl).2 := by
  rw [reflectionFunctorList]
  congr

/-- **A composite of reflections annihilates the zero representation.** Only the vanishing of the
vertex spaces is used at each stage, through `TauCeti.isZero_reflectRep`. -/
theorem isZero_reflectionFunctorList_obj :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSinkAdmissible q l) (M : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Limits.IsZero M → Limits.IsZero ((reflectionFunctorList k l q hq hl).obj M)
  | [], q, hq, hl, M, hM => by
      rw [reflectionFunctorList_nil]
      exact hM
  | i :: l, q, hq, hl, M, hM => by
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      rw [reflectionFunctorList_cons]
      refine isZero_reflectionFunctorList_obj l (Quiver.reflectAt q i)
        (@instFintypeReflectHom V q hq i) (Quiver.isSinkAdmissible_cons.mp hl).2
        ((reflectionFunctor i (Quiver.isSinkAdmissible_cons.mp hl).1).obj M) ?_
      rw [reflectionFunctor_obj]
      exact isZero_reflectRep M (Quiver.isSinkAdmissible_cons.mp hl).1 fun a _ ↦
        ModuleCat.subsingleton_of_isZero ((Functor.isZero_iff M).mp hM a)

/-! ### The action on an indecomposable representation -/

/-- **A composite of reflection functors on an indecomposable representation.** Either the
composite is again indecomposable, and then its dimension vector is the corresponding product of
simple reflections applied to the dimension vector of `M`, or the composite is the zero
representation.

The proof runs the dichotomy `TauCeti.incomingSum_surjective_or_forall_subsingleton` at each
stage: a stage meeting the vertex simple at its own sink annihilates the representation
(`TauCeti.isZero_reflectRep`), which is what lands in the second branch, while every other stage
preserves indecomposability and reflects the dimension vector. Both branches occur -- the vertex
simple at the first entry falls into the second. The simple reflections on the right are those of
the *original* quiver, by `TauCeti.vertexPreReflectionList_reflectAt`, even though the successive
stages act on successively reflected quivers. -/
theorem indecomposable_and_dimVector_reflectionFunctorList_or_isZero [DecidableEq V] :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSinkAdmissible q l) (M : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Indecomposable M → (∀ a : V, FiniteDimensional k (M.obj a)) →
      (Indecomposable ((reflectionFunctorList k l q hq hl).obj M) ∧
            (fun j : V ↦ (@dimVector k V fld (Quiver.reflectList q l)
                ((reflectionFunctorList k l q hq hl).obj M) j : ℤ))
              = @vertexPreReflectionList V q fV hq _ l fun j ↦ (@dimVector k V fld q M j : ℤ))
        ∨ Limits.IsZero ((reflectionFunctorList k l q hq hl).obj M)
  | [], q, hq, hl, M, hM, _ => by
      rw [reflectionFunctorList_nil, vertexPreReflectionList_nil]
      exact Or.inl ⟨hM, rfl⟩
  | i :: l, q, hq, hl, M, hM, hfd => by
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSinkAdmissible_cons.mp hl
      have key : (reflectionFunctorList.{u, v, w, x} k (i :: l) q hq hl).obj M
          = (reflectionFunctorList k l (Quiver.reflectAt q i)
              (@instFintypeReflectHom V q hq i) hl').obj (reflectRep M hi) := by
        rw [reflectionFunctorList_cons]
        exact congrArg _ (reflectionFunctor_obj i hi M)
      rw [key]
      rcases incomingSum_surjective_or_forall_subsingleton hi hM with hs | hsub
      · have hRdim : (fun j : V ↦
              (@dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi) j : ℤ))
            = @vertexPreReflection V q fV hq _ i fun j ↦ (@dimVector k V fld q M j : ℤ) :=
          dimVector_reflectRep M hi (fun e ↦ hfd e.1) hs
        rcases indecomposable_and_dimVector_reflectionFunctorList_or_isZero l
            (Quiver.reflectAt q i) (@instFintypeReflectHom V q hq i) hl' (reflectRep M hi)
            (indecomposable_reflectRep hi hM hs)
            (finiteDimensional_reflectRep_obj M hi hfd) with ⟨h1, h2⟩ | h
        · refine Or.inl ⟨h1, ?_⟩
          calc (fun j : V ↦ (@dimVector k V fld (Quiver.reflectList q (i :: l))
                ((reflectionFunctorList k l (Quiver.reflectAt q i)
                  (@instFintypeReflectHom V q hq i) hl').obj (reflectRep M hi)) j : ℤ))
              = @vertexPreReflectionList V (Quiver.reflectAt q i) fV
                  (@instFintypeReflectHom V q hq i) _ l
                  (fun j : V ↦
                    (@dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi) j : ℤ)) := h2
            _ = @vertexPreReflectionList V q fV hq _ l
                  (@vertexPreReflection V q fV hq _ i
                    fun j ↦ (@dimVector k V fld q M j : ℤ)) := by
                  rw [vertexPreReflectionList_reflectAt, hRdim]
            _ = @vertexPreReflectionList V q fV hq _ (i :: l)
                  fun j ↦ (@dimVector k V fld q M j : ℤ) :=
                  (vertexPreReflectionList_apply_cons V i l _).symm
        · exact Or.inr h
      · exact Or.inr (isZero_reflectionFunctorList_obj l (Quiver.reflectAt q i)
          (@instFintypeReflectHom V q hq i) hl' (reflectRep M hi)
          (isZero_reflectRep M hi hsub))

/-! ### The Coxeter functor -/

/-- A functor into the representations of the quiver structure `r`, read as a functor into the
representations of `q` along an equality `r = q`. It is only used to bring the composite of the
reflection functors along a sink-admissible *ordering* back to its own quiver, where
`TauCeti.Quiver.reflectList_eq_self` supplies the equality; the three lemmas below are its whole
interface, and each is the transport applied to a reflexive equality. -/
private noncomputable def transportCodomain {q r : _root_.Quiver.{w} V} (h : r = q)
    (F : @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld r) :
    @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld q :=
  h ▸ F

omit fV in
private theorem transportCodomain_eq_eqMp {q r : _root_.Quiver.{w} V} (h : r = q)
    (F : @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld r) :
    transportCodomain h F =
      Eq.mp (congrArg (fun s : _root_.Quiver.{w} V ↦
        @QuiverRep.{u, v, w, max v w x} k V fld q ⥤
          @QuiverRep.{u, v, w, max v w x} k V fld s) h) F := by
  subst h
  rfl

omit fV in
private theorem indecomposable_transportCodomain_obj {q r : _root_.Quiver.{w} V} (h : r = q)
    (F : @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld r)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    Indecomposable ((transportCodomain h F).obj M) ↔ Indecomposable (F.obj M) := by
  subst h
  exact Iff.rfl

omit fV in
private theorem isZero_transportCodomain_obj {q r : _root_.Quiver.{w} V} (h : r = q)
    (F : @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld r)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    Limits.IsZero ((transportCodomain h F).obj M) ↔ Limits.IsZero (F.obj M) := by
  subst h
  exact Iff.rfl

omit fV in
private theorem dimVector_transportCodomain_obj {q r : _root_.Quiver.{w} V} (h : r = q)
    (F : @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld r)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    @dimVector k V fld q ((transportCodomain h F).obj M) = @dimVector k V fld r (F.obj M) := by
  subst h
  rfl

/-- **The Coxeter functor** `C⁺`: the composite of the Bernstein-Gelfand-Ponomarev reflection
functors at the successive vertices of a sink-admissible *ordering* of the vertices -- a
sink-admissible list that repeats no vertex and contains every one of them. Reflecting once at
every vertex restores the quiver structure (`TauCeti.Quiver.reflectList_eq_self`), so unlike a
general composite of reflection functors this is an *endo*functor of the representations of `q`.

Every finite acyclic quiver has such an ordering, by
`TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`; the ordering is an argument rather than a
choice, since the Coxeter transformation it realizes on dimension vectors,
`TauCeti.vertexPreReflectionList`, depends on it. -/
noncomputable def coxeterFunctor (k : Type u) {V : Type v} [fld : Field k] [fV : Fintype V]
    (q : _root_.Quiver.{w} V) (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l)
    (hl : Quiver.IsSinkAdmissible q l) :
    @QuiverRep.{u, v, w, max v w x} k V fld q ⥤ @QuiverRep.{u, v, w, max v w x} k V fld q :=
  transportCodomain (Quiver.reflectList_eq_self q hnd hall) (reflectionFunctorList k l q hq hl)

/-- The Coxeter functor is the reflection-functor composite transported along the equality between
the iteratively reflected quiver and the original quiver. -/
theorem coxeterFunctor_def (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l) :
    coxeterFunctor.{u, v, w, x} k q hq hnd hall hl =
      Eq.mp (congrArg (fun r : _root_.Quiver.{w} V ↦
        @QuiverRep.{u, v, w, max v w x} k V fld q ⥤
          @QuiverRep.{u, v, w, max v w x} k V fld r)
        (Quiver.reflectList_eq_self q hnd hall)) (reflectionFunctorList k l q hq hl) :=
  transportCodomain_eq_eqMp (Quiver.reflectList_eq_self q hnd hall)
    (reflectionFunctorList k l q hq hl)

/-- Transporting the reflection-functor composite back to the original quiver does not change its
dimension vector. -/
theorem dimVector_coxeterFunctor_obj (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    @dimVector k V fld q ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) =
      @dimVector k V fld (Quiver.reflectList q l)
        ((reflectionFunctorList k l q hq hl).obj M) :=
  dimVector_transportCodomain_obj _ _ M

/-- Transporting the reflection-functor composite back to the original quiver does not change its
dimension vector after coercion to integers. -/
theorem intCast_dimVector_coxeterFunctor_obj (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    (fun j : V ↦
        (@dimVector k V fld q ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) j : ℤ))
      = fun j : V ↦ (@dimVector k V fld (Quiver.reflectList q l)
          ((reflectionFunctorList k l q hq hl).obj M) j : ℤ) :=
  congrArg (fun c : V → ℕ ↦ fun j : V ↦ (c j : ℤ))
    (dimVector_coxeterFunctor_obj q hq hnd hall hl M)

/-- **The Coxeter functor annihilates the zero representation.** -/
theorem isZero_coxeterFunctor_obj (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) (hM : Limits.IsZero M) :
    Limits.IsZero ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) :=
  (isZero_transportCodomain_obj _ _ M).mpr (isZero_reflectionFunctorList_obj l q hq hl M hM)

/-- **The Coxeter functor on an indecomposable representation.** Either it is again
indecomposable, with dimension vector the Coxeter transformation
`TauCeti.vertexPreReflectionList` of the ordering applied to the dimension vector of `M`, or it is
the zero representation. The proof applies the reflection dichotomy successively, with a vertex
simple at the current sink providing the annihilated case. This is the Layer 4 statement
`dim (C⁺ M) = c · dim M` for the Coxeter element `c`, with the boundary case named. -/
theorem indecomposable_and_dimVector_coxeterFunctor_or_isZero [DecidableEq V]
    (q : _root_.Quiver.{w} V) (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) (hM : Indecomposable M)
    (hfd : ∀ a : V, FiniteDimensional k (M.obj a)) :
    (Indecomposable ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) ∧
          (fun j : V ↦
              (@dimVector k V fld q ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) j : ℤ))
            = @vertexPreReflectionList V q fV hq _ l fun j ↦ (@dimVector k V fld q M j : ℤ))
      ∨ Limits.IsZero ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) := by
  rcases indecomposable_and_dimVector_reflectionFunctorList_or_isZero l q hq hl M hM hfd with
    ⟨h1, h2⟩ | h
  · refine Or.inl ⟨(indecomposable_transportCodomain_obj _ _ M).mpr h1, ?_⟩
    rw [intCast_dimVector_coxeterFunctor_obj]
    exact h2
  · exact Or.inr ((isZero_transportCodomain_obj _ _ M).mpr h)

/-- **The Coxeter functor preserves the Tits form of the dimension vector.** The Tits form is
unchanged by a simple reflection at a loopless vertex, hence by the whole Coxeter transformation
(`TauCeti.titsForm_vertexPreReflectionList`), and no vertex of a repetition-free sink-admissible
list carries a loop (`TauCeti.Quiver.IsSinkAdmissible.isEmpty_hom_self`). So on an indecomposable
representation the Coxeter functor either annihilates it or leaves the Tits form of its dimension
vector alone. This preserved invariant is used by the Layer 5 reflection induction, whose descent
measure is root height. -/
theorem titsForm_dimVector_coxeterFunctor_obj (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) (hM : Indecomposable M)
    (hfd : ∀ a : V, FiniteDimensional k (M.obj a))
    (hne : ¬ Limits.IsZero ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M)) :
    @titsForm V q fV hq (fun j : V ↦
        (@dimVector k V fld q ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) j : ℤ))
      = @titsForm V q fV hq fun j : V ↦ (@dimVector k V fld q M j : ℤ) := by
  classical
  rcases indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl M hM hfd with
    ⟨-, h2⟩ | h
  · rw [h2]
    exact @titsForm_vertexPreReflectionList V q fV hq _ l
      (fun i hi ↦ hl.isEmpty_hom_self hnd hi) _
  · exact absurd h hne

end TauCeti
