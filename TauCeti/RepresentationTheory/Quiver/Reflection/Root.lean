/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Composite
public import TauCeti.RepresentationTheory.Quiver.Reflection.Descent

/-!
# The dimension vector of an indecomposable representation is a root

Let `Q` be a finite quiver whose Tits form is positive definite, the numerical side of the ADE
condition in Gabriel's theorem, and fix a sink-admissible ordering of its vertices. This file
proves that every finite-dimensional indecomposable representation `M` of `Q` satisfies
`q(dim M) = 1`, so that its dimension vector is a root of the Tits form
(`TauCeti.titsForm_dimVector_eq_one_of_indecomposable`).

This is the half of the Gabriel correspondence saying that the dimension vector of an
indecomposable *is* a positive root: `dim M` is nonnegative by construction and nonzero by
`TauCeti.dimVector_ne_zero_of_indecomposable`, and the theorem below supplies `q(dim M) = 1`.

## The argument

The Bernstein-Gelfand-Ponomarev induction runs the Coxeter functor `C⁺` at `M`. A pass either
carries an indecomposable to an indecomposable and applies the Coxeter transformation to its
dimension vector, or annihilates it
(`TauCeti.indecomposable_and_dimVector_coxeterFunctor_or_isZero`). Dimension vectors are
nonnegative, and `TauCeti.exists_vertexPreReflectionList_pow_apply_neg` forbids a nonzero
nonnegative vector from surviving every iterate of the Coxeter transformation, so some pass must
annihilate `M`: this is `TauCeti.exists_isZero_coxeterFunctor_iterate`, that every
finite-dimensional indecomposable is killed by a power of `C⁺`.

The Tits form is unchanged by each pass, so it suffices to compute it at the last surviving
representation, that is, at an indecomposable the Coxeter functor annihilates. Such a
representation is caught by a single stage of the pass, and
`TauCeti.titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList` reads the answer off there:
the stage that annihilates finds the representation concentrated at its own sink `i`, hence a line
there, so its dimension vector is the simple `αᵢ`, of Tits norm `1`; every earlier stage only
applies a simple reflection, which preserves the Tits form, as does the reflection of the quiver
itself.

## Main results

* `TauCeti.titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList`: a finite-dimensional
  indecomposable representation annihilated by a composite of reflection functors has a dimension
  vector of Tits norm one.
* `TauCeti.exists_isZero_coxeterFunctor_iterate`: a positive definite Tits form forces a power of
  the Coxeter functor to annihilate every finite-dimensional indecomposable representation.
* `TauCeti.titsForm_dimVector_eq_one_of_indecomposable`: **the dimension vector of a
  finite-dimensional indecomposable representation is a root of the Tits form**, with
  `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic` the same statement over an
  acyclic quiver, where the ordering is chosen internally and so does not appear.

## Implementation notes

As in `TauCeti.coxeterFunctor` and `TauCeti.exists_vertexPreReflectionList_pow_apply_neg`, the
sink-admissible ordering is an explicit argument rather than a chosen one: the Coxeter functor and
the transformation it realizes both depend on the ordering. Every finite acyclic quiver has one,
by `TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`.

For the indecomposable *projectives* over an acyclic quiver the same Tits value is computed
directly, and without positive definiteness, by
`TauCeti.titsForm_dimVector_indecProjRep_of_isAcyclic`; the theorems here reach every
indecomposable, at the price of that hypothesis.

## References

This is the "descent by height" step of the reflection induction in Layer 5, Gabriel's theorem, of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`: it supplies the map to
positive roots that the layer's `gabriel_indecomposable_equiv_posRoot` target is built from. See
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
VII.5.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {V : Type v} [fld : Field k] [fV : Fintype V]

/-! ### The stage that annihilates an indecomposable representation -/

/-- **A finite-dimensional indecomposable representation annihilated by a composite of reflection
functors has a dimension vector of Tits norm one.**

The induction is on the list of sinks. A stage that does not meet the vertex simple at its own
sink preserves indecomposability and reflects the dimension vector, and neither reflecting the
quiver (`TauCeti.titsForm_reflect`) nor reflecting the dimension vector
(`TauCeti.titsForm_vertexPreReflection`) changes the Tits form. The stage that does meet it finds
the representation concentrated at that sink, hence a line there
(`TauCeti.exists_ne_zero_span_eq_top_of_forall_subsingleton`), so its dimension vector is the
simple `αᵢ`, whose Tits norm is one because a sink carries no loop. -/
theorem titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSinkAdmissible q l) (M : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Indecomposable M → @IsFinDim.{u, v, w, max v w x} k V fld q M →
      Limits.IsZero ((reflectionFunctorList k l q hq hl).obj M) →
      @titsForm V q fV hq (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) = 1
  | [], q, hq, hl, M, hM, _, hz => by
      rw [reflectionFunctorList_nil] at hz
      exact absurd hz hM.1
  | i :: l, q, hq, hl, M, hM, hfd, hz => by
      classical
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSinkAdmissible_cons.mp hl
      have hfd' : ∀ a : V, FiniteDimensional k (M.obj a) :=
        (@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd
      have key : (reflectionFunctorList.{u, v, w, x} k (i :: l) q hq hl).obj M
          = (reflectionFunctorList k l (Quiver.reflectAt q i)
              (@instFintypeReflectHom V q hq i) hl').obj (reflectRep M hi) :=
        reflectionFunctorList_cons_obj i l q hq hl M
      rw [key] at hz
      rcases incomingSum_surjective_or_forall_subsingleton hi hM with hs | hsub
      · -- The stage reflects: indecomposability and the dimension vector are transported.
        have hRdim : (fun j : V ↦
              (@dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi) j : ℤ))
            = @vertexPreReflection V q fV hq _ i fun j : V ↦ (@dimVector k V fld q M j : ℤ) :=
          dimVector_reflectRep M hi (fun e ↦ hfd' e.1) hs
        have ih := titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList l
          (Quiver.reflectAt q i) (@instFintypeReflectHom V q hq i) hl' (reflectRep M hi)
          (indecomposable_reflectRep hi hM hs)
          ((@isFinDim_iff.{u, v, w, max v w x} k V fld (Quiver.reflectAt q i) _).mpr
            (finiteDimensional_reflectRep_obj M hi hfd')) hz
        calc @titsForm V q fV hq (fun j : V ↦ (@dimVector k V fld q M j : ℤ))
            = @titsForm V q fV hq (@vertexPreReflection V q fV hq _ i
                fun j : V ↦ (@dimVector k V fld q M j : ℤ)) :=
              (@titsForm_vertexPreReflection V q fV hq _ i hi.isEmpty_hom_self _).symm
          _ = @titsForm V q fV hq (fun j : V ↦
                (@dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi) j : ℤ)) := by
              rw [hRdim]
          _ = @titsForm V (Quiver.reflectAt q i) fV (@instFintypeReflectHom V q hq i)
                (fun j : V ↦
                  (@dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi) j : ℤ)) :=
              (titsForm_reflect (V := V) i _).symm
          _ = 1 := ih
      · -- The stage annihilates: the representation is the vertex simple at the sink.
        obtain ⟨y, hy, hspan⟩ := exists_ne_zero_span_eq_top_of_forall_subsingleton hi hM hsub
        have hone : @dimVector k V fld q M i = 1 := by
          rw [dimVector_apply]
          exact (finrank_eq_one_iff_of_nonzero (K := k) y hy).mpr hspan
        have hzero : ∀ j : V, j ≠ i → @dimVector k V fld q M j = 0 := by
          intro j hj
          let : Subsingleton (M.obj ((Paths.of V).obj j)) := hsub j hj
          rw [dimVector_apply]
          exact Module.finrank_zero_of_subsingleton (R := k)
        have hd : (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) = Pi.single i 1 := by
          funext j
          rcases eq_or_ne j i with rfl | hj
          · rw [Pi.single_eq_same, hone, Nat.cast_one]
          · rw [Pi.single_eq_of_ne hj, hzero j hj, Nat.cast_zero]
        rw [hd]
        exact @titsForm_single_of_isEmpty V q fV hq _ i hi.isEmpty_hom_self

/-! ### Every indecomposable representation is annihilated by a power of the Coxeter functor -/

/-- **A power of the Coxeter functor annihilates every finite-dimensional indecomposable
representation** of a quiver with positive definite Tits form.

Were the iterates all nonzero they would all be indecomposable, with dimension vectors the
successive Coxeter transforms of `dim M`; those are nonnegative, which
`TauCeti.exists_vertexPreReflectionList_pow_apply_neg` forbids for a nonzero vector. -/
theorem exists_isZero_coxeterFunctor_iterate (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (hpd : (@titsForm V q fV hq).PosDef) (M : @QuiverRep.{u, v, w, max v w x} k V fld q)
    (hM : Indecomposable M) (hfd : @IsFinDim.{u, v, w, max v w x} k V fld q M) :
    ∃ N : ℕ,
      Limits.IsZero (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M) := by
  classical
  by_contra hcon
  push Not at hcon
  -- Every iterate is again an indecomposable whose dimension vector tracks the transformation.
  have key : ∀ N : ℕ,
      Indecomposable (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M) ∧
        @IsFinDim.{u, v, w, max v w x} k V fld q
          (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M) ∧
        (fun j : V ↦ (@dimVector k V fld q
            (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M) j : ℤ))
          = ((@vertexPreReflectionList V q fV hq _ l) ^ N)
              fun j : V ↦ (@dimVector k V fld q M j : ℤ) := by
    intro N
    induction N with
    | zero => exact ⟨hM, hfd, by simp⟩
    | succ N ih =>
      obtain ⟨hind, hfin, hdim⟩ := ih
      rw [Function.iterate_succ_apply']
      have hne : ¬ Limits.IsZero ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj
          (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M)) :=
        Function.iterate_succ_apply' ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj) N M ▸
          hcon (N + 1)
      obtain ⟨h1, h2⟩ :=
        (indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl _ hind
          ((@isFinDim_iff.{u, v, w, max v w x} k V fld q _).mp hfin)).resolve_right hne
      refine ⟨h1, isFinDim_coxeterFunctor_obj q hq hnd hall hl _ hfin, ?_⟩
      rw [h2, hdim, pow_succ', Module.End.mul_apply]
  -- A dimension vector is nonnegative, and it is nonzero because `M` is not the zero object.
  have hnn : ∀ (N : ℕ) (i : V),
      0 ≤ ((@vertexPreReflectionList V q fV hq _ l) ^ N)
        (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) i := by
    intro N i
    rw [← (key N).2.2]
    exact Int.natCast_nonneg _
  have hd0 : (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) ≠ 0 := by
    intro h0
    refine @dimVector_ne_zero_of_indecomposable k V fld q M
      ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd) hM (funext fun j ↦ ?_)
    simpa using congrFun h0 j
  obtain ⟨N, i, hNi⟩ :=
    @exists_vertexPreReflectionList_pow_apply_neg V q fV hq _ hpd l hnd hall _ hd0
  exact absurd (hnn N i) (not_le.mpr hNi)

/-! ### The dimension vector of an indecomposable is a root -/

/-- The Tits form is unchanged by a pass of the Coxeter functor that does not annihilate the
representation (`TauCeti.titsForm_dimVector_coxeterFunctor_obj`), so it may be computed at the last
surviving representation, which `TauCeti.titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList`
reads off. -/
private theorem titsForm_dimVector_eq_one_of_isZero_iterate (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l) :
    ∀ (N : ℕ) (M : @QuiverRep.{u, v, w, max v w x} k V fld q), Indecomposable M →
      @IsFinDim.{u, v, w, max v w x} k V fld q M →
      Limits.IsZero (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[N] M) →
      @titsForm V q fV hq (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) = 1 := by
  classical
  intro N
  induction N with
  | zero =>
    intro M hM _ hz
    rw [Function.iterate_zero_apply] at hz
    exact absurd hz hM.1
  | succ N ih =>
    intro M hM hfd hz
    rw [Function.iterate_succ_apply] at hz
    rcases indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl M hM
        ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd) with ⟨h1, -⟩ | h0
    · have hstep := ih ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M) h1
        (isFinDim_coxeterFunctor_obj q hq hnd hall hl M hfd) hz
      exact (titsForm_dimVector_coxeterFunctor_obj q hq hnd hall hl M hM
        ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd) h1.1).symm.trans hstep
    · exact titsForm_dimVector_eq_one_of_isZero_reflectionFunctorList l q hq hl M hM hfd
        ((isZero_coxeterFunctor_obj_iff_isZero_reflectionFunctorList_obj
          q hq hnd hall hl M).mp h0)

/-- **The dimension vector of a finite-dimensional indecomposable representation is a root of the
Tits form.** For a quiver with positive definite Tits form -- the numerical form of the ADE
condition -- and any sink-admissible ordering of its vertices, an indecomposable representation
with finite-dimensional vertex spaces has `q(dim M) = 1`. Since a dimension vector is nonnegative,
and is nonzero because an indecomposable is not the zero object, `dim M` is a *positive* root.

This is the half of Gabriel's correspondence that produces a positive root from an
indecomposable; the nonvanishing half is `TauCeti.dimVector_ne_zero_of_indecomposable`. -/
theorem titsForm_dimVector_eq_one_of_indecomposable (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (hpd : (@titsForm V q fV hq).PosDef) (M : @QuiverRep.{u, v, w, max v w x} k V fld q)
    (hM : Indecomposable M) (hfd : @IsFinDim.{u, v, w, max v w x} k V fld q M) :
    @titsForm V q fV hq (fun j : V ↦ (@dimVector k V fld q M j : ℤ)) = 1 := by
  obtain ⟨N, hN⟩ := exists_isZero_coxeterFunctor_iterate q hq hnd hall hl hpd M hM hfd
  exact titsForm_dimVector_eq_one_of_isZero_iterate q hq hnd hall hl N M hM hfd hN

/-- **The dimension vector of a finite-dimensional indecomposable representation of an acyclic
quiver with positive definite Tits form is a root.** This is the consumer-facing form of
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable`: acyclicity produces a sink-admissible
ordering by `TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`, and since the conclusion does not
mention the ordering, the choice is made here rather than by the caller. -/
theorem titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic [q : _root_.Quiver.{w} V]
    [hq : ∀ a b : V, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic V) (hpd : (titsForm V).PosDef)
    (M : QuiverRep.{u, v, w, max v w x} k V) (hM : Indecomposable M)
    (hfd : IsFinDim.{u, v, w, max v w x} k V M) :
    titsForm V (fun j : V ↦ (dimVector M j : ℤ)) = 1 := by
  obtain ⟨l, hnd, hall, hl⟩ := hac.exists_isSinkAdmissible
  exact titsForm_dimVector_eq_one_of_indecomposable q hq hnd hall hl hpd M hM hfd

end TauCeti
