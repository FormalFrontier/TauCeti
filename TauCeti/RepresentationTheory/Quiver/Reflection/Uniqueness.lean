/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Root

/-!
# An indecomposable representation is determined by its dimension vector

Let `Q` be a finite quiver whose Tits form is positive definite, the numerical side of the ADE
condition in Gabriel's theorem. This file proves that two finite-dimensional indecomposable
representations of `Q` with the same dimension vector are isomorphic
(`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable`), so that `TauCeti.dimVector` is
injective on the isomorphism classes of indecomposables
(`TauCeti.nonempty_iso_iff_dimVector_eq_of_indecomposable`).

Together with `TauCeti.titsForm_dimVector_eq_one_of_indecomposable`, which says that the dimension
vector of an indecomposable is a positive root of the Tits form, this is the injective half of the
Gabriel correspondence: `M ↦ dim M` is an injection from the isomorphism classes of
finite-dimensional indecomposables into the positive roots. Its surjectivity, that every positive
root is realized, is not proved here.

## The argument

The Bernstein-Gelfand-Ponomarev induction is run at `M` and `N` in parallel. The reflection functor
at a sink `i` is fully faithful on the representations whose incoming sum at `i` is onto
(`TauCeti.reflectionFunctor_map_bijective`), and a fully faithful functor reflects isomorphisms:
this is `TauCeti.nonempty_iso_of_nonempty_iso_reflectRep`. An indecomposable representation fails
that hypothesis only by being concentrated at `i`
(`TauCeti.incomingSum_surjective_or_forall_subsingleton`), and a representation with the same
dimension vector then vanishes wherever it does and has a vertex space of the same dimension at
`i`; two such representations are isomorphic, by
`TauCeti.nonempty_iso_of_isZero_away_of_linearEquiv`.

The comparison at such a stage is made directly, rather than through the vertex simple `Sᵢ` and
`TauCeti.nonempty_iso_simpleRep_of_forall_subsingleton`: the vertex space of `Sᵢ` is the field
itself, so naming it would force the universe of the vertex spaces to be that of the field, below
the generality at which `TauCeti.titsForm_dimVector_eq_one_of_indecomposable` states the other half
of the correspondence.

So at each stage of a sink-admissible list, either both representations are concentrated at the
current sink and are therefore already identified, or both reflect, with equal dimension vectors
again. The induction terminates because a power of the Coxeter functor annihilates `M`
(`TauCeti.exists_isZero_coxeterFunctor_iterate`), and the stage that annihilates it is a stage
where it is concentrated at the sink.

## Main results

* `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable`: **two finite-dimensional
  indecomposable representations with the same dimension vector are isomorphic**, with
  `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic` the same statement over an
  acyclic quiver, where the sink-admissible ordering is chosen internally.
* `TauCeti.nonempty_iso_iff_dimVector_eq_of_indecomposable`: the resulting characterization of
  isomorphism of indecomposables by equality of dimension vectors.

## References

This is the uniqueness milestone of Layer 5 ("Gabriel's theorem") of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, that the reflection
induction transports the dimension vector faithfully. See Bernstein--Gelfand--Ponomarev, *Coxeter
functors and Gabriel's theorem*, and Derksen--Weyman, *An Introduction to Quiver Representations*,
Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

/-! ### Uniqueness along a sink-admissible list -/

section Uniqueness

variable {k : Type u} {V : Type v} [fld : Field k] [fV : Fintype V]

/-- **Two indecomposable representations with the same dimension vector are isomorphic, provided a
composite of reflection functors identifies or annihilates them.** The induction is on the list of
sinks. A stage at which both representations reflect passes the hypothesis down and returns an
isomorphism through `TauCeti.nonempty_iso_of_nonempty_iso_reflectRep`; a stage at which either is
concentrated at its own sink identifies the two on the spot, by
`TauCeti.nonempty_iso_of_dimVector_eq_of_forall_subsingleton`. The empty list leaves the hypothesis
itself, whose second alternative an indecomposable representation excludes. -/
private theorem nonempty_iso_of_dimVector_eq_of_reflectionFunctorList :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSinkAdmissible q l)
      (M N : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Indecomposable M → Indecomposable N →
      @IsFinDim.{u, v, w, max v w x} k V fld q M →
      @IsFinDim.{u, v, w, max v w x} k V fld q N →
      @dimVector k V fld q M = @dimVector k V fld q N →
      (Nonempty ((reflectionFunctorList k l q hq hl).obj M
            ≅ (reflectionFunctorList k l q hq hl).obj N)
          ∨ Limits.IsZero ((reflectionFunctorList k l q hq hl).obj M)) →
      Nonempty (M ≅ N)
  | [], q, hq, hl, M, _, hM, _, _, _, _, hyp => by
      rw [reflectionFunctorList_nil] at hyp
      exact hyp.resolve_right hM.1
  | i :: l, q, hq, hl, M, N, hM, hN, hfdM, hfdN, hd, hyp => by
      classical
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSinkAdmissible_cons.mp hl
      have hfdM' : ∀ a : V, FiniteDimensional k (M.obj a) :=
        (@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfdM
      have hfdN' : ∀ a : V, FiniteDimensional k (N.obj a) :=
        (@isFinDim_iff.{u, v, w, max v w x} k V fld q N).mp hfdN
      rw [reflectionFunctorList_cons_obj i l q hq hl M,
        reflectionFunctorList_cons_obj i l q hq hl N] at hyp
      rcases incomingSum_surjective_or_forall_subsingleton hi hM with hsM | hsubM
      · rcases incomingSum_surjective_or_forall_subsingleton hi hN with hsN | hsubN
        · -- both stages reflect, so the dimension vectors stay equal and the induction descends
          refine nonempty_iso_of_nonempty_iso_reflectRep hi hsM hsN ?_
          have hmid : @vertexPreReflection V q fV hq _ i
                (fun j : V ↦ (@dimVector k V fld q M j : ℤ))
              = @vertexPreReflection V q fV hq _ i
                (fun j : V ↦ (@dimVector k V fld q N j : ℤ)) := by
            rw [hd]
          have hcast := (dimVector_reflectRep M hi (fun e ↦ hfdM' e.1) hsM).trans
            (hmid.trans (dimVector_reflectRep N hi (fun e ↦ hfdN' e.1) hsN).symm)
          have hdR : @dimVector k V fld (Quiver.reflectAt q i) (reflectRep M hi)
              = @dimVector k V fld (Quiver.reflectAt q i) (reflectRep N hi) :=
            funext fun j ↦ Nat.cast_inj.mp (congrFun hcast j)
          exact nonempty_iso_of_dimVector_eq_of_reflectionFunctorList l (Quiver.reflectAt q i)
            (@instFintypeReflectHom V q hq i) hl' (reflectRep M hi) (reflectRep N hi)
            (indecomposable_reflectRep hi hM hsM) (indecomposable_reflectRep hi hN hsN)
            ((@isFinDim_iff.{u, v, w, max v w x} k V fld (Quiver.reflectAt q i) _).mpr
              (finiteDimensional_reflectRep_obj M hi hfdM'))
            ((@isFinDim_iff.{u, v, w, max v w x} k V fld (Quiver.reflectAt q i) _).mpr
              (finiteDimensional_reflectRep_obj N hi hfdN')) hdR hyp
        · -- `N` is concentrated at the sink, hence so is `M`
          exact (nonempty_iso_of_dimVector_eq_of_forall_subsingleton hi hsubN (hfdN' i) hfdM
            hd.symm).map Iso.symm
      · -- `M` is concentrated at the sink, hence so is `N`
        exact nonempty_iso_of_dimVector_eq_of_forall_subsingleton hi hsubM (hfdM' i) hfdN hd

/-! ### Uniqueness -/

/-- **Two indecomposable representations with the same dimension vector are isomorphic, provided a
power of the Coxeter functor annihilates one of them.** Each pass either annihilates a
representation, which sends the argument back to the pass itself through
`TauCeti.nonempty_iso_of_dimVector_eq_of_reflectionFunctorList`, or carries both representations to
indecomposables with the same, Coxeter-transformed, dimension vector, where the induction
hypothesis applies and the pass reflects the isomorphism it produces. -/
private theorem nonempty_iso_of_dimVector_eq_of_isZero_iterate
    (q : _root_.Quiver.{w} V) (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l) :
    ∀ (n : ℕ) (M N : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Indecomposable M → Indecomposable N →
      @IsFinDim.{u, v, w, max v w x} k V fld q M →
      @IsFinDim.{u, v, w, max v w x} k V fld q N →
      @dimVector k V fld q M = @dimVector k V fld q N →
      Limits.IsZero (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[n] M) →
      Nonempty (M ≅ N) := by
  classical
  intro n
  induction n with
  | zero =>
    intro M _ hM _ _ _ _ hz
    rw [Function.iterate_zero_apply] at hz
    exact absurd hz hM.1
  | succ n ih =>
    intro M N hM hN hfdM hfdN hd hz
    rw [Function.iterate_succ_apply] at hz
    rcases indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl M hM
        ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfdM) with ⟨hM1, hdM⟩ | h0
    · rcases indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl N hN
          ((@isFinDim_iff.{u, v, w, max v w x} k V fld q N).mp hfdN) with ⟨hN1, hdN⟩ | h0N
      · -- both survive the pass, so the induction hypothesis identifies their images
        have hmid : (@vertexPreReflectionList V q fV hq _ l)
              (fun j : V ↦ (@dimVector k V fld q M j : ℤ))
            = (@vertexPreReflectionList V q fV hq _ l)
              (fun j : V ↦ (@dimVector k V fld q N j : ℤ)) := by
          rw [hd]
        have hcast := hdM.trans (hmid.trans hdN.symm)
        have hdC : @dimVector k V fld q
              ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj M)
            = @dimVector k V fld q ((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj N) :=
          funext fun j ↦ Nat.cast_inj.mp (congrFun hcast j)
        have hiso := ih _ _ hM1 hN1 (isFinDim_coxeterFunctor_obj q hq hnd hall hl M hfdM)
          (isFinDim_coxeterFunctor_obj q hq hnd hall hl N hfdN) hdC hz
        have hlist := (nonempty_iso_coxeterFunctor_obj_iff_nonempty_iso_reflectionFunctorList_obj
          q hq hnd hall hl M N).mp hiso
        exact nonempty_iso_of_dimVector_eq_of_reflectionFunctorList l q hq hl M N hM hN hfdM
          hfdN hd (Or.inl hlist)
      · exact (nonempty_iso_of_dimVector_eq_of_reflectionFunctorList l q hq hl N M hN hM hfdN
          hfdM hd.symm (Or.inr
            ((isZero_coxeterFunctor_obj_iff_isZero_reflectionFunctorList_obj q hq hnd hall hl
              N).mp h0N))).map Iso.symm
    · exact nonempty_iso_of_dimVector_eq_of_reflectionFunctorList l q hq hl M N hM hN hfdM hfdN
        hd (Or.inr ((isZero_coxeterFunctor_obj_iff_isZero_reflectionFunctorList_obj q hq hnd hall
          hl M).mp h0))

/-- **An indecomposable representation is determined by its dimension vector.** For a quiver with
positive definite Tits form -- the numerical form of the ADE condition -- and any sink-admissible
ordering of its vertices, two indecomposable representations with finite-dimensional vertex spaces
and the same dimension vector are isomorphic.

This is the injectivity half of the Gabriel correspondence; that the dimension vector of an
indecomposable is a positive root is
`TauCeti.titsForm_dimVector_eq_one_of_indecomposable`. -/
theorem nonempty_iso_of_dimVector_eq_of_indecomposable (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (hpd : (@titsForm V q fV hq).PosDef) (M N : @QuiverRep.{u, v, w, max v w x} k V fld q)
    (hM : Indecomposable M) (hN : Indecomposable N)
    (hfdM : @IsFinDim.{u, v, w, max v w x} k V fld q M)
    (hfdN : @IsFinDim.{u, v, w, max v w x} k V fld q N)
    (hd : @dimVector k V fld q M = @dimVector k V fld q N) :
    Nonempty (M ≅ N) := by
  obtain ⟨n, hn⟩ := exists_isZero_coxeterFunctor_iterate q hq hnd hall hl hpd M hM hfdM
  exact nonempty_iso_of_dimVector_eq_of_isZero_iterate q hq hnd hall hl n M N hM hN hfdM hfdN hd hn

/-- **An indecomposable representation of an acyclic quiver with positive definite Tits form is
determined by its dimension vector.** This is the consumer-facing form of
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable`: acyclicity produces a sink-admissible
ordering by `TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`, and since the conclusion does not
mention the ordering, the choice is made here rather than by the caller. -/
theorem nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic
    [q : _root_.Quiver.{w} V] [hq : ∀ a b : V, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic V)
    (hpd : (titsForm V).PosDef) (M N : QuiverRep.{u, v, w, max v w x} k V)
    (hM : Indecomposable M) (hN : Indecomposable N)
    (hfdM : IsFinDim.{u, v, w, max v w x} k V M) (hfdN : IsFinDim.{u, v, w, max v w x} k V N)
    (hd : dimVector M = dimVector N) :
    Nonempty (M ≅ N) := by
  obtain ⟨l, hnd, hall, hl⟩ := hac.exists_isSinkAdmissible
  exact nonempty_iso_of_dimVector_eq_of_indecomposable q hq hnd hall hl hpd M N hM hN hfdM hfdN hd

/-- **Indecomposable representations of an acyclic quiver with positive definite Tits form are
isomorphic exactly when their dimension vectors agree.** The forward direction is
`TauCeti.dimVector_eq_of_iso` and needs none of the hypotheses; the converse is
`TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`. -/
theorem nonempty_iso_iff_dimVector_eq_of_indecomposable
    [q : _root_.Quiver.{w} V] [hq : ∀ a b : V, Fintype (a ⟶ b)] (hac : Quiver.IsAcyclic V)
    (hpd : (titsForm V).PosDef) (M N : QuiverRep.{u, v, w, max v w x} k V)
    (hM : Indecomposable M) (hN : Indecomposable N)
    (hfdM : IsFinDim.{u, v, w, max v w x} k V M) (hfdN : IsFinDim.{u, v, w, max v w x} k V N) :
    Nonempty (M ≅ N) ↔ dimVector M = dimVector N :=
  ⟨fun ⟨e⟩ ↦ dimVector_eq_of_iso e, fun hd ↦
    nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic hac hpd M N hM hN hfdM hfdN hd⟩

end Uniqueness

end TauCeti
