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
`i`; two such representations are isomorphic, by `TauCeti.nonempty_iso_of_isZero_of_ne`.

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

* `TauCeti.nonempty_iso_of_isZero_of_ne`: two representations vanishing away from a sink are
  isomorphic as soon as their vertex spaces at that sink are, and
  `TauCeti.nonempty_iso_of_dimVector_eq_of_forall_subsingleton`: the same conclusion from equality
  of dimension vectors.
* `TauCeti.nonempty_iso_of_nonempty_iso_reflectRep`: **the reflection functor at a sink reflects
  isomorphisms** between representations whose incoming sums there are onto.
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

/-! ### Representations concentrated at a sink -/

section Concentrated

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
variable {M N : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-- **Two representations vanishing away from a sink are isomorphic as soon as their vertex spaces
at that sink are.** Every component away from `i` is a map between zero objects, and there is no
naturality condition to check at `i`, since no arrow leaves a sink. -/
theorem nonempty_iso_of_isZero_of_ne (hi : IsSink i)
    (hM : ∀ a : Q, a ≠ i → Limits.IsZero (M.obj a))
    (hN : ∀ a : Q, a ≠ i → Limits.IsZero (N.obj a))
    (e : M.obj ((Paths.of Q).obj i) ≃ₗ[k] N.obj ((Paths.of Q).obj i)) :
    Nonempty (M ≅ N) := by
  classical
  have eIso : M.obj ((Paths.of Q).obj i) ≅ N.obj ((Paths.of Q).obj i) :=
    { hom := ModuleCat.ofHom e.toLinearMap
      inv := ModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by ext y; exact e.symm_apply_apply y
      inv_hom_id := by ext y; exact e.apply_symm_apply y }
  refine ⟨NatIso.ofComponents (fun a ↦ if h : a = (Paths.of Q).obj i then
      eqToIso (congrArg M.obj h) ≪≫ eIso ≪≫ eqToIso (congrArg N.obj h).symm
    else (hM a h).iso (hN a h)) fun {a b} p ↦ ?_⟩
  by_cases ha : a = (Paths.of Q).obj i
  · -- a path out of a sink is the identity, so the naturality square is trivial
    subst ha
    obtain rfl := hi.eq_of_path p
    have hMp : M.map p = 𝟙 (M.obj a) := by
      rw [hi.path_self_eq_nil p]
      exact M.map_id a
    have hNp : N.map p = 𝟙 (N.obj a) := by
      rw [hi.path_self_eq_nil p]
      exact N.map_id a
    rw [hMp, hNp]
    simp
  · exact (hM a ha).eq_of_src _ _

/-- **A representation concentrated at a sink is isomorphic to every finite-dimensional
representation with the same dimension vector.** Equality of dimension vectors makes the comparison
representation vanish wherever `M` does, and matches the two vertex spaces at the sink. -/
theorem nonempty_iso_of_dimVector_eq_of_forall_subsingleton (hi : IsSink i)
    (hsub : ∀ a : Q, a ≠ i → Subsingleton (M.obj a))
    (hfdM : IsFinDim.{u, v, w, max v w x} k Q M) (hfdN : IsFinDim.{u, v, w, max v w x} k Q N)
    (hd : dimVector M = dimVector N) : Nonempty (M ≅ N) := by
  have hfdM' := isFinDim_iff.mp hfdM
  have hfdN' := isFinDim_iff.mp hfdN
  have hNzero : ∀ a : Q, a ≠ i → Limits.IsZero (N.obj a) := by
    intro a ha
    have hMa : Subsingleton (M.obj ((Paths.of Q).obj a)) := hsub a ha
    have hfdNa := hfdN' ((Paths.of Q).obj a)
    have h0 : Module.finrank k (N.obj ((Paths.of Q).obj a)) = 0 := by
      rw [← dimVector_apply, ← congrFun hd a, dimVector_apply]
      exact Module.finrank_zero_of_subsingleton (R := k)
    have hss : Subsingleton (N.obj ((Paths.of Q).obj a)) := Module.finrank_zero_iff.mp h0
    exact @ModuleCat.isZero_of_subsingleton k _ (N.obj a) hss
  have hfdMi := hfdM' ((Paths.of Q).obj i)
  have hfdNi := hfdN' ((Paths.of Q).obj i)
  have hfr : Module.finrank k (M.obj ((Paths.of Q).obj i))
      = Module.finrank k (N.obj ((Paths.of Q).obj i)) := by
    rw [← dimVector_apply, ← dimVector_apply, hd]
  exact nonempty_iso_of_isZero_of_ne hi
    (fun a ha ↦ @ModuleCat.isZero_of_subsingleton k _ (M.obj a) (hsub a ha)) hNzero
    (LinearEquiv.ofFinrankEq _ _ hfr)

end Concentrated

/-! ### Reflection at a sink reflects isomorphisms -/

section Reflect

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]
variable {M N : QuiverRep.{u, v, w, max v w x} k Q} {i : Q}

/-- **The reflection functor at a sink reflects isomorphisms**, between representations whose
incoming sums there are onto. Fullness produces morphisms `f : M ⟶ N` and `g : N ⟶ M` reflecting
to the two halves of the given isomorphism, and faithfulness turns the two triangle identities
downstairs into the two upstairs.

The reflection functor is not fully faithful on all of `TauCeti.QuiverRep k Q` -- it annihilates
the vertex simple at `i` -- so `CategoryTheory.Functor.ReflectsIsomorphisms` and the machinery
around it, which ask for `Full` and `Faithful` instances, do not apply, and the argument is made
directly from `TauCeti.reflectionFunctor_map_surjective` and
`TauCeti.reflectionFunctor_map_injective`. -/
theorem nonempty_iso_of_nonempty_iso_reflectRep (hi : IsSink i)
    (hsM : Function.Surjective (incomingSum M i))
    (hsN : Function.Surjective (incomingSum N i))
    (h : Nonempty (reflectRep M hi ≅ reflectRep N hi)) : Nonempty (M ≅ N) := by
  obtain ⟨θ⟩ := h
  have θ' : (reflectionFunctor i hi).obj M ≅ (reflectionFunctor i hi).obj N :=
    eqToIso (reflectionFunctor_obj i hi M) ≪≫ θ ≪≫ eqToIso (reflectionFunctor_obj i hi N).symm
  obtain ⟨f, hf⟩ := reflectionFunctor_map_surjective (M := M) (N := N) hi hsM θ'.hom
  obtain ⟨g, hg⟩ := reflectionFunctor_map_surjective (M := N) (N := M) hi hsN θ'.inv
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · refine reflectionFunctor_map_injective (M := M) (N := M) hi hsM ?_
    simp only [Functor.map_comp, hf, hg]
    exact θ'.hom_inv_id.trans ((reflectionFunctor i hi).map_id M).symm
  · refine reflectionFunctor_map_injective (M := N) (N := N) hi hsN ?_
    simp only [Functor.map_comp, hf, hg]
    exact θ'.inv_hom_id.trans ((reflectionFunctor i hi).map_id N).symm

end Reflect

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
theorem nonempty_iso_of_dimVector_eq_of_reflectionFunctorList :
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
          exact (nonempty_iso_of_dimVector_eq_of_forall_subsingleton hi hsubN hfdN hfdM
            hd.symm).map Iso.symm
      · -- `M` is concentrated at the sink, hence so is `N`
        exact nonempty_iso_of_dimVector_eq_of_forall_subsingleton hi hsubM hfdM hfdN hd

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
        exact nonempty_iso_of_dimVector_eq_of_reflectionFunctorList l q hq hl M N hM hN hfdM
          hfdN hd (Or.inl ((nonempty_iso_coxeterFunctor_obj_iff q hq hnd hall hl M N).mp hiso))
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
