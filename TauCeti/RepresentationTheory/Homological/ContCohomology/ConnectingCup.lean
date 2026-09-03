/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CupProduct
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact

/-!
# The connecting maps of the low-degree cup products

Let `0 → A' → A → A'' → 0` be a short exact sequence of discrete `G`-modules and let `B` be a
discrete `G`-module. Pairings `A' × B → C'`, `A × B → C` and `A'' × B → C''` compatible with a
second short exact sequence `0 → C' → C → C'' → 0` make both composites
`H^p(G, A'') × H^q(G, B) → H^{p+q+1}(G, C')` — cup and then connect, or connect and then cup —
defined, and they agree:

```text
δ (a'' ⌣ b) = δ a'' ⌣ b.
```

Exchanging the roles of the two variables produces the sign `(-1)^p`:

```text
δ (a ⌣ b'') = (-1)^p (a ⌣ δ b'').
```

The coefficient diagrams are inputs of the theorems rather than prose around an untyped equation,
so each of the two statements carries its own structure of compatible pairings,
`TauCeti.ContCohomology.ShortExactPairingFst` and `ShortExactPairingSnd`. Each identity is stated
once for every bidegree in which its two sides are defined: the explicit cup products stop at
total degree `2`, so the connecting map may raise a total degree `0` or `1` and no more, which
leaves exactly three instances of each.

## Main definitions

* `TauCeti.ContCohomology.ShortExactPairingFst`: a `G`-equivariant biadditive pairing of a short
  exact sequence of discrete `G`-modules with a fixed discrete `G`-module, valued in a short exact
  sequence.
* `TauCeti.ContCohomology.ShortExactPairingSnd`: the same datum with the short exact sequence in
  the second variable of the pairing.

## Main statements

* `TauCeti.ContCohomology.ShortExactPairingFst.explicitDelta0_explicitCup00`,
  `explicitDelta1_explicitCup01` and `explicitDelta1_explicitCup10`: the identity
  `δ (a'' ⌣ b) = δ a'' ⌣ b` in bidegrees `(0,0)`, `(0,1)` and `(1,0)`.
* `TauCeti.ContCohomology.ShortExactPairingSnd.explicitDelta0_explicitCup00`,
  `explicitDelta1_explicitCup01` and `explicitDelta1_explicitCup10`: the identity
  `δ (a ⌣ b'') = (-1)^p (a ⌣ δ b'')` in bidegrees `(0,0)`, `(0,1)` and `(1,0)`. The sign is `-1`
  exactly in bidegree `(1,0)`, the only one of the three whose first factor has odd degree.

## Implementation notes

Both structures carry three pairings with their equivariance, together with the two squares
saying that the inclusions and the projections of the two sequences intertwine them. Joint
continuity of a pairing is *not* carried as data: every module in sight is discrete, so it is
`continuous_of_discreteTopology`, which is what the cup products of
`TauCeti/RepresentationTheory/Homological/ContCohomology/CupProduct.lean` are fed here.

Every proof runs on representatives. A class in `H⁰(G, A'')` is lifted to an element of `A`, a
class in `H¹(G, A'')` to a *continuous* cochain into `A` — which exists because `A''` is discrete,
by `TauCeti.ContCohomology.exists_continuous_lift` — and the pairing of that lift with a
representative of the second factor is then a lift of the cup cochain. Its differential, retracted
to the subobject by `TauCeti.ContCohomology.DiscreteShortExact.exists_mem_Z1_incl_comp_eq_d0` or
`exists_mem_Z2_incl_comp_eq_d1`, is on the nose the cup of the connecting cochain with the second
factor. Since `explicitDelta0_apply` and `explicitDelta1_apply` hold for whatever lift a
computation has in hand, no comparison of choices is ever needed.

The one place a sign appears is `ShortExactPairingSnd.explicitDelta1_explicitCup10`, where the
`1`-cocycle identity for the first factor cancels all but one term of the differential and leaves
`-(a ⌣ δ b'')`. In the `𝔽₂`-valued arithmetic applications that sign is `1`.

This implements the "connecting maps, as typed diagrams" milestone of Layer 8 of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`, whose two theorems are
the two families below, with the six instances that layer lists as required downstream.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.3) and
  (1.4.5): the compatibility of the cup product with the connecting homomorphism in each variable,
  with the sign `(-1)^p` in the second.
* K. Brown, *Cohomology of Groups*, V §3: the cochain-level Leibniz rule the two identities
  descend from.
-/

public section

namespace TauCeti.ContCohomology

universe uG vA' vA vA'' vB' vB vB'' vC' vC vC''

/-! ### The short exact sequence in the first variable -/

/-- A `G`-equivariant biadditive pairing of a short exact sequence of discrete `G`-modules
`S : 0 → A' → A → A'' → 0` with a fixed discrete `G`-module `B`, valued in a short exact sequence
`T : 0 → C' → C → C'' → 0`.

This is the coefficient datum that types the identity `δ (a'' ⌣ b) = δ a'' ⌣ b`: the three
pairings make the three cup products of that identity defined, and the two squares `incl_pairing`
and `proj_pairing` make its two connecting maps match up. -/
@[ext]
structure ShortExactPairingFst {G : Type uG} [Monoid G]
    {A' : Type vA'} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
      [DistribMulAction G A']
    {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A]
    {A'' : Type vA''} [AddCommGroup A''] [TopologicalSpace A''] [DiscreteTopology A'']
      [DistribMulAction G A'']
    (S : DiscreteShortExact G A' A A'')
    (B : Type vB) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction G B]
    {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
      [DistribMulAction G C']
    {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
      [DistribMulAction G C]
    {C'' : Type vC''} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
      [DistribMulAction G C'']
    (T : DiscreteShortExact G C' C C'') where
  /-- The pairing of the subobject `A'` with `B`, valued in `C'`. -/
  pairing' : A' →+ B →+ C'
  /-- The pairing of `A` with `B`, valued in `C`. -/
  pairing : A →+ B →+ C
  /-- The pairing of the quotient `A''` with `B`, valued in `C''`. -/
  pairing'' : A'' →+ B →+ C''
  /-- The pairing on the subobject is `G`-equivariant. -/
  equivariant' : ∀ (g : G) (a : A') (b : B), pairing' (g • a) (g • b) = g • pairing' a b
  /-- The pairing on the total object is `G`-equivariant. -/
  equivariant : ∀ (g : G) (a : A) (b : B), pairing (g • a) (g • b) = g • pairing a b
  /-- The pairing on the quotient is `G`-equivariant. -/
  equivariant'' : ∀ (g : G) (a : A'') (b : B), pairing'' (g • a) (g • b) = g • pairing'' a b
  /-- The inclusions of the two sequences intertwine the two pairings they connect. -/
  incl_pairing : ∀ (a : A') (b : B), T.incl (pairing' a b) = pairing (S.incl a) b
  /-- The projections of the two sequences intertwine the two pairings they connect. -/
  proj_pairing : ∀ (a : A) (b : B), T.proj (pairing a b) = pairing'' (S.proj a) b

namespace ShortExactPairingFst

variable {G : Type uG} [Group G]
  {A' : Type vA'} [AddCommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
    [DistribMulAction G A']
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A]
  {A'' : Type vA''} [AddCommGroup A''] [TopologicalSpace A''] [DiscreteTopology A'']
    [DistribMulAction G A'']
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B]
  {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C']
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {C'' : Type vC''} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
    [DistribMulAction G C'']
  {S : DiscreteShortExact G A' A A''} {T : DiscreteShortExact G C' C C''}
  (P : ShortExactPairingFst S B T)

/-- Pairing with an invariant second factor commutes with the action of `G` on the first. -/
theorem pairing_smul_left (g : G) (a : A) (y : H0 G B) :
    P.pairing (g • a) (y : B) = g • P.pairing a (y : B) :=
  pairingRight_smul P.pairing P.equivariant y g a

variable [TopologicalSpace G] [ContinuousSMul G A'] [ContinuousSMul G A]
  [ContinuousSMul G A''] [ContinuousSMul G B] [ContinuousSMul G C'] [ContinuousSMul G C]
  [ContinuousSMul G C'']

omit [ContinuousSMul G A''] [ContinuousSMul G B] [ContinuousSMul G C''] in
/-- **`δ⁰` in the first variable of the `(0,0)` cup**: `δ⁰ (a'' ⌣ b) = δ⁰ a'' ⌣ b`, both sides
living in `H¹(G, C')`. -/
theorem explicitDelta0_explicitCup00 (x : H0 G A'') (y : H0 G B) :
    T.explicitDelta0 (explicitCup00 G A'' B C'' P.pairing'' P.equivariant'' x y) =
      explicitCup10 G A' B C' P.pairing' continuous_of_discreteTopology P.equivariant'
        (S.explicitDelta0 x) y := by
  have hy : ∀ g : G, g • (y : B) = (y : B) := (FixedPoints.mem_addSubgroup G B (y : B)).1 y.2
  obtain ⟨a, ha⟩ := S.proj_surjective (x : A'')
  obtain ⟨v, hv, hincl⟩ := S.exists_mem_Z1_incl_comp_eq_d0 (b := a) (by rw [ha]; exact x.2)
  rw [S.explicitDelta0_apply x ha hv hincl, QuotientAddGroup.mk'_apply, explicitCup10_mk]
  refine T.explicitDelta0_apply _ (b := P.pairing a (y : B)) ?_ _ fun g => ?_
  · rw [P.proj_pairing, ha, coe_explicitCup00]
  · rw [P.incl_pairing, hincl g, hy g, map_sub, AddMonoidHom.sub_apply, P.pairing_smul_left g a y]

variable [ContinuousMul G]

omit [ContinuousSMul G A''] in
/-- **`δ⁰` in the first variable of the `(0,1)` cup**: `δ¹ (a'' ⌣ b) = δ⁰ a'' ⌣ b`, both sides
living in `H²(G, C')`. -/
theorem explicitDelta1_explicitCup01 (x : H0 G A'') (y : H1 G B) :
    T.explicitDelta1 (explicitCup01 G A'' B C'' P.pairing'' continuous_of_discreteTopology
        P.equivariant'' x y) =
      explicitCup11 G A' B C' P.pairing' continuous_of_discreteTopology P.equivariant'
        (S.explicitDelta0 x) y := by
  induction y using QuotientAddGroup.induction_on with
  | _ β =>
    obtain ⟨a, ha⟩ := S.proj_surjective (x : A'')
    obtain ⟨v, hv, hincl⟩ := S.exists_mem_Z1_incl_comp_eq_d0 (b := a) (by rw [ha]; exact x.2)
    rw [S.explicitDelta0_apply x ha hv hincl, QuotientAddGroup.mk'_apply, explicitCup11_mk,
      explicitCup01_mk]
    refine T.explicitDelta1_apply _ (e := fun g => P.pairing a ((β : G → B) g))
      ((continuous_of_discreteTopology (f := P.pairing a)).comp' (mem_Z1_iff.1 β.2).1)
      (fun g => by rw [P.proj_pairing, ha]) _ fun g h => ?_
    rw [P.incl_pairing, hincl g, map_sub, AddMonoidHom.sub_apply,
      P.equivariant g a ((β : G → B) h), (mem_Z1_iff.1 β.2).2 g h, map_add]
    abel

omit [ContinuousSMul G B] in
/-- **`δ¹` in the first variable of the `(1,0)` cup**: `δ¹ (a'' ⌣ b) = δ¹ a'' ⌣ b`, both sides
living in `H²(G, C')`. -/
theorem explicitDelta1_explicitCup10 (x : H1 G A'') (y : H0 G B) :
    T.explicitDelta1 (explicitCup10 G A'' B C'' P.pairing'' continuous_of_discreteTopology
        P.equivariant'' x y) =
      explicitCup20 G A' B C' P.pairing' continuous_of_discreteTopology P.equivariant'
        (S.explicitDelta1 x) y := by
  induction x using QuotientAddGroup.induction_on with
  | _ α =>
    have hy : ∀ g : G, g • (y : B) = (y : B) := (FixedPoints.mem_addSubgroup G B (y : B)).1 y.2
    obtain ⟨e, hec, hep⟩ := exists_continuous_lift S.proj_surjective (mem_Z1_iff.1 α.2).1
    have hcoc : groupCohomology.IsCocycle₁ fun g => S.proj (e g) := by
      simpa only [hep] using (mem_Z1_iff.1 α.2).2
    obtain ⟨w, hw, hincl⟩ := S.exists_mem_Z2_incl_comp_eq_d1 hec hcoc
    have hδ : S.explicitDelta1 (α : H1 G A'') = H2pi G A' ⟨w, hw⟩ :=
      S.explicitDelta1_apply α hec hep hw hincl
    rw [hδ, QuotientAddGroup.mk'_apply, explicitCup20_mk, explicitCup10_mk]
    refine T.explicitDelta1_apply _ (e := fun g => P.pairing (e g) (y : B))
      ((continuous_of_discreteTopology (f := fun z : A => P.pairing z (y : B))).comp' hec)
      (fun g => by simp only [P.proj_pairing, hep, hy]) _ fun g h => ?_
    rw [P.incl_pairing, hincl g h, hy (g * h), map_add, map_sub, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, P.pairing_smul_left g (e h) y]

end ShortExactPairingFst

/-! ### The short exact sequence in the second variable -/

/-- A `G`-equivariant biadditive pairing of a fixed discrete `G`-module `A` with a short exact
sequence of discrete `G`-modules `S : 0 → B' → B → B'' → 0`, valued in a short exact sequence
`T : 0 → C' → C → C'' → 0`.

This is the coefficient datum that types the identity `δ (a ⌣ b'') = (-1)^p (a ⌣ δ b'')`; it is
`TauCeti.ContCohomology.ShortExactPairingFst` with the roles of the two variables of the pairing
exchanged. -/
@[ext]
structure ShortExactPairingSnd {G : Type uG} [Monoid G]
    (A : Type vA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A]
    {B' : Type vB'} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
      [DistribMulAction G B']
    {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [DistribMulAction G B]
    {B'' : Type vB''} [AddCommGroup B''] [TopologicalSpace B''] [DiscreteTopology B'']
      [DistribMulAction G B'']
    (S : DiscreteShortExact G B' B B'')
    {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
      [DistribMulAction G C']
    {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
      [DistribMulAction G C]
    {C'' : Type vC''} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
      [DistribMulAction G C'']
    (T : DiscreteShortExact G C' C C'') where
  /-- The pairing of `A` with the subobject `B'`, valued in `C'`. -/
  pairing' : A →+ B' →+ C'
  /-- The pairing of `A` with `B`, valued in `C`. -/
  pairing : A →+ B →+ C
  /-- The pairing of `A` with the quotient `B''`, valued in `C''`. -/
  pairing'' : A →+ B'' →+ C''
  /-- The pairing into the subobject is `G`-equivariant. -/
  equivariant' : ∀ (g : G) (a : A) (b : B'), pairing' (g • a) (g • b) = g • pairing' a b
  /-- The pairing into the total object is `G`-equivariant. -/
  equivariant : ∀ (g : G) (a : A) (b : B), pairing (g • a) (g • b) = g • pairing a b
  /-- The pairing into the quotient is `G`-equivariant. -/
  equivariant'' : ∀ (g : G) (a : A) (b : B''), pairing'' (g • a) (g • b) = g • pairing'' a b
  /-- The inclusions of the two sequences intertwine the two pairings they connect. -/
  incl_pairing : ∀ (a : A) (b : B'), T.incl (pairing' a b) = pairing a (S.incl b)
  /-- The projections of the two sequences intertwine the two pairings they connect. -/
  proj_pairing : ∀ (a : A) (b : B), T.proj (pairing a b) = pairing'' a (S.proj b)

namespace ShortExactPairingSnd

variable {G : Type uG} [Group G]
  {A : Type vA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A]
  {B' : Type vB'} [AddCommGroup B'] [TopologicalSpace B'] [DiscreteTopology B']
    [DistribMulAction G B']
  {B : Type vB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B]
  {B'' : Type vB''} [AddCommGroup B''] [TopologicalSpace B''] [DiscreteTopology B'']
    [DistribMulAction G B'']
  {C' : Type vC'} [AddCommGroup C'] [TopologicalSpace C'] [DiscreteTopology C']
    [DistribMulAction G C']
  {C : Type vC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C]
  {C'' : Type vC''} [AddCommGroup C''] [TopologicalSpace C''] [DiscreteTopology C'']
    [DistribMulAction G C'']
  {S : DiscreteShortExact G B' B B''} {T : DiscreteShortExact G C' C C''}
  (P : ShortExactPairingSnd A S T)

/-- Pairing with an invariant first factor commutes with the action of `G` on the second. -/
theorem pairing_smul_right (g : G) (x : H0 G A) (b : B) :
    P.pairing (x : A) (g • b) = g • P.pairing (x : A) b :=
  pairingLeft_smul P.pairing P.equivariant x g b

variable [TopologicalSpace G] [ContinuousSMul G A] [ContinuousSMul G B']
  [ContinuousSMul G B] [ContinuousSMul G B''] [ContinuousSMul G C'] [ContinuousSMul G C]
  [ContinuousSMul G C'']

omit [ContinuousSMul G A] [ContinuousSMul G B''] [ContinuousSMul G C''] in
/-- **`δ⁰` in the second variable of the `(0,0)` cup**: `δ⁰ (a ⌣ b'') = a ⌣ δ⁰ b''`, both sides
living in `H¹(G, C')`. The sign `(-1)^p` is `1`, the first factor having degree `0`. -/
theorem explicitDelta0_explicitCup00 (x : H0 G A) (y : H0 G B'') :
    T.explicitDelta0 (explicitCup00 G A B'' C'' P.pairing'' P.equivariant'' x y) =
      explicitCup01 G A B' C' P.pairing' continuous_of_discreteTopology P.equivariant' x
        (S.explicitDelta0 y) := by
  obtain ⟨b, hb⟩ := S.proj_surjective (y : B'')
  obtain ⟨v, hv, hincl⟩ := S.exists_mem_Z1_incl_comp_eq_d0 (b := b) (by rw [hb]; exact y.2)
  rw [S.explicitDelta0_apply y hb hv hincl, QuotientAddGroup.mk'_apply, explicitCup01_mk]
  refine T.explicitDelta0_apply _ (b := P.pairing (x : A) b) ?_ _ fun g => ?_
  · rw [P.proj_pairing, hb, coe_explicitCup00]
  · rw [P.incl_pairing, hincl g, map_sub, P.pairing_smul_right g x b]

variable [ContinuousMul G]

omit [ContinuousSMul G B''] in
/-- **`δ⁰` in the second variable of the `(1,0)` cup**: `δ¹ (a ⌣ b'') = -(a ⌣ δ⁰ b'')`, both
sides living in `H²(G, C')`. The sign `(-1)^p` is `-1`, the first factor having degree `1`. -/
theorem explicitDelta1_explicitCup10 (x : H1 G A) (y : H0 G B'') :
    T.explicitDelta1 (explicitCup10 G A B'' C'' P.pairing'' continuous_of_discreteTopology
        P.equivariant'' x y) =
      -explicitCup11 G A B' C' P.pairing' continuous_of_discreteTopology P.equivariant' x
        (S.explicitDelta0 y) := by
  induction x using QuotientAddGroup.induction_on with
  | _ α =>
    obtain ⟨b, hb⟩ := S.proj_surjective (y : B'')
    obtain ⟨v, hv, hincl⟩ := S.exists_mem_Z1_incl_comp_eq_d0 (b := b) (by rw [hb]; exact y.2)
    rw [S.explicitDelta0_apply y hb hv hincl, QuotientAddGroup.mk'_apply, explicitCup11_mk,
      explicitCup10_mk, ← QuotientAddGroup.mk_neg]
    refine T.explicitDelta1_apply _ (e := fun g => P.pairing ((α : G → A) g) (g • b))
      ((continuous_of_discreteTopology (f := fun p : A × B => P.pairing p.1 p.2)).comp'
        ((mem_Z1_iff.1 α.2).1.prodMk (continuous_id.smul continuous_const)))
      (fun g => by simp only [P.proj_pairing, S.proj_equivariant, hb]) _ fun g h => ?_
    have hα : (α : G → A) (g * h) = g • (α : G → A) h + (α : G → A) g := (mem_Z1_iff.1 α.2).2 g h
    have hgh : g • P.pairing ((α : G → A) h) (h • b) =
        P.pairing (g • (α : G → A) h) ((g * h) • b) := by
      rw [← P.equivariant g ((α : G → A) h) (h • b), mul_smul]
    simp only [Pi.neg_apply]
    rw [map_neg, P.incl_pairing, S.incl_equivariant, hincl h, smul_sub, ← mul_smul, map_sub,
      hα, map_add, AddMonoidHom.add_apply, hgh]
    abel

omit [ContinuousSMul G A] in
/-- **`δ¹` in the second variable of the `(0,1)` cup**: `δ¹ (a ⌣ b'') = a ⌣ δ¹ b''`, both sides
living in `H²(G, C')`. The sign `(-1)^p` is `1`, the first factor having degree `0`. -/
theorem explicitDelta1_explicitCup01 (x : H0 G A) (y : H1 G B'') :
    T.explicitDelta1 (explicitCup01 G A B'' C'' P.pairing'' continuous_of_discreteTopology
        P.equivariant'' x y) =
      explicitCup02 G A B' C' P.pairing' continuous_of_discreteTopology P.equivariant' x
        (S.explicitDelta1 y) := by
  induction y using QuotientAddGroup.induction_on with
  | _ β =>
    obtain ⟨e, hec, hep⟩ := exists_continuous_lift S.proj_surjective (mem_Z1_iff.1 β.2).1
    have hcoc : groupCohomology.IsCocycle₁ fun g => S.proj (e g) := by
      simpa only [hep] using (mem_Z1_iff.1 β.2).2
    obtain ⟨w, hw, hincl⟩ := S.exists_mem_Z2_incl_comp_eq_d1 hec hcoc
    have hδ : S.explicitDelta1 (β : H1 G B'') = H2pi G B' ⟨w, hw⟩ :=
      S.explicitDelta1_apply β hec hep hw hincl
    rw [hδ, QuotientAddGroup.mk'_apply, explicitCup02_mk, explicitCup01_mk]
    refine T.explicitDelta1_apply _ (e := fun g => P.pairing (x : A) (e g))
      ((continuous_of_discreteTopology (f := P.pairing (x : A))).comp' hec)
      (fun g => by rw [P.proj_pairing, hep]) _ fun g h => ?_
    rw [P.incl_pairing, hincl g h, map_add, map_sub, P.pairing_smul_right g x (e h)]

end ShortExactPairingSnd

end TauCeti.ContCohomology
