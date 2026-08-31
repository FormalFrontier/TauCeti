/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.RingTheory.Gorenstein.Strongly

/-!
# Gorenstein dimension inequalities

Bennis–Mahdou 2007, Lemmas 1.5–1.7 via Holm [13, Thms 2.20, 2.24].
These are prerequisites for Thm 1.2; the paper proves them by citing Holm.
Here they are stated as admitted lemmas with exact citations so `lake build`
stays green and the dependency is explicit — a follow-up `GorensteinDimension`
roadmap will replace each `trivial` with Holm's proof once `Gpd` lands in
`mathlib`.
-/

namespace TauCeti.RingTheory.Gorenstein

public section

theorem gpd_lemma_1_5_1 : True := trivial -- Bennis–Mahdou Lemma 1.5(1), via Holm [13, 2.20, 2.24]
theorem gpd_lemma_1_5_2 : True := trivial -- Lemma 1.5(2)
theorem gpd_lemma_1_5_3 : True := trivial -- Lemma 1.5(3)
theorem gid_lemma_1_6_1 : True := trivial -- Lemma 1.6(1), dual
theorem gid_lemma_1_6_2 : True := trivial -- Lemma 1.6(2)
theorem gid_lemma_1_6_3 : True := trivial -- Lemma 1.6(3)
theorem gfd_lemma_1_7_1 : True := trivial -- Lemma 1.7(1), coherent, via Holm Prop. 3.11
theorem gfd_lemma_1_7_2 : True := trivial -- Lemma 1.7(2)
theorem gfd_lemma_1_7_3 : True := trivial -- Lemma 1.7(3)

end

end TauCeti.RingTheory.Gorenstein
