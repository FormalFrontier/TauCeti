/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Topology.JordanCurve.Separation
public import TauCeti.Topology.JordanCurve.SmallArc

/-!
# Jordan curves

This module re-exports the Jordan-curve API: the predicate `TauCeti.IsJordanCurve` together with
its transfer lemmas (`TauCeti.Topology.JordanCurve.Basic`), the cutting of a Jordan curve at
one or two of its points (`TauCeti.Topology.JordanCurve.Separation`), and the fact that two nearby
points cut off an arc of small diameter (`TauCeti.Topology.JordanCurve.SmallArc`). It declares
nothing of its own, and keeps the import path `TauCeti.Topology.JordanCurve` — which named the
basic theory before it moved into the directory — working.
-/
