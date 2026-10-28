import open_math.P06_MordellWeil_Realization
import Mathlib.GroupTheory.Index

namespace P06.BSD.OpenMath

/-
Pinned-v4.19 weak Mordell-Weil boundary.

The pinned dependency supplies the elliptic-curve point group and finite-index
group API, but not the later elliptic-height/descent implementation.  Therefore
this file stops exactly at the finite-index statement E(Q)/2E(Q).

No claim of finite generation is made here.
-/

/-- Exact doubling image in the genuine rational-point group. -/
noncomputable def DoublingImage (E : EllipticCurveQ) : AddSubgroup (RationalPointGroup E) :=
  (nsmulAddMonoidHom (α := RationalPointGroup E) 2).range

/-- Material weak Mordell-Weil target available in the pinned API:
the doubling image has finite index. -/
def MordellWeilDoublingFiniteIndex (E : EllipticCurveQ) : Prop :=
  (DoublingImage E).FiniteIndex

/-- Universal finite-index producer.  This is the precise endpoint that can be
expressed in the pinned dependency without importing unavailable height code. -/
def MordellWeilDescentProducer : Prop :=
  ∀ E : EllipticCurveQ, MordellWeilDoublingFiniteIndex E

#check DoublingImage
#check MordellWeilDoublingFiniteIndex
#check MordellWeilDescentProducer

end P06.BSD.OpenMath
