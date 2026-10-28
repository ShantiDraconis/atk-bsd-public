import open_math.P06_MordellWeil_DescentForcing
import Mathlib.GroupTheory.Index

namespace P06.BSD.OpenMath

/-
Constructive weak Mordell-Weil producer.

A producer is not merely the proposition that E(Q)/2E(Q) is finite.  It must
supply a finite list of representatives and an explicit decomposition of every
rational point as representative + twice another rational point.
-/

/-- Finite representatives for E(Q) modulo doubling. -/
structure DoublingRepresentativeSystem (E : EllipticCurveQ) where
  reps : Finset (RationalPointGroup E)
  cover :
    ∀ P : RationalPointGroup E,
      ∃ r ∈ reps, ∃ Q : RationalPointGroup E,
        P = r + 2 • Q

/-- The quotient map restricted to the supplied finite representatives. -/
noncomputable def doublingRepresentativeQuotientMap
    {E : EllipticCurveQ}
    (R : DoublingRepresentativeSystem E) :
    {r : RationalPointGroup E // r ∈ R.reps} →
      (RationalPointGroup E ⧸ DoublingImage E) :=
  fun r => (r.1 : RationalPointGroup E ⧸ DoublingImage E)

/-- Coverage of representatives gives surjectivity onto E(Q)/2E(Q). -/
theorem doublingRepresentativeQuotientMap_surjective
    {E : EllipticCurveQ}
    (R : DoublingRepresentativeSystem E) :
    Function.Surjective (doublingRepresentativeQuotientMap R) := by
  intro q
  obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨r, hr, Q, hP⟩ := R.cover P
  refine ⟨⟨r, hr⟩, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [hP]
  have hEq :
      r - (r + 2 • Q) = -(2 • Q) := by
    abel
  rw [hEq]
  change -(2 • Q) ∈
    (nsmulAddMonoidHom (α := RationalPointGroup E) 2).range
  exact ⟨-Q, by simp⟩

/-- A finite representative system makes the doubling quotient finite. -/
theorem finite_doublingQuotient_of_representatives
    {E : EllipticCurveQ}
    (R : DoublingRepresentativeSystem E) :
    Finite (RationalPointGroup E ⧸ DoublingImage E) := by
  let f := doublingRepresentativeQuotientMap R
  exact Finite.of_surjective f (doublingRepresentativeQuotientMap_surjective R)

/-- Constructive representatives imply the exact finite-index input consumed by
Mordell-Weil descent. -/
theorem doublingFiniteIndex_of_representatives
    {E : EllipticCurveQ}
    (R : DoublingRepresentativeSystem E) :
    MordellWeilDoublingFiniteIndex E := by
  letI : Finite (RationalPointGroup E ⧸ DoublingImage E) :=
    finite_doublingQuotient_of_representatives R
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- Universal constructive producer: one finite representative system for every
elliptic curve over Q. -/
def WeakMordellWeilProducer : Type :=
  ∀ E : EllipticCurveQ, DoublingRepresentativeSystem E

/-- A genuine weak Mordell-Weil producer closes the whole doubling-index stage
mechanically. -/
theorem weakMordellWeilProducer_to_descent
    (W : WeakMordellWeilProducer) :
    MordellWeilDescentProducer := by
  intro E
  exact doublingFiniteIndex_of_representatives (W E)

/-- In the pinned v4.19 dependency this is the final mechanically certified
endpoint.  Finite generation requires additional elliptic-height/descent
machinery absent from the pin. -/
theorem weakMordellWeilProducer_to_finiteIndex
    (W : WeakMordellWeilProducer) :
    ∀ E : EllipticCurveQ, MordellWeilDoublingFiniteIndex E := by
  intro E
  exact doublingFiniteIndex_of_representatives (W E)

#check DoublingRepresentativeSystem
#check doublingRepresentativeQuotientMap_surjective
#check finite_doublingQuotient_of_representatives
#check doublingFiniteIndex_of_representatives
#check WeakMordellWeilProducer
#check weakMordellWeilProducer_to_descent
#check weakMordellWeilProducer_to_finiteIndex

end P06.BSD.OpenMath
