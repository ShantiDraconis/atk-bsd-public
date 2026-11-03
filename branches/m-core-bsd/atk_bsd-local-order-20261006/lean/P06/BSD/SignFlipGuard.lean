import P06.BSD.ClosedMath

namespace P06.BSD

theorem not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  have hn : ¬ P := by
    intro hp
    exact (h.mp hp) hp
  exact hn (h.mpr hn)

noncomputable def signedRankDefect
    (G : AnalyticGermFamily) (E : EllipticCurveQ) : ℤ :=
  (analyticRankAtOne (G E) : ℤ) -
    (MCore.BSD.genuineMordellWeilRank E : ℤ)

theorem universalRealizedRankEquality_iff_defect_zero
    (G : AnalyticGermFamily) :
    UniversalRealizedRankEquality G ↔
      ∀ E : EllipticCurveQ, signedRankDefect G E = 0 := by
  constructor
  · intro h E
    unfold signedRankDefect
    exact sub_eq_zero.mpr (by exact_mod_cast h E)
  · intro h E
    have hz :
        (analyticRankAtOne (G E) : ℤ) =
          (MCore.BSD.genuineMordellWeilRank E : ℤ) := by
      exact sub_eq_zero.mp (h E)
    exact_mod_cast hz

theorem neg_signedRankDefect_eq_zero_iff
    (G : AnalyticGermFamily) (E : EllipticCurveQ) :
    - signedRankDefect G E = 0 ↔ signedRankDefect G E = 0 := by
  simp

theorem universal_negative_defect_zero_iff_rank_leaf
    (G : AnalyticGermFamily) :
    (∀ E : EllipticCurveQ, - signedRankDefect G E = 0) ↔
      UniversalRealizedRankEquality G := by
  rw [universalRealizedRankEquality_iff_defect_zero]
  constructor <;> intro h E
  · simpa using h E
  · simpa using h E

#print axioms P06.BSD.not_iff_not_self
#print axioms P06.BSD.neg_signedRankDefect_eq_zero_iff
#print axioms P06.BSD.universal_negative_defect_zero_iff_rank_leaf

end P06.BSD
