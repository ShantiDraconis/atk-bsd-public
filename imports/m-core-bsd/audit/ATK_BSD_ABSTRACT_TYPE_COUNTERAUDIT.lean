import MCore.K12

namespace MCore

/--
Counter-audit for the current abstract BSD rank interface.

`BSDArithmeticAnalyticData` is currently just a pair of natural numbers.
Therefore the universal proposition
  ∀ d : BSDArithmeticAnalyticData, BSDRankPart d
is false as stated: arbitrary unrelated naturals need not be equal.

This does NOT refute BSD. It proves that the current abstract interface is too
broad to serve as the terminal producer for BSD without a realization predicate
tying the fields to an actual elliptic curve and its L-function.
-/
def abstractRankCounterexample : BSDArithmeticAnalyticData :=
  { mordellWeilRank := 0
    analyticOrderAtOne := 1 }

theorem abstractRankCounterexample_not_rankPart :
    ¬ BSDRankPart abstractRankCounterexample := by
  decide

theorem no_universal_rank_part_over_arbitrary_data :
    ¬ (∀ d : BSDArithmeticAnalyticData, BSDRankPart d) := by
  intro h
  exact abstractRankCounterexample_not_rankPart (h abstractRankCounterexample)

#print axioms MCore.abstractRankCounterexample_not_rankPart
#print axioms MCore.no_universal_rank_part_over_arbitrary_data

end MCore
