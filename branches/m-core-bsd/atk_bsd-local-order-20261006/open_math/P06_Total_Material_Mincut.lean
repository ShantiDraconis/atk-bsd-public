import open_math.P06_AnalyticField_Independence
import open_math.P06_WeakMordellWeil_Producer
import open_math.P06_RefinedField_Independence
import open_math.P2_TorsionRealization
import P06.BSD.ConcreteBSDProducer

namespace P06.BSD.OpenMath

/-
Total material min-cut for the current pinned P06 model.

After forcing mordellWeilRank to be the actual Z-finrank of E(Q), the terminal
BSD obligations contain exactly two scientific statements:

P1:
  analytic(E) = finrank_Z E(Q)

P2:
  RefinedBSDIdentity (refined(E))

No additional structural or wiring obligations remain in this file.
-/

/-- Exact universal rank statement after arithmetic rank realization. -/
def GenuineP1Material
    (analytic : EllipticCurveQ → Nat) : Prop :=
  ∀ E : EllipticCurveQ,
    analytic E = genuineMordellWeilRank E

/-- Exact universal refined statement for an explicitly supplied refined-data
function. -/
def GenuineP2Material
    (refined : EllipticCurveQ → BSDRefinedData) : Prop :=
  ∀ E : EllipticCurveQ,
    RefinedBSDIdentity (refined E)

/-- P1 contains no further hidden material once rank is definitionally realized
as finrank_Z E(Q). -/
theorem genuineP1Material_iff_BSDP1
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData) :
    GenuineP1Material analytic ↔
      P06.BSD.BSDP1 (mordellWeilRealizedModel analytic refined) := by
  constructor
  · intro h
    exact ⟨
      { rankProof := by
          intro E hRealizable
          exact h E }⟩
  · rintro ⟨P⟩ E
    have hEq := P.rankProof E trivial
    exact
      (MCore.BSD.RealizableEllipticCurveDomain.rankEquality_iff
        ((mordellWeilRealizedModel analytic refined).toRealizableDomain) E).1
        hEq

/-- P2 likewise contains exactly the universal refined identity for the
supplied refined-data function. -/
theorem genuineP2Material_iff_BSDP2
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData) :
    GenuineP2Material refined ↔
      P06.BSD.BSDP2 (mordellWeilRealizedModel analytic refined) := by
  constructor
  · intro h
    exact ⟨
      { refinedProof := by
          intro E hRealizable
          exact h E }⟩
  · rintro ⟨P⟩ E
    exact P.refinedProof E trivial

/-- Exact terminal min-cut for the rank-realized model. -/
theorem terminal_iff_total_material
    (analytic : EllipticCurveQ → Nat)
    (refined : EllipticCurveQ → BSDRefinedData) :
    P06.BSD.BSDTerminal (mordellWeilRealizedModel analytic refined) ↔
      GenuineP1Material analytic ∧ GenuineP2Material refined := by
  rw [P06.BSD.terminal_iff_p1_and_p2]
  exact and_congr
    (genuineP1Material_iff_BSDP1 analytic refined).symm
    (genuineP2Material_iff_BSDP2 analytic refined).symm

/-- Pointwise decomposition of P1 into the already-isolated low- and
higher-analytic-order regimes. -/
theorem genuineP1Material_iff_rank0_rank1_higher
    (analytic : EllipticCurveQ → Nat) :
    GenuineP1Material analytic ↔
      (∀ E, analytic E = 0 → genuineMordellWeilRank E = 0) ∧
      (∀ E, analytic E = 1 → genuineMordellWeilRank E = 1) ∧
      (∀ E, 2 ≤ analytic E →
        analytic E = genuineMordellWeilRank E) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro E h0
      rw [← h E, h0]
    · intro E h1
      rw [← h E, h1]
    · intro E h2
      exact h E
  · rintro ⟨h0, h1, hHigher⟩ E
    rcases Nat.eq_zero_or_pos (analytic E) with hE | hPos
    · simpa [hE] using (h0 E hE).symm
    · by_cases h1E : analytic E = 1
      · simpa [h1E] using (h1 E h1E).symm
      · exact hHigher E (by omega)

/-- Exact P2 quotient split, conditional only on the positivity needed to
divide by torsionOrder.  This makes clear that positivity and the quotient
identity are separate leaves. -/
theorem genuineP2Material_of_torsion_and_quotient
    {refined : EllipticCurveQ → BSDRefinedData}
    (hTor : ∀ E, 0 < (refined E).torsionOrder)
    (hQuot : ∀ E,
      (refined E).leadingCoefficient =
        MCore.BSD.refinedRHS (refined E) /
          ((refined E).torsionOrder : ℝ)^2) :
    GenuineP2Material refined := by
  intro E
  exact
    (MCore.BSD.refinedIdentity_iff_quotient
      (refined E) (hTor E)).2 (hQuot E)

#check GenuineP1Material
#check GenuineP2Material
#check genuineP1Material_iff_BSDP1
#check genuineP2Material_iff_BSDP2
#check terminal_iff_total_material
#check genuineP1Material_iff_rank0_rank1_higher
#check genuineP2Material_of_torsion_and_quotient

end P06.BSD.OpenMath
