import MCore

open MCore

namespace MCore.StableHoleExtraction

/-- The current BSDRealizableFamily type does not itself enforce semantic
    elliptic-curve realizability: its toData map is unrestricted. -/
def mismatchFamily : BSDRealizableFamily :=
  { Curve := Unit
    toData := fun _ => rankOrderMismatchData }

theorem mismatch_is_in_current_family_image :
    ∃ (F : BSDRealizableFamily) (E : F.Curve),
      F.toData E = rankOrderMismatchData := by
  exact ⟨mismatchFamily, (), rfl⟩

/-- Therefore the current family wrapper still admits the already-certified
    abstract countermodel. This is a domain/fence defect, not a BSD counterexample. -/
theorem current_realizable_family_does_not_exclude_mismatch :
    ¬ BSDRankPartOnFamily mismatchFamily := by
  intro h
  exact rankOrderMismatchData_not_BSDRankPart (h ())

#print axioms MCore.StableHoleExtraction.mismatch_is_in_current_family_image
#print axioms MCore.StableHoleExtraction.current_realizable_family_does_not_exclude_mismatch

end MCore.StableHoleExtraction
