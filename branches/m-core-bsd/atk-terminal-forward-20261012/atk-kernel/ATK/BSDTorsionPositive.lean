import Mathlib

/-!
ATK BSD: structural closure of the positive-torsion-cardinality obligation.
This is a theorem about an actual finite group. It does not assert BSD.
The application to a concrete elliptic curve requires the appropriate
finite-group instance and an explicit identification with E(Q)_tors.
-/

namespace ATK.BSD

theorem torsion_card_pos (G : Type*) [Group G] [Fintype G] :
    0 < Fintype.card G := by
  exact Fintype.card_pos_iff.mpr ⟨1⟩

theorem torsion_card_ge_one (G : Type*) [Group G] [Fintype G] :
    1 ≤ Fintype.card G := by
  exact torsion_card_pos G

end ATK.BSD

#print axioms ATK.BSD.torsion_card_pos
#print axioms ATK.BSD.torsion_card_ge_one
