import MCore.K0

namespace MCore.BSDUniversalFirewall

/-!
D01 universal-endpoint firewall.

A finite or curve-specific verification cannot by pure logic be promoted to a
universal BSD statement.  The Boolean countermodel below machine-checks that
"verified on the sampled family" does not imply "verified for every object".

This is a promotion firewall only; it says nothing against any genuine
curve-specific BSD certificate.
-/

def Formula (x : Bool) : Prop := x = false

theorem sampled_case_passes :
    ∀ x ∈ ([false] : List Bool), Formula x := by
  intro x hx
  simp at hx
  simpa [Formula, hx]

theorem universal_formula_fails :
    ¬ ∀ x : Bool, Formula x := by
  intro h
  have ht := h true
  simp [Formula] at ht

theorem finite_sample_does_not_force_universal :
    ¬ ((∀ x ∈ ([false] : List Bool), Formula x) →
       (∀ x : Bool, Formula x)) := by
  intro h
  exact universal_formula_fails (h sampled_case_passes)

#print axioms MCore.BSDUniversalFirewall.sampled_case_passes
#print axioms MCore.BSDUniversalFirewall.universal_formula_fails
#print axioms MCore.BSDUniversalFirewall.finite_sample_does_not_force_universal

end MCore.BSDUniversalFirewall
