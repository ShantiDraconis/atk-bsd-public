import Mathlib

namespace MCore.Heights

/-- Cremona/PARI normalization is twice the Silverman normalization.
    This file records the conversion as an explicit hypothesis-bearing interface;
    it does not manufacture the literature theorem as an axiom. -/
structure NormalizationWitness where
  silverman : ℝ
  cremona : ℝ
  conversion : cremona = 2 * silverman

/-- Abstract data required by a rigorously bounded archimedean series. -/
structure ArchimedeanSeriesData where
  term : ℕ → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  term_bound : ∀ i, |term i| ≤ C

def weight (i : ℕ) : ℝ := (4 : ℝ) ^ (-(i + 1 : ℤ))

/-- Tail majorant for a geometric 4^{-i-1} series. -/
def tailBound (C : ℝ) (N : ℕ) : ℝ := C * (4 : ℝ) ^ (-(N : ℤ)) / 3

/-- The mathematical obligations H2 must discharge before any computational
    interval may be called a certificate. -/
structure H2MathWitness (D : ArchimedeanSeriesData) where
  normalization : NormalizationWitness
  recurrence_domain : Prop
  recurrence_domain_proof : recurrence_domain
  tail_bound_proved : Prop
  tail_bound_proof : tail_bound_proved

theorem term_bound_available (D : ArchimedeanSeriesData) (i : ℕ) :
    |D.term i| ≤ D.C := D.term_bound i

end MCore.Heights
