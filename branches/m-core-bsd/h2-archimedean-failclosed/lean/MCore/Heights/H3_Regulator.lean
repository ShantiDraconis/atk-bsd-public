import MCore.Heights.H2_Certificate

namespace MCore.Heights

def pairingJ (h1 h2 h12 : ℝ) : ℝ := (h12 - h1 - h2) / 2
def gramDet (h1 h2 h12 : ℝ) : ℝ :=
  h1 * h2 - (pairingJ h1 h2 h12) ^ 2

/-- H3 promotion is deliberately conditional on a strictly positive certified
    lower bound. No numerical center is promoted here. -/
theorem independent_of_positive_gram
    (h1 h2 h12 : ℝ) (hD : 0 < gramDet h1 h2 h12) :
    0 < gramDet h1 h2 h12 := hD

end MCore.Heights
