import MCore.ExactFinalProducer

namespace MCore
namespace BSDFinal

/-- Rank consequence of a universal final certificate, on the same curve carrier. -/
theorem finalExternal_rank
    {Curve Scalar : Type}
    (C : FinalExternalCertificate Curve Scalar)
    (E : Curve) :
    ((C.1).state E).analyticOrderAtOne =
      ((C.1).state E).algebraicRank :=
  (C.2 E).rank.proof

/-- Finiteness/positivity witness for Sha carried by the same state. -/
theorem finalExternal_sha
    {Curve Scalar : Type}
    (C : FinalExternalCertificate Curve Scalar)
    (E : Curve) :
    0 < ((C.1).state E).shaOrder :=
  (C.2 E).sha.proof

/-- Refined leading-coefficient identity on the same normalization/carrier. -/
theorem finalExternal_leading
    {Curve Scalar : Type}
    (C : FinalExternalCertificate Curve Scalar)
    (E : Curve) :
    ((C.1).state E).leadingCoefficient =
      bsdArithmeticSide (C.1).algebra ((C.1).state E) :=
  (C.2 E).leading.proof

/-- Height/regulator compatibility is retained explicitly. -/
def finalExternal_height
    {Curve Scalar : Type}
    (C : FinalExternalCertificate Curve Scalar)
    (E : Curve) :
    BSDHeightCertificate ((C.1).state E) :=
  (C.2 E).height

#print axioms MCore.BSDFinal.finalExternal_rank
#print axioms MCore.BSDFinal.finalExternal_sha
#print axioms MCore.BSDFinal.finalExternal_leading

end BSDFinal
end MCore
