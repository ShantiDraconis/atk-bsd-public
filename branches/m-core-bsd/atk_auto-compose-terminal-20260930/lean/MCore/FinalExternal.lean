import MCore.BSDCompositeCertificate

namespace MCore
namespace BSDFinal

abbrev FinalExternalCertificate (Curve Scalar : Type) : Type :=
  BSDUniversalCertificate Curve Scalar

def FINAL_ROOT (Curve Scalar : Type) : Type :=
  BSDUniversalCertificate Curve Scalar

def finalExternal_to_FINAL_ROOT
    {Curve Scalar : Type}
    (E : FinalExternalCertificate Curve Scalar) :
    FINAL_ROOT Curve Scalar :=
  E

end BSDFinal
end MCore
