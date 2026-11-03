import MCore.BSDAnalyticMaterial

namespace MCore.BSDMaterialEndpointProbe

open MCore
open MCore.BSDMaterialPromotion
open MCore.BSDAnalyticMaterial

/--
Canonical full BSD material statement used by the fraud-resistant audit.
-/
abbrev ProbeBSDStatement := BSDFullMaterialPayload

/--
Promotion is mechanical only after a closed material payload is supplied.
This is a consumer, not an inhabitant.
-/
def promoteBSDMaterial
    (p : ProbeBSDStatement) :
    BSDMaterialPromotionCertificate :=
  ⟨p⟩

theorem promotedBSDMaterial_sound
    (p : ProbeBSDStatement) :
    (∀ E, BSDOpenCore
      (universalRankDatum p.analyticOrderAtOne E)) ∧
    (∀ E, p.shaFinite E) ∧
    (∀ E, BSDRefinedIdentity (p.refinedData E)) :=
  (promoteBSDMaterial p).sound

/-
A genuine full promotion must add exactly a closed declaration of the form

  def hBSD_material : ProbeBSDStatement := ...

whose term proves:
  1. universal rank equality on genuine Q-elliptic curves,
     including the analytic-order >= 2 regime;
  2. Sha finiteness on the same domain;
  3. the refined leading-coefficient BSD identity on the same domain.

No such closed term is manufactured in this structural probe.
-/

end MCore.BSDMaterialEndpointProbe
