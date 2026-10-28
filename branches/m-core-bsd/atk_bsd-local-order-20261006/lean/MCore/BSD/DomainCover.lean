import MCore.BSD.CertifiedPrefixReuse

namespace MCore.BSD

universe u

/-- A family of mathematically meaningful subdomains of genuine elliptic curves.
Each piece is represented by an exact predicate on EllipticCurveQ. -/
structure CurveDomainCover where
  Piece : Type u
  contains : Piece → EllipticCurveQ → Prop
  covers : ∀ E : EllipticCurveQ, ∃ i : Piece, contains i E

/-- Rank equality proved piecewise on an exact domain cover. -/
structure PiecewiseRankProducer
    (M : ConcreteBSDModel) (C : CurveDomainCover) where
  rankProof :
    ∀ i : C.Piece, ∀ E : EllipticCurveQ,
      C.contains i E →
      M.analyticOrderAtOne E = M.mordellWeilRank E

/-- Refined BSD identity proved piecewise on the same exact domain cover. -/
structure PiecewiseRefinedProducer
    (M : ConcreteBSDModel) (C : CurveDomainCover) where
  refinedProof :
    ∀ i : C.Piece, ∀ E : EllipticCurveQ,
      C.contains i E →
      RefinedBSDIdentity (M.refinedData E)

/-- Exact assembly of a piecewise rank proof into the universal rank producer.
The only globalization input is C.covers. -/
def PiecewiseRankProducer.toUniversal
    {M : ConcreteBSDModel} {C : CurveDomainCover}
    (P : PiecewiseRankProducer M C) :
    ConcreteBSDRankProducer M :=
  { rankProof := fun E _ =>
      let h := C.covers E
      match h with
      | ⟨i, hi⟩ => P.rankProof i E hi }

/-- Exact assembly of a piecewise refined proof into the universal refined
producer, again using only the explicit cover theorem. -/
def PiecewiseRefinedProducer.toUniversal
    {M : ConcreteBSDModel} {C : CurveDomainCover}
    (P : PiecewiseRefinedProducer M C) :
    ConcreteBSDRefinedProducer M :=
  { refinedProof := fun E _ =>
      let h := C.covers E
      match h with
      | ⟨i, hi⟩ => P.refinedProof i E hi }

/-- Full terminal assembly from piecewise results on one common exhaustive
cover.  No finite or restricted family can pass this theorem without a proof
of C.covers. -/
def assembleFromExhaustiveCover
    {M : ConcreteBSDModel} {C : CurveDomainCover}
    (R : PiecewiseRankProducer M C)
    (F : PiecewiseRefinedProducer M C) :
    ConcreteBSDProducer M :=
  combine R.toUniversal F.toUniversal

/-- Nonempty-level form for certificate registries. -/
theorem exhaustive_cover_sufficient
    {M : ConcreteBSDModel} {C : CurveDomainCover}
    (hR : Nonempty (PiecewiseRankProducer M C))
    (hF : Nonempty (PiecewiseRefinedProducer M C)) :
    Nonempty (ConcreteBSDProducer M) := by
  rcases hR with ⟨R⟩
  rcases hF with ⟨F⟩
  exact ⟨assembleFromExhaustiveCover R F⟩

end MCore.BSD
