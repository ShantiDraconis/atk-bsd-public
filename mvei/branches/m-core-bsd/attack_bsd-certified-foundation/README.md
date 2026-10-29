# m-core-bsd — branch `attack/bsd-certified-foundation`

Lean sources from the branch `attack/bsd-certified-foundation` of the private repository `ShantiDraconis/m-core-bsd`, commit `405bc5a9982f082c172ebbfbc55a5b90d4787967` (2026-09-26T23:19:51+01:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 115 — closed 9, conditional 0, open 0, proof error 0, not reached 106, no result 0.
* History: 49 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `185989dd13c93794efa152a86c0e8a80b91c503e5511d972a08fe0bbebea0564`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-bsd/attack_bsd-certified-foundation/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.FF_is_closed` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:59 | nao_alcancado |
| `MCore.FT_is_closed` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:55 | nao_alcancado |
| `MCore.TF_is_closed` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:51 | nao_alcancado |
| `MCore.TT_is_closed` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:47 | nao_alcancado |
| `MCore.abstract_high_rank_open_math_closed` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:53 | nao_alcancado |
| `MCore.abstract_higher_rank_height_open_math_closed` | `lean/MCore/BSD/HigherRankHeightDomainGapClosure.lean`:25 | nao_alcancado |
| `MCore.abstract_leading_coefficient_open_math_closed` | `lean/MCore/BSD/LeadingCoefficientDomainGapClosure.lean`:24 | nao_alcancado |
| `MCore.algebraic_rank_grounding_external_version_mismatch` | `lean/MCore/BSD/F5GroundingFrontier.lean`:16 | nao_alcancado |
| `MCore.all_abstract_data_high_rank_producer_false` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:21 | nao_alcancado |
| `MCore.analytic_order_grounding_missing` | `lean/MCore/BSD/F5GroundingFrontier.lean`:21 | nao_alcancado |
| `MCore.arbitrary_maps_unconditional_claim_false` | `lean/MCore/BSD/UnconditionalRankClaim.lean`:22 | nao_alcancado |
| `MCore.arbitrary_realizability_closure_false` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:27 | nao_alcancado |
| `MCore.bsd_algebraic_grounding_not_available` | `lean/MCore/BSD/F5AnalyticGroundingAudit.lean`:56 | nao_alcancado |
| `MCore.bsd_analytic_grounding_not_available` | `lean/MCore/BSD/F5AnalyticGroundingAudit.lean`:52 | nao_alcancado |
| `MCore.bsd_analytic_order_kernel_not_available` | `lean/MCore/BSD/F5AnalyticKernelTarget.lean`:17 | nao_alcancado |
| `MCore.bsd_atk_foundation_ready` | `lean/MCore/BSD/CertifiedFoundation.lean`:36 | nao_alcancado |
| `MCore.bsd_concrete_theorem_not_enabled` | `lean/MCore/BSD/ConcreteCarrierGap.lean`:23 | nao_alcancado |
| `MCore.bsd_exact_f5_producer_count_one` | `lean/MCore/BSD/F5GroundingFrontier.lean`:40 | nao_alcancado |
| `MCore.bsd_exact_f5_producer_iff` | `lean/MCore/BSD/F5GroundingFrontier.lean`:34 | nao_alcancado |
| `MCore.bsd_f5_mathematical_closure_false` | `lean/MCore/BSD/F5GroundingFrontier.lean`:46 | nao_alcancado |
| `MCore.bsd_f5_open_math_producer_count_one` | `lean/MCore/BSD/F5AnalyticGroundingAudit.lean`:66 | nao_alcancado |
| `MCore.bsd_final_proof_ready_conditional` | `lean/MCore/BSD/BSDHabitant.lean`:61 | nao_alcancado |
| `MCore.bsd_grounded_material_producer_gaps_one` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:98 | nao_alcancado |
| `MCore.bsd_high_rank_producer_still_open` | `lean/MCore/BSD/OpenMathRankGE2.lean`:68 | fechado |
| `MCore.bsd_low_plus_high_closes_universal` | `lean/MCore/BSD/OpenMathRankGE2.lean`:30 | fechado |
| `MCore.bsd_material_producer_gaps_one` | `lean/MCore/BSD/BSDHabitant.lean`:57 | nao_alcancado |
| `MCore.bsd_mathematical_closure_not_claimed` | `lean/MCore/BSD/ProofTermGap.lean`:32 | nao_alcancado |
| `MCore.bsd_mordell_weil_rank_kernel_not_available` | `lean/MCore/BSD/F5AlgebraicKernelTarget.lean`:17 | nao_alcancado |
| `MCore.bsd_no_sorry_material_producer_count_one` | `lean/MCore/BSD/NoSorryF5Expansion.lean`:76 | nao_alcancado |
| `MCore.bsd_post_frontier_closure_enabled` | `lean/MCore/BSD/PostFrontierState.lean`:20 | nao_alcancado |
| `MCore.bsd_post_frontier_open_math_zero` | `lean/MCore/BSD/PostFrontierState.lean`:16 | nao_alcancado |
| `MCore.bsd_rank_claims_zero` | `lean/MCore/BSD/BSDHabitant.lean`:65 | nao_alcancado |
| `MCore.bsd_rank_domain_dichotomy` | `lean/MCore/BSD/OpenMathRankGE2.lean`:25 | fechado |
| `MCore.bsd_rank_equality_producer_not_available` | `lean/MCore/BSD/F5AnalyticGroundingAudit.lean`:60 | nao_alcancado |
| `MCore.bsd_rank_of_habitant` | `lean/MCore/BSD/BSDHabitant.lean`:20 | nao_alcancado |
| `MCore.bsd_realizable_high_rank_still_open` | `lean/MCore/BSD/RealizableRankFrontier.lean`:53 | nao_alcancado |
| `MCore.bsd_realizable_low_plus_high_closes_universal` | `lean/MCore/BSD/RealizableRankFrontier.lean`:25 | nao_alcancado |
| `MCore.bsd_realizable_universal_iff_high_given_low` | `lean/MCore/BSD/RealizableRankFrontier.lean`:40 | nao_alcancado |
| `MCore.bsd_realizable_universal_implies_high` | `lean/MCore/BSD/RealizableRankFrontier.lean`:34 | nao_alcancado |
| `MCore.bsd_same_carrier_rank_equality_not_available` | `lean/MCore/BSD/F5SameCarrierEquality.lean`:38 | nao_alcancado |
| `MCore.bsd_target_not_enabled_after_frontier_retirement` | `lean/MCore/BSD/PostFrontierState.lean`:24 | nao_alcancado |
| `MCore.bsd_unconditional_claim_not_enabled` | `lean/MCore/BSD/UnconditionalOneGapEndpoint.lean`:37 | nao_alcancado |
| `MCore.bsd_unconditional_infrastructure_closed` | `lean/MCore/BSD/UnconditionalOneGapEndpoint.lean`:30 | nao_alcancado |
| `MCore.bsd_unconditional_open_math_count_one` | `lean/MCore/BSD/UnconditionalOneGapEndpoint.lean`:23 | nao_alcancado |
| `MCore.bsd_universal_iff_high_given_low` | `lean/MCore/BSD/OpenMathRankGE2.lean`:54 | fechado |
| `MCore.bsd_universal_implies_high` | `lean/MCore/BSD/OpenMathRankGE2.lean`:41 | fechado |
| `MCore.bsd_universal_implies_low` | `lean/MCore/BSD/OpenMathRankGE2.lean`:48 | fechado |
| `MCore.canonical_bsd_rank_semantic_anchor_not_available` | `lean/MCore/BSD/SemanticCanonicalRankPackage.lean`:44 | nao_alcancado |
| `MCore.canonical_package_closes_rank` | `lean/MCore/BSD/CanonicalSameCurveRankPackage.lean`:14 | nao_alcancado |
| `MCore.canonical_rank_theorem_enabled_of_package` | `lean/MCore/BSD/CanonicalSameCurveRankPackage.lean`:42 | nao_alcancado |
| `MCore.canonical_same_curve_rank_maps_not_available` | `lean/MCore/BSD/SameCurveRankMaps.lean`:39 | nao_alcancado |
| `MCore.canonical_same_curve_rank_package_not_available` | `lean/MCore/BSD/CanonicalSameCurveRankPackage.lean`:34 | nao_alcancado |
| `MCore.certified_foundation_frontier_zero` | `lean/MCore/BSD/CertifiedFoundation.lean`:27 | nao_alcancado |
| `MCore.classical_bsd_reuse_closed_negative_provenance` | `lean/MCore/BSD/F5AnalyticGroundingAudit.lean`:19 | nao_alcancado |
| `MCore.closed_iff_distance_zero` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:63 | nao_alcancado |
| `MCore.closed_implies_100_percent` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:67 | nao_alcancado |
| `MCore.closure_theorem_does_not_promote_bsd` | `lean/MCore/BSD/OpenMathClosureCertificate.lean`:34 | nao_alcancado |
| `MCore.concrete_carrier_blocker_classified` | `lean/MCore/BSD/ConcreteCarrierGap.lean`:31 | nao_alcancado |
| `MCore.concrete_higher_rank_height_theorem_not_enabled` | `lean/MCore/BSD/HigherRankHeightDomainGapClosure.lean`:33 | nao_alcancado |
| `MCore.concrete_leading_coefficient_theorem_not_enabled` | `lean/MCore/BSD/LeadingCoefficientDomainGapClosure.lean`:33 | nao_alcancado |
| `MCore.create_same_curve_rank_theorem` | `lean/MCore/BSD/SameCurveRankTheoremFactory.lean`:35 | nao_alcancado |
| `MCore.current_abstract_high_rank_route_closed_negative` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:47 | nao_alcancado |
| `MCore.current_bsd_concrete_carrier_missing` | `lean/MCore/BSD/ConcreteCarrierGap.lean`:15 | nao_alcancado |
| `MCore.current_bsd_frontier_closure_theorem_enabled` | `lean/MCore/BSD/ExternalRouteClosure.lean`:39 | nao_alcancado |
| `MCore.current_bsd_frontier_open_math_count_zero` | `lean/MCore/BSD/ExternalRouteClosure.lean`:33 | nao_alcancado |
| `MCore.current_bsd_proof_term_missing` | `lean/MCore/BSD/ProofTermGap.lean`:14 | nao_alcancado |
| `MCore.current_higher_rank_height_route_closed_negative` | `lean/MCore/BSD/HigherRankHeightDomainGapClosure.lean`:16 | nao_alcancado |
| `MCore.current_leading_coefficient_route_closed_negative` | `lean/MCore/BSD/LeadingCoefficientDomainGapClosure.lean`:16 | nao_alcancado |
| `MCore.directional_mathematics_not_available` | `lean/MCore/BSD/SameCurveRankTheoremFactory.lean`:54 | nao_alcancado |
| `MCore.exact_unconditional_certificate_still_open` | `lean/MCore/BSD/UnconditionalProducerAudit.lean`:37 | nao_alcancado |
| `MCore.exact_unconditional_enable_gate` | `lean/MCore/BSD/UnconditionalProducerAudit.lean`:29 | nao_alcancado |
| `MCore.external_classical_bsd_algebraic_rank_rejected` | `lean/MCore/BSD/NoSorryF5Expansion.lean`:36 | nao_alcancado |
| `MCore.external_classical_bsd_known_cases_rejected` | `lean/MCore/BSD/NoSorryF5Expansion.lean`:40 | nao_alcancado |
| `MCore.external_classical_bsd_proof_reuse_rejected` | `lean/MCore/BSD/NoSorryF5Expansion.lean`:32 | nao_alcancado |
| `MCore.frontier_closure_theorem` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:82 | nao_alcancado |
| `MCore.grounded_bsd_habitant_not_available` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:92 | nao_alcancado |
| `MCore.grounded_bsd_of_habitant` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:59 | nao_alcancado |
| `MCore.grounded_habitant_has_analytic_semantics` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:66 | nao_alcancado |
| `MCore.grounded_habitant_has_mordell_weil_semantics` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:76 | nao_alcancado |
| `MCore.grounded_rank_defect_zero` | `lean/MCore/BSD/GroundedBSDHabitant.lean`:53 | nao_alcancado |
| `MCore.highRankMismatchData_is_high` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:9 | nao_alcancado |
| `MCore.highRankMismatchData_not_rank_part` | `lean/MCore/BSD/HighRankDomainGapClosure.lean`:13 | nao_alcancado |
| `MCore.legacy_directional_certificates_cannot_close_current_claim` | `lean/MCore/BSD/UnconditionalProducerAudit.lean`:22 | nao_alcancado |
| `MCore.legacy_to_canonical_bridge_not_available` | `lean/MCore/BSD/CanonicalSameCurveRankPackage.lean`:27 | nao_alcancado |
| `MCore.map_only_package_not_promotable_to_bsd` | `lean/MCore/BSD/SemanticCanonicalRankPackage.lean`:37 | nao_alcancado |
| `MCore.mismatch_same_curve_statement_false` | `lean/MCore/BSD/UnconditionalRankClaim.lean`:16 | nao_alcancado |
| `MCore.no_sorry_kernel_target_closes_f5` | `lean/MCore/BSD/NoSorryF5Expansion.lean`:68 | nao_alcancado |
| `MCore.nonzero_force_resolves_branch` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:109 | nao_alcancado |
| `MCore.one_open_is_50_percent` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:73 | nao_alcancado |
| `MCore.open_math_closure_theorem_enabled` | `lean/MCore/BSD/OpenMathClosureCertificate.lean`:26 | nao_alcancado |
| `MCore.open_open_is_0_percent` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:78 | nao_alcancado |
| `MCore.penchev_agpp_universalization_closed_negative` | `lean/MCore/BSD/ExternalRouteClosure.lean`:15 | nao_alcancado |
| `MCore.penchev_prc_closed_negative_for_promotion` | `lean/MCore/BSD/ExternalRouteClosure.lean`:25 | nao_alcancado |
| `MCore.post_frontier_gate_closed` | `lean/MCore/BSD/ProofTermGap.lean`:26 | nao_alcancado |
| `MCore.post_frontier_hard_atomic_zero` | `lean/MCore/BSD/ProofTermGap.lean`:20 | nao_alcancado |
| `MCore.rankOrderMismatchData_not_BSDRankPart` | `lean/MCore/BSDUniversalCountermodel.lean`:11 | fechado |
| `MCore.rank_defect_vanishing_closes_rank` | `lean/MCore/BSD/BSDHabitant.lean`:40 | nao_alcancado |
| `MCore.rank_defect_zero` | `lean/MCore/BSD/BSDHabitant.lean`:27 | nao_alcancado |
| `MCore.restricted_bsd_rank_theorem_not_enabled` | `lean/MCore/BSD/SameCurveRankMaps.lean`:45 | nao_alcancado |
| `MCore.same_carrier_rank_equality_closes_f5` | `lean/MCore/BSD/F5SameCarrierEquality.lean`:30 | nao_alcancado |
| `MCore.same_curve_rank_part_iff` | `lean/MCore/BSD/ShortWeierstrassCurveQ.lean`:31 | nao_alcancado |
| `MCore.same_curve_rank_statement_of_directions` | `lean/MCore/BSD/SameCurveRankTheoremFactory.lean`:18 | nao_alcancado |
| `MCore.same_curve_rank_theorem_factory_enabled` | `lean/MCore/BSD/SameCurveRankTheoremFactory.lean`:48 | nao_alcancado |
| `MCore.same_curve_rank_theorem_not_enabled` | `lean/MCore/BSD/ShortWeierstrassCurveQ.lean`:45 | nao_alcancado |
| `MCore.same_curve_rank_theorem_of_certificate` | `lean/MCore/BSD/SameCurveRankMaps.lean`:30 | nao_alcancado |
| `MCore.same_curve_statement_iff_rank_part` | `lean/MCore/BSD/SameCurveRankMaps.lean`:21 | nao_alcancado |
| `MCore.semantic_canonical_package_closes_rank` | `lean/MCore/BSD/SemanticCanonicalRankPackage.lean`:25 | nao_alcancado |
| `MCore.semantic_unconditional_bsd_rank_claim_not_enabled` | `lean/MCore/BSD/SemanticCanonicalRankPackage.lean`:51 | nao_alcancado |
| `MCore.short_weierstrass_concrete_carrier_enabled` | `lean/MCore/BSD/ShortWeierstrassCurveQ.lean`:38 | nao_alcancado |
| `MCore.two_nonzero_forces_close_open_math` | `lean/MCore/BSD/OpenMathClosureGeometry.lean`:118 | nao_alcancado |
| `MCore.unconditional_certificate_closes_open_math` | `lean/MCore/BSD/UnconditionalOneGapEndpoint.lean`:13 | nao_alcancado |
| `MCore.unconditional_claim_closes_rank` | `lean/MCore/BSD/UnconditionalRankClaim.lean`:34 | nao_alcancado |
| `MCore.unconditional_rank_claim_certificate_not_available` | `lean/MCore/BSD/UnconditionalRankClaim.lean`:45 | nao_alcancado |
| `MCore.universal_abstract_BSDRankPart_false` | `lean/MCore/BSDUniversalCountermodel.lean`:16 | fechado |
| `MCore.unrestricted_not_a_valid_terminal_producer` | `lean/MCore/BSDUniversalCountermodel.lean`:30 | fechado |
