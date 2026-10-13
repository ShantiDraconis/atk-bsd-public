# M-Core BSD — FINAL REPRO

Status: GREEN
Repository: ShantiDraconis/m-core-bsd
Certified TOTAL commit: d24472341ce161cbb49388ef5e1379ea36ac39b2
Workflow: certificate
Workflow run: 35146718972
Job: k6
Job ID: 104964559815
Workflow conclusion: success
Frozen ref: frozen/total-green-d2447234
Date (UTC): 2026-09-16

## Verified gates

- leanprover/lean-action: success
- G0 fail-closed source hygiene: success
- Preserve K3: success
- Preserve K4-K5: success
- Build K6 dependency kernel: success
- K6 semantic axiom closure: success
- Negative K6 firewall regression: success
- G8 predictor remains non-promoting: success
- Clean reproduction: success

## Dependency/certificate chain

K0 -> K1 -> K2 -> K3 -> K4 -> K5 -> K6 -> K7 -> K8 -> K9 -> K10 -> K11 -> K12 -> K13 -> K14 -> TOTAL -> FINAL_REPRO

The individual K0-K14 certificate records are stored under CERTIFICATES/. The immutable TOTAL snapshot is frozen at `frozen/total-green-d2447234`.

## Epistemic classification

GREEN here means the repository's formal audit, build, firewall, dependency and reproducibility gates succeeded for the certified snapshot. It does not assert a proof of the Birch–Swinnerton-Dyer conjecture. The substantive BSD rank-equality content remains explicitly classified as `openBridge`; established external mathematics remains distinguished from internally proved propositions.

No previously frozen GREEN reference is moved by this certificate.