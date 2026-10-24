# leancheck — quadrangle (2026-10-18 23:54 UTC)

- path: /home/jack/quadrangle
- HEAD: not a git repo
- uncommitted entries: 0

## Layers 1-2 — gate and tamper
```
'QuadMiquel.poncelet_cyc' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuadMiquel.ponDen_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (94 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: QuadMiquel.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 389 | UNUSED 17 | NEEDED 372 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `circC_T4` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `circC_T3` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `circC_scaled` : `(hq : q ≠ 0)`
- UNUSED `circC_scaled` : `(hD : B * γ - β * G ≠ 0)`
- UNUSED `simF2` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF2` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF2` : `(hE : s * U - t * V - U + V ≠ 0)`
- UNUSED `simF2` : `(hu : u ≠ 0)`
- UNUSED `simF2` : `(hv : v ≠ 0)`
- UNUSED `simF3` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF3` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF3` : `(hu : u ≠ 0)`
- UNUSED `simF3` : `(huv : v - u ≠ 0)`
- UNUSED `simF4` : `(hK : V * u - U * v ≠ 0)`
- UNUSED `simF4` : `(hD : s * u - t * v - u + v ≠ 0)`
- UNUSED `simF4` : `(hu : u ≠ 0)`
- UNUSED `simF4` : `(h4 : t * v - s * u ≠ 0)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 7 files
linter (scratch): 0 warnings in 0 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (94 declarations, standard axioms only) |
| tamper (layer 2) | 6/6 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 7 of 7 files ok |
| conclusion mutations (layer 4) | **355/373 rejected** (330 by error, 25 by timeout/heartbeat); 1 SURVIVED, 17 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 128 probed ok — error-unattributed 4 no-hyp 40 |
| satisfiability (layer 8) | 0/0 certified [0 with hypotheses, 0 hypothesis-free binders, 0 closed], 0 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 0/0 credited, 0 unresolved |
| hypothesis ablation (layer 6) | 372 needed, **17 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 7 files |
| linter, scratch (layer 7) | 0 warnings in 0 files |
| bridge inventory (layer 9) | 22 notions, 3 has-bridge, 19 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `circC_T4`: (hK : V * u - U * v ≠ 0), `circC_T3`: (hK : V * u - U * v ≠ 0), `circC_scaled`: (hq : q ≠ 0), `circC_scaled`: (hD : B * γ - β * G ≠ 0), `simF2`: (hK : V * u - U * v ≠ 0), `simF2`: (hD : s * u - t * v - u + v ≠ 0), `simF2`: (hE : s * U - t * V - U + V ≠ 0), `simF2`: (hu : u ≠ 0), `simF2`: (hv : v ≠ 0), `simF3`: (hK : V * u - U * v ≠ 0), `simF3`: (hD : s * u - t * v - u + v ≠ 0), `simF3`: (hu : u ≠ 0)

mutation survivors (classify by hand): `orthocentres_not_all_eq'` [eq->ne@153] own proof compiled; downstream errors at lines [261]; `npc_eq_ninePointCircle_center` [eq->ne@15] exit 137 with no error line; `ninePointCircle_radius_eq` [eq->ne@110] exit 137 with no error line; `nineC` [lit2->3@112] exit 137 with no error line; `pedC` [eq->ne@224] exit 137 with no error line; `nine0` [eq->ne@171] exit 137 with no error line; `pD_swap` [eq->ne@16] exit 137 with no error line; `pN_swap` [eq->ne@16] exit 137 with no error line; `ndiffC` [lit2->3@40] exit 137 with no error line; `crossC_power` [eq->ne@157] exit 137 with no error line; `pedK` [eq->ne@254] exit 137 with no error line; `pedK'` [lit0->1@21] exit 137 with no error line
LEANCHECK DONE Mon Oct 19 05:43:11 AM UTC 2026
