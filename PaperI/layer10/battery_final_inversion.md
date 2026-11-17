# leancheck — final_inversion (2026-11-10 17:20 UTC)

- path: /Users/john/final_inversion
- HEAD: c71abb76b265d660ae2d73b629beac2c338c8b27
- uncommitted entries:        0

## Layers 1-2 — gate and tamper
```
'Inversion.bridge_cross_iff_collinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'Inversion.bridge_peaucellier_collinear' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS (84 declarations, standard axioms only)
ok    sorry     rejected (exit 1): FAIL: forbidden token
ok    ax2line   rejected (exit 1): FAIL: forbidden token
ok    evalfake  rejected (exit 1): FAIL: forbidden token
ok    macro     rejected (exit 1): FAIL: forbidden token
ok    wrap      rejected (exit 1): FAIL: nonstandard axioms: Inversion.zz_extra_axiom_with_a_long_name_for_the_negative_gate_test
ok    falsehyp  rejected (exit 1): FAIL: build
ok    falsehyp2 rejected (exit 1): FAIL: build
ok    falsehyp3 rejected (exit 1): FAIL: build
ok    falsestmt rejected (exit 1): FAIL: build
ALL TAMPERING TESTS REJECTED
```
## Layers 4,5,8 — mutations, contradiction probe, satisfiability
# Lean statement audit (jack)

Generated 2026-11-10 10:00 PST

## TOTAL (per repo, duplicates counted in each repo)
{"thm": 87, "mut": 272, "killed": 268, "surv": 4, "tout": 0, "contra": 0, "sat": 55, "unres": 32, "nohyp": 0, "invalid": 0}

Baseline failures (files skipped): 0

## final_inversion
- theorems: 87
- step 1 mutants: 272 | killed 268 | killed-timeout 0 | SURVIVED 4 | unattributed 0
- step 2a contradiction probe: CONTRADICTORY 0 | ok 57 | no-hyp 30 | invalid 0 | timeout 0
- step 2b satisfiable: CERTIFIED 55 | unresolved 32 | stmt-invalid 0 | llm-error 0
- step 2b+ satisfiable by linked hand-written witness (separate from CERTIFIED): 0 [0 of them not certified by step 2b] | rejected claims 0
  - SURVIVED detail: 
  - SURVIVOR `l14w_ptolemy_inequality` [lit0->1@15]: `(3 : ℂ) ≠ 0 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(` -> `(3 : ℂ) ≠ 1 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(`
  - SURVIVED detail: 
  - SURVIVOR `l14w_ptolemy_inequality` [lit3->4@6]: `(3 : ℂ) ≠ 0 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(` -> `(4 : ℂ) ≠ 0 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(`
  - SURVIVED detail: 
  - SURVIVOR `l14w_ptolemy_inequality` [lit0->1@21]: `(3 : ℂ) ≠ 0 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(` -> `(3 : ℂ) ≠ 0 ∧ (⟨1, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(`
  - SURVIVED detail: 
  - SURVIVOR `l14w_apollonian_integral` [neg1->1@40]: `((-1 : ℤ) + 2 + 2 + 3) ^ 2 - 2 * ((-1) ^ 2 + 2 ^ 2 + 2 ^ 2 + 3 ^ 2) = 0 ∧
    (2 : ℤ) * (2 + 2 + 3) - (-1) = 15` -> `((-1 : ℤ) + 2 + 2 + 3) ^ 2 - 2 * ((1) ^ 2 + 2 ^ 2 + 2 ^ 2 + 3 ^ 2) = 0 ∧
    (2 : ℤ) * (2 + 2 + 3) - (-1) = 15`
  - needs manual satisfiability check: `bridge_descartes_classical` (unresolved)
  - needs manual satisfiability check: `bridge_apolloMove` (unresolved)
  - needs manual satisfiability check: `descartes` (unresolved)
  - needs manual satisfiability check: `soddy` (unresolved)
  - needs manual satisfiability check: `descartes_vieta` (unresolved)
  - needs manual satisfiability check: `descartes_reflect` (unresolved)
  - needs manual satisfiability check: `isDescartes_apolloMove` (unresolved)
  - needs manual satisfiability check: `apollonian_integral` (unresolved)
  - needs manual satisfiability check: `isDescartes_foldr` (unresolved)
  - needs manual satisfiability check: `l14_dist_sq_invPt` (unresolved)
  - needs manual satisfiability check: `l14_ptolemy_iff_dist_add_dist_invPt` (unresolved)
  - needs manual satisfiability check: `l14_ptolemy_inequality` (unresolved)
  - needs manual satisfiability check: `l14_collinear_invPt_of_concyclic` (unresolved)
  - needs manual satisfiability check: `l14_ptolemy_concyclic` (unresolved)
  - needs manual satisfiability check: `l14_peaucellier` (unresolved)
  - needs manual satisfiability check: `l14_peaucellier_classic` (unresolved)
  - needs manual satisfiability check: `l14_peaucellier_classic_line` (unresolved)
  - needs manual satisfiability check: `l14_peaucellier_line` (unresolved)
  - needs manual satisfiability check: `l14_descartes` (unresolved)
  - needs manual satisfiability check: `l14_soddy` (unresolved)
  - needs manual satisfiability check: `l14_descartes_vieta` (unresolved)
  - needs manual satisfiability check: `l14_apollonian_integral` (unresolved)
  - needs manual satisfiability check: `l14h_norm` (unresolved)
  - needs manual satisfiability check: `peaucellier_add` (unresolved)
  - needs manual satisfiability check: `peaucellier_inner` (unresolved)
  - needs manual satisfiability check: `peaucellier_collinear` (unresolved)
  - needs manual satisfiability check: `peaucellier` (unresolved)
  - needs manual satisfiability check: `peaucellier_classic` (unresolved)
  - needs manual satisfiability check: `peaucellier_line` (unresolved)
  - needs manual satisfiability check: `peaucellier_classic_line` (unresolved)
  - needs manual satisfiability check: `collinear_invPt_of_concyclic` (unresolved)
  - needs manual satisfiability check: `ptolemy_concyclic` (unresolved)
  - no mutants generated (manual look): collinear_invPt_of_concyclic, isDescartes_apolloMove, isDescartes_foldr, l14w_descartes, l14w_peaucellier, l14w_peaucellier_classic, l14w_ptolemy_concyclic

## Layers 6,9 — hypothesis ablation and bridge inventory
# gap checks (ablation + bridge inventory)

## hypothesis ablation
jobs 257 | UNUSED 1 | NEEDED 256 | SKIP 0 | timeout 0 | bad-control decls 0

- UNUSED `bridge_intTangent` : `(h₂ : r₂ < 0)`

see inventory.md for the definition table
## Layer 7 — unused-variable linter
linter (library): 0 warnings in 6 files
linter (scratch): 0 warnings in 1 files

## Verdict
| check | result |
|---|---|
| gate (layer 1) | PASS (84 declarations, standard axioms only) |
| tamper (layer 2) | 9/9 planted defects rejected, ALL TAMPERING TESTS REJECTED |
| baseline build | 6 of 6 files ok |
| conclusion mutations (layer 4) | **268/272 rejected** (268 by error, 0 by timeout/heartbeat); 4 SURVIVED, 0 unattributed |
| contradiction probe (layer 5) | 0 contradictory, 57 probed ok — no-hyp 30 |
| satisfiability (layer 8) | 55/87 certified [21 with hypotheses, 25 hypothesis-free binders, 9 closed], 32 unresolved, 0 stmt-invalid |
| satisfiability by linked hand-written witness (layer 8b, separate) | 0 theorems linked (0 not certified by layer 8); 0 rejected claims; layer 8 + 8b: 55/87 credited, 32 unresolved |
| hypothesis ablation (layer 6) | 256 needed, **1 unused**, 0 skipped, 0 timeout; bad controls 0 |
| linter, library (layer 7) | 0 warnings in 6 files |
| linter, scratch (layer 7) | 0 warnings in 1 files |
| bridge inventory (layer 9) | 10 notions, 1 has-bridge, 9 NO-BRIDGE (see inventory.md) |

unused hypotheses (check each by hand): `bridge_intTangent`: (h₂ : r₂ < 0)

mutation survivors (classify by hand): `l14w_ptolemy_inequality` [lit0->1@15] ; `l14w_ptolemy_inequality` [lit3->4@6] ; `l14w_ptolemy_inequality` [lit0->1@21] ; `l14w_apollonian_integral` [neg1->1@40] 

satisfiability not certified (recorded as unresolved, not success): `bridge_descartes_classical` (unresolved), `bridge_apolloMove` (unresolved), `descartes` (unresolved), `soddy` (unresolved), `descartes_vieta` (unresolved), `descartes_reflect` (unresolved), `isDescartes_apolloMove` (unresolved), `apollonian_integral` (unresolved), `isDescartes_foldr` (unresolved), `l14_dist_sq_invPt` (unresolved), `l14_ptolemy_iff_dist_add_dist_invPt` (unresolved), `l14_ptolemy_inequality` (unresolved), `l14_collinear_invPt_of_concyclic` (unresolved), `l14_ptolemy_concyclic` (unresolved), `l14_peaucellier` (unresolved), `l14_peaucellier_classic` (unresolved), `l14_peaucellier_classic_line` (unresolved), `l14_peaucellier_line` (unresolved), `l14_descartes` (unresolved), `l14_soddy` (unresolved), `l14_descartes_vieta` (unresolved), `l14_apollonian_integral` (unresolved), `l14h_norm` (unresolved), `peaucellier_add` (unresolved), `peaucellier_inner` (unresolved), `peaucellier_collinear` (unresolved), `peaucellier` (unresolved), `peaucellier_classic` (unresolved), `peaucellier_line` (unresolved), `peaucellier_classic_line` (unresolved)
LEANCHECK DONE Tue Nov 10 18:22:21 UTC 2026
