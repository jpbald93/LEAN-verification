# Paper L — v0.3 review triage (2026-11-24)

Source: `REVIEW_gpt-6-astra_v03.md` (independent review of v0.3, `gpt-6-astra`, 2026-11-24).
Verdict MINOR REVISION; row closure 14 APPLIED / 5 PARTIAL / 0 NOT APPLIED; findings 0 MAJOR /
6 MINOR / 3 NOTE. No Lean proof changed. The five partial rows are ## 2, 5, 7, 15, 16 below; the
findings are `R-01 … R-09`.

| id | finding (short) | disposition in v0.4 | where |
|---|---|---|---|
| R-01 | §2.1 claimed the `Counter6` witness has a zero parent cross vector — **false** | Applied. The example is replaced by the §2.4 parabola tuple `2t − 2it²`, with the exact checks named (middle coordinate zero, level-5 `P₀ ≠ 0`, whole vector zero by `parent_crossVec_zero_of_mid`, all std); `Counter6` is stated not to be an instance, with its last coordinate `−238878720000`. | §2.1 |
| R-02 | corner-witness margins overstated; JSON not in the review packet | Applied in the draft: margins reported per run (recorded witness `triP` 1e-2, `cycP` 1.3e-3, transversals ≥ 1e-2; earlier looser run 0.14/0.024/0.04). The JSON is present in the artifact tree (`layer0/r25_jack/`) and named as such; the flat review packet simply did not carry `layer0/` — Appendix A now states the packet mapping. | §1.1, App. A |
| R-03 | the layer-13 provenance still put the retyping at stage 4b only; stage 4a had already replaced the payloads and dropped S5's all-n clause | Applied. `layer13/L13_COMPARE.md` gets a correction header naming `BlindCompare.lean:89–107` and the dropped S5 clause; §5.3 rewritten with the seven-row result (below). `L13_REPORT.md` corrected. | §5.3, `layer13/L13_COMPARE.md`, `L13_REPORT.md` |
| R-04 | `KP` described via an undefined `Kf`; kernel equivalence written without the nonzero-centre hypothesis | Applied. The piecewise entry formula of `KP` is displayed; `Kf`, `aOf`, `tOf` are given with lines; `KP_mulVec_eq_zero_iff` is qualified by nonzero centres, with `hc_of_genPos` and the `n = 1` counterexample stated. | §2.1 |
| R-05 | "some child `P_{k+2} = 0` … the level points coincide … circle not unique" — the cited lemma gives only finite children | Applied. The sentence now says the finite child points coincide, that a zero middle coordinate is `∞` by `EptInf`, and that `heven_of_common` builds the line; no non-uniqueness is inferred from this branch. | §2.3 |
| R-06 | two stale references: the "definite article in §2.5" and the "0/0 row in §4" | Applied. The first now refers to the former §2.5 wording (replaced by "some level-(n−1) object"); the second to the battery report's former 0/0 row (`BATTERY_JACK.md`). | §5.4, §5.2 |
| R-07 | "six ssh attempts" — the bundled record has five | Applied. Five, with the count source named. | §5.5 |
| R-08 | path claims: `evidence/`, `check/`, `layer13/` presented as packet paths | Applied. Appendix A now opens with the mapping (paper artifact directory `AFM/PaperL/`, host paths prefixed), and the specific claims are reworded. The eventual release must carry the `evidence/`, `check/` and `layer13/` directories; the flat referee packet does not. | App. A, App. B, App. C |
| R-09 | supporting records out of sync with the draft (136/94; L11 provenance; `L13_REPORT` "not vacuous") | Applied. `REVIEW_TRIAGE_v03.md` says 140/95; `L11_NAMEGATE.md` says the hypothesis audit has run on v0.1–v0.3; `L13_REPORT.md` states that layers 1–9 do not certify non-vacuity. | those files |

## Partial rows

* **#2** — completed by R-03 and the §5.3 rewrite.
* **#5** — completed by R-02 (margins, JSON location, packet mapping).
* **#7** — completed by R-04 (and R-01 for the witness).
* **#15** — completed by R-06 (stale definite-article reference).
* **#16** — completed by R-08 (path mapping).

## Layer 13 closure (same round)

`L13_FULL_COMPARE.md` and `layer13/BlindCompareFull.lean`: all seven rows compared against the blind
writer's real types, both directions, with the compile receipt. §5.3 rewritten from that result.

## Exact checks behind R-01 (recorded 2026-11-24, jack, pinned tree)

`lake env lean -DmaxHeartbeats=4000000 -DmaxRecDepth=10000 --stdin`, pinned tree
(`Clifford/MorleyKernel.lean` sha `dce7b011…`), all exit 0 with `[propext, Classical.choice,
Quot.sound]`:

```lean
-- Counter6 is NOT a zero-vector instance: its parent vector has this last coordinate
theorem counter6_last_check :
    crossVec (KP 6 Counter6.cx (fun j => conj (Counter6.cx j))) (Fin.last 6)
      = (-238878720000 : ℂ)
```

For the §2.4 parabola tuple `c = ![⟨2,-2⟩,⟨4,-8⟩,⟨6,-18⟩,⟨8,-32⟩,⟨10,-50⟩,⟨12,-72⟩]`:

```lean
crossVec (KP 6 c (fun j => conj (c j))) ⟨3, by omega⟩ = 0            -- middle coordinate
crossVec (KP 5 (c ∘ (0 : Fin 6).succAbove)
  (fun j => conj ((c ∘ (0 : Fin 6).succAbove) j))) 0 = -9784472371200  -- level-5 P₀ ≠ 0
-- hence, by `parent_crossVec_zero_of_mid 0 c 0`, the whole parent vector is zero
```

`GenPosN` for that tuple and the level-4/5/6 witnesses are in `check/not_UniqEven.lean` (rc 0,
~28 s, std). The `Counter6` last-coordinate check is what makes the v0.3 example false; the parabola
checks are what replaces it.

## Layer 13 full pass (2026-11-24, gpt-5.6-sol on jack)

`layer13/L13_FULL_COMPARE.md`, `layer13/BlindCompareFull.lean` (8817 B, `lake env lean` rc 0 in
2.8 s, no `sorry`/`admit`/`axiom`/`native_decide`), `layer13/L13_FULL_STATUS.md`. All seven rows
compared against the writer's real types; six definitional, S2/S3 also quantifier differences; the
real ⇒ writer direction unclosed on all seven because the bridge lemmas do not exist. `sha256sum
Clifford/*.lean` identical before/after. `L13_REPORT.md` stage 6 and §5.3 of the draft record it.
